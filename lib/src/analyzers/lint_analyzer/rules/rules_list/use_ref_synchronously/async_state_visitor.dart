// Taken from https://github.com/dart-lang/sdk/blob/965234ccbe07dde0bf9f13466928c56767054d8f/pkg/linter/lib/src/rules/use_build_context_synchronously.dart#L73-L951

// ignore_for_file: implementation_imports

import 'package:analyzer/dart/ast/token.dart';
import 'package:analyzer/dart/ast/visitor.dart';
import 'package:analyzer/dart/constant/value.dart';
import 'package:analyzer/dart/element/element.dart';
import 'package:analyzer/dart/element/nullability_suffix.dart';
import 'package:analyzer/dart/element/type.dart';
import 'package:analyzer/error/error.dart';
import 'package:analyzer/error/listener.dart';
import 'package:analyzer/src/dart/ast/ast.dart';
import 'package:analyzer/src/dart/ast/token.dart';
import 'package:analyzer/src/dart/constant/compute.dart';
import 'package:analyzer/src/dart/constant/constant_verifier.dart';
import 'package:analyzer/src/dart/constant/evaluation.dart';
import 'package:analyzer/src/dart/constant/utilities.dart';
import 'package:analyzer/src/dart/constant/value.dart';
import 'package:analyzer/src/dart/element/element.dart';
import 'package:analyzer/src/dart/resolver/exit_detector.dart';
import 'package:analyzer/src/error/codes.g.dart';
import 'package:collection/collection.dart';

/// An enum whose values describe the state of asynchrony that a certain node
/// has in the syntax tree, with respect to another node.
///
/// A mounted check is a check of whether a bool-typed identifier, 'mounted',
/// is checked to be `true` or `false`, in a position which affects control
/// flow.
enum AsyncState {
  /// A value indicating that a node contains an "asynchronous gap" which is
  /// not definitely guarded with a mounted check.
  asynchronous,

  /// A value indicating that a node contains a positive mounted check that can
  /// guard a certain other node.
  mountedCheck,

  /// A value indicating that a node contains a negative mounted check that can
  /// guard a certain other node.
  notMountedCheck;

  AsyncState? get asynchronousOrNull =>
      this == asynchronous ? asynchronous : null;
}

/// A class that reuses a single [AsyncStateVisitor] to calculate and cache the
/// async state between parent and child nodes.
class AsyncStateTracker {
  final _asyncStateVisitor = AsyncStateVisitor();

  /// Whether a check on an unrelated 'mounted' property has been seen.
  bool get hasUnrelatedMountedCheck =>
      _asyncStateVisitor.hasUnrelatedMountedCheck;

  /// Returns the asynchronous state that exists between `this` and [reference].
  ///
  /// [reference] must be a direct child of `this`, or a sibling of `this`
  /// in a List of [AstNode]s.
  AsyncState? asyncStateFor(AstNode reference) {
    _asyncStateVisitor.reference = reference;
    final parent = reference.parent;
    if (parent == null) {
      return null;
    }

    final state = parent.accept(_asyncStateVisitor);
    _asyncStateVisitor.cacheState(parent, state);
    return state;
  }
}

/// A visitor whose `visit*` methods return the async state between a given node
/// and [reference].
///
/// The entrypoint for this visitor is [AsyncStateTracker.asyncStateFor].
///
/// Each `visit*` method can return one of three values:
/// * `null` means there is no interesting asynchrony between node and
///   [reference].
/// * [AsyncState.asynchronous] means the node contains an asynchronous gap
///   which is not guarded with a mounted check.
/// * [AsyncState.mountedCheck] means the node guards [reference] with a
///   positive mounted check.
/// * [AsyncState.notMountedCheck] means the node guards [reference] with a
///   negative mounted check.
///
/// (For all `visit*` methods except the entrypoint call, the value is
/// intermediate, and is only used in calculating the value for parent nodes.)
///
/// A node that contains a mounted check "guards" [reference] if control flow
/// can only reach [reference] if 'mounted' is `true`. Such checks can take
/// many forms:
///
/// * A mounted check in an if-condition can be a simple guard for nodes in the
///   if's then-statement or the if's else-statement, depending on the polarity
///   of the check. So `if (mounted) { reference; }` has a proper mounted check
///   and `if (!mounted) {} else { reference; }` has a proper mounted check.
/// * A statement in a series of statements containing a mounted check can guard
///   the later statements if control flow definitely exits in the case of a
///   `false` value for 'mounted'. So `if (!mounted) { return; } reference;` has
///   a proper mounted check.
/// * A mounted check in a try-statement can only guard later statements if it
///   is found in the `finally` section, as no statements found in the `try`
///   section or any `catch` sections are not guaranteed to have run before the
///   later statements.
/// * etc.
///
/// The `visit*` methods generally fall into three categories:
///
/// * A node may affect control flow, such that a contained mounted check may
///   properly guard [reference]. See [visitIfStatement] for one of the most
///   complicated examples.
/// * A node may be one component of a mounted check. An associated `visit*`
///   method builds up such a mounted check from inner expressions. For example,
///   given `!(context.mounted)`, the  notion of a mounted check is built from
///   the PrefixedIdentifier, the ParenthesizedExpression, and the
///   PrefixExpression (from inside to outside).
/// * Otherwise, a node may just contain an asynchronous gap. The vast majority
///   of node types fall into this category. Most of these `visit*` methods
///   use [AsyncState.asynchronousOrNull] or [_asynchronousIfAnyIsAsync].
class AsyncStateVisitor extends SimpleAstVisitor<AsyncState> {
  static const mountedName = 'mounted';

  late AstNode reference;

  final Map<AstNode, AsyncState?> _stateCache = {};

  /// Whether a check on an unrelated 'mounted' property has been seen.
  bool hasUnrelatedMountedCheck = false;

  /// Cache the async state between [node] and some reference node.
  ///
  /// Caching an async state is only valid when [node] is the parent of the
  /// reference node, and later visitations are performed using ancestors of the
  /// reference node as [reference].
  /// That is, if the async state between a parent node and a reference node,
  /// `R` is `A`, then the async state between any other node and a direct
  /// child, which is an ancestor of `R`, is also `A`.
  // TODO(srawlins): Checking the cache in every visit method could improve
  // performance. Just need to do the legwork.
  void cacheState(AstNode node, AsyncState? state) {
    _stateCache[node] = state;
  }

  @override
  AsyncState? visitAdjacentStrings(AdjacentStrings node) =>
      _asynchronousIfAnyIsAsync(node.strings);

  @override
  AsyncState? visitAsExpression(AsExpression node) =>
      node.expression.accept(this)?.asynchronousOrNull;

  @override
  AsyncState? visitAssignmentExpression(AssignmentExpression node) =>
      _inOrderAsyncState([
        (node: node.leftHandSide, mountedCanGuard: false),
        (node: node.rightHandSide, mountedCanGuard: true),
      ]);

  @override
  AsyncState? visitAwaitExpression(AwaitExpression node) {
    if (_stateCache.containsKey(node)) {
      return _stateCache[node];
    }

    // An expression _inside_ an await is executed before the await, and so is
    // safe; otherwise asynchronous.
    return reference == node.expression ? null : AsyncState.asynchronous;
  }

  @override
  AsyncState? visitBinaryExpression(BinaryExpression node) {
    if (node.leftOperand == reference) {
      return null;
    } else if (node.rightOperand == reference) {
      final leftGuardState = node.leftOperand.accept(this);
      return switch (leftGuardState) {
        AsyncState.asynchronous => AsyncState.asynchronous,
        AsyncState.mountedCheck when node.isAnd => AsyncState.mountedCheck,
        AsyncState.notMountedCheck when node.isOr => AsyncState.notMountedCheck,
        _ => null,
      };
    }

    // `reference` follows `node`, or an ancestor of `node`.

    if (node.isAnd) {
      final leftGuardState = node.leftOperand.accept(this);
      final rightGuardState = node.rightOperand.accept(this);
      return switch ((leftGuardState, rightGuardState)) {
        // If the left is uninteresting, just return the state of the right.
        (null, _) => rightGuardState,
        // If the right is uninteresting, just return the state of the left.
        (_, null) => leftGuardState,
        // Anything on the left followed by async on the right is async.
        (_, AsyncState.asynchronous) => AsyncState.asynchronous,
        // An async state on the left is superseded by the state on the right.
        (AsyncState.asynchronous, _) => rightGuardState,
        // Otherwise just use the state on the left.
        (AsyncState.mountedCheck, _) => AsyncState.mountedCheck,
        (AsyncState.notMountedCheck, _) => AsyncState.notMountedCheck,
      };
    }
    if (node.isOr) {
      final leftGuardState = node.leftOperand.accept(this);
      final rightGuardState = node.rightOperand.accept(this);
      return switch ((leftGuardState, rightGuardState)) {
        // Anything on the left followed by async on the right is async.
        (_, AsyncState.asynchronous) => AsyncState.asynchronous,
        // Async on the left followed by anything on the right is async.
        (AsyncState.asynchronous, _) => AsyncState.asynchronous,
        // A mounted guard only applies if both sides are guarded.
        (AsyncState.mountedCheck, AsyncState.mountedCheck) =>
          AsyncState.mountedCheck,
        (_, AsyncState.notMountedCheck) => AsyncState.notMountedCheck,
        (AsyncState.notMountedCheck, _) => AsyncState.notMountedCheck,
        // Otherwise it's just uninteresting.
        (_, _) => null,
      };
    }

    if (node.isEqual) {
      final leftGuardState = node.leftOperand.accept(this);
      final rightGuardState = node.rightOperand.accept(this);
      if (leftGuardState == AsyncState.asynchronous ||
          rightGuardState == AsyncState.asynchronous) {
        return AsyncState.asynchronous;
      }
      if (leftGuardState == AsyncState.mountedCheck ||
          leftGuardState == AsyncState.notMountedCheck) {
        final rightConstantValue = node.rightOperand.constantBoolValue;
        if (rightConstantValue == null) {
          return null;
        }
        return _constantEquality(leftGuardState, constant: rightConstantValue);
      }
      if (rightGuardState == AsyncState.mountedCheck ||
          rightGuardState == AsyncState.notMountedCheck) {
        final leftConstantValue = node.leftOperand.constantBoolValue;
        if (leftConstantValue == null) {
          return null;
        }
        return _constantEquality(rightGuardState, constant: leftConstantValue);
      }
      return null;
    }
    if (node.isNotEqual) {
      final leftGuardState = node.leftOperand.accept(this);
      final rightGuardState = node.rightOperand.accept(this);
      if (leftGuardState == AsyncState.asynchronous ||
          rightGuardState == AsyncState.asynchronous) {
        return AsyncState.asynchronous;
      }
      if (leftGuardState == AsyncState.mountedCheck ||
          leftGuardState == AsyncState.notMountedCheck) {
        final rightConstantValue = node.rightOperand.constantBoolValue;
        if (rightConstantValue == null) {
          return null;
        }
        return _constantEquality(leftGuardState, constant: !rightConstantValue);
      }
      if (rightGuardState == AsyncState.mountedCheck ||
          rightGuardState == AsyncState.notMountedCheck) {
        final leftConstantValue = node.leftOperand.constantBoolValue;
        if (leftConstantValue == null) {
          return null;
        }
        return _constantEquality(rightGuardState, constant: !leftConstantValue);
      }
      return null;
    } else {
      // Outside of a binary logical operation, a mounted check cannot guard a
      // later expression, so only check for asynchronous code.
      return node.leftOperand.accept(this)?.asynchronousOrNull ??
          node.rightOperand.accept(this)?.asynchronousOrNull;
    }
  }

  @override
  AsyncState? visitBlock(Block node) =>
      _visitBlockLike(node.statements, parent: node.parent);

  @override
  AsyncState? visitBlockFunctionBody(BlockFunctionBody node) =>
      // Stop visiting when we arrive at a function body.
      // Awaits and mounted checks inside it don't matter.
      null;

  @override
  AsyncState? visitCascadeExpression(CascadeExpression node) =>
      _asynchronousIfAnyIsAsync([node.target, ...node.cascadeSections]);

  @override
  AsyncState? visitCaseClause(CaseClause node) =>
      node.guardedPattern.accept(this);

  @override
  AsyncState? visitCatchClause(CatchClause node) =>
      node.body.accept(this)?.asynchronousOrNull;

  @override
  AsyncState? visitConditionalExpression(ConditionalExpression node) =>
      _visitIfLike(
        expression: node.condition,
        caseClause: null,
        thenBranch: node.thenExpression,
        elseBranch: node.elseExpression,
      );

  @override
  AsyncState? visitDoStatement(DoStatement node) {
    if (node.body == reference) {
      // After one loop, an `await` in the condition can affect the body.
      return node.condition.accept(this)?.asynchronousOrNull;
    } else if (node.condition == reference) {
      return node.body.accept(this)?.asynchronousOrNull;
    } else {
      return node.condition.accept(this)?.asynchronousOrNull ??
          node.body.accept(this)?.asynchronousOrNull;
    }
  }

  @override
  AsyncState? visitExpressionFunctionBody(ExpressionFunctionBody node) =>
      // Stop visiting when we arrive at a function body.
      // Awaits and mounted checks inside it don't matter.
      null;

  @override
  AsyncState? visitExpressionStatement(ExpressionStatement node) =>
      node.expression == reference
          ? null
          : node.expression.accept(this)?.asynchronousOrNull;

  @override
  AsyncState? visitExtensionOverride(ExtensionOverride node) =>
      _asynchronousIfAnyIsAsync(node.argumentList.arguments);

  @override
  AsyncState? visitForElement(ForElement node) {
    final forLoopParts = node.forLoopParts;
    final referenceIsBody = node.body == reference;
    return switch (forLoopParts) {
      ForPartsWithDeclarations() => _inOrderAsyncState([
          for (final declaration in forLoopParts.variables.variables)
            (node: declaration, mountedCanGuard: false),
          (node: forLoopParts.condition, mountedCanGuard: referenceIsBody),
          for (final updater in forLoopParts.updaters)
            (node: updater, mountedCanGuard: false),
          (node: node.body, mountedCanGuard: false),
        ]),
      ForPartsWithExpression() => _inOrderAsyncState([
          (node: forLoopParts.initialization, mountedCanGuard: false),
          (node: forLoopParts.condition, mountedCanGuard: referenceIsBody),
          for (final updater in forLoopParts.updaters)
            (node: updater, mountedCanGuard: false),
          (node: node.body, mountedCanGuard: false),
        ]),
      ForEachParts() => _inOrderAsyncState([
          (node: forLoopParts.iterable, mountedCanGuard: false),
          (node: node.body, mountedCanGuard: false),
        ]),
      _ => null,
    };
  }

  @override
  AsyncState? visitForStatement(ForStatement node) {
    final forLoopParts = node.forLoopParts;
    final referenceIsBody = node.body == reference;
    return switch (forLoopParts) {
      ForPartsWithDeclarations() => _inOrderAsyncState([
          for (final declaration in forLoopParts.variables.variables)
            (node: declaration, mountedCanGuard: false),
          // The body can be guarded by the condition.
          (node: forLoopParts.condition, mountedCanGuard: referenceIsBody),
          for (final updater in forLoopParts.updaters)
            (node: updater, mountedCanGuard: false),
          (node: node.body, mountedCanGuard: false),
        ]),
      ForPartsWithExpression() => _inOrderAsyncState([
          (node: forLoopParts.initialization, mountedCanGuard: false),
          // The body can be guarded by the condition.
          (node: forLoopParts.condition, mountedCanGuard: referenceIsBody),
          for (final updater in forLoopParts.updaters)
            (node: updater, mountedCanGuard: false),
          (node: node.body, mountedCanGuard: false),
        ]),
      ForEachParts() => _inOrderAsyncState([
          (node: forLoopParts.iterable, mountedCanGuard: false),
          (node: node.body, mountedCanGuard: false),
        ]),
      _ => null,
    };
  }

  @override
  AsyncState? visitFunctionExpressionInvocation(
          FunctionExpressionInvocation node) =>
      _asynchronousIfAnyIsAsync(
          [node.function, ...node.argumentList.arguments]);

  @override
  AsyncState? visitGuardedPattern(GuardedPattern node) =>
      node.whenClause?.accept(this);

  @override
  AsyncState? visitIfElement(IfElement node) => _visitIfLike(
        expression: node.expression,
        caseClause: node.caseClause,
        thenBranch: node.thenElement,
        elseBranch: node.elseElement,
      );

  @override
  AsyncState? visitIfStatement(IfStatement node) => _visitIfLike(
        expression: node.expression,
        caseClause: node.caseClause,
        thenBranch: node.thenStatement,
        elseBranch: node.elseStatement,
      );

  @override
  AsyncState? visitIndexExpression(IndexExpression node) =>
      _asynchronousIfAnyIsAsync([node.target, node.index]);

  @override
  AsyncState? visitInstanceCreationExpression(
    InstanceCreationExpression node,
  ) =>
      _asynchronousIfAnyIsAsync(node.argumentList.arguments);

  @override
  AsyncState? visitInterpolationExpression(InterpolationExpression node) =>
      node.expression.accept(this)?.asynchronousOrNull;

  @override
  AsyncState? visitIsExpression(IsExpression node) =>
      node.expression.accept(this)?.asynchronousOrNull;

  @override
  AsyncState? visitLabeledStatement(LabeledStatement node) =>
      node.statement.accept(this);

  @override
  AsyncState? visitListLiteral(ListLiteral node) =>
      _asynchronousIfAnyIsAsync(node.elements);

  @override
  AsyncState? visitMapLiteralEntry(MapLiteralEntry node) =>
      _asynchronousIfAnyIsAsync([node.key, node.value]);

  @override
  AsyncState? visitMethodInvocation(MethodInvocation node) =>
      _asynchronousIfAnyIsAsync([node.target, ...node.argumentList.arguments]);

  @override
  AsyncState? visitNamedExpression(NamedExpression node) =>
      node.expression.accept(this)?.asynchronousOrNull;

  @override
  AsyncState? visitParenthesizedExpression(ParenthesizedExpression node) =>
      node.expression.accept(this);

  @override
  AsyncState? visitPostfixExpression(PostfixExpression node) =>
      node.operand.accept(this)?.asynchronousOrNull;

  @override
  AsyncState? visitPrefixedIdentifier(PrefixedIdentifier node) =>
      _visitIdentifier(node.identifier);

  @override
  AsyncState? visitPrefixExpression(PrefixExpression node) {
    if (node.isNot) {
      final guardState = node.operand.accept(this);
      return switch (guardState) {
        AsyncState.mountedCheck => AsyncState.notMountedCheck,
        AsyncState.notMountedCheck => AsyncState.mountedCheck,
        _ => guardState,
      };
    } else {
      return null;
    }
  }

  @override
  AsyncState? visitPropertyAccess(PropertyAccess node) {
    if (node.propertyName.name == mountedName) {
      return node.target?.accept(this)?.asynchronousOrNull ??
          node.propertyName.accept(this);
    }
    return node.target?.accept(this)?.asynchronousOrNull;
  }

  @override
  AsyncState? visitRecordLiteral(RecordLiteral node) =>
      _asynchronousIfAnyIsAsync(node.fields);

  @override
  AsyncState? visitSetOrMapLiteral(SetOrMapLiteral node) =>
      _asynchronousIfAnyIsAsync(node.elements);

  @override
  AsyncState? visitSimpleIdentifier(SimpleIdentifier node) =>
      _visitIdentifier(node);

  @override
  AsyncState? visitSpreadElement(SpreadElement node) =>
      node.expression.accept(this)?.asynchronousOrNull;

  @override
  AsyncState? visitStringInterpolation(StringInterpolation node) =>
      _asynchronousIfAnyIsAsync(node.elements);

  @override
  AsyncState? visitSwitchCase(SwitchCase node) =>
      // TODO(srawlins): Handle when `reference` is in one of the statements.
      _inOrderAsyncStateGuardable([node.expression, ...node.statements]);

  @override
  AsyncState? visitSwitchDefault(SwitchDefault node) =>
      _inOrderAsyncStateGuardable(node.statements);

  @override
  AsyncState? visitSwitchExpression(SwitchExpression node) =>
      _asynchronousIfAnyIsAsync([node.expression, ...node.cases]);

  @override
  AsyncState? visitSwitchExpressionCase(SwitchExpressionCase node) {
    if (reference == node.guardedPattern) {
      return null;
    }
    final whenClauseState = node.guardedPattern.whenClause?.accept(this);
    if (reference == node.expression) {
      if (whenClauseState == AsyncState.asynchronous ||
          whenClauseState == AsyncState.mountedCheck) {
        return whenClauseState;
      }
      return null;
    }
    return whenClauseState?.asynchronousOrNull ??
        node.expression.accept(this)?.asynchronousOrNull;
  }

  @override
  AsyncState? visitSwitchPatternCase(SwitchPatternCase node) {
    if (reference == node.guardedPattern) {
      return null;
    }
    final statementsAsyncState =
        _visitBlockLike(node.statements, parent: node.parent);
    if (statementsAsyncState != null) {
      return statementsAsyncState;
    }
    if (node.statements.contains(reference)) {
      // Any when-clause in `node` and any fallthrough when-clauses are handled
      // in `visitSwitchStatement`.
      return null;
    } else {
      return node.guardedPattern.whenClause?.accept(this)?.asynchronousOrNull;
    }
  }

  @override
  AsyncState? visitSwitchStatement(SwitchStatement node) {
    // TODO(srawlins): Check for definite exits in the members.
    node.expression.accept(this)?.asynchronousOrNull ??
        _asynchronousIfAnyIsAsync(node.members);

    final reference = this.reference;
    if (reference is SwitchMember) {
      final index = node.members.indexOf(reference);

      // Control may flow to `node.statements` via this case's `guardedPattern`,
      // or via fallthrough. Consider fallthrough when-clauses.

      // Track whether we are iterating in fall-through cases.
      var checkedCasesFallThrough = true;
      // Track whether all checked cases have been `AsyncState.mountedCheck`
      // (only relevant for fall-through cases).
      var checkedCasesAreAllMountedChecks = true;

      for (var i = index; i >= 0; i--) {
        final case_ = node.members[i];
        if (case_ is! SwitchPatternCase) {
          continue;
        }

        final whenAsyncState = case_.guardedPattern.whenClause?.accept(this);
        if (whenAsyncState == AsyncState.asynchronous) {
          return AsyncState.asynchronous;
        }
        if (checkedCasesFallThrough) {
          final caseIsFallThrough = i == index || case_.statements.isEmpty;

          if (caseIsFallThrough) {
            checkedCasesAreAllMountedChecks &=
                whenAsyncState == AsyncState.mountedCheck;
          } else {
            // We have collected whether all of the fallthrough cases have
            // mounted guards.
            if (checkedCasesAreAllMountedChecks) {
              return AsyncState.mountedCheck;
            }
          }
          checkedCasesFallThrough &= caseIsFallThrough;
        }
      }

      if (checkedCasesFallThrough && checkedCasesAreAllMountedChecks) {
        return AsyncState.mountedCheck;
      }

      return null;
    } else {
      return node.expression.accept(this)?.asynchronousOrNull ??
          _asynchronousIfAnyIsAsync(node.members);
    }
  }

  @override
  AsyncState? visitTryStatement(TryStatement node) {
    if (node.body == reference) {
      return null;
    } else if (node.catchClauses.any((clause) => clause == reference)) {
      return node.body.accept(this)?.asynchronousOrNull;
    } else if (node.finallyBlock == reference) {
      return _asynchronousIfAnyIsAsync([node.body, ...node.catchClauses]);
    }

    // Only statements in the `finally` section of a try-statement can
    // sufficiently guard statements following the try-statement.
    return node.finallyBlock?.accept(this) ??
        _asynchronousIfAnyIsAsync([node.body, ...node.catchClauses]);
  }

  @override
  AsyncState? visitVariableDeclaration(VariableDeclaration node) =>
      node.initializer?.accept(this)?.asynchronousOrNull;

  @override
  AsyncState? visitVariableDeclarationStatement(
          VariableDeclarationStatement node) =>
      _asynchronousIfAnyIsAsync([
        for (final variable in node.variables.variables) variable.initializer,
      ]);

  @override
  AsyncState? visitWhenClause(WhenClause node) => node.expression.accept(this);

  @override
  AsyncState? visitWhileStatement(WhileStatement node) =>
      // TODO(srawlins): if the condition is a mounted guard and `reference` is
      // the body or follows the while.
      // A while-statement's body is not guaranteed to execute, so no mounted
      // checks properly guard.
      node.condition.accept(this)?.asynchronousOrNull ??
      node.body.accept(this)?.asynchronousOrNull;

  @override
  AsyncState? visitYieldStatement(YieldStatement node) =>
      node.expression.accept(this)?.asynchronousOrNull;

  /// Returns [AsyncState.asynchronous] if visiting any of [nodes] returns
  /// [AsyncState.asynchronous], otherwise `null`.
  ///
  /// This function does not take mounted checks into account, so it cannot be
  /// used when [nodes] can affect control flow.
  AsyncState? _asynchronousIfAnyIsAsync(List<AstNode?> nodes) {
    final index = nodes.indexOf(reference);
    if (index < 0) {
      return nodes.any((node) => node?.accept(this) == AsyncState.asynchronous)
          ? AsyncState.asynchronous
          : null;
    } else {
      return nodes
              .take(index)
              .any((node) => node?.accept(this) == AsyncState.asynchronous)
          ? AsyncState.asynchronous
          : null;
    }
  }

  /// Returns an [AsyncState] representing [state] or its opposite, based on
  /// equality with [constant].
  AsyncState? _constantEquality(AsyncState? state, {required bool constant}) =>
      switch ((state, constant)) {
        // Representing `context.mounted == true`, etc.
        (AsyncState.mountedCheck, true) => AsyncState.mountedCheck,
        (AsyncState.notMountedCheck, true) => AsyncState.notMountedCheck,
        (AsyncState.mountedCheck, false) => AsyncState.notMountedCheck,
        (AsyncState.notMountedCheck, false) => AsyncState.mountedCheck,
        _ => null,
      };

  /// Walks backwards through [nodes] looking for "interesting" async states,
  /// determining the async state of [nodes], with respect to [reference].
  ///
  /// [nodes] is a list of records, each with an [AstNode] and a field
  /// representing whether a mounted check in the node can guard [reference].
  ///
  /// [nodes] must be in expected execution order. [reference] can be one of
  /// [nodes], or can follow [nodes], or can follow an ancestor of [nodes].
  ///
  /// If [reference] is one of the [nodes], this traversal starts at the node
  /// that precedes it, rather than at the end of the list.
  AsyncState? _inOrderAsyncState(
      List<({AstNode? node, bool mountedCanGuard})> nodes) {
    if (nodes.isEmpty) {
      return null;
    }
    if (nodes.first.node == reference) {
      return null;
    }
    final referenceIndex =
        nodes.indexWhere((element) => element.node == reference);
    final startingIndex =
        referenceIndex > 0 ? referenceIndex - 1 : nodes.length - 1;

    for (var i = startingIndex; i >= 0; i--) {
      final (:node, :mountedCanGuard) = nodes[i];
      if (node == null) {
        continue;
      }
      final asyncState = node.accept(this);
      if (asyncState == AsyncState.asynchronous) {
        return AsyncState.asynchronous;
      }
      if (mountedCanGuard && asyncState != null) {
        // Walking from the last node to the first, as soon as we encounter a
        // mounted check (positive or negative) or asynchronous code, that's
        // the state of the whole series.
        return asyncState;
      }
    }
    return null;
  }

  /// A simple wrapper for [_inOrderAsyncState] for [nodes] which can all guard
  /// [reference] with a mounted check.
  AsyncState? _inOrderAsyncStateGuardable(Iterable<AstNode?> nodes) =>
      _inOrderAsyncState([
        for (final node in nodes) (node: node, mountedCanGuard: true),
      ]);

  /// Compute the [AsyncState] of a "block-like" node which has [statements].
  AsyncState? _visitBlockLike(List<Statement> statements,
      {required AstNode? parent}) {
    final reference = this.reference;
    if (reference is Statement) {
      final index = statements.indexOf(reference);
      if (index >= 0) {
        final precedingAsyncState = _inOrderAsyncStateGuardable(statements);
        if (precedingAsyncState != null) {
          return precedingAsyncState;
        }
        if (parent is DoStatement ||
            parent is ForStatement ||
            parent is WhileStatement) {
          // Check for asynchrony in the statements that _follow_ [reference],
          // as they may lead to an async gap before we loop back to
          // [reference].
          return _inOrderAsyncStateGuardable(statements.skip(index + 1))
              ?.asynchronousOrNull;
        }
        return null;
      }
    }

    // When [reference] is not one of [node.statements], walk through all of
    // them.
    return statements.reversed
        .map((s) => s.accept(this))
        .firstWhereOrNull((state) => state != null);
  }

  /// The state of [node], accounting for a possible mounted check, or an
  /// attempted mounted check (using an unrelated element).
  AsyncState? _visitIdentifier(SimpleIdentifier node) {
    if (node.name != mountedName) {
      return null;
    }

    return AsyncState.mountedCheck;
  }

  /// Compute the [AsyncState] of an "if-like" node which has a [expression], a
  /// possible [caseClause], a [thenBranch], and a possible [elseBranch].
  AsyncState? _visitIfLike({
    required Expression expression,
    required CaseClause? caseClause,
    required AstNode thenBranch,
    required AstNode? elseBranch,
  }) {
    if (reference == expression) {
      // The async state of the condition is not affected by the case-clause,
      // then-branch, or else-branch.
      return null;
    }
    final expressionAsyncState = expression.accept(this);
    if (reference == caseClause) {
      return switch (expressionAsyncState) {
        AsyncState.asynchronous => AsyncState.asynchronous,
        AsyncState.mountedCheck => AsyncState.mountedCheck,
        _ => null,
      };
    }

    final caseClauseAsyncState = caseClause?.accept(this);
    // The condition state is the combined state of `expression` and
    // `caseClause`.
    final conditionAsyncState =
        switch ((expressionAsyncState, caseClauseAsyncState)) {
      // If the left is uninteresting, just return the state of the right.
      (null, _) => caseClauseAsyncState,
      // If the right is uninteresting, just return the state of the left.
      (_, null) => expressionAsyncState,
      // Anything on the left followed by async on the right is async.
      (_, AsyncState.asynchronous) => AsyncState.asynchronous,
      // An async state on the left is superseded by the state on the right.
      (AsyncState.asynchronous, _) => caseClauseAsyncState,
      // Otherwise just use the state on the left.
      (AsyncState.mountedCheck, _) => AsyncState.mountedCheck,
      (AsyncState.notMountedCheck, _) => AsyncState.notMountedCheck,
    };

    if (reference == thenBranch) {
      return switch (conditionAsyncState) {
        AsyncState.asynchronous => AsyncState.asynchronous,
        AsyncState.mountedCheck => AsyncState.mountedCheck,
        _ => null,
      };
    } else if (reference == elseBranch) {
      return switch (conditionAsyncState) {
        AsyncState.asynchronous => AsyncState.asynchronous,
        AsyncState.notMountedCheck => AsyncState.mountedCheck,
        _ => null,
      };
    } else {
      // `reference` is a statement that comes after `node`, or an ancestor of
      // `node`, in a NodeList.
      final thenAsyncState = thenBranch.accept(this);
      final elseAsyncState = elseBranch?.accept(this);
      final thenTerminates = thenBranch.terminatesControl;
      final elseTerminates = elseBranch?.terminatesControl ?? false;

      if (thenAsyncState == AsyncState.notMountedCheck) {
        if (elseAsyncState == AsyncState.notMountedCheck || elseTerminates) {
          return AsyncState.notMountedCheck;
        }
      }
      if (elseAsyncState == AsyncState.notMountedCheck && thenTerminates) {
        return AsyncState.notMountedCheck;
      }

      if (thenAsyncState == AsyncState.asynchronous && !thenTerminates) {
        return AsyncState.asynchronous;
      }
      if (elseAsyncState == AsyncState.asynchronous && !elseTerminates) {
        return AsyncState.asynchronous;
      }

      if (conditionAsyncState == AsyncState.asynchronous) {
        return AsyncState.asynchronous;
      }

      if (conditionAsyncState == AsyncState.mountedCheck && elseTerminates) {
        return AsyncState.notMountedCheck;
      }

      if (conditionAsyncState == AsyncState.notMountedCheck && thenTerminates) {
        return AsyncState.notMountedCheck;
      }

      return null;
    }
  }
}

/// Function with callback parameters that should be "protected."
///
/// Any callback passed as a [positional] argument or [named] argument to such
/// a function must have a mounted guard check for any references to
/// BuildContext.
class ProtectedFunction {
  const ProtectedFunction(
    this.library,
    this.type,
    this.name, {
    this.positional = const <int>[],
    this.named = const <String>[],
  });

  // Taken from https://github.com/dart-lang/sdk/blob/965234ccbe07dde0bf9f13466928c56767054d8f/pkg/linter/lib/src/rules/use_build_context_synchronously.dart#L1004-L1079
  static const constructors = [
    // Future constructors.
    // Protect the unnamed constructor as both `Future()` and `Future.new()`.
    ProtectedFunction('dart.async', 'Future', null, positional: [0]),
    ProtectedFunction('dart.async', 'Future', 'new', positional: [0]),
    ProtectedFunction('dart.async', 'Future', 'delayed', positional: [1]),
    ProtectedFunction('dart.async', 'Future', 'microtask', positional: [0]),

    // Stream constructors.
    ProtectedFunction(
      'dart.async',
      'Stream',
      'eventTransformed',
      positional: [1],
    ),
    ProtectedFunction('dart.async', 'Stream', 'multi', positional: [0]),
    ProtectedFunction('dart.async', 'Stream', 'periodic', positional: [1]),

    // StreamController constructors.
    ProtectedFunction(
      'dart.async',
      'StreamController',
      null,
      named: ['onListen', 'onPause', 'onResume', 'onCancel'],
    ),
    ProtectedFunction(
      'dart.async',
      'StreamController',
      'new',
      named: ['onListen', 'onPause', 'onResume', 'onCancel'],
    ),
    ProtectedFunction(
      'dart.async',
      'StreamController',
      'broadcast',
      named: ['onListen', 'onCancel'],
    ),
  ];

  static const instanceMethods = [
    // Future instance methods.
    ProtectedFunction(
      'dart.async',
      'Future',
      'catchError',
      positional: [0],
      named: ['test'],
    ),
    ProtectedFunction(
      'dart.async',
      'Future',
      'onError',
      positional: [0],
      named: ['test'],
    ),
    ProtectedFunction(
      'dart.async',
      'Future',
      'then',
      positional: [0],
      named: ['onError'],
    ),
    ProtectedFunction('dart.async', 'Future', 'timeout', named: ['onTimeout']),
    ProtectedFunction('dart.async', 'Future', 'whenComplete', positional: [0]),

    // Stream instance methods.
    ProtectedFunction('dart.async', 'Stream', 'any', positional: [0]),
    ProtectedFunction(
      'dart.async',
      'Stream',
      'asBroadcastStream',
      named: ['onListen', 'onCancel'],
    ),
    ProtectedFunction('dart.async', 'Stream', 'asyncExpand', positional: [0]),
    ProtectedFunction('dart.async', 'Stream', 'asyncMap', positional: [0]),
    ProtectedFunction('dart.async', 'Stream', 'doOnCancel', positional: [0]),
    ProtectedFunction('dart.async', 'Stream', 'doOnData', positional: [0]),
    ProtectedFunction('dart.async', 'Stream', 'doOnDone', positional: [0]),
    ProtectedFunction('dart.async', 'Stream', 'doOnEach', positional: [0]),
    ProtectedFunction('dart.async', 'Stream', 'doOnError', positional: [0]),
    ProtectedFunction('dart.async', 'Stream', 'doOnListen', positional: [0]),
    ProtectedFunction('dart.async', 'Stream', 'doOnPause', positional: [0]),
    ProtectedFunction('dart.async', 'Stream', 'doOnResume', positional: [0]),
    ProtectedFunction('dart.async', 'Stream', 'distinct', positional: [0]),
    ProtectedFunction('dart.async', 'Stream', 'expand', positional: [0]),
    ProtectedFunction(
      'dart.async',
      'Stream',
      'firstWhere',
      positional: [0],
      named: ['orElse'],
    ),
    ProtectedFunction('dart.async', 'Stream', 'fold', positional: [1]),
    ProtectedFunction('dart.async', 'Stream', 'forEach', positional: [0]),
    ProtectedFunction(
      'dart.async',
      'Stream',
      'handleError',
      positional: [0],
      named: ['test'],
    ),
    ProtectedFunction(
      'dart.async',
      'Stream',
      'lastWhere',
      positional: [0],
      named: ['orElse'],
    ),
    ProtectedFunction(
      'dart.async',
      'Stream',
      'listen',
      positional: [0],
      named: ['onError', 'onDone'],
    ),
    ProtectedFunction('dart.async', 'Stream', 'map', positional: [0]),
    ProtectedFunction('dart.async', 'Stream', 'reduce', positional: [0]),
    ProtectedFunction(
      'dart.async',
      'Stream',
      'singleWhere',
      positional: [0],
      named: ['orElse'],
    ),
    ProtectedFunction('dart.async', 'Stream', 'skipWhile', positional: [0]),
    ProtectedFunction('dart.async', 'Stream', 'takeWhile', positional: [0]),
    ProtectedFunction('dart.async', 'Stream', 'timeout', named: ['onTimeout']),
    ProtectedFunction('dart.async', 'Stream', 'where', positional: [0]),

    // StreamSubscription instance methods.
    ProtectedFunction(
      'dart.async',
      'StreamSubscription',
      'onData',
      positional: [0],
    ),
    ProtectedFunction(
      'dart.async',
      'StreamSubscription',
      'onDone',
      positional: [0],
    ),
    ProtectedFunction(
      'dart.async',
      'StreamSubscription',
      'onError',
      positional: [0],
    ),
  ];

  static const staticMethods = [
    // Future static methods.
    ProtectedFunction('dart.async', 'Future', 'doWhile', positional: [0]),
    ProtectedFunction('dart.async', 'Future', 'forEach', positional: [1]),
    ProtectedFunction('dart.async', 'Future', 'wait', named: ['cleanUp']),
  ];

  final String library;

  /// The name of the target type of the function (for instance methods) or the
  /// defining element (for constructors and static methods).
  final String? type;

  /// The name of the function. Can be `null` to represent an unnamed
  /// constructor.
  final String? name;

  /// The list of positional parameters that are protected.
  final List<int> positional;

  /// The list of named parameters that are protected.
  final List<String> named;
}

extension on AstNode {
  bool get terminatesControl {
    final self = this;
    if (self is Block) {
      return self.statements.isNotEmpty &&
          self.statements.last.terminatesControl;
    }
    // TODO(srawlins): Make ExitDetector 100% functional for our needs. The
    // basic (only?) difference is that it doesn't consider a `break` statement
    // to be exiting.
    if (self is ReturnStatement ||
        self is BreakStatement ||
        self is ContinueStatement) {
      return true;
    }
    return accept(ExitDetector()) ?? false;
  }
}

extension on PrefixExpression {
  bool get isNot => operator.type == TokenType.BANG;
}

extension on BinaryExpression {
  bool get isAnd => operator.type == TokenType.AMPERSAND_AMPERSAND;
  bool get isEqual => operator.type == TokenType.EQ_EQ;
  bool get isNotEqual => operator.type == TokenType.BANG_EQ;
  bool get isOr => operator.type == TokenType.BAR_BAR;
}

extension on Statement {
  /// Whether this statement terminates control, via a [BreakStatement], a
  /// [ContinueStatement], or other definite exits, as determined by
  /// [ExitDetector].
  bool get terminatesControl {
    final self = this;
    if (self is Block) {
      final last = self.statements.lastOrNull;
      return last != null && last.terminatesControl;
    }
    // TODO(srawlins): Make ExitDetector 100% functional for our needs. The
    // basic (only?) difference is that it doesn't consider a `break` statement
    // to be exiting.
    if (self is BreakStatement || self is ContinueStatement) {
      return true;
    }
    return accept(ExitDetector()) ?? false;
  }
}

extension on Expression {
  bool? get constantBoolValue => computeConstantValue().value?.toBoolValue();
}

extension ElementExtension on Element {
  /// The `mounted` getter which is associated with `this`, if this static
  /// element is `BuildContext` from Flutter.
  Element? get associatedMountedGetter {
    final self = this;

    if (self is PropertyAccessorElement) {
      final enclosingElement = self.enclosingElement3;
      if (enclosingElement is InterfaceElement &&
          Flutter.isState(enclosingElement)) {
        // The BuildContext object is the field on Flutter's State class.
        // This object can only be guarded by async gaps with a mounted
        // check on the State.
        return enclosingElement.augmented
            .lookUpGetter(name: 'mounted', library: enclosingElement.library);
      }
    }

    final buildContextElement = switch (self) {
      ExecutableElement() => self.returnType,
      VariableElement() => self.type,
      _ => null,
    }
        ?.element;
    if (buildContextElement is InterfaceElement) {
      return buildContextElement.augmented
          .lookUpGetter(name: 'mounted', library: buildContextElement.library);
    }

    return null;
  }
}

/// The result of attempting to evaluate an expression as a constant.
final class LinterConstantEvaluationResult {
  /// The value of the expression, or `null` if has [errors].
  final DartObject? value;

  /// The errors reported during the evaluation.
  final List<AnalysisError> errors;

  LinterConstantEvaluationResult._(this.value, this.errors);
}

extension ExpressionExtension on Expression {
  /// Whether it would be valid for this expression to have a `const` keyword.
  ///
  /// Note that this method can cause constant evaluation to occur, which can be
  /// computationally expensive.
  bool get canBeConst {
    final self = this;
    return switch (self) {
      InstanceCreationExpressionImpl() => _canBeConstInstanceCreation(self),
      TypedLiteralImpl() => _canBeConstTypedLiteral(self),
      _ => false,
    };
  }

  /// Computes the constant value of `this`, if it has one.
  ///
  /// Returns a [LinterConstantEvaluationResult], containing both the computed
  /// constant value, and a list of errors that occurred during the computation.
  LinterConstantEvaluationResult computeConstantValue() {
    final unitElement =
        thisOrAncestorOfType<CompilationUnit>()?.declaredElement;
    if (unitElement == null) {
      return LinterConstantEvaluationResult._(null, []);
    }
    final libraryElement = unitElement.library as LibraryElementImpl;

    final errorListener = RecordingErrorListener();

    final evaluationEngine = ConstantEvaluationEngine(
      declaredVariables: unitElement.session.declaredVariables,
      configuration: ConstantEvaluationConfiguration(),
    );

    final dependencies = <ConstantEvaluationTarget>[];
    accept(ReferenceFinder(dependencies.add));

    computeConstants(
      declaredVariables: unitElement.session.declaredVariables,
      constants: dependencies,
      featureSet: libraryElement.featureSet,
      configuration: ConstantEvaluationConfiguration(),
    );

    final visitor = ConstantVisitor(
      evaluationEngine,
      libraryElement,
      ErrorReporter(errorListener, unitElement.source),
    );

    final constant = visitor.evaluateAndReportInvalidConstant(this);
    final dartObject = constant is DartObjectImpl ? constant : null;
    return LinterConstantEvaluationResult._(dartObject, errorListener.errors);
  }

  bool _canBeConstInstanceCreation(InstanceCreationExpressionImpl node) {
    final element = node.constructorName.staticElement;
    if (element == null || !element.isConst) {
      return false;
    }

    // Ensure that dependencies (e.g. default parameter values) are computed.
    final implElement = element.declaration;
    // ignore: cascade_invocations
    implElement.computeConstantDependencies();

    // Verify that the evaluation of the constructor would not produce an
    // exception.
    final oldKeyword = node.keyword;
    try {
      node.keyword = KeywordToken(Keyword.CONST, offset);
      return !hasConstantVerifierError;
    } finally {
      node.keyword = oldKeyword;
    }
  }

  bool _canBeConstTypedLiteral(TypedLiteralImpl node) {
    final oldKeyword = node.constKeyword;
    try {
      node.constKeyword = KeywordToken(Keyword.CONST, offset);
      return !hasConstantVerifierError;
    } finally {
      node.constKeyword = oldKeyword;
    }
  }
}

extension on AstNode {
  /// Whether [ConstantVerifier] reports an error when computing the value of
  /// `this` as a constant.
  bool get hasConstantVerifierError {
    final unitElement =
        thisOrAncestorOfType<CompilationUnit>()?.declaredElement;
    if (unitElement == null) {
      return false;
    }
    final libraryElement = unitElement.library as LibraryElementImpl;

    final dependenciesFinder = ConstantExpressionsDependenciesFinder();
    accept(dependenciesFinder);
    computeConstants(
      declaredVariables: unitElement.session.declaredVariables,
      constants: dependenciesFinder.dependencies.toList(),
      featureSet: libraryElement.featureSet,
      configuration: ConstantEvaluationConfiguration(),
    );

    final listener = _ConstantAnalysisErrorListener();
    final errorReporter = ErrorReporter(listener, unitElement.source);

    accept(
      ConstantVerifier(
        errorReporter,
        libraryElement,
        unitElement.session.declaredVariables,
      ),
    );
    return listener.hasConstError;
  }
}

/// An error listener that only records whether any constant related errors have
/// been reported.
class _ConstantAnalysisErrorListener extends AnalysisErrorListener {
  /// A flag indicating whether any constant related errors have been reported
  /// to this listener.
  bool hasConstError = false;

  @override
  void onError(AnalysisError error) {
    final errorCode = error.errorCode;
    if (errorCode is CompileTimeErrorCode) {
      switch (errorCode) {
        case CompileTimeErrorCode
              .CONST_CONSTRUCTOR_CONSTANT_FROM_DEFERRED_LIBRARY:
        case CompileTimeErrorCode
              .CONST_CONSTRUCTOR_WITH_FIELD_INITIALIZED_BY_NON_CONST:
        case CompileTimeErrorCode.CONST_EVAL_EXTENSION_METHOD:
        case CompileTimeErrorCode.CONST_EVAL_EXTENSION_TYPE_METHOD:
        case CompileTimeErrorCode.CONST_EVAL_METHOD_INVOCATION:
        case CompileTimeErrorCode.CONST_EVAL_PROPERTY_ACCESS:
        case CompileTimeErrorCode.CONST_EVAL_TYPE_BOOL:
        case CompileTimeErrorCode.CONST_EVAL_TYPE_BOOL_INT:
        case CompileTimeErrorCode.CONST_EVAL_TYPE_BOOL_NUM_STRING:
        case CompileTimeErrorCode.CONST_EVAL_TYPE_INT:
        case CompileTimeErrorCode.CONST_EVAL_TYPE_NUM:
        case CompileTimeErrorCode.CONST_EVAL_TYPE_NUM_STRING:
        case CompileTimeErrorCode.CONST_EVAL_TYPE_STRING:
        case CompileTimeErrorCode.CONST_EVAL_THROWS_EXCEPTION:
        case CompileTimeErrorCode.CONST_EVAL_THROWS_IDBZE:
        case CompileTimeErrorCode.CONST_EVAL_FOR_ELEMENT:
        case CompileTimeErrorCode.CONST_MAP_KEY_NOT_PRIMITIVE_EQUALITY:
        case CompileTimeErrorCode.CONST_SET_ELEMENT_NOT_PRIMITIVE_EQUALITY:
        case CompileTimeErrorCode.CONST_TYPE_PARAMETER:
        case CompileTimeErrorCode.CONST_WITH_NON_CONST:
        case CompileTimeErrorCode.CONST_WITH_NON_CONSTANT_ARGUMENT:
        case CompileTimeErrorCode.CONST_WITH_TYPE_PARAMETERS:
        case CompileTimeErrorCode
              .CONST_WITH_TYPE_PARAMETERS_CONSTRUCTOR_TEAROFF:
        case CompileTimeErrorCode.INVALID_CONSTANT:
        case CompileTimeErrorCode.MISSING_CONST_IN_LIST_LITERAL:
        case CompileTimeErrorCode.MISSING_CONST_IN_MAP_LITERAL:
        case CompileTimeErrorCode.MISSING_CONST_IN_SET_LITERAL:
        case CompileTimeErrorCode.NON_BOOL_CONDITION:
        case CompileTimeErrorCode.NON_CONSTANT_LIST_ELEMENT:
        case CompileTimeErrorCode.NON_CONSTANT_MAP_ELEMENT:
        case CompileTimeErrorCode.NON_CONSTANT_MAP_KEY:
        case CompileTimeErrorCode.NON_CONSTANT_MAP_VALUE:
        case CompileTimeErrorCode.NON_CONSTANT_RECORD_FIELD:
        case CompileTimeErrorCode.NON_CONSTANT_SET_ELEMENT:
          hasConstError = true;
      }
    }
  }
}

/// A utility class for determining whether a given element is an expected
/// Flutter element.
///
/// See pkg/analysis_server/lib/src/utilities/flutter.dart.
abstract final class Flutter {
  static final _uriBasic = Uri.parse('package:flutter/src/widgets/basic.dart');
  static final _uriContainer =
      Uri.parse('package:flutter/src/widgets/container.dart');
  static final _uriFramework =
      Uri.parse('package:flutter/src/widgets/framework.dart');
  static final _uriFoundation =
      Uri.parse('package:flutter/src/foundation/constants.dart');

  static const _nameBuildContext = 'BuildContext';
  static const _nameContainer = 'Container';
  static const _nameSizedBox = 'SizedBox';
  static const _nameState = 'State';
  static const _nameStatefulWidget = 'StatefulWidget';
  static const _nameWidget = 'Widget';

  static bool hasWidgetAsAscendant(
    InterfaceElement? element, [
    Set<InterfaceElement>? alreadySeen,
  ]) {
    if (element == null) {
      return false;
    }

    if (isExactly(element, _nameWidget, _uriFramework)) {
      return true;
    }

    alreadySeen ??= {};
    if (!alreadySeen.add(element)) {
      return false;
    }

    final type =
        element.isAugmentation ? element.augmented.thisType : element.supertype;
    return hasWidgetAsAscendant(type?.element, alreadySeen);
  }

  static bool isBuildContext(DartType? type, {bool skipNullable = false}) {
    if (type is! InterfaceType) {
      return false;
    }
    if (skipNullable && type.nullabilitySuffix == NullabilitySuffix.question) {
      return false;
    }
    return isExactly(type.element, _nameBuildContext, _uriFramework);
  }

  /// Whether [element] is exactly the element named [type], from Flutter.
  static bool isExactly(InterfaceElement element, String type, Uri uri) =>
      element.name == type && element.source.uri == uri;

  static bool isExactWidget(ClassElement element) =>
      isExactly(element, _nameWidget, _uriFramework);

  static bool isExactWidgetTypeContainer(DartType? type) =>
      type is InterfaceType &&
      isExactly(type.element, _nameContainer, _uriContainer);

  static bool isExactWidgetTypeSizedBox(DartType? type) =>
      type is InterfaceType &&
      isExactly(type.element, _nameSizedBox, _uriBasic);

  static bool isKDebugMode(Element? element) =>
      element != null &&
      element.name == 'kDebugMode' &&
      element.source?.uri == _uriFoundation;

  static bool isState(InterfaceElement element) =>
      isExactly(element, _nameState, _uriFramework) ||
      element.allSupertypes
          .any((type) => isExactly(type.element, _nameState, _uriFramework));

  static bool isStatefulWidget(ClassElement element) =>
      isExactly(element, _nameStatefulWidget, _uriFramework) ||
      element.allSupertypes.any((type) =>
          isExactly(type.element, _nameStatefulWidget, _uriFramework));

  static bool isWidget(InterfaceElement element) {
    if (isExactly(element, _nameWidget, _uriFramework)) {
      return true;
    }
    for (final type in element.allSupertypes) {
      if (isExactly(type.element, _nameWidget, _uriFramework)) {
        return true;
      }
    }
    return false;
  }

  static bool isWidgetType(DartType? type) =>
      type is InterfaceType && isWidget(type.element);
}
