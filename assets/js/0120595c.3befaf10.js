"use strict";(self.webpackChunkdart_code_metrics_website=self.webpackChunkdart_code_metrics_website||[]).push([[598],{3905:(e,t,n)=>{n.d(t,{Zo:()=>u,kt:()=>m});var r=n(7294);function i(e,t,n){return t in e?Object.defineProperty(e,t,{value:n,enumerable:!0,configurable:!0,writable:!0}):e[t]=n,e}function a(e,t){var n=Object.keys(e);if(Object.getOwnPropertySymbols){var r=Object.getOwnPropertySymbols(e);t&&(r=r.filter((function(t){return Object.getOwnPropertyDescriptor(e,t).enumerable}))),n.push.apply(n,r)}return n}function o(e){for(var t=1;t<arguments.length;t++){var n=null!=arguments[t]?arguments[t]:{};t%2?a(Object(n),!0).forEach((function(t){i(e,t,n[t])})):Object.getOwnPropertyDescriptors?Object.defineProperties(e,Object.getOwnPropertyDescriptors(n)):a(Object(n)).forEach((function(t){Object.defineProperty(e,t,Object.getOwnPropertyDescriptor(n,t))}))}return e}function l(e,t){if(null==e)return{};var n,r,i=function(e,t){if(null==e)return{};var n,r,i={},a=Object.keys(e);for(r=0;r<a.length;r++)n=a[r],t.indexOf(n)>=0||(i[n]=e[n]);return i}(e,t);if(Object.getOwnPropertySymbols){var a=Object.getOwnPropertySymbols(e);for(r=0;r<a.length;r++)n=a[r],t.indexOf(n)>=0||Object.prototype.propertyIsEnumerable.call(e,n)&&(i[n]=e[n])}return i}var s=r.createContext({}),d=function(e){var t=r.useContext(s),n=t;return e&&(n="function"==typeof e?e(t):o(o({},t),e)),n},u=function(e){var t=d(e.components);return r.createElement(s.Provider,{value:t},e.children)},c={inlineCode:"code",wrapper:function(e){var t=e.children;return r.createElement(r.Fragment,{},t)}},p=r.forwardRef((function(e,t){var n=e.components,i=e.mdxType,a=e.originalType,s=e.parentName,u=l(e,["components","mdxType","originalType","parentName"]),p=d(n),m=i,g=p["".concat(s,".").concat(m)]||p[m]||c[m]||a;return n?r.createElement(g,o(o({ref:t},u),{},{components:n})):r.createElement(g,o({ref:t},u))}));function m(e,t){var n=arguments,i=t&&t.mdxType;if("string"==typeof e||i){var a=n.length,o=new Array(a);o[0]=p;var l={};for(var s in t)hasOwnProperty.call(t,s)&&(l[s]=t[s]);l.originalType=e,l.mdxType="string"==typeof e?e:i,o[1]=l;for(var d=2;d<a;d++)o[d]=n[d];return r.createElement.apply(null,o)}return r.createElement.apply(null,n)}p.displayName="MDXCreateElement"},9729:(e,t,n)=>{n.d(t,{Z:()=>a});var r=n(7294),i=n(5321);function a(e){let{version:t,severity:n,hasConfig:a,hasFix:o,isDeprecated:l}=e;return r.createElement("div",{className:"single-rule-info"},r.createElement(i.Z,{version:t,severity:n,hasConfig:a,hasFix:o,isDeprecated:l}))}},5321:(e,t,n)=>{n.d(t,{Z:()=>a});var r=n(7294);function i(e){let{hasConfig:t,hasFix:n,isDeprecated:i}=e;return r.createElement("div",{className:"rule-options"},t&&r.createElement("span",{title:"Configurable"},"\u2699\ufe0f"),n&&r.createElement("span",{title:"Has auto-fix"},"\ud83d\udee0"),i&&r.createElement("span",{title:"Deprecated"},"\u26a0\ufe0f"))}function a(e){let{severity:t,version:n,hasConfig:a,hasFix:o,isDeprecated:l}=e;const s=null==t?void 0:t.toLowerCase();return r.createElement("div",{className:"rule-additional-info"},r.createElement("div",null,r.createElement("span",{className:"added-in-label"},"added in:")," ",n),r.createElement("div",{className:`rule-severity ${s}`},s),r.createElement(i,{hasConfig:a,hasFix:o,isDeprecated:l}))}},6812:(e,t,n)=>{n.r(t),n.d(t,{assets:()=>d,contentTitle:()=>l,default:()=>p,frontMatter:()=>o,metadata:()=>s,toc:()=>u});var r=n(7462),i=(n(7294),n(3905)),a=n(9729);const o={},l=void 0,s={unversionedId:"rules/flutter/avoid-returning-widgets",id:"rules/flutter/avoid-returning-widgets",title:"avoid-returning-widgets",description:"Warns when a method, function or getter returns a Widget or subclass of a Widget.",source:"@site/docs/rules/flutter/avoid-returning-widgets.mdx",sourceDirName:"rules/flutter",slug:"/rules/flutter/avoid-returning-widgets",permalink:"/docs/rules/flutter/avoid-returning-widgets",draft:!1,editUrl:"https://github.com/dart-code-checker/dart-code-metrics/tree/master/website/docs/rules/flutter/avoid-returning-widgets.mdx",tags:[],version:"current",frontMatter:{},sidebar:"sidebar",previous:{title:"avoid-border-all",permalink:"/docs/rules/flutter/avoid-border-all"},next:{title:"avoid-shrink-wrap-in-lists",permalink:"/docs/rules/flutter/avoid-shrink-wrap-in-lists"}},d={},u=[{value:"\u2699\ufe0f Config example",id:"config-example",level:3},{value:"Example",id:"example",level:3}],c={toc:u};function p(e){let{components:t,...n}=e;return(0,i.kt)("wrapper",(0,r.Z)({},c,n,{components:t,mdxType:"MDXLayout"}),(0,i.kt)(a.Z,{version:"3.1.0",severity:"warning",hasConfig:!0,mdxType:"RuleDetails"}),(0,i.kt)("p",null,"Warns when a method, function or getter returns a Widget or subclass of a Widget."),(0,i.kt)("p",null,"Extracting widgets to a method is considered as a Flutter anti-pattern, because when Flutter rebuilds widget tree, it calls the function all the time, making more processor time for the operations."),(0,i.kt)("p",null,"Consider creating a separate widget instead of a function or method."),(0,i.kt)("admonition",{type:"info"},(0,i.kt)("p",{parentName:"admonition"},"The following patterns will not trigger the rule:"),(0,i.kt)("ul",{parentName:"admonition"},(0,i.kt)("li",{parentName:"ul"},"Widget ",(0,i.kt)("inlineCode",{parentName:"li"},"build")," method overrides."),(0,i.kt)("li",{parentName:"ul"},"Class method that is passed to a builder."),(0,i.kt)("li",{parentName:"ul"},"Functions with ",(0,i.kt)("a",{parentName:"li",href:"https://pub.dev/packages/functional_widget"},"functional_widget")," package annotations."))),(0,i.kt)("p",null,"Additional resources:"),(0,i.kt)("ul",null,(0,i.kt)("li",{parentName:"ul"},(0,i.kt)("a",{parentName:"li",href:"https://github.com/flutter/flutter/issues/19269"},"https://github.com/flutter/flutter/issues/19269")),(0,i.kt)("li",{parentName:"ul"},(0,i.kt)("a",{parentName:"li",href:"https://flutter.dev/docs/perf/rendering/best-practices#controlling-build-cost"},"https://flutter.dev/docs/perf/rendering/best-practices#controlling-build-cost")),(0,i.kt)("li",{parentName:"ul"},(0,i.kt)("a",{parentName:"li",href:"https://www.reddit.com/r/FlutterDev/comments/avhvco/extracting_widgets_to_a_function_is_not_an/"},"https://www.reddit.com/r/FlutterDev/comments/avhvco/extracting_widgets_to_a_function_is_not_an/")),(0,i.kt)("li",{parentName:"ul"},(0,i.kt)("a",{parentName:"li",href:"https://medium.com/flutter-community/splitting-widgets-to-methods-is-a-performance-antipattern-16aa3fb4026c"},"https://medium.com/flutter-community/splitting-widgets-to-methods-is-a-performance-antipattern-16aa3fb4026c"))),(0,i.kt)("p",null,"Use ",(0,i.kt)("inlineCode",{parentName:"p"},"ignored-names")," configuration, if you want to ignore a function or method name."),(0,i.kt)("p",null,"Use ",(0,i.kt)("inlineCode",{parentName:"p"},"ignored-annotations")," configuration, if you want to override default ignored annotation list."),(0,i.kt)("h3",{id:"config-example"},"\u2699\ufe0f Config example"),(0,i.kt)("pre",null,(0,i.kt)("code",{parentName:"pre",className:"language-yaml"},"dart_code_metrics:\n  ...\n  rules:\n    ...\n    - avoid-returning-widgets:\n        ignored-names:\n          - testFunction\n        ignored-annotations:\n          - allowedAnnotation\n")),(0,i.kt)("p",null,"will ignore all functions named ",(0,i.kt)("inlineCode",{parentName:"p"},"testFunction")," and all functions having ",(0,i.kt)("inlineCode",{parentName:"p"},"allowedAnnotation")," annotation."),(0,i.kt)("h3",{id:"example"},"Example"),(0,i.kt)("p",null,(0,i.kt)("strong",{parentName:"p"},"\u274c Bad:")),(0,i.kt)("pre",null,(0,i.kt)("code",{parentName:"pre",className:"language-dart"},"class MyWidget extends StatelessWidget {\n  const MyWidget();\n\n  // LINT\n  Widget _getWidget() => Container();\n\n  Widget _buildShinyWidget() {\n    return Container(\n      child: Column(\n        children: [\n          Text('Hello'),\n          ...\n        ],\n      ),\n    );\n  }\n\n  @override\n  Widget build(BuildContext context) {\n    return Row(\n      children: [\n        Text('Text!'),\n        ...\n        _buildShinyWidget(), // LINT\n      ],\n    );\n  }\n}\n")),(0,i.kt)("p",null,(0,i.kt)("strong",{parentName:"p"},"\u2705 Good:")),(0,i.kt)("pre",null,(0,i.kt)("code",{parentName:"pre",className:"language-dart"},"class MyWidget extends StatelessWidget {\n  const MyWidget();\n\n  @override\n  Widget build(BuildContext context) {\n    return Row(\n      children: [\n        Text('Text!'),\n        ...\n        const _MyShinyWidget(),\n      ],\n    );\n  }\n}\n\nclass _MyShinyWidget extends StatelessWidget {\n  const _MyShinyWidget();\n\n  @override\n  Widget build(BuildContext context) {\n    return Container(\n      child: Column(\n        children: [\n          Text('Hello'),\n          ...\n        ],\n      ),\n    );\n  }\n}\n")),(0,i.kt)("p",null,(0,i.kt)("strong",{parentName:"p"},"\u2705 Good:")),(0,i.kt)("pre",null,(0,i.kt)("code",{parentName:"pre",className:"language-dart"},"class MyWidget extends StatelessWidget {\n  Widget _buildMyWidget(BuildContext context) {\n    return Container();\n  }\n\n  @override\n  Widget build(BuildContext context) {\n    return Builder(\n      builder: _buildMyWidget,\n    );\n  }\n}\n")))}p.isMDXComponent=!0}}]);