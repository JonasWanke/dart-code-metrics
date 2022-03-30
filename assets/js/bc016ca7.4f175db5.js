"use strict";(self.webpackChunkdart_code_metrics_website=self.webpackChunkdart_code_metrics_website||[]).push([[138],{3905:function(e,n,r){r.d(n,{Zo:function(){return u},kt:function(){return d}});var t=r(7294);function o(e,n,r){return n in e?Object.defineProperty(e,n,{value:r,enumerable:!0,configurable:!0,writable:!0}):e[n]=r,e}function i(e,n){var r=Object.keys(e);if(Object.getOwnPropertySymbols){var t=Object.getOwnPropertySymbols(e);n&&(t=t.filter((function(n){return Object.getOwnPropertyDescriptor(e,n).enumerable}))),r.push.apply(r,t)}return r}function a(e){for(var n=1;n<arguments.length;n++){var r=null!=arguments[n]?arguments[n]:{};n%2?i(Object(r),!0).forEach((function(n){o(e,n,r[n])})):Object.getOwnPropertyDescriptors?Object.defineProperties(e,Object.getOwnPropertyDescriptors(r)):i(Object(r)).forEach((function(n){Object.defineProperty(e,n,Object.getOwnPropertyDescriptor(r,n))}))}return e}function c(e,n){if(null==e)return{};var r,t,o=function(e,n){if(null==e)return{};var r,t,o={},i=Object.keys(e);for(t=0;t<i.length;t++)r=i[t],n.indexOf(r)>=0||(o[r]=e[r]);return o}(e,n);if(Object.getOwnPropertySymbols){var i=Object.getOwnPropertySymbols(e);for(t=0;t<i.length;t++)r=i[t],n.indexOf(r)>=0||Object.prototype.propertyIsEnumerable.call(e,r)&&(o[r]=e[r])}return o}var s=t.createContext({}),l=function(e){var n=t.useContext(s),r=n;return e&&(r="function"==typeof e?e(n):a(a({},n),e)),r},u=function(e){var n=l(e.components);return t.createElement(s.Provider,{value:n},e.children)},p={inlineCode:"code",wrapper:function(e){var n=e.children;return t.createElement(t.Fragment,{},n)}},f=t.forwardRef((function(e,n){var r=e.components,o=e.mdxType,i=e.originalType,s=e.parentName,u=c(e,["components","mdxType","originalType","parentName"]),f=l(r),d=o,m=f["".concat(s,".").concat(d)]||f[d]||p[d]||i;return r?t.createElement(m,a(a({ref:n},u),{},{components:r})):t.createElement(m,a({ref:n},u))}));function d(e,n){var r=arguments,o=n&&n.mdxType;if("string"==typeof e||o){var i=r.length,a=new Array(i);a[0]=f;var c={};for(var s in n)hasOwnProperty.call(n,s)&&(c[s]=n[s]);c.originalType=e,c.mdxType="string"==typeof e?e:o,a[1]=c;for(var l=2;l<i;l++)a[l]=r[l];return t.createElement.apply(null,a)}return t.createElement.apply(null,r)}f.displayName="MDXCreateElement"},4237:function(e,n,r){r.r(n),r.d(n,{assets:function(){return u},contentTitle:function(){return s},default:function(){return d},frontMatter:function(){return c},metadata:function(){return l},toc:function(){return p}});var t=r(7462),o=r(3366),i=(r(7294),r(3905)),a=["components"],c={},s="Prefer conditional expressions",l={unversionedId:"rules/common/prefer-conditional-expressions",id:"rules/common/prefer-conditional-expressions",title:"Prefer conditional expressions",description:"Has auto-fix",source:"@site/docs/rules/common/prefer-conditional-expressions.md",sourceDirName:"rules/common",slug:"/rules/common/prefer-conditional-expressions",permalink:"/docs/rules/common/prefer-conditional-expressions",editUrl:"https://github.com/dart-code-checker/dart-code-metrics/tree/master/website/docs/rules/common/prefer-conditional-expressions.md",tags:[],version:"current",frontMatter:{},sidebar:"sidebar",previous:{title:"Prefer async await",permalink:"/docs/rules/common/prefer-async-await"},next:{title:"Prefer correct identifier length",permalink:"/docs/rules/common/prefer-correct-identifier-length"}},u={},p=[{value:"Rule id",id:"rule-id",level:2},{value:"Severity",id:"severity",level:2},{value:"Description",id:"description",level:2},{value:"Example",id:"example",level:3}],f={toc:p};function d(e){var n=e.components,r=(0,o.Z)(e,a);return(0,i.kt)("wrapper",(0,t.Z)({},f,r,{components:n,mdxType:"MDXLayout"}),(0,i.kt)("h1",{id:"prefer-conditional-expressions"},"Prefer conditional expressions"),(0,i.kt)("p",null,(0,i.kt)("img",{parentName:"p",src:"https://img.shields.io/badge/-has%20auto--fix-success",alt:"Has auto-fix"})),(0,i.kt)("h2",{id:"rule-id"},"Rule id"),(0,i.kt)("p",null,"prefer-conditional-expressions"),(0,i.kt)("h2",{id:"severity"},"Severity"),(0,i.kt)("p",null,"Style"),(0,i.kt)("h2",{id:"description"},"Description"),(0,i.kt)("p",null,"Recommends to use a conditional expression instead of assigning to the same thing or return statement in each branch of an if statement."),(0,i.kt)("h3",{id:"example"},"Example"),(0,i.kt)("p",null,"Bad:"),(0,i.kt)("pre",null,(0,i.kt)("code",{parentName:"pre",className:"language-dart"},"  int a = 0;\n\n  // LINT\n  if (a > 0) {\n    a = 1;\n  } else {\n    a = 2;\n  }\n\n  // LINT\n  if (a > 0) a = 1;\n  else a = 2;\n\n  int function() {\n    // LINT\n    if (a == 1) {\n        return 0;\n    } else {\n        return 1;\n    }\n\n    // LINT\n    if (a == 2) return 0;\n    else return 1;\n  }\n")),(0,i.kt)("p",null,"Good:"),(0,i.kt)("pre",null,(0,i.kt)("code",{parentName:"pre",className:"language-dart"},"  int a = 0;\n\n  a = a > 0 ? 1 : 2;\n\n  int function() {\n    return a == 2 ? 0 : 1;\n  }\n")))}d.isMDXComponent=!0}}]);