"use strict";(self.webpackChunkdart_code_metrics_website=self.webpackChunkdart_code_metrics_website||[]).push([[8981],{3905:(e,t,r)=>{r.d(t,{Zo:()=>p,kt:()=>f});var n=r(7294);function i(e,t,r){return t in e?Object.defineProperty(e,t,{value:r,enumerable:!0,configurable:!0,writable:!0}):e[t]=r,e}function l(e,t){var r=Object.keys(e);if(Object.getOwnPropertySymbols){var n=Object.getOwnPropertySymbols(e);t&&(n=n.filter((function(t){return Object.getOwnPropertyDescriptor(e,t).enumerable}))),r.push.apply(r,n)}return r}function a(e){for(var t=1;t<arguments.length;t++){var r=null!=arguments[t]?arguments[t]:{};t%2?l(Object(r),!0).forEach((function(t){i(e,t,r[t])})):Object.getOwnPropertyDescriptors?Object.defineProperties(e,Object.getOwnPropertyDescriptors(r)):l(Object(r)).forEach((function(t){Object.defineProperty(e,t,Object.getOwnPropertyDescriptor(r,t))}))}return e}function o(e,t){if(null==e)return{};var r,n,i=function(e,t){if(null==e)return{};var r,n,i={},l=Object.keys(e);for(n=0;n<l.length;n++)r=l[n],t.indexOf(r)>=0||(i[r]=e[r]);return i}(e,t);if(Object.getOwnPropertySymbols){var l=Object.getOwnPropertySymbols(e);for(n=0;n<l.length;n++)r=l[n],t.indexOf(r)>=0||Object.prototype.propertyIsEnumerable.call(e,r)&&(i[r]=e[r])}return i}var s=n.createContext({}),c=function(e){var t=n.useContext(s),r=t;return e&&(r="function"==typeof e?e(t):a(a({},t),e)),r},p=function(e){var t=c(e.components);return n.createElement(s.Provider,{value:t},e.children)},u={inlineCode:"code",wrapper:function(e){var t=e.children;return n.createElement(n.Fragment,{},t)}},d=n.forwardRef((function(e,t){var r=e.components,i=e.mdxType,l=e.originalType,s=e.parentName,p=o(e,["components","mdxType","originalType","parentName"]),d=c(r),f=i,m=d["".concat(s,".").concat(f)]||d[f]||u[f]||l;return r?n.createElement(m,a(a({ref:t},p),{},{components:r})):n.createElement(m,a({ref:t},p))}));function f(e,t){var r=arguments,i=t&&t.mdxType;if("string"==typeof e||i){var l=r.length,a=new Array(l);a[0]=d;var o={};for(var s in t)hasOwnProperty.call(t,s)&&(o[s]=t[s]);o.originalType=e,o.mdxType="string"==typeof e?e:i,a[1]=o;for(var c=2;c<l;c++)a[c]=r[c];return n.createElement.apply(null,a)}return n.createElement.apply(null,r)}d.displayName="MDXCreateElement"},9729:(e,t,r)=>{r.d(t,{Z:()=>l});var n=r(7294),i=r(5321);function l(e){let{version:t,severity:r,hasConfig:l,hasFix:a,isDeprecated:o}=e;return n.createElement("div",{className:"single-rule-info"},n.createElement(i.Z,{version:t,severity:r,hasConfig:l,hasFix:a,isDeprecated:o}))}},5321:(e,t,r)=>{r.d(t,{Z:()=>l});var n=r(7294);function i(e){let{hasConfig:t,hasFix:r,isDeprecated:i}=e;return n.createElement("div",{className:"rule-options"},t&&n.createElement("span",{title:"Configurable"},"\u2699\ufe0f"),r&&n.createElement("span",{title:"Has auto-fix"},"\ud83d\udee0"),i&&n.createElement("span",{title:"Deprecated"},"\u26a0\ufe0f"))}function l(e){let{severity:t,version:r,hasConfig:l,hasFix:a,isDeprecated:o}=e;const s=null==t?void 0:t.toLowerCase();return n.createElement("div",{className:"rule-additional-info"},n.createElement("div",null,n.createElement("span",{className:"added-in-label"},"added in:")," ",r),n.createElement("div",{className:`rule-severity ${s}`},s),n.createElement(i,{hasConfig:l,hasFix:a,isDeprecated:o}))}},4208:(e,t,r)=>{r.r(t),r.d(t,{assets:()=>c,contentTitle:()=>o,default:()=>d,frontMatter:()=>a,metadata:()=>s,toc:()=>p});var n=r(7462),i=(r(7294),r(3905)),l=r(9729);const a={},o=void 0,s={unversionedId:"rules/flutter/prefer-using-list-view",id:"rules/flutter/prefer-using-list-view",title:"prefer-using-list-view",description:"Warns when a Column widget with only children parameter is wrapped in a SingleChildScrollView widget.",source:"@site/docs/rules/flutter/prefer-using-list-view.mdx",sourceDirName:"rules/flutter",slug:"/rules/flutter/prefer-using-list-view",permalink:"/docs/rules/flutter/prefer-using-list-view",draft:!1,editUrl:"https://github.com/dart-code-checker/dart-code-metrics/tree/master/website/docs/rules/flutter/prefer-using-list-view.mdx",tags:[],version:"current",frontMatter:{},sidebar:"sidebar",previous:{title:"prefer-single-widget-per-file",permalink:"/docs/rules/flutter/prefer-single-widget-per-file"},next:{title:"prefer-intl-name",permalink:"/docs/rules/intl/prefer-intl-name"}},c={},p=[{value:"Example",id:"example",level:3}],u={toc:p};function d(e){let{components:t,...r}=e;return(0,i.kt)("wrapper",(0,n.Z)({},u,r,{components:t,mdxType:"MDXLayout"}),(0,i.kt)(l.Z,{version:"5.2.0",severity:"performance",mdxType:"RuleDetails"}),(0,i.kt)("p",null,"Warns when a ",(0,i.kt)("inlineCode",{parentName:"p"},"Column")," widget with only ",(0,i.kt)("inlineCode",{parentName:"p"},"children")," parameter is wrapped in a ",(0,i.kt)("inlineCode",{parentName:"p"},"SingleChildScrollView")," widget."),(0,i.kt)("p",null,"Additional resources:"),(0,i.kt)("ul",null,(0,i.kt)("li",{parentName:"ul"},(0,i.kt)("a",{parentName:"li",href:"https://stackoverflow.com/a/62147092"},"https://stackoverflow.com/a/62147092"))),(0,i.kt)("h3",{id:"example"},"Example"),(0,i.kt)("p",null,(0,i.kt)("strong",{parentName:"p"},"\u274c Bad:")),(0,i.kt)("pre",null,(0,i.kt)("code",{parentName:"pre",className:"language-dart"},"SingleChildScrollView(\n  child: Column(\n    children: [\n      Text('Wow lint rule'),\n      Text('Wow another lint rule'),\n    ],\n  ),\n),\n")),(0,i.kt)("p",null,(0,i.kt)("strong",{parentName:"p"},"\u2705 Good:")),(0,i.kt)("pre",null,(0,i.kt)("code",{parentName:"pre",className:"language-dart"},"ListView(\n  children: [\n    Text('Wow lint rule'),\n    Text('Wow another lint rule'),\n  ],\n),\n")))}d.isMDXComponent=!0}}]);