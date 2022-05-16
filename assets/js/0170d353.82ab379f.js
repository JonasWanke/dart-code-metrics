"use strict";(self.webpackChunkdart_code_metrics_website=self.webpackChunkdart_code_metrics_website||[]).push([[2375],{3905:function(e,t,n){n.d(t,{Zo:function(){return c},kt:function(){return f}});var r=n(7294);function a(e,t,n){return t in e?Object.defineProperty(e,t,{value:n,enumerable:!0,configurable:!0,writable:!0}):e[t]=n,e}function o(e,t){var n=Object.keys(e);if(Object.getOwnPropertySymbols){var r=Object.getOwnPropertySymbols(e);t&&(r=r.filter((function(t){return Object.getOwnPropertyDescriptor(e,t).enumerable}))),n.push.apply(n,r)}return n}function l(e){for(var t=1;t<arguments.length;t++){var n=null!=arguments[t]?arguments[t]:{};t%2?o(Object(n),!0).forEach((function(t){a(e,t,n[t])})):Object.getOwnPropertyDescriptors?Object.defineProperties(e,Object.getOwnPropertyDescriptors(n)):o(Object(n)).forEach((function(t){Object.defineProperty(e,t,Object.getOwnPropertyDescriptor(n,t))}))}return e}function i(e,t){if(null==e)return{};var n,r,a=function(e,t){if(null==e)return{};var n,r,a={},o=Object.keys(e);for(r=0;r<o.length;r++)n=o[r],t.indexOf(n)>=0||(a[n]=e[n]);return a}(e,t);if(Object.getOwnPropertySymbols){var o=Object.getOwnPropertySymbols(e);for(r=0;r<o.length;r++)n=o[r],t.indexOf(n)>=0||Object.prototype.propertyIsEnumerable.call(e,n)&&(a[n]=e[n])}return a}var s=r.createContext({}),u=function(e){var t=r.useContext(s),n=t;return e&&(n="function"==typeof e?e(t):l(l({},t),e)),n},c=function(e){var t=u(e.components);return r.createElement(s.Provider,{value:t},e.children)},d={inlineCode:"code",wrapper:function(e){var t=e.children;return r.createElement(r.Fragment,{},t)}},p=r.forwardRef((function(e,t){var n=e.components,a=e.mdxType,o=e.originalType,s=e.parentName,c=i(e,["components","mdxType","originalType","parentName"]),p=u(n),f=a,m=p["".concat(s,".").concat(f)]||p[f]||d[f]||o;return n?r.createElement(m,l(l({ref:t},c),{},{components:n})):r.createElement(m,l({ref:t},c))}));function f(e,t){var n=arguments,a=t&&t.mdxType;if("string"==typeof e||a){var o=n.length,l=new Array(o);l[0]=p;var i={};for(var s in t)hasOwnProperty.call(t,s)&&(i[s]=t[s]);i.originalType=e,i.mdxType="string"==typeof e?e:a,l[1]=i;for(var u=2;u<o;u++)l[u]=n[u];return r.createElement.apply(null,l)}return r.createElement.apply(null,n)}p.displayName="MDXCreateElement"},9974:function(e,t,n){n.r(t),n.d(t,{assets:function(){return c},contentTitle:function(){return s},default:function(){return f},frontMatter:function(){return i},metadata:function(){return u},toc:function(){return d}});var r=n(7462),a=n(3366),o=(n(7294),n(3905)),l=["components"],i={},s="Check unused files",u={unversionedId:"cli/check-unused-files",id:"cli/check-unused-files",title:"Check unused files",description:"Checks unused *.dart files. To execute the command, run",source:"@site/docs/cli/check-unused-files.md",sourceDirName:"cli",slug:"/cli/check-unused-files",permalink:"/docs/cli/check-unused-files",draft:!1,editUrl:"https://github.com/dart-code-checker/dart-code-metrics/tree/master/website/docs/cli/check-unused-files.md",tags:[],version:"current",frontMatter:{},sidebar:"sidebar",previous:{title:"Check unused code",permalink:"/docs/cli/check-unused-code"},next:{title:"Check unused l10n",permalink:"/docs/cli/check-unused-l10n"}},c={},d=[{value:"Output example",id:"output-example",level:2},{value:"Console",id:"console",level:3},{value:"JSON",id:"json",level:3},{value:"The <strong>root</strong> object fields are",id:"the-root-object-fields-are",level:4},{value:"The <strong>unusedFiles</strong> object fields are",id:"the-unused-files-object-fields-are",level:4}],p={toc:d};function f(e){var t=e.components,i=(0,a.Z)(e,l);return(0,o.kt)("wrapper",(0,r.Z)({},p,i,{components:t,mdxType:"MDXLayout"}),(0,o.kt)("h1",{id:"check-unused-files"},"Check unused files"),(0,o.kt)("p",null,"Checks unused ",(0,o.kt)("inlineCode",{parentName:"p"},"*.dart")," files. To execute the command, run"),(0,o.kt)("pre",null,(0,o.kt)("code",{parentName:"pre",className:"language-sh"},"$ dart run dart_code_metrics:metrics check-unused-files lib\n\n# or for a Flutter package\n$ flutter pub run dart_code_metrics:metrics check-unused-files lib\n")),(0,o.kt)("p",null,"Full command description:"),(0,o.kt)("pre",null,(0,o.kt)("code",{parentName:"pre",className:"language-text"},'Usage: metrics check-unused-files [arguments...] <directories>\n\n-h, --help                                        Print this usage information.\n\n\n-r, --reporter=<console>                          The format of the output of the analysis.\n                                                  [console (default), json]\n\n\n    --root-folder=<./>                            Root folder.\n                                                  (defaults to current directory)\n    --sdk-path=<directory-path>                   Dart SDK directory path. \n                                                  Should be provided only when you run the application as compiled executable(https://dart.dev/tools/dart-compile#exe) and automatic Dart SDK path detection fails.\n    --exclude=<{/**.g.dart,/**.template.dart}>    File paths in Glob syntax to be exclude.\n                                                  (defaults to "{/**.g.dart,/**.template.dart}")\n\n\n    --no-congratulate                             Don\'t show output even when there are no issues.\n\n\n    --[no-]fatal-unused                           Treat find unused file as fatal.\n\n-d, --[no-]delete-files                           Delete all unused files.\n')),(0,o.kt)("h2",{id:"output-example"},"Output example"),(0,o.kt)("h3",{id:"console"},"Console"),(0,o.kt)("p",null,"Use ",(0,o.kt)("inlineCode",{parentName:"p"},"--reporter=console")," to enable this format."),(0,o.kt)("p",null,(0,o.kt)("img",{alt:"Console",src:n(5068).Z,width:"1540",height:"136"})),(0,o.kt)("h3",{id:"json"},"JSON"),(0,o.kt)("p",null,"The reporter prints a single JSON object containing meta information and the unused file paths. Use ",(0,o.kt)("inlineCode",{parentName:"p"},"--reporter=json")," to enable this format."),(0,o.kt)("h4",{id:"the-root-object-fields-are"},"The ",(0,o.kt)("strong",{parentName:"h4"},"root")," object fields are"),(0,o.kt)("ul",null,(0,o.kt)("li",{parentName:"ul"},(0,o.kt)("inlineCode",{parentName:"li"},"formatVersion")," - an integer representing the format version (will be incremented each time the serialization format changes)"),(0,o.kt)("li",{parentName:"ul"},(0,o.kt)("inlineCode",{parentName:"li"},"timestamp")," - a creation time of the report in YYYY-MM-DD HH:MM:SS format"),(0,o.kt)("li",{parentName:"ul"},(0,o.kt)("inlineCode",{parentName:"li"},"unusedFiles")," - an array of ",(0,o.kt)("a",{parentName:"li",href:"#the-unused-files-object-fields-are"},"unused files")),(0,o.kt)("li",{parentName:"ul"},(0,o.kt)("inlineCode",{parentName:"li"},"automaticallyDeleted")," - an indication of unused files being automatically deleted")),(0,o.kt)("pre",null,(0,o.kt)("code",{parentName:"pre",className:"language-JSON"},'{\n  "formatVersion": 2,\n  "timestamp": "2021-04-11 14:44:42",\n  "unusedFiles": [\n    {\n      ...\n    },\n    {\n      ...\n    },\n    {\n      ...\n    }\n  ],\n  "automaticallyDeleted": false\n}\n')),(0,o.kt)("h4",{id:"the-unused-files-object-fields-are"},"The ",(0,o.kt)("strong",{parentName:"h4"},"unusedFiles")," object fields are"),(0,o.kt)("ul",null,(0,o.kt)("li",{parentName:"ul"},(0,o.kt)("inlineCode",{parentName:"li"},"path")," - a relative path of the unused file")),(0,o.kt)("pre",null,(0,o.kt)("code",{parentName:"pre",className:"language-JSON"},'{\n  "path": "lib/src/some/file.dart",\n}\n')))}f.isMDXComponent=!0},5068:function(e,t,n){t.Z=n.p+"assets/images/unused-files-console-report-8823699e3f7a3d1dcec8bec0f613b204.png"}}]);