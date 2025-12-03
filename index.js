import * as wasm from './js/compiler_rs_lib.js';

wasm.default('./js/compiler_rs_lib_bg.wasm')
    .then(() => {
        const result = wasm.lex("123"); 
        const root = document.getElementById("root");
        root.innerText = JSON.stringify(result);

    })
    .catch(error => {
        console.error("Error loading WASM module:", error);
    });
