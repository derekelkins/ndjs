import resolve from 'rollup-plugin-node-resolve';
import typescript from 'rollup-plugin-typescript2';

export default {
    //input: 'ndjs.js',
    //entry: 'ndjs.ts',
    input: 'ndjs.ts',
    output: {
        file: 'bundle.js',
        format: 'iife'
    },
    plugins: [
        resolve(),
        typescript()
    ]
};
