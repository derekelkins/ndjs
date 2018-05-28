import resolve from 'rollup-plugin-node-resolve';
import typescript from 'rollup-plugin-typescript2';

export default {
    input: 'ndjs.ts',
    output: {
        file: 'bundle.js',
        format: 'iife',
        name: 'ndjs'
    },
    plugins: [
        resolve(),
        typescript()
    ]
};
