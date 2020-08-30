/*
 * Copyright 2017-2020 The ShadowEditor Authors. All rights reserved.
 *
 * Use of this source code is governed by a MIT-style
 * license that can be found in the LICENSE file.
 * 
 * For more information, please visit: https://github.com/tengge1/ShadowEditor
 * You can also visit: https://gitee.com/tengge1/ShadowEditor
 */
import commonjs from 'rollup-plugin-commonjs';
import resolve from 'rollup-plugin-node-resolve';
import postcss from 'rollup-plugin-postcss';
import babel from 'rollup-plugin-babel';

export default {
    input: 'src/index.js',
    output: {
        indent: '\t',
        format: 'umd',
        name: 'UI',
        file: 'build/editor-ui.js'
    },
    treeshake: true,
    external: [],
    plugins: [
        resolve(),
        commonjs({
            exclude: [
                'assets/**'
            ]
        }),
        postcss({
            extract: true
        }),
        babel({
            exclude: 'node_modules/**'
        })
    ],
    onwarn(warning, rollupWarn) {
        if (warning.code !== 'CIRCULAR_DEPENDENCY') {
            rollupWarn(warning);
        }
    }
};
