type Json = any

/**
 * Expands a JSON object produced by [[cse]] into a JavaScript object whose object-level
 * sharing matches that encoded by the input JSON object.
 *
 * @param json A JSON object produced by [[cse]].
 * @param valueField Should match `valueField` as used by [[cse]].
 * @param cseField Should match `cseField` as used by [[cse]].
 * @param refField Should match `refField` as used by [[cse]].
 * @returns The JSON object encoded by `json`.
 */
export function expandCse(json: Json, valueField = '_value', cseField = '_cse', refField = '_r'): Json {
    if(typeof json !== 'object') return json;
    if(json === null || json[cseField] === void(0)) return json;
    const cse = json[cseField];
    return expandRec(json[valueField], cse, new Array(cse.length), refField);
}

/**
 * Identifies structurally equivalent subexpressions of the input JSON object and replaces them
 * with explicit references. It does not common up strings or other atomic expressions. If
 * `useSharing` is `true` it will use pointer equality to attempt to speed up the common subexpression
 * recognition. This can exponentially improve speed and space usage when there are a lot of nested
 * shared objects. However, it can hurt performance if the input has no object-level sharing. It does
 * not change the result in any way though.
 *
 *      cse([{foo: [1], bar: [1]},{foo: [1], bar: [1]}])
 *
 * produces
 *
 *      {_cse: [{foo: {_r: 1}, bar: {_r: 1}},[1]], _value: [{_r: 0}, {_r: 0}]}
 *
 * When [[expandCse]] is applied to the above output, it will produce an JavaScript object whose
 * sharing is equivalent to the following:
 *
 *      const r1 = [1];
 *      const r0 = [r1, r1];
 *      const result = [r0, r0];
 *
 * Anything in the `_cse` array will only be represented by a single JavaScript object.
 *  
 * This will loop forever if given an input with cyclic references.
 *
 * @param json A JSON object.
 * @param useSharing Exploit object identity to recognize shared subexpressions.
 * @param valueField A field name which does not appear in `json` distinct from `cseField`.
 * @param cseField A field name which does not appear in `json` distinct from `valueField`.
 * @param refField A field name which does not appear in `json`. This field will be used potentially
 *                 many times, so shorter is better.
 * @returns A JSON object encoding `json` with common subexpressions explicitly represented.
 */
export function cse(json: Json, useSharing = true, valueField = '_value', cseField = '_cse', refField = '_r'): Json {
    const cseTemp: Array<Json> = [];
    const reused: Array<boolean> = [];
    if(typeof json === 'object') {
        if(json === null) return null;
        const intermediate = useSharing ? cseRecWithSharing(json, JsonTrie.create(), cseTemp, reused, [], refField)
                                        : cseRec(json, JsonTrie.create(), cseTemp, reused, refField);
        const cse: Array<Json> = [];
        const result = reconstitute(intermediate, cseTemp, cse, reused, refField);
        return cse.length === 0 ? json : {[valueField]: result, [cseField]: cse};
    } else {
        return json;
    }
}

function expandRec(json: Json, cse: Array<object>, reformed: Array<Json>, refField: string): Json {
    const type = typeof json;
    if(type === 'object') {
        if(json === null) return null;
        const ix: number | undefined = json[refField];
        if(ix !== void(0)) {
            const t = reformed[ix];
            if(t !== void(0)) return t;
            return reformed[ix] = expandRec(cse[ix], cse, reformed, refField);
        }
        if(json instanceof Array) {
            const len = json.length;
            const t = new Array(json.length);
            for(let i = 0; i < len; ++i) {
                t[i] = expandRec(json[i], cse, reformed, refField);
            }
            return t;
        } else {
            const keys = Object.keys(json);
            const len = keys.length;
            const t: any = {};
            for(let i = 0; i < len; ++i) {
                const k = keys[i];
                t[k] = expandRec(json[k], cse, reformed, refField);
            }
            return t;
        }
    } else {
        return json;
    }
}

class JsonTrie {
    private readonly trie: any = {};
    private count: number = 1;

    static create(): JsonTrie {
        return new JsonTrie();
    }

    insert(key: Json): number {
        return this.insertRec(key, void(0), this.trie);
    }

    private insertRec(key: Json, val: any, curr: any, root: boolean = true): any {
        const type = typeof key;
        if(type === 'object') {
            if(key === null) {
                if(root) return 'null' in curr ? -curr.null : curr.null = this.count++;
                let node = curr.null;
                if(node === void(0)) curr.null = node = val;
                return node;
            } else if(key instanceof Array) {
                let node = curr.array;
                if(node === void(0)) curr.array = node = {};
                const len = key.length;
                for(let i = 0; i < len; ++i) {
                    node = this.insertRec(key[i], {}, node, false);
                }
                if(root) return 'empty' in node ? -node.empty : node.empty = this.count++;
                let node2 = node.empty;
                if(node2 === void(0)) node.empty = node2 = val;
                return node2;
            } else { // it's an object
                let node = curr.object;
                if(node === void(0)) curr.object = node = {};
                const keys = Object.keys(key).sort();
                const len = keys.length;
                for(let i = 0; i < len; ++i) {
                    const k = keys[i];
                    let node2 = node.more;
                    if(node2 === void(0)) node.more = node2 = {};
                    let node3 = node2[k];
                    if(node3 === void(0)) node2[k] = node3 = {};
                    node = this.insertRec(key[k], {}, node3, false);
                }
                if(root) return 'empty' in node ? -node.empty : node.empty = this.count++;
                let node2 = node.empty;
                if(node2 === void(0)) node.empty = node2 = val;
                return node2;
            }
        } else if(type === 'undefined') {
            if(root) return 'undefined' in curr ? -curr.undefined : curr.undefined = this.count++;
            let node = curr.undefined;
            if(node === void(0)) curr.undefined = node = val;
            return node;
        } else {
            let node = curr[type];
            if(node === void(0)) curr[type] = node = {};
            if(root) return key in node ? -node[key] : node[key] = this.count++;
            let node2 = node[key];
            if(node2 === void(0)) node[key] = node2 = val;
            return node2;
        }
    }
}

function cseRecWithSharing(key: Json, trie: JsonTrie, cse: Array<Json>, reused: Array<boolean>, seen: Array<[Json, object]>, refField: string): Json {
    const type = typeof key;
    if(type === 'object') {
        if(key === null) return null;
        const seenLen = seen.length;
        for(let i = 0; i < seenLen; ++i) {
            const p = seen[i];
            if(key === p[0]) {
                const r: any = p[1];
                reused[r[refField]] = true;
                return r;
            }
        }
        if(key instanceof Array) {
            const len = key.length;
            const result = new Array(len);
            for(let i = 0; i < len; ++i) {
                result[i] = cseRecWithSharing(key[i], trie, cse, reused, seen, refField);
            }
            const ix = trie.insert(result);
            if(ix < 0) {
                reused[-ix-1] = true;
                return {[refField]: -ix-1};
            } else {
                cse[ix-1] = result;
                const r = {[refField]: ix-1};
                seen.push([key, r]);
                return r;
            }
        } else { // it's an object
            const keys = Object.keys(key);
            const len = keys.length;
            const result: Json = {};
            for(let i = 0; i < len; ++i) {
                const k = keys[i];
                result[k] = cseRecWithSharing(key[k], trie, cse, reused, seen, refField);
            }
            const ix = trie.insert(result);
            if(ix < 0) {
                reused[-ix-1] = true;
                return {[refField]: -ix-1};
            } else {
                cse[ix-1] = result;
                const r = {[refField]: ix-1};
                seen.push([key, r]);
                return r;
            }
        }
    } else { // it's atomic
        return key;
    }
}

function cseRec(key: Json, trie: JsonTrie, cse: Array<Json>, reused: Array<boolean>, refField: string): Json {
    const type = typeof key;
    if(type === 'object') {
        if(key === null) return null;
        if(key instanceof Array) {
            const len = key.length;
            const result = new Array(len);
            for(let i = 0; i < len; ++i) {
                result[i] = cseRec(key[i], trie, cse, reused, refField);
            }
            const ix = trie.insert(result);
            if(ix < 0) {
                reused[-ix-1] = true;
                return {[refField]: -ix-1};
            } else {
                cse[ix-1] = result;
                const r = {[refField]: ix-1};
                return r;
            }
        } else { // it's an object
            const keys = Object.keys(key);
            const len = keys.length;
            const result: Json = {};
            for(let i = 0; i < len; ++i) {
                const k = keys[i];
                result[k] = cseRec(key[k], trie, cse, reused, refField);
            }
            const ix = trie.insert(result);
            if(ix < 0) {
                reused[-ix-1] = true;
                return {[refField]: -ix-1};
            } else {
                cse[ix-1] = result;
                const r = {[refField]: ix-1};
                return r;
            }
        }
    } else { // it's atomic
        return key;
    }
}

function reconstitute(intermediate: Json, cseTemp: Array<Json | number>, cse: Array<object>, reused: Array<boolean>, refField: string): Json {
    const type = typeof intermediate;
    if(type === 'object') {
        if(intermediate === null) return null;
        const ix: number = intermediate[refField];
        if(reused[ix]) {
            const t = cseTemp[ix];
            if(typeof t === 'number') { // use this new index
                return {[refField]: t}
            } else { // it's an object and this is our first time seeing it
                const newIx = cse.length;
                cse.push(t);
                cseTemp[ix] = newIx;

                if(t instanceof Array) {
                    const len = t.length;
                    for(let i = 0; i < len; ++i) {
                        t[i] = reconstitute(t[i], cseTemp, cse, reused, refField);
                    }
                } else {
                    const keys = Object.keys(t);
                    const len = keys.length;
                    for(let i = 0; i < len; ++i) {
                        const k = keys[i];
                        t[k] = reconstitute(t[k], cseTemp, cse, reused, refField);
                    }
                }

                return {[refField]: newIx};
            }
        } else {
            const tmp = cseTemp[ix];
            if(tmp instanceof Array) {
                const len = tmp.length;
                for(let i = 0; i < len; ++i) {
                    tmp[i] = reconstitute(tmp[i], cseTemp, cse, reused, refField);
                }
                return tmp;
            } else {
                const tmp: Json = cseTemp[ix];
                const keys = Object.keys(tmp);
                const len = keys.length;
                for(let i = 0; i < len; ++i) {
                    const k = keys[i];
                    tmp[k] = reconstitute(tmp[k], cseTemp, cse, reused, refField);
                }
                return tmp;
            }
        }
    } else {
        return intermediate;
    }
}
