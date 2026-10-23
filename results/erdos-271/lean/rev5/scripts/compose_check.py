#!/usr/bin/env python3
"""Portable, fail-closed composition check for the C* checker bundles.
Usage: python3 compose_check.py <bundle_dir>
<bundle_dir> must contain b1,b5,b6,b7,b8a,b8b,b9 .statement.txt files (byte-exact checker inputs).
No sidecar files are used: every intermediate 'core' is derived from the statements themselves.
Checks: (1) sha256 of each statement equals the published (checker-verified) hash;
(2) each hypothesis of B7, B8a, B8b, B9 equals (after stripping outer newlines) the statement/conclusion it consumes;
(3) prints the derived final conclusion C9 and its sha256. Exits nonzero on any failure."""
import hashlib,sys,os
PUB={ # statement sha256 as verified by the Delegate checker (grok-release-checker-bundles.md section 0)
 'b1':'3dcb27598dd381d9a3a1ec520040ff14788472f2738e840d6747ac3c5eb341a6',
 'b5':'374514dcab31798eb0a98e9a82c54ed35e4622cc8cda036775aa6cd474883594',
 'b6':'64f9f246b5a0f11528679b3c98c85aeae60bae8b01ec99d7c6f01edbe9dedcd0',
 'b7':'33ec85e89e1dadec538ec8836f94a0a1696cabd8b15d9f59e88a1c58dc62e193',
 'b8a':'ed41ac1a711c7c022f84fb8571271aa96475e15bdc26c8c86fbb3d18963c241c',
 'b8b':'9aaa15e846915a3a4327150adfe42dafa450f4ead9c8b479d17a8c4b0a633f16',
 'b9':'fd0870189b96767e07f87e64e56f426d15c69983ceff3199569ad27bde1074f9'}
def fail(m): print('FAIL',m); sys.exit(1)
if len(sys.argv)!=2: fail('usage: compose_check.py <bundle_dir>')
D=sys.argv[1]; S={}
for n,h in PUB.items():
    p=os.path.join(D,n+'.statement.txt')
    if not os.path.isfile(p): fail('missing '+p)
    b=open(p,'rb').read(); got=hashlib.sha256(b).hexdigest()
    if got!=h: fail(f'{n} statement hash {got} != published {h}')
    print('OK   hash',n); S[n]=b.decode()
def hyps(stmt,k):
    out=[];i=0
    for _ in range(k):
        if stmt[i:i+2]!='(\n': fail('expected "(\\n" at offset %d'%i)
        d=0;j=i
        while True:
            if j>=len(stmt): fail('unbalanced parentheses')
            c=stmt[j]
            if c=='(': d+=1
            elif c==')':
                d-=1
                if d==0: break
            j+=1
        out.append(stmt[i+2:j]); i=j+1
        if stmt[i:i+3]!=' →\n': fail('expected " →\\n" after hypothesis at offset %d'%i)
        i+=3
    return out,stmt[i:]
st=lambda s:s.strip('\n')
def eq(name,a,b):
    if st(a)!=st(b): fail(name)
    print('OK  ',name)
h,C7=hyps(S['b7'],1);  eq('B7.hyp1 == B6',h[0],S['b6'])
h,C8a=hyps(S['b8a'],3); eq('B8a.hyp1 == B1',h[0],S['b1']); eq('B8a.hyp2 == B5',h[1],S['b5']); eq('B8a.hyp3 == concl(B7)',h[2],C7)
h,C8=hyps(S['b8b'],1); eq('B8b.hyp1 == concl(B8a)',h[0],C8a)
h,C9=hyps(S['b9'],1);  eq('B9.hyp1 == concl(B8b)',h[0],C8)
print('C9 sha256 (stripped, +newline):',hashlib.sha256((st(C9)+'\n').encode()).hexdigest())
print('composed : C9 := b9 (b8b (b8a b1 b5 (b7 b6)))')
print('ALL OK')
