#!/usr/bin/env python3
"""Fail-closed check (and generator) for Liminf1675.lean (rev 6 candidate).
Liminf1675.lean must be exactly HEADER + 'theorem liminf_construction_1675 :\n' + <statement> + ' :=\n' + <proof> + FOOTER,
with <statement>/<proof> the byte-exact checker inputs of Claude's job 042a1cf7-e251-4071-90f5-b1f384498329.
Usage: python3 scripts/check_c1675.py [--write]   (run from the package root)"""
import hashlib,sys
PUB={'statement':'f34ea2a577ba67182a137abd724314a1680934c5b5e52e9886a1145a90589836',
     'proof':'4cab2175f543161e3fff9819fb22bf70aa39920232f83be2bfbec39009ef81b3'}
HEADER='''import Mathlib

/-!
# Liminf at most 1675*sqrt(3)/1536 for a strong AP3-covering (Claude's single-term proof)

Statement and proof are inserted byte-for-byte from `checker-bundles/c1675.statement.txt` and
`checker-bundles/c1675.proof.txt`, the inputs of Delegate checker job 042a1cf7-e251-4071-90f5-b1f384498329
(statement sha256 f34ea2a5..., proof sha256 4cab2175...). Regenerate or verify with `scripts/check_c1675.py`.
This is a separate, later construction (seed chain extended to S_786432, 1672 elements). It does not
replace the frozen release theorem `Erdos271.Liminf.liminf_construction_1889` (419*sqrt(3)/384).
-/

namespace Erdos271.Liminf1675

'''
FOOTER='\n\nend Erdos271.Liminf1675\n'
def fail(m): print('FAIL',m); sys.exit(1)
b={}
for k,h in PUB.items():
    d=open(f'checker-bundles/c1675.{k}.txt','rb').read(); g=hashlib.sha256(d).hexdigest()
    if g!=h: fail(f'{k} sha256 {g} != published {h}')
    print('OK   hash',k); b[k]=d.decode('utf-8')
want=HEADER+'theorem liminf_construction_1675 :\n'+b['statement']+' :=\n'+b['proof']+FOOTER
if '--write' in sys.argv: open('Liminf1675.lean','w',encoding='utf-8').write(want); print('wrote Liminf1675.lean')
if open('Liminf1675.lean',encoding='utf-8').read()!=want: fail('Liminf1675.lean is not the exact embedding of the checker inputs')
print('OK   Liminf1675.lean embeds the checker inputs byte-for-byte')
print('ALL OK')
