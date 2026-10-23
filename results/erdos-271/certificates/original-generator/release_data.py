#!/usr/bin/env python3
"""Frozen release data for the room-5 constructions (Claude).  Pure Python 3, exact arithmetic, no dependencies.
Prints canonical hashes.  Witness-table convention (matches ChatGPT #136 and the A' stream of #83/#99):
UTF-8 rows "n,a,b\\n" in increasing n, no header; for each n the witness with the smallest b (then a=2b-n)."""
import hashlib
from fractions import Fraction as F

def sha(s): return hashlib.sha256(s.encode()).hexdigest()

def witness_table(Aset, lo, hi, apos=True):
    S=sorted(Aset); rows=[]; bad=[]
    for n in range(lo,hi+1):
        found=None
        for b in S:
            if 2*b<=n: continue
            if b>=n: break
            a=2*b-n
            if (a>0 or not apos) and a in Aset:
                found=(a,b); break
        if found is None: bad.append(n)
        else: rows.append(f"{n},{found[0]},{found[1]}\n")
    return "".join(rows), bad

def digit_family(q,V,W,H):
    A=set(); tails=[0]; scale=1
    while min(W)*scale<=H:
        for w in W:
            for d in tails:
                x=w*scale+d
                if x<=H: A.add(x)
        tails=[d+v*scale for d in tails for v in V]; scale*=q
    return A

out={}
# ---------------- (I) limsup 17/6, base 16 ----------------
q,V,W=16,(8,11,12,15),(2,3,5,7,10,12,14,21,23,25,28)
N0=89; H=16*N0+22
res=sorted(((2*v1-v2)%16,2*v1-v2,v1,v2) for v1 in V for v2 in V)
assert [r[0] for r in res]==list(range(16))
out['17/6 residue table (r, t=2v1-v2, v1, v2)']=res
A16=digit_family(q,V,W,16**4)
canonA="".join(f"{x}\n" for x in sorted(A16))
out['17/6 A cap (0,16^4) count, sha256']=(len(A16),sha(canonA))
tab,bad=witness_table(A16,N0,H)
assert not bad
out['17/6 base window [89,1446] rows, sha256']=(tab.count("\n"),sha(tab))
nonmem=[n for n in range(1,16**4) if n not in A16 and witness_table(A16,n,n)[1]]
out['17/6 uncovered non-members (a>0) below 16^4']=nonmem
# cylinder certificate: integer-cleared rows
k=len(W); rows=[]; fails=[]
import itertools, math
for j,w in enumerate(W):
    c=F(k,3)+j
    for ds in itertools.product(range(4),repeat=4):
        g=sum(d*4**(3-i) for i,d in enumerate(ds))            # sum d_i 4^{4-i}  (i=1..4)
        rho=sum(V[d]*16**(3-i) for i,d in enumerate(ds))      # sum v_i 16^{4-i}
        N1=256*(k+3*j)+3*(g+1)                                 # c+G_end = N1/768
        N2=15*65536*w+15*rho+8                                 # w+rho_start = N2/(15*65536)
        lhs=36*15*65536*N1*N1; rhs=289*768*768*N2
        assert F(N1,768)==c+F(g+1,256) and F(N2,15*65536)==w+F(rho,65536)+F(8,15*65536)
        rows.append(f"{j},{w},{ds[0]}{ds[1]}{ds[2]}{ds[3]},{lhs},{rhs}\n")
        if lhs>rhs: fails.append((w,ds))
cyl="".join(rows)
out['17/6 cylinder rows (11*256), failing cylinders, sha256']=(len(rows),fails,sha(cyl))
# largest passing bound (as decimal)
mx=0
for j,w in enumerate(W):
    c=F(k,3)+j
    for ds in itertools.product(range(4),repeat=4):
        if (w,ds) in fails: continue
        g=sum(d*4**(3-i) for i,d in enumerate(ds)); rho=sum(V[d]*16**(3-i) for i,d in enumerate(ds))
        val=float(c+F(g+1,256))/math.sqrt(float(w+F(rho,65536)+F(8,15*65536)))
        mx=max(mx,val)
out['17/6 largest passing cylinder bound']=round(mx,6)
open('/tmp/rel/w16_base_window.csv','w').write(tab); open('/tmp/rel/cyl16_rows.csv','w').write(cyl)

# ---------------- (II) limsup sqrt(588/73), base 4 ----------------
A4=digit_family(4,(0,1),(9,10,16,19,20,23,24),4*4737)
tab4,bad4=witness_table(A4,1182,4737)
assert not bad4
out["A' base window [1182,4737] rows, sha256"]=(tab4.count("\n"),sha(tab4))

# ---------------- (III) liminf static certificates ----------------
L=lambda T:{4*t+v for t in T for v in (0,1)}
S768={1,2,3,4,5,8,9,12,13,16,21,24,33,36,41,44,45,48,53,56,77,80,85,88,129,132,137,140,
      161,164,169,172,253,256,261,264,271,301,304,309,312,340,345,348,353,356,377,380,385,388}
S192={1,2,3,4,6,9,11,12,14,20,22,33,35,41,43,49,63,74,76,82,88,94,96,102}
S3072={1,2,3,12}|L(S768-{3})
S49152=(L(L(S3072)|{1,2,3})|{1,2,3})-{13}
for name,S,X in [("S192",S192,192),("S768",S768,768),("S3072",S3072,3072),("S49152",S49152,49152)]:
    canon="".join(f"{x}\n" for x in sorted(S))
    tb,bd=witness_table(S,3,X)
    assert not bd and min(S)>=1 and {1,2}<=S
    out[f"{name}: |S|, max, (K+3)^2/X, set sha256, witness sha256"]=(len(S),max(S),F((len(S)+3)**2,X),sha(canon),sha(tb))
    open(f'/tmp/rel/{name}.txt','w').write(canon); open(f'/tmp/rel/{name}_witness.csv','w').write(tb)
for k_,v in out.items(): print(k_,":",v)
