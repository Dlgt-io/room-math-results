import bisect,sys
S768=[1,2,3,4,5,8,9,12,13,16,21,24,33,36,41,44,45,48,53,56,77,80,85,88,129,132,137,140,161,164,169,172,253,256,261,264,271,301,304,309,312,340,345,348,353,356,377,380,385,388]
L=lambda T:{4*t for t in T}|{4*t+1 for t in T}
S3=sorted({1,2,3,12}|L(set(S768)-{3}))
S49=sorted((L(L(S3)|{1,2,3})|{1,2,3})-{13})
CH=2048
def gen(name,S,X):
    St=set(S); rows=[]
    for n in range(3,X+1):
        lo=bisect.bisect_right(S,n//2); hi=bisect.bisect_left(S,n)
        b=next(b for b in S[lo:hi] if 2*b-n>=1 and (2*b-n) in St)
        rows.append((n,b))
    B=sum(1<<s for s in S)
    chunks=[rows[i:i+CH] for i in range(0,len(rows),CH)]
    out=[f"""import LiminfCheck

/-! Bitset certificate: a {len(S)}-element set covering `[3,{X}]` (Claude, `claude-ap3-liminf-below-2.md`). -/

set_option maxRecDepth 100000

namespace Erdos271.Liminf

/-- Bit `m` is set iff `m` is in the static set. -/
def B{name} : ℕ := {hex(B)}
"""]
    bounds=[]
    for i,c in enumerate(chunks):
        u=c[0][0]; ln=len(c); bounds.append((u,ln))
        out.append(f"""
def rows{name}_{i} : List (ℕ × ℕ) := [{",".join(f"({n},{b})" for n,b in c)}]

theorem rows{name}_{i}_all : rows{name}_{i}.all (okRowB B{name}) = true := by decide +kernel

theorem rows{name}_{i}_keys : rows{name}_{i}.map Prod.fst = List.range' {u} {ln} := by decide +kernel
""")
    cases=[]
    for i,(u,ln) in enumerate(bounds):
        cases.append(f"(n < {u+ln})" if i==0 else f"({u} ≤ n ∧ n < {u+ln})")
    pats=" | ".join(["h"]*len(bounds))
    body="\n".join(f"  · exact chunk_cov B{name} {X} rows{name}_{i} {u} {ln} rows{name}_{i}_all rows{name}_{i}_keys (by norm_num) n (by omega) (by omega)" for i,(u,ln) in enumerate(bounds))
    out.append(f"""
theorem S{name}_cov : Cov (bitset B{name} {X}) 3 {X} := by
  intro n h1 h2
  rcases (show {" ∨ ".join(cases)} by omega) with {pats}
{body}

theorem S{name}_card : (bitset B{name} {X}).card = {len(S)} := by
  rw [card_bitset]; decide +kernel

theorem S{name}_small : 1 ∈ bitset B{name} {X} ∧ 2 ∈ bitset B{name} {X} :=
  ⟨mem_bitset.2 ⟨by norm_num, by decide +kernel⟩, mem_bitset.2 ⟨by norm_num, by decide +kernel⟩⟩

theorem S{name}_pos : ∀ x ∈ bitset B{name} {X}, 1 ≤ x := by
  intro x hx
  have h0 : B{name}.testBit 0 = false := by decide +kernel
  rcases Nat.eq_zero_or_pos x with rfl | h
  · rw [mem_bitset, h0] at hx; simp at hx
  · exact h

end Erdos271.Liminf
""")
    open(f'./LiminfCert{name}.lean','w').write("".join(out))
    print(name,len(S),len(rows),len(chunks))
gen("3072",S3,3072); gen("49152",S49,49152)
