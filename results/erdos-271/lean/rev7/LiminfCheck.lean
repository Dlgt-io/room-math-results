import LiminfCore

/-! Generic Boolean certificate checker for `Cov S 3 X` (`S` given as a list). -/

namespace Erdos271.Liminf

def okRowL (S : List ℕ) (p : ℕ × ℕ) : Bool :=
  S.contains p.2 && S.contains (2 * p.2 - p.1) && decide (1 ≤ 2 * p.2 - p.1) &&
    decide (2 * p.2 - p.1 < p.2) && decide (p.2 < p.1)

theorem cov_of_cert (S : List ℕ) (cert : List (ℕ × ℕ)) (X : ℕ)
    (h1 : cert.all (okRowL S) = true) (h2 : cert.map Prod.fst = List.range' 3 (X - 2)) :
    Cov S.toFinset 3 X := by
  intro n hn1 hn2
  have hn : n ∈ cert.map Prod.fst := by rw [h2, List.mem_range'_1]; omega
  obtain ⟨⟨n', b⟩, hp, rfl⟩ := List.mem_map.1 hn
  have hrow := List.all_eq_true.1 h1 _ hp
  simp only [okRowL, Bool.and_eq_true, List.contains_iff_mem, decide_eq_true_eq] at hrow
  obtain ⟨⟨⟨⟨hb, ha⟩, ha1⟩, hab⟩, hbn⟩ := hrow
  exact ⟨2 * b - n', List.mem_toFinset.2 ha, b, List.mem_toFinset.2 hb, ha1, hab, by omega⟩

end Erdos271.Liminf

/-! ## Bitset certificates (kernel-accelerated `Nat` bit operations) -/

namespace Erdos271.Liminf

/-- The set `{m ≤ X : bit m of B is set}`. -/
def bitset (B X : ℕ) : Finset ℕ := ((List.range (X + 1)).filter (fun m => B.testBit m)).toFinset

theorem mem_bitset {B X m : ℕ} : m ∈ bitset B X ↔ m ≤ X ∧ B.testBit m = true := by
  simp only [bitset, List.mem_toFinset, List.mem_filter, List.mem_range]
  constructor <;> rintro ⟨h, h'⟩ <;> exact ⟨by omega, h'⟩

theorem card_bitset (B X : ℕ) :
    (bitset B X).card = ((List.range (X + 1)).filter (fun m => B.testBit m)).length :=
  List.toFinset_card_of_nodup (List.nodup_range.filter _)

def okRowB (B : ℕ) (p : ℕ × ℕ) : Bool :=
  B.testBit p.2 && B.testBit (2 * p.2 - p.1) && decide (1 ≤ 2 * p.2 - p.1) &&
    decide (2 * p.2 - p.1 < p.2) && decide (p.2 < p.1)

/-- A chunk of witness rows covering `[u, u+len)`. -/
theorem chunk_cov (B X : ℕ) (rows : List (ℕ × ℕ)) (u len : ℕ)
    (h1 : rows.all (okRowB B) = true) (h2 : rows.map Prod.fst = List.range' u len)
    (hX : u + len ≤ X + 1) :
    ∀ n, u ≤ n → n < u + len →
      ∃ a ∈ bitset B X, ∃ b ∈ bitset B X, 1 ≤ a ∧ a < b ∧ a + n = 2 * b := by
  intro n hn1 hn2
  have hn : n ∈ rows.map Prod.fst := by rw [h2, List.mem_range'_1]; omega
  obtain ⟨⟨n', b⟩, hp, rfl⟩ := List.mem_map.1 hn
  have hrow := List.all_eq_true.1 h1 _ hp
  simp only [okRowB, Bool.and_eq_true, decide_eq_true_eq] at hrow
  obtain ⟨⟨⟨⟨hb, ha⟩, ha1⟩, hab⟩, hbn⟩ := hrow
  exact ⟨2 * b - n', mem_bitset.2 ⟨by omega, ha⟩, b, mem_bitset.2 ⟨by omega, hb⟩, ha1, hab,
    by omega⟩

end Erdos271.Liminf
