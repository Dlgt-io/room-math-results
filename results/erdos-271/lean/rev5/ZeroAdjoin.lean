import Mathlib
namespace Erdos271.Endgame

theorem zero_adjoining_bundle :
(∀ S : Set Nat, ∀ s : Nat, (∀ z : Nat, s < z → Not (Membership.mem S z) → ∃ a : Nat, Membership.mem S a ∧ ∃ b : Nat, Membership.mem S b ∧ a < b ∧ 2 * b - a = z) → ∀ z : Nat, s < z → Not (Membership.mem (insert 0 S) z) → ∃ a : Nat, Membership.mem (insert 0 S) a ∧ ∃ b : Nat, Membership.mem (insert 0 S) b ∧ a < b ∧ 2 * b - a = z) ∧ (∀ S : Set Nat, Set.inter (insert 0 S) (Set.Ioi 0) = Set.inter S (Set.Ioi 0)) :=
by
  constructor
  · intro S s hcov z hz hn
    have hnS : z ∉ S := by
      intro hzS
      apply hn
      exact Set.mem_insert_iff.mpr (Or.inr hzS)
    obtain ⟨a, ha, b, hb, hab, heq⟩ := hcov z hz hnS
    exact ⟨a, Set.mem_insert_iff.mpr (Or.inr ha),
      b, Set.mem_insert_iff.mpr (Or.inr hb), hab, heq⟩
  · intro S
    apply Set.ext
    intro n
    change ((n = 0 ∨ n ∈ S) ∧ 0 < n) ↔ (n ∈ S ∧ 0 < n)
    constructor
    · rintro ⟨hn, hpos⟩
      rcases hn with hzero | hS
      · omega
      · exact ⟨hS, hpos⟩
    · rintro ⟨hS, hpos⟩
      exact ⟨Or.inr hS, hpos⟩

end Erdos271.Endgame
