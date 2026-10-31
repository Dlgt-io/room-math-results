by
  obtain ⟨C, hC⟩ : ∃ C : Finset ℕ → ℕ → ℕ → Prop, C = fun T u v =>
      ∀ n, u ≤ n → n ≤ v → ∃ a ∈ T, ∃ b ∈ T, 1 ≤ a ∧ a < b ∧ a + n = 2 * b := ⟨_, rfl⟩
  obtain ⟨st, hst⟩ : ∃ st : Finset ℕ → Finset ℕ,
      st = fun T => T.image (fun t => 4 * t) ∪ T.image (fun t => 4 * t + 1) ∪ {1, 2, 3} := ⟨_, rfl⟩
  have mem_st : ∀ (T : Finset ℕ) (m : ℕ),
      m ∈ st T ↔ (∃ t ∈ T, 4 * t = m ∨ 4 * t + 1 = m) ∨ m = 1 ∨ m = 2 ∨ m = 3 := by
    intro T m
    rw [hst]
    simp only [Finset.mem_union, Finset.mem_image, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ((⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩) | h)
      · exact Or.inl ⟨t, ht, Or.inl rfl⟩
      · exact Or.inl ⟨t, ht, Or.inr rfl⟩
      · exact Or.inr h
    · rintro (⟨t, ht, h | h⟩ | h)
      · exact Or.inl (Or.inl ⟨t, ht, h⟩)
      · exact Or.inl (Or.inr ⟨t, ht, h⟩)
      · exact Or.inr h
  have card_st : ∀ T : Finset ℕ, (st T).card ≤ 2 * T.card + 3 := by
    intro T
    have h1 := Finset.card_union_le (T.image (fun t => 4 * t) ∪ T.image (fun t => 4 * t + 1))
      ({1, 2, 3} : Finset ℕ)
    have h2 := Finset.card_union_le (T.image (fun t => 4 * t)) (T.image (fun t => 4 * t + 1))
    have h3 : (T.image (fun t => 4 * t)).card ≤ T.card := Finset.card_image_le
    have h4 : (T.image (fun t => 4 * t + 1)).card ≤ T.card := Finset.card_image_le
    have h5 : ({1, 2, 3} : Finset ℕ).card = 3 := by first | rfl | decide | simp
    rw [hst]
    show (T.image (fun t => 4 * t) ∪ T.image (fun t => 4 * t + 1) ∪ {1, 2, 3}).card ≤ 2 * T.card + 3
    omega
  have step_small : ∀ T : Finset ℕ, 1 ∈ st T ∧ 2 ∈ st T := fun T =>
    ⟨(mem_st T 1).2 (Or.inr (Or.inl rfl)), (mem_st T 2).2 (Or.inr (Or.inr (Or.inl rfl)))⟩
  have step_cov : ∀ (T : Finset ℕ) (Y : ℕ), 1 ∈ T → 2 ∈ T → C T 3 Y → C (st T) 3 (4 * Y) := by
    intro T Y h1 h2 h
    simp only [hC] at h ⊢
    intro n hn1 hn2
    have m4 : ∀ t ∈ T, 4 * t ∈ st T := fun t ht => (mem_st T _).2 (Or.inl ⟨t, ht, Or.inl rfl⟩)
    have m41 : ∀ t ∈ T, 4 * t + 1 ∈ st T := fun t ht => (mem_st T _).2 (Or.inl ⟨t, ht, Or.inr rfl⟩)
    have s1 : 1 ∈ st T := (step_small T).1
    have s2 : 2 ∈ st T := (step_small T).2
    have s3 : 3 ∈ st T := (mem_st T 3).2 (Or.inr (Or.inr (Or.inr rfl)))
    have s4 : 4 ∈ st T := m4 1 h1
    have s5 : 5 ∈ st T := m41 1 h1
    have s8 : 8 ∈ st T := m4 2 h2
    have s9 : 9 ∈ st T := m41 2 h2
    by_cases hn : n ≤ 10
    · interval_cases n
      · exact ⟨1, s1, 2, s2, by omega, by omega, by omega⟩
      · exact ⟨2, s2, 3, s3, by omega, by omega, by omega⟩
      · exact ⟨1, s1, 3, s3, by omega, by omega, by omega⟩
      · exact ⟨2, s2, 4, s4, by omega, by omega, by omega⟩
      · exact ⟨1, s1, 4, s4, by omega, by omega, by omega⟩
      · exact ⟨2, s2, 5, s5, by omega, by omega, by omega⟩
      · exact ⟨1, s1, 5, s5, by omega, by omega, by omega⟩
      · exact ⟨8, s8, 9, s9, by omega, by omega, by omega⟩
    · have : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by omega
      rcases this with hr | hr | hr | hr
      · obtain ⟨a, ha, b, hb, ha1, hab, he⟩ := h (n / 4) (by omega) (by omega)
        exact ⟨4 * a, m4 a ha, 4 * b, m4 b hb, by omega, by omega, by omega⟩
      · obtain ⟨a, ha, b, hb, ha1, hab, he⟩ := h (n / 4) (by omega) (by omega)
        exact ⟨4 * a + 1, m41 a ha, 4 * b + 1, m41 b hb, by omega, by omega, by omega⟩
      · obtain ⟨a, ha, b, hb, ha1, hab, he⟩ := h (n / 4) (by omega) (by omega)
        exact ⟨4 * a, m4 a ha, 4 * b + 1, m41 b hb, by omega, by omega, by omega⟩
      · obtain ⟨a, ha, b, hb, ha1, hab, he⟩ := h (n / 4 + 1) (by omega) (by omega)
        exact ⟨4 * a + 1, m41 a ha, 4 * b, m4 b hb, by omega, by omega, by omega⟩
  have remF : ∀ (U : Finset ℕ) (e Y : ℕ), C U 3 Y →
      (∀ b ∈ U, e < b → 3 ≤ 2 * b - e → 2 * b - e ≤ Y →
        ∃ c ∈ U.erase e, ∃ d ∈ U.erase e, 1 ≤ c ∧ c < d ∧ c + (2 * b - e) = 2 * d) →
      (∀ a ∈ U, 1 ≤ a → a < e → 3 ≤ 2 * e - a → 2 * e - a ≤ Y →
        ∃ c ∈ U.erase e, ∃ d ∈ U.erase e, 1 ≤ c ∧ c < d ∧ c + (2 * e - a) = 2 * d) →
      C (U.erase e) 3 Y := by
    intro U e Y hU h1 h2
    simp only [hC] at hU ⊢
    intro n hn1 hn2
    obtain ⟨a, ha, b, hb, h1a, hab, he⟩ := hU n hn1 hn2
    by_cases hae : a = e
    · have hn : n = 2 * b - e := by omega
      rw [hn]; exact h1 b hb (by omega) (by omega) (by omega)
    · by_cases hbe : b = e
      · have hn : n = 2 * e - a := by omega
        rw [hn]; exact h2 a ha h1a (by omega) (by omega) (by omega)
      · exact ⟨a, Finset.mem_erase.2 ⟨hae, ha⟩, b, Finset.mem_erase.2 ⟨hbe, hb⟩, h1a, hab, he⟩
  obtain ⟨lp, hlp⟩ : ∃ lp : (ℕ → Bool) → ℕ → Bool, lp = fun p x =>
      (x == 1 || x == 2 || x == 3) || ((x % 4 == 0 || x % 4 == 1) && p (x / 4)) := ⟨_, rfl⟩
  have lp_iff : ∀ p x, lp p x = true ↔
      (x = 1 ∨ x = 2 ∨ x = 3) ∨ ((x % 4 = 0 ∨ x % 4 = 1) ∧ p (x / 4) = true) := by
    intro p x
    rw [hlp]
    first
    | (simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] <;> tauto)
    | (simp <;> tauto)
  have st_iff : ∀ (T : Finset ℕ) (p : ℕ → Bool), (∀ y, y ∈ T ↔ p y = true) →
      ∀ x, x ∈ st T ↔ lp p x = true := by
    intro T p hT x
    rw [mem_st, lp_iff]
    constructor
    · rintro (⟨t, ht, h | h⟩ | h)
      · exact Or.inr ⟨Or.inl (by omega), by rw [show x / 4 = t by omega]; exact (hT t).1 ht⟩
      · exact Or.inr ⟨Or.inr (by omega), by rw [show x / 4 = t by omega]; exact (hT t).1 ht⟩
      · exact Or.inl h
    · rintro (h | ⟨h4, hp⟩)
      · exact Or.inr h
      · exact Or.inl ⟨x / 4, (hT _).2 hp, by omega⟩
  have er_iff : ∀ (U : Finset ℕ) (p : ℕ → Bool) (e : ℕ), (∀ y, y ∈ U ↔ p y = true) →
      ∀ x, x ∈ U.erase e ↔ (p x && x != e) = true := by
    intro U p e hU x
    first
    | (rw [Finset.mem_erase, hU, Bool.and_eq_true, bne_iff_ne]; exact and_comm)
    | (simp only [Finset.mem_erase, hU, Bool.and_eq_true, bne_iff_ne, ne_eq] <;> tauto)
    | (simp [Finset.mem_erase, hU] <;> tauto)
  have lp_lt : ∀ (p : ℕ → Bool) (B : ℕ), (∀ y, p y = true → y < B) → 1 ≤ B →
      ∀ x, lp p x = true → x < 4 * B := by
    intro p B hB hB1 x hx
    rw [lp_iff] at hx
    rcases hx with h | ⟨-, hp⟩
    · omega
    · have := hB _ hp; omega
  have liftQ : ∀ (p : ℕ → Bool) (Q : ℕ → Prop), (∀ t, p t = true → Q (4 * t) ∧ Q (4 * t + 1)) →
      Q 1 → Q 2 → Q 3 → ∀ b, lp p b = true → Q b := by
    intro p Q hQ k1 k2 k3 b hb
    rw [lp_iff] at hb
    rcases hb with (h | h | h) | ⟨h | h, hp⟩
    · rw [h]; exact k1
    · rw [h]; exact k2
    · rw [h]; exact k3
    · have e : 4 * (b / 4) = b := by omega
      have := (hQ _ hp).1
      rw [e] at this; exact this
    · have e : 4 * (b / 4) + 1 = b := by omega
      have := (hQ _ hp).2
      rw [e] at this; exact this
  obtain ⟨Wt, hWt⟩ : ∃ Wt : (ℕ → Bool) → ℕ → ℕ → Prop, Wt = fun q K n =>
      ∃ c ∈ List.range' 0 K, q c = true ∧ 1 ≤ c ∧ (n + c) % 2 = 0 ∧ q ((n + c) / 2) = true ∧
        c < (n + c) / 2 ∧ (n + c) / 2 < n := ⟨_, rfl⟩
  obtain ⟨PB, hPB⟩ : ∃ PB : (ℕ → Bool) → ℕ → ℕ → ℕ → ℕ → Prop, PB = fun q e Y K b =>
      e < b → 3 ≤ 2 * b - e → 2 * b - e ≤ Y → Wt q K (2 * b - e) := ⟨_, rfl⟩
  obtain ⟨PA, hPA⟩ : ∃ PA : (ℕ → Bool) → ℕ → ℕ → ℕ → ℕ → Prop, PA = fun q e Y K a =>
      1 ≤ a → 3 ≤ 2 * e - a → 2 * e - a ≤ Y → Wt q K (2 * e - a) := ⟨_, rfl⟩
  have PB_small : ∀ q Y K b, b ≤ 13 → PB q 13 Y K b := by
    intro q Y K b hb
    rw [hPB]
    intro h
    omega
  obtain ⟨wtb, hwtb⟩ : ∃ f : (ℕ → Bool) → List ℕ → ℕ → Bool, f = fun q L n =>
      L.any (fun c => ((n + c) % 2 == 0) && q c && decide (1 ≤ c) && q ((n + c) / 2) &&
        decide (c < (n + c) / 2) && decide ((n + c) / 2 < n)) := ⟨_, rfl⟩
  have wtb_Wt : ∀ q K L n, (∀ c ∈ L, c < K) → wtb q L n = true → Wt q K n := by
    intro q K L n hL h
    rw [hwtb] at h
    rw [hWt]
    obtain ⟨c, hc, hc'⟩ := List.any_eq_true.1 h
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hc'
    exact ⟨c, List.mem_range'_1.2 ⟨Nat.zero_le _, by have := hL c hc; omega⟩, by tauto⟩
  obtain ⟨pbb, hpbb⟩ : ∃ f : (ℕ → Bool) → ℕ → ℕ → List ℕ → ℕ → Bool, f = fun q e Y L b =>
      !(decide (e < b) && decide (3 ≤ 2 * b - e) && decide (2 * b - e ≤ Y)) || wtb q L (2 * b - e) :=
    ⟨_, rfl⟩
  obtain ⟨paa, hpaa⟩ : ∃ f : (ℕ → Bool) → ℕ → ℕ → List ℕ → ℕ → Bool, f = fun q e Y L a =>
      !(decide (1 ≤ a) && decide (3 ≤ 2 * e - a) && decide (2 * e - a ≤ Y)) || wtb q L (2 * e - a) :=
    ⟨_, rfl⟩
  have pbb_PB : ∀ q e Y K L b, (∀ c ∈ L, c < K) → pbb q e Y L b = true → PB q e Y K b := by
    intro q e Y K L b hL h
    rw [hPB]
    intro h1 h2 h3
    rw [hpbb] at h
    have h' : wtb q L (2 * b - e) = true := by simpa [h1, h2, h3] using h
    exact wtb_Wt q K L _ hL h'
  have paa_PA : ∀ q e Y K L a, (∀ c ∈ L, c < K) → paa q e Y L a = true → PA q e Y K a := by
    intro q e Y K L a hL h
    rw [hPA]
    intro h1 h2 h3
    rw [hpaa] at h
    have h' : wtb q L (2 * e - a) = true := by simpa [h1, h2, h3] using h
    exact wtb_Wt q K L _ hL h'
  obtain ⟨L1, hL1⟩ : ∃ L : List ℕ, L = [37, 53, 21, 181, 341, 3, 1, 2, 5, 16, 85, 309, 1045, 9] := ⟨_, rfl⟩
  have L1_lt : ∀ c ∈ L1, c < 1046 := by subst hL1; decide
  obtain ⟨L2, hL2⟩ : ∃ L : List ℕ, L = [5, 21, 1, 2, 3, 16, 9] := ⟨_, rfl⟩
  have L2_lt : ∀ c ∈ L2, c < 22 := by subst hL2; decide
  obtain ⟨LC, hLC⟩ : ∃ L : List ℕ, L = [20, 276, 3, 4, 5, 2, 8, 9, 13, 12, 32, 33, 36, 37, 48, 49, 52, 53, 260, 261] := ⟨_, rfl⟩
  have LC_lt : ∀ c ∈ LC, c < 277 := by subst hLC; decide
  have remP : ∀ (U : Finset ℕ) (pU q : ℕ → Bool) (e Y K : ℕ), (∀ x, x ∈ U ↔ pU x = true) →
      (∀ x, x ∈ U.erase e ↔ q x = true) → C U 3 Y →
      (∀ b, pU b = true → PB q e Y K b) → (∀ a, a < e → pU a = true → PA q e Y K a) →
      C (U.erase e) 3 Y := by
    intro U pU q e Y K hU hq hC0 hb ha
    have use : ∀ n, Wt q K n → ∃ c ∈ U.erase e, ∃ d ∈ U.erase e, 1 ≤ c ∧ c < d ∧ c + n = 2 * d := by
      intro n hw
      simp only [hWt] at hw
      obtain ⟨c, -, hq1, hc1, hpar, hq2, hcd, hd⟩ := hw
      exact ⟨c, (hq c).2 hq1, (n + c) / 2, (hq _).2 hq2, hc1, hcd, by omega⟩
    refine remF U e Y hC0 ?_ ?_
    · intro b hbU h1 h2 h3
      have := hb b ((hU b).1 hbU)
      simp only [hPB] at this
      exact use _ (this h1 h2 h3)
    · intro a haU h1 h2 h3 h4
      have := ha a h2 ((hU a).1 haU)
      simp only [hPA] at this
      exact use _ (this h1 h3 h4)
  obtain ⟨it, hit0, hitS⟩ : ∃ it : Finset ℕ → ℕ → Finset ℕ,
      (∀ S, it S 0 = S) ∧ ∀ S j, it S (j + 1) = st (it S j) :=
    ⟨fun S j => Nat.rec (motive := fun _ => Finset ℕ) S (fun _ T => st T) j, fun _ => rfl, fun _ _ => rfl⟩
  have iter_spec : ∀ (S : Finset ℕ) (X K : ℕ), 1 ∈ S → 2 ∈ S → C S 3 X → S.card ≤ K → ∀ j : ℕ,
      C (it S j) 3 (4 ^ j * X) ∧ 1 ∈ it S j ∧ 2 ∈ it S j ∧
        (it S j).card + 3 ≤ 2 ^ j * (K + 3) := by
    intro S X K h1 h2 hS hK j
    induction j with
    | zero =>
      rw [hit0]
      simp only [pow_zero, one_mul]
      exact ⟨hS, h1, h2, by omega⟩
    | succ j ih =>
      obtain ⟨hc, i1, i2, hk⟩ := ih
      rw [hitS]
      refine ⟨?_, (step_small _).1, (step_small _).2, ?_⟩
      · have e : 4 ^ (j + 1) * X = 4 * (4 ^ j * X) := by ring
        rw [e]; exact step_cov _ _ i1 i2 hc
      · have := card_st (it S j)
        rw [pow_succ]; nlinarith [hk, this]
  obtain ⟨p0, hp0⟩ : ∃ p0 : ℕ → Bool, p0 = fun x =>
      decide (x < 389) && (712006565261563799222420049390883128778328161928433194935513472185973773576035059310582382486636252388574868795372350 / 2 ^ x % 2 == 1) := ⟨_, rfl⟩
  have p0_lt : ∀ y, p0 y = true → y < 389 := by
    intro y hy
    rw [hp0] at hy
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hy
    exact hy.1
  obtain ⟨F768, hF768⟩ : ∃ F : Finset ℕ, F = (Finset.range 389).filter (fun x => p0 x = true) := ⟨_, rfl⟩
  have base_iff : ∀ y, y ∈ F768 ↔ p0 y = true := by
    intro y
    rw [hF768, Finset.mem_filter, Finset.mem_range]
    exact ⟨fun h => h.2, fun h => ⟨p0_lt y h, h⟩⟩
  obtain ⟨L768, hL768⟩ : ∃ L : List ℕ, L = [1, 2, 3, 4, 5, 8, 9, 12, 13, 16, 21, 24, 33, 36, 41, 44, 45, 48, 53, 56, 77, 80, 85, 88, 129, 132, 137, 140, 161, 164, 169, 172, 253, 256, 261, 264, 271, 301, 304, 309, 312, 340, 345, 348, 353, 356, 377, 380, 385, 388] := ⟨_, rfl⟩
  have c768b : (List.range' 3 766).all (fun n => L768.any (fun b =>
      p0 b && p0 (2 * b - n) && decide (1 ≤ 2 * b - n) && decide (2 * b - n < b) && decide (b < n))) = true := by
    subst hL768; subst hp0; decide +kernel
  have c768 : ∀ n ∈ List.range' 3 766, ∃ b ∈ L768,
      p0 b = true ∧ p0 (2 * b - n) = true ∧ 1 ≤ 2 * b - n ∧ 2 * b - n < b ∧ b < n := by
    intro n hn
    obtain ⟨b, hb, h⟩ := List.any_eq_true.1 (List.all_eq_true.1 c768b n hn)
    refine ⟨b, hb, ?_⟩
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    tauto
  have cov768 : C F768 3 768 := by
    simp only [hC]
    intro n h1 h2
    obtain ⟨b, -, hpb, hpa, ha1, hab, hbn⟩ := c768 n (List.mem_range'_1.2 ⟨by omega, by omega⟩)
    exact ⟨2 * b - n, (base_iff _).2 hpa, b, (base_iff _).2 hpb, ha1, hab, by omega⟩
  have p0_123 : p0 1 = true ∧ p0 2 = true ∧ p0 3 = true := by subst hp0; decide +kernel
  have F1 : 1 ∈ F768 := (base_iff 1).2 p0_123.1
  have F2 : 2 ∈ F768 := (base_iff 2).2 p0_123.2.1
  have F3 : 3 ∈ F768 := (base_iff 3).2 p0_123.2.2
  have cF768 : F768.card ≤ 50 := by rw [hF768]; subst hp0; decide +kernel
  have hU1 : ∀ x, x ∈ st F768 ↔ lp p0 x = true := st_iff F768 p0 base_iff
  obtain ⟨q1, hq1⟩ : ∃ q : ℕ → Bool, q = fun x => lp p0 x && x != 13 := ⟨_, rfl⟩
  have hF3 : ∀ x, x ∈ (st F768).erase 13 ↔ q1 x = true := by
    intro x; rw [hq1]; exact er_iff _ _ 13 hU1 x
  have D1b : (List.range' 0 389).all (fun t => !p0 t ||
      (pbb q1 13 3072 L1 (4 * t) && pbb q1 13 3072 L1 (4 * t + 1))) = true := by
    subst hpbb; subst hpaa; subst hwtb; subst hL1; subst hL2; subst hLC; subst hq1; subst hlp; subst hp0; decide +kernel
  have DA1b : (List.range' 0 13).all (fun a => !lp p0 a || paa q1 13 3072 L1 a) = true := by
    subst hpbb; subst hpaa; subst hwtb; subst hL1; subst hL2; subst hLC; subst hq1; subst hlp; subst hp0; decide +kernel
  have covF3 : C ((st F768).erase 13) 3 3072 := by
    refine remP (st F768) (lp p0) q1 13 3072 1046 hU1 hF3 (step_cov F768 768 F1 F2 cov768) ?_ ?_
    · intro b hb
      refine liftQ p0 (PB q1 13 3072 1046) ?_ (PB_small _ _ _ _ (by norm_num))
        (PB_small _ _ _ _ (by norm_num)) (PB_small _ _ _ _ (by norm_num)) b hb
      intro t ht
      have h := List.all_eq_true.1 D1b t (List.mem_range'_1.2 ⟨by omega, by have := p0_lt t ht; omega⟩)
      simp only [ht, Bool.not_true, Bool.false_or, Bool.and_eq_true] at h
      exact ⟨pbb_PB _ _ _ _ _ _ L1_lt h.1, pbb_PB _ _ _ _ _ _ L1_lt h.2⟩
    · intro a ha hpa
      have h := List.all_eq_true.1 DA1b a (List.mem_range'_1.2 ⟨by omega, by omega⟩)
      simp only [hpa, Bool.not_true, Bool.false_or] at h
      exact paa_PA _ _ _ _ _ _ L1_lt h
  have F31 : 1 ∈ (st F768).erase 13 := Finset.mem_erase.2 ⟨by norm_num, (step_small _).1⟩
  have F32 : 2 ∈ (st F768).erase 13 := Finset.mem_erase.2 ⟨by norm_num, (step_small _).2⟩
  have hU2a : ∀ x, x ∈ st ((st F768).erase 13) ↔ lp q1 x = true := st_iff _ q1 hF3
  have hU2 : ∀ x, x ∈ st (st ((st F768).erase 13)) ↔ lp (lp q1) x = true := st_iff _ _ hU2a
  obtain ⟨q2, hq2⟩ : ∃ q : ℕ → Bool, q = fun x => lp (lp q1) x && x != 13 := ⟨_, rfl⟩
  have hS : ∀ x, x ∈ (st (st ((st F768).erase 13))).erase 13 ↔ q2 x = true := by
    intro x; rw [hq2]; exact er_iff _ _ 13 hU2 x
  have q1_lt : ∀ y, q1 y = true → y < 1556 := by
    intro y hy
    rw [← hF3] at hy
    exact lp_lt p0 389 p0_lt (by norm_num) y ((hU1 y).1 (Finset.mem_of_mem_erase hy))
  have D2b : (List.range' 0 1556).all (fun t => !q1 t || (pbb q2 13 49152 L2 (4 * (4 * t)) &&
      pbb q2 13 49152 L2 (4 * (4 * t) + 1) && pbb q2 13 49152 L2 (4 * (4 * t + 1)) &&
      pbb q2 13 49152 L2 (4 * (4 * t + 1) + 1))) = true := by
    subst hpbb; subst hpaa; subst hwtb; subst hL1; subst hL2; subst hLC; subst hq2; subst hq1; subst hlp; subst hp0; decide +kernel
  have DA2b : (List.range' 0 13).all (fun a => !lp (lp q1) a || paa q2 13 49152 L2 a) = true := by
    subst hpbb; subst hpaa; subst hwtb; subst hL1; subst hL2; subst hLC; subst hq2; subst hq1; subst hlp; subst hp0; decide +kernel
  have covU2 : C (st (st ((st F768).erase 13))) 3 49152 :=
    step_cov (st ((st F768).erase 13)) (4 * 3072) (step_small _).1 (step_small _).2
      (step_cov ((st F768).erase 13) 3072 F31 F32 covF3)
  have covS : C ((st (st ((st F768).erase 13))).erase 13) 3 49152 := by
    refine remP _ (lp (lp q1)) q2 13 49152 22 hU2 hS covU2 ?_ ?_
    · intro b hb
      refine liftQ (lp q1) (PB q2 13 49152 22) ?_ (PB_small _ _ _ _ (by norm_num))
        (PB_small _ _ _ _ (by norm_num)) (PB_small _ _ _ _ (by norm_num)) b hb
      intro y hy
      refine liftQ q1 (fun y => PB q2 13 49152 22 (4 * y) ∧ PB q2 13 49152 22 (4 * y + 1))
        ?_ ?_ ?_ ?_ y hy
      · intro t ht
        have h := List.all_eq_true.1 D2b t (List.mem_range'_1.2 ⟨by omega, by have := q1_lt t ht; omega⟩)
        simp only [ht, Bool.not_true, Bool.false_or, Bool.and_eq_true] at h
        exact ⟨⟨pbb_PB _ _ _ _ _ _ L2_lt h.1.1.1, pbb_PB _ _ _ _ _ _ L2_lt h.1.1.2⟩,
          ⟨pbb_PB _ _ _ _ _ _ L2_lt h.1.2, pbb_PB _ _ _ _ _ _ L2_lt h.2⟩⟩
      · exact ⟨PB_small _ _ _ _ (by norm_num), PB_small _ _ _ _ (by norm_num)⟩
      · exact ⟨PB_small _ _ _ _ (by norm_num), PB_small _ _ _ _ (by norm_num)⟩
      · exact ⟨PB_small _ _ _ _ (by norm_num), PB_small _ _ _ _ (by norm_num)⟩
    · intro a ha hpa
      have h := List.all_eq_true.1 DA2b a (List.mem_range'_1.2 ⟨by omega, by omega⟩)
      simp only [hpa, Bool.not_true, Bool.false_or] at h
      exact paa_PA _ _ _ _ _ _ L2_lt h
  have h13a : 13 ∈ st F768 := (mem_st _ 13).2 (Or.inl ⟨3, F3, Or.inr rfl⟩)
  have cF3 : ((st F768).erase 13).card ≤ 102 := by
    rw [Finset.card_erase_of_mem h13a]
    have := card_st F768
    omega
  have h13b : 13 ∈ st (st ((st F768).erase 13)) :=
    (mem_st _ 13).2 (Or.inl ⟨3, (mem_st _ 3).2 (Or.inr (Or.inr (Or.inr rfl))), Or.inr rfl⟩)
  have cS : ((st (st ((st F768).erase 13))).erase 13).card ≤ 416 := by
    rw [Finset.card_erase_of_mem h13b]
    have h1 := card_st (st ((st F768).erase 13))
    have h2 := card_st ((st F768).erase 13)
    omega
  obtain ⟨S49, hS49⟩ : ∃ S : Finset ℕ, S = (st (st ((st F768).erase 13))).erase 13 := ⟨_, rfl⟩
  rw [← hS49] at covS hS cS
  have S49_1 : 1 ∈ S49 := by rw [hS49]; exact Finset.mem_erase.2 ⟨by norm_num, (step_small _).1⟩
  have S49_2 : 2 ∈ S49 := by rw [hS49]; exact Finset.mem_erase.2 ⟨by norm_num, (step_small _).2⟩
  have S49_9 : 9 ∈ S49 := by
    rw [hS49]
    exact Finset.mem_erase.2 ⟨by norm_num, (mem_st _ 9).2 (Or.inl ⟨2, (step_small _).2, Or.inr rfl⟩)⟩
  have hU3a : ∀ x, x ∈ st S49 ↔ lp q2 x = true := st_iff _ q2 hS
  have hU3 : ∀ x, x ∈ st (st S49) ↔ lp (lp q2) x = true := st_iff _ _ hU3a
  obtain ⟨q3, hq3⟩ : ∃ q : ℕ → Bool, q = fun x => lp (lp q2) x && x != 148 := ⟨_, rfl⟩
  have hS3 : ∀ x, x ∈ (st (st S49)).erase 148 ↔ q3 x = true := by
    intro x; rw [hq3]; exact er_iff _ _ 148 hU3 x
  have q2_lt : ∀ y, q2 y = true → y < 24896 := by
    intro y hy
    rw [← hS, hS49] at hy
    have h1 := (hU2 y).1 (Finset.mem_of_mem_erase hy)
    have h2 := lp_lt (lp q1) 6224 (lp_lt q1 1556 q1_lt (by norm_num)) (by norm_num) y h1
    omega
  have PB_small2 : ∀ q Y K b, b ≤ 148 → PB q 148 Y K b := by
    intro q Y K b hb
    rw [hPB]
    intro h
    omega
  have lift2 : ∀ (p : ℕ → Bool) (Q : ℕ → Prop), (∀ t, p t = true → ∀ d ∈ [0, 1, 4, 5], Q (16 * t + d)) →
      (∀ b ∈ [1, 2, 3, 4, 5, 8, 9, 12, 13], Q b) → ∀ b, lp (lp p) b = true → Q b := by
    intro p Q hQ hs b hb
    rw [lp_iff] at hb
    rcases hb with h | ⟨h4, hb'⟩
    · exact hs b (by rcases h with h | h | h <;> simp [h])
    · rw [lp_iff] at hb'
      rcases hb' with h' | ⟨h4', hp⟩
      · have : b = 4 ∨ b = 5 ∨ b = 8 ∨ b = 9 ∨ b = 12 ∨ b = 13 := by omega
        exact hs b (by rcases this with h | h | h | h | h | h <;> simp [h])
      · have key := hQ _ hp
        have e : b = 16 * (b / 4 / 4) + b % 16 := by omega
        have hd : b % 16 ∈ [0, 1, 4, 5] := by
          have : b % 16 = 0 ∨ b % 16 = 1 ∨ b % 16 = 4 ∨ b % 16 = 5 := by omega
          rcases this with h | h | h | h <;> simp [h]
        rw [e]; exact key _ hd
  have D3c : (List.range' 0 1556).all (fun u => !q1 u || [0, 1, 4, 5].all (fun d1 =>
      [0, 1, 4, 5].all (fun d2 => pbb q3 148 786432 LC (16 * (16 * u + d1) + d2)))) = true := by
    subst hpbb; subst hpaa; subst hwtb; subst hL1; subst hL2; subst hLC; subst hq3; subst hq2; subst hq1; subst hlp; subst hp0; decide +kernel
  have DS3 : [1, 2, 3, 4, 5, 8, 9, 12, 13].all (fun t => [0, 1, 4, 5].all (fun d =>
      pbb q3 148 786432 LC (16 * t + d))) = true := by
    subst hpbb; subst hpaa; subst hwtb; subst hL1; subst hL2; subst hLC; subst hq3; subst hq2; subst hq1; subst hlp; subst hp0; decide +kernel
  have DA3b : (List.range' 0 148).all (fun a => !lp (lp q2) a || paa q3 148 786432 LC a) = true := by
    subst hpbb; subst hpaa; subst hwtb; subst hL1; subst hL2; subst hLC; subst hq3; subst hq2; subst hq1; subst hlp; subst hp0; decide +kernel
  have covU3 : C (st (st S49)) 3 786432 :=
    step_cov (st S49) (4 * 49152) (step_small _).1 (step_small _).2
      (step_cov S49 49152 S49_1 S49_2 covS)
  have covS3 : C ((st (st S49)).erase 148) 3 786432 := by
    refine remP _ (lp (lp q2)) q3 148 786432 277 hU3 hS3 covU3 ?_ ?_
    · intro b hb
      refine lift2 q2 (PB q3 148 786432 277) ?_ (fun b hb => PB_small2 _ _ _ _ (by simp at hb; omega)) b hb
      intro t ht
      have ht' : lp (lp q1) t = true := by
        rw [hq2] at ht
        simp only [Bool.and_eq_true] at ht
        exact ht.1
      refine lift2 q1 (fun t => ∀ d ∈ [0, 1, 4, 5], PB q3 148 786432 277 (16 * t + d)) ?_ ?_ t ht'
      · intro u hu d1 hd1 d2 hd2
        have h := List.all_eq_true.1 D3c u (List.mem_range'_1.2 ⟨by omega, by have := q1_lt u hu; omega⟩)
        simp only [hu, Bool.not_true, Bool.false_or, List.all_eq_true] at h
        exact pbb_PB _ _ _ _ _ _ LC_lt (h d1 hd1 d2 hd2)
      · intro t' ht'' d hd
        have h := List.all_eq_true.1 DS3 t' ht''
        simp only [List.all_eq_true] at h
        exact pbb_PB _ _ _ _ _ _ LC_lt (h d hd)
    · intro a ha hpa
      have h := List.all_eq_true.1 DA3b a (List.mem_range'_1.2 ⟨by omega, by omega⟩)
      simp only [hpa, Bool.not_true, Bool.false_or] at h
      exact paa_PA _ _ _ _ _ _ LC_lt h
  have h37 : 37 ∈ st S49 := (mem_st _ 37).2 (Or.inl ⟨9, S49_9, Or.inr rfl⟩)
  have h148 : 148 ∈ st (st S49) := (mem_st _ 148).2 (Or.inl ⟨37, h37, Or.inl rfl⟩)
  have cS3 : ((st (st S49)).erase 148).card ≤ 1672 := by
    rw [Finset.card_erase_of_mem h148]
    have h1 := card_st (st S49)
    have h2 := card_st S49
    omega
  obtain ⟨S0, hS0c, hS01, hS02, hS0K⟩ : ∃ S0 : Finset ℕ, C S0 3 786432 ∧ 1 ∈ S0 ∧ 2 ∈ S0 ∧ S0.card ≤ 1672 :=
    ⟨_, covS3, Finset.mem_erase.2 ⟨by norm_num, (step_small _).1⟩,
      Finset.mem_erase.2 ⟨by norm_num, (step_small _).2⟩, cS3⟩
  obtain ⟨Y, hY⟩ : ∃ Y : ℕ → ℕ, Y = fun k => 4 ^ (k * k) * 786432 := ⟨_, rfl⟩
  obtain ⟨R, hR⟩ : ∃ R : ℕ → Finset ℕ, R = fun k => it S0 (k * k) := ⟨_, rfl⟩
  obtain ⟨t, ht⟩ : ∃ t : ℕ → ℕ, t = fun k => ∑ i ∈ Finset.range k, (Y i - 3) := ⟨_, rfl⟩
  have hYe : ∀ k, Y k = 4 ^ (k * k) * 786432 := fun k => by rw [hY]
  have hRe : ∀ k, R k = it S0 (k * k) := fun k => by rw [hR]
  have hte : ∀ k, t k = ∑ i ∈ Finset.range k, (Y i - 3) := fun k => by rw [ht]
  have R_spec : ∀ k, C (R k) 3 (Y k) ∧ (R k).card + 3 ≤ 2 ^ (k * k) * 1675 := by
    intro k
    have h := iter_spec S0 786432 1672 hS01 hS02 hS0c hS0K (k * k)
    rw [hRe k, hYe k]
    exact ⟨h.1, h.2.2.2⟩
  have Y_ge : ∀ k, 786432 ≤ Y k := by
    intro k
    have h3 : 0 < 4 ^ (k * k) := by positivity
    have h4 := hYe k
    omega
  have lt4 : ∀ n : ℕ, n < 4 ^ n := by
    intro n
    induction n with
    | zero => norm_num
    | succ k ih => rw [pow_succ]; omega
  have le_Y : ∀ n, n ≤ Y n := by
    intro n
    have h1 := lt4 n
    have h2 : 4 ^ n ≤ 4 ^ (n * n) := Nat.pow_le_pow_right (by norm_num) (Nat.le_mul_self n)
    have h4 := hYe n
    omega
  have t_zero : t 0 = 0 := by rw [hte, Finset.sum_range_zero]
  have t_succ : ∀ k, t (k + 1) + 3 = t k + Y k := by
    intro k
    have := Y_ge k
    rw [hte, hte, Finset.sum_range_succ]
    omega
  have t_mono : Monotone t :=
    monotone_nat_of_le_succ fun k => by have := t_succ k; have := Y_ge k; omega
  obtain ⟨A, hA⟩ : ∃ A : Set ℕ, A = {x | ∃ k, ∃ r ∈ R k, x = r + t k} := ⟨_, rfl⟩
  have memA : ∀ x, x ∈ A ↔ ∃ k, ∃ r ∈ R k, x = r + t k := by
    intro x; subst hA; exact Iff.rfl
  have stage_cov : ∀ k n, t k + 3 ≤ n → n ≤ t k + Y k →
      ∃ a b : ℕ, a ∈ A ∧ b ∈ A ∧ 0 < a ∧ a < b ∧ b < n ∧ a + n = 2 * b := by
    intro k n h1 h2
    have hc := (R_spec k).1
    simp only [hC] at hc
    obtain ⟨a, ha, b, hb, ha1, hab, he⟩ := hc (n - t k) (by omega) (by omega)
    exact ⟨a + t k, b + t k, (memA _).2 ⟨k, a, ha, rfl⟩, (memA _).2 ⟨k, b, hb, rfl⟩,
      by omega, by omega, by omega, by omega⟩
  have covering : ∀ n : ℕ, 3 ≤ n →
      ∃ a b : ℕ, a ∈ A ∧ b ∈ A ∧ 0 < a ∧ a < b ∧ b < n ∧ a + n = 2 * b := by
    intro n hn
    have hex : ∃ k, n ≤ t k + Y k := ⟨n, by have := le_Y n; omega⟩
    obtain ⟨k, hk, hmin⟩ : ∃ k, n ≤ t k + Y k ∧ ∀ i < k, ¬ n ≤ t i + Y i :=
      ⟨Nat.find hex, Nat.find_spec hex, fun i hi => Nat.find_min hex hi⟩
    cases k with
    | zero => exact stage_cov 0 n (by rw [t_zero]; omega) hk
    | succ p => exact stage_cov (p + 1) n (by have := hmin p (by omega); have := t_succ p; omega) hk
  have sub_F : ∀ k, A ∩ Set.Iic (t k + Y k) ⊆
      ↑(((Finset.range (k + 1)).biUnion fun i => (R i).image (· + t i)) ∪
        (Finset.range 4).image (· + t (k + 1))) := by
    intro k
    rintro x ⟨hx, hm⟩
    obtain ⟨i, r, hr, rfl⟩ := (memA x).1 hx
    simp only [Set.mem_Iic] at hm
    rw [Finset.mem_coe]
    rcases lt_trichotomy i (k + 1) with h | h | h
    · refine Finset.mem_union_left _ ?_
      rw [Finset.mem_biUnion]
      exact ⟨i, Finset.mem_range.2 h, Finset.mem_image.2 ⟨r, hr, rfl⟩⟩
    · subst h
      refine Finset.mem_union_right _ ?_
      have := t_succ k
      rw [Finset.mem_image]
      exact ⟨r, Finset.mem_range.2 (by omega), rfl⟩
    · exfalso
      have hm2 : t (k + 1 + 1) ≤ t i := t_mono (by omega)
      have := t_succ (k + 1)
      have := t_succ k
      have := Y_ge (k + 1)
      omega
  have card_F : ∀ k, (((Finset.range (k + 1)).biUnion fun i => (R i).image (· + t i)) ∪
      (Finset.range 4).image (· + t (k + 1))).card ≤ (∑ i ∈ Finset.range (k + 1), (R i).card) + 4 := by
    intro k
    calc _ ≤ ((Finset.range (k + 1)).biUnion fun i => (R i).image (· + t i)).card +
          ((Finset.range 4).image (· + t (k + 1))).card := Finset.card_union_le _ _
      _ ≤ (∑ i ∈ Finset.range (k + 1), (R i).card) + 4 := by
          apply add_le_add
          · exact Finset.card_biUnion_le.trans (Finset.sum_le_sum fun i _ => Finset.card_image_le)
          · exact Finset.card_image_le.trans (by simp)
  have cnt_le : ∀ k, (A ∩ Set.Iic (t k + Y k)).ncard ≤
      (((Finset.range (k + 1)).biUnion fun i => (R i).image (· + t i)) ∪
        (Finset.range 4).image (· + t (k + 1))).card := by
    intro k
    rw [← Set.ncard_coe_finset]
    exact Set.ncard_le_ncard (sub_F k) (Finset.finite_toSet _)
  have geom : ∀ m : ℕ, ∑ i ∈ Finset.range (m + 1), 1675 * 2 ^ (i * i) < 1675 * 2 ^ (m * m + 1) := by
    intro m
    induction m with
    | zero => first | simp | decide | norm_num [Finset.sum_range_one]
    | succ m ih =>
      rw [Finset.sum_range_succ]
      have h1 : 2 ^ (m * m + 1) ≤ 2 ^ ((m + 1) * (m + 1)) :=
        Nat.pow_le_pow_right (by norm_num) (by nlinarith)
      have h2 : 2 ^ ((m + 1) * (m + 1) + 1) = 2 * 2 ^ ((m + 1) * (m + 1)) := by ring
      omega
  have cnt_bound : ∀ m : ℕ, (A ∩ Set.Iic (t (m + 1) + Y (m + 1))).ncard ≤
      1675 * 2 ^ ((m + 1) * (m + 1)) + 1679 * 2 ^ (m * m + 1) := by
    intro m
    have h1 := cnt_le (m + 1)
    have h2 := card_F (m + 1)
    have h3 : ∑ i ∈ Finset.range (m + 1 + 1), (R i).card ≤
        ∑ i ∈ Finset.range (m + 1 + 1), 1675 * 2 ^ (i * i) :=
      Finset.sum_le_sum fun i _ => by have := (R_spec i).2; omega
    have h4 : ∑ i ∈ Finset.range (m + 1 + 1), 1675 * 2 ^ (i * i) =
        ∑ i ∈ Finset.range (m + 1), 1675 * 2 ^ (i * i) + 1675 * 2 ^ ((m + 1) * (m + 1)) :=
      Finset.sum_range_succ _ _
    have h5 := geom m
    have h6 : 0 < 2 ^ (m * m + 1) := by positivity
    omega
  have pow_split : ∀ m : ℕ, (2 : ℝ) ^ ((m + 1) * (m + 1)) = 2 ^ (m * m + 1) * 4 ^ m := by
    intro m
    rw [show (m + 1) * (m + 1) = (m * m + 1) + 2 * m by ring, pow_add, pow_mul] <;> norm_num
  refine ⟨A, covering, ?_⟩
  intro ε hε N
  obtain ⟨m0, hm0⟩ : ∃ m0 : ℕ, 1679 / ε < 4 ^ m0 := pow_unbounded_of_one_lt _ (by norm_num)
  have h0 : 1679 < 4 ^ m0 * ε := by
    first
    | exact (div_lt_iff₀ hε).1 hm0
    | exact (div_lt_iff hε).1 hm0
    | (rw [div_lt_iff₀ hε] at hm0; exact hm0)
  obtain ⟨m, hm⟩ : ∃ m : ℕ, m = max m0 N := ⟨_, rfl⟩
  have hmN : N ≤ m := by rw [hm]; exact le_max_right m0 N
  have hm0m : m0 ≤ m := by rw [hm]; exact le_max_left m0 N
  refine ⟨t (m + 1) + Y (m + 1), ?_, ?_⟩
  · have := le_Y (m + 1); omega
  · obtain ⟨P, hP⟩ : ∃ P : ℝ, P = (2 : ℝ) ^ ((m + 1) * (m + 1)) := ⟨_, rfl⟩
    obtain ⟨Q, hQ⟩ : ∃ Q : ℝ, Q = (2 : ℝ) ^ (m * m + 1) := ⟨_, rfl⟩
    have hPQ : P = Q * 4 ^ m := by rw [hP, hQ]; exact pow_split m
    have hc : ((A ∩ Set.Iic (t (m + 1) + Y (m + 1))).ncard : ℝ) ≤ 1675 * P + 1679 * Q := by
      have := cnt_bound m
      rw [hP, hQ]; exact_mod_cast this
    have hQ0 : 0 < Q := by rw [hQ]; positivity
    have hP0 : 0 < P := by rw [hP]; positivity
    have h4n : 4 ^ m0 ≤ 4 ^ m := Nat.pow_le_pow_right (by norm_num) hm0m
    have h4 : (4 : ℝ) ^ m0 ≤ 4 ^ m := by exact_mod_cast h4n
    have h423 : 1679 < ε * 4 ^ m := by
      have := mul_le_mul_of_nonneg_left h4 hε.le
      linarith
    have hQP : 1679 * Q ≤ ε * P := by
      rw [hPQ]
      have := mul_lt_mul_of_pos_right h423 hQ0
      linarith
    have hYm := hYe (m + 1)
    have hx : (786432 : ℝ) * P ^ 2 ≤ ((t (m + 1) + Y (m + 1) : ℕ) : ℝ) := by
      have e : (2 ^ ((m + 1) * (m + 1))) ^ 2 = 4 ^ ((m + 1) * (m + 1)) := by
        rw [← pow_mul, mul_comm, pow_mul] <;> norm_num
      have hn : 786432 * (2 ^ ((m + 1) * (m + 1))) ^ 2 ≤ t (m + 1) + Y (m + 1) := by
        rw [e]; omega
      rw [hP]; exact_mod_cast hn
    have s3 := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
    have s0 : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
    have s1 : 1 ≤ Real.sqrt 3 := by nlinarith
    have hsq2 : (512 * Real.sqrt 3 * P) ^ 2 ≤ ((t (m + 1) + Y (m + 1) : ℕ) : ℝ) := by
      have e3 : (512 * Real.sqrt 3 * P) ^ 2 = 262144 * Real.sqrt 3 ^ 2 * P ^ 2 := by ring
      rw [e3, s3]
      linarith
    have hnn : 0 ≤ 512 * Real.sqrt 3 * P := mul_nonneg (mul_nonneg (by norm_num) s0) hP0.le
    have hsq : 512 * Real.sqrt 3 * P ≤ Real.sqrt ((t (m + 1) + Y (m + 1) : ℕ) : ℝ) := by
      first
      | exact Real.le_sqrt_of_sq_le hsq2
      | exact le_trans (le_abs_self _) (Real.abs_le_sqrt hsq2)
      | exact (Real.le_sqrt hnn).2 hsq2
      | (have h' := Real.sqrt_le_sqrt hsq2; rwa [Real.sqrt_sq hnn] at h')
    have hεP : 0 < ε * P := mul_pos hε hP0
    have hk : 0 ≤ 1675 * Real.sqrt 3 / 1536 + ε := by linarith
    have e4 : (1675 * Real.sqrt 3 / 1536 + ε) * (512 * Real.sqrt 3 * P) =
        1675 * Real.sqrt 3 ^ 2 / 3 * P + 512 * Real.sqrt 3 * (ε * P) := by ring
    have h1e : 1 * (ε * P) ≤ Real.sqrt 3 * (ε * P) := mul_le_mul_of_nonneg_right s1 hεP.le
    calc ((A ∩ Set.Iic (t (m + 1) + Y (m + 1))).ncard : ℝ) ≤ 1675 * P + 1679 * Q := hc
      _ ≤ 1675 * P + ε * P := by linarith
      _ ≤ (1675 * Real.sqrt 3 / 1536 + ε) * (512 * Real.sqrt 3 * P) := by
          rw [e4, s3]; linarith
      _ ≤ (1675 * Real.sqrt 3 / 1536 + ε) * Real.sqrt ((t (m + 1) + Y (m + 1) : ℕ) : ℝ) :=
          mul_le_mul_of_nonneg_left hsq hk