import GaloisForLFunctions.SumProductArithmeticOfTheLogarithm.NormCollisionAmplification

/-!
# Count-distance rigidity

Translation by one couples to multiplicative cancellation: if a uniquely factored
integer-norm system represents r, r+1, mr and m(r+1), it represents m. A missing
integer thus forces a linear count deficit. Together with collision amplification,
this yields an exact count-distance trichotomy and bounded-error rigidity.
-/

noncomputable section

open scoped BigOperators Classical

namespace GaloisForLFunctions.SumProductArithmeticOfTheLogarithm

open GaloisForLFunctions.RigidArithmeticOfCuts

/-- The discrepancy of the integer-supported multiplicity count. -/
private noncomputable def prefixCountError (B : RHTower.BeurlingSystem) (n : ℕ) : ℤ :=
  ((∑ k ∈ Finset.Ioc 0 n, intCount B k : ℕ) : ℤ) - n

/-- A collision forces growing discrepancy at adjacent geometric thresholds. -/
private theorem collision_forces_prefix_error (B : RHTower.BeurlingSystem)
    (hdisc : B.IsDiscrete) {u v : B.Integer} (hne : u ≠ v)
    (huv : B.intNorm u = B.intNorm v) {m : ℕ} (hmu : B.intNorm u = m) (k : ℕ) :
    (k : ℤ) ≤ |prefixCountError B (m ^ k)| + |prefixCountError B (m ^ k - 1)| := by
  have hm : 1 ≤ m := by
    have h := B.one_le_intNorm u
    rw [hmu] at h
    exact_mod_cast h
  let M := m ^ k
  have hM : 1 ≤ M := by
    have hp : 0 < m ^ k := pow_pos (by omega) k
    exact hp
  have hrepr : M = M - 1 + 1 := by omega
  have hstep : (∑ i ∈ Finset.Ioc 0 M, intCount B i) =
      (∑ i ∈ Finset.Ioc 0 (M - 1), intCount B i) + intCount B M := by
    nth_rw 1 [hrepr]
    rw [Finset.sum_Ioc_succ_top (Nat.zero_le _), ← hrepr]
  have hstepZ : ((∑ i ∈ Finset.Ioc 0 M, intCount B i : ℕ) : ℤ) =
      ((∑ i ∈ Finset.Ioc 0 (M - 1), intCount B i : ℕ) : ℤ) + (intCount B M : ℤ) := by
    exact_mod_cast hstep
  have hd : prefixCountError B M - prefixCountError B (M - 1) =
      (intCount B M : ℤ) - 1 := by
    have hMi : ((M - 1 : ℕ) : ℤ) = (M : ℤ) - 1 := by omega
    dsimp only [prefixCountError]
    rw [hMi, hstepZ]
    ring
  have hcard : (k : ℤ) + 1 ≤ intCount B M := by
    exact_mod_cast intCount_pow_ge_of_collision B hdisc hne huv hmu k
  calc
    (k : ℤ) ≤ prefixCountError B M - prefixCountError B (M - 1) := by rw [hd]; omega
    _ ≤ |prefixCountError B M| + |prefixCountError B (M - 1)| :=
      (le_abs_self _).trans (abs_sub _ _)

/-- Consecutive integer norms cannot share a generator of integer norm greater than one. -/
theorem no_common_label_of_consecutive (B : RHTower.BeurlingSystem)
    (h : HasIntegerNorms B) {u v : B.Integer} {r : ℕ}
    (hu : B.intNorm u = r) (hv : B.intNorm v = (r + 1 : ℕ))
    (p : B.Label) : p ∈ u → p ∈ v → False := by
  intro hpu hpv
  obtain ⟨u', heu⟩ := Multiset.exists_cons_of_mem hpu
  obtain ⟨v', hev⟩ := Multiset.exists_cons_of_mem hpv
  obtain ⟨a, _, ha⟩ := exists_nat_intNorm B h u'
  obtain ⟨b, _, hb⟩ := exists_nat_intNorm B h v'
  obtain ⟨n, hn⟩ := h p
  have hn2 : 2 ≤ n := by
    have hp := B.one_lt_labelNorm p
    rw [hn] at hp
    exact_mod_cast hp
  rw [heu, ← Multiset.singleton_add, B.intNorm_add, B.intNorm_singleton, hn, ha] at hu
  rw [hev, ← Multiset.singleton_add, B.intNorm_add, B.intNorm_singleton, hn, hb] at hv
  have hna : n * a = r := by exact_mod_cast hu
  have hnb : n * b = r + 1 := by exact_mod_cast hv
  by_cases hab : a < b
  · have hmul := Nat.mul_le_mul_left n (show a + 1 ≤ b by omega)
    nlinarith only [hmul, hna, hnb, hn2]
  · have hmul := Nat.mul_le_mul_left n (show b ≤ a by omega)
    omega

/-- Representing r, r+1, mr and m(r+1) forces a representation of m under unique factorization. -/
theorem represent_of_cross (B : RHTower.BeurlingSystem) (h : HasIntegerNorms B)
    (hinj : Function.Injective B.intNorm) {m r : ℕ} (hr : 1 ≤ r)
    (hu : ∃ u : B.Integer, B.intNorm u = r)
    (hv : ∃ v : B.Integer, B.intNorm v = (r + 1 : ℕ))
    (hw : ∃ w : B.Integer, B.intNorm w = (m * r : ℕ))
    (hz : ∃ z : B.Integer, B.intNorm z = (m * (r + 1) : ℕ)) :
    ∃ g : B.Integer, B.intNorm g = m := by
  classical
  obtain ⟨u, hu⟩ := hu
  obtain ⟨v, hv⟩ := hv
  obtain ⟨w, hw⟩ := hw
  obtain ⟨z, hz⟩ := hz
  have he : w + v = u + z := hinj (by
    rw [B.intNorm_add, B.intNorm_add, hw, hv, hu, hz]
    push_cast
    ring)
  have huw : u ≤ w := by
    apply Multiset.le_iff_count.mpr
    intro p
    by_cases hp : p ∈ u
    · have hnot : p ∉ v := no_common_label_of_consecutive B h hu hv p hp
      have hc := congrArg (Multiset.count p) he
      simp only [Multiset.count_add, Multiset.count_eq_zero.mpr hnot] at hc
      omega
    · simp only [Multiset.count_eq_zero.mpr hp, Nat.zero_le]
  obtain ⟨g, hg⟩ := exists_add_of_le huw
  refine ⟨g, ?_⟩
  have hrR : (r : ℝ) ≠ 0 := by positivity
  have heq : (r : ℝ) * B.intNorm g = (r : ℝ) * m := by
    calc
      _ = B.intNorm w := by rw [hg, B.intNorm_add, hu]
      _ = (r : ℝ) * m := by rw [hw, Nat.cast_mul]; ring
  exact mul_left_cancel₀ hrR heq

/-- The actual finite ball is partitioned by its positive integer norms. -/
theorem countBall_eq_prefix (B : RHTower.BeurlingSystem) (h : HasIntegerNorms B)
    (hdisc : B.IsDiscrete) (N : ℕ) :
    B.countBall N = ∑ n ∈ Finset.Ioc 0 N, intCount B n := by
  classical
  let ν (g : B.Integer) := Classical.choose (exists_nat_intNorm B h g)
  have hν (g : B.Integer) : B.intNorm g = (ν g : ℝ) :=
    (Classical.choose_spec (exists_nat_intNorm B h g)).2
  have hν1 (g : B.Integer) : 1 ≤ ν g :=
    (Classical.choose_spec (exists_nat_intNorm B h g)).1
  let F := (hdisc (N : ℝ)).toFinset
  have hmap : (F : Set B.Integer).MapsTo ν (Finset.Ioc 0 N) := by
    intro g hg
    have hgN : B.intNorm g ≤ N := by
      simpa only [Finset.mem_coe, F, Set.Finite.mem_toFinset, Set.mem_setOf_eq] using hg
    have hnN : ν g ≤ N := by rw [hν] at hgN; exact_mod_cast hgN
    exact Finset.mem_Ioc.mpr ⟨hν1 g, hnN⟩
  rw [RHTower.BeurlingSystem.countBall, Set.ncard_eq_toFinset_card _ (hdisc _)]
  change F.card = _
  rw [Finset.card_eq_sum_card_fiberwise hmap]
  apply Finset.sum_congr rfl
  intro n hn
  have hfinite : {g : B.Integer | B.intNorm g = (n : ℝ)}.Finite :=
    (hdisc (n : ℝ)).subset (fun g hg => hg.le)
  rw [intCount, Set.ncard_eq_toFinset_card _ hfinite]
  congr 1
  ext g
  simp only [Finset.mem_filter, F, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
  constructor
  · rintro ⟨_, hgn⟩
    rw [hν, hgn]
  · intro hg
    refine ⟨?_, ?_⟩
    · rw [hg]
      exact_mod_cast (Finset.mem_Ioc.mp hn).2
    · exact_mod_cast (hν g).symm.trans hg

/-- A four-map incidence cover bounds the domain by four times the target cardinality. -/
private theorem card_le_four_mul_of_cover_by_injections (S M : Finset ℕ) (f₁ f₂ f₃ f₄ : ℕ → ℕ)
    (hi₁ : Function.Injective f₁) (hi₂ : Function.Injective f₂)
    (hi₃ : Function.Injective f₃) (hi₄ : Function.Injective f₄)
    (hc : ∀ r ∈ S, f₁ r ∈ M ∨ f₂ r ∈ M ∨ f₃ r ∈ M ∨ f₄ r ∈ M) :
    S.card ≤ 4 * M.card := by
  classical
  let F (f : ℕ → ℕ) := S.filter fun r => f r ∈ M
  have hb (f : ℕ → ℕ) (hi : Function.Injective f) : (F f).card ≤ M.card := by
    rw [← Finset.card_image_of_injective (F f) hi]
    apply Finset.card_le_card
    intro n hn
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hn
    exact (Finset.mem_filter.mp hr).2
  have hsub : S ⊆ ((F f₁ ∪ F f₂) ∪ F f₃) ∪ F f₄ := by
    intro r hr
    have := hc r hr
    simpa only [Finset.mem_union, F, Finset.mem_filter, hr, true_and,
      or_assoc] using this
  have h₁ := Finset.card_union_le (F f₁) (F f₂)
  have h₂ := Finset.card_union_le (F f₁ ∪ F f₂) (F f₃)
  have h₃ := Finset.card_union_le ((F f₁ ∪ F f₂) ∪ F f₃) (F f₄)
  have h₄ := Finset.card_le_card hsub
  have := hb f₁ hi₁
  have := hb f₂ hi₂
  have := hb f₃ hi₃
  have := hb f₄ hi₄
  omega

/-- A missing integer forces at least R/4 omissions below m(R+1). -/
theorem missing_quadruples (B : RHTower.BeurlingSystem) (h : HasIntegerNorms B)
    (hinj : Function.Injective B.intNorm) {m : ℕ} (hm : 1 ≤ m)
    (hmiss : ¬ ∃ g : B.Integer, B.intNorm g = m) (R : ℕ) :
    R ≤ 4 * ((Finset.Icc 1 (m * (R + 1))).filter
      (fun n : ℕ => ¬ ∃ g : B.Integer, B.intNorm g = (n : ℝ))).card := by
  classical
  let M := (Finset.Icc 1 (m * (R + 1))).filter
    (fun n : ℕ => ¬ ∃ g : B.Integer, B.intNorm g = (n : ℝ))
  have hi : Function.Injective (fun r : ℕ => m * r) := by
    intro a b hab
    exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < m) hab
  have his : Function.Injective (fun r : ℕ => m * (r + 1)) := by
    intro a b hab
    have := hi hab
    omega
  have hb := card_le_four_mul_of_cover_by_injections (Finset.Icc 1 R) M id (fun r => r + 1)
    (fun r => m * r) (fun r => m * (r + 1)) Function.injective_id
    (by intro a b hab; exact Nat.add_right_cancel hab) hi his ?_
  · simpa only [Nat.card_Icc, Nat.add_sub_cancel] using hb
  · intro r hr
    obtain ⟨hr₁, hrR⟩ := Finset.mem_Icc.mp hr
    have htop : R + 1 ≤ m * (R + 1) := by nlinarith only [hm]
    have hmr₁ : 1 ≤ m * r := Nat.mul_pos hm hr₁
    have hmrR := Nat.mul_le_mul_left m (show r ≤ R + 1 by omega)
    have hms₁ : 1 ≤ m * (r + 1) := Nat.mul_pos hm (by omega)
    have hmsR := Nat.mul_le_mul_left m (show r + 1 ≤ R + 1 by omega)
    by_contra! hn
    dsimp only [id] at hn
    apply hmiss
    apply represent_of_cross B h hinj hr₁
    · by_contra hh
      exact hn.1 (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hr₁, by omega⟩, hh⟩)
    · by_contra hh
      exact hn.2.1 (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, hh⟩)
    · by_contra hh
      exact hn.2.2.1 (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hmr₁, hmrR⟩, hh⟩)
    · by_contra hh
      exact hn.2.2.2 (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hms₁, hmsR⟩, hh⟩)

/-- With unique factorization, each norm multiplicity is its representability indicator. -/
theorem intCount_indicator_of_norm_injective (B : RHTower.BeurlingSystem)
    (hinj : Function.Injective B.intNorm) (n : ℕ) :
    intCount B n = if ∃ g : B.Integer, B.intNorm g = (n : ℝ) then 1 else 0 := by
  classical
  by_cases hh : ∃ g : B.Integer, B.intNorm g = (n : ℝ)
  · rw [if_pos hh]
    obtain ⟨g, hg⟩ := hh
    apply Set.ncard_eq_one.mpr
    refine ⟨g, ?_⟩
    ext g'
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    exact ⟨fun he => hinj (he.trans hg.symm), fun he => he ▸ hg⟩
  · rw [if_neg hh]
    have he : {g : B.Integer | B.intNorm g = (n : ℝ)} = ∅ := by
      ext g
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      exact fun hg => hh ⟨g, hg⟩
    rw [intCount, he, Set.ncard_empty]

/-- For an injective integer norm, represented and missing integers partition the interval. -/
theorem countBall_add_missing (B : RHTower.BeurlingSystem) (h : HasIntegerNorms B)
    (hdisc : B.IsDiscrete) (hinj : Function.Injective B.intNorm) (N : ℕ) :
    B.countBall N + ((Finset.Icc 1 N).filter
      (fun n : ℕ => ¬ ∃ g : B.Integer, B.intNorm g = (n : ℝ))).card = N := by
  classical
  have he : Finset.Ioc 0 N = Finset.Icc 1 N := by
    ext n
    simp only [Finset.mem_Ioc, Finset.mem_Icc]
    omega
  have hs : ((Finset.Icc 1 N).filter
      (fun n : ℕ => ¬ ∃ g : B.Integer, B.intNorm g = (n : ℝ))).card =
      ∑ n ∈ Finset.Icc 1 N, if ¬ ∃ g : B.Integer, B.intNorm g = (n : ℝ) then 1 else 0 := by
    simp
  rw [countBall_eq_prefix B h hdisc, he, hs, ← Finset.sum_add_distrib]
  calc
    _ = ∑ _n ∈ Finset.Icc 1 N, (1 : ℕ) := by
      apply Finset.sum_congr rfl
      intro n _
      rw [intCount_indicator_of_norm_injective B hinj]
      split_ifs <;> omega
    _ = N := by simp

/-- One missing integer forces a linear deficit on an explicit arithmetic progression. -/
theorem linear_deficit_of_missing (B : RHTower.BeurlingSystem)
    (h : HasIntegerNorms B) (hdisc : B.IsDiscrete)
    (hinj : Function.Injective B.intNorm) {m : ℕ} (hm : 1 ≤ m)
    (hmiss : ¬ ∃ g : B.Integer, B.intNorm g = (m : ℝ)) (k : ℕ) :
    B.countBall (m * (4 * k + 1) : ℕ) + k ≤ m * (4 * k + 1) := by
  have hb := missing_quadruples B h hinj hm hmiss (4 * k)
  have hc := countBall_add_missing B h hdisc hinj (m * (4 * k + 1))
  omega

/-- An injective integer norm either gives rational primes or omits an integer at least two. -/
theorem primes_or_missing_of_norm_injective (B : RHTower.BeurlingSystem) (h : HasIntegerNorms B)
    (hinj : Function.Injective B.intNorm) :
    (Nonempty {e : B.Label ≃ {p : ℕ // p.Prime} //
      ∀ l, B.labelNorm l = ((e l : ℕ) : ℝ)}) ∨
    ∃ m : ℕ, 2 ≤ m ∧ ¬ ∃ g : B.Integer, B.intNorm g = (m : ℝ) := by
  classical
  by_cases hh : ∃ m : ℕ, 2 ≤ m ∧ ¬ ∃ g : B.Integer, B.intNorm g = (m : ℝ)
  · exact Or.inr hh
  · left
    apply nonempty_label_equiv_primes h (n₀ := 2)
    intro n hn
    have hex : ∃ g : B.Integer, B.intNorm g = (n : ℝ) := by
      by_contra hm
      exact hh ⟨n, hn, hm⟩
    obtain ⟨g, hg⟩ := hex
    exact ⟨g, hg, fun g' hg' => hinj (hg'.trans hg.symm)⟩

/-- Every discrete integer-norm system is classical, has amplified collisions, or has a linear count deficit. -/
theorem count_distance_trichotomy (B : RHTower.BeurlingSystem)
    (h : HasIntegerNorms B) (hdisc : B.IsDiscrete) :
    (Nonempty {e : B.Label ≃ {p : ℕ // p.Prime} //
      ∀ l, B.labelNorm l = ((e l : ℕ) : ℝ)}) ∨
    (∃ m : ℕ, 2 ≤ m ∧ ∀ k : ℕ,
      (k : ℤ) ≤ |(B.countBall (m ^ k : ℕ) : ℤ) - (m ^ k : ℕ)| +
        |(B.countBall (m ^ k - 1 : ℕ) : ℤ) - (m ^ k - 1 : ℕ)|) ∨
    (∃ m : ℕ, 2 ≤ m ∧ ∀ k : ℕ,
      B.countBall (m * (4 * k + 1) : ℕ) + k ≤ m * (4 * k + 1)) := by
  classical
  by_cases hinj : Function.Injective B.intNorm
  · rcases primes_or_missing_of_norm_injective B h hinj with hp | ⟨m, hm, hmiss⟩
    · exact Or.inl hp
    · exact Or.inr (Or.inr ⟨m, hm, fun k =>
        linear_deficit_of_missing B h hdisc hinj (by omega) hmiss k⟩)
  · simp only [Function.Injective] at hinj
    push Not at hinj
    obtain ⟨u, v, huv, hne⟩ := hinj
    obtain ⟨m, _, hmu⟩ := exists_nat_intNorm B h u
    refine Or.inr (Or.inl ⟨m, collision_norm_ge_two B hne huv hmu, ?_⟩)
    intro k
    have hb := collision_forces_prefix_error B hdisc hne huv hmu k
    simpa only [prefixCountError, ← countBall_eq_prefix B h hdisc] using hb

/-- Bounded count error at slope one forces precisely the rational-prime labels and norms. -/
theorem primes_of_bounded_count_error (B : RHTower.BeurlingSystem)
    (h : HasIntegerNorms B) (hdisc : B.IsDiscrete) (C : ℕ)
    (hC : ∀ N : ℕ, |(B.countBall N : ℤ) - N| ≤ C) :
    Nonempty {e : B.Label ≃ {p : ℕ // p.Prime} //
      ∀ l, B.labelNorm l = ((e l : ℕ) : ℝ)} := by
  rcases count_distance_trichotomy B h hdisc with hp | ⟨m, _, hj⟩ | ⟨m, _, hd⟩
  · exact hp
  · have hjump := hj (2 * C + 1)
    have h₁ := hC (m ^ (2 * C + 1))
    have h₂ := hC (m ^ (2 * C + 1) - 1)
    omega
  · have hdef := hd (C + 1)
    have hb := (abs_le.mp (hC (m * (4 * (C + 1) + 1)))).1
    omega

end GaloisForLFunctions.SumProductArithmeticOfTheLogarithm
