import GaloisForLFunctions.HTGeometry.PolynomialPhaseMomentGap

open Filter Finset PowerSeries MvPolynomial Polynomial Topology Asymptotics Set

namespace GaloisForLFunctions

noncomputable section

def polynomialPatternSourceSum {M D : ℕ}
    (p : Fin M → Fin (D + 1)) : ℕ :=
  ∑ r : Fin M, (r : ℕ) * (p r : ℕ)

noncomputable def minimalPolynomialPatternSourceSum {M D : ℕ}
    (S : Finset (Fin M → Fin (D + 1))) (hS : S.Nonempty) : ℕ :=
  (S.image polynomialPatternSourceSum).min'
    (Finset.image_nonempty.mpr hS)

noncomputable def polynomialPatternLeastSourceClass {M D : ℕ}
    (S : Finset (Fin M → Fin (D + 1))) (hS : S.Nonempty) :
    Finset (Fin M → Fin (D + 1)) :=
  S.filter fun p => polynomialPatternSourceSum p =
    minimalPolynomialPatternSourceSum S hS

theorem polynomialPatternLeastSourceClass_nonempty {M D : ℕ}
    (S : Finset (Fin M → Fin (D + 1))) (hS : S.Nonempty) :
    (polynomialPatternLeastSourceClass S hS).Nonempty := by
  classical
  have hminmem : minimalPolynomialPatternSourceSum S hS ∈
      S.image polynomialPatternSourceSum := Finset.min'_mem _ _
  obtain ⟨p, hpS, hp⟩ := Finset.mem_image.mp hminmem
  exact ⟨p, Finset.mem_filter.mpr ⟨hpS, hp⟩⟩

theorem polynomialPatternLeastSourceClass_subset {M D : ℕ}
    (S : Finset (Fin M → Fin (D + 1))) (hS : S.Nonempty) :
    polynomialPatternLeastSourceClass S hS ⊆ S :=
  Finset.filter_subset _ _

theorem sourceSum_eq_of_mem_polynomialPatternLeastSourceClass {M D : ℕ}
    {S : Finset (Fin M → Fin (D + 1))} {hS : S.Nonempty}
    {p : Fin M → Fin (D + 1)}
    (hp : p ∈ polynomialPatternLeastSourceClass S hS) :
    polynomialPatternSourceSum p = minimalPolynomialPatternSourceSum S hS :=
  (Finset.mem_filter.mp hp).2

theorem minimalSourceSum_lt_of_mem_not_class {M D : ℕ}
    {S : Finset (Fin M → Fin (D + 1))} (hS : S.Nonempty)
    {p : Fin M → Fin (D + 1)} (hpS : p ∈ S)
    (hpC : p ∉ polynomialPatternLeastSourceClass S hS) :
    minimalPolynomialPatternSourceSum S hS < polynomialPatternSourceSum p := by
  classical
  have hle : minimalPolynomialPatternSourceSum S hS ≤ polynomialPatternSourceSum p :=
    Finset.min'_le _ _ (Finset.mem_image.mpr ⟨p, hpS, rfl⟩)
  have hne : minimalPolynomialPatternSourceSum S hS ≠ polynomialPatternSourceSum p := by
    intro heq
    exact hpC (Finset.mem_filter.mpr ⟨hpS, heq.symm⟩)
  exact lt_of_le_of_ne hle hne

theorem eventually_polynomialPatternPower_gap_of_sourceSum_lt
    {β : ℝ} (hβ : 2 < β) {M D : ℕ}
    (p₀ p : Fin M → Fin (D + 1))
    (hcount₀ : (∑ r, (p₀ r : ℕ)) = D)
    (hcount : (∑ r, (p r : ℕ)) = D)
    (hsum : polynomialPatternSourceSum p₀ < polynomialPatternSourceSum p) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ x : ℝ in atTop,
      c * x ^ (β - 1) ≤
        polynomialPatternPowerValuation β p x -
          polynomialPatternPowerValuation β p₀ x := by
  let d := polynomialRealCoeffFinsupp (atomPatternDifferencePolynomial p₀ p)
  have hm0 : stretchedMoment d 0 = 0 := by
    dsimp [d]
    rw [stretchedMoment_atomPatternDifference p₀ p hcount₀ hcount,
      polynomialPatternMoment_zero, polynomialPatternMoment_zero,
      hcount₀, hcount]
    simp
  have hm1 : 0 < stretchedMoment d 1 := by
    dsimp [d]
    rw [stretchedMoment_atomPatternDifference p₀ p hcount₀ hcount,
      polynomialPatternMoment_one, polynomialPatternMoment_one, sub_pos]
    have hsum' : (∑ r : Fin M, (r : ℕ) * (p₀ r : ℕ)) <
        ∑ r : Fin M, (r : ℕ) * (p r : ℕ) := by
      simpa [polynomialPatternSourceSum] using hsum
    exact_mod_cast hsum'
  have hpoch : 0 < (descPochhammer ℝ 1).eval β := by
    apply descPochhammer_eval_pos_of_natCast_lt
    norm_num
    linarith
  let c₀ := polynomialPowerDifferenceCoefficient β d 1
  have hc₀ : 0 < c₀ := by
    dsimp [c₀, polynomialPowerDifferenceCoefficient]
    exact div_pos (mul_pos hm1 hpoch) (by positivity)
  have hequiv := polynomialPowerFiniteDifference_isEquivalent d 1
    (by intro k hk; interval_cases k; exact hm0) hm1.ne' hpoch.ne'
  have hequiv' : polynomialPowerFiniteDifference β d ~[atTop]
      fun x => c₀ * x ^ (β - 1) := by
    simpa [c₀] using hequiv
  have hleadPos : ∀ᶠ x : ℝ in atTop, 0 < c₀ * x ^ (β - 1) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    exact mul_pos hc₀ (Real.rpow_pos_of_pos hx _)
  have hhalf := eventually_half_le_of_isEquivalent_positive hequiv' hleadPos
  refine ⟨c₀ / 2, by positivity, ?_⟩
  filter_upwards [hhalf] with x hx
  rw [polynomialPatternPowerValuation_sub β x p₀ p hcount₀ hcount]
  convert hx using 1 ; ring

theorem exists_uniform_eventually_finset_rpow_gap {α : Type*}
    [DecidableEq α] (T : Finset α) (η : ℝ) (V : α → ℝ → ℝ)
    (hgap : ∀ a ∈ T, ∃ c : ℝ, 0 < c ∧ ∀ᶠ x : ℝ in atTop,
      c * x ^ η ≤ V a x) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ x : ℝ in atTop,
      ∀ a ∈ T, c * x ^ η ≤ V a x := by
  classical
  by_cases hT : T.Nonempty
  · choose c hcpos hc using fun a : ↥T => hgap a.1 a.2
    let U : Finset ↥T := Finset.univ
    let cmin : ℝ := (U.image c).min'
      (Finset.image_nonempty.mpr (by simpa [U] using hT))
    have hcminMem : cmin ∈ U.image c := Finset.min'_mem _ _
    obtain ⟨a, haU, hac⟩ := Finset.mem_image.mp hcminMem
    have hcminPos : 0 < cmin := by rw [← hac]; exact hcpos a
    have hcle : ∀ a : ↥T, cmin ≤ c a := by
      intro a
      exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨a, by simp [U], rfl⟩)
    have hall : ∀ᶠ x : ℝ in atTop, ∀ a : ↥T,
        c a * x ^ η ≤ V a.1 x := eventually_all.mpr (fun a => hc a)
    refine ⟨cmin, hcminPos, ?_⟩
    filter_upwards [hall, eventually_ge_atTop (0 : ℝ)] with x hx hx0
    intro a ha
    let asub : ↥T := ⟨a, ha⟩
    exact (mul_le_mul_of_nonneg_right (hcle asub)
      (Real.rpow_nonneg hx0 _)).trans (hx asub)
  · have hTempty : T = ∅ := Finset.not_nonempty_iff_eq_empty.mp hT
    subst T
    exact ⟨1, one_pos, Eventually.of_forall (fun x a ha => by simp at ha)⟩

theorem eventually_uniform_polynomialPatternPower_source_gap
    {β : ℝ} (hβ : 2 < β) {M D : ℕ}
    (S : Finset (Fin M → Fin (D + 1))) (hS : S.Nonempty)
    (hcount : ∀ p ∈ S, (∑ r, (p r : ℕ)) = D)
    (p₀ : Fin M → Fin (D + 1))
    (hp₀ : p₀ ∈ polynomialPatternLeastSourceClass S hS) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ x : ℝ in atTop,
      ∀ p ∈ S \ polynomialPatternLeastSourceClass S hS,
        c * x ^ (β - 1) ≤
          polynomialPatternPowerValuation β p x -
            polynomialPatternPowerValuation β p₀ x := by
  classical
  let C := polynomialPatternLeastSourceClass S hS
  let T := S \ C
  have hp₀S : p₀ ∈ S := polynomialPatternLeastSourceClass_subset S hS hp₀
  have hp₀sum : polynomialPatternSourceSum p₀ =
      minimalPolynomialPatternSourceSum S hS :=
    sourceSum_eq_of_mem_polynomialPatternLeastSourceClass hp₀
  have hgap : ∀ p ∈ T, ∃ c : ℝ, 0 < c ∧ ∀ᶠ x : ℝ in atTop,
      c * x ^ (β - 1) ≤
        polynomialPatternPowerValuation β p x -
          polynomialPatternPowerValuation β p₀ x := by
    intro p hpT
    have hpS : p ∈ S := (Finset.mem_sdiff.mp hpT).1
    have hpC : p ∉ C := (Finset.mem_sdiff.mp hpT).2
    have hsum : polynomialPatternSourceSum p₀ < polynomialPatternSourceSum p := by
      rw [hp₀sum]
      exact minimalSourceSum_lt_of_mem_not_class hS hpS hpC
    exact eventually_polynomialPatternPower_gap_of_sourceSum_lt hβ p₀ p
      (hcount p₀ hp₀S) (hcount p hpS) hsum
  simpa [T, C] using exists_uniform_eventually_finset_rpow_gap T (β - 1)
    (fun p x => polynomialPatternPowerValuation β p x -
      polynomialPatternPowerValuation β p₀ x) hgap

theorem eventually_uniform_polynomialPatternPower_gap
    {β : ℝ} (hβ : 2 < β) {M D : ℕ}
    (S : Finset (Fin M → Fin (D + 1))) (hS : S.Nonempty)
    (hcount : ∀ p ∈ S, (∑ r, (p r : ℕ)) = D)
    {Csum : ℕ}
    (hsum : ∀ p ∈ S, (∑ r : Fin M, (r : ℕ) * (p r : ℕ)) = Csum)
    (p₀ : Fin M → Fin (D + 1))
    (hp₀ : p₀ ∈ polynomialPatternMinimalCluster
      (R := Nat.ceil β - 2) S hS) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ x : ℝ in atTop,
      ∀ p ∈ S \ polynomialPatternMinimalCluster
          (R := Nat.ceil β - 2) S hS,
        c * x ^ (β - (Nat.ceil β - 1 : ℕ)) ≤
          polynomialPatternPowerValuation β p x -
            polynomialPatternPowerValuation β p₀ x := by
  classical
  let C := polynomialPatternMinimalCluster (R := Nat.ceil β - 2) S hS
  let T := S \ C
  have hp₀S : p₀ ∈ S := polynomialPatternMinimalCluster_subset S hS hp₀
  have hgap : ∀ p ∈ T, ∃ c : ℝ, 0 < c ∧ ∀ᶠ x : ℝ in atTop,
      c * x ^ (β - (Nat.ceil β - 1 : ℕ)) ≤
        polynomialPatternPowerValuation β p x -
          polynomialPatternPowerValuation β p₀ x := by
    intro p hpT
    have hpS : p ∈ S := (Finset.mem_sdiff.mp hpT).1
    have hpC : p ∉ C := (Finset.mem_sdiff.mp hpT).2
    obtain ⟨i, hprev, hi⟩ :=
      exists_first_signature_moment_lt_of_mem_not_cluster hS hp₀ hpS hpC
    exact eventually_polynomialPatternPower_gap_of_signature_lt hβ p₀ p
      (hcount p₀ hp₀S) (hcount p hpS)
      ((hsum p₀ hp₀S).trans (hsum p hpS).symm) i hprev hi
  simpa [T, C] using exists_uniform_eventually_finset_rpow_gap T
    (β - (Nat.ceil β - 1 : ℕ))
    (fun p x => polynomialPatternPowerValuation β p x -
      polynomialPatternPowerValuation β p₀ x) hgap

theorem polynomialPowerFiniteDifference_natCast_eq_stretchedMoment
    (d : ℕ →₀ ℝ) (k : ℕ) (hcancel : ∀ j < k, stretchedMoment d j = 0)
    (x : ℝ) :
    polynomialPowerFiniteDifference (k : ℝ) d x = stretchedMoment d k := by
  classical
  rw [polynomialPowerFiniteDifference, Finsupp.sum, stretchedMoment, Finsupp.sum]
  simp_rw [Real.rpow_natCast, add_pow, Finset.mul_sum]
  rw [Finset.sum_comm]
  calc
    ∑ i ∈ Finset.range (k + 1),
        ∑ r ∈ d.support,
          d r * (x ^ i * (r : ℝ) ^ (k - i) * (k.choose i : ℝ)) =
        ∑ i ∈ Finset.range (k + 1),
          ((k.choose i : ℝ) * x ^ i) *
            ∑ r ∈ d.support, d r * (r : ℝ) ^ (k - i) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r hr
      ring
    _ = ∑ i ∈ Finset.range (k + 1),
          ((k.choose i : ℝ) * x ^ i) * stretchedMoment d (k - i) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [stretchedMoment, Finsupp.sum]
    _ = ((k.choose 0 : ℝ) * x ^ 0) * stretchedMoment d (k - 0) := by
      apply Finset.sum_eq_single 0
      · intro i hi hi0
        rw [hcancel (k - i) (by
          have hik : i ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
          omega), mul_zero]
      · simp
    _ = stretchedMoment d k := by simp

theorem eventually_abs_polynomialPatternPower_sub_le_of_same_signature
    {β : ℝ} (hβ : 2 < β) {M D : ℕ}
    (p₀ p : Fin M → Fin (D + 1))
    (hcount₀ : (∑ r, (p₀ r : ℕ)) = D)
    (hcount : (∑ r, (p r : ℕ)) = D)
    (hsum : (∑ r : Fin M, (r : ℕ) * (p₀ r : ℕ)) =
      ∑ r : Fin M, (r : ℕ) * (p r : ℕ))
    (hsig : polynomialPatternSignature (Nat.ceil β - 2) p₀ =
      polynomialPatternSignature (Nat.ceil β - 2) p) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℝ in atTop,
      |polynomialPatternPowerValuation β p x -
        polynomialPatternPowerValuation β p₀ x| ≤ C := by
  let d := polynomialRealCoeffFinsupp (atomPatternDifferencePolynomial p₀ p)
  have hceil3 : 3 ≤ Nat.ceil β := by
    by_contra hnot
    have hceil2 : Nat.ceil β ≤ 2 := by omega
    have : β ≤ (2 : ℝ) := Nat.ceil_le.mp hceil2
    linarith
  have hsigfun : (fun i : Fin (Nat.ceil β - 2) =>
      polynomialPatternMoment p₀ ((i : ℕ) + 2)) =
      fun i : Fin (Nat.ceil β - 2) =>
        polynomialPatternMoment p ((i : ℕ) + 2) := by
    apply List.ofFn_injective
    exact hsig
  have heqMoment : ∀ j < Nat.ceil β,
      polynomialPatternMoment p₀ j = polynomialPatternMoment p j := by
    intro j hj
    rcases lt_trichotomy j 1 with hj0 | hj1 | hj2
    · have : j = 0 := by omega
      subst j
      rw [polynomialPatternMoment_zero, polynomialPatternMoment_zero,
        hcount₀, hcount]
    · subst j
      rw [polynomialPatternMoment_one, polynomialPatternMoment_one, hsum]
    · let i : Fin (Nat.ceil β - 2) := ⟨j - 2, by omega⟩
      have hi := congrFun hsigfun i
      have hij : (i : ℕ) + 2 = j := by dsimp [i]; omega
      simpa only [hij] using hi
  have hcancelCeil : ∀ j < Nat.ceil β, stretchedMoment d j = 0 := by
    intro j hj
    dsimp [d]
    rw [stretchedMoment_atomPatternDifference p₀ p hcount₀ hcount,
      heqMoment j hj]
    simp
  by_cases hp : p = p₀
  · subst p
    exact ⟨1, one_pos, Eventually.of_forall (fun x => by simp)⟩
  obtain ⟨μ, hμD, hcancel, hmoment⟩ :=
    exists_first_atomPatternDifference_moment p₀ p (Ne.symm hp) hcount₀ hcount
  have hceilμ : Nat.ceil β ≤ μ := by
    by_contra hnot
    have hμceil : μ < Nat.ceil β := by omega
    exact hmoment (hcancelCeil μ hμceil)
  by_cases hβnat : β = (Nat.ceil β : ℝ)
  · let k := Nat.ceil β
    have hcancelK : ∀ j < k, stretchedMoment d j = 0 := by
      simpa [k] using hcancelCeil
    refine ⟨|stretchedMoment d k| + 1, by positivity, ?_⟩
    apply Eventually.of_forall
    intro x
    rw [polynomialPatternPowerValuation_sub β x p₀ p hcount₀ hcount,
      hβnat, polynomialPowerFiniteDifference_natCast_eq_stretchedMoment d k hcancelK]
    linarith [abs_nonneg (stretchedMoment d k)]
  · have hβceil : β < (Nat.ceil β : ℝ) := by
      have hle : β ≤ (Nat.ceil β : ℝ) := Nat.le_ceil β
      exact lt_of_le_of_ne hle hβnat
    have hβμ : β < (μ : ℝ) := hβceil.trans_le (Nat.cast_le.mpr hceilμ)
    have hpoch : (descPochhammer ℝ μ).eval β ≠ 0 := by
      rw [descPochhammer_eval_eq_prod_range]
      apply Finset.prod_ne_zero_iff.mpr
      intro j hj hzero
      have hβj : β = (j : ℝ) := sub_eq_zero.mp hzero
      apply hβnat
      rw [hβj, Nat.ceil_natCast]
    have hequiv := polynomialPowerFiniteDifference_isEquivalent d μ hcancel hmoment hpoch
    have hlead : Tendsto
        (fun x : ℝ => polynomialPowerDifferenceCoefficient β d μ * x ^ (β - μ))
        atTop (𝓝 0) := by
      have hneg : 0 < (μ : ℝ) - β := sub_pos.mpr hβμ
      have hpw : Tendsto (fun x : ℝ => x ^ (-((μ : ℝ) - β))) atTop (𝓝 0) :=
        tendsto_rpow_neg_atTop hneg
      simpa [neg_sub] using hpw.const_mul (polynomialPowerDifferenceCoefficient β d μ)
    have hdiff : Tendsto (polynomialPowerFiniteDifference β d) atTop (𝓝 0) :=
      hequiv.symm.tendsto_nhds hlead
    have hsmall : ∀ᶠ x : ℝ in atTop,
        |polynomialPowerFiniteDifference β d x| < 1 := by
      have hmetric := (Metric.tendsto_atTop.1 hdiff) 1 one_pos
      simpa [Real.dist_eq] using hmetric
    refine ⟨1, one_pos, ?_⟩
    filter_upwards [hsmall] with x hx
    rw [polynomialPatternPowerValuation_sub β x p₀ p hcount₀ hcount]
    exact hx.le

theorem exists_uniform_eventually_finset_abs_bound {α : Type*}
    [DecidableEq α] (T : Finset α) (V : α → ℝ → ℝ)
    (hbound : ∀ a ∈ T, ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℝ in atTop,
      |V a x| ≤ C) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℝ in atTop,
      ∀ a ∈ T, |V a x| ≤ C := by
  classical
  by_cases hT : T.Nonempty
  · choose C hCpos hC using fun a : ↥T => hbound a.1 a.2
    let U : Finset ↥T := Finset.univ
    let Cmax : ℝ := (U.image C).max'
      (Finset.image_nonempty.mpr (by simpa [U] using hT))
    have hCmaxMem : Cmax ∈ U.image C := Finset.max'_mem _ _
    obtain ⟨a, haU, haC⟩ := Finset.mem_image.mp hCmaxMem
    have hCmaxPos : 0 < Cmax := by rw [← haC]; exact hCpos a
    have hCle : ∀ a : ↥T, C a ≤ Cmax := by
      intro a
      exact Finset.le_max' _ _ (Finset.mem_image.mpr ⟨a, by simp [U], rfl⟩)
    have hall : ∀ᶠ x : ℝ in atTop, ∀ a : ↥T,
        |V a.1 x| ≤ C a := eventually_all.mpr (fun a => hC a)
    refine ⟨Cmax, hCmaxPos, ?_⟩
    filter_upwards [hall] with x hx
    intro a ha
    let asub : ↥T := ⟨a, ha⟩
    exact (hx asub).trans (hCle asub)
  · have hTempty : T = ∅ := Finset.not_nonempty_iff_eq_empty.mp hT
    subst T
    exact ⟨1, one_pos, Eventually.of_forall (fun x a ha => by simp at ha)⟩

theorem eventually_uniform_polynomialPatternPower_cluster_bound
    {β : ℝ} (hβ : 2 < β) {M D : ℕ}
    (S : Finset (Fin M → Fin (D + 1))) (hS : S.Nonempty)
    (hcount : ∀ p ∈ S, (∑ r, (p r : ℕ)) = D)
    {Csum : ℕ}
    (hsum : ∀ p ∈ S, (∑ r : Fin M, (r : ℕ) * (p r : ℕ)) = Csum)
    (p₀ : Fin M → Fin (D + 1))
    (hp₀ : p₀ ∈ polynomialPatternMinimalCluster
      (R := Nat.ceil β - 2) S hS) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℝ in atTop,
      ∀ p ∈ polynomialPatternMinimalCluster
          (R := Nat.ceil β - 2) S hS,
        |polynomialPatternPowerValuation β p x -
          polynomialPatternPowerValuation β p₀ x| ≤ C := by
  classical
  let T := polynomialPatternMinimalCluster (R := Nat.ceil β - 2) S hS
  have hp₀S : p₀ ∈ S := polynomialPatternMinimalCluster_subset S hS hp₀
  have hbound : ∀ p ∈ T, ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℝ in atTop,
      |polynomialPatternPowerValuation β p x -
        polynomialPatternPowerValuation β p₀ x| ≤ C := by
    intro p hpT
    have hpS : p ∈ S := polynomialPatternMinimalCluster_subset S hS hpT
    have hsig : polynomialPatternSignature (Nat.ceil β - 2) p₀ =
        polynomialPatternSignature (Nat.ceil β - 2) p := by
      rw [signature_eq_of_mem_polynomialPatternMinimalCluster hp₀,
        signature_eq_of_mem_polynomialPatternMinimalCluster hpT]
    exact eventually_abs_polynomialPatternPower_sub_le_of_same_signature hβ p₀ p
      (hcount p₀ hp₀S) (hcount p hpS)
      ((hsum p₀ hp₀S).trans (hsum p hpS).symm) hsig
  simpa [T] using exists_uniform_eventually_finset_abs_bound T
    (fun p x => polynomialPatternPowerValuation β p x -
      polynomialPatternPowerValuation β p₀ x) hbound

noncomputable def polynomialPatternClusterMinValuation {M D : ℕ}
    (β : ℝ) (C : Finset (Fin M → Fin (D + 1))) (hC : C.Nonempty)
    (x : ℝ) : ℝ :=
  (C.image (fun p => polynomialPatternPowerValuation β p x)).min'
    (Finset.image_nonempty.mpr hC)

theorem polynomialPatternClusterMinValuation_le {M D : ℕ}
    (β : ℝ) {C : Finset (Fin M → Fin (D + 1))} (hC : C.Nonempty)
    (x : ℝ) {p : Fin M → Fin (D + 1)} (hp : p ∈ C) :
    polynomialPatternClusterMinValuation β C hC x ≤
      polynomialPatternPowerValuation β p x := by
  exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨p, hp, rfl⟩)

theorem exists_pattern_eq_clusterMinValuation {M D : ℕ}
    (β : ℝ) {C : Finset (Fin M → Fin (D + 1))} (hC : C.Nonempty)
    (x : ℝ) :
    ∃ p ∈ C, polynomialPatternPowerValuation β p x =
      polynomialPatternClusterMinValuation β C hC x := by
  have hmem : polynomialPatternClusterMinValuation β C hC x ∈
      C.image (fun p => polynomialPatternPowerValuation β p x) :=
    Finset.min'_mem _ _
  exact Finset.mem_image.mp hmem

theorem eventually_polynomialPatternPower_cluster_delta_bounds
    {β : ℝ} (hβ : 2 < β) {M D : ℕ}
    (S : Finset (Fin M → Fin (D + 1))) (hS : S.Nonempty)
    (hcount : ∀ p ∈ S, (∑ r, (p r : ℕ)) = D)
    {Csum : ℕ}
    (hsum : ∀ p ∈ S, (∑ r : Fin M, (r : ℕ) * (p r : ℕ)) = Csum)
    (p₀ : Fin M → Fin (D + 1))
    (hp₀ : p₀ ∈ polynomialPatternMinimalCluster
      (R := Nat.ceil β - 2) S hS) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℝ in atTop,
      ∀ p ∈ polynomialPatternMinimalCluster
          (R := Nat.ceil β - 2) S hS,
        0 ≤ polynomialPatternPowerValuation β p x -
            polynomialPatternClusterMinValuation β
              (polynomialPatternMinimalCluster (R := Nat.ceil β - 2) S hS)
              (polynomialPatternMinimalCluster_nonempty S hS) x ∧
        polynomialPatternPowerValuation β p x -
            polynomialPatternClusterMinValuation β
              (polynomialPatternMinimalCluster (R := Nat.ceil β - 2) S hS)
              (polynomialPatternMinimalCluster_nonempty S hS) x ≤ 2 * C := by
  classical
  let T := polynomialPatternMinimalCluster (R := Nat.ceil β - 2) S hS
  let hT : T.Nonempty := polynomialPatternMinimalCluster_nonempty S hS
  obtain ⟨C, hC, hbound⟩ :=
    eventually_uniform_polynomialPatternPower_cluster_bound hβ S hS hcount hsum p₀ hp₀
  refine ⟨C, hC, ?_⟩
  filter_upwards [hbound] with x hx
  intro p hp
  obtain ⟨pmin, hpmin, hpminEq⟩ :=
    exists_pattern_eq_clusterMinValuation β hT x
  have hpBound := hx p hp
  have hpminBound := hx pmin hpmin
  have hminle := polynomialPatternClusterMinValuation_le β hT x hp
  constructor
  · exact sub_nonneg.mpr hminle
  · rw [← hpminEq]
    have h₁ : polynomialPatternPowerValuation β p x -
        polynomialPatternPowerValuation β p₀ x ≤ C :=
      (le_abs_self _).trans hpBound
    have h₂ : polynomialPatternPowerValuation β p₀ x -
        polynomialPatternPowerValuation β pmin x ≤ C :=
      by simpa only [neg_sub] using (neg_le_abs _).trans hpminBound
    linarith

end

end GaloisForLFunctions
