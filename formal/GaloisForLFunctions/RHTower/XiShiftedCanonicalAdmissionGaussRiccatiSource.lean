import GaloisForLFunctions.RHTower.XiShiftedCanonicalAdmissionGaussEdgeArithmeticSource
import GaloisForLFunctions.RHTower.XiShiftedCanonicalAdmissionConnection

open Matrix Polynomial
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Relative Gaussian-visible part of current adaptive source. -/
def xiShiftedCanonicalAdmissionRelativeGaussBulk (y : ℝ) (n : ℕ) : ℝ :=
  let s : ℕ → ℝ := fun k => (xiShiftedReciprocalMoment y k).re
  HTGeometry.adaptiveOrthoGaussAggregate s n /
    HTGeometry.monicOrthoNormSq s n

theorem xiShiftedCanonicalAdmissionRelativeGaussBulk_eq_visibleEnergy
    {y : ℝ} {n : ℕ} (hn : 0 < n)
    (hH : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) (n + 2)).PosDef) :
    xiShiftedCanonicalAdmissionRelativeGaussBulk y n =
      HTGeometry.adaptiveOrthoJacobiEnergy
          (fun k => (xiShiftedReciprocalMoment y k).re) n -
        (n + 1 : ℝ) * HTGeometry.monicOrthoBeta
          (fun k => (xiShiftedReciprocalMoment y k).re) (n + 1) := by
  let s : ℕ → ℝ := fun k => (xiShiftedReciprocalMoment y k).re
  let hbelow := HTGeometry.positiveMomentFormBelow_of_hankelPosDef hH
  have haggregate := HTGeometry.adaptiveOrthoGaussAggregate_eq_visibleJacobiEnergy
    hbelow hn (le_refl (n + 2))
  have hnorm : 0 < HTGeometry.monicOrthoNormSq s n :=
    HTGeometry.monicOrtho_inner_self_pos_below hbelow (by omega)
  unfold xiShiftedCanonicalAdmissionRelativeGaussBulk
  dsimp only [s]
  rw [haggregate]
  apply mul_div_cancel_left₀
  simpa only [s] using ne_of_gt hnorm

theorem xiShiftedCanonicalAdmissionRelativeGaussBulk_pos
    {y : ℝ} {n : ℕ} (hn : 0 < n)
    (hH : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) (n + 2)).PosDef) :
    0 < xiShiftedCanonicalAdmissionRelativeGaussBulk y n := by
  let s : ℕ → ℝ := fun k => (xiShiftedReciprocalMoment y k).re
  let hbelow := HTGeometry.positiveMomentFormBelow_of_hankelPosDef hH
  have haggregate : 0 < HTGeometry.adaptiveOrthoGaussAggregate s n :=
    HTGeometry.adaptiveOrthoGaussAggregate_pos hbelow hn (le_refl (n + 2))
  have hnorm : 0 < HTGeometry.monicOrthoNormSq s n :=
    HTGeometry.monicOrtho_inner_self_pos_below hbelow (by omega)
  unfold xiShiftedCanonicalAdmissionRelativeGaussBulk
  dsimp only [s]
  exact div_pos haggregate hnorm

/-- Exact energy/dissipation decomposition behind adaptive source forcing. -/
theorem two_mul_adaptiveOrthoJacobiEnergy_eq_cumulativeDissipation_add_riccatiDrift
    {y : ℝ} {n : ℕ} (hn : 0 < n)
    (hH : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) (n + 2)).PosDef) :
    2 * HTGeometry.adaptiveOrthoJacobiEnergy
        (fun k => (xiShiftedReciprocalMoment y k).re) n =
      xiShiftedCanonicalAdmissionCumulativeJacobiDissipation y n +
        HTGeometry.monicOrthoAlpha
            (fun k => (xiShiftedReciprocalMoment y k).re) n *
          xiShiftedCanonicalAdmissionCumulativeJacobiFlux y n +
        2 * (n : ℝ) *
          HTGeometry.monicOrthoAlpha
            (fun k => (xiShiftedReciprocalMoment y k).re) n ^ 2 := by
  let s : ℕ → ℝ := fun k => (xiShiftedReciprocalMoment y k).re
  let alpha := HTGeometry.monicOrthoAlpha s n
  have htrace := xiShiftedCanonicalAdmissionCumulativeJacobiFlux_eq_trace hn hH
  have hsquares :
      (∑ j ∈ Finset.range n,
          (HTGeometry.monicOrthoAlpha s j + alpha / 2) ^ 2) =
        (∑ j ∈ Finset.range n, HTGeometry.monicOrthoAlpha s j ^ 2) +
          alpha * (∑ j ∈ Finset.range n, HTGeometry.monicOrthoAlpha s j) +
          (n : ℝ) * alpha ^ 2 / 4 := by
    have hpoint (j : ℕ) :
        (HTGeometry.monicOrthoAlpha s j + alpha / 2) ^ 2 =
          HTGeometry.monicOrthoAlpha s j ^ 2 +
            alpha * HTGeometry.monicOrthoAlpha s j + alpha ^ 2 / 4 := by ring
    simp_rw [hpoint]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
    simp [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    ring
  rw [htrace]
  simp only [HTGeometry.adaptiveOrthoJacobiEnergy,
    xiShiftedCanonicalAdmissionCumulativeJacobiDissipation]
  change 2 *
      ((∑ j ∈ Finset.range n,
          (HTGeometry.monicOrthoAlpha s j + alpha / 2) ^ 2) +
        (3 * (n : ℝ) / 4 + 1) * alpha ^ 2 +
        2 * (∑ j ∈ Finset.range n, HTGeometry.monicOrthoBeta s j) +
        (n + 1 : ℝ) *
          (HTGeometry.monicOrthoBeta s n + HTGeometry.monicOrthoBeta s (n + 1))) = _
  rw [hsquares]
  dsimp only [alpha]
  ring

theorem hasDerivAt_xiShiftedCanonicalAdmissionCumulativeJacobiFlux_eq_sourceRiccati
    {y : ℝ} (hy : 0 < y) {n : ℕ} (hn : 0 < n)
    (hH : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) (n + 2)).PosDef) :
    HasDerivAt
      (fun v => xiShiftedCanonicalAdmissionCumulativeJacobiFlux v n)
      (HTGeometry.monicOrthoAlpha
            (fun k => (xiShiftedReciprocalMoment y k).re) n *
          xiShiftedCanonicalAdmissionCumulativeJacobiFlux y n +
        2 * (n : ℝ) *
          HTGeometry.monicOrthoAlpha
            (fun k => (xiShiftedReciprocalMoment y k).re) n ^ 2 -
        2 * HTGeometry.adaptiveOrthoJacobiEnergy
          (fun k => (xiShiftedReciprocalMoment y k).re) n) y := by
  have hderiv := hasDerivAt_xiShiftedCanonicalAdmissionCumulativeJacobiFlux hy hn hH
  have henergy :=
    two_mul_adaptiveOrthoJacobiEnergy_eq_cumulativeDissipation_add_riccatiDrift hn hH
  apply hderiv.congr_deriv
  linarith

theorem hasDerivAt_xiShiftedCanonicalAdmissionCumulativeJacobiFlux_eq_gaussRiccati
    {y : ℝ} (hy : 0 < y) {n : ℕ} (hn : 0 < n)
    (hH : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) (n + 2)).PosDef) :
    HasDerivAt
      (fun v => xiShiftedCanonicalAdmissionCumulativeJacobiFlux v n)
      (HTGeometry.monicOrthoAlpha
            (fun k => (xiShiftedReciprocalMoment y k).re) n *
          xiShiftedCanonicalAdmissionCumulativeJacobiFlux y n +
        2 * (n : ℝ) *
          HTGeometry.monicOrthoAlpha
            (fun k => (xiShiftedReciprocalMoment y k).re) n ^ 2 -
        2 * xiShiftedCanonicalAdmissionRelativeGaussBulk y n -
        2 * (n + 1 : ℝ) * HTGeometry.monicOrthoBeta
          (fun k => (xiShiftedReciprocalMoment y k).re) (n + 1)) y := by
  have hderiv :=
    hasDerivAt_xiShiftedCanonicalAdmissionCumulativeJacobiFlux_eq_sourceRiccati
      hy hn hH
  have hbulk := xiShiftedCanonicalAdmissionRelativeGaussBulk_eq_visibleEnergy hn hH
  apply hderiv.congr_deriv
  linarith

theorem hasDerivAt_xiShiftedCanonicalAdmissionCumulativeJacobiFlux_eq_literalArithmeticRiccati
    {w : ℝ} (hw : 1 / 2 < w) {n : ℕ} (hn : 0 < n)
    (hH : (HTGeometry.momentHankelMatrix
      (xiShiftedRealMomentSequence w) (n + 2)).PosDef) :
    HasDerivAt
      (fun v => xiShiftedCanonicalAdmissionCumulativeJacobiFlux v n)
      (HTGeometry.monicOrthoAlpha (xiShiftedRealMomentSequence w) n *
          xiShiftedCanonicalAdmissionCumulativeJacobiFlux (w ^ 2) n +
        2 * (n : ℝ) *
          HTGeometry.monicOrthoAlpha (xiShiftedRealMomentSequence w) n ^ 2 -
        xiShiftedAdaptiveMixedCompletedArithmeticSource w
            (HTGeometry.monicMomentAdmissionPolynomial
              (xiShiftedRealMomentSequence w) n) /
          HTGeometry.monicOrthoNormSq (xiShiftedRealMomentSequence w) n) (w ^ 2) := by
  have hy : 0 < w ^ 2 := sq_pos_of_pos (lt_trans (by norm_num) hw)
  have hderiv :=
    hasDerivAt_xiShiftedCanonicalAdmissionCumulativeJacobiFlux_eq_sourceRiccati
      hy hn hH
  change HasDerivAt
      (fun v => xiShiftedCanonicalAdmissionCumulativeJacobiFlux v n)
      (HTGeometry.monicOrthoAlpha (xiShiftedRealMomentSequence w) n *
          xiShiftedCanonicalAdmissionCumulativeJacobiFlux (w ^ 2) n +
        2 * (n : ℝ) *
          HTGeometry.monicOrthoAlpha (xiShiftedRealMomentSequence w) n ^ 2 -
        2 * HTGeometry.adaptiveOrthoJacobiEnergy
          (xiShiftedRealMomentSequence w) n) (w ^ 2) at hderiv
  have hsource :=
    xiShiftedAdaptiveMixedCompletedArithmeticSource_canonicalAdmission_eq_jacobiEnergy
      hw hn hH
  let hbelow := HTGeometry.positiveMomentFormBelow_of_hankelPosDef hH
  have hnorm : 0 < HTGeometry.monicOrthoNormSq (xiShiftedRealMomentSequence w) n :=
    HTGeometry.monicOrtho_inner_self_pos_below hbelow (by omega)
  apply hderiv.congr_deriv
  rw [hsource]
  field_simp [ne_of_gt hnorm]

/-- Weighted Cauchy law for the trace multiplicities `2,…,2,1`. -/
theorem cumulativeJacobiTrace_sq_le_mul_alphaEnergy
    (a : ℕ → ℝ) (b : ℝ) {n : ℕ} (hn : 0 < n) :
    (2 * (∑ j ∈ Finset.range n, a j) + b) ^ 2 ≤
      (2 * n + 1 : ℝ) *
        (2 * (∑ j ∈ Finset.range n, a j ^ 2) + b ^ 2) := by
  let A : ℝ := ∑ j ∈ Finset.range n, a j
  let Q : ℝ := ∑ j ∈ Finset.range n, a j ^ 2
  have hcs := sq_sum_le_card_mul_sum_sq
    (s := Finset.range n) (f := a)
  simp only [Finset.card_range] at hcs
  change A ^ 2 ≤ (n : ℝ) * Q at hcs
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hgap : 0 ≤ ((4 : ℝ) * n + 2) * ((n : ℝ) * Q - A ^ 2) :=
    mul_nonneg (by positivity) (sub_nonneg.mpr hcs)
  have hsquare : 0 ≤ 2 * (A - (n : ℝ) * b) ^ 2 :=
    mul_nonneg (by norm_num) (sq_nonneg _)
  have hmul : (n : ℝ) * (2 * A + b) ^ 2 ≤
      (n : ℝ) * ((2 * n + 1 : ℝ) * (2 * Q + b ^ 2)) := by
    nlinarith
  change (2 * A + b) ^ 2 ≤ (2 * n + 1 : ℝ) * (2 * Q + b ^ 2)
  exact le_of_mul_le_mul_left hmul hnR

theorem xiShiftedCanonicalAdmissionCumulativeJacobiFlux_sq_lt_mul_dissipation
    {y : ℝ} {n : ℕ} (hn : 0 < n)
    (hH : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) (n + 2)).PosDef) :
    xiShiftedCanonicalAdmissionCumulativeJacobiFlux y n ^ 2 <
      (2 * n + 1 : ℝ) *
        xiShiftedCanonicalAdmissionCumulativeJacobiDissipation y n := by
  let s : ℕ → ℝ := fun k => (xiShiftedReciprocalMoment y k).re
  let hbelow := HTGeometry.positiveMomentFormBelow_of_hankelPosDef hH
  have htrace := xiShiftedCanonicalAdmissionCumulativeJacobiFlux_eq_trace hn hH
  have hcs := cumulativeJacobiTrace_sq_le_mul_alphaEnergy
    (fun j => HTGeometry.monicOrthoAlpha s j)
    (HTGeometry.monicOrthoAlpha s n) hn
  have hbetas : 0 ≤ ∑ j ∈ Finset.range n, HTGeometry.monicOrthoBeta s j := by
    apply Finset.sum_nonneg
    intro j hj
    rcases j with _ | j
    · simp [HTGeometry.monicOrthoBeta]
    · exact (HTGeometry.monicOrthoBeta_pos_below hbelow (Nat.succ_pos j) (by
        have hjn := Finset.mem_range.mp hj
        omega)).le
  have hboundary : 0 < HTGeometry.monicOrthoBeta s n +
      HTGeometry.monicOrthoBeta s (n + 1) :=
    add_pos
      (HTGeometry.monicOrthoBeta_pos_below hbelow hn (by omega))
      (HTGeometry.monicOrthoBeta_pos_below hbelow (by omega) (by omega))
  rw [htrace]
  simp only [xiShiftedCanonicalAdmissionCumulativeJacobiDissipation]
  change (2 * (∑ j ∈ Finset.range n, HTGeometry.monicOrthoAlpha s j) +
      HTGeometry.monicOrthoAlpha s n) ^ 2 < _
  have hweight : 0 < (2 * n + 1 : ℝ) := by positivity
  have hextra : 0 <
      4 * (∑ j ∈ Finset.range n, HTGeometry.monicOrthoBeta s j) +
        2 * (n + 1 : ℝ) *
          (HTGeometry.monicOrthoBeta s n + HTGeometry.monicOrthoBeta s (n + 1)) := by
    exact add_pos_of_nonneg_of_pos (mul_nonneg (by norm_num) hbetas)
      (mul_pos (mul_pos (by norm_num) (by positivity)) hboundary)
  have henergyLt :
      2 * (∑ j ∈ Finset.range n, HTGeometry.monicOrthoAlpha s j ^ 2) +
          HTGeometry.monicOrthoAlpha s n ^ 2 <
        2 * (∑ j ∈ Finset.range n, HTGeometry.monicOrthoAlpha s j ^ 2) +
          HTGeometry.monicOrthoAlpha s n ^ 2 +
          4 * (∑ j ∈ Finset.range n, HTGeometry.monicOrthoBeta s j) +
          2 * (n + 1 : ℝ) *
            (HTGeometry.monicOrthoBeta s n +
              HTGeometry.monicOrthoBeta s (n + 1)) := by
    linarith
  exact lt_of_le_of_lt hcs (mul_lt_mul_of_pos_left henergyLt hweight)

/-- Universal strict scalar Riccati contraction of current adaptive flux. -/
theorem deriv_xiShiftedCanonicalAdmissionCumulativeJacobiFlux_mul_degreeWeight_lt_neg_sq
    {y : ℝ} (hy : 0 < y) {n : ℕ} (hn : 0 < n)
    (hH : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) (n + 2)).PosDef) :
    (2 * n + 1 : ℝ) *
        deriv (fun v => xiShiftedCanonicalAdmissionCumulativeJacobiFlux v n) y <
      -xiShiftedCanonicalAdmissionCumulativeJacobiFlux y n ^ 2 := by
  rw [(hasDerivAt_xiShiftedCanonicalAdmissionCumulativeJacobiFlux hy hn hH).deriv]
  have hstrict :=
    xiShiftedCanonicalAdmissionCumulativeJacobiFlux_sq_lt_mul_dissipation hn hH
  linarith

/-- Degree-free cumulative flux.  Multiplicity `2n+1` is forced by the exact source law. -/
def xiShiftedCanonicalAdmissionRenormalizedJacobiFlux (y : ℝ) (n : ℕ) : ℝ :=
  xiShiftedCanonicalAdmissionCumulativeJacobiFlux y n / (2 * n + 1 : ℝ)

/-- The literal arithmetic producer is the forcing term in renormalized flux evolution. -/
theorem hasDerivAt_xiShiftedCanonicalAdmissionRenormalizedJacobiFlux_eq_literalArithmeticRiccati
    {w : ℝ} (hw : 1 / 2 < w) {n : ℕ} (hn : 0 < n)
    (hH : (HTGeometry.momentHankelMatrix
      (xiShiftedRealMomentSequence w) (n + 2)).PosDef) :
    HasDerivAt
      (fun v => xiShiftedCanonicalAdmissionRenormalizedJacobiFlux v n)
      ((HTGeometry.monicOrthoAlpha (xiShiftedRealMomentSequence w) n *
            xiShiftedCanonicalAdmissionCumulativeJacobiFlux (w ^ 2) n +
          2 * (n : ℝ) *
            HTGeometry.monicOrthoAlpha (xiShiftedRealMomentSequence w) n ^ 2 -
          xiShiftedAdaptiveMixedCompletedArithmeticSource w
              (HTGeometry.monicMomentAdmissionPolynomial
                (xiShiftedRealMomentSequence w) n) /
            HTGeometry.monicOrthoNormSq (xiShiftedRealMomentSequence w) n) /
        (2 * n + 1 : ℝ)) (w ^ 2) := by
  simpa only [xiShiftedCanonicalAdmissionRenormalizedJacobiFlux] using
    (hasDerivAt_xiShiftedCanonicalAdmissionCumulativeJacobiFlux_eq_literalArithmeticRiccati
      hw hn hH).div_const (2 * n + 1 : ℝ)

/-- **Degree-uniform Riccati contraction.**  After forced trace-multiplicity normalization, every
positive admission chamber obeys the same scalar law `U′ < -U²`, independently of degree. -/
theorem deriv_xiShiftedCanonicalAdmissionRenormalizedJacobiFlux_lt_neg_sq
    {y : ℝ} (hy : 0 < y) {n : ℕ} (hn : 0 < n)
    (hH : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) (n + 2)).PosDef) :
    deriv (fun v => xiShiftedCanonicalAdmissionRenormalizedJacobiFlux v n) y <
      -xiShiftedCanonicalAdmissionRenormalizedJacobiFlux y n ^ 2 := by
  let c : ℝ := (2 * n + 1 : ℝ)
  have hc : 0 < c := by positivity
  have hderiv :=
    (hasDerivAt_xiShiftedCanonicalAdmissionCumulativeJacobiFlux hy hn hH).div_const c
  have hstrict :=
    deriv_xiShiftedCanonicalAdmissionCumulativeJacobiFlux_mul_degreeWeight_lt_neg_sq
      hy hn hH
  rw [(hasDerivAt_xiShiftedCanonicalAdmissionCumulativeJacobiFlux hy hn hH).deriv]
    at hstrict
  rw [show (fun v => xiShiftedCanonicalAdmissionRenormalizedJacobiFlux v n) =
      (fun v => xiShiftedCanonicalAdmissionCumulativeJacobiFlux v n / c) by
        funext v
        rfl,
    hderiv.deriv]
  unfold xiShiftedCanonicalAdmissionRenormalizedJacobiFlux
  dsimp only [c] at hc hstrict ⊢
  rw [div_pow]
  apply (div_lt_iff₀ hc).2
  have hcne : (2 * n + 1 : ℝ) ≠ 0 := ne_of_gt hc
  field_simp [hcne]
  nlinarith

/-- A strict Riccati contraction cannot enter the nonpositive half-line on a complete right ray.
This is a finite-time blow-down obstruction, proved without a limit assumption. -/
theorem pos_of_deriv_lt_neg_sq_on_Ioi
    {f : ℝ → ℝ} {A x : ℝ} (hx : A < x)
    (hf : ∀ t, A < t → DifferentiableAt ℝ f t)
    (hR : ∀ t, A < t → deriv f t < -(f t) ^ 2) :
    0 < f x := by
  have hcont : ContinuousOn f (Set.Ioi A) := by
    intro t ht
    exact (hf t ht).continuousAt.continuousWithinAt
  have hanti : StrictAntiOn f (Set.Ioi A) := by
    apply strictAntiOn_of_deriv_neg (convex_Ioi A) hcont
    intro t ht
    rw [interior_Ioi] at ht
    exact lt_of_lt_of_le (hR t ht) (neg_nonpos.mpr (sq_nonneg _))
  by_contra hnot
  have hxnonpos : f x ≤ 0 := le_of_not_gt hnot
  obtain ⟨x₀, hx₀A, hx₀neg⟩ : ∃ x₀ : ℝ, A < x₀ ∧ f x₀ < 0 := by
    rcases hxnonpos.eq_or_lt with hzero | hneg
    · refine ⟨x + 1, by linarith, ?_⟩
      have hdrop := hanti (Set.mem_Ioi.mpr hx)
        (Set.mem_Ioi.mpr (by linarith : A < x + 1)) (by linarith : x < x + 1)
      linarith
    · exact ⟨x, hx, hneg⟩
  let b : ℝ := x₀ - (f x₀)⁻¹
  have hxb : x₀ < b := by
    dsimp only [b]
    have hinvneg : (f x₀)⁻¹ < 0 := inv_lt_zero.mpr hx₀neg
    linarith
  have hbA : A < b := lt_trans hx₀A hxb
  have hneg : ∀ t ∈ Set.Icc x₀ b, f t < 0 := by
    intro t ht
    rcases ht.1.eq_or_lt with rfl | hxt
    · exact hx₀neg
    · exact lt_trans (hanti (Set.mem_Ioi.mpr hx₀A)
        (Set.mem_Ioi.mpr (lt_trans hx₀A hxt)) hxt) hx₀neg
  let g : ℝ → ℝ := f⁻¹ - id
  have hgcont : ContinuousOn g (Set.Icc x₀ b) := by
    have hfcont : ContinuousOn f (Set.Icc x₀ b) := by
      intro t ht
      exact (hf t (lt_of_lt_of_le hx₀A ht.1)).continuousAt.continuousWithinAt
    exact (hfcont.inv₀ (fun t ht => ne_of_lt (hneg t ht))).sub continuousOn_id
  have hgpos : ∀ t ∈ interior (Set.Icc x₀ b), 0 < deriv g t := by
    intro t ht
    rw [interior_Icc] at ht
    have htA : A < t := lt_trans hx₀A ht.1
    have hft := hf t htA
    have htmem : t ∈ Set.Icc x₀ b := ⟨ht.1.le, ht.2.le⟩
    have hftneg := hneg t htmem
    have hftne : f t ≠ 0 := ne_of_lt hftneg
    have hgd : HasDerivAt g (-deriv f t / (f t) ^ 2 - 1) t := by
      dsimp only [g]
      exact (hft.hasDerivAt.inv hftne).sub (hasDerivAt_id t)
    rw [hgd.deriv]
    have hsq : 0 < (f t) ^ 2 := sq_pos_of_ne_zero hftne
    have hratio : 1 < -deriv f t / (f t) ^ 2 := by
      apply (lt_div_iff₀ hsq).2
      nlinarith [hR t htA]
    linarith
  have hgmono : StrictMonoOn g (Set.Icc x₀ b) :=
    strictMonoOn_of_deriv_pos (convex_Icc x₀ b) hgcont hgpos
  have hgb := hgmono (Set.left_mem_Icc.mpr hxb.le)
    (Set.right_mem_Icc.mpr hxb.le) hxb
  have hinvbneg : (f b)⁻¹ < 0 :=
    inv_lt_zero.mpr (hneg b (Set.right_mem_Icc.mpr hxb.le))
  change (f x₀)⁻¹ - x₀ < (f b)⁻¹ - b at hgb
  dsimp only [b] at hgb
  linarith

/-- Terminal positive chambers force strictly positive normalized adaptive flux.  No recession
rate is assumed: finite-time Riccati blow-down supplies the sign. -/
theorem xiShiftedCanonicalAdmissionRenormalizedJacobiFlux_pos_of_terminalChamber
    {A y : ℝ} (hA : 0 ≤ A) (hy : A < y) {n : ℕ} (hn : 0 < n)
    (hchamber : ∀ v, A < v →
      (HTGeometry.momentHankelMatrix
        (fun k => (xiShiftedReciprocalMoment v k).re) (n + 2)).PosDef) :
    0 < xiShiftedCanonicalAdmissionRenormalizedJacobiFlux y n := by
  apply pos_of_deriv_lt_neg_sq_on_Ioi hy
  · intro v hv
    have hv0 : 0 < v := lt_of_le_of_lt hA hv
    exact ((hasDerivAt_xiShiftedCanonicalAdmissionCumulativeJacobiFlux
      hv0 hn (hchamber v hv)).div_const (2 * n + 1 : ℝ)).differentiableAt
  · intro v hv
    exact deriv_xiShiftedCanonicalAdmissionRenormalizedJacobiFlux_lt_neg_sq
      (lt_of_le_of_lt hA hv) hn (hchamber v hv)

/-- Every fixed shifted-Xi block has a complete terminal positive chamber in mass squared. -/
theorem exists_xiShiftedCanonicalAdmissionTerminalChamber (n : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ v, A < v →
      (HTGeometry.momentHankelMatrix
        (fun k => (xiShiftedReciprocalMoment v k).re) (n + 2)).PosDef := by
  have hevent :=
    (xiShiftedMomentHankelMatrix_squareParam_posDef_eventually (n + 2)).and
      (Filter.eventually_gt_atTop (1 : ℝ))
  obtain ⟨W, hW⟩ := Filter.eventually_atTop.mp hevent
  refine ⟨W ^ 2, sq_nonneg W, ?_⟩
  intro v hv
  let r := Real.sqrt v
  have hWdata := hW r
  have hWpos : 0 < W := by
    have := (hW W le_rfl).2
    linarith
  have hvpos : 0 < v := lt_of_le_of_lt (sq_nonneg W) hv
  have hrsq : r ^ 2 = v := Real.sq_sqrt hvpos.le
  have hrnonneg : 0 ≤ r := Real.sqrt_nonneg v
  have hWr : W < r := by
    nlinarith
  have hpos := (hWdata hWr.le).1
  rw [hrsq] at hpos
  have heq : HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment v k).re) (n + 2) =
      xiShiftedMomentHankelMatrix v (n + 2) := by
    ext i j
    rfl
  rwa [heq]

/-- **Unconditional terminal source-flow sign.**  Every fixed degree eventually enters a complete
positive chamber where its degree-normalized adaptive arithmetic flux is strictly positive. -/
theorem exists_xiShiftedCanonicalAdmissionRenormalizedJacobiFlux_terminal_pos
    {n : ℕ} (hn : 0 < n) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ y, A < y →
      0 < xiShiftedCanonicalAdmissionRenormalizedJacobiFlux y n := by
  obtain ⟨A, hA, hchamber⟩ := exists_xiShiftedCanonicalAdmissionTerminalChamber n
  refine ⟨A, hA, ?_⟩
  intro y hy
  exact xiShiftedCanonicalAdmissionRenormalizedJacobiFlux_pos_of_terminalChamber
    hA hy hn hchamber

end

end RHTower
