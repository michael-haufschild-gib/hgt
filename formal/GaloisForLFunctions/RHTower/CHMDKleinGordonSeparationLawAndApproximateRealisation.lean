import GaloisForLFunctions.RHTower.CHMDGrowthPositivityCollapseAndTwoPointCriterion

/-!
# CHMD: The Klein–Gordon Separation Law and the Approximate-Realisation Principle

This module records the exact boundary exposed by testing spectral-realisation candidates for the
CHMD causal wave `φ_Λ(y) = cosineShiftFn Λ sechHalf y` against its Laplace transform, the
Klein–Gordon pole series `kgPoleSeries`.

1. **Separation law.** Every nontrivial zero `ρ` has Klein–Gordon frequency
   `ρ_ρ = √(γ_ρ² + 2)` with `Re ρ_ρ > √(7/4)` **strictly** (`sqrt_seven_fourths_lt_re_kgFreq`), so
   every pole `± i ρ_ρ` of the pole series satisfies `|Im| > √(7/4)` and `|Re| < 1/2`
   (`kgPoleSet_subset`). The pole series is therefore analytic on the whole closed strip
   `|Im s| ≤ √(7/4)` (`analyticAt_kgPoleSeries_of_abs_im_le`).
2. **The pole of `ζ` sits exactly on the separation line.** The pole term of the causal wave is
   `(2 / cos²(1/4)) cos(u √(7/4))`; its Laplace transform is `(2 / cos²(1/4)) · s / (s² + 7/4)`
   (`integral_polePartWave_mul_cexp`), with poles at `± i √(7/4)`, which are regular points of the
   zero-side series. Hence the archimedean-minus-prime Laplace transform
   `kgPoleSeries − (2 / cos²(1/4)) s/(s² + 7/4)` is **not** analytic at `i √(7/4)`
   (`not_analyticAt_kgPoleSeries_sub_poleLaplace`): the prime side must carry the pole of `ζ`, and it
   carries it on the boundary of the strip where the Euler product converges absolutely.
3. **Approximate realisation suffices.** If the causal wave is a function attaining its maximum at
   the origin (for instance a matrix coefficient `Re⟨U(u)v, v⟩` of a unitary group) plus a function
   bounded above on `[0, ∞)`, then the Riemann Hypothesis holds
   (`riemannHypothesis_of_eq_add_of_le_zero_value`). A spectral realisation of the Klein–Gordon
   prime wave need not be exact: a bounded defect is allowed.

The content is the sharp boundary: positivity-preserving (elliptic, Euler-product) information
lives exactly in the strip `|Im s| < √(7/4)`, the pole of `ζ` is its boundary point, and every
Riemann-Hypothesis-sensitive pole lies strictly outside.
-/

open Complex MeasureTheory Set Filter Topology Zeta23
open scoped BigOperators ComplexConjugate

noncomputable section

namespace RHTower.CHMDSeparationLaw

open WeilOneSided WeilSpectral GaloisForLFunctions.HTGeometry RHTower.EvenSector
open RHTower.CHMDStage11 RHTower.CHMDStage13 RHTower.CHMDGrowthCollapse

/-! ## Section 1: The separation law -/

/-- **Sharp strict lower bound on every Klein–Gordon frequency**: `√(7/4) < Re √(γ_ρ² + 2)`. -/
theorem sqrt_seven_fourths_lt_re_kgFreq (ρ : zetaZeroConfig.carrier) :
    Real.sqrt (7 / 4) < (kgFreq ρ).re := by
  have hpos := re_kgFreq_pos ρ
  rw [Real.sqrt_lt' hpos]
  have hsq := kgFreq_sq ρ
  have h1 : (kgFreq ρ ^ 2).re = (kgFreq ρ).re ^ 2 - (kgFreq ρ).im ^ 2 := by simp [sq]
  rw [hsq, re_sq_add_two] at h1
  have him := im_sq_gammaOf_lt ρ
  nlinarith [sq_nonneg (Zeta23.gammaOf (ρ : ℂ)).re, sq_nonneg (kgFreq ρ).im]

/-- **Every pole of the Klein–Gordon pole series lies strictly beyond the separation line**:
`√(7/4) < |Im p|` and `|Re p| < 1/2`. -/
theorem kgPoleSet_subset :
    kgPoleSet ⊆ {s : ℂ | Real.sqrt (7 / 4) < |s.im| ∧ |s.re| < 1 / 2} := by
  rintro s ⟨ρ, h | h⟩
  · rw [h]
    simp only [mem_setOf_eq, Complex.I_mul_im, Complex.I_mul_re, abs_neg]
    exact ⟨(sqrt_seven_fourths_lt_re_kgFreq ρ).trans_le (le_abs_self _), abs_im_kgFreq_lt ρ⟩
  · rw [h]
    simp only [mem_setOf_eq, Complex.neg_im, Complex.neg_re, Complex.I_mul_im, Complex.I_mul_re,
      abs_neg, neg_neg]
    exact ⟨(sqrt_seven_fourths_lt_re_kgFreq ρ).trans_le (le_abs_self _), abs_im_kgFreq_lt ρ⟩

theorem notMem_kgPoleSet_of_abs_im_le {s : ℂ} (hs : |s.im| ≤ Real.sqrt (7 / 4)) :
    s ∉ kgPoleSet := fun h => by
  have := (kgPoleSet_subset h).1
  linarith

/-- **The pole series is analytic on the closed strip `|Im s| ≤ √(7/4)`.** -/
theorem analyticAt_kgPoleSeries_of_abs_im_le {s : ℂ} (hs : |s.im| ≤ Real.sqrt (7 / 4)) :
    AnalyticAt ℂ kgPoleSeries s :=
  analyticAt_kgPoleSeries (notMem_kgPoleSet_of_abs_im_le hs)

/-! ## Section 2: The pole of `ζ` sits exactly on the separation line -/

/-- The pole term of the causal wave, `evenPolePart (rhoCosShift u sechHalf)`. -/
def polePartWave (u : ℝ) : ℝ := evenPolePart (rhoCosShift u sechHalf)

theorem polePartWave_eq (u : ℝ) :
    polePartWave u = (2 / Real.cos (1 / 4 : ℝ) ^ 2) * Real.cos (u * Real.sqrt (7 / 4)) :=
  RHTower.CHMDStage13.evenPolePart_rhoCosShift_sechHalf u

theorem sqrt_seven_fourths_sq : Real.sqrt (7 / 4) ^ 2 = (7 / 4 : ℝ) :=
  Real.sq_sqrt (by norm_num)

theorem ofReal_sqrt_seven_fourths_sq : ((Real.sqrt (7 / 4) : ℝ) : ℂ) ^ 2 = 7 / 4 := by
  rw [← Complex.ofReal_pow, sqrt_seven_fourths_sq]
  push_cast
  ring

/-- **Laplace transform of the pole term**: `(2 / cos²(1/4)) · s / (s² + 7/4)` on `Re s > 0`, with
poles exactly at `± i √(7/4)`. -/
theorem integral_polePartWave_mul_cexp {s : ℂ} (hs : 0 < s.re) :
    ∫ u in Ioi (0 : ℝ), (polePartWave u : ℂ) * Complex.exp (-s * u) =
      ((2 / Real.cos (1 / 4 : ℝ) ^ 2 : ℝ) : ℂ) * (s / (s ^ 2 + 7 / 4)) := by
  set a : ℝ := Real.sqrt (7 / 4) with ha
  set c : ℝ := 2 / Real.cos (1 / 4 : ℝ) ^ 2 with hc
  have hpt : ∀ u : ℝ, (polePartWave u : ℂ) * Complex.exp (-s * u) =
      (c : ℂ) / 2 * Complex.exp (-(s - I * a) * u) +
        (c : ℂ) / 2 * Complex.exp (-(s + I * a) * u) := by
    intro u
    rw [polePartWave_eq, ← hc, ← ha, Complex.ofReal_mul, Complex.ofReal_cos, Complex.ofReal_mul]
    have e1 : Complex.exp (-(s - I * a) * u) = Complex.exp (u * a * I) * Complex.exp (-s * u) := by
      rw [← Complex.exp_add]; congr 1; ring
    have e2 : Complex.exp (-(s + I * a) * u) =
        Complex.exp (-(u * a) * I) * Complex.exp (-s * u) := by
      rw [← Complex.exp_add]; congr 1; ring
    rw [e1, e2, Complex.cos]
    ring
  simp_rw [hpt]
  have h1 : 0 < (s - I * a).re := by
    rw [Complex.sub_re, Complex.I_mul_re, Complex.ofReal_im]; linarith
  have h2 : 0 < (s + I * a).re := by
    rw [Complex.add_re, Complex.I_mul_re, Complex.ofReal_im]; linarith
  rw [integral_add ((integrableOn_cexp_neg_mul_ofReal_Ioi h1).const_mul _)
    ((integrableOn_cexp_neg_mul_ofReal_Ioi h2).const_mul _),
    integral_const_mul, integral_const_mul, integral_cexp_neg_mul_Ioi h1,
    integral_cexp_neg_mul_Ioi h2]
  have hne1 : s - I * a ≠ 0 := fun h => by rw [h] at h1; simp at h1
  have hne2 : s + I * a ≠ 0 := fun h => by rw [h] at h2; simp at h2
  have hprod : (s - I * a) * (s + I * a) = s ^ 2 + 7 / 4 := by
    linear_combination ofReal_sqrt_seven_fourths_sq - ((a : ℝ) : ℂ) ^ 2 * Complex.I_sq
  rw [← hprod]
  field_simp
  ring

/-- The rational function `s / (s² + 7/4)` is not analytic at its pole `i √(7/4)`. -/
theorem not_analyticAt_poleLaplace :
    ¬ AnalyticAt ℂ (fun s : ℂ => s / (s ^ 2 + 7 / 4)) (I * Real.sqrt (7 / 4)) := by
  intro h
  set a : ℝ := Real.sqrt (7 / 4) with ha
  have hapos : 0 < a := Real.sqrt_pos.mpr (by norm_num)
  set p₀ : ℂ := I * a with hp₀
  have hcont := h.continuousAt
  obtain ⟨δ, hδ, hδf⟩ := Metric.continuousAt_iff.mp hcont 1 one_pos
  set M : ℝ := ‖p₀ / (p₀ ^ 2 + 7 / 4)‖ + 1 with hM
  have hM0 : 0 < M := by positivity
  set t : ℝ := min (min (δ / 2) (a / 2)) (1 / (12 * M)) with ht
  have htpos : 0 < t := lt_min (lt_min (by positivity) (by positivity)) (by positivity)
  have htδ : t ≤ δ / 2 := (min_le_left _ _).trans (min_le_left _ _)
  have hta : t ≤ a / 2 := (min_le_left _ _).trans (min_le_right _ _)
  have htM : t ≤ 1 / (12 * M) := min_le_right _ _
  set s : ℂ := p₀ + t with hs
  have hdist : dist s p₀ < δ := by
    rw [hs, dist_eq_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos htpos]
    linarith
  have hbound := hδf hdist
  rw [dist_eq_norm] at hbound
  have hfs : ‖s / (s ^ 2 + 7 / 4)‖ ≤ M := by
    have := norm_sub_norm_le (s / (s ^ 2 + 7 / 4)) (p₀ / (p₀ ^ 2 + 7 / 4))
    rw [hM]; linarith
  -- the exact value near the pole
  have hprod : s ^ 2 + 7 / 4 = (s - p₀) * (s + p₀) := by
    have := ofReal_sqrt_seven_fourths_sq
    rw [hp₀]
    linear_combination (-1 : ℂ) * this + ((a : ℝ) : ℂ) ^ 2 * Complex.I_sq
  have hsp : s - p₀ = (t : ℂ) := by rw [hs]; ring
  have hnorm_num : a - t ≤ ‖s‖ := by
    have h1 := norm_sub_norm_le p₀ (-(t : ℂ))
    rw [sub_neg_eq_add, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos htpos] at h1
    have h2 : ‖p₀‖ = a := by
      rw [hp₀, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hapos]
    rw [h2] at h1
    exact h1.trans (le_of_eq (by rw [hs]))
  have hnorm_den : ‖s + p₀‖ ≤ 2 * a + t := by
    have h2 : ‖p₀‖ = a := by
      rw [hp₀, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hapos]
    calc ‖s + p₀‖ = ‖p₀ + p₀ + (t : ℂ)‖ := by rw [hs]; ring_nf
      _ ≤ ‖p₀ + p₀‖ + ‖(t : ℂ)‖ := norm_add_le _ _
      _ ≤ 2 * a + t := by
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos htpos]
          have := norm_add_le p₀ p₀
          linarith
  have hval : ‖s / (s ^ 2 + 7 / 4)‖ = ‖s‖ / (t * ‖s + p₀‖) := by
    rw [hprod, norm_div, norm_mul, hsp, Complex.norm_real, Real.norm_eq_abs, abs_of_pos htpos]
  have hden_pos : 0 < t * ‖s + p₀‖ := by
    have : 0 < ‖s + p₀‖ := by
      rw [norm_pos_iff]
      intro h0
      have := congrArg Complex.im h0
      rw [hs, hp₀] at this
      simp at this
      linarith
    positivity
  have hlow : 1 / (6 * t) ≤ ‖s / (s ^ 2 + 7 / 4)‖ := by
    rw [hval, div_le_div_iff₀ (by positivity) hden_pos]
    have h3 : 2 * a + t ≤ 3 * a := by linarith
    have h4 : a / 2 ≤ ‖s‖ := by linarith
    have h5 : ‖s + p₀‖ ≤ 3 * a := hnorm_den.trans h3
    nlinarith [norm_nonneg (s + p₀), norm_nonneg s]
  have hbig : M < 1 / (6 * t) := by
    rw [lt_div_iff₀ (by positivity)]
    calc M * (6 * t) ≤ M * (6 * (1 / (12 * M))) := by gcongr
      _ = 1 / 2 := by field_simp; ring
      _ < 1 := by norm_num
  linarith

/-- **The prime side carries the pole of `ζ` on the separation line**: the archimedean-minus-prime
Laplace transform `kgPoleSeries − (2 / cos²(1/4)) · s/(s² + 7/4)` is not analytic at `i √(7/4)`,
although the zero-side series itself is. -/
theorem not_analyticAt_kgPoleSeries_sub_poleLaplace :
    ¬ AnalyticAt ℂ (fun s : ℂ => kgPoleSeries s -
      ((2 / Real.cos (1 / 4 : ℝ) ^ 2 : ℝ) : ℂ) * (s / (s ^ 2 + 7 / 4))) (I * Real.sqrt (7 / 4)) := by
  intro h
  apply not_analyticAt_poleLaplace
  have hG : AnalyticAt ℂ kgPoleSeries (I * Real.sqrt (7 / 4)) := by
    apply analyticAt_kgPoleSeries_of_abs_im_le
    rw [Complex.I_mul_im, Complex.ofReal_re, abs_of_nonneg (Real.sqrt_nonneg _)]
  have hc : (Real.cos (1 / 4 : ℝ) ^ 2 : ℝ) ≠ 0 := pow_ne_zero 2 cos_one_fourth_pos.ne'
  have hcC : ((2 / Real.cos (1 / 4 : ℝ) ^ 2 : ℝ) : ℂ) ≠ 0 := by
    rw [Ne, Complex.ofReal_eq_zero]
    positivity
  have h2 : AnalyticAt ℂ (fun s : ℂ => ((2 / Real.cos (1 / 4 : ℝ) ^ 2 : ℝ) : ℂ)⁻¹ *
      (kgPoleSeries s - (kgPoleSeries s -
        ((2 / Real.cos (1 / 4 : ℝ) ^ 2 : ℝ) : ℂ) * (s / (s ^ 2 + 7 / 4)))))
      (I * Real.sqrt (7 / 4)) :=
    analyticAt_const.mul (hG.sub h)
  refine h2.congr (Filter.Eventually.of_forall fun s => ?_)
  simp only
  rw [sub_sub_cancel, inv_mul_cancel_left₀ hcC]

/-! ## Section 3: An approximate spectral realisation suffices -/

/-- **Approximate realisation principle.** If the causal wave decomposes as `p + e` where `p`
attains its maximum at the origin (as every matrix coefficient `Re⟨U(u)v, v⟩` of a unitary
one-parameter group does) and `e` is bounded above on `[0, ∞)`, then the Riemann Hypothesis holds.
A spectral realisation of the Klein–Gordon prime wave may therefore carry a bounded defect. -/
theorem riemannHypothesis_of_eq_add_of_le_zero_value {p e : ℝ → ℝ} (hp : ∀ y, p y ≤ p 0)
    {C : ℝ} (he : ∀ u : ℝ, 0 ≤ u → e u ≤ C) (h : ∀ u : ℝ, chmdWave u = p u + e u) :
    RiemannHypothesis :=
  riemannHypothesis_iff_chmdWave_bddAbove.mpr
    ⟨p 0 + C, fun u hu => by rw [h u]; linarith [hp u, he u hu]⟩

end RHTower.CHMDSeparationLaw

end
