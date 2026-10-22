import GaloisForLFunctions.RHTower.PrimeAlmostAllShortIntervalsAsymptotic
import GaloisForLFunctions.RHTower.ZetaZeroSumMeanSquarePlain
import GaloisForLFunctions.RHTower.ShortIntervalBlockReductionPsi

/-!
# The second moment of the multiplicative window increment

The two-sided pointwise bound `abs_psi_short_sub_le_at` controls `ψ(u+δu) − ψ(u) − δu` by a small
explicit term plus two near sums over the low zeros.  Squaring it and integrating against
`integral_norm_sq_zeroSum_le` gives the second moment of the multiplicative window increment on a
dyadic range, which is the input the block reduction of `ShortIntervalBlockReductionPsi` consumes.
-/

set_option autoImplicit false

namespace RHTower

open MeasureTheory intervalIntegral

noncomputable section

/-- The multiplicative increment of `ψ` written with the additive window. -/
theorem multIncr_psi_eq (δ x : ℝ) :
    multIncr Chebyshev.psi δ x = Chebyshev.psi (x + δ * x) - Chebyshev.psi x - δ * x := by
  unfold multIncr
  rw [show x * (1 + δ) = x + δ * x by ring]

/-- `(a + b + c)² ≤ 3(a² + b² + c²)`. -/
theorem sq_add_add_le_three (a b c : ℝ) : (a + b + c) ^ 2 ≤ 3 * (a ^ 2 + b ^ 2 + c ^ 2) := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (a - c)]

/-- The pointwise square bound from the two-sided estimate. -/
theorem sq_multIncr_psi_le {δ ε X x : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hX : 4 ≤ X)
    (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 2)
    (hbig : 16 * (64 + 1152 * xiSpectralThreeHalvesMass) ≤ ε ^ 2 * (δ * X) ^ 2)
    (hx : x ∈ Set.Icc X (2 * X)) :
    (multIncr Chebyshev.psi δ x) ^ 2
      ≤ 3 * ((3 * ε / 16 * (δ * x)) ^ 2 + ‖asymInnerSumAt δ ε X x‖ ^ 2
          + ‖asymOuterSumAt δ ε X x‖ ^ 2) := by
  have hpt := abs_psi_short_sub_le_at hε hε1 hX hδ0 hδ hbig hx
  rw [multIncr_psi_eq]
  have hx0 : 0 < x := by linarith [hx.1]
  have hA : (0 : ℝ) ≤ 3 * ε / 16 * (δ * x) := by positivity
  have hB : (0 : ℝ) ≤ ‖asymInnerSumAt δ ε X x‖ := norm_nonneg _
  have hC : (0 : ℝ) ≤ ‖asymOuterSumAt δ ε X x‖ := norm_nonneg _
  have hsq : (Chebyshev.psi (x + δ * x) - Chebyshev.psi x - δ * x) ^ 2
      ≤ (3 * ε / 16 * (δ * x) + ‖asymInnerSumAt δ ε X x‖ + ‖asymOuterSumAt δ ε X x‖) ^ 2 := by
    have habs := abs_le.mp hpt
    nlinarith [habs.1, habs.2, hA, hB, hC]
  exact hsq.trans (sq_add_add_le_three _ _ _)

/-- `∫_X^{2X} x² = 7X³/3`, in the form needed below. -/
theorem integral_sq_id (X : ℝ) :
    ∫ x in X..(2 * X), x ^ 2 = 7 * X ^ 3 / 3 := by
  rw [integral_pow]
  norm_num
  ring

/-- The dyadic-range second-moment bound of `integral_sq_multIncr_psi_le`, as a function of the
scale: the explicit term plus the two near-sum mean squares. -/
def multWindowMoment (δ ε X : ℝ) : ℝ :=
  3 * ((3 * ε / 16) ^ 2 * δ ^ 2 * (7 * X ^ 3 / 3)
    + (2 * X) ^ 3 * (4 * almostAllHarmonicWeight X *
        ∑ q ∈ almostAllLowZeros X,
          ‖multWindowCoeff δ (ε * δ / 16) (q.1 : ℂ)‖ ^ 2 * X ^ (2 * (q.1 : ℂ).re - 2))
    + (2 * X) ^ 3 * (4 * almostAllHarmonicWeight X *
        ∑ q ∈ almostAllLowZeros X,
          ‖multWindowCoeffOuter δ (ε * δ / 16) (q.1 : ℂ)‖ ^ 2
            * X ^ (2 * (q.1 : ℂ).re - 2)))

/-- **The second moment of the multiplicative window increment on a dyadic range.**  The explicit
term contributes `(3ε/16)² δ² · 7X³/3`, and each near sum contributes `(2X)³` times its mean-square
bound. -/
theorem integral_sq_multIncr_psi_le {δ ε X : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hX : 4 ≤ X)
    (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 2)
    (hbig : 16 * (64 + 1152 * xiSpectralThreeHalvesMass) ≤ ε ^ 2 * (δ * X) ^ 2) :
    ∫ x in X..(2 * X), (multIncr Chebyshev.psi δ x) ^ 2
      ≤ multWindowMoment δ ε X := by
  rw [multWindowMoment]
  have hX0 : (0 : ℝ) < X := by linarith
  have hX1 : (1 : ℝ) ≤ X := by linarith
  have hX2 : X ≤ 2 * X := by linarith
  have hW := sum_inv_lowZeros_le_harmonicWeight hX1
  -- the three pieces are interval integrable
  have hiA : IntervalIntegrable (fun x : ℝ => (3 * ε / 16 * (δ * x)) ^ 2) volume X (2 * X) :=
    (continuous_const.mul ((continuous_const.mul continuous_id))).pow 2 |>.intervalIntegrable _ _
  have hcontD := continuousOn_zeroSum hX0 (almostAllLowZeros X)
    (fun q => multWindowCoeff δ (ε * δ / 16) (q.1 : ℂ))
  have hcontE := continuousOn_zeroSum hX0 (almostAllLowZeros X)
    (fun q => multWindowCoeffOuter δ (ε * δ / 16) (q.1 : ℂ))
  have hiB : IntervalIntegrable (fun x : ℝ => ‖asymInnerSumAt δ ε X x‖ ^ 2) volume X (2 * X) := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hX2]
    exact (hcontD.norm.pow 2).integrableOn_Icc
  have hiC : IntervalIntegrable (fun x : ℝ => ‖asymOuterSumAt δ ε X x‖ ^ 2) volume X (2 * X) := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hX2]
    exact (hcontE.norm.pow 2).integrableOn_Icc
  have hiG : IntervalIntegrable (fun x : ℝ => (multIncr Chebyshev.psi δ x) ^ 2) volume X (2 * X) :=
    intervalIntegrable_sq_multIncr_psi hδ0.le hX0.le hX2
  have hiRHS : IntervalIntegrable
      (fun x : ℝ => 3 * ((3 * ε / 16 * (δ * x)) ^ 2 + ‖asymInnerSumAt δ ε X x‖ ^ 2
        + ‖asymOuterSumAt δ ε X x‖ ^ 2)) volume X (2 * X) :=
    ((hiA.add hiB).add hiC).const_mul _
  -- integrate the pointwise bound
  have hstep : ∫ x in X..(2 * X), (multIncr Chebyshev.psi δ x) ^ 2
      ≤ ∫ x in X..(2 * X), 3 * ((3 * ε / 16 * (δ * x)) ^ 2 + ‖asymInnerSumAt δ ε X x‖ ^ 2
          + ‖asymOuterSumAt δ ε X x‖ ^ 2) :=
    integral_mono_on hX2 hiG hiRHS fun x hx => sq_multIncr_psi_le hε hε1 hX hδ0 hδ hbig hx
  rw [intervalIntegral.integral_const_mul, integral_add (hiA.add hiB) hiC,
    integral_add hiA hiB] at hstep
  -- the explicit term
  have hAval : ∫ x in X..(2 * X), (3 * ε / 16 * (δ * x)) ^ 2
      = (3 * ε / 16) ^ 2 * δ ^ 2 * (7 * X ^ 3 / 3) := by
    have e : ∀ x : ℝ, (3 * ε / 16 * (δ * x)) ^ 2 = ((3 * ε / 16) ^ 2 * δ ^ 2) * x ^ 2 := by
      intro x; ring
    simp_rw [e]
    rw [intervalIntegral.integral_const_mul, integral_sq_id X]
  -- the two near sums
  have hBval := integral_norm_sq_zeroSum_le hX0 (almostAllLowZeros X)
    (fun q => multWindowCoeff δ (ε * δ / 16) (q.1 : ℂ)) hW
  have hCval := integral_norm_sq_zeroSum_le hX0 (almostAllLowZeros X)
    (fun q => multWindowCoeffOuter δ (ε * δ / 16) (q.1 : ℂ)) hW
  rw [hAval] at hstep
  have hBeq : (fun x : ℝ => ‖asymInnerSumAt δ ε X x‖ ^ 2)
      = fun x : ℝ => ‖∑ q ∈ almostAllLowZeros X,
          multWindowCoeff δ (ε * δ / 16) (q.1 : ℂ) * (x : ℂ) ^ (q.1 : ℂ)‖ ^ 2 := rfl
  have hCeq : (fun x : ℝ => ‖asymOuterSumAt δ ε X x‖ ^ 2)
      = fun x : ℝ => ‖∑ q ∈ almostAllLowZeros X,
          multWindowCoeffOuter δ (ε * δ / 16) (q.1 : ℂ) * (x : ℂ) ^ (q.1 : ℂ)‖ ^ 2 := rfl
  rw [hBeq, hCeq] at hstep
  linarith [hstep, hBval, hCval]


/-- **The second moment on the tripled range.**  `[X, 3X] ⊆ [X, 2X] ∪ [2X, 4X]`, and the integrand is
nonnegative, so the dyadic bound at the scales `X` and `2X` suffices. -/
theorem integral_sq_multIncr_psi_tripled_le {δ ε X : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hX : 4 ≤ X)
    (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 2)
    (hbig : 16 * (64 + 1152 * xiSpectralThreeHalvesMass) ≤ ε ^ 2 * (δ * X) ^ 2) :
    ∫ u in X..(3 * X), (multIncr Chebyshev.psi δ u) ^ 2
      ≤ multWindowMoment δ ε X + multWindowMoment δ ε (2 * X) := by
  have hX0 : (0 : ℝ) < X := by linarith
  have hX4 : (4 : ℝ) ≤ 2 * X := by linarith
  have hbig2 : 16 * (64 + 1152 * xiSpectralThreeHalvesMass) ≤ ε ^ 2 * (δ * (2 * X)) ^ 2 := by
    have h1 : (δ * X) ^ 2 ≤ (δ * (2 * X)) ^ 2 := by nlinarith [mul_pos hδ0 hX0]
    nlinarith [sq_nonneg ε]
  have h1 := integral_sq_multIncr_psi_le hε hε1 hX hδ0 hδ hbig
  have h2 := integral_sq_multIncr_psi_le hε hε1 hX4 hδ0 hδ hbig2
  -- the middle piece, extended to the second dyadic range
  have hi2 : IntervalIntegrable (fun u => (multIncr Chebyshev.psi δ u) ^ 2) volume (2 * X)
      (2 * (2 * X)) := intervalIntegrable_sq_multIncr_psi hδ0.le (by linarith) (by linarith)
  have hmid : ∫ u in (2 * X)..(3 * X), (multIncr Chebyshev.psi δ u) ^ 2
      ≤ ∫ u in (2 * X)..(2 * (2 * X)), (multIncr Chebyshev.psi δ u) ^ 2 := by
    refine integral_mono_interval (le_refl _) (by linarith) (by linarith) ?_ hi2
    exact Filter.Eventually.of_forall fun u => sq_nonneg _
  have hsplit : (∫ u in X..(2 * X), (multIncr Chebyshev.psi δ u) ^ 2)
      + ∫ u in (2 * X)..(3 * X), (multIncr Chebyshev.psi δ u) ^ 2
      = ∫ u in X..(3 * X), (multIncr Chebyshev.psi δ u) ^ 2 := by
    refine intervalIntegral.integral_add_adjacent_intervals ?_ ?_
    · exact intervalIntegrable_sq_multIncr_psi hδ0.le hX0.le (by linarith)
    · exact intervalIntegrable_sq_multIncr_psi hδ0.le (by linarith) (by linarith)
  linarith [h1, h2, hmid, hsplit]

/-- **The second moment of the fixed-length window increment.**  Guth–Maynard's block reduction with
the multiplicative second moment supplied: for `2(1+δ)^J ≤ 3`,
`∫_X^{2X} (ψ(x+y) − ψ(x) − y)² ≤ 2J²(M(X) + M(2X)) + 2∫_X^{2X} (boundary)²`. -/
theorem integral_sq_fixedIncr_psi_bound {δ ε X y : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hX : 4 ≤ X)
    (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 2) (hy : 0 ≤ y) (J : ℕ) (hJ : 2 * (1 + δ) ^ J ≤ 3)
    (hbig : 16 * (64 + 1152 * xiSpectralThreeHalvesMass) ≤ ε ^ 2 * (δ * X) ^ 2) :
    ∫ x in X..(2 * X), (fixedIncr Chebyshev.psi y x) ^ 2
      ≤ 2 * (J : ℝ) ^ 2 * (multWindowMoment δ ε X + multWindowMoment δ ε (2 * X))
        + 2 * ∫ x in X..(2 * X), (bdryIncr Chebyshev.psi y x δ J) ^ 2 := by
  have hX0 : (0 : ℝ) < X := by linarith
  have h := integral_sq_fixedIncr_psi_le hδ0 hX0 hy J hJ
  have htr := integral_sq_multIncr_psi_tripled_le hε hε1 hX hδ0 hδ hbig
  have hJ0 : (0 : ℝ) ≤ 2 * (J : ℝ) ^ 2 := by positivity
  nlinarith [h, htr, hJ0]


/-- **The multiplicative second moment over any subrange of `[X, 8X]`.**  Splitting into the three
dyadic ranges `[X,2X]`, `[2X,4X]`, `[4X,8X]` and using nonnegativity of the integrand. -/
theorem integral_sq_multIncr_psi_sub_le {δ ε X a b : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hX : 4 ≤ X)
    (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 2)
    (hbig : 16 * (64 + 1152 * xiSpectralThreeHalvesMass) ≤ ε ^ 2 * (δ * X) ^ 2)
    (ha : X ≤ a) (hab : a ≤ b) (hb : b ≤ 8 * X) :
    ∫ u in a..b, (multIncr Chebyshev.psi δ u) ^ 2
      ≤ multWindowMoment δ ε X + multWindowMoment δ ε (2 * X) + multWindowMoment δ ε (4 * X) := by
  have hX0 : (0 : ℝ) < X := by linarith
  have hmono : ∀ {c d : ℝ}, (0 : ℝ) < c → c ≤ d →
      16 * (64 + 1152 * xiSpectralThreeHalvesMass) ≤ ε ^ 2 * (δ * c) ^ 2 →
      16 * (64 + 1152 * xiSpectralThreeHalvesMass) ≤ ε ^ 2 * (δ * d) ^ 2 := by
    intro c d hc hcd h
    have h1 : (δ * c) ^ 2 ≤ (δ * d) ^ 2 :=
      pow_le_pow_left₀ (mul_nonneg hδ0.le hc.le) (mul_le_mul_of_nonneg_left hcd hδ0.le) 2
    have h2 : ε ^ 2 * (δ * c) ^ 2 ≤ ε ^ 2 * (δ * d) ^ 2 :=
      mul_le_mul_of_nonneg_left h1 (sq_nonneg ε)
    linarith
  have hb2 := hmono hX0 (by linarith : X ≤ 2 * X) hbig
  have hb4 := hmono hX0 (by linarith : X ≤ 4 * X) hbig
  have h1 := integral_sq_multIncr_psi_le hε hε1 hX hδ0 hδ hbig
  have h2 := integral_sq_multIncr_psi_le hε hε1 (by linarith : (4 : ℝ) ≤ 2 * X) hδ0 hδ hb2
  have h4 := integral_sq_multIncr_psi_le hε hε1 (by linarith : (4 : ℝ) ≤ 4 * X) hδ0 hδ hb4
  -- integrability on each dyadic piece and on the whole of `[X, 8X]`
  have hiall : IntervalIntegrable (fun u => (multIncr Chebyshev.psi δ u) ^ 2) volume X (8 * X) :=
    intervalIntegrable_sq_multIncr_psi hδ0.le hX0.le (by linarith)
  have hwhole : ∫ u in a..b, (multIncr Chebyshev.psi δ u) ^ 2
      ≤ ∫ u in X..(8 * X), (multIncr Chebyshev.psi δ u) ^ 2 := by
    refine integral_mono_interval ha hab hb ?_ hiall
    exact Filter.Eventually.of_forall fun u => sq_nonneg _
  have hs1 : (∫ u in X..(2 * X), (multIncr Chebyshev.psi δ u) ^ 2)
      + ∫ u in (2 * X)..(4 * X), (multIncr Chebyshev.psi δ u) ^ 2
      = ∫ u in X..(4 * X), (multIncr Chebyshev.psi δ u) ^ 2 :=
    intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_sq_multIncr_psi hδ0.le hX0.le (by linarith))
      (intervalIntegrable_sq_multIncr_psi hδ0.le (by linarith) (by linarith))
  have hs2 : (∫ u in X..(4 * X), (multIncr Chebyshev.psi δ u) ^ 2)
      + ∫ u in (4 * X)..(8 * X), (multIncr Chebyshev.psi δ u) ^ 2
      = ∫ u in X..(8 * X), (multIncr Chebyshev.psi δ u) ^ 2 :=
    intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_sq_multIncr_psi hδ0.le hX0.le (by linarith))
      (intervalIntegrable_sq_multIncr_psi hδ0.le (by linarith) (by linarith))
  have e2 : (2 : ℝ) * (2 * X) = 4 * X := by ring
  have e4 : (2 : ℝ) * (4 * X) = 8 * X := by ring
  rw [e2] at h2
  rw [e4] at h4
  linarith [hwhole, hs1, hs2, h1, h2, h4]

end

end RHTower
