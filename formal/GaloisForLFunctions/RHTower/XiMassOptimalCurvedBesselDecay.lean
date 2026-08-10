import GaloisForLFunctions.RHTower.XiMassHyperbolicCurvedContourDecay

/-!
# Optimal curved-contour Bessel decay for the Xi mass transform

The variational optimizer from `XiMassSpacelikeContourOptimality` is converted into an actual
interior first-quadrant angle.  Combining that angle with the entire hyperbolic contour theorem
identifies the Bessel argument exactly with

`a * Re sqrt ((sigma+i*u)^2+h^2)`.

Consequently the mass Fourier transform has both an exact optimal `K₁` bound and a fixed-base
bound retaining the full exponential coefficient `1`.  This closes the analytic C41-S lift; the
remaining Route T obstruction is arithmetic cancellation in the timelike-plus-glancing layer.
-/

open Complex Real MeasureTheory Set Filter Topology

namespace RHTower

noncomputable section

theorem xiMassSpacelikePropagationRateSq_gt_gap
    {sigma u h : ℝ} (hsigma : 0 < sigma) (hu : 0 ≤ u) (huh : u < h) :
    h ^ 2 - u ^ 2 < xiMassSpacelikePropagationRateSq sigma u h := by
  have hgap : 0 < h ^ 2 - u ^ 2 := by nlinarith
  have hsqrt := sqrt_spacelikeGap_lt_csqrtRe_propagationArgument hsigma hu huh
  have hsqrt0 : 0 ≤ Real.sqrt (h ^ 2 - u ^ 2) := Real.sqrt_nonneg _
  have hkappa0 : 0 ≤ HTGeometry.csqrtRe
      (xiMassSpacelikePropagationArgument sigma u h) := HTGeometry.csqrtRe_nonneg _
  have hgapSq : Real.sqrt (h ^ 2 - u ^ 2) ^ 2 = h ^ 2 - u ^ 2 :=
    Real.sq_sqrt hgap.le
  have htrace : 0 < xiMassSpacelikeTrace sigma u h := by
    rw [xiMassSpacelikeTrace]
    nlinarith [sq_pos_of_pos hsigma]
  have hkappaSq := sq_csqrtRe_xiMassSpacelikePropagationArgument htrace
  nlinarith

theorem exists_xiMassSpacelikeOptimalContourAngle
    {sigma u h : ℝ} (hsigma : 0 < sigma) (hu : 0 ≤ u) (huh : u < h) :
    ∃ theta : ℝ, 0 ≤ theta ∧ theta < Real.pi / 2 ∧
      xiMassSpacelikeContourRateSq sigma u h
          (Real.cos theta) (Real.sin theta) =
        xiMassSpacelikePropagationRateSq sigma u h := by
  have hh : 0 < h := lt_of_le_of_lt hu huh
  rcases exists_xiMassSpacelikeOptimalContour (u := u) hsigma hh with
    ⟨c, s, hc, hs, hunit, hopt⟩
  have hcpos : 0 < c := by
    by_contra hnc
    have hc0 : c = 0 := le_antisymm (le_of_not_gt hnc) hc
    have hsSq : s ^ 2 = 1 := by nlinarith
    have hrate : xiMassSpacelikeContourRateSq sigma u h c s = h ^ 2 - u ^ 2 := by
      rw [xiMassSpacelikeContourRateSq, hc0]
      nlinarith
    have hstrict := xiMassSpacelikePropagationRateSq_gt_gap hsigma hu huh
    rw [← hopt, hrate] at hstrict
    exact (lt_irrefl _ hstrict)
  let z : ℂ := (c : ℂ) + (s : ℂ) * I
  have hzNorm : ‖z‖ = 1 := by
    have hzSq : ‖z‖ ^ 2 = 1 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp only [z, Complex.add_re, Complex.add_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re,
        Complex.I_im, mul_zero, sub_zero, add_zero, mul_one, zero_add]
      nlinarith
    nlinarith [norm_nonneg z]
  have hz0 : z ≠ 0 := by
    intro hz
    rw [hz, norm_zero] at hzNorm
    norm_num at hzNorm
  let theta : ℝ := z.arg
  have hcos : Real.cos theta = c := by
    dsimp only [theta]
    rw [Complex.cos_arg hz0, hzNorm, div_one]
    simp only [z, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      Complex.ofReal_im, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
  have hsin : Real.sin theta = s := by
    dsimp only [theta]
    rw [Complex.sin_arg, hzNorm, div_one]
    simp only [z, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_im,
      Complex.ofReal_re, Complex.I_re, mul_one, zero_mul, add_zero, zero_add]
  have htheta0 : 0 ≤ theta := by
    dsimp only [theta]
    rw [Complex.arg_nonneg_iff]
    simpa only [z, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_im,
      Complex.ofReal_re, Complex.I_re, mul_one, zero_mul, add_zero, zero_add] using hs
  have hthetaPi : theta < Real.pi / 2 := by
    by_contra hnot
    have hlower : Real.pi / 2 ≤ theta := le_of_not_gt hnot
    have hupper : theta ≤ Real.pi + Real.pi / 2 := by
      have harg := Complex.arg_le_pi z
      dsimp only [theta]
      nlinarith [Real.pi_pos]
    have hnonpos := Real.cos_nonpos_of_pi_div_two_le_of_le hlower hupper
    rw [hcos] at hnonpos
    linarith
  refine ⟨theta, htheta0, hthetaPi, ?_⟩
  rw [hcos, hsin]
  exact hopt

theorem sq_csqrtRe_eq_optimalContourRateSq
    {sigma u h theta : ℝ}
    (hsigma : 0 < sigma) (hu : 0 ≤ u) (huh : u < h)
    (hopt : xiMassSpacelikeContourRateSq sigma u h
      (Real.cos theta) (Real.sin theta) =
        xiMassSpacelikePropagationRateSq sigma u h) :
    xiMassSpacelikeContourRateSq sigma u h
        (Real.cos theta) (Real.sin theta) =
      HTGeometry.csqrtRe
        (xiMassSpacelikePropagationArgument sigma u h) ^ 2 := by
  have htrace : 0 < xiMassSpacelikeTrace sigma u h := by
    rw [xiMassSpacelikeTrace]
    nlinarith [sq_pos_of_pos hsigma]
  rw [hopt, sq_csqrtRe_xiMassSpacelikePropagationArgument htrace]

theorem sqrt_optimalContourRateSq_eq_csqrtRe
    {sigma u h theta : ℝ}
    (hsigma : 0 < sigma) (hu : 0 ≤ u) (huh : u < h)
    (hopt : xiMassSpacelikeContourRateSq sigma u h
      (Real.cos theta) (Real.sin theta) =
        xiMassSpacelikePropagationRateSq sigma u h) :
    Real.sqrt (xiMassSpacelikeContourRateSq sigma u h
      (Real.cos theta) (Real.sin theta)) =
        HTGeometry.csqrtRe
          (xiMassSpacelikePropagationArgument sigma u h) := by
  rw [sq_csqrtRe_eq_optimalContourRateSq hsigma hu huh hopt]
  exact Real.sqrt_sq (HTGeometry.csqrtRe_nonneg _)

theorem exists_norm_stripFourier_xiMass_le_optimalCurvedBessel
    {a sigma u h : ℝ}
    (ha : 0 < a) (hsigma : 0 < sigma) (hu : 0 ≤ u) (huh : u < h) :
    let kappa := HTGeometry.csqrtRe
      (xiMassSpacelikePropagationArgument sigma u h)
    ∃ theta : ℝ, 0 ≤ theta ∧ theta < Real.pi / 2 ∧
      xiMassSpacelikeContourRateSq sigma u h
          (Real.cos theta) (Real.sin theta) = kappa ^ 2 ∧
      ‖stripFourier
        (xiMassAnalyticTest a ((sigma : ℂ) + (u : ℂ) * I)) (h : ℂ)‖ ≤
          2 * a * Real.exp
            (Real.arsinh (u * Real.sin theta / kappa)) *
            GaloisForLFunctions.HTGeometry.realModifiedBesselKOrder (a * kappa) 1 := by
  dsimp only
  let kappa := HTGeometry.csqrtRe
    (xiMassSpacelikePropagationArgument sigma u h)
  rcases exists_xiMassSpacelikeOptimalContourAngle hsigma hu huh with
    ⟨theta, htheta0, hthetaPi, hopt⟩
  have hrate := sq_csqrtRe_eq_optimalContourRateSq hsigma hu huh hopt
  have hq := sqrt_optimalContourRateSq_eq_csqrtRe hsigma hu huh hopt
  have hq' : Real.sqrt
      ((sigma * Real.cos theta + h * Real.sin theta) ^ 2 -
        (u * Real.sin theta) ^ 2) = kappa := by
    simpa only [xiMassSpacelikeContourRateSq, kappa] using hq
  have hb := norm_stripFourier_xiMass_le_curvedBessel
    ha hsigma hu huh.le htheta0 hthetaPi
  dsimp only at hb
  rw [hq'] at hb
  refine ⟨theta, htheta0, hthetaPi, ?_, ?_⟩
  · simpa only [kappa] using hrate
  · exact hb

theorem exists_norm_stripFourier_xiMass_le_optimal_full_exponent
    {a sigma u h q₀ : ℝ}
    (ha : 0 < a) (hsigma : 0 < sigma) (hu : 0 ≤ u) (huh : u < h)
    (hq₀ : 0 < q₀)
    (hq₀kappa : q₀ ≤ HTGeometry.csqrtRe
      (xiMassSpacelikePropagationArgument sigma u h)) :
    let kappa := HTGeometry.csqrtRe
      (xiMassSpacelikePropagationArgument sigma u h)
    ∃ theta : ℝ, 0 ≤ theta ∧ theta < Real.pi / 2 ∧
      xiMassSpacelikeContourRateSq sigma u h
          (Real.cos theta) (Real.sin theta) = kappa ^ 2 ∧
      ‖stripFourier
        (xiMassAnalyticTest a ((sigma : ℂ) + (u : ℂ) * I)) (h : ℂ)‖ ≤
          2 * a * Real.exp
            (Real.arsinh (u * Real.sin theta / kappa)) *
          Real.exp (-(a * (kappa - q₀))) *
            GaloisForLFunctions.HTGeometry.realModifiedBesselKOrder (a * q₀) 1 := by
  dsimp only
  let kappa := HTGeometry.csqrtRe
    (xiMassSpacelikePropagationArgument sigma u h)
  rcases exists_xiMassSpacelikeOptimalContourAngle hsigma hu huh with
    ⟨theta, htheta0, hthetaPi, hopt⟩
  have hrate := sq_csqrtRe_eq_optimalContourRateSq hsigma hu huh hopt
  have hq := sqrt_optimalContourRateSq_eq_csqrtRe hsigma hu huh hopt
  have hq' : Real.sqrt
      ((sigma * Real.cos theta + h * Real.sin theta) ^ 2 -
        (u * Real.sin theta) ^ 2) = kappa := by
    simpa only [xiMassSpacelikeContourRateSq, kappa] using hq
  have hq₀angle : q₀ ≤ Real.sqrt
      ((sigma * Real.cos theta + h * Real.sin theta) ^ 2 -
        (u * Real.sin theta) ^ 2) := by
    rw [hq']
    exact hq₀kappa
  have hb := norm_stripFourier_xiMass_le_curvedBessel_full_exponent
    ha hsigma hu huh.le htheta0 hthetaPi hq₀ hq₀angle
  dsimp only at hb
  rw [hq'] at hb
  refine ⟨theta, htheta0, hthetaPi, ?_, ?_⟩
  · simpa only [kappa] using hrate
  · exact hb

end

end RHTower
