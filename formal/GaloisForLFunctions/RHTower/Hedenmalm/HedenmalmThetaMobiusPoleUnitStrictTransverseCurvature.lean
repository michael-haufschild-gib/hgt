import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaMobiusPoleUnitTransverseCurvature
import GaloisForLFunctions.RHTower.XiEndpointReciprocalTraceReflection
import GaloisForLFunctions.RHTower.XiThermalSourceRelativeGapBound
import GaloisForLFunctions.RHTower.XiCollapseDirichletLeg
import GaloisForLFunctions.RHTower.XiExplicitFormulaLogDeriv
import GaloisForLFunctions.RHTower.XiRealAxisGrowth
import GaloisForLFunctions.HTGeometry.PolygammaReflection
import GaloisForLFunctions.HTGeometry.RealDirichletSeries
import Mathlib.Analysis.Calculus.SmoothSeries

/-!
# Strict pole-unit transverse curvature of the normalized Möbius source

P-G41 reduces the first non-universal source jet to the derivative at the Euler pole of the
regular squarefree current.  This module proves its strict sign without numerical zero data.

The new bridge is an endpoint spectral budget.  The second logarithmic derivative of `xi` at
`s = 1` is the negative raw reciprocal-square divisor trace.  Its norm is bounded by the raw
Hermitian endpoint mass, already strictly below `3/43`.  The completed factorization then leaves
the archimedean reserve `pi^(2 : ℕ)/8 - 1`, which is larger than `1/8`.  The Euler squarefree correction
has the same favorable sign.  Hence the pole unit is strictly log-concave at `1`, and the literal
finite source Gram has strictly positive arithmetic transverse curvature.

This is an unconditional local discriminator, not an RH proof: it orients the first arithmetic
departure from the universal boost orbit but does not force that departure to vanish.
-/

open Complex Filter Metric Set ArithmeticFunction LSeries
open scoped BigOperators

namespace RHTower

noncomputable section

private def xiEndpointPartialFractionTerm (s : ℂ) (q : XiZeroCopy) : ℂ :=
  (((q.1 : ℂ) - 1 / 2)⁻¹ + (s - (q.1 : ℂ))⁻¹)

private theorem xiEndpointPartialFractionTerm_hasDerivAt
    (q : XiZeroCopy) {s : ℂ} (hs : s ≠ (q.1 : ℂ)) :
    HasDerivAt (fun u => xiEndpointPartialFractionTerm u q)
      (-((s - (q.1 : ℂ))⁻¹ ^ 2)) s := by
  unfold xiEndpointPartialFractionTerm
  have hsub : s - (q.1 : ℂ) ≠ 0 := sub_ne_zero.mpr hs
  convert! (hasDerivAt_const (x := s)
      (c := (((q.1 : ℂ) - 1 / 2)⁻¹))).add
    (((hasDerivAt_id (𝕜 := ℂ) (x := s)).sub_const (q.1 : ℂ)).inv hsub) using 1
  all_goals field_simp [hsub]
  all_goals simp only [id_eq]
  all_goals ring

private theorem xiEndpointPartialFractionTerm_deriv_norm_le
    (q : XiZeroCopy) {s : ℂ} (hs : s ∈ ball (1 : ℂ) (1 / 20 : ℝ)) :
    ‖-((s - (q.1 : ℂ))⁻¹ ^ 2)‖ ≤
      400 * ‖xiRawReciprocalCoordinate q‖ ^ 2 := by
  have hq0 : (q.1 : ℂ) ≠ 0 := by
    intro hzero
    have him := congrArg Complex.im hzero
    simp only [Complex.zero_im] at him
    exact xi_divisor_support_im_ne_zero q.1 him
  have hqnorm : 10 / 9 < ‖(q.1 : ℂ)‖ := by
    have hraw := xiRawReciprocalCoordinate_norm_lt_nine_tenths q
    rw [xiRawReciprocalCoordinate, norm_inv] at hraw
    have hpos : 0 < ‖(q.1 : ℂ)‖ := norm_pos_iff.mpr hq0
    have hmul := mul_lt_mul_of_pos_right hraw hpos
    rw [inv_mul_cancel₀ hpos.ne'] at hmul
    nlinarith
  have hsnear : ‖s - 1‖ < 1 / 20 := by
    simpa only [mem_ball, dist_eq_norm] using hs
  have hsnorm : ‖s‖ < 21 / 20 := by
    have htri : ‖s‖ ≤ ‖s - 1‖ + ‖(1 : ℂ)‖ := by
      calc
        ‖s‖ = ‖(s - 1) + 1‖ := by ring_nf
        _ ≤ ‖s - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
    norm_num at htri
    linarith
  have hratio : ‖s‖ ≤ (19 / 20 : ℝ) * ‖(q.1 : ℂ)‖ := by
    nlinarith
  have hrev : ‖(q.1 : ℂ)‖ - ‖s‖ ≤ ‖(q.1 : ℂ) - s‖ :=
    norm_sub_norm_le (q.1 : ℂ) s
  have hsep : ‖(q.1 : ℂ)‖ / 20 ≤ ‖(q.1 : ℂ) - s‖ := by
    nlinarith
  have hqpos : 0 < ‖(q.1 : ℂ)‖ := norm_pos_iff.mpr hq0
  have hseppos : 0 < ‖(q.1 : ℂ) - s‖ :=
    lt_of_lt_of_le (div_pos hqpos (by norm_num)) hsep
  have hinv : ‖(q.1 : ℂ) - s‖⁻¹ ≤ 20 * ‖(q.1 : ℂ)‖⁻¹ := by
    have h := one_div_le_one_div_of_le (div_pos hqpos (by norm_num)) hsep
    rw [one_div, one_div, inv_div] at h
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm] using h
  rw [norm_neg, norm_pow, norm_inv, norm_sub_rev,
    xiRawReciprocalCoordinate, norm_inv]
  calc
    ‖(q.1 : ℂ) - s‖⁻¹ ^ 2 ≤
        (20 * ‖(q.1 : ℂ)‖⁻¹) ^ 2 := by gcongr
    _ = 400 * ‖(q.1 : ℂ)‖⁻¹ ^ 2 := by ring

private theorem summable_xiEndpointPartialFractionTerm_one :
    Summable (xiEndpointPartialFractionTerm 1) := by
  let h : ℂ → ℂ := fun w => (w - 1 / 2) * -I
  have hXi : XiC (h 1) ≠ 0 := by
    rw [← xi_eq_XiC_comp]
    rw [xi_one]
    norm_num
  have hsum := (summable_xiRelativeResolventTerm hXi).mul_right (-I)
  apply hsum.congr
  intro q
  unfold xiEndpointPartialFractionTerm
  rw [xiRelativeResolventTerm]
  have hspec : xiSpectralPoint q = (((q.1 : ℂ)) - 1 / 2) * -I := by
    rw [xiSpectralPoint_eq_support, xiSpectralPointSupport]
  rw [hspec]
  have hth := resolvent_coordinate_transport
    (((q.1 : ℂ)) - 1 / 2) (1 - 1 / 2)
  calc
    ((((q.1 : ℂ) - 1 / 2) * -I)⁻¹ -
        (((q.1 : ℂ) - 1 / 2) * -I - h 1)⁻¹) * -I =
        ((((q.1 : ℂ) - 1 / 2) * -I)⁻¹ -
          (((q.1 : ℂ) - 1 / 2) * -I - (1 - 1 / 2) * -I)⁻¹) * -I := by
      simp [h]
    _ = ((q.1 : ℂ) - 1 / 2)⁻¹ -
        ((q.1 : ℂ) - 1 / 2 - (1 - 1 / 2))⁻¹ := hth
    _ = ((q.1 : ℂ) - 1 / 2)⁻¹ + (1 - (q.1 : ℂ))⁻¹ := by
      rw [show (q.1 : ℂ) - 1 / 2 - (1 - 1 / 2) =
          -(1 - (q.1 : ℂ)) by ring, inv_neg]
      ring

private theorem hasDerivAt_tsum_xiEndpointPartialFractionTerm_one :
    HasDerivAt (fun s : ℂ => ∑' q : XiZeroCopy,
      xiEndpointPartialFractionTerm s q)
      (∑' q : XiZeroCopy, -(((1 : ℂ) - (q.1 : ℂ))⁻¹ ^ 2)) 1 := by
  let majorant : XiZeroCopy → ℝ := fun q =>
    400 * ‖xiRawReciprocalCoordinate q‖ ^ 2
  have hmajorant : Summable majorant :=
    summable_norm_xiRawReciprocalCoordinate_sq.mul_left 400
  have hderiv : ∀ q : XiZeroCopy, ∀ s ∈ ball (1 : ℂ) (1 / 20 : ℝ),
      HasDerivAt (fun u => xiEndpointPartialFractionTerm u q)
        (-((s - (q.1 : ℂ))⁻¹ ^ 2)) s := by
    intro q s hs
    apply xiEndpointPartialFractionTerm_hasDerivAt
    intro heq
    have hzero : xi (q.1 : ℂ) = 0 := xi_eq_zero_of_mem_divisor_support q.1
    have hqnorm : 10 / 9 < ‖(q.1 : ℂ)‖ := by
      have hraw := xiRawReciprocalCoordinate_norm_lt_nine_tenths q
      have hq0 : (q.1 : ℂ) ≠ 0 := by
        intro hq
        have him := congrArg Complex.im hq
        simp only [Complex.zero_im] at him
        exact xi_divisor_support_im_ne_zero q.1 him
      rw [xiRawReciprocalCoordinate, norm_inv] at hraw
      have hpos : 0 < ‖(q.1 : ℂ)‖ := norm_pos_iff.mpr hq0
      have hmul := mul_lt_mul_of_pos_right hraw hpos
      rw [inv_mul_cancel₀ hpos.ne'] at hmul
      nlinarith
    have hsnear : ‖s - 1‖ < 1 / 20 := by
      simpa only [mem_ball, dist_eq_norm] using hs
    have hsnorm : ‖s‖ < 21 / 20 := by
      have htri : ‖s‖ ≤ ‖s - 1‖ + ‖(1 : ℂ)‖ := by
        calc
          ‖s‖ = ‖(s - 1) + 1‖ := by ring_nf
          _ ≤ ‖s - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
      norm_num at htri
      linarith
    rw [heq] at hsnorm
    linarith
  have hbound : ∀ q : XiZeroCopy, ∀ s ∈ ball (1 : ℂ) (1 / 20 : ℝ),
      ‖-((s - (q.1 : ℂ))⁻¹ ^ 2)‖ ≤ majorant q := by
    intro q s hs
    exact xiEndpointPartialFractionTerm_deriv_norm_le q hs
  exact hasDerivAt_tsum_of_isPreconnected hmajorant Metric.isOpen_ball
    (convex_ball (1 : ℂ) (1 / 20 : ℝ)).isPreconnected hderiv hbound
    (Metric.mem_ball_self (by norm_num)) summable_xiEndpointPartialFractionTerm_one
    (Metric.mem_ball_self (by norm_num))

/-- **Endpoint Hadamard jet bridge.**  The physical endpoint second logarithmic derivative is the
negative multiplicity-exact raw reciprocal-square trace. -/
theorem deriv_logDeriv_xi_one_eq_neg_rawReciprocalPowerTrace_two :
    deriv (logDeriv xi) 1 = -xiRawReciprocalPowerTrace 2 := by
  let S : ℂ → ℂ := fun s => ∑' q : XiZeroCopy,
    xiEndpointPartialFractionTerm s q
  have hxi : ∀ᶠ s in nhds (1 : ℂ), xi s ≠ 0 :=
    (xi_differentiable 1).continuousAt.eventually_ne (by rw [xi_one]; norm_num)
  have heq : logDeriv xi =ᶠ[nhds (1 : ℂ)] S := by
    filter_upwards [hxi] with s hs
    exact logDeriv_xi_eq_partialFraction hs
  rw [heq.deriv_eq]
  have hderiv := hasDerivAt_tsum_xiEndpointPartialFractionTerm_one.deriv
  rw [hderiv]
  have hreindex :
      (∑' q : XiZeroCopy, ((1 : ℂ) - (q.1 : ℂ))⁻¹ ^ 2) =
        xiRawReciprocalPowerTrace 2 := by
    rw [xiRawReciprocalPowerTrace]
    change (∑' q : XiZeroCopy,
      xiRawReciprocalCoordinate (xiZeroCopyReflectEquiv q) ^ 2) = _
    exact xiZeroCopyReflectEquiv.tsum_eq
      (fun q : XiZeroCopy => xiRawReciprocalCoordinate q ^ 2)
  rw [tsum_neg, hreindex]

/-- Raw reciprocal-square trace norm is controlled by the endpoint Hermitian mass. -/
theorem norm_xiRawReciprocalPowerTrace_two_le_mass :
    ‖xiRawReciprocalPowerTrace 2‖ ≤ xiRawReciprocalHermitianMass := by
  rw [xiRawReciprocalPowerTrace, xiRawReciprocalHermitianMass]
  calc
    ‖∑' q : XiZeroCopy, xiRawReciprocalCoordinate q ^ 2‖ ≤
        ∑' q : XiZeroCopy, ‖xiRawReciprocalCoordinate q ^ 2‖ :=
      norm_tsum_le_tsum_norm (by
        simpa only [norm_pow] using summable_norm_xiRawReciprocalCoordinate_sq)
    _ = ∑' q : XiZeroCopy, ‖xiRawReciprocalCoordinate q‖ ^ 2 := by
      apply tsum_congr
      intro q
      rw [norm_pow]

/-- The raw reciprocal-square trace is strictly smaller than the rational endpoint reserve. -/
theorem norm_xiRawReciprocalPowerTrace_two_lt_three_over_fortyThree :
    ‖xiRawReciprocalPowerTrace 2‖ < 3 / 43 := by
  have hnorm := norm_xiRawReciprocalPowerTrace_two_le_mass
  have hmass := xiRawReciprocalHermitianMass_lt_three_halves_mul_endpointCurvature
  have hcurv := xiEndpointCompletedCurvature_lt_two_over_fortyThree
  nlinarith

/-- The entire completed function factors through the analytic pole unit on the whole right
half-plane, including the removable point `s = 1`. -/
theorem xi_eq_half_mul_Gammaℝ_mul_zetaResidueUnit {s : ℂ} (hs : 0 < s.re) :
    xi s = (s / 2 * Complex.Gammaℝ s) * zetaResidueUnit s := by
  by_cases hs1 : s = 1
  · subst s
    rw [xi_one, Complex.Gammaℝ_one, zetaResidueUnit_one]
    norm_num
  · have hs0 : s ≠ 0 := by
      intro hs0
      rw [hs0] at hs
      norm_num at hs
    rw [xi_eq_mul_completedRiemannZeta hs0 hs1,
      completedRiemannZeta_eq_Gammaℝ_mul hs]
    rw [zetaResidueUnit, Function.update_of_ne hs1]
    ring

private theorem logDeriv_xi_eq_endpoint_factors
    {s : ℂ} (hs : 0 < s.re) (hG : zetaResidueUnit s ≠ 0) :
    logDeriv xi s = s⁻¹ + logDeriv Complex.Gammaℝ s +
      logDeriv zetaResidueUnit s := by
  have hopen : IsOpen {w : ℂ | 0 < w.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have hev : xi =ᶠ[nhds s]
      fun w : ℂ => (w / 2 * Complex.Gammaℝ w) * zetaResidueUnit w := by
    filter_upwards [hopen.mem_nhds hs] with w hw
    exact xi_eq_half_mul_Gammaℝ_mul_zetaResidueUnit hw
  rw [logDeriv_congr_of_eventuallyEq hev]
  have hs0 : s ≠ 0 := by
    intro hzero
    rw [hzero] at hs
    norm_num at hs
  have hlin : DifferentiableAt ℂ (fun w : ℂ => w / 2) s := by fun_prop
  have hlin0 : s / 2 ≠ 0 := div_ne_zero hs0 (by norm_num)
  have hGamma : DifferentiableAt ℂ Complex.Gammaℝ s :=
    differentiableAt_Gammaℝ_of_re_pos hs
  have hGamma0 : Complex.Gammaℝ s ≠ 0 :=
    Complex.Gammaℝ_ne_zero_of_re_pos hs
  have hGdiff : DifferentiableAt ℂ zetaResidueUnit s :=
    analyticAt_zetaResidueUnit s |>.differentiableAt
  rw [logDeriv_mul (f := fun w : ℂ => w / 2 * Complex.Gammaℝ w)
      (g := zetaResidueUnit) s (mul_ne_zero hlin0 hGamma0) hG
      (hlin.mul hGamma) hGdiff,
    logDeriv_mul (f := fun w : ℂ => w / 2) (g := Complex.Gammaℝ)
      s hlin0 hGamma0 hlin hGamma]
  have hlinDeriv : deriv (fun w : ℂ => w / 2) s = 1 / 2 := by simp
  rw [logDeriv_apply, hlinDeriv]
  field_simp [hs0]

/-- Exact archimedean endpoint reserve. -/
theorem deriv_logDeriv_Gammaℝ_one_eq_pi_sq_div_eight :
    deriv (logDeriv Complex.Gammaℝ) 1 = (Real.pi : ℂ) ^ 2 / 8 := by
  have hopen : IsOpen {s : ℂ | 0 < s.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have heq : logDeriv Complex.Gammaℝ =ᶠ[nhds (1 : ℂ)]
      fun s : ℂ => -((Real.log Real.pi : ℂ) / 2) +
        Complex.digamma (s / 2) / 2 := by
    filter_upwards [hopen.mem_nhds (by norm_num : (0 : ℝ) < ((1 : ℂ)).re)] with s hs
    exact logDeriv_Gammaℝ_eq hs
  rw [heq.deriv_eq]
  have hnon : ∀ m : ℕ, (1 / 2 : ℂ) ≠ -(m : ℂ) := by
    intro m hm
    have hre := congrArg Complex.re hm
    norm_num at hre
    have hm0 : (0 : ℝ) ≤ m := by positivity
    linarith
  have hdigDiff : DifferentiableAt ℂ Complex.digamma (1 / 2 : ℂ) :=
    (GaloisForLFunctions.contDiffAt_digamma_n
      (1 / 2 : ℂ) hnon 1).differentiableAt (by norm_num)
  have hdig : HasDerivAt Complex.digamma ((Real.pi : ℂ) ^ 2 / 2) (1 / 2 : ℂ) := by
    rw [← trigamma_one_half]
    exact hdigDiff.hasDerivAt
  have hinner : HasDerivAt (fun s : ℂ => s / 2) (1 / 2) 1 := by
    simpa using (hasDerivAt_id (𝕜 := ℂ) (x := (1 : ℂ))).div_const 2
  have hcomp := hdig.comp (1 : ℂ) hinner
  have hdiv := hcomp.div_const 2
  have hsum := (hasDerivAt_const (x := (1 : ℂ))
    (c := -((Real.log Real.pi : ℂ) / 2))).add hdiv
  have hfun :
      (fun s : ℂ => -((Real.log Real.pi : ℂ) / 2) +
        Complex.digamma (s / 2) / 2) =
      ((fun _ : ℂ => -((Real.log Real.pi : ℂ) / 2)) +
        fun s : ℂ => (Complex.digamma ∘ fun w : ℂ => w / 2) s / 2) := by
    funext s
    rfl
  rw [hfun, hsum.deriv]
  ring

/-- Endpoint completion turns Xi divisor curvature into strict pole-unit log-concavity. -/
theorem neg_deriv_logDeriv_zetaResidueUnit_one_re_pos :
    0 < (-deriv (logDeriv zetaResidueUnit) 1).re := by
  have hGne : zetaResidueUnit 1 ≠ 0 := by simp [zetaResidueUnit_one]
  have hGevent : ∀ᶠ s in nhds (1 : ℂ), zetaResidueUnit s ≠ 0 :=
    zetaResidueUnit_analyticAt.continuousAt.eventually_ne hGne
  have hopen : IsOpen {s : ℂ | 0 < s.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have hsplit : logDeriv xi =ᶠ[nhds (1 : ℂ)]
      fun s : ℂ => s⁻¹ + logDeriv Complex.Gammaℝ s +
        logDeriv zetaResidueUnit s := by
    filter_upwards [
      hopen.mem_nhds (by norm_num : (0 : ℝ) < ((1 : ℂ)).re), hGevent] with s hs hG
    exact logDeriv_xi_eq_endpoint_factors hs hG
  have hinv : HasDerivAt (fun s : ℂ => s⁻¹) (-1) 1 := by
    have hdiff : DifferentiableAt ℂ (fun s : ℂ => s⁻¹) 1 := by
      exact (differentiableAt_id (𝕜 := ℂ)).inv one_ne_zero
    have h := hdiff.hasDerivAt
    rw [show deriv (fun s : ℂ => s⁻¹) 1 = -1 by simp] at h
    exact h
  have hGamma : HasDerivAt (logDeriv Complex.Gammaℝ)
      ((Real.pi : ℂ) ^ 2 / 8) 1 := by
    have hdiff : DifferentiableAt ℂ (logDeriv Complex.Gammaℝ) 1 := by
      have heq : logDeriv Complex.Gammaℝ =ᶠ[nhds (1 : ℂ)]
          fun s : ℂ => -((Real.log Real.pi : ℂ) / 2) +
            Complex.digamma (s / 2) / 2 := by
        filter_upwards [hopen.mem_nhds
          (by norm_num : (0 : ℝ) < ((1 : ℂ)).re)] with s hs
        exact logDeriv_Gammaℝ_eq hs
      have hnon : ∀ m : ℕ, (1 / 2 : ℂ) ≠ -(m : ℂ) := by
        intro m hm
        have hre := congrArg Complex.re hm
        norm_num at hre
        have hm0 : (0 : ℝ) ≤ m := by positivity
        linarith
      have hdigDiff : DifferentiableAt ℂ Complex.digamma (1 / 2 : ℂ) :=
        (GaloisForLFunctions.contDiffAt_digamma_n
          (1 / 2 : ℂ) hnon 1).differentiableAt (by norm_num)
      have hrhs : DifferentiableAt ℂ
          (fun s : ℂ => -((Real.log Real.pi : ℂ) / 2) +
            Complex.digamma (s / 2) / 2) 1 := by
        exact (differentiableAt_const _).add
          ((hdigDiff.comp (1 : ℂ) (by fun_prop)).div_const 2)
      exact hrhs.congr_of_eventuallyEq heq
    rw [← deriv_logDeriv_Gammaℝ_one_eq_pi_sq_div_eight]
    exact hdiff.hasDerivAt
  have hGdiff : DifferentiableAt ℂ (logDeriv zetaResidueUnit) 1 := by
    rw [show logDeriv zetaResidueUnit =
        fun z => deriv zetaResidueUnit z / zetaResidueUnit z by
      funext z
      rw [logDeriv_apply]]
    exact (zetaResidueUnit_analyticAt.deriv.div zetaResidueUnit_analyticAt hGne).differentiableAt
  have hsum := (hinv.add hGamma).add hGdiff.hasDerivAt
  have hcurv : deriv (logDeriv xi) 1 =
      -1 + (Real.pi : ℂ) ^ 2 / 8 + deriv (logDeriv zetaResidueUnit) 1 := by
    rw [hsplit.deriv_eq]
    exact hsum.deriv
  have hxiTrace := deriv_logDeriv_xi_one_eq_neg_rawReciprocalPowerTrace_two
  have htrace := norm_xiRawReciprocalPowerTrace_two_lt_three_over_fortyThree
  have hxiRe : (deriv (logDeriv xi) 1).re < 3 / 43 := by
    calc
      (deriv (logDeriv xi) 1).re ≤ ‖deriv (logDeriv xi) 1‖ :=
        Complex.re_le_norm _
      _ = ‖xiRawReciprocalPowerTrace 2‖ := by rw [hxiTrace, norm_neg]
      _ < 3 / 43 := htrace
  have hpi := Real.pi_gt_three
  have hreserve : (1 / 8 : ℝ) < Real.pi ^ 2 / 8 - 1 := by
    nlinarith [Real.pi_pos]
  have hpoleEq : -deriv (logDeriv zetaResidueUnit) 1 =
      (Real.pi : ℂ) ^ 2 / 8 - 1 - deriv (logDeriv xi) 1 := by
    rw [hcurv]
    ring
  rw [hpoleEq]
  norm_num [Complex.div_re, Complex.mul_re, pow_two]
  nlinarith

/-- The positive von Mangoldt logarithmic moment makes the Euler correction strictly favorable. -/
theorem neg_deriv_infinitePrimeFlux_two_re_pos :
    0 < (-deriv infinitePrimeFlux 2).re := by
  have hopen : IsOpen {s : ℂ | 1 < s.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have heq : infinitePrimeFlux =ᶠ[nhds (2 : ℂ)]
      LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) := by
    filter_upwards [hopen.mem_nhds (by norm_num : (1 : ℝ) < ((2 : ℂ)).re)] with s hs
    exact infinitePrimeFlux_eq_vonMangoldtLSeries hs
  have hsum := GaloisForLFunctions.HTGeometry.summable_vonMangoldt_logMul_rpow
    (σ := (2 : ℝ)) (by norm_num)
  have hterm : 0 < (Real.log 2 * (ArithmeticFunction.vonMangoldt 2 : ℝ)) *
      (2 : ℝ) ^ (-(2 : ℝ)) := by
    rw [ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
    positivity
  have hnonneg : ∀ n : ℕ, 0 ≤
      (Real.log n * (ArithmeticFunction.vonMangoldt n : ℝ)) *
        (n : ℝ) ^ (-(2 : ℝ)) := by
    intro n
    exact mul_nonneg
      (mul_nonneg (Real.log_natCast_nonneg n) ArithmeticFunction.vonMangoldt_nonneg)
      (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  have hpos : 0 < ∑' n : ℕ,
      (Real.log n * (ArithmeticFunction.vonMangoldt n : ℝ)) *
        (n : ℝ) ^ (-(2 : ℝ)) := by
    have hle := hsum.le_tsum 2 (fun n _ => hnonneg n)
    exact lt_of_lt_of_le (by simpa using hterm) hle
  have hmoment := GaloisForLFunctions.HTGeometry.ofReal_tsum_vonMangoldt_logMul_eq
    (σ := (2 : ℝ)) (by norm_num)
  have hderivEq : deriv infinitePrimeFlux 2 =
      deriv (LSeries fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) 2 := heq.deriv_eq
  rw [hderivEq]
  have hneg : -deriv (LSeries fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) 2 =
      ((∑' n : ℕ, (Real.log n * (ArithmeticFunction.vonMangoldt n : ℝ)) *
        (n : ℝ) ^ (-(2 : ℝ)) : ℝ) : ℂ) := by
    simpa using hmoment.symm
  rw [hneg]
  simpa using hpos

end

end RHTower

namespace RHTower.HedenmalmThetaSource

noncomputable section

/-- **Strict arithmetic orientation.**  Pole-unit completion and the positive Euler moment point
the regular squarefree current in the same transverse direction. -/
theorem deriv_squarefreeMobiusCriticalRegularCurrent_one_re_pos :
    0 < (deriv squarefreeMobiusCriticalRegularCurrent 1).re := by
  rw [deriv_squarefreeMobiusCriticalRegularCurrent_eq_pole_curvature_add_euler_curvature]
  have hpole := RHTower.neg_deriv_logDeriv_zetaResidueUnit_one_re_pos
  have heuler := RHTower.neg_deriv_infinitePrimeFlux_two_re_pos
  norm_num [Complex.mul_re] at hpole heuler ⊢
  linarith

/-- Exact real pole-unit value needed to orient the literal midpoint defect. -/
theorem squarefreeMobiusCriticalPoleUnit_one_eq_ofReal :
    squarefreeMobiusCriticalPoleUnit 1 = ((6 / Real.pi ^ 2 : ℝ) : ℂ) := by
  rw [squarefreeMobiusCriticalPoleUnit_one, riemannZeta_two]
  have hpi : ((Real.pi : ℂ) ^ 2) ≠ 0 := pow_ne_zero 2 (by exact_mod_cast Real.pi_ne_zero)
  push_cast
  field_simp

/-- **P-G42 strict literal-source transverse curvature.**  Every nontrivial real two-aperture
split has positive quadratic pole-unit midpoint defect. -/
theorem squarefreeMobiusPoleUnitMidpointDefect_iteratedDeriv_two_re_pos
    {x z : ℝ} (hxz : x ≠ z) :
    0 < (iteratedDeriv 2
      (squarefreeMobiusPoleUnitMidpointDefect (x : ℂ) (z : ℂ)) 0).re := by
  rw [squarefreeMobiusPoleUnitMidpointDefect_iteratedDeriv_two,
    squarefreeMobiusCriticalPoleUnit_one_eq_ofReal]
  have hcurrent := deriv_squarefreeMobiusCriticalRegularCurrent_one_re_pos
  have hpi : 0 < Real.pi ^ 2 := sq_pos_of_pos Real.pi_pos
  have hsplit : 0 < (x - z) ^ 2 / 2 := div_pos (sq_pos_of_ne_zero (sub_ne_zero.mpr hxz)) (by norm_num)
  have hcoef :
      (((x : ℂ) - (z : ℂ)) ^ 2 / 2) * (((6 / Real.pi ^ 2 : ℝ) : ℂ)) ^ 2 =
        ((((x - z) ^ 2 / 2) * (6 / Real.pi ^ 2) ^ 2 : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hcoef]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  exact mul_pos (mul_pos hsplit (sq_pos_of_pos (div_pos (by norm_num) hpi))) hcurrent

end

end RHTower.HedenmalmThetaSource
