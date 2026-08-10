import GaloisForLFunctions.RHTower.XiMassOptimalCurvedBesselDecay
import GaloisForLFunctions.RHTower.XiMassCriticalCenteredAtomCone
import GaloisForLFunctions.RHTower.VonMangoldtLineSeriesSwap

/-!
# Sharp spacelike-cone summability for the centered Xi-mass atoms

The optimal curved contour has a potentially moving Lorentz boost.  This module proves that its
boost factor is uniformly bounded on every cone strictly inside the spacelike chamber.  The sharp
slope inequality is then converted into a fixed positive Dirichlet exponent margin.  Consequently
the complete centered von Mangoldt contribution from

`alpha * u <= log n`,  `xiMassSpacelikeSharpSlope a < alpha`,

is absolutely summable, uniformly in the vertical parameter `u` and in every finite cutoff.

This closes the absolute spacelike part of the Route T source problem.  Any remaining RH-strength
cancellation is confined to the timelike-plus-glancing layer.  No asymptotic expansion, numerical
computation, or unproved arithmetic hypothesis is used.
-/

open Complex Real MeasureTheory Set Filter Topology

namespace RHTower

noncomputable section

/-- Lorentz boost is uniformly bounded when time coordinate dominates space coordinate by a fixed
factor `alpha > 1`. -/
theorem exp_arsinh_div_lorentzGap_le_slopeRatio
    {alpha A B q : ℝ} (halpha : 1 < alpha) (hB : 0 ≤ B)
    (hAB : alpha * B ≤ A) (hq : 0 < q) (hqSq : q ^ 2 = A ^ 2 - B ^ 2) :
    Real.exp (Real.arsinh (B / q)) ≤ (alpha + 1) / (alpha - 1) := by
  have halpha0 : 0 < alpha := lt_trans (by norm_num) halpha
  have hA : 0 ≤ A := le_trans (mul_nonneg halpha0.le hB) hAB
  have hBA : B < A := by
    by_cases hB0 : B = 0
    · subst B
      have hqSqPos : 0 < q ^ 2 := sq_pos_of_pos hq
      nlinarith
    · have hBpos : 0 < B := lt_of_le_of_ne hB (Ne.symm hB0)
      nlinarith
  have hqLower : A - B ≤ q := by
    have hsub : 0 ≤ A - B := sub_nonneg.mpr hBA.le
    have hsq : (A - B) ^ 2 ≤ q ^ 2 := by
      rw [hqSq]
      nlinarith
    nlinarith
  have hratio : (A + B) / q ≤ (alpha + 1) / (alpha - 1) := by
    have hden : 0 < alpha - 1 := sub_pos.mpr halpha
    rw [div_le_iff₀ hq, div_mul_eq_mul_div, le_div_iff₀ hden]
    have hnum : 0 ≤ alpha + 1 := by linarith
    have hqScaled := mul_le_mul_of_nonneg_left hqLower hnum
    nlinarith
  have hcosh := cosh_arsinh_div_sqrt_sq_sub_sq hB hBA
  have hqSqrt : Real.sqrt (A ^ 2 - B ^ 2) = q := by
    rw [← hqSq, Real.sqrt_sq_eq_abs, abs_of_pos hq]
  rw [hqSqrt] at hcosh
  rw [← Real.cosh_add_sinh (Real.arsinh (B / q)),
    Real.sinh_arsinh, hcosh]
  simpa only [add_div] using hratio

/-- Sine-like cone margin attached to a slope `alpha`. -/
def xiMassSpacelikeSlopeMargin (alpha : ℝ) : ℝ :=
  Real.sqrt (1 - (alpha⁻¹) ^ 2)

theorem xiMassSpacelikeSlopeMargin_pos
    {alpha : ℝ} (halpha : 1 < alpha) :
    0 < xiMassSpacelikeSlopeMargin alpha := by
  rw [xiMassSpacelikeSlopeMargin, Real.sqrt_pos]
  have halpha0 : 0 < alpha := lt_trans (by norm_num) halpha
  have hinv : 0 < alpha⁻¹ := inv_pos.mpr halpha0
  have hinvlt : alpha⁻¹ < 1 := by
    rw [inv_lt_one₀ halpha0]
    exact halpha
  nlinarith [sq_pos_of_pos hinv, sq_nonneg (1 - alpha⁻¹)]

theorem sq_xiMassSpacelikeSlopeMargin
    {alpha : ℝ} (halpha : 1 < alpha) :
    xiMassSpacelikeSlopeMargin alpha ^ 2 = 1 - (alpha⁻¹) ^ 2 := by
  have harg : 0 ≤ 1 - (alpha⁻¹) ^ 2 := by
    have hp := xiMassSpacelikeSlopeMargin_pos halpha
    rw [xiMassSpacelikeSlopeMargin, Real.sqrt_pos] at hp
    exact hp.le
  rw [xiMassSpacelikeSlopeMargin, Real.sq_sqrt harg]

theorem one_lt_xiMassSpacelikeSharpSlope
    {a : ℝ} (ha : 1 / 2 < a) :
    1 < xiMassSpacelikeSharpSlope a := by
  let k := Real.sqrt (a ^ 2 - 1 / 4)
  have ha0 : 0 < a := lt_trans (by norm_num) ha
  have hk : 0 < k := by
    simpa only [k] using xiMassSpacelikeSharpSlope_denominator_pos ha
  have hkSq : k ^ 2 = a ^ 2 - 1 / 4 := by
    dsimp only [k]
    rw [Real.sq_sqrt]
    nlinarith [sq_pos_of_pos ha0]
  rw [xiMassSpacelikeSharpSlope, one_lt_div hk]
  nlinarith [sq_nonneg (a + k)]

/-- A slope strictly above the sharp spacelike threshold supplies a strict Dirichlet exponent
margin beyond the critical half-density. -/
theorem half_lt_mul_xiMassSpacelikeSlopeMargin
    {a alpha : ℝ} (ha : 1 / 2 < a)
    (hsharp : xiMassSpacelikeSharpSlope a < alpha) :
    1 / 2 < a * xiMassSpacelikeSlopeMargin alpha := by
  let k := Real.sqrt (a ^ 2 - 1 / 4)
  let beta := xiMassSpacelikeSlopeMargin alpha
  have ha0 : 0 < a := lt_trans (by norm_num) ha
  have hk : 0 < k := by
    simpa only [k] using xiMassSpacelikeSharpSlope_denominator_pos ha
  have halpha : 1 < alpha := by
    exact (one_lt_xiMassSpacelikeSharpSlope ha).trans hsharp
  have hbeta : 0 < beta := by
    simpa only [beta] using xiMassSpacelikeSlopeMargin_pos halpha
  have hkSq : k ^ 2 = a ^ 2 - 1 / 4 := by
    dsimp only [k]
    rw [Real.sq_sqrt]
    nlinarith [sq_pos_of_pos ha0]
  have hbetaSq : beta ^ 2 = 1 - (alpha⁻¹) ^ 2 := by
    simpa only [beta] using sq_xiMassSpacelikeSlopeMargin halpha
  have hlin : a < alpha * k := by
    rw [xiMassSpacelikeSharpSlope] at hsharp
    exact (div_lt_iff₀ hk).mp hsharp
  have halpha0 : 0 < alpha := lt_trans (by norm_num) halpha
  have halphaInv : alpha * alpha⁻¹ = 1 := mul_inv_cancel₀ halpha0.ne'
  have hdiv : a * alpha⁻¹ < k := by
    nlinarith [mul_pos hk halpha0]
  have hsq : (a * alpha⁻¹) ^ 2 < k ^ 2 := by
    nlinarith [mul_pos ha0 (inv_pos.mpr halpha0), sq_nonneg (a * alpha⁻¹ + k)]
  have hmainSq : (1 / 2 : ℝ) ^ 2 < (a * beta) ^ 2 := by
    rw [hkSq] at hsq
    rw [show (a * beta) ^ 2 = a ^ 2 * beta ^ 2 by ring, hbetaSq]
    nlinarith
  nlinarith [mul_pos ha0 hbeta]

/-- On a slope-`alpha` cone, Lorentz gap is at least the fixed fraction `beta` of height. -/
theorem xiMassSpacelikeSlopeMargin_mul_le_sqrt_gap
    {alpha u h : ℝ} (halpha : 1 < alpha) (hu : 0 ≤ u)
    (hcone : alpha * u ≤ h) :
    xiMassSpacelikeSlopeMargin alpha * h ≤ Real.sqrt (h ^ 2 - u ^ 2) := by
  let beta := xiMassSpacelikeSlopeMargin alpha
  have halpha0 : 0 < alpha := lt_trans (by norm_num) halpha
  have hbeta : 0 < beta := by
    simpa only [beta] using xiMassSpacelikeSlopeMargin_pos halpha
  have hh : 0 ≤ h := le_trans (mul_nonneg halpha0.le hu) hcone
  have hbetaSq : beta ^ 2 = 1 - (alpha⁻¹) ^ 2 := by
    simpa only [beta] using sq_xiMassSpacelikeSlopeMargin halpha
  have hsqCone : (alpha * u) ^ 2 ≤ h ^ 2 := by
    nlinarith [mul_nonneg halpha0.le hu]
  have halphaInv : alpha ^ 2 * (alpha⁻¹) ^ 2 = 1 := by
    field_simp [halpha0.ne']
  have huSq : u ^ 2 ≤ (alpha⁻¹) ^ 2 * h ^ 2 := by
    nlinarith
  have hgap : 0 ≤ h ^ 2 - u ^ 2 := by nlinarith
  have hsqrtSq : Real.sqrt (h ^ 2 - u ^ 2) ^ 2 = h ^ 2 - u ^ 2 :=
    Real.sq_sqrt hgap
  have hbetaH : 0 ≤ beta * h := mul_nonneg hbeta.le hh
  have hsqrt0 := Real.sqrt_nonneg (h ^ 2 - u ^ 2)
  have hsq : (beta * h) ^ 2 ≤ Real.sqrt (h ^ 2 - u ^ 2) ^ 2 := by
    rw [hsqrtSq, show (beta * h) ^ 2 = beta ^ 2 * h ^ 2 by ring, hbetaSq]
    nlinarith
  nlinarith

/-- Optimal curved-contour estimate with the moving Lorentz boost replaced by a slope-only
constant. -/
theorem norm_stripFourier_xiMass_le_optimal_full_exponent_uniformBoost
    {a sigma alpha u h q₀ : ℝ}
    (ha : 0 < a) (hsigma : 0 < sigma) (halpha : 1 < alpha)
    (hu : 0 ≤ u) (hh : 0 < h) (hcone : alpha * u ≤ h)
    (hq₀ : 0 < q₀)
    (hq₀kappa : q₀ ≤ HTGeometry.csqrtRe
      (xiMassSpacelikePropagationArgument sigma u h)) :
    let kappa := HTGeometry.csqrtRe
      (xiMassSpacelikePropagationArgument sigma u h)
    ‖stripFourier
      (xiMassAnalyticTest a ((sigma : ℂ) + (u : ℂ) * I)) (h : ℂ)‖ ≤
        2 * a * ((alpha + 1) / (alpha - 1)) *
          Real.exp (-(a * (kappa - q₀))) *
            GaloisForLFunctions.HTGeometry.realModifiedBesselKOrder (a * q₀) 1 := by
  dsimp only
  let kappa := HTGeometry.csqrtRe
    (xiMassSpacelikePropagationArgument sigma u h)
  have huh : u < h := by
    by_cases hu0 : u = 0
    · simpa only [hu0] using hh
    · have hupos : 0 < u := lt_of_le_of_ne hu (Ne.symm hu0)
      have huAlpha : u < alpha * u := by nlinarith
      exact huAlpha.trans_le hcone
  have hkappa : 0 < kappa := by
    have hgap := sqrt_spacelikeGap_lt_csqrtRe_propagationArgument
      hsigma hu huh
    exact lt_of_le_of_lt (Real.sqrt_nonneg _) hgap
  rcases exists_norm_stripFourier_xiMass_le_optimal_full_exponent
      ha hsigma hu huh hq₀ hq₀kappa with
    ⟨theta, htheta0, hthetaPi, hopt, hfourier⟩
  let A := sigma * Real.cos theta + h * Real.sin theta
  let B := u * Real.sin theta
  have hthetaLePi : theta ≤ Real.pi := by
    nlinarith [Real.pi_pos]
  have hsin : 0 ≤ Real.sin theta :=
    Real.sin_nonneg_of_nonneg_of_le_pi htheta0 hthetaLePi
  have hcos : 0 ≤ Real.cos theta := by
    have hneg : -(Real.pi / 2) < theta := by nlinarith [Real.pi_pos]
    exact (Real.cos_pos_of_mem_Ioo ⟨hneg, hthetaPi⟩).le
  have hB : 0 ≤ B := by
    dsimp only [B]
    positivity
  have hAB : alpha * B ≤ A := by
    dsimp only [A, B]
    have hslope := mul_le_mul_of_nonneg_right hcone hsin
    have harch : 0 ≤ sigma * Real.cos theta := mul_nonneg hsigma.le hcos
    nlinarith
  have hkappaSq : kappa ^ 2 = A ^ 2 - B ^ 2 := by
    simpa only [xiMassSpacelikeContourRateSq, A, B, kappa] using hopt.symm
  have hboost : Real.exp (Real.arsinh (B / kappa)) ≤
      (alpha + 1) / (alpha - 1) :=
    exp_arsinh_div_lorentzGap_le_slopeRatio halpha hB hAB hkappa hkappaSq
  have htail : 0 ≤ Real.exp (-(a * (kappa - q₀))) *
      GaloisForLFunctions.HTGeometry.realModifiedBesselKOrder (a * q₀) 1 := by
    exact mul_nonneg (Real.exp_nonneg _)
      (GaloisForLFunctions.HTGeometry.realModifiedBesselKOrder_pos
        (mul_pos ha hq₀) 1).le
  calc
    ‖stripFourier
        (xiMassAnalyticTest a ((sigma : ℂ) + (u : ℂ) * I)) (h : ℂ)‖ ≤
        2 * a * Real.exp (Real.arsinh (B / kappa)) *
          Real.exp (-(a * (kappa - q₀))) *
            GaloisForLFunctions.HTGeometry.realModifiedBesselKOrder (a * q₀) 1 := by
      simpa only [B, kappa] using hfourier
    _ ≤ 2 * a * ((alpha + 1) / (alpha - 1)) *
          Real.exp (-(a * (kappa - q₀))) *
            GaloisForLFunctions.HTGeometry.realModifiedBesselKOrder (a * q₀) 1 := by
      have hscaled := mul_le_mul_of_nonneg_left hboost (mul_nonneg (by positivity) htail)
      nlinarith

/-- Exponent of the slope-`alpha` Dirichlet majorant. -/
def xiMassSharpSpacelikeDirichletExponent (a alpha : ℝ) : ℝ :=
  1 / 2 + a * xiMassSpacelikeSlopeMargin alpha

/-- Fixed absolute-majorant constant obtained by anchoring the Bessel comparison at the first
arithmetic height `log 2`. -/
def xiMassSharpSpacelikeProfileConstant (a alpha : ℝ) : ℝ :=
  let beta := xiMassSpacelikeSlopeMargin alpha
  let q₀ := beta * Real.log 2
  2 * a * ((alpha + 1) / (alpha - 1)) * Real.exp (a * q₀) *
    GaloisForLFunctions.HTGeometry.realModifiedBesselKOrder (a * q₀) 1

theorem xiMassSharpSpacelikeProfileConstant_nonneg
    {a alpha : ℝ} (ha : 0 < a) (halpha : 1 < alpha) :
    0 ≤ xiMassSharpSpacelikeProfileConstant a alpha := by
  have hbeta := xiMassSpacelikeSlopeMargin_pos halpha
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hq₀ : 0 < xiMassSpacelikeSlopeMargin alpha * Real.log 2 :=
    mul_pos hbeta hlog
  unfold xiMassSharpSpacelikeProfileConstant
  dsimp only
  have hratio : 0 ≤ (alpha + 1) / (alpha - 1) := by positivity
  have hK : 0 ≤
      GaloisForLFunctions.HTGeometry.realModifiedBesselKOrder
        (a * (xiMassSpacelikeSlopeMargin alpha * Real.log 2)) 1 :=
    (GaloisForLFunctions.HTGeometry.realModifiedBesselKOrder_pos
      (mul_pos ha hq₀) 1).le
  exact mul_nonneg
    (mul_nonneg (mul_nonneg (by positivity) hratio) (Real.exp_nonneg _)) hK

/-- Coefficient-faithful sharp spacelike bound for the damped mass profile. -/
theorem norm_xiMassCriticalDampedFourierProfile_le_sharpSpacelike
    {a sigma alpha u h : ℝ}
    (ha : 1 / 2 < a) (hsigma : 0 < sigma)
    (hsharp : xiMassSpacelikeSharpSlope a < alpha)
    (hu : 0 ≤ u) (hcone : alpha * u ≤ h)
    (hlogTwo : Real.log 2 ≤ h) :
    ‖xiMassCriticalDampedFourierProfile a sigma u h‖ ≤
      xiMassSharpSpacelikeProfileConstant a alpha *
        Real.exp (-(xiMassSharpSpacelikeDirichletExponent a alpha * h)) := by
  let beta := xiMassSpacelikeSlopeMargin alpha
  let q₀ := beta * Real.log 2
  let kappa := HTGeometry.csqrtRe
    (xiMassSpacelikePropagationArgument sigma u h)
  have ha0 : 0 < a := lt_trans (by norm_num) ha
  have halpha : 1 < alpha := by
    exact (one_lt_xiMassSpacelikeSharpSlope ha).trans hsharp
  have hbeta : 0 < beta := by
    simpa only [beta] using xiMassSpacelikeSlopeMargin_pos halpha
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hq₀ : 0 < q₀ := by
    dsimp only [q₀]
    exact mul_pos hbeta hlog
  have hh : 0 < h := hlog.trans_le hlogTwo
  have huh : u < h := by
    by_cases hu0 : u = 0
    · simpa only [hu0] using hh
    · have hupos : 0 < u := lt_of_le_of_ne hu (Ne.symm hu0)
      have huAlpha : u < alpha * u := by nlinarith
      exact huAlpha.trans_le hcone
  have hbetaGap := xiMassSpacelikeSlopeMargin_mul_le_sqrt_gap
    halpha hu hcone
  have hgapKappa := sqrt_spacelikeGap_lt_csqrtRe_propagationArgument
    hsigma hu huh
  have hq₀kappa : q₀ ≤ kappa := by
    dsimp only [q₀, kappa]
    have hheight := mul_le_mul_of_nonneg_left hlogTwo hbeta.le
    exact hheight.trans (hbetaGap.trans hgapKappa.le)
  have hfourier := norm_stripFourier_xiMass_le_optimal_full_exponent_uniformBoost
    ha0 hsigma halpha hu hh hcone hq₀ hq₀kappa
  dsimp only at hfourier
  have hkappaLower : beta * h ≤ kappa := by
    dsimp only [beta, kappa]
    exact hbetaGap.trans hgapKappa.le
  have hexp : Real.exp (-(a * (kappa - q₀))) ≤
      Real.exp (a * q₀) * Real.exp (-(a * beta * h)) := by
    calc
      Real.exp (-(a * (kappa - q₀))) ≤
          Real.exp (-(a * (beta * h - q₀))) := by
        exact Real.exp_le_exp.mpr (by nlinarith)
      _ = Real.exp (a * q₀) * Real.exp (-(a * beta * h)) := by
        rw [← Real.exp_add]
        congr 1
        ring
  have hratio : 0 ≤ (alpha + 1) / (alpha - 1) := by positivity
  have hK : 0 ≤
      GaloisForLFunctions.HTGeometry.realModifiedBesselKOrder (a * q₀) 1 :=
    (GaloisForLFunctions.HTGeometry.realModifiedBesselKOrder_pos
      (mul_pos ha0 hq₀) 1).le
  have hfourier' :
      ‖stripFourier
        (xiMassAnalyticTest a ((sigma : ℂ) + (u : ℂ) * I)) (h : ℂ)‖ ≤
        xiMassSharpSpacelikeProfileConstant a alpha *
          Real.exp (-(a * beta * h)) := by
    calc
      ‖stripFourier
          (xiMassAnalyticTest a ((sigma : ℂ) + (u : ℂ) * I)) (h : ℂ)‖ ≤
          2 * a * ((alpha + 1) / (alpha - 1)) *
            Real.exp (-(a * (kappa - q₀))) *
              GaloisForLFunctions.HTGeometry.realModifiedBesselKOrder (a * q₀) 1 := by
        simpa only [kappa] using hfourier
      _ ≤ 2 * a * ((alpha + 1) / (alpha - 1)) *
            (Real.exp (a * q₀) * Real.exp (-(a * beta * h))) *
              GaloisForLFunctions.HTGeometry.realModifiedBesselKOrder (a * q₀) 1 := by
        gcongr
      _ = xiMassSharpSpacelikeProfileConstant a alpha *
            Real.exp (-(a * beta * h)) := by
        unfold xiMassSharpSpacelikeProfileConstant
        dsimp only [beta, q₀]
        ring
  rw [xiMassCriticalDampedFourierProfile, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  calc
    Real.exp (-h / 2) *
        ‖stripFourier
          (xiMassAnalyticTest a ((sigma : ℂ) + u * I)) (h : ℂ)‖ ≤
      Real.exp (-h / 2) *
        (xiMassSharpSpacelikeProfileConstant a alpha *
          Real.exp (-(a * beta * h))) :=
        mul_le_mul_of_nonneg_left hfourier' (Real.exp_nonneg _)
    _ = xiMassSharpSpacelikeProfileConstant a alpha *
        Real.exp (-(xiMassSharpSpacelikeDirichletExponent a alpha * h)) := by
      rw [show Real.exp (-h / 2) *
          (xiMassSharpSpacelikeProfileConstant a alpha *
            Real.exp (-(a * beta * h))) =
        xiMassSharpSpacelikeProfileConstant a alpha *
          (Real.exp (-h / 2) * Real.exp (-(a * beta * h))) by ring,
        ← Real.exp_add]
      unfold xiMassSharpSpacelikeDirichletExponent
      dsimp only [beta]
      congr 2
      ring

/-- Centered atom retained exactly on the strict-slope spacelike region. -/
noncomputable def xiMassSharpSpacelikeCenteredAtom
    (a sigma alpha u : ℝ) (n : ℕ) : ℂ :=
  if alpha * u ≤ Real.log ((n : ℝ) + 2) then
    ((ArithmeticFunction.vonMangoldt (n + 2) - 1 : ℝ) : ℂ) *
      xiMassCriticalDampedFourierProfile a sigma u
        (Real.log ((n : ℝ) + 2))
  else 0

/-- Positive arithmetic majorant for the sharp spacelike atom. -/
noncomputable def xiMassSharpSpacelikeCenteredMajorant
    (a alpha : ℝ) (n : ℕ) : ℝ :=
  xiMassSharpSpacelikeProfileConstant a alpha *
    ((ArithmeticFunction.vonMangoldt (n + 2) + 1) *
      ((n : ℝ) + 2) ^
        (-xiMassSharpSpacelikeDirichletExponent a alpha))

theorem xiMassSharpSpacelikeCenteredMajorant_nonneg
    {a alpha : ℝ} (ha : 0 < a) (halpha : 1 < alpha) (n : ℕ) :
    0 ≤ xiMassSharpSpacelikeCenteredMajorant a alpha n := by
  unfold xiMassSharpSpacelikeCenteredMajorant
  have hC := xiMassSharpSpacelikeProfileConstant_nonneg ha halpha
  have hLambda : 0 ≤ ArithmeticFunction.vonMangoldt (n + 2) :=
    ArithmeticFunction.vonMangoldt_nonneg
  positivity

/-- Every spacelike centered atom is pointwise dominated by one fixed Dirichlet majorant,
independently of the vertical parameter. -/
theorem norm_xiMassSharpSpacelikeCenteredAtom_le
    {a sigma alpha u : ℝ} (ha : 1 / 2 < a) (hsigma : 0 < sigma)
    (hsharp : xiMassSpacelikeSharpSlope a < alpha) (hu : 0 ≤ u)
    (n : ℕ) :
    ‖xiMassSharpSpacelikeCenteredAtom a sigma alpha u n‖ ≤
      xiMassSharpSpacelikeCenteredMajorant a alpha n := by
  let x : ℝ := (n : ℝ) + 2
  let p : ℝ := xiMassSharpSpacelikeDirichletExponent a alpha
  have ha0 : 0 < a := lt_trans (by norm_num) ha
  have halpha : 1 < alpha := by
    exact (one_lt_xiMassSpacelikeSharpSlope ha).trans hsharp
  have hx : 0 < x := by dsimp only [x]; positivity
  have hxTwo : (2 : ℝ) ≤ x := by dsimp only [x]; norm_num
  have hlogTwo : Real.log 2 ≤ Real.log x :=
    Real.log_le_log (by norm_num) hxTwo
  have hrpow : Real.exp (-(p * Real.log x)) = x ^ (-p) := by
    rw [Real.rpow_def_of_pos hx]
    congr 1
    ring
  rw [xiMassSharpSpacelikeCenteredAtom]
  split_ifs with hcone
  · have hprofile := norm_xiMassCriticalDampedFourierProfile_le_sharpSpacelike
      ha hsigma hsharp hu hcone hlogTwo
    have hprofile' :
        ‖xiMassCriticalDampedFourierProfile a sigma u (Real.log x)‖ ≤
          xiMassSharpSpacelikeProfileConstant a alpha * x ^ (-p) := by
      change ‖xiMassCriticalDampedFourierProfile a sigma u (Real.log x)‖ ≤
        xiMassSharpSpacelikeProfileConstant a alpha *
          Real.exp (-(p * Real.log x)) at hprofile
      rw [hrpow] at hprofile
      exact hprofile
    have hLambda : 0 ≤ ArithmeticFunction.vonMangoldt (n + 2) :=
      ArithmeticFunction.vonMangoldt_nonneg
    have hcoeff :
        |ArithmeticFunction.vonMangoldt (n + 2) - 1| ≤
          ArithmeticFunction.vonMangoldt (n + 2) + 1 := by
      rw [abs_le]
      constructor <;> linarith
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    unfold xiMassSharpSpacelikeCenteredMajorant
    change |ArithmeticFunction.vonMangoldt (n + 2) - 1| *
        ‖xiMassCriticalDampedFourierProfile a sigma u (Real.log x)‖ ≤
      xiMassSharpSpacelikeProfileConstant a alpha *
        ((ArithmeticFunction.vonMangoldt (n + 2) + 1) * x ^ (-p))
    have hC := xiMassSharpSpacelikeProfileConstant_nonneg ha0 halpha
    have hpow : 0 ≤ x ^ (-p) := Real.rpow_nonneg hx.le _
    calc
      |ArithmeticFunction.vonMangoldt (n + 2) - 1| *
          ‖xiMassCriticalDampedFourierProfile a sigma u (Real.log x)‖ ≤
        |ArithmeticFunction.vonMangoldt (n + 2) - 1| *
          (xiMassSharpSpacelikeProfileConstant a alpha * x ^ (-p)) :=
        mul_le_mul_of_nonneg_left hprofile' (abs_nonneg _)
      _ ≤ (ArithmeticFunction.vonMangoldt (n + 2) + 1) *
          (xiMassSharpSpacelikeProfileConstant a alpha * x ^ (-p)) :=
        mul_le_mul_of_nonneg_right hcoeff (mul_nonneg hC hpow)
      _ = xiMassSharpSpacelikeProfileConstant a alpha *
          ((ArithmeticFunction.vonMangoldt (n + 2) + 1) * x ^ (-p)) := by ring
  · simpa only [norm_zero] using
      xiMassSharpSpacelikeCenteredMajorant_nonneg ha0 halpha n

/-- The fixed majorant is summable precisely because the curved-contour exponent has crossed the
Dirichlet threshold `1`. -/
theorem summable_xiMassSharpSpacelikeCenteredMajorant
    {a alpha : ℝ} (ha : 1 / 2 < a)
    (hsharp : xiMassSpacelikeSharpSlope a < alpha) :
    Summable (xiMassSharpSpacelikeCenteredMajorant a alpha) := by
  let p := xiMassSharpSpacelikeDirichletExponent a alpha
  have ha0 : 0 < a := lt_trans (by norm_num) ha
  have halpha : 1 < alpha := by
    exact (one_lt_xiMassSpacelikeSharpSlope ha).trans hsharp
  have hp : 1 < p := by
    have hmargin := half_lt_mul_xiMassSpacelikeSlopeMargin ha hsharp
    dsimp only [p, xiMassSharpSpacelikeDirichletExponent]
    linarith
  have hLambdaAll : Summable (fun n : ℕ =>
      (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-p)) :=
    summable_vonMangoldt_mul_rpow hp
  have hLambdaShift : Summable (fun n : ℕ =>
      (ArithmeticFunction.vonMangoldt (n + 2) : ℝ) *
        ((n : ℝ) + 2) ^ (-p)) := by
    simpa only [Nat.cast_add, Nat.cast_ofNat] using
      (summable_nat_add_iff 2).mpr hLambdaAll
  have hPowerAll : Summable (fun n : ℕ => (n : ℝ) ^ (-p)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  have hPowerShift : Summable (fun n : ℕ => ((n : ℝ) + 2) ^ (-p)) := by
    simpa only [Nat.cast_add, Nat.cast_ofNat] using
      (summable_nat_add_iff 2).mpr hPowerAll
  have hcore : Summable (fun n : ℕ =>
      (ArithmeticFunction.vonMangoldt (n + 2) + 1) *
        ((n : ℝ) + 2) ^ (-p)) := by
    convert hLambdaShift.add hPowerShift using 1
    funext n
    ring
  unfold xiMassSharpSpacelikeCenteredMajorant
  exact hcore.mul_left (xiMassSharpSpacelikeProfileConstant a alpha)

theorem summable_norm_xiMassSharpSpacelikeCenteredAtom
    {a sigma alpha u : ℝ} (ha : 1 / 2 < a) (hsigma : 0 < sigma)
    (hsharp : xiMassSpacelikeSharpSlope a < alpha) (hu : 0 ≤ u) :
    Summable (fun n : ℕ =>
      ‖xiMassSharpSpacelikeCenteredAtom a sigma alpha u n‖) := by
  apply Summable.of_nonneg_of_le (fun n => norm_nonneg _)
    (fun n => norm_xiMassSharpSpacelikeCenteredAtom_le
      ha hsigma hsharp hu n)
  exact summable_xiMassSharpSpacelikeCenteredMajorant ha hsharp

/-- Exact spacelike part of the rounded finite centered-atom cone. -/
noncomputable def xiMassCriticalCenteredSharpSpacelikeConeSum
    (a sigma d alpha u : ℝ) : ℂ :=
  let H := d * u / (d - 1 / 2)
  let M := ⌊Real.exp H⌋₊
  ∑ k ∈ Finset.range (M - 1),
    xiMassSharpSpacelikeCenteredAtom a sigma alpha u k

/-- Complementary finite timelike-plus-glancing layer. -/
noncomputable def xiMassCriticalCenteredTimelikeGlancingConeSum
    (a sigma d alpha u : ℝ) : ℂ :=
  let H := d * u / (d - 1 / 2)
  let M := ⌊Real.exp H⌋₊
  ∑ k ∈ Finset.range (M - 1),
    if Real.log ((k : ℝ) + 2) < alpha * u then
      ((ArithmeticFunction.vonMangoldt (k + 2) - 1 : ℝ) : ℂ) *
        xiMassCriticalDampedFourierProfile a sigma u
          (Real.log ((k : ℝ) + 2))
    else 0

/-- Exact partition: no atom is dropped and no boundary term is introduced. -/
theorem xiMassCriticalCenteredAtomConeSum_eq_sharpSpacelike_add_timelikeGlancing
    (a sigma d alpha u : ℝ) :
    xiMassCriticalCenteredAtomConeSum a sigma d u =
      xiMassCriticalCenteredSharpSpacelikeConeSum a sigma d alpha u +
        xiMassCriticalCenteredTimelikeGlancingConeSum a sigma d alpha u := by
  simp only [xiMassCriticalCenteredAtomConeSum,
    xiMassCriticalCenteredSharpSpacelikeConeSum,
    xiMassCriticalCenteredTimelikeGlancingConeSum,
    xiMassSharpSpacelikeCenteredAtom, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  by_cases hcone : alpha * u ≤ Real.log ((k : ℝ) + 2)
  · simp only [if_pos hcone, if_neg (not_lt_of_ge hcone), add_zero]
  · have htimelike : Real.log ((k : ℝ) + 2) < alpha * u := lt_of_not_ge hcone
    simp only [if_neg hcone, if_pos htimelike, zero_add]

/-- **Sharp spacelike cone closure.**  Every finite cutoff of the exact spacelike component has one
bound independent of `u`, `d`, and cutoff. -/
theorem norm_xiMassCriticalCenteredSharpSpacelikeConeSum_le_tsum
    {a sigma d alpha u : ℝ} (ha : 1 / 2 < a) (hsigma : 0 < sigma)
    (hsharp : xiMassSpacelikeSharpSlope a < alpha) (hu : 0 ≤ u) :
    ‖xiMassCriticalCenteredSharpSpacelikeConeSum a sigma d alpha u‖ ≤
      ∑' n : ℕ, xiMassSharpSpacelikeCenteredMajorant a alpha n := by
  let H := d * u / (d - 1 / 2)
  let M := ⌊Real.exp H⌋₊
  let S := Finset.range (M - 1)
  have hmajor := summable_xiMassSharpSpacelikeCenteredMajorant ha hsharp
  rw [xiMassCriticalCenteredSharpSpacelikeConeSum]
  change ‖∑ k ∈ S, xiMassSharpSpacelikeCenteredAtom a sigma alpha u k‖ ≤ _
  calc
    ‖∑ k ∈ S, xiMassSharpSpacelikeCenteredAtom a sigma alpha u k‖ ≤
        ∑ k ∈ S, xiMassSharpSpacelikeCenteredMajorant a alpha k :=
      norm_sum_le_of_le S (fun k hk =>
        norm_xiMassSharpSpacelikeCenteredAtom_le ha hsigma hsharp hu k)
    _ ≤ ∑' n : ℕ, xiMassSharpSpacelikeCenteredMajorant a alpha n :=
      hmajor.sum_le_tsum S (fun n hn => by
        have ha0 : 0 < a := lt_trans (by norm_num) ha
        have halpha : 1 < alpha := by
          exact (one_lt_xiMassSpacelikeSharpSlope ha).trans hsharp
        exact xiMassSharpSpacelikeCenteredMajorant_nonneg ha0 halpha n)

end

end RHTower
