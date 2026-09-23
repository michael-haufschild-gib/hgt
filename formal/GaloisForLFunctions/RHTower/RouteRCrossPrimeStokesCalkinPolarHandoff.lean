import GaloisForLFunctions.RHTower.RouteRDeningerBVGreenPositiveUnitComparison
import GaloisForLFunctions.RHTower.RouteRDegreeSixBVGreenNeutralFinitePart
import GaloisForLFunctions.RHTower.XiPrimeTwoThreeSeamRigidity
import GaloisForLFunctions.RHTower.XiPrimeSeamCofinalAnchoredEssentialNormDecay

/-!
# Route R's explicit cross-prime Stokes/Calkin polar handoff

The ordered forward-`p` and reflected-`q` Stokes inverses have a canonical regularized curvature.
Its reflection-odd part is a positive unit times the hyperbolic horizontal carrier.  At `(2,3)`
its square is exactly the degree-six BV--Green modular square.  Using the literal finite Euler
source and fixed Sonin compression then produces one explicit commutator whose Calkin class
vanishes exactly at neutral horizontal grade.

This constructs and identifies the external polar receiver left abstract by the pre-polar no-go.
It does not assert compactness of that commutator from source data: that independent compactness
law remains the Route R producer.
-/

open Complex

namespace RHTower

noncomputable section

/-- Hyperbolic sinc is even, including its removable central value. -/
@[simp] theorem routeRDeningerHyperbolicSinc_neg (x : ℝ) :
    routeRDeningerHyperbolicSinc (-x) = routeRDeningerHyperbolicSinc x := by
  by_cases hx : x = 0
  · simp [hx]
  · rw [routeRDeningerHyperbolicSinc, routeRDeningerHyperbolicSinc,
      if_neg (neg_ne_zero.mpr hx), if_neg hx, Real.sinh_neg, neg_div_neg_eq]

/-- Positive regularized ratio of reflected and forward directional Stokes defects. -/
def routeRCrossPrimeStokesRatio (p q : ℕ) (a : ℝ) : ℝ :=
  ((Real.log q / Real.log p) *
      routeRDeningerHyperbolicSinc (a * Real.log q / 2)) /
    routeRDeningerHyperbolicSinc (a * Real.log p / 2)

theorem routeRCrossPrimeStokesRatio_pos
    {p q : ℕ} (hp : 1 < p) (hq : 1 < q) (a : ℝ) :
    0 < routeRCrossPrimeStokesRatio p q a := by
  exact div_pos
    (mul_pos
      (div_pos (Real.log_pos (by exact_mod_cast hq))
        (Real.log_pos (by exact_mod_cast hp)))
      (routeRDeningerHyperbolicSinc_pos _))
    (routeRDeningerHyperbolicSinc_pos _)

@[simp] theorem routeRCrossPrimeStokesRatio_neg
    (p q : ℕ) (a : ℝ) :
    routeRCrossPrimeStokesRatio p q (-a) =
      routeRCrossPrimeStokesRatio p q a := by
  rw [routeRCrossPrimeStokesRatio, routeRCrossPrimeStokesRatio]
  have hp : -a * Real.log p / 2 = -(a * Real.log p / 2) := by ring
  have hq : -a * Real.log q / 2 = -(a * Real.log q / 2) := by ring
  rw [hp, hq, routeRDeningerHyperbolicSinc_neg,
    routeRDeningerHyperbolicSinc_neg]

/-- Positive gauge multiplying the reflection-odd cross-prime curvature. -/
def routeRCrossPrimeStokesGauge (p q : ℕ) (a : ℝ) : ℝ :=
  routeRCrossPrimeStokesRatio p q a +
    (routeRCrossPrimeStokesRatio p q a)⁻¹

theorem routeRCrossPrimeStokesGauge_pos
    {p q : ℕ} (hp : 1 < p) (hq : 1 < q) (a : ℝ) :
    0 < routeRCrossPrimeStokesGauge p q a := by
  exact add_pos (routeRCrossPrimeStokesRatio_pos hp hq a)
    (inv_pos.mpr (routeRCrossPrimeStokesRatio_pos hp hq a))

/-- Hyperbolic phase carried jointly by the ordered prime pair. -/
def routeRCrossPrimeStokesPhase (p q : ℕ) (a : ℝ) : ℝ :=
  a * (Real.log p + Real.log q) / 2

@[simp] theorem routeRCrossPrimeStokesPhase_neg (p q : ℕ) (a : ℝ) :
    routeRCrossPrimeStokesPhase p q (-a) =
      -routeRCrossPrimeStokesPhase p q a := by
  simp [routeRCrossPrimeStokesPhase]
  ring

/-- Regularized ordered Stokes curvature, defined on the central fibre without division by a
vanishing character defect. -/
def routeRCrossPrimeStokesCurvature (p q : ℕ) (a : ℝ) : ℝ :=
  -Real.exp (routeRCrossPrimeStokesPhase p q a) *
      routeRCrossPrimeStokesRatio p q a +
    Real.exp (-routeRCrossPrimeStokesPhase p q a) *
      (routeRCrossPrimeStokesRatio p q a)⁻¹

/-- Reflection-odd part of the regularized curvature. -/
def routeRCrossPrimeStokesOddCurvature (p q : ℕ) (a : ℝ) : ℝ :=
  routeRCrossPrimeStokesCurvature p q a -
    routeRCrossPrimeStokesCurvature p q (-a)

private theorem odd_exp_pair_identity (E F r s : ℝ) :
    (-E * r + F * s) - (-F * r + E * s) =
      -2 * ((E - F) / 2) * (r + s) := by
  ring

/-- Exact cross-prime polar normal form. -/
theorem routeRCrossPrimeStokesOddCurvature_eq
    (p q : ℕ) (a : ℝ) :
    routeRCrossPrimeStokesOddCurvature p q a =
      -2 * Real.sinh (routeRCrossPrimeStokesPhase p q a) *
        routeRCrossPrimeStokesGauge p q a := by
  rw [routeRCrossPrimeStokesOddCurvature,
    routeRCrossPrimeStokesCurvature, routeRCrossPrimeStokesCurvature,
    routeRCrossPrimeStokesPhase_neg, routeRCrossPrimeStokesRatio_neg,
    neg_neg, routeRCrossPrimeStokesGauge]
  rw [show Real.sinh (routeRCrossPrimeStokesPhase p q a) =
      (Real.exp (routeRCrossPrimeStokesPhase p q a) -
        Real.exp (-routeRCrossPrimeStokesPhase p q a)) / 2 from
    Real.sinh_eq _]
  exact odd_exp_pair_identity
    (Real.exp (routeRCrossPrimeStokesPhase p q a))
    (Real.exp (-routeRCrossPrimeStokesPhase p q a))
    (routeRCrossPrimeStokesRatio p q a)
    (routeRCrossPrimeStokesRatio p q a)⁻¹

theorem routeRCrossPrimeStokesPhase_eq_log_mul
    {p q : ℕ} (hp : 0 < p) (hq : 0 < q) (a : ℝ) :
    routeRCrossPrimeStokesPhase p q a = a * Real.log (p * q) / 2 := by
  rw [routeRCrossPrimeStokesPhase,
    Real.log_mul (by exact_mod_cast hp.ne') (by exact_mod_cast hq.ne')]

/-- The odd curvature has no accidental zero: its radical is exactly neutral grade. -/
theorem routeRCrossPrimeStokesOddCurvature_eq_zero_iff
    {p q : ℕ} (hp : 1 < p) (hq : 1 < q) (a : ℝ) :
    routeRCrossPrimeStokesOddCurvature p q a = 0 ↔ a = 0 := by
  rw [routeRCrossPrimeStokesOddCurvature_eq, mul_eq_zero]
  have hg : routeRCrossPrimeStokesGauge p q a ≠ 0 :=
    (routeRCrossPrimeStokesGauge_pos hp hq a).ne'
  rw [or_iff_left hg]
  rw [mul_eq_zero]
  norm_num
  unfold routeRCrossPrimeStokesPhase
  have hlog : 0 < Real.log p + Real.log q :=
    add_pos (Real.log_pos (by exact_mod_cast hp))
      (Real.log_pos (by exact_mod_cast hq))
  constructor
  · intro h
    rcases div_eq_zero_iff.mp h with hnum | htwo
    · rcases mul_eq_zero.mp hnum with ha | hlogzero
      · exact ha
      · exact False.elim (hlog.ne' hlogzero)
    · norm_num at htwo
  · rintro rfl
    simp

/-- The reflected degree-six BV--Green modular square. -/
def routeRDegreeSixBVGreenModularSquare (a : ℝ) : ℝ :=
  -deningerOrdinaryIntegerBVGreenModularAnomaly 6 a *
    deningerOrdinaryIntegerBVGreenModularAnomaly 6 (-a)

theorem routeRDegreeSixBVGreenModularSquare_eq (a : ℝ) :
    routeRDegreeSixBVGreenModularSquare a =
      4 * (6 : ℝ)⁻¹ ^ (2 : ℕ) * Real.sinh (a * Real.log 6 / 2) ^ (2 : ℕ) := by
  have hpos : 0 < (6 : ℝ) := by norm_num
  have hunit : Real.exp (-(a * Real.log 6 / 2)) *
      Real.exp (a * Real.log 6 / 2) = 1 := by
    rw [← Real.exp_add]
    simp
  have hminus : 1 - Real.exp (-a * Real.log 6) =
      2 * Real.exp (-(a * Real.log 6 / 2)) *
        Real.sinh (a * Real.log 6 / 2) := by
    rw [Real.sinh_eq]
    have hdouble : Real.exp (-a * Real.log 6) =
        Real.exp (-(a * Real.log 6 / 2)) *
          Real.exp (-(a * Real.log 6 / 2)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [hdouble]
    field_simp
    nlinarith
  have hplus : 1 - Real.exp (-(-a) * Real.log 6) =
      -2 * Real.exp (a * Real.log 6 / 2) *
        Real.sinh (a * Real.log 6 / 2) := by
    rw [show -(-a) * Real.log 6 = a * Real.log 6 by ring, Real.sinh_eq]
    have hdouble : Real.exp (a * Real.log 6) =
        Real.exp (a * Real.log 6 / 2) *
          Real.exp (a * Real.log 6 / 2) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [hdouble]
    field_simp
    nlinarith
  rw [routeRDegreeSixBVGreenModularSquare,
    deningerOrdinaryIntegerBVGreenModularAnomaly,
    deningerOrdinaryIntegerBVGreenModularAnomaly]
  norm_num only [Nat.cast_ofNat]
  rw [hminus, hplus]
  nlinarith

/-- At `(2,3)`, cross-prime Stokes curvature is exactly a positive-gauge realization of the
degree-six physical modular square. -/
theorem routeRTwoThreeStokesOddCurvature_sq_eq_modularSquare (a : ℝ) :
    routeRCrossPrimeStokesOddCurvature 2 3 a ^ (2 : ℕ) =
      36 * routeRCrossPrimeStokesGauge 2 3 a ^ (2 : ℕ) *
        routeRDegreeSixBVGreenModularSquare a := by
  rw [routeRCrossPrimeStokesOddCurvature_eq,
    routeRCrossPrimeStokesPhase_eq_log_mul (by norm_num) (by norm_num),
    routeRDegreeSixBVGreenModularSquare_eq]
  norm_num
  ring

/-- The two oriented Stokes curvatures used as coefficients of the literal Euler packet. -/
def routeRTwoThreeStokesCurvaturePacket (a : ℝ) : Fin 2 → ℂ :=
  ![(routeRCrossPrimeStokesCurvature 2 3 a : ℂ),
    (routeRCrossPrimeStokesCurvature 2 3 (-a) : ℂ)]

/-- Fixed Sonin-compressed commutator of the literal `(2,3)` Euler source with the universal
Euler source. -/
def routeRTwoThreeStokesSoninCommutator (A a : ℝ) :
    ArchimedeanWeightedL2 →L[ℂ] ArchimedeanWeightedL2 :=
  finiteArchimedeanEulerCompression A
      (fun i ↦ (primeTwoThreePacket i : ℝ))
      (routeRTwoThreeStokesCurvaturePacket a) *
    finiteArchimedeanEulerCompression A
      (fun i ↦ (primeTwoThreePacket i : ℝ)) (fun _ ↦ 1) -
  finiteArchimedeanEulerCompression A
      (fun i ↦ (primeTwoThreePacket i : ℝ)) (fun _ ↦ 1) *
    finiteArchimedeanEulerCompression A
      (fun i ↦ (primeTwoThreePacket i : ℝ))
      (routeRTwoThreeStokesCurvaturePacket a)

/-- The source commutator is the negative fixed Sonin orientation Gram. -/
theorem routeRTwoThreeStokesSoninCommutator_eq_neg_orientationGram
    (A a : ℝ) :
    routeRTwoThreeStokesSoninCommutator A a =
      -finiteArchimedeanEulerOrientationGram A
        (fun i ↦ (primeTwoThreePacket i : ℝ))
        (routeRTwoThreeStokesCurvaturePacket a) := by
  have h := finiteArchimedeanEulerOrientationGram_eq_neg_compression_commutator
    A (fun i ↦ (primeTwoThreePacket i : ℝ))
      (fun i ↦ by
        exact_mod_cast (primeTwoThreePacket_prime i).one_lt)
      (routeRTwoThreeStokesCurvaturePacket a)
  have hneg := congrArg Neg.neg h
  simpa [routeRTwoThreeStokesSoninCommutator] using hneg.symm

/-- **Explicit Calkin classification.** The fixed compressed cross-prime Stokes commutator is
compact exactly at neutral grade. -/
theorem routeRTwoThreeStokesSoninCommutator_isCompactOperator_iff
    {A : ℝ} (hA : 0 < A) (a : ℝ) :
    IsCompactOperator (routeRTwoThreeStokesSoninCommutator A a) ↔ a = 0 := by
  rw [routeRTwoThreeStokesSoninCommutator,
    finitePrimeArchimedeanEulerCompression_commutator_isCompactOperator_iff
    A hA primeTwoThreePacket primeTwoThreePacket_prime
      primeTwoThreePacket_injective (routeRTwoThreeStokesCurvaturePacket a)]
  constructor
  · intro hconstant
    apply (routeRCrossPrimeStokesOddCurvature_eq_zero_iff
      (p := 2) (q := 3) (by norm_num) (by norm_num) a).1
    have h01 := hconstant (0 : Fin 2) (1 : Fin 2)
    exact sub_eq_zero.mpr (by
      simpa [routeRTwoThreeStokesCurvaturePacket] using congrArg Complex.re h01)
  · rintro rfl i j
    fin_cases i <;> fin_cases j <;>
      simp [routeRTwoThreeStokesCurvaturePacket]

/-- Quantitative Calkin landing: every compact perturbation leaves at least the exact normalized
reflection-odd Stokes curvature. -/
theorem abs_routeRTwoThreeStokesOddCurvature_div_sqrt_six_le_essentialNorm
    {A : ℝ} (hA : 0 < A) (a : ℝ) :
    |routeRCrossPrimeStokesOddCurvature 2 3 a| / Real.sqrt 6 ≤
      essentialNorm (routeRTwoThreeStokesSoninCommutator A a) := by
  have hlower := norm_orientationDifference_div_sqrt_le_essentialNorm
    hA primeTwoThreePacket primeTwoThreePacket_prime primeTwoThreePacket_injective
      (routeRTwoThreeStokesCurvaturePacket a) (0 : Fin 2) (1 : Fin 2) (by decide)
  rw [routeRTwoThreeStokesSoninCommutator_eq_neg_orientationGram,
    essentialNorm_neg]
  have hsqrt : Real.sqrt (3 : ℝ) * Real.sqrt (2 : ℝ) = Real.sqrt 6 := by
    rw [← Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 3)]
    norm_num
  have hdiff :
      ‖(routeRTwoThreeStokesCurvaturePacket a (1 : Fin 2) -
          routeRTwoThreeStokesCurvaturePacket a (0 : Fin 2))‖ =
        |routeRCrossPrimeStokesOddCurvature 2 3 a| := by
    simp only [routeRTwoThreeStokesCurvaturePacket, Matrix.cons_val_one,
      Matrix.cons_val_zero, routeRCrossPrimeStokesOddCurvature]
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm]
  rw [hdiff, show Real.sqrt (primeTwoThreePacket (1 : Fin 2)) *
      Real.sqrt (primeTwoThreePacket (0 : Fin 2)) = Real.sqrt 6 by
        simpa [primeTwoThreePacket] using hsqrt] at hlower
  exact hlower

/-- Compactness of this single explicit source-selected commutator on every Xi fibre is an
unconditional RH endpoint.  The premise is not asserted here. -/
theorem riemannHypothesis_of_routeRTwoThreeStokesSoninCommutator_compact
    {A : ℝ} (hA : 0 < A)
    (hcompact : ∀ rho : XiDivisorSupport,
      IsCompactOperator
        (routeRTwoThreeStokesSoninCommutator A
          (primeDepthBVWoldXiCenteredRate rho))) :
    RiemannHypothesis := by
  rw [riemannHypothesis_iff_xi_zero_re_eq_half]
  intro z hz
  let rho : XiDivisorSupport := ⟨z, mem_xi_divisor_support_of_eq_zero hz⟩
  have hrate :=
    (routeRTwoThreeStokesSoninCommutator_isCompactOperator_iff hA
      (primeDepthBVWoldXiCenteredRate rho)).1 (hcompact rho)
  exact (primeDepthBVWoldXiCenteredRate_eq_zero_iff rho).1 hrate

/-- Exact endpoint calibration: global compactness of the explicit cross-prime commutator is
equivalent to RH. -/
theorem routeRTwoThreeStokesSoninCommutator_globalCompact_iff_riemannHypothesis
    {A : ℝ} (hA : 0 < A) :
    (∀ rho : XiDivisorSupport,
      IsCompactOperator
        (routeRTwoThreeStokesSoninCommutator A
          (primeDepthBVWoldXiCenteredRate rho))) ↔
      RiemannHypothesis := by
  constructor
  · exact riemannHypothesis_of_routeRTwoThreeStokesSoninCommutator_compact hA
  · intro hRH rho
    apply (routeRTwoThreeStokesSoninCommutator_isCompactOperator_iff hA _).2
    exact (primeDepthBVWoldXiCenteredRate_eq_zero_iff rho).2
      (xi_divisor_support_re_eq_half_of_rh hRH rho)

end

end RHTower
