import GaloisForLFunctions.RHTower.Deninger.DeningerExponentExceptionalTameGreenBridge
import GaloisForLFunctions.RHTower.Deninger.DeningerCenteredFlowCountercharacterRelativeCurvatureNoGo

/-!
# Completed-exponent line-reflection blow-up transport

The completed exponent source

`EΞ(z,s) = ξ(s) / ξ(zs)`

has a forced anti-birational lift of critical-line reflection.  On the open
strip source chart it is

`(z,s) ↦ (conj ((1-zs)/(1-s)), 1-conj s)`.

It is an involution, conjugates `EΞ`, and induces on the exceptional divisor
over an Xi point `rho` the anti-linear map

`w ↦ conj(w) * (1-conj(rho))/conj(rho)`.

This map carries the marked pole `-rho` exactly to the marked pole over
`1-conj(rho)` and conjugates the complete multiplicity-exact exceptional
profile.  Thus the singular reflected transport exists before divisor
specialization; no critical-line premise is used.

The construction is covariance, not selection.  It exchanges the two
Gamma-six edge orientations and negates their physical readout, but it does
not assert simultaneous projective-trace admission or fixed-reader cyclicity.
-/

open Complex Filter Topology

namespace RHTower

noncomputable section

/-! ## Anti-birational lift on the completed exponent source -/

/-- Completed exponent deformation `ξ(s)/ξ(zs)`. -/
def deningerCompletedExponentDeformationActivation (z s : ℂ) : ℂ :=
  xi s / xi (z * s)

/-- Open-strip source points for the completed exponent deformation.  Using
the strip as the domain makes the birational reflection total and retains
every nontrivial Xi divisor point. -/
abbrev DeningerCompletedExponentOpenStripPoint :=
  {x : ℂ × ℂ // x.2.re ∈ Set.Ioo (0 : ℝ) 1}

/-- Forced lift of `s ↦ 1-conj(s)` through the product coordinate `zs`. -/
def deningerCompletedExponentLineReflection
    (x : DeningerCompletedExponentOpenStripPoint) :
    DeningerCompletedExponentOpenStripPoint :=
  ⟨((starRingEnd ℂ) ((1 - x.1.1 * x.1.2) / (1 - x.1.2)),
      1 - (starRingEnd ℂ) x.1.2), by
    constructor
    · simpa using sub_pos.mpr x.2.2
    · simpa using x.2.1⟩

/-- The base coordinate of the lifted reflection is the critical-line
reflection. -/
@[simp]
theorem deningerCompletedExponentLineReflection_snd
    (x : DeningerCompletedExponentOpenStripPoint) :
    (deningerCompletedExponentLineReflection x).1.2 =
      1 - (starRingEnd ℂ) x.1.2 := rfl

/-- The reflected product coordinate is exactly `1-conj(zs)`. -/
theorem deningerCompletedExponentLineReflection_mul
    (x : DeningerCompletedExponentOpenStripPoint) :
    (deningerCompletedExponentLineReflection x).1.1 *
        (deningerCompletedExponentLineReflection x).1.2 =
      1 - (starRingEnd ℂ) (x.1.1 * x.1.2) := by
  have hs : x.1.2 ≠ 1 := by
    intro hs
    have := x.2.2
    rw [hs] at this
    norm_num at this
  have hden : 1 - (starRingEnd ℂ) x.1.2 ≠ 0 := by
    intro h
    have hstar : (starRingEnd ℂ) x.1.2 = 1 := (sub_eq_zero.mp h).symm
    have hsOne : x.1.2 = 1 := by
      have := congrArg (starRingEnd ℂ) hstar
      simpa using this
    exact hs hsOne
  rw [deningerCompletedExponentLineReflection]
  dsimp
  simp only [map_div₀, map_sub, map_one, map_mul]
  field_simp [hden]

/-- **Completed exponent reflection covariance.**  The lifted source
involution conjugates the literal completed exponent deformation. -/
theorem deningerCompletedExponentDeformationActivation_lineReflection
    (x : DeningerCompletedExponentOpenStripPoint) :
    deningerCompletedExponentDeformationActivation
        (deningerCompletedExponentLineReflection x).1.1
        (deningerCompletedExponentLineReflection x).1.2 =
      (starRingEnd ℂ)
        (deningerCompletedExponentDeformationActivation x.1.1 x.1.2) := by
  rw [deningerCompletedExponentDeformationActivation,
    deningerCompletedExponentLineReflection_mul,
    deningerCompletedExponentLineReflection_snd,
    xi_one_sub, xi_one_sub, xi_conj, xi_conj,
    deningerCompletedExponentDeformationActivation, map_div₀]

/-- The lifted line reflection is an actual involution on the open-strip
two-variable source, not merely a divisor relabeling. -/
theorem deningerCompletedExponentLineReflection_involutive :
    Function.Involutive deningerCompletedExponentLineReflection := by
  intro x
  apply Subtype.ext
  apply Prod.ext
  · have hs0 : x.1.2 ≠ 0 := by
      intro hs
      have := x.2.1
      rw [hs] at this
      norm_num at this
    have hmulStar :
        (starRingEnd ℂ)
              (deningerCompletedExponentLineReflection x).1.1 *
            (1 - x.1.2) =
          1 - x.1.1 * x.1.2 := by
      simpa using congrArg (starRingEnd ℂ)
        (deningerCompletedExponentLineReflection_mul x)
    rw [deningerCompletedExponentLineReflection]
    dsimp
    simp only [map_div₀, map_sub, map_one, map_mul]
    field_simp [hs0]
    rw [starRingEnd_self_apply]
    rw [hmulStar]
    ring
  · simp [deningerCompletedExponentLineReflection]

/-- The completed exponent line reflection as an equivalence. -/
def deningerCompletedExponentLineReflectionEquiv :
    DeningerCompletedExponentOpenStripPoint ≃
      DeningerCompletedExponentOpenStripPoint where
  toFun := deningerCompletedExponentLineReflection
  invFun := deningerCompletedExponentLineReflection
  left_inv := deningerCompletedExponentLineReflection_involutive
  right_inv := deningerCompletedExponentLineReflection_involutive

/-! ## Forced transport on the exceptional divisor -/

/-- Nontrivial Xi divisor points do not meet zero. -/
theorem xiDivisorSupport_ne_zero (rho : XiDivisorSupport) :
    (rho : ℂ) ≠ 0 := by
  intro h
  have hstrip := (xi_divisor_support_re_mem_open_unit rho).1
  rw [h] at hstrip
  norm_num at hstrip

/-- The line-reflected Xi divisor point does not meet zero. -/
theorem xiDivisorSupport_lineReflection_ne_zero
    (rho : XiDivisorSupport) :
    ((xiZeroLineConjEquiv rho : XiDivisorSupport) : ℂ) ≠ 0 :=
  xiDivisorSupport_ne_zero (xiZeroLineConjEquiv rho)

/-- Exceptional-direction transport induced by the anti-birational source
reflection. -/
def deningerExponentExceptionalLineReflectionDirection
    (rho : XiDivisorSupport) (w : ℂ) : ℂ :=
  (starRingEnd ℂ) w *
    (((xiZeroLineConjEquiv rho : XiDivisorSupport) : ℂ) /
      (starRingEnd ℂ) (rho : ℂ))

/-- The divisor-face direction is fixed. -/
@[simp]
theorem deningerExponentExceptionalLineReflectionDirection_zero
    (rho : XiDivisorSupport) :
    deningerExponentExceptionalLineReflectionDirection rho 0 = 0 := by
  simp [deningerExponentExceptionalLineReflectionDirection]

/-- **Marked-pole transport.**  The forced exceptional map carries the
source pole to the marked pole over the critical-line-reflected divisor. -/
theorem deningerExponentExceptionalLineReflectionDirection_sourcePole
    (rho : XiDivisorSupport) :
    deningerExponentExceptionalLineReflectionDirection rho (-(rho : ℂ)) =
      -((xiZeroLineConjEquiv rho : XiDivisorSupport) : ℂ) := by
  rw [deningerExponentExceptionalLineReflectionDirection]
  have hrhoStar : (starRingEnd ℂ) (rho : ℂ) ≠ 0 := by
    exact (map_ne_zero (starRingEnd ℂ)).2 (xiDivisorSupport_ne_zero rho)
  simp only [map_neg]
  field_simp [hrhoStar]

/-- **Forced exceptional coefficient.**  There is exactly one anti-linear
degree-one direction map `w ↦ a * conj(w)` carrying the source marked pole
to its line-reflected marked pole, and its coefficient is the one induced by
the completed exponent source involution. -/
theorem existsUnique_deningerExponentExceptionalLineReflectionCoefficient
    (rho : XiDivisorSupport) :
    ∃! a : ℂ,
      a * (starRingEnd ℂ) (-(rho : ℂ)) =
        -((xiZeroLineConjEquiv rho : XiDivisorSupport) : ℂ) := by
  let sigma : ℂ :=
    ((xiZeroLineConjEquiv rho : XiDivisorSupport) : ℂ)
  have hrhoStar : (starRingEnd ℂ) (rho : ℂ) ≠ 0 :=
    (map_ne_zero (starRingEnd ℂ)).2 (xiDivisorSupport_ne_zero rho)
  refine ⟨sigma / (starRingEnd ℂ) (rho : ℂ), ?_, ?_⟩
  · dsimp [sigma]
    simp only [map_neg]
    field_simp [hrhoStar]
  · intro a ha
    dsimp [sigma] at ha ⊢
    simp only [map_neg] at ha
    apply (mul_right_cancel₀ hrhoStar)
    field_simp [hrhoStar] at ha ⊢
    exact neg_inj.mp ha

/-- Critical-line reflection preserves the exact exceptional multiplicity. -/
theorem deningerExponentExceptionalOrder_lineReflection
    (rho : XiDivisorSupport) :
    DeningerExponentExceptionalOrder (xiZeroLineConjEquiv rho) =
      DeningerExponentExceptionalOrder rho := by
  rw [deningerExponentExceptionalOrder_eq_xiSupportMultiplicity,
    deningerExponentExceptionalOrder_eq_xiSupportMultiplicity,
    xiSupportMultiplicity_eq_analyticOrderAt_toNat,
    xiSupportMultiplicity_eq_analyticOrderAt_toNat,
    xiZeroLineConjEquiv_apply, xi_orderAt_one_sub, xi_orderAt_conj]

/-- Exact affine denominator identity behind exceptional-profile
equivariance. -/
theorem deningerExponentExceptionalLineReflectionDirection_add
    (rho : XiDivisorSupport) (w : ℂ) :
    deningerExponentExceptionalLineReflectionDirection rho w +
        ((xiZeroLineConjEquiv rho : XiDivisorSupport) : ℂ) =
      ((xiZeroLineConjEquiv rho : XiDivisorSupport) : ℂ) *
        ((starRingEnd ℂ) w + (starRingEnd ℂ) (rho : ℂ)) /
          (starRingEnd ℂ) (rho : ℂ) := by
  rw [deningerExponentExceptionalLineReflectionDirection]
  have hrhoStar : (starRingEnd ℂ) (rho : ℂ) ≠ 0 := by
    exact (map_ne_zero (starRingEnd ℂ)).2 (xiDivisorSupport_ne_zero rho)
  field_simp [hrhoStar]

/-- **Multiplicity-exact exceptional equivariance.**  The full exceptional
profile, not only its pole support, is conjugated by the forced singular
transport. -/
theorem deningerExponentExceptionalRawProfile_lineReflection
    (rho : XiDivisorSupport)
    (w : DeningerExponentExceptionalRegularDirection rho) :
    deningerExponentExceptionalRawProfile (xiZeroLineConjEquiv rho)
        (deningerExponentExceptionalLineReflectionDirection rho w.1) =
      (starRingEnd ℂ) (deningerExponentExceptionalRawProfile rho w.1) := by
  have hrhoStar : (starRingEnd ℂ) (rho : ℂ) ≠ 0 := by
    exact (map_ne_zero (starRingEnd ℂ)).2 (xiDivisorSupport_ne_zero rho)
  have hsigma :
      ((xiZeroLineConjEquiv rho : XiDivisorSupport) : ℂ) ≠ 0 :=
    xiDivisorSupport_lineReflection_ne_zero rho
  have hwStar : (starRingEnd ℂ) w.1 ≠ 0 :=
    (map_ne_zero (starRingEnd ℂ)).2 w.2.1
  have hwAddStar :
      (starRingEnd ℂ) w.1 + (starRingEnd ℂ) (rho : ℂ) ≠ 0 := by
    rw [← map_add]
    exact (map_ne_zero (starRingEnd ℂ)).2 w.2.2
  rw [deningerExponentExceptionalRawProfile,
    deningerExponentExceptionalRawProfile,
    deningerExponentExceptionalOrder_lineReflection,
    map_pow, map_div₀, map_add]
  congr 1
  rw [deningerExponentExceptionalLineReflectionDirection_add,
    deningerExponentExceptionalLineReflectionDirection]
  field_simp [hrhoStar, hsigma, hwStar, hwAddStar]

/-- The exceptional direction transport is involutive over the
critical-line-reflected divisor. -/
theorem deningerExponentExceptionalLineReflectionDirection_involutive
    (rho : XiDivisorSupport) (w : ℂ) :
    deningerExponentExceptionalLineReflectionDirection
        (xiZeroLineConjEquiv rho)
        (deningerExponentExceptionalLineReflectionDirection rho w) = w := by
  have hrho : (rho : ℂ) ≠ 0 := xiDivisorSupport_ne_zero rho
  have hsigma :
      ((xiZeroLineConjEquiv rho : XiDivisorSupport) : ℂ) ≠ 0 :=
    xiDivisorSupport_lineReflection_ne_zero rho
  have hstarSigma :
      (starRingEnd ℂ)
          ((xiZeroLineConjEquiv rho : XiDivisorSupport) : ℂ) ≠ 0 :=
    (map_ne_zero (starRingEnd ℂ)).2 hsigma
  rw [deningerExponentExceptionalLineReflectionDirection,
    deningerExponentExceptionalLineReflectionDirection,
    xiZeroLineConjEquiv_involutive]
  simp only [map_mul, map_div₀]
  field_simp [hrho, hsigma, hstarSigma]
  simpa using (mul_comm w (rho : ℂ))

/-! ## Physical Gamma-six readout -/

/-- The marked tame/Gamma-six readout is reflection-odd under the explicit
source involution. -/
theorem deningerGammaSixExceptionalTameReader_lineReflection
    (rho : XiDivisorSupport) (m : ℕ) :
    deningerGammaSixExceptionalTameReader m
        ((xiZeroLineConjEquiv rho : XiDivisorSupport) : ℂ) =
      -deningerGammaSixExceptionalTameReader m (rho : ℂ) := by
  rw [xiZeroLineConjEquiv_apply,
    deningerGammaSixExceptionalTameReader_eq_mateCurvature,
    deningerGammaSixExceptionalTameReader_eq_mateCurvature,
    deningerTensorSquareRadialMateCurvature_eq_sinh,
    deningerTensorSquareRadialMateCurvature_eq_sinh]
  · have hre : (1 - (starRingEnd ℂ) (rho : ℂ)).re = 1 - (rho : ℂ).re := by
      simp
    rw [hre]
    have harg :
        (2 * (1 - (rho : ℂ).re) - 1) *
            Real.log (((6 ^ m : ℕ) : ℝ)) =
          -((2 * (rho : ℂ).re - 1) *
            Real.log (((6 ^ m : ℕ) : ℝ))) := by
      ring
    rw [harg, Real.sinh_neg]
    ring
  · positivity
  · positivity

end

end RHTower
