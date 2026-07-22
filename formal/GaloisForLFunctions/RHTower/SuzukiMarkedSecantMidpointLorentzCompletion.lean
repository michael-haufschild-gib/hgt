import GaloisForLFunctions.RHTower.SuzukiGlobalLocalCompoundBezoutianWeld

/-!
# Midpoint Lorentz completion of Suzuki's marked secant

Write the two shifts as `alpha = m - d`, `beta = m + d`.  The complete marked affine-secant
pair then has exact midpoint form

`Q = U*V - d^2*x*y + m*F`, `P = V^2 - d^2*y^2`,

where `U = X+c-m*x`, `V = Y-m*y`, and `F = (X+c)*y-x*Y`.  Thus its symmetric coefficient form
has one Lorentzian debt, exactly `d^2`; adding `kappa` in the rooted diagonal is nonnegative for
all real source coordinates iff `d^2 <= kappa`.  At equality it collapses to one square.

The global-local compound numerator splits into three forced channels: midpoint determinant,
halfgap-squared rooted debt, and centered Pluecker flux.  On an actual two-resolvent orbit, the
same `d^2` appears inside the relative Volterra phase observation as a literal Neumann midpoint
source.  This identifies the exact source term that a prime--Gamma Green identity must pay.

No RH premise, positivity hypothesis, Xi-divisor data, estimate, or computation is used.
-/

namespace RHTower

noncomputable section

/-! ## Exact marked midpoint pair -/

/-- **Midpoint Lorentz--Pluecker decomposition.**  The marked numerator is one split bilinear
product, one halfgap-squared rooted debt, and one centered alternating flux. -/
theorem suzukiProjectiveAffineSecantTensor_midpoint_halfGap
    {F : Type*} [CommRing F] (m d x X y Y c : F) :
    suzukiProjectiveAffineSecantTensor (m - d) (m + d) x X y Y c =
      ((X + c) - m * x) * (Y - m * y) - d ^ 2 * x * y +
        m * ((X + c) * y - x * Y) := by
  simp only [suzukiProjectiveAffineSecantTensor]
  ring

/-- Endpoint denominator is the Lorentz norm of the centered denominator coordinate. -/
theorem suzukiProjectiveAffineSecantDenominator_midpoint_halfGap
    {F : Type*} [CommRing F] (m d y Y : F) :
    suzukiProjectiveAffineSecantDenominator (m - d) (m + d) y Y =
      (Y - m * y) ^ 2 - d ^ 2 * y ^ 2 := by
  simp only [suzukiProjectiveAffineSecantDenominator]
  ring

/-- Symmetric part of the marked coefficient form in uncentered source coordinates. -/
def suzukiMarkedSecantSymmetricForm
    {F : Type*} [CommRing F]
    (m d r s R S : F) : F :=
  r * R - m * (r * S + s * R) + (m ^ 2 - d ^ 2) * s * S

/-- Alternating, centered Pluecker part of the marked coefficient form. -/
def suzukiMarkedSecantAlternatingForm
    {F : Type*} [CommRing F]
    (m r s R S : F) : F :=
  m * (r * S - s * R)

/-- Symmetric plus alternating forms recover the complete marked tensor, including affine mark. -/
theorem suzukiProjectiveAffineSecantTensor_eq_symmetric_add_alternating
    {F : Type*} [CommRing F] (m d x X y Y c : F) :
    suzukiProjectiveAffineSecantTensor (m - d) (m + d) x X y Y c =
      suzukiMarkedSecantSymmetricForm m d (X + c) x Y y +
        suzukiMarkedSecantAlternatingForm m (X + c) x Y y := by
  simp only [suzukiProjectiveAffineSecantTensor,
    suzukiMarkedSecantSymmetricForm, suzukiMarkedSecantAlternatingForm]
  ring

/-- The diagonal symmetric form is a Lorentz square with exact negative coefficient `d^2`. -/
theorem suzukiMarkedSecantSymmetricForm_self_eq
    {F : Type*} [CommRing F] (m d r s : F) :
    suzukiMarkedSecantSymmetricForm m d r s r s =
      (r - m * s) ^ 2 - d ^ 2 * s ^ 2 := by
  simp only [suzukiMarkedSecantSymmetricForm]
  ring

/-! ## Sharp completion and inertia -/

/-- Exact square completion after adding a rooted diagonal source with rate `kappa`. -/
theorem suzukiMarkedSecantSymmetricForm_add_rootedCompletion
    (m d kappa r s : ℝ) :
    suzukiMarkedSecantSymmetricForm m d r s r s + kappa * s ^ 2 =
      (r - m * s) ^ 2 + (kappa - d ^ 2) * s ^ 2 := by
  simp only [suzukiMarkedSecantSymmetricForm]
  ring

/-- **Sharp completion law.**  A rooted diagonal repairs every source coordinate exactly when its
rate is at least the square of the shift halfgap. -/
theorem suzukiMarkedSecant_rootedCompletion_nonneg_iff
    (m d kappa : ℝ) :
    (∀ r s : ℝ,
      0 ≤ suzukiMarkedSecantSymmetricForm m d r s r s + kappa * s ^ 2) ↔
        d ^ 2 ≤ kappa := by
  constructor
  · intro h
    have hm := h m 1
    rw [suzukiMarkedSecantSymmetricForm_add_rootedCompletion] at hm
    norm_num at hm
    exact hm
  · intro hk r s
    rw [suzukiMarkedSecantSymmetricForm_add_rootedCompletion]
    exact add_nonneg (sq_nonneg _) (mul_nonneg (sub_nonneg.mpr hk) (sq_nonneg s))

/-- At the unique minimal rate, the completed symmetric block is one rank-one square. -/
theorem suzukiMarkedSecant_minimalRootedCompletion_eq_square
    (m d r s : ℝ) :
    suzukiMarkedSecantSymmetricForm m d r s r s + d ^ 2 * s ^ 2 =
      (r - m * s) ^ 2 := by
  rw [suzukiMarkedSecantSymmetricForm_add_rootedCompletion]
  ring

/-- Distinct shifts expose both signs before completion: exact coefficient inertia is `(1,1)`. -/
theorem suzukiMarkedSecantSymmetricForm_has_positive_and_negative_directions
    (m d : ℝ) (hd : d ≠ 0) :
    0 < suzukiMarkedSecantSymmetricForm m d 1 0 1 0 ∧
      suzukiMarkedSecantSymmetricForm m d m 1 m 1 < 0 := by
  constructor
  · simp [suzukiMarkedSecantSymmetricForm]
  · rw [suzukiMarkedSecantSymmetricForm_self_eq]
    norm_num
    exact sq_pos_of_ne_zero hd

/-- Dyadic Suzuki shifts have sharp missing rooted rate `L^2/4`. -/
theorem suzukiMarkedSecant_dyadic_rootedCompletion_nonneg_iff
    (L kappa : ℝ) :
    (∀ r s : ℝ,
      0 ≤ r ^ 2 + 3 * L * r * s + 2 * L ^ 2 * s ^ 2 + kappa * s ^ 2) ↔
        L ^ 2 / 4 ≤ kappa := by
  constructor
  · intro h
    have hm := h (-3 * L / 2) 1
    norm_num at hm
    nlinarith
  · intro hk r s
    have hsq : 0 ≤ (r + 3 * L * s / 2) ^ 2 := sq_nonneg _
    have hroot : 0 ≤ (kappa - L ^ 2 / 4) * s ^ 2 :=
      mul_nonneg (sub_nonneg.mpr hk) (sq_nonneg s)
    nlinarith

/-! ## Three-channel compound split -/

/-- **Compound midpoint split.**  Canonical full-jump numerator has exactly midpoint determinant,
rooted halfgap debt, and centered Pluecker flux channels. -/
theorem suzukiGlobalLocalCompoundNumerator_marked_midpoint_halfGap
    {F : Type*} [CommRing F]
    (m d x X y Y c S T : F) :
    suzukiGlobalLocalCompoundNumerator
        (suzukiProjectiveAffineSecantTensor (m - d) (m + d) x X y Y c)
        (suzukiProjectiveAffineSecantDenominator (m - d) (m + d) y Y)
        S T =
      (Y - m * y) * (((X + c) - m * x) * T - S * (Y - m * y)) +
        d ^ 2 * y * (S * y - x * T) +
        m * ((X + c) * y - x * Y) * T := by
  simp only [suzukiGlobalLocalCompoundNumerator,
    suzukiProjectiveAffineSecantTensor,
    suzukiProjectiveAffineSecantDenominator]
  ring

/-- Compound denominator retains the same exact Lorentz norm. -/
theorem suzukiGlobalLocalCompoundDenominator_marked_midpoint_halfGap
    {F : Type*} [CommRing F] (m d y Y T : F) :
    suzukiGlobalLocalCompoundDenominator
        (suzukiProjectiveAffineSecantDenominator (m - d) (m + d) y Y) T =
      ((Y - m * y) ^ 2 - d ^ 2 * y ^ 2) * T := by
  simp only [suzukiGlobalLocalCompoundDenominator,
    suzukiProjectiveAffineSecantDenominator]
  ring

/-- In midpoint coordinates, affine gauge is the shear `(x,U) -> (x+delta*y,U+delta*V)`. -/
theorem suzukiMarkedSecantMidpoint_affineGauge_shear
    {F : Type*} [CommRing F] (m delta x X y Y c : F) :
    (X + delta * Y + c) - m * (x + delta * y) =
      ((X + c) - m * x) + delta * (Y - m * y) := by
  ring

/-- Centered Pluecker flux is invariant under the same affine shear. -/
theorem suzukiMarkedSecantMidpoint_flux_affineGauge_invariant
    {F : Type*} [CommRing F] (delta x X y Y c : F) :
    (X + delta * Y + c) * y - (x + delta * y) * Y =
      (X + c) * y - x * Y := by
  ring

/-! ## Physical two-resolvent source debt -/

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- Product of resolvents at `m-d` and `m+d` obeys centered second-order forcing with exact
halfgap debt `d^2`. -/
theorem suzukiTwoResolvent_midpoint_forcing
    (A RMinus RPlus : V →ₗ[ℂ] V) (m d : ℂ) (e : V)
    (hMinusInv : ∀ u, A (RMinus u) - (m - d) • RMinus u = u)
    (hPlusInv : ∀ u, A (RPlus u) - (m + d) • RPlus u = u)
    (hcomm : RMinus (RPlus e) = RPlus (RMinus e)) :
    let v := RMinus (RPlus e)
    let uMid := A v - m • v
    e = A uMid - m • uMid - d ^ 2 • v := by
  dsimp only
  have hPlusState :
      RMinus e =
        A (RMinus (RPlus e)) - (m + d) • RMinus (RPlus e) := by
    rw [hcomm]
    exact (hPlusInv (RMinus e)).symm
  have hroot := (hMinusInv e).symm
  rw [hPlusState] at hroot
  exact hroot.trans (by
    simp only [map_sub, map_smul, smul_sub, smul_smul]
    module)

/-- Relative Volterra phase reads centered forcing as shifted phase plus a literal
`-d^2 * phaseNeumann(v)` rooted source. -/
theorem suzukiRelativeVolterraPhaseObservation_midpoint_forcing
    (A : V →ₗ[ℂ] V) (phaseEuler phaseNeumann : V →ₗ[ℂ] ℂ)
    (m d : ℂ) (e v uMid : V)
    (hforcing : e = A uMid - m • uMid - d ^ 2 • v) :
    suzukiRelativeVolterraPhaseObservation A phaseEuler phaseNeumann uMid +
        phaseNeumann e =
      phaseEuler uMid - m * phaseNeumann uMid - d ^ 2 * phaseNeumann v := by
  rw [suzukiRelativeVolterraPhaseObservation]
  simp only [LinearMap.sub_apply, LinearMap.comp_apply]
  rw [hforcing]
  simp only [map_sub, map_smul, smul_eq_mul]
  ring

/-- **Physical midpoint debt capstone.**  On actual two-resolvent orbit, square of shift halfgap
is exactly coefficient of rooted Neumann midpoint source in relative phase carrier. -/
theorem suzukiTwoResolvent_relativeVolterraPhase_midpoint_debt
    (A RMinus RPlus : V →ₗ[ℂ] V)
    (phaseEuler phaseNeumann : V →ₗ[ℂ] ℂ)
    (m d : ℂ) (e : V)
    (hMinusInv : ∀ u, A (RMinus u) - (m - d) • RMinus u = u)
    (hPlusInv : ∀ u, A (RPlus u) - (m + d) • RPlus u = u)
    (hcomm : RMinus (RPlus e) = RPlus (RMinus e)) :
    let v := RMinus (RPlus e)
    let uMid := A v - m • v
    suzukiRelativeVolterraPhaseObservation A phaseEuler phaseNeumann uMid +
        phaseNeumann e =
      phaseEuler uMid - m * phaseNeumann uMid - d ^ 2 * phaseNeumann v := by
  dsimp only
  exact suzukiRelativeVolterraPhaseObservation_midpoint_forcing
    A phaseEuler phaseNeumann m d e
      (RMinus (RPlus e))
      (A (RMinus (RPlus e)) - m • RMinus (RPlus e))
      (suzukiTwoResolvent_midpoint_forcing
        A RMinus RPlus m d e hMinusInv hPlusInv hcomm)

/-! ## Direct connector to the canonical marked Xi compound target -/

/-- Source-specialized full-jump numerator in three midpoint channels.  This is exact left side of
`SUZUKI-ROOTED-MIDPOINT-COMPOUND-GRAM`; only its prime--Gamma Gram factorization remains open. -/
theorem suzukiMarkedXiCompoundNumerator_midpoint_halfGap
    (m d : ℂ) (x X y Y c : ℂ → ℂ) (z : ℂ) :
    suzukiMarkedXiCompoundNumerator (m - d) (m + d) x X y Y c z =
      (Y z - m * y z) *
          (((X z + c z) - m * x z) * suzukiXiDerivativePairDenominator z -
            suzukiXiDerivativePairNumerator z * (Y z - m * y z)) +
        d ^ 2 * y z *
          (suzukiXiDerivativePairNumerator z * y z -
            x z * suzukiXiDerivativePairDenominator z) +
        m * ((X z + c z) * y z - x z * Y z) *
          suzukiXiDerivativePairDenominator z := by
  simp only [suzukiMarkedXiCompoundNumerator,
    suzukiXiGlobalLocalCompoundNumerator,
    suzukiGlobalLocalCompoundNumeratorFn,
    suzukiMarkedAffineSecantNumeratorFn,
    suzukiMarkedAffineSecantDenominatorFn,
    suzukiGlobalLocalCompoundNumerator,
    suzukiComplexProjectiveAffineSecantTensor,
    suzukiProjectiveAffineSecantDenominator]
  ring

/-- Source-specialized compound denominator retains exact centered Lorentz divisor. -/
theorem suzukiMarkedXiCompoundDenominator_midpoint_halfGap
    (m d : ℂ) (y Y : ℂ → ℂ) (z : ℂ) :
    suzukiMarkedXiCompoundDenominator (m - d) (m + d) y Y z =
      ((Y z - m * y z) ^ 2 - d ^ 2 * (y z) ^ 2) *
        suzukiXiDerivativePairDenominator z := by
  simp only [suzukiMarkedXiCompoundDenominator,
    suzukiXiGlobalLocalCompoundDenominator,
    suzukiGlobalLocalCompoundDenominatorFn,
    suzukiMarkedAffineSecantDenominatorFn,
    suzukiGlobalLocalCompoundDenominator,
    suzukiProjectiveAffineSecantDenominator]
  ring

end

end RHTower
