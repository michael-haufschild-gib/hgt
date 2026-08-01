import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Local principal-symbol calibration for two clock masses

This file gives an exact local-coordinate model of a scalar differential operator of order at
most two. A `ScalarTwoJet` records value, first derivatives, and ordered second derivatives at one
point. Its product is verified against the literal iterated Leibniz rule for arbitrary derivations.

For a local operator `P`, the file computes every coefficient of left/right multiplication
`b · P · a`. It proves that derivatives of the right gain affect only lower-order coefficients,
while the quadratic principal symbol is multiplied by `b * a.value`. Adding a scalar mass changes
only the zeroth-order coefficient. Consequently, two distinct mass channels isolate endpoint
calibration as an actual zeroth-order operator and reconstruct the undressed principal symbol.

No spacetime, Green operator, support-domain, or experimental-reconstruction assumption is
introduced here; those are separate analytic and physical inputs.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {ι R : Type*}

/-- Exact value, first derivatives, and ordered second derivatives at one point. -/
@[ext]
structure ScalarTwoJet (ι R : Type*) where
  value : R
  first : ι → R
  second : ι → ι → R

namespace ScalarTwoJet

variable [CommRing R]

/-- Exact second-order product rule on scalar jets. -/
def mul (a f : ScalarTwoJet ι R) : ScalarTwoJet ι R where
  value := a.value * f.value
  first i := a.first i * f.value + a.value * f.first i
  second i j := a.second i j * f.value + a.first j * f.first i +
    a.first i * f.first j + a.value * f.second i j

/-- Jet supplied by an actual family of derivations. -/
def ofFunction (D : ι → Derivation ℤ R R) (f : R) : ScalarTwoJet ι R where
  value := f
  first i := D i f
  second i j := D i (D j f)

/-- Abstract jet multiplication is the literal iterated Leibniz rule. -/
theorem ofFunction_mul (D : ι → Derivation ℤ R R) (a f : R) :
    ofFunction D (a * f) = mul (ofFunction D a) (ofFunction D f) := by
  ext i j
  · rfl
  · simp [ofFunction, mul, Derivation.leibniz, smul_eq_mul]
    ring_nf
  · simp only [ofFunction, mul, Derivation.leibniz, smul_eq_mul, map_add]
    ring_nf

end ScalarTwoJet

/-- Scalar differential operator of order at most two in local coordinates. -/
@[ext]
structure ScalarSecondOrderOperator (ι R : Type*) where
  zeroth : R
  first : ι → R
  second : ι → ι → R

namespace ScalarSecondOrderOperator

variable [CommRing R] [Fintype ι]

/-- Exact action of a local scalar second-order operator on a two-jet. -/
def evalJet (P : ScalarSecondOrderOperator ι R) (f : ScalarTwoJet ι R) : R :=
  P.zeroth * f.value +
    ∑ i, P.first i * f.first i +
      ∑ i, ∑ j, P.second i j * f.second i j

/-- Composition on the right by multiplication with a scalar two-jet. -/
def rightMultiply (P : ScalarSecondOrderOperator ι R) (a : ScalarTwoJet ι R) :
    ScalarSecondOrderOperator ι R where
  zeroth := P.zeroth * a.value +
    ∑ i, P.first i * a.first i +
      ∑ i, ∑ j, P.second i j * a.second i j
  first k := P.first k * a.value +
    (∑ j, P.second k j * a.first j) +
      ∑ i, P.second i k * a.first i
  second i j := P.second i j * a.value

/-- Right-multiplication coefficients agree exactly with second-order jet substitution. -/
theorem evalJet_rightMultiply (P : ScalarSecondOrderOperator ι R)
    (a f : ScalarTwoJet ι R) :
    evalJet (rightMultiply P a) f = evalJet P (ScalarTwoJet.mul a f) := by
  classical
  have hcross₂ :
      (∑ k, ∑ i, (P.second i k * a.first i) * f.first k) =
        ∑ i, ∑ j, P.second i j * a.first i * f.first j := by
    rw [Finset.sum_comm]
  have hcomm :
      (∑ i, ∑ j, a.first i * P.second i j * f.first j) =
        ∑ i, ∑ j, P.second i j * a.first i * f.first j := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hprincipal :
      (∑ i, ∑ j, a.value * P.second i j * f.second i j) =
        ∑ i, ∑ j, P.second i j * a.value * f.second i j := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp only [evalJet, rightMultiply, ScalarTwoJet.mul]
  simp_rw [add_mul, mul_add, Finset.sum_add_distrib, Finset.sum_mul]
  rw [hcross₂]
  ring_nf
  rw [hcomm, hprincipal]
  ring

/-- Right multiplication is literal multiplication when jets come from derivations. -/
theorem evalJet_rightMultiply_ofFunction (D : ι → Derivation ℤ R R)
    (P : ScalarSecondOrderOperator ι R) (a f : R) :
    evalJet (rightMultiply P (ScalarTwoJet.ofFunction D a))
        (ScalarTwoJet.ofFunction D f) =
      evalJet P (ScalarTwoJet.ofFunction D (a * f)) := by
  rw [ScalarTwoJet.ofFunction_mul]
  exact evalJet_rightMultiply P _ _

/-- Composition on the left by a multiplication value. -/
def leftMultiply (b : R) (P : ScalarSecondOrderOperator ι R) :
    ScalarSecondOrderOperator ι R where
  zeroth := b * P.zeroth
  first i := b * P.first i
  second i j := b * P.second i j

/-- Left multiplication acts literally after operator evaluation. -/
theorem evalJet_leftMultiply (b : R) (P : ScalarSecondOrderOperator ι R)
    (f : ScalarTwoJet ι R) :
    evalJet (leftMultiply b P) f = b * evalJet P f := by
  classical
  have hfirst :
      (∑ i, b * P.first i * f.first i) = b * ∑ i, P.first i * f.first i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hsecond :
      (∑ i, ∑ j, b * P.second i j * f.second i j) =
        b * ∑ i, ∑ j, P.second i j * f.second i j := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp only [evalJet, leftMultiply]
  rw [hfirst, hsecond]
  ring

/-- Endpoint dressing `b · P · a` as an exact second-order operator. -/
def dress (b : R) (P : ScalarSecondOrderOperator ι R) (a : ScalarTwoJet ι R) :
    ScalarSecondOrderOperator ι R :=
  leftMultiply b (rightMultiply P a)

/-- Exact action of the endpoint-dressed operator. -/
theorem evalJet_dress (b : R) (P : ScalarSecondOrderOperator ι R)
    (a f : ScalarTwoJet ι R) :
    evalJet (dress b P a) f = b * evalJet P (ScalarTwoJet.mul a f) := by
  rw [dress, evalJet_leftMultiply, evalJet_rightMultiply]

/-- Quadratic principal symbol of a local second-order scalar operator. -/
def principalSymbol (P : ScalarSecondOrderOperator ι R) (ξ : ι → R) : R :=
  ∑ i, ∑ j, P.second i j * ξ i * ξ j

/-- Exact principal-symbol scaling under left and right multiplication. -/
theorem principalSymbol_dress (b : R) (P : ScalarSecondOrderOperator ι R)
    (a : ScalarTwoJet ι R) (ξ : ι → R) :
    principalSymbol (dress b P a) ξ =
      (b * a.value) * principalSymbol P ξ := by
  classical
  simp only [principalSymbol, dress, leftMultiply, rightMultiply]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- A mass shift changes only the zeroth-order coefficient. -/
def massShift (P : ScalarSecondOrderOperator ι R) (μ : R) :
    ScalarSecondOrderOperator ι R where
  zeroth := P.zeroth + μ
  first := P.first
  second := P.second

@[simp]
theorem principalSymbol_massShift (P : ScalarSecondOrderOperator ι R) (μ : R) (ξ : ι → R) :
    principalSymbol (massShift P μ) ξ = principalSymbol P ξ := rfl

/-- Difference of local second-order operators, coefficient by coefficient. -/
def sub (P Q : ScalarSecondOrderOperator ι R) : ScalarSecondOrderOperator ι R where
  zeroth := P.zeroth - Q.zeroth
  first i := P.first i - Q.first i
  second i j := P.second i j - Q.second i j

/-- Zeroth-order multiplication operator. -/
def zerothOrder (c : R) : ScalarSecondOrderOperator ι R where
  zeroth := c
  first := 0
  second := 0

/-- Local-coordinate measured inverse `B⁻¹(P + μ)A⁻¹`. -/
def measuredClockInverseOperator (P : ScalarSecondOrderOperator ι R)
    (sourceGainInv : R) (receiverGainInv : ScalarTwoJet ι R) (μ : R) :
    ScalarSecondOrderOperator ι R :=
  dress sourceGainInv (massShift P μ) receiverGainInv

/-- Two mass channels differ by the zeroth-order endpoint-calibration operator. -/
theorem measuredClockInverseOperator_difference
    (P : ScalarSecondOrderOperator ι R)
    (sourceGainInv : R) (receiverGainInv : ScalarTwoJet ι R) (μ₁ μ₂ : R) :
    sub (measuredClockInverseOperator P sourceGainInv receiverGainInv μ₁)
        (measuredClockInverseOperator P sourceGainInv receiverGainInv μ₂) =
      zerothOrder ((μ₁ - μ₂) * (sourceGainInv * receiverGainInv.value)) := by
  ext i j
  · simp only [sub, measuredClockInverseOperator, dress, leftMultiply, rightMultiply,
      massShift, zerothOrder]
    ring
  · simp [sub, measuredClockInverseOperator, dress, leftMultiply, rightMultiply,
      massShift, zerothOrder]
  · simp [sub, measuredClockInverseOperator, dress, leftMultiply, rightMultiply,
      massShift, zerothOrder]

/-- The two-mass difference acts literally as zeroth-order multiplication on every jet. -/
theorem evalJet_measuredClockInverseOperator_difference
    (P : ScalarSecondOrderOperator ι R)
    (sourceGainInv : R) (receiverGainInv : ScalarTwoJet ι R) (μ₁ μ₂ : R)
    (f : ScalarTwoJet ι R) :
    evalJet
        (sub (measuredClockInverseOperator P sourceGainInv receiverGainInv μ₁)
          (measuredClockInverseOperator P sourceGainInv receiverGainInv μ₂)) f =
      ((μ₁ - μ₂) * (sourceGainInv * receiverGainInv.value)) * f.value := by
  rw [measuredClockInverseOperator_difference]
  simp [evalJet, zerothOrder]

/-- Measured principal symbol is endpoint calibration times geometric principal symbol. -/
theorem principalSymbol_measuredClockInverseOperator
    (P : ScalarSecondOrderOperator ι R)
    (sourceGainInv : R) (receiverGainInv : ScalarTwoJet ι R) (μ : R) (ξ : ι → R) :
    principalSymbol (measuredClockInverseOperator P sourceGainInv receiverGainInv μ) ξ =
      (sourceGainInv * receiverGainInv.value) * principalSymbol P ξ := by
  rw [measuredClockInverseOperator, principalSymbol_dress, principalSymbol_massShift]

end ScalarSecondOrderOperator

namespace ScalarSecondOrderOperator

variable [Field R] [Fintype ι]

/-- Two distinct masses reconstruct the undressed principal symbol exactly. -/
theorem twoMassPrincipalSymbol_reconstruction
    (P : ScalarSecondOrderOperator ι R)
    {sourceGainInv : R} (hsource : sourceGainInv ≠ 0)
    (receiverGainInv : ScalarTwoJet ι R) (hreceiver : receiverGainInv.value ≠ 0)
    {μ₁ μ₂ : R} (hmass : μ₁ ≠ μ₂) (ξ : ι → R) :
    (μ₁ - μ₂) *
          principalSymbol
            (measuredClockInverseOperator P sourceGainInv receiverGainInv μ₁) ξ /
        ((μ₁ - μ₂) * (sourceGainInv * receiverGainInv.value)) =
      principalSymbol P ξ := by
  rw [principalSymbol_measuredClockInverseOperator]
  field_simp [sub_ne_zero.mpr hmass, hsource, hreceiver]

end ScalarSecondOrderOperator

end

end GaloisForLFunctions.HTGeometry
