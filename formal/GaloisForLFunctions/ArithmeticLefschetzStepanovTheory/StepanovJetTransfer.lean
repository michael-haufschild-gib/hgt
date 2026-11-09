import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Tactic.Ring

/-!
# The binomial transfer of differentiated multiplication

Left and right composition by an endomorphism commute. Their combination
`T ↦ q D T + (1-q) T D` therefore has an exact binomial expansion. When `D`
is a derivation, applying this transfer to multiplication by `g` gives the
recurrence for Euler jets after Adams substitution.
-/

open Finset
noncomputable section
namespace GaloisForLFunctions.ArithmeticLefschetzStepanovTheory

variable {A : Type*} [AddCommGroup A]

/-- Post- and pre-composition transfer, with complementary integer weights. -/
def stepanovJetTransfer (q : ℤ) (D : Module.End ℤ A) : Module.End ℤ (Module.End ℤ A) :=
  q • LinearMap.mulLeft ℤ D + (1 - q) • LinearMap.mulRight ℤ D

theorem stepanovJetTransfer_apply (q : ℤ) (D T : Module.End ℤ A) :
    stepanovJetTransfer q D T = q • (D * T) + (1 - q) • (T * D) := rfl

/-- The exact transfer coefficients at every derivative order. -/
theorem stepanovJetTransfer_pow (q : ℤ) (D T : Module.End ℤ A) (n : ℕ) :
    (stepanovJetTransfer q D ^ n) T =
      ∑ ij ∈ antidiagonal n, n.choose ij.1 •
        ((q ^ ij.2 * (1 - q) ^ ij.1) • (D ^ ij.2 * T * D ^ ij.1)) := by
  have h := (((LinearMap.commute_mulLeft_right (R := ℤ) D D).symm).smul_left (1 - q)).smul_right q
  rw [stepanovJetTransfer, add_comm, h.add_pow', LinearMap.sum_apply]
  apply sum_congr rfl
  rintro ⟨i, j⟩ _
  simp only [smul_pow, LinearMap.pow_mulLeft, LinearMap.pow_mulRight,
    LinearMap.smul_apply, Module.End.mul_apply, LinearMap.mulLeft_apply,
    LinearMap.mulRight_apply, map_smul, smul_smul]

theorem stepanovJetTransfer_commute_right (q : ℤ) (D : Module.End ℤ A) :
    Commute (stepanovJetTransfer q D) (LinearMap.mulRight ℤ D) := by
  ext T x
  rfl

theorem stepanovJetTransfer_pow_right (q : ℤ) (D T : Module.End ℤ A) (n : ℕ) :
    (stepanovJetTransfer q D ^ n) (T * D) = (stepanovJetTransfer q D ^ n) T * D :=
  congrArg (fun L : Module.End ℤ (Module.End ℤ A) => L T)
    ((stepanovJetTransfer_commute_right q D).pow_left n).eq

section Derivation

variable {B : Type*} [CommRing B]

/-- Leibniz turns the complementary weights into one derivative on each factor. -/
theorem stepanovJetTransfer_mulRight (q : ℤ) (D : Derivation ℤ B B) (g : B) :
    stepanovJetTransfer q D.toLinearMap (LinearMap.mulRight ℤ g) =
      q • LinearMap.mulRight ℤ (D g) + LinearMap.mulRight ℤ g * D.toLinearMap := by
  ext f
  change q • D (f * g) + (1 - q) • (D f * g) = q • (f * D g) + D f * g
  rw [Derivation.leibniz]
  simp only [smul_eq_mul, zsmul_eq_mul, Int.cast_sub, Int.cast_one]
  ring

/-- The transfer recurrence is the differentiated product rule with an Adams weight. -/
theorem stepanovJetTransfer_succ_mulRight (q : ℤ) (D : Derivation ℤ B B)
    (n : ℕ) (f g : B) :
    ((stepanovJetTransfer q D.toLinearMap ^ (n + 1)) (LinearMap.mulRight ℤ g)) f =
      ((stepanovJetTransfer q D.toLinearMap ^ n) (LinearMap.mulRight ℤ g)) (D f) +
        q • ((stepanovJetTransfer q D.toLinearMap ^ n) (LinearMap.mulRight ℤ (D g))) f := by
  rw [pow_succ, Module.End.mul_apply, stepanovJetTransfer_mulRight, map_add, map_smul,
    stepanovJetTransfer_pow_right]
  simp only [LinearMap.add_apply, LinearMap.smul_apply, Module.End.mul_apply, add_comm]
  rfl

end Derivation

#print axioms stepanovJetTransfer_pow
#print axioms stepanovJetTransfer_succ_mulRight

end GaloisForLFunctions.ArithmeticLefschetzStepanovTheory
