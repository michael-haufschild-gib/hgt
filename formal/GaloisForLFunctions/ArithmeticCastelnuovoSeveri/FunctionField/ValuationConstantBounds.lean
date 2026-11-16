import Mathlib.RingTheory.Valuation.Integers

/-!
# Valuation bounds over a constant field

When the constants lie in a valuation ring, each valuation ball is a
vector subspace over those constants. These spaces impose pole bounds
on functions in a function field.
-/

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
variable {K L Γ₀ : Type*} [Field K] [Field L] [Algebra K L]
  [LinearOrderedCommGroupWithZero Γ₀]

/-- A valuation ball is a constant-field vector space. -/
def valuationConstantBound (v : Valuation L Γ₀)
    (hK : ∀ a : K, v (algebraMap K L a) ≤ 1) (γ : Γ₀) : Submodule K L where
  __ := v.leAddSubgroup γ
  smul_mem' a x hx := by
    change v (a • x) ≤ γ
    rw [Algebra.smul_def, map_mul]
    exact mul_le_of_le_one_of_le (hK a) hx

/-- Membership is the literal bound on the function's valuation. -/
theorem mem_valuationConstantBound_iff (v : Valuation L Γ₀)
    (hK : ∀ a : K, v (algebraMap K L a) ≤ 1) (γ : Γ₀) (x : L) :
    x ∈ valuationConstantBound v hK γ ↔ v x ≤ γ := Iff.rfl

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
