import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerRationalSubcover

/-!
# Rationality at the divisible branch boundary

When the branch exponent is a multiple of the covering degree, the
quotient-radical rational subfield already has the full extension degree.
Its rational parameter therefore generates the whole Kummer field.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial
variable {K : Type*} [Field K] (c : Kˣ) (b n t : ℕ)
local notation "F" => FractionRing K[X]
local notation "L" => KummerBranchField c b ((n + 1) * t) n
local notation "S" => kummerBranchUnitSubfield c b ((n + 1) * t) n

/-- A branch exponent divisible by the covering degree makes the rational subcover the entire field. -/
theorem kummerBranchUnitSubfield_mul_degree_eq_top :
    kummerBranchUnitSubfield c b ((n + 1) * t) n = ⊤ := by
  letI : FiniteDimensional F L :=
    (monic_X_pow_sub_C _ (Nat.succ_ne_zero n)).finite_adjoinRoot
  have hdim : Module.finrank F S = Module.finrank F L := by
    rw [kummerBranchUnitSubfield_finrank, kummerBranchField_finrank,
      Nat.gcd_eq_left (show n + 1 ∣ (n + 1) * t from ⟨t, rfl⟩)]
  have htop : (S).toSubalgebra.toSubmodule = ⊤ := Submodule.eq_top_of_finrank_eq hdim
  apply top_unique
  intro x _
  have hx : x ∈ (S).toSubalgebra.toSubmodule := by rw [htop]; trivial
  exact hx

/-- Every Kummer field with branch exponent a multiple of the covering degree is explicitly rational. -/
def kummerBranchField_mul_degree_rationalEquiv :
    FractionRing K[X] ≃ₐ[K] KummerBranchField c b ((n + 1) * t) n := by
  let f : S →ₐ[K] L := (S).val.restrictScalars K
  have hsurj : Function.Surjective f := by
    intro x
    have hx : x ∈ S := by rw [kummerBranchUnitSubfield_mul_degree_eq_top]; trivial
    exact ⟨⟨x, hx⟩, rfl⟩
  exact (kummerBranchUnitSubfield_rationalEquiv c b ((n + 1) * t) n).trans
    (AlgEquiv.ofBijective f ⟨f.injective, hsurj⟩)

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
