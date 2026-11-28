import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.CyclicInvariantCharacter
import GaloisForLFunctions.RHTower.Artin.ArtinLocalEulerFactorOfAnInflatedRepresentation

/-! Conjugation carries relative arithmetic Frobenius to the conjugate
prime even when the ambient automorphism acts on the base of the relative extension. -/

open scoped Pointwise

namespace GlobalTheory.Reciprocity

universe u

variable {B C G Γ : Type u} [CommRing B] [CommRing C] [Algebra B C]
  [Group G] [Group Γ] [MulSemiringAction G B] [MulSemiringAction Γ C]
  (r : Γ →* G)
  (hr : ∀ (t : Γ) (x : B), t • algebraMap B C x = algebraMap B C (r t • x))

include hr in
theorem conjugateIn_isArithFrobAt [SMulCommClass r.ker B C] {P : Ideal C} {σ : r.ker}
    (hσ : IsArithFrobAt B σ P) (t : Γ) :
    IsArithFrobAt B (conjugateIn r.ker t σ) (t • P) := by
  have hcard : Nat.card (B ⧸ (t • P : Ideal C).under B) = Nat.card (B ⧸ P.under B) := by
    rw [GaloisForLFunctions.under_smul_eq_map_smul_under r (fun t x => (hr t x).symm)]
    let e := MulSemiringAction.toRingEquiv G B (r t)
    exact (Nat.card_congr (Ideal.quotientEquiv _ _ e (Ideal.pointwise_smul_def _)).toEquiv).symm
  intro x
  change (t * σ.val * t⁻¹) • x - x ^ Nat.card (B ⧸ (t • P : Ideal C).under B) ∈ t • P
  rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem, hcard, smul_sub, smul_pow', mul_smul, mul_smul,
    inv_smul_smul]
  exact hσ (t⁻¹ • x)

end GlobalTheory.Reciprocity
