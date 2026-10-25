import GaloisForLFunctions.ArithmeticDefectRigidity.RankOneCofactorMagnitudesArePowers
import GaloisForLFunctions.ArithmeticDefectRigidity.CofactorAnnihilatorsArePrincipalQuotients

/-!
# Rank-one cofactor states are fixed by contraction

Multiplicativity of the actual rank-one character makes every positive
cofactor normalization recover the original Gram and Wiener annihilator.
-/

noncomputable section
set_option autoImplicit false

namespace GaloisForLFunctions.ArithmeticDefectRigidity.ActualCofactorLimit

/-- In an actual line, simultaneous dilation scales the entire Gram by its selected diagonal. -/
theorem kernel_mul_mul_of_finrank_one {ε : SubcriticalDamping}
    (L : ActualCofactorLimit ε) (hL : Module.finrank ℂ (Hilbert L) = 1)
    (p j k : ℕ+) :
    L.kernel (p * j) (p * k) = L.kernel p p * L.kernel j k := by
  rw [kernel_eq_product_of_finrank_one L hL (p * j) (p * k),
    kernel_eq_product_of_finrank_one L hL p p,
    kernel_eq_product_of_finrank_one L hL j k]
  change rankOneCharacter L hL (p * j) * rankOneCharacter L hL (p * k) =
    (rankOneCharacter L hL p * rankOneCharacter L hL p) *
      (rankOneCharacter L hL j * rankOneCharacter L hL k)
  rw [map_mul, map_mul]
  ring

/-- Every defined cofactor contraction fixes an actual rank-one Gram. -/
theorem contracted_kernel_eq_of_finrank_one {ε : SubcriticalDamping}
    (L M : ActualCofactorLimit ε) (hL : Module.finrank ℂ (Hilbert L) = 1)
    (p : ℕ+) (hp : 0 < L.kernel p p)
    (hM : ∀ j k, M.kernel j k = L.kernel (p * j) (p * k) / L.kernel p p) :
    M.kernel = L.kernel := by
  funext j k
  rw [hM, kernel_mul_mul_of_finrank_one L hL]
  exact mul_div_cancel_left₀ _ hp.ne'

/-- A nonzero cofactor in an actual line has the same full Wiener annihilator. -/
theorem cofactorAnnihilator_eq_of_finrank_one {ε : SubcriticalDamping}
    (L : ActualCofactorLimit ε) (hL : Module.finrank ℂ (Hilbert L) = 1)
    (p : ℕ+) (hp : 0 < L.kernel p p) : cofactorAnnihilator L p = annihilator L := by
  have hne : L.kernel p 1 ≠ 0 := by
    intro h
    rw [kernel_eq_product_of_finrank_one L hL p p, h, mul_zero] at hp
    exact (lt_irrefl 0) hp
  have hneC : (L.kernel p 1 : ℂ) ≠ 0 := by exact_mod_cast hne
  ext a
  rw [mem_cofactorAnnihilator_iff, mem_annihilator_iff,
    vector_eq_kernel_smul_of_finrank_one L hL p, map_smul]
  constructor
  · intro h
    exact (smul_eq_zero.mp h).resolve_left hneC
  · intro h
    rw [h, smul_zero]

end GaloisForLFunctions.ArithmeticDefectRigidity.ActualCofactorLimit

#print axioms GaloisForLFunctions.ArithmeticDefectRigidity.ActualCofactorLimit.contracted_kernel_eq_of_finrank_one
#print axioms GaloisForLFunctions.ArithmeticDefectRigidity.ActualCofactorLimit.cofactorAnnihilator_eq_of_finrank_one
end
