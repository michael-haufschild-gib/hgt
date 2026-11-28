import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EllipticNameDeterminantTwist
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

/-! Inversion on an elliptic matrix inverts its residue root.
Consequently the dual character has the inverse regular name. -/

noncomputable section

open Matrix Polynomial GlobalTheory.GLq

namespace GlobalTheory.EllipticCharacters

variable {p n : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K]

private theorem minpoly_natDegree_inv [FiniteDimensional (ZMod p) K] (x : K) :
    (minpoly (ZMod p) x⁻¹).natDegree = (minpoly (ZMod p) x).natDegree := by
  have he : IntermediateField.adjoin (ZMod p) {x⁻¹} = IntermediateField.adjoin (ZMod p) {x} := by
    apply le_antisymm
    · rw [IntermediateField.adjoin_simple_le_iff]
      exact inv_mem (IntermediateField.mem_adjoin_simple_self (ZMod p) x)
    · rw [IntermediateField.adjoin_simple_le_iff]
      simpa only [inv_inv] using inv_mem (IntermediateField.mem_adjoin_simple_self (ZMod p) x⁻¹)
  rw [← IntermediateField.adjoin.finrank (Algebra.IsIntegral.isIntegral _),
    ← IntermediateField.adjoin.finrank (Algebra.IsIntegral.isIntegral x), he]

private theorem irreducible_charpoly_inverse_and_root [FiniteDimensional (ZMod p) K]
    (y : Gn p n) (hy : Irreducible y.val.charpoly) (z : Kˣ)
    (hz : aeval (z : K) y.val.charpoly = 0) :
    Irreducible (y⁻¹ : Gn p n).val.charpoly ∧
      aeval ((z⁻¹ : Kˣ) : K) (y⁻¹ : Gn p n).val.charpoly = 0 := by
  let A := y.val
  let x := (z : K)
  letI := invertibleOfNonzero (Units.ne_zero z)
  have hrev : aeval x⁻¹ A.charpoly.reverse = 0 := by
    have h := (Polynomial.eval₂_reverse_eq_zero_iff (algebraMap (ZMod p) K) x A.charpoly).mpr
      (show eval₂ (algebraMap (ZMod p) K) x A.charpoly = 0 from hz)
    simpa only [Polynomial.aeval_def, invOf_eq_inv] using h
  have hroot : aeval x⁻¹ (y⁻¹ : Gn p n).val.charpoly = 0 := by
    rw [Matrix.coe_units_inv, Matrix.charpoly_inv _ y.isUnit, ← Matrix.reverse_charpoly, map_mul, hrev, mul_zero]
  have hmin : A.charpoly = minpoly (ZMod p) x :=
    minpoly.eq_of_irreducible_of_monic hy hz (Matrix.charpoly_monic A)
  have hdeg : (minpoly (ZMod p) x⁻¹).natDegree = n := by
    rw [minpoly_natDegree_inv, ← hmin, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  have hi : IsIntegral (ZMod p) x⁻¹ := Algebra.IsIntegral.isIntegral _
  have he : (y⁻¹ : Gn p n).val.charpoly = minpoly (ZMod p) x⁻¹ := by
    refine Polynomial.eq_of_monic_of_dvd_of_natDegree_le
      (minpoly.monic hi)
      (Matrix.charpoly_monic (y⁻¹ : Gn p n).val) (minpoly.dvd (ZMod p) x⁻¹ hroot) ?_
    rw [hdeg, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  exact ⟨he.symm ▸ minpoly.irreducible hi, by simpa only [Units.val_inv_eq_inv_val, x] using hroot⟩

theorem HasEllipticName.inverse (hn : 0 < n) (hd : Module.finrank (ZMod p) K = n)
    {θ : Kˣ →* ℂˣ} {χ : Gn p n → ℂ} (hχ : HasEllipticName θ χ) :
    HasEllipticName θ⁻¹ (fun y => χ y⁻¹) := by
  letI : FiniteDimensional (ZMod p) K := Module.finite_of_finrank_pos (hd ▸ hn)
  intro y hy z hz
  obtain ⟨hy', hz'⟩ := irreducible_charpoly_inverse_and_root y hy z hz
  change χ y⁻¹ = _
  rw [hχ _ hy' z⁻¹ hz']
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [inv_pow, map_inv, MonoidHom.inv_apply]

end GlobalTheory.EllipticCharacters

#print axioms GlobalTheory.EllipticCharacters.HasEllipticName.inverse
