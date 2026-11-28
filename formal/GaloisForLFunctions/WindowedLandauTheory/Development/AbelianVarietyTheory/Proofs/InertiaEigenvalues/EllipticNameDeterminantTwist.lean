import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EllipticCuspidalNames
import Mathlib.FieldTheory.Finite.Trace

/-! On an elliptic class, the determinant is the norm of any
characteristic root. Twisting by a determinant character therefore
multiplies the elliptic name by the corresponding norm character. -/

noncomputable section

open Polynomial Matrix GlobalTheory.GLq GlobalTheory.Published

namespace GlobalTheory.EllipticCharacters

variable {g n : ℕ} [Fact g.Prime] {K : Type} [Field K] [Algebra (ZMod g) K]

/-- The norm of a unit in the residue extension, as a base unit. -/
def residueUnitNorm (K : Type) [Field K] [Algebra (ZMod g) K] : Kˣ →* (ZMod g)ˣ :=
  Units.map (Algebra.norm (ZMod g))

theorem determinant_eq_residueUnitNorm_of_elliptic_root (hn : 0 < n)
    (hd : Module.finrank (ZMod g) K = n) (y : Gn g n)
    (hy : Irreducible (y : Mt g n).charpoly) (z : Kˣ)
    (hz : aeval (z : K) (y : Mt g n).charpoly = 0) :
    GeneralLinearGroup.det y = residueUnitNorm K z := by
  haveI : FiniteDimensional (ZMod g) K := Module.finite_of_finrank_pos (hd ▸ hn)
  let b : Module.Basis (Fin n) (ZMod g) K := Module.finBasisOfFinrankEq _ _ hd
  have hc := minpoly.eq_of_irreducible_of_monic hy hz (Matrix.charpoly_monic _)
  have hdeg : (minpoly (ZMod g) (z : K)).natDegree = n := by
    rw [← hc, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  apply Units.ext
  change (y : Mt g n).det = Algebra.norm (ZMod g) (z : K)
  rw [Algebra.norm_eq_matrix_det b, Matrix.det_eq_sign_charpoly_coeff (y : Mt g n),
    Matrix.det_eq_sign_charpoly_coeff (Algebra.leftMulMatrix b (z : K)), hc,
    leftMulMatrix_charpoly_of_fullDegree b z hdeg]

theorem residueUnitNorm_eq_frobeniusProduct (hn : 0 < n) (hd : Module.finrank (ZMod g) K = n)
    (z : Kˣ) :
    Units.map (algebraMap (ZMod g) K).toMonoidHom (residueUnitNorm K z) =
      ∏ i ∈ Finset.range n, z ^ g ^ i := by
  haveI : Finite K := finite_of_rank_eq hn hd
  apply Units.ext
  change algebraMap (ZMod g) K (Algebra.norm (ZMod g) (z : K)) =
    ((∏ i ∈ Finset.range n, z ^ g ^ i : Kˣ) : K)
  rw [FiniteField.algebraMap_norm_eq_prod_pow, hd, Nat.card_zmod]
  simpa only [Units.coeHom_apply, Units.val_pow_eq_pow_val] using
    (map_prod (Units.coeHom K) (fun i : ℕ => z ^ g ^ i) (Finset.range n)).symm

private theorem norm_twist_frob (δ : (ZMod g)ˣ →* ℂˣ) (i : ℕ) (z : Kˣ) :
    δ (residueUnitNorm K (z ^ g ^ i)) = δ (residueUnitNorm K z) := by
  rw [map_pow]
  congr 1
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, ZMod.pow_card_pow]

theorem regular_mul_residueNorm {θ : Kˣ →* ℂˣ} (hθ : IsRegularChar g n θ)
    (δ : (ZMod g)ˣ →* ℂˣ) : IsRegularChar g n (θ * δ.comp (residueUnitNorm K)) := by
  intro i j hi hj he
  apply hθ i j hi hj
  apply MonoidHom.ext
  intro z
  have e := DFunLike.congr_fun he z
  simp only [MonoidHom.pow_apply] at e ⊢
  rw [← map_pow (θ * δ.comp (residueUnitNorm K)), ← map_pow (θ * δ.comp (residueUnitNorm K))] at e
  simp only [MonoidHom.mul_apply, MonoidHom.comp_apply, norm_twist_frob, map_pow θ] at e
  exact mul_right_cancel e

theorem HasEllipticName.twistDet (hn : 0 < n) (hd : Module.finrank (ZMod g) K = n)
    {θ : Kˣ →* ℂˣ} {χ : Gn g n → ℂ} (hχ : HasEllipticName θ χ)
    (δ : (ZMod g)ˣ →* ℂˣ) :
    HasEllipticName (θ * δ.comp (residueUnitNorm K))
      (fun y => χ y * (δ (GeneralLinearGroup.det y) : ℂ)) := by
  intro y hy z hz
  change χ y * (δ (GeneralLinearGroup.det y) : ℂ) =
    (-1) ^ (n - 1) * ∑ j ∈ Finset.range n, ((θ * δ.comp (residueUnitNorm K)) (z ^ g ^ j) : ℂ)
  rw [hχ y hy z hz, determinant_eq_residueUnitNorm_of_elliptic_root hn hd y hy z hz, mul_assoc,
    Finset.sum_mul]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [MonoidHom.mul_apply, MonoidHom.comp_apply, Units.val_mul, norm_twist_frob]

theorem regular_inv {θ : Kˣ →* ℂˣ} (hθ : IsRegularChar g n θ) :
    IsRegularChar g n θ⁻¹ := by
  intro i j hi hj he
  apply hθ i j hi hj
  apply MonoidHom.ext
  intro z
  have hz := DFunLike.congr_fun he z
  simpa only [MonoidHom.pow_apply, MonoidHom.inv_apply, inv_pow, _root_.inv_inj] using hz

end GlobalTheory.EllipticCharacters

#print axioms GlobalTheory.EllipticCharacters.residueUnitNorm_eq_frobeniusProduct
#print axioms GlobalTheory.EllipticCharacters.HasEllipticName.twistDet
