import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CharacterTheory.CuspidalRadicalAveraging
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitriangularMonomialCosets
import Mathlib.LinearAlgebra.Matrix.Reindex

/-! Reordering matrix coordinates transports a parabolic radical by conjugation. -/

noncomputable section
open scoped Classical

namespace GlobalTheory.GLq

variable {g a b n m : ℕ} [Fact g.Prime]

/-- The homomorphism on matrix units induced by reindexing both coordinates. -/
def reindexUnit (e : Fin n ≃ Fin m) : Gn g n →* Gn g m :=
  Units.map (Matrix.reindexRingEquiv (ZMod g) e).toRingHom.toMonoidHom

theorem reindexUnit_apply (e : Fin n ≃ Fin m) (x : Gn g n) (i j : Fin m) :
    (reindexUnit e x).val i j = x.val (e.symm i) (e.symm j) := rfl

theorem permutationUnit_conj_apply (σ : Equiv.Perm (Fin n)) (x : Gn g n) (i j : Fin n) :
    ((monomialUnit σ (fun _ => 1))⁻¹ * x * monomialUnit σ (fun _ => 1) : Gn g n).val i j =
      x.val (σ i) (σ j) := by
  simpa only [Units.val_one, inv_one, one_mul, mul_one] using monomialConj_apply σ (fun _ => 1) x i j

theorem reindexUnit_perm (σ : Equiv.Perm (Fin n)) (x : Gn g n) :
    reindexUnit σ x = monomialUnit σ (fun _ => 1) * x * (monomialUnit σ (fun _ => 1))⁻¹ := by
  let w : Gn g n := monomialUnit σ (fun _ => 1)
  have hx : w⁻¹ * reindexUnit σ x * w = x := by
    apply Units.ext
    ext i j
    rw [permutationUnit_conj_apply, reindexUnit_apply, σ.symm_apply_apply, σ.symm_apply_apply]
  calc
    reindexUnit σ x = w * (w⁻¹ * reindexUnit σ x * w) * w⁻¹ := by group
    _ = w * x * w⁻¹ := by rw [hx]

/-- Cuspidal radical averaging also vanishes in any coordinates for a proper splitting. -/
theorem sum_cuspidal_reindexed_radical_translate_eq_zero {χ : Gn g n → ℂ} (hχ : IsCusp χ)
    (ha : 0 < a) (hb : 0 < b) (e : Fin (a + b) ≃ Fin n) (z : Gn g n)
    [Fintype (twoBlockLevi (g := g) (a := a) (b := b)).ker] :
    ∑ u : (twoBlockLevi (g := g) (a := a) (b := b)).ker, χ (z * reindexUnit e u.val.val) = 0 := by
  have he : a + b = n := by simpa only [Fintype.card_fin] using Fintype.card_congr e
  subst n
  let w : Gn g (a + b) := monomialUnit e (fun _ => 1)
  have hc : IsClass χ := by
    obtain ⟨V, _, hV⟩ := hχ.2.1
    intro x y
    exact (hV (y * x * y⁻¹)).symm.trans ((V.char_conj x y).trans (hV x))
  calc
    _ = ∑ u : (twoBlockLevi (g := g) (a := a) (b := b)).ker, χ ((w⁻¹ * z * w) * u.val.val) := by
      refine Finset.sum_congr rfl fun u _ => ?_
      rw [reindexUnit_perm]
      change χ (z * (w * u.val.val * w⁻¹)) = χ ((w⁻¹ * z * w) * u.val.val)
      have hu : z * (w * u.val.val * w⁻¹) = w * ((w⁻¹ * z * w) * u.val.val) * w⁻¹ := by group
      rw [hu]
      exact hc _ _
    _ = 0 := sum_cuspidal_radical_translate_eq_zero hχ ha hb (w⁻¹ * z * w)

end GlobalTheory.GLq
