import GaloisForLFunctions.WindowedLandauTheory.SharpRestriction.LevelLetterCocycles.BlochKatoPhases
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

/-! A rank-one twist scales the characteristic roots and leaves the
invariant subspaces of the representation unchanged. -/

noncomputable section

open Polynomial
open WindowedLandauTheory.MainNotions.N
open WindowedLandauTheory.MainNotions.BlochKatoReduction

namespace GlobalTheory.SSComplement

variable {Γ K : Type} [Group Γ] [CommRing K] {n : ℕ}

theorem val_twGL (ρ : Γ →* GL (Fin n) K) (χ : Γ →* Kˣ) (g : Γ) :
    (twGL ρ χ g).val = (((χ g)⁻¹ : Kˣ) : K) • (ρ g).val := by
  change algebraMap K (Matrix (Fin n) (Fin n) K) (((χ g)⁻¹ : Kˣ) : K) * (ρ g).val = _
  exact (Algebra.smul_def _ _).symm

theorem map_smul_matrix {L : Type*} [CommRing L] (f : K →+* L) (c : K)
    (M : Matrix (Fin n) (Fin n) K) : (c • M).map f = f c • M.map f := by
  ext i j
  simp

theorem mapRep_twGL {L : Type} [CommRing L] (f : K →+* L)
    (ρ : Γ →* GL (Fin n) K) (χ : Γ →* Kˣ) :
    mapRep f (twGL ρ χ) = twGL (mapRep f ρ) ((Units.map f.toMonoidHom).comp χ) := by
  apply MonoidHom.ext
  intro g
  apply Units.ext
  change ((twGL ρ χ g).val).map f = (twGL (mapRep f ρ) ((Units.map f.toMonoidHom).comp χ) g).val
  rw [val_twGL, val_twGL, map_smul_matrix] <;> rfl

theorem continuous_twGL [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [TopologicalSpace K] [IsTopologicalRing K]
    (ρ : Γ →* GL (Fin n) K) (χ : Γ →* Kˣ)
    (hρ : Continuous fun g => (ρ g).val) (hχ : Continuous fun g => (χ g : K)) :
    Continuous fun g => (twGL ρ χ g).val := by
  simp only [val_twGL, ← map_inv]
  exact (hχ.comp continuous_inv).smul hρ

theorem isSSRep_twGL {k : Type} [Field k] (ρ : Γ →* GL (Fin n) k)
    (χ : Γ →* kˣ) (h : IsSSRep ρ) : IsSSRep (twGL ρ χ) := by
  have hInv (W : Submodule k (Fin n → k)) : IsInv (twGL ρ χ) W ↔ IsInv ρ W := by
    refine ⟨fun hW g v hv => ?_, fun hW g v hv => ?_⟩
    · have hh := hW g v hv
      rw [val_twGL, Matrix.smul_mulVec] at hh
      exact (W.smul_mem_iff ((χ g)⁻¹).ne_zero).mp hh
    · rw [val_twGL, Matrix.smul_mulVec]
      exact W.smul_mem _ (hW g v hv)
  intro W hW
  obtain ⟨C, hC, hcomp⟩ := h W ((hInv W).mp hW)
  exact ⟨C, (hInv C).mpr hC, hcomp⟩

theorem charpoly_smul_of_prod {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (m : Multiset ℂ) (c : ℂ)
    (h : M.charpoly = (m.map fun a => X - C a).prod) : (c • M).charpoly = (m.map fun a => X - C (a * c)).prod := by
  have hn : Multiset.card m = n := by
    have := congrArg natDegree h
    rwa [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin, natDegree_multiset_prod_X_sub_C_eq_card, eq_comm] at this
  rcases eq_or_ne c 0 with rfl | hc
  · simp [hn]
  · apply Polynomial.funext
    intro z
    have h1 := congrArg (eval (z / c)) h
    rw [Matrix.eval_charpoly, eval_multiset_prod, Multiset.map_map] at h1
    have e : Matrix.scalar (Fin n) z - c • M = c • (Matrix.scalar (Fin n) (z / c) - M) := by
      rw [smul_sub, Matrix.scalar_apply, Matrix.scalar_apply, ← Matrix.diagonal_smul]
      congr 2
      funext x
      simp [mul_div_cancel₀ _ hc]
    rw [Matrix.eval_charpoly, eval_multiset_prod, Multiset.map_map, e, Matrix.det_smul, h1, Fintype.card_fin, ← hn,
      ← Multiset.prod_replicate, ← Multiset.map_const', ← Multiset.prod_map_mul]
    refine congrArg _ (Multiset.map_congr rfl fun a _ => ?_)
    simp only [Function.comp_apply, eval_sub, eval_X, eval_C]
    field_simp

end GlobalTheory.SSComplement
