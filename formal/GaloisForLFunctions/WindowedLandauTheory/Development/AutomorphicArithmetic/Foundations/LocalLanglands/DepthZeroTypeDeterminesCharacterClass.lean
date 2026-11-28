import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.LocalLanglands.DepthZeroTypeDeterminesRepresentation
import Mathlib.RepresentationTheory.FinGroupCharZero

/-! The finite character determines a cuspidal residue type.
Its character and the central character determine a smooth
irreducible p-adic representation admitting that type. -/

noncomputable section

open Matrix Representation CategoryTheory GlobalTheory.GLq

namespace GlobalTheory.GLp

variable {p n : ℕ} [Fact p.Prime] {V V' : Type}
  [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']

private theorem nonempty_iso_of_cuspidal_character_eq (τ τ' : FDRep ℂ (Gn p n))
    (hτ : IsCusp τ.character) (he : τ'.character = τ.character) :
    Nonempty (τ ≅ τ') := by
  obtain ⟨W, hW, hch⟩ := hτ.2.1
  haveI : Simple τ := by
    rw [FDRep.simple_iff_char_is_norm_one] at hW ⊢
    simpa only [hch] using hW
  haveI : Simple τ' := by
    have ht : Simple τ := inferInstance
    rw [FDRep.simple_iff_char_is_norm_one] at ht ⊢
    simpa only [he] using ht
  letI := invertibleOfNonzero (Nat.cast_ne_zero.mpr (Nat.card_pos : 0 < Nat.card (Gn p n)).ne' :
    (Nat.card (Gn p n) : ℂ) ≠ 0)
  have ha := FDRep.char_orthonormal τ τ'
  have hb := FDRep.char_orthonormal τ τ
  classical
  rw [if_pos ⟨Iso.refl τ⟩] at hb
  rw [he, hb] at ha
  by_contra h
  rw [if_neg h] at ha
  exact one_ne_zero ha

theorem nonempty_equiv_of_cuspidal_type_character
    (ρ : Representation ℂ (GL (Fin n) ℚ_[p]) V)
    (ρ' : Representation ℂ (GL (Fin n) ℚ_[p]) V') [ρ.IsIrreducible] [ρ'.IsIrreducible]
    (hρ : ∀ v : V, IsOpen {g : GL (Fin n) ℚ_[p] | ρ g v = v})
    (hρ' : ∀ v : V', IsOpen {g : GL (Fin n) ℚ_[p] | ρ' g v = v})
    (ω : ℚ_[p]ˣ →* ℂˣ)
    (hω : ∀ z v, ρ (GeneralLinearGroup.scalar (Fin n) z) v = (ω z : ℂ) • v)
    (hω' : ∀ z v, ρ' (GeneralLinearGroup.scalar (Fin n) z) v = (ω z : ℂ) • v)
    (τ τ' : FDRep ℂ (Gn p n)) (hτ : IsCusp τ.character) (hch : τ'.character = τ.character)
    (j : τ →ₗ[ℂ] V) (j' : τ' →ₗ[ℂ] V') (hj₀ : j ≠ 0)
    (hji : Function.Injective j) (hji' : Function.Injective j')
    (hj : ∀ (k : GL (Fin n) ℤ_[p]) (w : τ),
      j (τ.ρ (integralReduction p (Fin n) k) w) = ρ (integralInclusion p (Fin n) k) (j w))
    (hj' : ∀ (k : GL (Fin n) ℤ_[p]) (w : τ'),
      j' (τ'.ρ (integralReduction p (Fin n) k) w) = ρ' (integralInclusion p (Fin n) k) (j' w)) :
    Nonempty (ρ.Equiv ρ') := by
  haveI : Nontrivial τ := by
    by_contra h
    haveI := not_nontrivial_iff_subsingleton.mp h
    exact hj₀ (LinearMap.ext fun w => by rw [Subsingleton.elim w 0, map_zero, map_zero])
  obtain ⟨a⟩ := nonempty_iso_of_cuspidal_character_eq τ τ' hτ hch
  let e := FDRep.isoToLinearEquiv a
  let f := j'.comp e.toLinearMap
  have hf (k : GL (Fin n) ℤ_[p]) (w : τ) :
      f (τ.ρ (integralReduction p (Fin n) k) w) = ρ' (integralInclusion p (Fin n) k) (f w) := by
    have he : e (τ.ρ (integralReduction p (Fin n) k) w) =
        τ'.ρ (integralReduction p (Fin n) k) (e w) := by
      rw [FDRep.Iso.conj_ρ a, LinearEquiv.conj_apply_apply]
      change e (τ.ρ (integralReduction p (Fin n) k) w) =
        e (τ.ρ (integralReduction p (Fin n) k) (e.symm (e w)))
      rw [e.symm_apply_apply]
    change j' (e (τ.ρ (integralReduction p (Fin n) k) w)) =
      ρ' (integralInclusion p (Fin n) k) (j' (e w))
    rw [he, hj']
  exact nonempty_equiv_of_cuspidal_type ρ ρ' hρ hρ' ω hω hω' τ.ρ hτ j f hji
    (hji'.comp e.injective) hj hf

end GlobalTheory.GLp

#print axioms GlobalTheory.GLp.nonempty_equiv_of_cuspidal_type_character
