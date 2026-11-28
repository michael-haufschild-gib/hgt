import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.LocalLanglands.DepthZeroResidueCuspidality
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.LocalLanglands.TwoBlockResidueRadical
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.LocalLanglands.FiniteResidueTypeSelection
import GaloisForLFunctions.RHTower.Artin.ArtinVirtualCharacterPairing

/-! A nonzero first principal-congruence fixed space of a cuspidal
representation contains an inflated finite cuspidal type. Opposite
Jacquet vanishing forces each finite radical fixed space to vanish. -/

noncomputable section

open Matrix Representation GlobalTheory.OppRad GlobalTheory.GLq GaloisForLFunctions
open CategoryTheory

namespace GlobalTheory.GLp

variable {p n : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module ℂ V]

private theorem fdRep_simple_of_ρ_isIrreducible {G : Type} [Group G] [Fintype G]
    (τ : FDRep ℂ G) (hτ : IsIrreducible τ.ρ) : Simple τ := by
  letI : IsIrreducible τ.ρ := hτ
  have he := representationCharacterPairing_eq_finrank G τ.ρ τ.ρ
  rw [characterPairing, Representation.IsIrreducible.finrank_intertwiningMap_self, Nat.cast_one] at he
  have hc : (Nat.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  rw [FDRep.simple_iff_char_is_norm_one]
  change ∑ g : G, (Representation.character τ.ρ) g * (Representation.character τ.ρ) g⁻¹ = (Nat.card G : ℂ)
  calc
    _ = (Nat.card G : ℂ) * ((Nat.card G : ℂ)⁻¹ * ∑ g : G, (Representation.character τ.ρ) g * (Representation.character τ.ρ) g⁻¹) := by
      rw [← mul_assoc, mul_inv_cancel₀ hc, one_mul]
    _ = _ := by rw [he, mul_one]

theorem exists_cuspidal_type_of_jacquetVanishing
    (hn : 0 < n) (ρ : Representation ℂ (GL (Fin n) ℚ_[p]) V)
    (hρ : ∀ v : V, IsOpen {g : GL (Fin n) ℚ_[p] | ρ g v = v})
    (hJ : ∀ a, 0 < a → a < n →
      let A := blockProjection ℚ_[p] a n
      Coinvariants.ker (ρ.comp (U (1 - A) A).subtype) = ⊤)
    (hfix : principalFixed ρ ≠ ⊥) :
    ∃ (τ : FDRep ℂ (Gn p n)) (j : τ →ₗ[ℂ] V), IsCusp τ.character ∧ Function.Injective j ∧
      ∀ (k : GL (Fin n) ℤ_[p]) (v : τ),
        j (τ.ρ (integralReduction p (Fin n) k) v) = ρ (integralInclusion p (Fin n) k) (j v) := by
  letI : Nontrivial (principalFixed ρ) := Submodule.nontrivial_iff_ne_bot.mpr hfix
  obtain ⟨τ, hτ, j, hj⟩ := exists_fd_irreducible_embedding (principalFixedReduction ρ)
  let f : τ →ₗ[ℂ] V := (principalFixed ρ).subtype.comp j.toLinearMap
  refine ⟨τ, f, ⟨hn, ⟨τ, fdRep_simple_of_ρ_isIrreducible τ hτ, fun _ => rfl⟩, ?_⟩,
    Subtype.val_injective.comp hj, ?_⟩
  · intro a ha han
    have hdeg (b : ℕ) (hab : a + b = n) : res a b τ.character 1 1 = 0 := by
      subst n
      let P := blockProjection ℤ_[p] a (a + b)
      have hP : P * P = P := blockProjection_idempotent _ _ _
      have hJ' : Coinvariants.ker
          (ρ.comp (U (1 - (algebraMap ℤ_[p] ℚ_[p]).mapMatrix P) ((algebraMap ℤ_[p] ℚ_[p]).mapMatrix P)).subtype) = ⊤ := by
        rw [mapMatrix_blockProjection]
        exact hJ a ha han
      apply restriction_degree_zero_of_no_blockRadical_fixed τ.ρ
      intro v hv
      apply hj
      rw [map_zero]
      apply eq_zero_of_residueRadical_fixed ρ hρ hP hJ'
      intro u hu
      rw [← j.isIntertwining]
      rw [mapMatrix_blockProjection] at hu
      rw [hv u hu]
    exact hdeg (n - a) (Nat.add_sub_of_le han.le)
  · intro k v
    change (j (τ.ρ (integralReduction p (Fin n) k) v)).val =
      ρ (integralInclusion p (Fin n) k) (j v).val
    rw [j.isIntertwining, principalFixedReduction_apply]

end GlobalTheory.GLp

#print axioms GlobalTheory.GLp.exists_cuspidal_type_of_jacquetVanishing
