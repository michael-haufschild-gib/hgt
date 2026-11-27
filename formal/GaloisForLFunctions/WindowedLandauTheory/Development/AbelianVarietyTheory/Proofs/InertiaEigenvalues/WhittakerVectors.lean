import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WhittakerCharacter

/-! Whittaker projection traces compute the dimension of the space of
vectors transforming by the unitriangular character. -/

noncomputable section
open scoped Classical

open GaloisForLFunctions WindowedLandauTheory.MainNotions.ArithmeticCylinders

namespace GlobalTheory.GLq

variable {g n : ℕ} [Fact g.Prime]

/-- Frobenius reciprocity identifies the Whittaker trace with the dimension of
the equivariant maps from the one-dimensional Whittaker representation. -/
theorem wh_eq_finrank (ψ : AddChar (ZMod g) ℂ) (V : FDRep ℂ (Gn g n)) :
    wh ψ V.character = (Module.finrank ℂ
      ((linearCharacterRepresentation (whittakerCharacter ψ n)).IntertwiningMap
        (V.ρ.comp (upperUnitriangular g n).subtype)) : ℂ) := by
  have hp : ip V.character (gg ψ n) =
      characterPairing (Gn g n) (gg ψ n) V.character := by
    rw [ip, characterPairing, Nat.card_eq_fintype_card]
  calc
    wh ψ V.character = ip V.character (gg ψ n) :=
      (ip_gg ψ n V.character (fun x y => V.char_conj x y)).symm
    _ = _ := hp
    _ = _ := by
      rw [gg_eq_monomialCharacter]
      exact (monomialCharacter_pairing_eq_restricted _ _ _ V.ρ).trans
        (representationCharacterPairing_eq_finrank (upperUnitriangular g n)
          (linearCharacterRepresentation (whittakerCharacter ψ n))
          (V.ρ.comp (upperUnitriangular g n).subtype))

/-- A nonzero Whittaker vector gives a nonzero Whittaker projection trace. -/
theorem wh_ne_zero_of_vector (ψ : AddChar (ZMod g) ℂ) (V : FDRep ℂ (Gn g n))
    (v : V) (hv : v ≠ 0)
    (h : ∀ u : upperUnitriangular g n, V.ρ u.val v = (whittakerCharacter ψ n u : ℂ) • v) :
    wh ψ V.character ≠ 0 := by
  let U := upperUnitriangular g n
  let χ := whittakerCharacter ψ n
  let τ := linearCharacterRepresentation χ
  let σ := V.ρ.comp U.subtype
  let F : τ.IntertwiningMap σ :=
    LinearMap.intertwiningMap_of_isIntertwiningMap τ σ
      ((LinearMap.id : ℂ →ₗ[ℂ] ℂ).smulRight v) (fun u a => by
        change ((χ u : ℂ) * a) • v = V.ρ u.val (a • v)
        rw [map_smul, h u, smul_smul, mul_comm])
  have hF : F ≠ 0 := by
    intro h0
    have h1 : (1 : ℂ) • v = 0 := congrArg (fun I : τ.IntertwiningMap σ => I 1) h0
    exact hv ((one_smul ℂ v).symm.trans h1)
  letI : Nontrivial (τ.IntertwiningMap σ) := ⟨⟨F, 0, hF⟩⟩
  rw [wh_eq_finrank]
  exact Nat.cast_ne_zero.mpr (Module.finrank_pos : 0 < Module.finrank ℂ
    (τ.IntertwiningMap σ)).ne'

end GlobalTheory.GLq
