import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CharacterTheory.InducedCharacterDoubleCosets
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CharacterTheory.TwoBlockHarishChandraInduction
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WhittakerCharacter

/-! Whittaker traces of Harish–Chandra induction reduce to pairings
on the intersections of the unitriangular subgroup with conjugate parabolics. -/

noncomputable section
open scoped Classical

open GaloisForLFunctions WindowedLandauTheory.MainNotions.ArithmeticCylinders

namespace GaloisForLFunctions

/-- A nontrivial linear character cancels the overlap sum when a translation
preserving the right function acts with a nontrivial weight on the left. -/
theorem doubleCosetPairing_linear_eq_zero_of_invariance {G : Type*} [Group G] [Fintype G]
    (H K : Subgroup G) (χ : LinearCharacter H) (β : K → ℂ) (x : G)
    [Fintype (doubleCosetOverlap H K x)]
    (z : doubleCosetOverlap H K x) (hz : χ z.val ≠ 1)
    (hβ : ∀ u : doubleCosetOverlap H K x,
      β (doubleCosetOverlapConj H K x z * doubleCosetOverlapConj H K x u) =
        β (doubleCosetOverlapConj H K x u)) :
    doubleCosetPairing H K (fun u => (χ u : ℂ)) β x = 0 := by
  let O := doubleCosetOverlap H K x
  let c : ℂ := χ z.val⁻¹
  let F (u : O) : ℂ := β (doubleCosetOverlapConj H K x u) * (χ u.val⁻¹ : ℂ)
  have hc : c ≠ 1 := by
    intro h
    have e : χ z.val⁻¹ = 1 := Units.ext h
    rw [map_inv, inv_eq_one] at e
    exact hz e
  have hF (u : O) : F (z * u) = c * F u := by
    dsimp only [F, c]
    rw [map_mul, hβ]
    change β (doubleCosetOverlapConj H K x u) * (χ (z.val * u.val)⁻¹ : ℂ) = _
    rw [mul_inv_rev, map_mul, Units.val_mul]
    ring
  have hsum : (∑ u : O, F u) = c * ∑ u : O, F u := by
    calc
      _ = ∑ u : O, F (z * u) := (Equiv.sum_comp (Equiv.mulLeft z) F).symm
      _ = _ := by simp only [hF, Finset.mul_sum]
  have hzero : ∑ u : O, F u = 0 := by
    have he : (1 - c) * ∑ u : O, F u = 0 := by
      rw [sub_mul, one_mul, ← hsum, sub_self]
    exact (mul_eq_zero.mp he).resolve_left (sub_ne_zero.mpr (Ne.symm hc))
  rw [doubleCosetPairing_eq_pairing H K]
  change (Nat.card O : ℂ)⁻¹ * (∑ u : O, F u) = 0
  rw [hzero, mul_zero]

end GaloisForLFunctions

namespace GlobalTheory.GLq

variable {g a b : ℕ} [Fact g.Prime]

/-- The contributions to the Whittaker trace of an induced block character
are indexed by unitriangular–parabolic double cosets. -/
theorem wh_hc_eq_doubleCosets (ψ : AddChar (ZMod g) ℂ) {α : Gn g a → ℂ} {β : Gn g b → ℂ}
    (hα : IsChar α) (hβ : IsChar β) :
    let U := upperUnitriangular g (a + b)
    let P := twoBlockParabolic g a b
    letI := mixedDoubleCosetFintype U P
    wh ψ (hc a b α β (a + b)) =
      ∑ q : DoubleCoset.Quotient (U : Set (Gn g (a + b))) P,
        doubleCosetPairing U P (fun u => (whittakerCharacter ψ (a + b) u : ℂ))
          (fun p => α (twoBlockLevi p).1 * β (twoBlockLevi p).2) q.out := by
  let U := upperUnitriangular g (a + b)
  let P := twoBlockParabolic g a b
  let π : P →* Gn g a × Gn g b := twoBlockLevi
  let χ : Gn g (a + b) → ℂ := hc a b α β (a + b)
  have hclass : IsClass χ := by
    obtain ⟨V, hV⟩ := isChar_hc hα hβ
    intro x y
    exact (hV (y * x * y⁻¹)).symm.trans ((V.char_conj x y).trans (hV x))
  have hp : wh ψ χ = characterPairing (Gn g (a + b)) (gg ψ (a + b)) χ := by
    rw [← ip_gg ψ (a + b) χ hclass, ip, characterPairing, Nat.card_eq_fintype_card]
  obtain ⟨V, hV⟩ := hα
  obtain ⟨W, hW⟩ := hβ
  let ρ := linearCharacterRepresentation (whittakerCharacter ψ (a + b))
  let σ := Representation.tprod (V.ρ.comp ((MonoidHom.fst _ _).comp π))
    (W.ρ.comp ((MonoidHom.snd _ _).comp π))
  have hρ : Representation.character ρ = (fun u : U => (whittakerCharacter ψ (a + b) u : ℂ)) :=
    funext (linearCharacterRepresentation_character _)
  have hσ : Representation.character σ = (fun p : P => α (π p).1 * β (π p).2) := by
    funext p
    change (Representation.tprod (V.ρ.comp ((MonoidHom.fst _ _).comp π))
      (W.ρ.comp ((MonoidHom.snd _ _).comp π))).character p = _
    rw [Representation.char_tensor, Pi.mul_apply]
    exact congrArg₂ (· * ·) (hV (π p).1) (hW (π p).2)
  have hGG : gg ψ (a + b) = inducedFunction U (Representation.character ρ) :=
    (gg_eq_inducedFunction ψ (a + b)).trans (congrArg (inducedFunction U) hρ.symm)
  have hHC : χ = inducedFunction P (Representation.character σ) :=
    (hc_eq_inducedFunction α β).trans (congrArg (inducedFunction P) hσ.symm)
  exact (hp.trans (congrArg₂ (characterPairing (Gn g (a + b))) hGG hHC)).trans (by
    simpa only [hρ, hσ] using characterPairing_induced_doubleCosets U P ρ σ)

end GlobalTheory.GLq
