import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.LocalLanglands.FiniteCuspidalTypeIrreducible
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CharacterTheory.HarishChandraCuspidalRestriction
import Mathlib.RepresentationTheory.Character

/-! The finite dual inverts the character argument. Inversion
permutes the identity fiber of the Levi map, so it preserves
vanishing of the Harish–Chandra restriction at the identity. -/

noncomputable section

open Matrix Representation CategoryTheory
open GaloisForLFunctions WindowedLandauTheory.MainNotions.ArithmeticCylinders
open scoped Classical

namespace GlobalTheory.GLq

variable {p n : ℕ} [Fact p.Prime]

def finiteTypeDual (τ : FDRep ℂ (Gn p n)) : FDRep ℂ (Gn p n) := FDRep.of (Representation.dual τ.ρ)

@[simp] theorem finiteTypeDual_character (τ : FDRep ℂ (Gn p n)) (g : Gn p n) :
    (finiteTypeDual τ).character g = τ.character g⁻¹ := FDRep.char_dual τ g

theorem isCusp_finiteTypeDual (τ : FDRep ℂ (Gn p n)) (hτ : IsCusp τ.character) :
    IsCusp (finiteTypeDual τ).character := by
  refine ⟨hτ.1, ?_, fun a ha han => ?_⟩
  · obtain ⟨V, hV, hχ⟩ := hτ.2.1
    refine ⟨finiteTypeDual V, ?_, fun x => ?_⟩
    · rw [FDRep.simple_iff_char_is_norm_one] at hV ⊢
      rw [← hV]
      simp only [finiteTypeDual_character, inv_inv]
      exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
    · rw [finiteTypeDual_character, finiteTypeDual_character, hχ]
  · have he : n = a + (n - a) := by omega
    obtain ⟨b, rfl⟩ : ∃ b, n = a + b := ⟨n - a, he⟩
    have hvan := hτ.2.2 a ha han
    rw [Nat.add_sub_cancel_left, res_eq_sum_diagonal_fibre] at hvan ⊢
    let P := twoBlockParabolic p a b
    let f (x : P) := if twoBlockLevi x = (1, 1) then (finiteTypeDual τ).character x.val else 0
    let g (x : P) := if twoBlockLevi x = (1, 1) then τ.character x.val else 0
    have hsum : (∑ x, f x) = ∑ x, g x := by
      refine Fintype.sum_equiv (Equiv.inv P) f g fun x => ?_
      simp only [f, g, Equiv.inv_apply, finiteTypeDual_character, Subgroup.coe_inv, map_inv]
      exact if_congr (inv_eq_one (a := twoBlockLevi x)).symm rfl rfl
    exact (congrArg (((p : ℂ) ^ (a * b))⁻¹ * ·) hsum).trans hvan

end GlobalTheory.GLq

#print axioms GlobalTheory.GLq.isCusp_finiteTypeDual
