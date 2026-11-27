import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CharacterTheory.HarishChandraCuspidalRestriction
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CharacterTheory.InducedCharacterDoubleCosets

/-! Averaging over a proper parabolic radical annihilates translates of a
cuspidal character and cancels the corresponding double-coset pairing. -/

noncomputable section
open scoped Classical

namespace GaloisForLFunctions

/-- An overlap pairing vanishes if the average of its summand over
every translate of a finite group acting from the left vanishes. -/
theorem doubleCosetPairing_eq_zero_of_overlap_average
    {G N : Type*} [Group G] [Fintype G] [Group N] [Fintype N]
    (H K : Subgroup G) (α : H → ℂ) (β : K → ℂ) (x : G)
    [Fintype (doubleCosetOverlap H K x)] (m : N →* doubleCosetOverlap H K x)
    (h : ∀ u : doubleCosetOverlap H K x,
      (∑ z : N, β (doubleCosetOverlapConj H K x (m z * u)) * α (m z * u).val⁻¹) = 0) :
    doubleCosetPairing H K α β x = 0 := by
  let O := doubleCosetOverlap H K x
  let F (u : O) := β (doubleCosetOverlapConj H K x u) * α u.val⁻¹
  have hAvg (u : O) : ∑ z : N, F (m z * u) = 0 := h u
  have hsum : (Fintype.card N : ℂ) * (∑ u : O, F u) = 0 := by
    calc
      _ = ∑ _ : N, ∑ u : O, F u := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ = ∑ z : N, ∑ u : O, F (m z * u) :=
        Finset.sum_congr rfl fun z _ => (Equiv.sum_comp (Equiv.mulLeft (m z)) F).symm
      _ = ∑ u : O, ∑ z : N, F (m z * u) := Finset.sum_comm
      _ = 0 := Finset.sum_eq_zero fun u _ => hAvg u
  have hz : ∑ u : O, F u = 0 :=
    (mul_eq_zero.mp hsum).resolve_left (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
  rw [doubleCosetPairing_eq_pairing]
  change (Nat.card O : ℂ)⁻¹ * (∑ u : O, F u) = 0
  rw [hz, mul_zero]

end GaloisForLFunctions

namespace GlobalTheory.GLq

variable {g a b : ℕ} [Fact g.Prime]

/-- Every translate of a cuspidal character has zero sum over a proper parabolic radical. -/
theorem sum_cuspidal_radical_translate_eq_zero {χ : Gn g (a + b) → ℂ} (hχ : IsCusp χ)
    (ha : 0 < a) (hb : 0 < b) (z : Gn g (a + b))
    [Fintype (twoBlockLevi (g := g) (a := a) (b := b)).ker] :
    ∑ u : (twoBlockLevi (g := g) (a := a) (b := b)).ker, χ (z * u.val.val) = 0 := by
  let P := twoBlockParabolic g a b
  let N := (twoBlockLevi (g := g) (a := a) (b := b)).ker
  obtain ⟨V, _, hV⟩ := hχ.2.1
  have eχ : V.character = χ := funext hV
  have h0 : res a b V.character 1 1 = 0 := by
    rw [eχ]
    have hd := congrArg (fun k : ℕ => res a k χ (1 : Gn g a) (1 : Gn g k))
      (Nat.add_sub_cancel_left a b)
    exact hd.symm.trans (hχ.2.2 a ha (Nat.lt_add_of_pos_right hb))
  let ρ := V.ρ
  let ν : Representation ℂ N V := ρ.comp (P.subtype.comp N.subtype)
  let S : Module.End ℂ V := ∑ u : N, ν u
  have hS : S = 0 := by
    ext v
    change S v = 0
    apply eq_zero_of_leviKernel_fixed ρ h0
    intro w
    change ν w (S v) = S v
    have hw : ν w * S = S := by
      change ν w * (∑ u : N, ν u) = ∑ u : N, ν u
      rw [Finset.mul_sum]
      simp only [← map_mul]
      exact Equiv.sum_comp (Equiv.mulLeft w) ν
    exact congrArg (fun f : Module.End ℂ V => f v) hw
  calc
    _ = ∑ u : N, LinearMap.trace ℂ V (ρ z * ν u) := by
      refine Finset.sum_congr rfl fun u _ => ?_
      rw [← hV (z * u.val.val)]
      exact congrArg (LinearMap.trace ℂ V) (map_mul ρ z u.val.val)
    _ = LinearMap.trace ℂ V (ρ z * S) := by
      change (∑ u : N, LinearMap.trace ℂ V (ρ z * ν u)) =
        LinearMap.trace ℂ V (ρ z * ∑ u : N, ν u)
      rw [Finset.mul_sum, map_sum]
    _ = 0 := by rw [hS, mul_zero, map_zero]

end GlobalTheory.GLq
