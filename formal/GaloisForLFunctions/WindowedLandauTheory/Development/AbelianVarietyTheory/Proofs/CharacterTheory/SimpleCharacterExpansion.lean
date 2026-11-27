import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CharacterTheory.VirtualCharacterNorm
import GaloisForLFunctions.RHTower.Artin.ArtinInducedSpanDescent
import Mathlib.LinearAlgebra.Span.Basic

/-! Coefficients in the simple-character expansion are the normalized pairings.
Two genuine characters have nonzero pairing exactly when they share a simple constituent. -/

open GaloisForLFunctions

namespace GlobalTheory.CuspGL

variable {G : Type} [Group G] [Fintype G]

private theorem summation_over_simple {χ : G → ℂ} (hχ : χ ∈ virtualCharacterGroup G) :
    ∃ S : Finset (G → ℂ), (↑S : Set (G → ℂ)) ⊆ simpleCharacterSet G ∧
      ∀ η : G → ℂ, characterPairing G χ η =
        ∑ α ∈ S, characterPairing G χ α * characterPairing G α η := by
  classical
  have hspan : χ ∈ Submodule.span ℤ (simpleCharacterSet G) := by
    rw [← AddSubgroup.toIntSubmodule_closure, ← virtualCharacterGroup_eq_simple_span]
    exact hχ
  obtain ⟨S, hS, hs⟩ := Submodule.mem_span_finite_of_mem_span hspan
  have hs' : χ ∈ AddSubgroup.closure (S : Set (G → ℂ)) := by
    change χ ∈ (AddSubgroup.closure (S : Set (G → ℂ))).toIntSubmodule
    rwa [AddSubgroup.toIntSubmodule_closure]
  have hχsum : ∀ x, ∑ α ∈ S, characterPairing G χ α * α x = χ x := by
    refine AddSubgroup.closure_induction
      (p := fun φ _ => ∀ x, ∑ α ∈ S, characterPairing G φ α * α x = φ x)
      ?_ ?_ ?_ ?_ hs'
    · intro α ha x
      have hα := hS ha
      rw [Finset.sum_eq_single_of_mem α ha]
      · rw [pairing_simple hα hα, if_pos rfl, one_mul]
      · intro β hb hba
        rw [pairing_simple hα (hS hb), if_neg hba.symm, zero_mul]
    · intro x
      simp
    · intro α β _ _ ha hb x
      simp only [characterPairing_add_left, add_mul, Finset.sum_add_distrib, ha x, hb x,
        Pi.add_apply]
    · intro α _ ha x
      simp only [characterPairing_neg_left, neg_mul, Finset.sum_neg_distrib, ha x,
        Pi.neg_apply]
  refine ⟨S, hS, fun η => ?_⟩
  calc
    characterPairing G χ η =
        characterPairing G (fun x => ∑ α ∈ S, characterPairing G χ α * α x) η :=
      congrArg (fun φ => characterPairing G φ η) (funext hχsum).symm
    _ = characterPairing G (fun x => ∑ α : S, characterPairing G χ α.val * α.val x) η := by
      congr 1
      funext x
      rw [Finset.univ_eq_attach]
      exact (Finset.sum_attach S (fun α : G → ℂ => characterPairing G χ α * α x)).symm
    _ = ∑ α : S, characterPairing G χ α.val * characterPairing G α.val η :=
      characterPairing_sum_mul_left (G := G) (fun α : S => characterPairing G χ α.val)
        (fun α : S => α.val) η
    _ = _ := by
      rw [Finset.univ_eq_attach]
      exact Finset.sum_attach S (fun α : G → ℂ => characterPairing G χ α * characterPairing G α η)

/-- Nonzero pairing with an integral virtual character detects a simple character
that pairs nontrivially with both functions. -/
theorem exists_common_simple_of_pairing_ne_zero {χ η : G → ℂ}
    (hχ : χ ∈ virtualCharacterGroup G) (h : characterPairing G χ η ≠ 0) :
    ∃ α ∈ simpleCharacterSet G, characterPairing G χ α ≠ 0 ∧ characterPairing G η α ≠ 0 := by
  obtain ⟨S, hS, hsum⟩ := summation_over_simple hχ
  by_contra! hnone
  apply h
  rw [hsum η]
  refine Finset.sum_eq_zero fun α ha => ?_
  by_cases hzero : characterPairing G χ α = 0
  · rw [hzero, zero_mul]
  · rw [characterPairing_comm G α η, hnone α (hS ha) hzero, mul_zero]

/-- If a simple character pairs nontrivially with two genuine characters, the
pairing of those genuine characters is nonzero. -/
theorem pairing_ne_zero_of_common_simple (χ η : GenuineCharacter G) {α : G → ℂ}
    (hα : α ∈ simpleCharacterSet G) (hχα : characterPairing G χ.val α ≠ 0)
    (hηα : characterPairing G η.val α ≠ 0) : characterPairing G χ.val η.val ≠ 0 := by
  classical
  obtain ⟨S, hS, hsum⟩ := summation_over_simple
    (genuineCharacterMonoid_le_virtualCharacterGroup G χ.property)
  have ha : α ∈ S := by
    by_contra hn
    apply hχα
    rw [hsum α]
    refine Finset.sum_eq_zero fun β hb => ?_
    have hba : β ≠ α := fun e => hn (e ▸ hb)
    rw [pairing_simple (hS hb) hα, if_neg hba, mul_zero]
  have natTerms (β : G → ℂ) (hβ : β ∈ simpleCharacterSet G) :
      ∃ a b : ℕ, characterPairing G χ.val β = a ∧ characterPairing G β η.val = b := by
    have hgen : β ∈ genuineCharacterMonoid G := by
      obtain ⟨V, _, rfl⟩ := hβ
      exact AddSubmonoid.subset_closure ⟨V, rfl⟩
    obtain ⟨a, hna⟩ := genuineCharacterPairing_eq_natCast G χ ⟨β, hgen⟩
    obtain ⟨b, hnb⟩ := genuineCharacterPairing_eq_natCast G ⟨β, hgen⟩ η
    exact ⟨a, b, hna, hnb⟩
  have hpos : 0 < (characterPairing G χ.val α * characterPairing G α η.val).re := by
    obtain ⟨a, b, ha', hb'⟩ := natTerms α hα
    have an : a ≠ 0 := fun e => hχα (by simpa only [e, Nat.cast_zero] using ha')
    have bn : b ≠ 0 := fun e => hηα (by
      simpa only [e, Nat.cast_zero, characterPairing_comm G η.val α] using hb')
    rw [ha', hb', ← Nat.cast_mul, Complex.natCast_re]
    exact_mod_cast Nat.mul_pos (Nat.pos_of_ne_zero an) (Nat.pos_of_ne_zero bn)
  have hle :
      (characterPairing G χ.val α * characterPairing G α η.val).re ≤
        ∑ β ∈ S, (characterPairing G χ.val β * characterPairing G β η.val).re := by
    refine Finset.single_le_sum (f := fun β : G → ℂ =>
      (characterPairing G χ.val β * characterPairing G β η.val).re) (fun β hb => ?_) ha
    obtain ⟨a, b, ea, eb⟩ := natTerms β (hS hb)
    rw [ea, eb, ← Nat.cast_mul, Complex.natCast_re]
    exact Nat.cast_nonneg _
  have hp : 0 < (characterPairing G χ.val η.val).re := by
    rw [hsum η.val, Complex.re_sum]
    exact hpos.trans_le hle
  intro e
  rw [e, Complex.zero_re] at hp
  exact (lt_irrefl 0) hp

end GlobalTheory.CuspGL
