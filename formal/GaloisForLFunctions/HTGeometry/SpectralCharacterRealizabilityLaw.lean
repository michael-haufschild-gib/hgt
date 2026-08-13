import GaloisForLFunctions.HTGeometry.ValuatedSpectralCharacterLaw

/-!
# Exact realizability of spectral-character birth

An arbitrary supplied jet need not activate a projective character, and the zero character can
never be active.  This file proves the sharp universal realization law: every nonzero projective
character can be made active at any prescribed birth order by a single-coordinate spectral jet.
-/

namespace GaloisForLFunctions.HTGeometry

/-- **Prescribed-birth realizability law.**  A spectral jet on which `k` is active with exact birth
order `r` exists precisely when `k` is nonzero. -/
theorem exists_spectralCharacterActive_birthOrder_eq_iff_ne_zero
    {I : Type*} (k : ProjectiveCharacter I) (r : ℕ) :
    (∃ (jet : ℕ → I → ℂ) (hactive : SpectralCharacterActive jet k),
      spectralCharacterBirthOrder jet k hactive = r) ↔ k ≠ 0 := by
  constructor
  · rintro ⟨jet, hactive, -⟩ rfl
    obtain ⟨n, hn⟩ := hactive
    exact hn (map_zero (projectiveSpectralRelationJet jet n))
  · intro hk
    classical
    obtain ⟨i₀, hi₀⟩ : ∃ i, k.1 i ≠ 0 := by
      by_contra hall
      push Not at hall
      apply hk
      apply Subtype.ext
      exact Finsupp.ext hall
    let jet : ℕ → I → ℂ := fun n i => if n = r ∧ i = i₀ then 1 else 0
    have hbefore {n : ℕ} (hn : n < r) :
        projectiveSpectralRelationJet jet n k = 0 := by
      classical
      simp [projectiveSpectralRelationJet, spectralRelationJet, jet, ne_of_lt hn]
    have hat : projectiveSpectralRelationJet jet r k = (k.1 i₀ : ℂ) := by
      classical
      simp [projectiveSpectralRelationJet, spectralRelationJet, jet, hi₀]
    have hat_ne : projectiveSpectralRelationJet jet r k ≠ 0 := by
      rw [hat]
      exact Int.cast_ne_zero.mpr hi₀
    let hactive : SpectralCharacterActive jet k := ⟨r, hat_ne⟩
    refine ⟨jet, hactive, ?_⟩
    apply (Nat.find_eq_iff hactive).2
    exact ⟨hat_ne, fun n hn hne => hne (hbefore hn)⟩

/-- A projective character is realizable as active for some jet exactly when it is nonzero. -/
theorem exists_spectralCharacterActive_iff_ne_zero {I : Type*} (k : ProjectiveCharacter I) :
    (∃ jet : ℕ → I → ℂ, SpectralCharacterActive jet k) ↔ k ≠ 0 := by
  constructor
  · rintro ⟨jet, hactive⟩ rfl
    obtain ⟨n, hn⟩ := hactive
    exact hn (map_zero (projectiveSpectralRelationJet jet n))
  · intro hk
    obtain ⟨jet, hactive, -⟩ :=
      (exists_spectralCharacterActive_birthOrder_eq_iff_ne_zero k 0).2 hk
    exact ⟨jet, hactive⟩

end GaloisForLFunctions.HTGeometry
