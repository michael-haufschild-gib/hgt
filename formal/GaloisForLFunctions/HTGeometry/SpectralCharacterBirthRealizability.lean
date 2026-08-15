import GaloisForLFunctions.HTGeometry.ValuatedSpectralCharacterLaw

/-!
# Exact prescribed-birth realizability of spectral-character activity

A projective phase character is activated by a spectral jet exactly when it is nonzero, and the
depth at which it is activated can be prescribed arbitrarily.  The witness is a coordinate
functional: put a single unit at the prescribed order on one label where the character has a nonzero
coefficient, and zero everywhere else.

The zero character can never be activated, because every additive character functional vanishes on
it, so the criterion is sharp.
-/

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

section BirthRealizability

variable {I : Type*} [DecidableEq I]

/-- The coordinate jet that activates a label at a prescribed order. -/
noncomputable def coordinateSpectralJet (r : ℕ) (i₀ : I) : ℕ → I → ℂ :=
  fun n i => if n = r ∧ i = i₀ then 1 else 0

theorem projectiveSpectralRelationJet_coordinateSpectralJet_of_ne
    {r n : ℕ} (hn : n ≠ r) (i₀ : I) (k : ProjectiveCharacter I) :
    projectiveSpectralRelationJet (coordinateSpectralJet r i₀) n k = 0 := by
  classical
  have hzero : ∀ i : I, coordinateSpectralJet r i₀ n i = 0 := by
    intro i
    rw [coordinateSpectralJet, if_neg (fun h => hn h.1)]
  show ((k : I →₀ ℤ).sum fun i m => (m : ℂ) * coordinateSpectralJet r i₀ n i) = 0
  refine Finset.sum_eq_zero fun i _ => ?_
  show (((k : I →₀ ℤ) i : ℤ) : ℂ) * coordinateSpectralJet r i₀ n i = 0
  rw [hzero i, mul_zero]

theorem projectiveSpectralRelationJet_coordinateSpectralJet_self
    (r : ℕ) {i₀ : I} {k : ProjectiveCharacter I} (hi₀ : (k : I →₀ ℤ) i₀ ≠ 0) :
    projectiveSpectralRelationJet (coordinateSpectralJet r i₀) r k =
      (((k : I →₀ ℤ) i₀ : ℤ) : ℂ) := by
  classical
  have hterm : ∀ i : I, ((((k : I →₀ ℤ) i : ℤ) : ℂ) * coordinateSpectralJet r i₀ r i) =
      if i = i₀ then (((k : I →₀ ℤ) i : ℤ) : ℂ) else 0 := by
    intro i
    by_cases hi : i = i₀
    · rw [coordinateSpectralJet, if_pos ⟨rfl, hi⟩, mul_one, if_pos hi]
    · rw [coordinateSpectralJet, if_neg (fun h => hi h.2), mul_zero, if_neg hi]
  show ((k : I →₀ ℤ).sum fun i m => (m : ℂ) * coordinateSpectralJet r i₀ r i) = _
  rw [Finsupp.sum, Finset.sum_congr rfl fun i _ => hterm i,
    Finset.sum_ite_eq' (k : I →₀ ℤ).support i₀ (fun i => (((k : I →₀ ℤ) i : ℤ) : ℂ)),
    if_pos (Finsupp.mem_support_iff.mpr hi₀)]

theorem spectralCharacterActive_coordinateSpectralJet (r : ℕ) {i₀ : I}
    {k : ProjectiveCharacter I} (hi₀ : (k : I →₀ ℤ) i₀ ≠ 0) :
    SpectralCharacterActive (coordinateSpectralJet r i₀) k := by
  refine ⟨r, ?_⟩
  rw [projectiveSpectralRelationJet_coordinateSpectralJet_self r hi₀]
  exact_mod_cast hi₀

/-- **Exact prescribed-birth realizability.**  A projective character can be activated at a
prescribed birth order exactly when it is nonzero. -/
theorem exists_spectralCharacterActive_birthOrder_eq_iff_ne_zero
    (k : ProjectiveCharacter I) (r : ℕ) :
    (∃ jet : ℕ → I → ℂ, ∃ hactive : SpectralCharacterActive jet k,
      spectralCharacterBirthOrder jet k hactive = r) ↔ k ≠ 0 := by
  classical
  constructor
  · rintro ⟨jet, hactive, -⟩ hk
    obtain ⟨n, hn⟩ := hactive
    exact hn (by rw [hk, map_zero])
  · intro hk
    have hne : (k : I →₀ ℤ) ≠ 0 := fun h => hk (Subtype.ext h)
    obtain ⟨i₀, hi₀⟩ := Finsupp.ne_iff.mp hne
    rw [Finsupp.coe_zero, Pi.zero_apply] at hi₀
    refine ⟨coordinateSpectralJet r i₀, spectralCharacterActive_coordinateSpectralJet r hi₀, ?_⟩
    rw [spectralCharacterBirthOrder]
    refine Nat.find_eq_iff _ |>.mpr ⟨?_, fun m hm => ?_⟩
    · rw [projectiveSpectralRelationJet_coordinateSpectralJet_self r hi₀]
      exact_mod_cast hi₀
    · simp only [not_not]
      exact projectiveSpectralRelationJet_coordinateSpectralJet_of_ne (by omega) i₀ k

end BirthRealizability

end GaloisForLFunctions.HTGeometry
