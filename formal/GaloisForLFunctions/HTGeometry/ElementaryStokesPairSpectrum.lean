import GaloisForLFunctions.HTGeometry.AiryTowerStokesRigidity

/-!
# Exact pair spectrum for elementary loopless Stokes circles

This file formalizes the complete two-vertex edge spectrum for elementary circles: an unramified
circle (`r = 1`) or a simple Airy circle (`r > 1`, one consequential level `(r+1)/r`).

`ElementaryPairPresentation` is the finite list of geometric contact mechanisms.  Low contact is
separation at or below the Airy level; high contact is an inconsequential common polynomial term.
The recognition theorem eliminates the presentation and gives the exact arithmetic spectrum.
-/

namespace GaloisForLFunctions
namespace IrregularStokes

/-- Geometric mechanisms producing an edge between two elementary loopless Stokes circles.

The indices are the two ramifications and resulting edge multiplicity.  The constructors are
oriented, so the theorem below does not silently quotient labeled vertices. -/
inductive ElementaryPairPresentation : (leftRamification rightRamification edge : ℕ) → Type
  | unramified (edge : ℕ) : ElementaryPairPresentation 1 1 edge
  | unramifiedAiryBase {r : ℕ} (ramified : 1 < r) : ElementaryPairPresentation 1 r 1
  | unramifiedAiryHigh {r k : ℕ} (ramified : 1 < r) (positiveHeight : 0 < k) :
      ElementaryPairPresentation 1 r (r * k)
  | airyUnramifiedBase {r : ℕ} (ramified : 1 < r) : ElementaryPairPresentation r 1 1
  | airyUnramifiedHigh {r k : ℕ} (ramified : 1 < r) (positiveHeight : 0 < k) :
      ElementaryPairPresentation r 1 (r * k)
  | unequalAiryBase {r s : ℕ} (leftRamified : 1 < r) (rightRamified : 1 < s)
      (unequal : r ≠ s) : ElementaryPairPresentation r s (max r s)
  | unequalAiryHigh {r s k : ℕ} (leftRamified : 1 < r) (rightRamified : 1 < s)
      (unequal : r ≠ s) (positiveHeight : 0 < k) :
      ElementaryPairPresentation r s (r * s * k)
  | equalAiryLow {r edge : ℕ} (ramified : 1 < r) (low : edge ≤ r) :
      ElementaryPairPresentation r r edge
  | equalAiryHigh {r k : ℕ} (ramified : 1 < r) (positiveHeight : 0 < k) :
      ElementaryPairPresentation r r (r ^ (2 : ℕ) * k)

/-- Arithmetic form of the exact elementary pair spectrum. -/
def InElementaryPairSpectrum (r s edge : ℕ) : Prop :=
  (r = 1 ∧ s = 1) ∨
  (r = 1 ∧ 1 < s ∧ (edge = 1 ∨ ∃ k, 0 < k ∧ edge = s * k)) ∨
  (1 < r ∧ s = 1 ∧ (edge = 1 ∨ ∃ k, 0 < k ∧ edge = r * k)) ∨
  (1 < r ∧ 1 < s ∧ r ≠ s ∧
    (edge = max r s ∨ ∃ k, 0 < k ∧ edge = r * s * k)) ∨
  (1 < r ∧ r = s ∧ (edge ≤ r ∨ ∃ k, 0 < k ∧ edge = r ^ (2 : ℕ) * k))

/-- **Exact elementary pair-spectrum theorem.**  The arithmetic list is necessary and sufficient
for a geometric elementary pair presentation. -/
theorem nonempty_elementaryPairPresentation_iff_spectrum (r s edge : ℕ) :
    Nonempty (ElementaryPairPresentation r s edge) ↔ InElementaryPairSpectrum r s edge := by
  constructor
  · rintro ⟨p⟩
    cases p with
    | unramified edge => exact Or.inl ⟨rfl, rfl⟩
    | unramifiedAiryBase hr => exact Or.inr <| Or.inl ⟨rfl, hr, Or.inl rfl⟩
    | unramifiedAiryHigh hr hk =>
        exact Or.inr <| Or.inl ⟨rfl, hr, Or.inr ⟨_, hk, rfl⟩⟩
    | airyUnramifiedBase hr => exact Or.inr <| Or.inr <| Or.inl ⟨hr, rfl, Or.inl rfl⟩
    | airyUnramifiedHigh hr hk =>
        exact Or.inr <| Or.inr <| Or.inl ⟨hr, rfl, Or.inr ⟨_, hk, rfl⟩⟩
    | unequalAiryBase hr hs hne =>
        exact Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨hr, hs, hne, Or.inl rfl⟩
    | unequalAiryHigh hr hs hne hk =>
        exact Or.inr <| Or.inr <| Or.inr <| Or.inl
          ⟨hr, hs, hne, Or.inr ⟨_, hk, rfl⟩⟩
    | equalAiryLow hr hedge =>
        exact Or.inr <| Or.inr <| Or.inr <| Or.inr ⟨hr, rfl, Or.inl hedge⟩
    | equalAiryHigh hr hk =>
        exact Or.inr <| Or.inr <| Or.inr <| Or.inr
          ⟨hr, rfl, Or.inr ⟨_, hk, rfl⟩⟩
  · intro h
    rcases h with h11 | h1s | hr1 | hrs | hrr
    · rcases h11 with ⟨rfl, rfl⟩
      exact ⟨ElementaryPairPresentation.unramified edge⟩
    · rcases h1s with ⟨rfl, hs, rfl | ⟨k, hk, rfl⟩⟩
      · exact ⟨ElementaryPairPresentation.unramifiedAiryBase hs⟩
      · exact ⟨ElementaryPairPresentation.unramifiedAiryHigh hs hk⟩
    · rcases hr1 with ⟨hr, rfl, rfl | ⟨k, hk, rfl⟩⟩
      · exact ⟨ElementaryPairPresentation.airyUnramifiedBase hr⟩
      · exact ⟨ElementaryPairPresentation.airyUnramifiedHigh hr hk⟩
    · rcases hrs with ⟨hr, hs, hne, rfl | ⟨k, hk, rfl⟩⟩
      · exact ⟨ElementaryPairPresentation.unequalAiryBase hr hs hne⟩
      · exact ⟨ElementaryPairPresentation.unequalAiryHigh hr hs hne hk⟩
    · rcases hrr with ⟨hr, rfl, hedge | ⟨k, hk, rfl⟩⟩
      · exact ⟨ElementaryPairPresentation.equalAiryLow hr hedge⟩
      · exact ⟨ElementaryPairPresentation.equalAiryHigh hr hk⟩

/-- Closed form when both simple Airy circles have the same ramification. -/
theorem equalAiry_spectrum_iff {r edge : ℕ} (hr : 1 < r) :
    InElementaryPairSpectrum r r edge ↔
      edge ≤ r ∨ ∃ k, 0 < k ∧ edge = r ^ (2 : ℕ) * k := by
  simp [InElementaryPairSpectrum, hr, (ne_of_gt hr)]

/-- Closed form when two simple Airy circles have unequal ramifications. -/
theorem unequalAiry_spectrum_iff {r s edge : ℕ} (hr : 1 < r) (hs : 1 < s) (hne : r ≠ s) :
    InElementaryPairSpectrum r s edge ↔
      edge = max r s ∨ ∃ k, 0 < k ∧ edge = r * s * k := by
  simp [InElementaryPairSpectrum, hr, hs, (ne_of_gt hr), (ne_of_gt hs), hne]

/-- Closed form for an unramified/simple-Airy pair. -/
theorem unramifiedAiry_spectrum_iff {r edge : ℕ} (hr : 1 < r) :
    InElementaryPairSpectrum 1 r edge ↔
      edge = 1 ∨ ∃ k, 0 < k ∧ edge = r * k := by
  simp [InElementaryPairSpectrum, hr, (ne_of_gt hr)]

end IrregularStokes
end GaloisForLFunctions
