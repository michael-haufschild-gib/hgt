import GaloisForLFunctions.HTGeometry.FiniteContactDendrogram
import GaloisForLFunctions.HTGeometry.StokesEnergyTree

/-!
# Canonical threshold cuts from finite highest-difference contacts

A bounded integral highest-difference matrix satisfying symmetry and the acute-isosceles law
determines its rooted cut geometry without an independently supplied tree or cut certificate.
At every positive integer threshold, the strict contact relation is a finite partition.  One cut
for each partition class, with length the reciprocal common-cover degree, telescopes exactly to
the normalized contact matrix.  The first threshold gives all pendant singleton cuts.
-/

open scoped BigOperators

namespace GaloisForLFunctions
namespace IrregularStokes

noncomputable section

/-- Integral finite contact data on a common ramified cover.  The numerator is the leading
difference degree; division by `coverDegree` gives the normalized Puiseux contact. -/
structure NatContactDendrogram (m K N : ℕ) where
  contactNumerator : Fin m → Fin m → ℕ
  coverDegree_pos : 0 < N
  contact_self : ∀ i, contactNumerator i i = 0
  contact_symm : ∀ i j, contactNumerator i j = contactNumerator j i
  contact_acute : FiniteContactDendrogram.IsAcute contactNumerator
  contact_pos_of_ne : ∀ {i j}, i ≠ j → 0 < contactNumerator i j
  contact_le : ∀ i j, contactNumerator i j ≤ K

namespace NatContactDendrogram

variable {m K N : ℕ}

/-- Strict threshold partition at integral level `t + 1`. -/
def thresholdSetoid (d : NatContactDendrogram m K N) (t : Fin (K + 1)) :
    Setoid (Fin m) :=
  FiniteContactDendrogram.strictThresholdSetoid d.contactNumerator
    d.contact_symm d.contact_acute (t.val + 1)

/-- Class of a branch at one strict threshold. -/
def thresholdClass (d : NatContactDendrogram m K N) (t : Fin (K + 1))
    (i : Fin m) : Quotient (d.thresholdSetoid t) :=
  Quotient.mk _ i

/-- Two branches share a threshold class exactly above their highest-difference numerator. -/
theorem thresholdClass_eq_iff (d : NatContactDendrogram m K N)
    (t : Fin (K + 1)) (i j : Fin m) :
    d.thresholdClass t i = d.thresholdClass t j ↔
      d.contactNumerator i j < t.val + 1 := by
  rw [show d.thresholdClass t i = d.thresholdClass t j ↔
      i = j ∨ d.contactNumerator i j < t.val + 1 by
    exact FiniteContactDendrogram.thresholdClass_eq_iff
      d.contactNumerator d.contact_symm d.contact_acute (t.val + 1) i j]
  constructor
  · rintro (rfl | h)
    · simp [d.contact_self]
    · exact h
  · exact Or.inr

noncomputable instance thresholdClassFintype (d : NatContactDendrogram m K N)
    (t : Fin (K + 1)) : Fintype (Quotient (d.thresholdSetoid t)) :=
  Fintype.ofFinite _

/-- One canonical cut index for every threshold class. -/
abbrev ThresholdEdge (d : NatContactDendrogram m K N) :=
  Σ t : Fin (K + 1), Quotient (d.thresholdSetoid t)

/-- Canonical finite numbering of threshold-class cuts. -/
noncomputable def edgeEquiv (d : NatContactDendrogram m K N) :
    d.ThresholdEdge ≃ Fin (Fintype.card d.ThresholdEdge) :=
  Fintype.equivFin d.ThresholdEdge

/-- Threshold class represented by a finite edge coordinate. -/
noncomputable def edgeAt (d : NatContactDendrogram m K N)
    (e : Fin (Fintype.card d.ThresholdEdge)) : d.ThresholdEdge :=
  d.edgeEquiv.symm e

/-- Indicator that a branch belongs to a threshold-class cut. -/
noncomputable def sideAt (d : NatContactDendrogram m K N)
    (edge : d.ThresholdEdge) (i : Fin m) : ℝ := by
  classical
  exact if d.thresholdClass edge.1 i = edge.2 then 1 else 0

/-- Cut indicator in canonical finite coordinates. -/
noncomputable def cutSide (d : NatContactDendrogram m K N)
    (e : Fin (Fintype.card d.ThresholdEdge)) (i : Fin m) : ℝ :=
  d.sideAt (d.edgeAt e) i

/-- Every unit numerator threshold has length `1 / N` on the common cover. -/
noncomputable def cutLength (d : NatContactDendrogram m K N)
    (_e : Fin (Fintype.card d.ThresholdEdge)) : ℝ :=
  1 / (N : ℝ)

/-- Threshold-one singleton class chosen as the pendant cut of a branch. -/
noncomputable def pendantEdge (d : NatContactDendrogram m K N) (i : Fin m) :
    Fin (Fintype.card d.ThresholdEdge) :=
  d.edgeEquiv ⟨0, d.thresholdClass 0 i⟩

@[simp] theorem edgeAt_pendantEdge (d : NatContactDendrogram m K N) (i : Fin m) :
    d.edgeAt (d.pendantEdge i) = ⟨0, d.thresholdClass 0 i⟩ := by
  simp [edgeAt, pendantEdge, edgeEquiv]

/-- Strict positivity of off-diagonal contact makes threshold-one classes singletons. -/
theorem cutSide_pendant (d : NatContactDendrogram m K N) (i j : Fin m) :
    d.cutSide (d.pendantEdge i) j = if j = i then 1 else 0 := by
  classical
  rw [cutSide, edgeAt_pendantEdge]
  simp only [sideAt]
  by_cases hji : j = i
  · subst j
    simp
  · have hclasses : d.thresholdClass 0 j ≠ d.thresholdClass 0 i := by
      intro h
      have hlt : d.contactNumerator j i < 1 := by
        simpa using (d.thresholdClass_eq_iff 0 j i).mp h
      have hpos := d.contact_pos_of_ne hji
      omega
    simp [hji, hclasses]

/-- Threshold-class indicators are idempotent. -/
theorem sideAt_sq (d : NatContactDendrogram m K N)
    (edge : d.ThresholdEdge) (i : Fin m) :
    d.sideAt edge i ^ (2 : ℕ) = d.sideAt edge i := by
  classical
  simp [sideAt]

/-- Canonical positive rooted cuts constructed directly from the contact numerators. -/
noncomputable def canonicalCuts (d : NatContactDendrogram m K N) :
    RootedCutContact m (Fintype.card d.ThresholdEdge) where
  length := d.cutLength
  side := d.cutSide
  length_pos := by
    intro e
    simp only [cutLength]
    exact one_div_pos.mpr (Nat.cast_pos.mpr d.coverDegree_pos)
  pendant := d.pendantEdge
  pendant_side := d.cutSide_pendant
  root := (K + 1 : ℕ) / (N : ℝ)
  side_idempotent := by
    intro e i
    exact d.sideAt_sq (d.edgeAt e) i

/-- Two point indicators have total overlap one exactly when their labels agree. -/
theorem quotient_indicator_sum {α : Type*} [Fintype α] [DecidableEq α]
    (a b : α) :
    (∑ c : α, (if a = c then (1 : ℝ) else 0) *
      (if b = c then 1 else 0)) = if a = b then 1 else 0 := by
  by_cases hab : a = b
  · subst b
    simp
  · simp [hab]

/-- At one threshold, exactly one class contributes if the two branches have not separated. -/
theorem sideAt_sum (d : NatContactDendrogram m K N) (t : Fin (K + 1))
    (i j : Fin m) :
    (∑ c : Quotient (d.thresholdSetoid t),
      d.sideAt ⟨t, c⟩ i * d.sideAt ⟨t, c⟩ j) =
        if d.contactNumerator i j < t.val + 1 then 1 else 0 := by
  classical
  simp only [sideAt]
  rw [quotient_indicator_sum]
  congr 1
  exact propext (d.thresholdClass_eq_iff t i j)

/-- Number of positive integral thresholds strictly above `h` up to `K + 1`. -/
theorem threshold_count (h K : ℕ) (hle : h ≤ K) :
    (∑ t : Fin (K + 1), if h < t.val + 1 then 1 else 0) = K + 1 - h := by
  induction K generalizing h with
  | zero =>
      have hh : h = 0 := Nat.eq_zero_of_le_zero hle
      subst h
      simp
  | succ K ih =>
      rw [Fin.sum_univ_succ]
      cases h with
      | zero => simp; omega
      | succ h =>
          have hle' : h ≤ K := by omega
          simpa using ih h hle'

/-- Real-valued form of the finite threshold-count identity. -/
theorem threshold_count_real (h K : ℕ) (hle : h ≤ K) :
    (∑ t : Fin (K + 1), if h < t.val + 1 then (1 : ℝ) else 0) =
      (K + 1 - h : ℕ) := by
  exact_mod_cast threshold_count h K hle

/-- Total common-cut length equals the complementary normalized contact. -/
theorem canonicalCutSum_eq (d : NatContactDendrogram m K N) (i j : Fin m) :
    (∑ e, d.canonicalCuts.length e *
      (d.canonicalCuts.side e i * d.canonicalCuts.side e j)) =
        ((K + 1 - d.contactNumerator i j : ℕ) : ℝ) / N := by
  classical
  let f : (Σ t : Fin (K + 1), Quotient (d.thresholdSetoid t)) → ℝ := fun edge =>
    (1 / (N : ℝ)) * (d.sideAt edge i * d.sideAt edge j)
  calc
    (∑ e, d.canonicalCuts.length e *
      (d.canonicalCuts.side e i * d.canonicalCuts.side e j)) =
        ∑ e, f (d.edgeAt e) := by rfl
    _ = ∑ edge : d.ThresholdEdge, f edge :=
      Equiv.sum_comp d.edgeEquiv.symm f
    _ = ∑ t : Fin (K + 1), ∑ c : Quotient (d.thresholdSetoid t),
        (1 / (N : ℝ)) * (d.sideAt ⟨t, c⟩ i * d.sideAt ⟨t, c⟩ j) := by
      simpa [f] using Fintype.sum_sigma
        (ι := Fin (K + 1))
        (α := fun t => Quotient (d.thresholdSetoid t)) f
    _ = ∑ t : Fin (K + 1), (1 / (N : ℝ)) *
        (if d.contactNumerator i j < t.val + 1 then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro t _
      rw [← Finset.mul_sum, d.sideAt_sum t i j]
    _ = (1 / (N : ℝ)) * ∑ t : Fin (K + 1),
        (if d.contactNumerator i j < t.val + 1 then 1 else 0) := by
      rw [Finset.mul_sum]
    _ = ((K + 1 - d.contactNumerator i j : ℕ) : ℝ) / N := by
      rw [threshold_count_real _ _ (d.contact_le i j)]
      ring

/-- **Canonical threshold-cut realization.** The constructed rooted cuts recover the normalized
highest-difference contact exactly; neither a rooted tree nor a cut realization is an input. -/
theorem canonicalCuts_contact_eq (d : NatContactDendrogram m K N) (i j : Fin m) :
    d.canonicalCuts.contact i j = d.contactNumerator i j / (N : ℝ) := by
  rw [RootedCutContact.contact, d.canonicalCutSum_eq]
  simp only [canonicalCuts]
  have hle : d.contactNumerator i j ≤ K + 1 :=
    (d.contact_le i j).trans (Nat.le_succ K)
  rw [Nat.cast_sub hle]
  have hN : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt d.coverDegree_pos)
  field_simp [hN]
  ring

end NatContactDendrogram
end
end IrregularStokes
end GaloisForLFunctions
