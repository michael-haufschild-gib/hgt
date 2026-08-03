import GaloisForLFunctions.HTGeometry.ElementaryStokesGlobalPuiseuxRealization

namespace GaloisForLFunctions.IrregularStokes

noncomputable section

namespace FiniteContactDendrogram

variable {α L K : Type*} [LinearOrder L]

/-- Acute-isosceles law for an abstract symmetric contact height. -/
def IsAcute (d : α → α → L) : Prop :=
  ∀ i j k, d i j ≤ max (d i k) (d j k)

/-- Strict threshold partition attached to an acute symmetric contact matrix. -/
def strictThresholdSetoid (d : α → α → L)
    (hsymm : ∀ i j, d i j = d j i) (hacute : IsAcute d) (t : L) : Setoid α where
  r i j := i = j ∨ d i j < t
  iseqv := {
    refl := fun i => Or.inl rfl
    symm := by
      intro i j h
      rcases h with rfl | h
      · exact Or.inl rfl
      · exact Or.inr (by simpa [hsymm] using h)
    trans := by
      intro i j k hij hjk
      rcases hij with rfl | hij
      · exact hjk
      rcases hjk with rfl | hjk
      · exact Or.inr hij
      right
      have hik := hacute i k j
      rw [hsymm k j] at hik
      exact hik.trans_lt (max_lt hij hjk) }

def thresholdClass (d : α → α → L)
    (hsymm : ∀ i j, d i j = d j i) (hacute : IsAcute d) (t : L) (i : α) :
    Quotient (strictThresholdSetoid d hsymm hacute t) :=
  Quotient.mk _ i

/-- Distinct coefficients for the finite threshold quotient in any infinite coefficient type. -/
def thresholdCoefficient (d : α → α → L)
    (hsymm : ∀ i j, d i j = d j i) (hacute : IsAcute d) (t : L)
    [Finite α] [Infinite K] (i : α) : K :=
  ElementaryDecoratedGraph.finiteDistinctCoefficients
    (Quotient (strictThresholdSetoid d hsymm hacute t)) K
    (thresholdClass d hsymm hacute t i)

theorem thresholdClass_eq_iff (d : α → α → L)
    (hsymm : ∀ i j, d i j = d j i) (hacute : IsAcute d) (t : L) (i j : α) :
    thresholdClass d hsymm hacute t i = thresholdClass d hsymm hacute t j ↔
      i = j ∨ d i j < t := by
  exact Quotient.eq

theorem thresholdCoefficient_eq_iff (d : α → α → L)
    (hsymm : ∀ i j, d i j = d j i) (hacute : IsAcute d) (t : L)
    [Finite α] [Infinite K] (i j : α) :
    thresholdCoefficient (K := K) d hsymm hacute t i =
        thresholdCoefficient (K := K) d hsymm hacute t j ↔
      i = j ∨ d i j < t := by
  rw [← thresholdClass_eq_iff d hsymm hacute]
  exact (ElementaryDecoratedGraph.finiteDistinctCoefficients_injective
    (Quotient (strictThresholdSetoid d hsymm hacute t)) K).eq_iff

/-- Threshold partitions coarsen with the threshold. -/
theorem threshold_mono (d : α → α → L)
    (hsymm : ∀ i j, d i j = d j i) (hacute : IsAcute d)
    {s t : L} (hst : s ≤ t) {i j : α} :
    (strictThresholdSetoid d hsymm hacute s).r i j →
      (strictThresholdSetoid d hsymm hacute t).r i j := by
  rintro (rfl | h)
  · exact Or.inl rfl
  · exact Or.inr (h.trans_le hst)

/-- Exact highest-difference realization: two different labels separate at their prescribed
height and agree at every strictly larger threshold. -/
theorem exact_highestDifference (d : α → α → L)
    (hsymm : ∀ i j, d i j = d j i) (hacute : IsAcute d)
    [Finite α] [Infinite K] {i j : α} (hij : i ≠ j) :
    thresholdCoefficient (K := K) d hsymm hacute (d i j) i ≠
        thresholdCoefficient (K := K) d hsymm hacute (d i j) j ∧
      ∀ t, d i j < t →
        thresholdCoefficient (K := K) d hsymm hacute t i =
          thresholdCoefficient (K := K) d hsymm hacute t j := by
  constructor
  · intro heq
    have hrel := (thresholdCoefficient_eq_iff (K := K)
      d hsymm hacute (d i j) i j).mp heq
    exact hrel.elim hij (lt_irrefl _)
  · intro t hit
    apply (thresholdCoefficient_eq_iff (K := K) d hsymm hacute t i j).mpr
    exact Or.inr hit

end FiniteContactDendrogram
end
end GaloisForLFunctions.IrregularStokes
