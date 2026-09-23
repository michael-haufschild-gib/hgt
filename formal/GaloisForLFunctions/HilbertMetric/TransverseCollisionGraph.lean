import GaloisForLFunctions.HilbertMetric.PolynomialFockRecombination
import Mathlib.Analysis.Real.Sqrt

/-!
# Transverse coherent-collision graph

The top homogeneous monomial channels are sent into a new orthogonal coordinate space with a
prescribed scalar amplitude.  Their Gram entry is constructed explicitly from the unisolvent
nodes.  Double recombination then gives the exact weighted top-degree projection, so the
transverse graph term is derived from actual vectors rather than postulated as a matrix.
-/

open scoped BigOperators

namespace GaloisForLFunctions.HilbertMetric

noncomputable section

/-- The positive symmetric-Fock weight of a homogeneous monomial. -/
def fockMonomialWeight {d n : ℕ} (a : HomogeneousMultiIndex d n) : ℝ :=
  (Nat.multinomial Finset.univ a.1 : ℝ) / (n.factorial : ℝ)

/-- Every symmetric-Fock monomial weight is strictly positive. -/
theorem fockMonomialWeight_pos {d n : ℕ} (a : HomogeneousMultiIndex d n) :
    0 < fockMonomialWeight a := by
  unfold fockMonomialWeight
  apply div_pos
  · exact_mod_cast Nat.multinomial_pos (Finset.univ : Finset (Fin d)) a.1
  · exact_mod_cast Nat.factorial_pos n

/-- The top degree as an element of the bounded grading index. -/
def topDegreeIndex (M : ℕ) : Fin (M + 1) := ⟨M, by omega⟩

/-- Explicit transverse coordinate of one collision node in one top monomial channel. -/
def transverseCollisionVector {d M : ℕ}
    (lam : ℝ) (nodes : GradedMultiIndex d M → (Fin d → ℝ))
    (i : GradedMultiIndex d M) (a : HomogeneousMultiIndex d M) : ℝ :=
  lam * Real.sqrt (fockMonomialWeight a) *
    monomialFeature HomogeneousMultiIndex.exponent a (nodes i)

/-- Inner product of the explicit transverse vectors attached to two collision nodes. -/
def transverseCollisionGramEntry {d M : ℕ}
    (lam : ℝ) (nodes : GradedMultiIndex d M → (Fin d → ℝ))
    (i j : GradedMultiIndex d M) : ℝ :=
  ∑ a : HomogeneousMultiIndex d M,
    transverseCollisionVector lam nodes i a * transverseCollisionVector lam nodes j a

/-- Recombination of one transverse vector isolates exactly one top monomial coordinate. -/
theorem recombined_transverseCollisionVector {d M : ℕ}
    (lam : ℝ) (nodes : GradedMultiIndex d M → (Fin d → ℝ))
    (c : GradedMultiIndex d M → GradedMultiIndex d M → ℝ)
    (hdelta : ∀ q r, ∑ i, c q i * monomialFeature GradedMultiIndex.exponent r (nodes i) =
      if q = r then 1 else 0)
    (q : GradedMultiIndex d M) (a : HomogeneousMultiIndex d M) :
    ∑ i, c q i * transverseCollisionVector lam nodes i a =
      lam * Real.sqrt (fockMonomialWeight a) *
        (if q = gradedIndex (topDegreeIndex M) a then 1 else 0) := by
  calc
    ∑ i, c q i * transverseCollisionVector lam nodes i a =
        lam * Real.sqrt (fockMonomialWeight a) *
          (∑ i, c q i *
            monomialFeature HomogeneousMultiIndex.exponent a (nodes i)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      unfold transverseCollisionVector
      ring
    _ = _ := by
      have hmoment := graded_monomial_delta nodes c hdelta q (topDegreeIndex M) a
      simpa [topDegreeIndex] using congrArg
        (fun z => lam * Real.sqrt (fockMonomialWeight a) * z) hmoment

/-- **Explicit transverse graph law.**  The recombined Gram entry is precisely `lam²` times
the weighted projection onto the top homogeneous channels. -/
theorem recombined_transverseCollisionGramEntry {d M : ℕ}
    (lam : ℝ) (nodes : GradedMultiIndex d M → (Fin d → ℝ))
    (c : GradedMultiIndex d M → GradedMultiIndex d M → ℝ)
    (hdelta : ∀ q r, ∑ i, c q i * monomialFeature GradedMultiIndex.exponent r (nodes i) =
      if q = r then 1 else 0)
    (q r : GradedMultiIndex d M) :
    ∑ i, ∑ j, c q i * c r j * transverseCollisionGramEntry lam nodes i j =
      ∑ a : HomogeneousMultiIndex d M,
        lam ^ (2 : ℕ) * fockMonomialWeight a *
          (if q = gradedIndex (topDegreeIndex M) a then 1 else 0) *
          (if r = gradedIndex (topDegreeIndex M) a then 1 else 0) := by
  calc
    ∑ i, ∑ j, c q i * c r j * transverseCollisionGramEntry lam nodes i j =
        ∑ i, ∑ a : HomogeneousMultiIndex d M, ∑ j,
          c q i * c r j *
            (transverseCollisionVector lam nodes i a *
              transverseCollisionVector lam nodes j a) := by
      unfold transverseCollisionGramEntry
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.mul_sum]
    _ = ∑ a : HomogeneousMultiIndex d M, ∑ i, ∑ j,
          c q i * c r j *
            (transverseCollisionVector lam nodes i a *
              transverseCollisionVector lam nodes j a) := Finset.sum_comm
    _ = ∑ a : HomogeneousMultiIndex d M,
          (∑ i, c q i * transverseCollisionVector lam nodes i a) *
            (∑ j, c r j * transverseCollisionVector lam nodes j a) := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [recombined_transverseCollisionVector lam nodes c hdelta q a,
        recombined_transverseCollisionVector lam nodes c hdelta r a]
      have hsqrt : Real.sqrt (fockMonomialWeight a) ^ (2 : ℕ) = fockMonomialWeight a := by
        rw [Real.sq_sqrt (le_of_lt (fockMonomialWeight_pos a))]
      calc
        (lam * Real.sqrt (fockMonomialWeight a) *
            (if q = gradedIndex (topDegreeIndex M) a then 1 else 0)) *
            (lam * Real.sqrt (fockMonomialWeight a) *
              (if r = gradedIndex (topDegreeIndex M) a then 1 else 0)) =
          lam ^ (2 : ℕ) * Real.sqrt (fockMonomialWeight a) ^ (2 : ℕ) *
            (if q = gradedIndex (topDegreeIndex M) a then 1 else 0) *
            (if r = gradedIndex (topDegreeIndex M) a then 1 else 0) := by ring
        _ = _ := by rw [hsqrt]

/-- On top homogeneous indices, the explicit transverse Gram recombination is diagonal with
entry `lam²` times the symmetric-Fock weight. -/
theorem recombined_transverseCollisionGramEntry_top {d M : ℕ}
    (lam : ℝ) (nodes : GradedMultiIndex d M → (Fin d → ℝ))
    (c : GradedMultiIndex d M → GradedMultiIndex d M → ℝ)
    (hdelta : ∀ q r, ∑ i, c q i * monomialFeature GradedMultiIndex.exponent r (nodes i) =
      if q = r then 1 else 0)
    (a b : HomogeneousMultiIndex d M) :
    ∑ i, ∑ j,
      c (gradedIndex (topDegreeIndex M) a) i *
        c (gradedIndex (topDegreeIndex M) b) j *
          transverseCollisionGramEntry lam nodes i j =
      if a = b then lam ^ (2 : ℕ) * fockMonomialWeight a else 0 := by
  rw [recombined_transverseCollisionGramEntry lam nodes c hdelta]
  by_cases hab : a = b
  · subst b
    rw [if_pos rfl]
    calc
      (∑ x : HomogeneousMultiIndex d M,
        lam ^ (2 : ℕ) * fockMonomialWeight x *
          (if gradedIndex (topDegreeIndex M) a = gradedIndex (topDegreeIndex M) x then 1 else 0) *
          (if gradedIndex (topDegreeIndex M) a = gradedIndex (topDegreeIndex M) x then 1 else 0)) =
        lam ^ (2 : ℕ) * fockMonomialWeight a *
          (if gradedIndex (topDegreeIndex M) a = gradedIndex (topDegreeIndex M) a then 1 else 0) *
          (if gradedIndex (topDegreeIndex M) a = gradedIndex (topDegreeIndex M) a then 1 else 0) := by
        apply Finset.sum_eq_single a
        · intro x hx hxa
          have hne : gradedIndex (topDegreeIndex M) a ≠ gradedIndex (topDegreeIndex M) x := by
            intro h
            exact hxa (eq_of_heq (Sigma.ext_iff.mp h).2.symm)
          simp [hne]
        · simp
      _ = _ := by simp
  · rw [if_neg hab]
    apply Finset.sum_eq_zero
    intro x hx
    by_cases ha : a = x
    · subst x
      have hb : b ≠ a := fun h => hab h.symm
      have hne : gradedIndex (topDegreeIndex M) b ≠ gradedIndex (topDegreeIndex M) a := by
        intro h
        exact hb (eq_of_heq (Sigma.ext_iff.mp h).2)
      simp [hne]
    · have hne : gradedIndex (topDegreeIndex M) a ≠ gradedIndex (topDegreeIndex M) x := by
        intro h
        exact ha (eq_of_heq (Sigma.ext_iff.mp h).2)
      simp [hne]

/-- Diagonal form of the transverse graph on the full graded family: only equal top-degree
channels survive. -/
theorem recombined_transverseCollisionGramEntry_diagonal {d M : ℕ}
    (lam : ℝ) (nodes : GradedMultiIndex d M → (Fin d → ℝ))
    (c : GradedMultiIndex d M → GradedMultiIndex d M → ℝ)
    (hdelta : ∀ q r, ∑ i, c q i * monomialFeature GradedMultiIndex.exponent r (nodes i) =
      if q = r then 1 else 0)
    (q r : GradedMultiIndex d M) :
    ∑ i, ∑ j, c q i * c r j * transverseCollisionGramEntry lam nodes i j =
      if q = r ∧ q.1 = topDegreeIndex M then
        lam ^ (2 : ℕ) * fockMonomialWeight q.2 else 0 := by
  by_cases hqr : q = r
  · subst r
    by_cases htop : q.1 = topDegreeIndex M
    · cases q with
      | mk qn qa =>
          dsimp at htop
          subst qn
          rw [if_pos ⟨rfl, rfl⟩]
          simpa [gradedIndex] using!
            recombined_transverseCollisionGramEntry_top lam nodes c hdelta qa qa
    · rw [if_neg (fun h => htop h.2)]
      rw [recombined_transverseCollisionGramEntry lam nodes c hdelta]
      apply Finset.sum_eq_zero
      intro a ha
      have hne : q ≠ gradedIndex (topDegreeIndex M) a := by
        intro h
        exact htop (congrArg Sigma.fst h)
      simp [hne]
  · rw [if_neg (fun h => hqr h.1)]
    rw [recombined_transverseCollisionGramEntry lam nodes c hdelta]
    apply Finset.sum_eq_zero
    intro a ha
    by_cases hq : q = gradedIndex (topDegreeIndex M) a
    · subst q
      have hr : r ≠ gradedIndex (topDegreeIndex M) a := fun hr => hqr hr.symm
      simp [hr]
    · simp [hq]

end

end GaloisForLFunctions.HilbertMetric
