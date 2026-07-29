import GaloisForLFunctions.HilbertMetric.PolynomialFockKernel

/-!
# Exact recombination of polynomial Fock powers

Given the delta-moment coefficients supplied by an unconditional unisolvent family, double
recombination diagonalizes every polynomial Fock degree.  Equal basis channels retain exactly
their multinomial weight; unequal channels, and mismatched degrees, vanish exactly.

These are literal finite identities, not asymptotic or rank-certificate statements.  They supply
the algebraic half of the degree-five coherent-collision matrix jet.
-/

open scoped BigOperators

namespace GaloisForLFunctions.HilbertMetric

noncomputable section

/-- Embed an exact-degree multi-index into the graded family. -/
def gradedIndex {d M : ℕ} (n : Fin (M + 1)) (a : HomogeneousMultiIndex d n) :
    GradedMultiIndex d M := ⟨n, a⟩

/-- The graded delta-moment identity restricted to one homogeneous degree. -/
theorem graded_monomial_delta {d M : ℕ}
    (nodes : GradedMultiIndex d M → (Fin d → ℝ))
    (c : GradedMultiIndex d M → GradedMultiIndex d M → ℝ)
    (hdelta : ∀ q r, ∑ i, c q i * monomialFeature GradedMultiIndex.exponent r (nodes i) =
      if q = r then 1 else 0)
    (q : GradedMultiIndex d M) (n : Fin (M + 1))
    (a : HomogeneousMultiIndex d n) :
    ∑ i, c q i * monomialFeature HomogeneousMultiIndex.exponent a (nodes i) =
      if q = gradedIndex n a then 1 else 0 := by
  simpa [gradedIndex, GradedMultiIndex.exponent] using! hdelta q (gradedIndex n a)

/-- **Exact recombined power law.**  Double recombination of the degree-`n` Euclidean power
kernel is the weighted projection onto its homogeneous multi-index channels. -/
theorem recombined_innerPower_eq {d M : ℕ}
    (nodes : GradedMultiIndex d M → (Fin d → ℝ))
    (c : GradedMultiIndex d M → GradedMultiIndex d M → ℝ)
    (hdelta : ∀ q r, ∑ i, c q i * monomialFeature GradedMultiIndex.exponent r (nodes i) =
      if q = r then 1 else 0)
    (q r : GradedMultiIndex d M) (n : Fin (M + 1)) :
    ∑ i, ∑ j, c q i * c r j * (∑ l, nodes i l * nodes j l) ^ (n : ℕ) =
      ∑ a : HomogeneousMultiIndex d n,
        (Nat.multinomial Finset.univ a.1 : ℝ) *
          (if q = gradedIndex n a then 1 else 0) *
          (if r = gradedIndex n a then 1 else 0) := by
  calc
    ∑ i, ∑ j, c q i * c r j * (∑ l, nodes i l * nodes j l) ^ (n : ℕ) =
        ∑ i, ∑ j, ∑ a : HomogeneousMultiIndex d n,
          c q i * c r j *
            ((Nat.multinomial Finset.univ a.1 : ℝ) *
              monomialFeature HomogeneousMultiIndex.exponent a (nodes i) *
              monomialFeature HomogeneousMultiIndex.exponent a (nodes j)) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      rw [innerPower_eq_sum_homogeneousMonomial]
      rw [Finset.mul_sum]
    _ = ∑ i, ∑ a : HomogeneousMultiIndex d n, ∑ j,
          c q i * c r j *
            ((Nat.multinomial Finset.univ a.1 : ℝ) *
              monomialFeature HomogeneousMultiIndex.exponent a (nodes i) *
              monomialFeature HomogeneousMultiIndex.exponent a (nodes j)) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact Finset.sum_comm
    _ = ∑ a : HomogeneousMultiIndex d n, ∑ i, ∑ j,
          c q i * c r j *
            ((Nat.multinomial Finset.univ a.1 : ℝ) *
              monomialFeature HomogeneousMultiIndex.exponent a (nodes i) *
              monomialFeature HomogeneousMultiIndex.exponent a (nodes j)) :=
      Finset.sum_comm
    _ = ∑ a : HomogeneousMultiIndex d n,
          (Nat.multinomial Finset.univ a.1 : ℝ) *
            (∑ i, c q i * monomialFeature HomogeneousMultiIndex.exponent a (nodes i)) *
            (∑ j, c r j * monomialFeature HomogeneousMultiIndex.exponent a (nodes j)) := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [mul_assoc, Finset.sum_mul, Finset.mul_sum]
      simp_rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [graded_monomial_delta nodes c hdelta q n a,
        graded_monomial_delta nodes c hdelta r n a]

/-- A basis channel retains exactly its multinomial weight at its own degree. -/
theorem recombined_innerPower_self_degree {d M : ℕ}
    (nodes : GradedMultiIndex d M → (Fin d → ℝ))
    (c : GradedMultiIndex d M → GradedMultiIndex d M → ℝ)
    (hdelta : ∀ q r, ∑ i, c q i * monomialFeature GradedMultiIndex.exponent r (nodes i) =
      if q = r then 1 else 0)
    (q : GradedMultiIndex d M) :
    ∑ i, ∑ j, c q i * c q j * (∑ l, nodes i l * nodes j l) ^ (q.1 : ℕ) =
      (Nat.multinomial Finset.univ q.2.1 : ℝ) := by
  rw [recombined_innerPower_eq nodes c hdelta q q q.1]
  have hsingle :
      (∑ a : HomogeneousMultiIndex d q.1,
        (Nat.multinomial Finset.univ a.1 : ℝ) *
          (if q = gradedIndex q.1 a then 1 else 0) *
          (if q = gradedIndex q.1 a then 1 else 0)) =
        (Nat.multinomial Finset.univ q.2.1 : ℝ) *
          (if q = gradedIndex q.1 q.2 then 1 else 0) *
          (if q = gradedIndex q.1 q.2 then 1 else 0) := by
    apply Finset.sum_eq_single q.2
    · intro a ha haneq
      have hqne : q ≠ gradedIndex q.1 a := by
        intro h
        apply haneq
        exact eq_of_heq (Sigma.ext_iff.mp h).2.symm
      simp [hqne]
    · simp
  rw [hsingle]
  simp [gradedIndex]

/-- Unequal graded channels are orthogonal for every polynomial Fock degree. -/
theorem recombined_innerPower_eq_zero_of_ne {d M : ℕ}
    (nodes : GradedMultiIndex d M → (Fin d → ℝ))
    (c : GradedMultiIndex d M → GradedMultiIndex d M → ℝ)
    (hdelta : ∀ q r, ∑ i, c q i * monomialFeature GradedMultiIndex.exponent r (nodes i) =
      if q = r then 1 else 0)
    (q r : GradedMultiIndex d M) (n : Fin (M + 1)) (hqr : q ≠ r) :
    ∑ i, ∑ j, c q i * c r j * (∑ l, nodes i l * nodes j l) ^ (n : ℕ) = 0 := by
  rw [recombined_innerPower_eq nodes c hdelta q r n]
  apply Finset.sum_eq_zero
  intro a ha
  by_cases hq : q = gradedIndex n a
  · subst q
    have hr : r ≠ gradedIndex n a := fun hr => hqr hr.symm
    simp [hr]
  · simp [hq]

/-- A channel has zero recombined contribution from every degree other than its own. -/
theorem recombined_innerPower_eq_zero_of_degree_ne {d M : ℕ}
    (nodes : GradedMultiIndex d M → (Fin d → ℝ))
    (c : GradedMultiIndex d M → GradedMultiIndex d M → ℝ)
    (hdelta : ∀ q r, ∑ i, c q i * monomialFeature GradedMultiIndex.exponent r (nodes i) =
      if q = r then 1 else 0)
    (q r : GradedMultiIndex d M) (n : Fin (M + 1)) (hq : q.1 ≠ n) :
    ∑ i, ∑ j, c q i * c r j * (∑ l, nodes i l * nodes j l) ^ (n : ℕ) = 0 := by
  rw [recombined_innerPower_eq nodes c hdelta q r n]
  apply Finset.sum_eq_zero
  intro a ha
  have hqne : q ≠ gradedIndex n a := by
    intro h
    exact hq (congrArg Sigma.fst h)
  simp [hqne]

/-- Diagonal form combining the self-degree, cross-channel, and degree-mismatch laws. -/
theorem recombined_innerPower_eq_diagonal {d M : ℕ}
    (nodes : GradedMultiIndex d M → (Fin d → ℝ))
    (c : GradedMultiIndex d M → GradedMultiIndex d M → ℝ)
    (hdelta : ∀ q r, ∑ i, c q i * monomialFeature GradedMultiIndex.exponent r (nodes i) =
      if q = r then 1 else 0)
    (q r : GradedMultiIndex d M) (n : Fin (M + 1)) :
    ∑ i, ∑ j, c q i * c r j * (∑ l, nodes i l * nodes j l) ^ (n : ℕ) =
      if q = r ∧ q.1 = n then (Nat.multinomial Finset.univ q.2.1 : ℝ) else 0 := by
  by_cases hqr : q = r
  · subst r
    by_cases hqn : q.1 = n
    · subst n
      rw [if_pos ⟨rfl, rfl⟩]
      exact recombined_innerPower_self_degree nodes c hdelta q
    · rw [if_neg (fun h => hqn h.2)]
      exact recombined_innerPower_eq_zero_of_degree_ne nodes c hdelta q q n hqn
  · rw [if_neg (fun h => hqr h.1)]
    exact recombined_innerPower_eq_zero_of_ne nodes c hdelta q r n hqr

end

end GaloisForLFunctions.HilbertMetric
