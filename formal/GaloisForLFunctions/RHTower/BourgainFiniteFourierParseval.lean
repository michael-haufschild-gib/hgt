/-
# Finite Fourier Parseval with repeated frequencies

A finite family may contain repeated natural frequencies.  This module
packages polynomial Parseval in the exact form needed by Bourgain's moment
arguments: coefficients with the same frequency are grouped before their
squared norms are summed.
-/
import Mathlib.Analysis.Polynomial.Fourier

open scoped BigOperators Polynomial

namespace RHTower

noncomputable section

/-- Polynomial attached to a finite weighted natural-frequency family. -/
def finiteFrequencyPolynomial
    {ι : Type*} (s : Finset ι) (ν : ι → ℕ) (w : ι → ℂ) : ℂ[X] :=
  ∑ i ∈ s, Polynomial.monomial (ν i) (w i)

/-- A coefficient is the sum of all weights carrying that frequency. -/
theorem coeff_finiteFrequencyPolynomial
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (ν : ι → ℕ) (w : ι → ℂ) (n : ℕ) :
    (finiteFrequencyPolynomial s ν w).coeff n =
      ∑ i ∈ s.filter (fun i => ν i = n), w i := by
  classical
  rw [finiteFrequencyPolynomial]
  rw [Polynomial.finsetSum_coeff, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  rw [Polynomial.coeff_monomial]

/-- Every supported frequency occurs in the original finite family. -/
theorem support_finiteFrequencyPolynomial_subset_image
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (ν : ι → ℕ) (w : ι → ℂ) :
    (finiteFrequencyPolynomial s ν w).support ⊆ s.image ν := by
  classical
  intro n hn
  rw [Polynomial.mem_support_iff] at hn
  by_contra hnot
  have hempty :
      s.filter (fun i => ν i = n) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro i hi
    apply hnot
    exact Finset.mem_image.mpr
      ⟨i, (Finset.mem_filter.mp hi).1, (Finset.mem_filter.mp hi).2⟩
  apply hn
  rw [coeff_finiteFrequencyPolynomial, hempty]
  simp

/-- Exact Parseval identity for a finite family with repeated frequencies. -/
theorem circleAverage_finiteFrequencyPolynomial_norm_sq
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (ν : ι → ℕ) (w : ι → ℂ) :
    Real.circleAverage
        (fun z => ‖(finiteFrequencyPolynomial s ν w).eval z‖ ^ (2 : ℕ))
        0 1 =
      ∑ n ∈ s.image ν,
        ‖∑ i ∈ s.filter (fun i => ν i = n), w i‖ ^ (2 : ℕ) := by
  classical
  let P := finiteFrequencyPolynomial s ν w
  have hparseval := Polynomial.sum_sq_norm_coeff_eq_circleAverage P
  calc
    Real.circleAverage (fun z => ‖P.eval z‖ ^ (2 : ℕ)) 0 1 =
        ∑ n ∈ P.support, ‖P.coeff n‖ ^ (2 : ℕ) := hparseval.symm
    _ = ∑ n ∈ s.image ν, ‖P.coeff n‖ ^ (2 : ℕ) := by
      apply Finset.sum_subset
      · simpa [P] using support_finiteFrequencyPolynomial_subset_image s ν w
      · intro n _ hn
        rw [Polynomial.notMem_support_iff.mp hn]
        simp
    _ = ∑ n ∈ s.image ν,
        ‖∑ i ∈ s.filter (fun i => ν i = n), w i‖ ^ (2 : ℕ) := by
      apply Finset.sum_congr rfl
      intro n _
      rw [show P = finiteFrequencyPolynomial s ν w by rfl,
        coeff_finiteFrequencyPolynomial]

end

end RHTower
