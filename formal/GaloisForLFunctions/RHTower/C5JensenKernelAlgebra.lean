import GaloisForLFunctions.RHTower.C5JensenPrimeKernel

/-!
# Finite algebra of the C5 Jensen prime kernel

This file isolates the exact finite Leibniz rearrangement behind the C5
Jensen-section kernel.  It carries no regularization or zero-set assumption:
the analytic completed-source input is kept separate from this finite
coefficient algebra.
-/

noncomputable section

namespace GaloisForLFunctions.RHTower

open scoped BigOperators

/-- The `i`th finite Leibniz coefficient in a degree-`d` Jensen section. -/
def c5JensenLeibnizCoefficient (d : ℕ) (arch : ℕ → ℂ) (i : ℕ) (X : ℂ) : ℂ :=
  ∑ j ∈ Finset.range (d + 1),
    if i ≤ j then
      (d.choose j : ℂ) * (j.choose i : ℂ) * arch (j - i) * X ^ j / (j.factorial : ℂ)
    else 0

/-- The degree-`d` first-order Jensen perturbation assembled from finite jet data. -/
def c5JensenFirstOrderSection (d : ℕ) (arch perturb : ℕ → ℂ) (X : ℂ) : ℂ :=
  ∑ j ∈ Finset.range (d + 1),
    (d.choose j : ℂ) * X ^ j / (j.factorial : ℂ) *
      ∑ i ∈ Finset.range (d + 1),
        if i ≤ j then (j.choose i : ℂ) * arch (j - i) * perturb i else 0

/-- Exact finite collection of the first-order Leibniz terms by derivative index. -/
theorem c5JensenFirstOrderSection_eq_sum_coefficients
    (d : ℕ) (arch perturb : ℕ → ℂ) (X : ℂ) :
    c5JensenFirstOrderSection d arch perturb X =
      ∑ i ∈ Finset.range (d + 1),
        perturb i * c5JensenLeibnizCoefficient d arch i X := by
  unfold c5JensenFirstOrderSection c5JensenLeibnizCoefficient
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.sum_congr rfl fun j hj => ?_]
  split_ifs with hij <;> ring

/-- One exponential frequency contributes its amplitude times a degree-`≤ d`
polynomial in that frequency. -/
theorem c5JensenFirstOrderSection_singleFrequency
    (d : ℕ) (arch : ℕ → ℂ) (amplitude frequency X : ℂ) :
    c5JensenFirstOrderSection d arch
        (fun i => amplitude * (-Complex.I * frequency) ^ i) X =
      amplitude * ∑ i ∈ Finset.range (d + 1),
        (-Complex.I * frequency) ^ i * c5JensenLeibnizCoefficient d arch i X := by
  rw [c5JensenFirstOrderSection_eq_sum_coefficients]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  ring

/-- A logarithmic prime perturbation has no zero-order contribution, so its
finite Jensen kernel starts at positive derivative order. -/
theorem c5JensenFirstOrderSection_singleFrequency_noConstant
    (d : ℕ) (arch : ℕ → ℂ) (amplitude frequency X : ℂ) :
    c5JensenFirstOrderSection d arch
        (fun i => if i = 0 then 0 else amplitude * (-Complex.I * frequency) ^ i) X =
      amplitude * ∑ i ∈ Finset.range (d + 1),
        if i = 0 then 0 else
          (-Complex.I * frequency) ^ i * c5JensenLeibnizCoefficient d arch i X := by
  rw [c5JensenFirstOrderSection_eq_sum_coefficients]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  split_ifs with h <;> ring

end GaloisForLFunctions.RHTower

end
