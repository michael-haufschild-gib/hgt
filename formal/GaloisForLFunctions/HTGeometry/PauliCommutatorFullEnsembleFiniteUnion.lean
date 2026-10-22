import GaloisForLFunctions.HTGeometry.PauliCommutatorFullEnsembleLowerTail

/-!
# Union bound for Pauli commutator tubes over finitely many targets

For the Gaussian ensemble of `n`-qubit Hamiltonians with independent standard normal coefficients
on all nonidentity Pauli strings of weight at most `q`, the commutator tube of a nonidentity Pauli
target `P` is the set of coefficient vectors whose commutator coordinates against `P` have squared
norm at most `θ (n - 1) (2 · 2ⁿ)²`. Each tube has Gaussian mass at most
`exp(-2 (a - θ)² (n - 1))`, where `a = gaussianIntervalActivationMass`. A union bound extends this
to a finite family of targets.

## Main results

- `fullActivePauliCommutatorFiniteTargetTube`: union of the commutator tubes of a finite family of
  targets.
- `measure_fullActivePauliCommutatorFiniteTargetTube_le`: for `q ≥ 2` and `θ ≤ a`, the union has
  Gaussian mass at most `|K| · exp(-2 (a - θ)² (n - 1))`.

## Hypotheses

Unconditional; the bound assumes `2 ≤ q` and `θ ≤ gaussianIntervalActivationMass`.
-/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Coefficient vectors lying in the commutator tube of at least one target `target k`. -/
def fullActivePauliCommutatorFiniteTargetTube
    {n q : ℕ} {K : Type*} [Fintype K]
    (target : K → NonzeroPauliCharacter (Fin n)) (θ : ℝ) :
    Set (PauliTracelessLabel n q → ℝ) :=
  {J | ∃ k, J ∈ fullActivePauliCommutatorTube (target k) θ}

/-- Assuming `2 ≤ q` and `θ ≤ gaussianIntervalActivationMass`, the standard Gaussian mass of the
union of commutator tubes over `K` targets is at most `|K| · exp(-2 (a - θ)² (n - 1))`. -/
theorem measure_fullActivePauliCommutatorFiniteTargetTube_le
    {n q : ℕ} (hq : 2 ≤ q) {K : Type*} [Fintype K]
    (target : K → NonzeroPauliCharacter (Fin n))
    {θ : ℝ} (hθ : θ ≤ gaussianIntervalActivationMass) :
    (Measure.pi fun _ : PauliTracelessLabel n q => gaussianReal 0 1).real
        (fullActivePauliCommutatorFiniteTargetTube target θ) ≤
      Fintype.card K *
        Real.exp
          (-2 * (gaussianIntervalActivationMass - θ) ^ 2 * (n - 1 : ℕ)) := by
  let μ := Measure.pi fun _ : PauliTracelessLabel n q => gaussianReal 0 1
  change μ.real {J | ∃ k, J ∈ fullActivePauliCommutatorTube (target k) θ} ≤ _
  calc
    μ.real {J | ∃ k, J ∈ fullActivePauliCommutatorTube (target k) θ} =
        μ.real (⋃ k, fullActivePauliCommutatorTube (target k) θ) := by
      congr 1
      ext J
      simp
    _ ≤ ∑ k : K, μ.real (fullActivePauliCommutatorTube (target k) θ) :=
      measureReal_iUnion_fintype_le _
    _ ≤ ∑ _k : K,
        Real.exp
          (-2 * (gaussianIntervalActivationMass - θ) ^ 2 * (n - 1 : ℕ)) := by
      exact Finset.sum_le_sum fun k _ =>
        measure_fullActivePauliCommutatorTube_le hq (target k) hθ
    _ = Fintype.card K *
        Real.exp
          (-2 * (gaussianIntervalActivationMass - θ) ^ 2 * (n - 1 : ℕ)) := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

end

end GaloisForLFunctions.HTGeometry
