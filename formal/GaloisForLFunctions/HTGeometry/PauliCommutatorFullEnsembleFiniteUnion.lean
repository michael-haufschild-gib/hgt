import GaloisForLFunctions.HTGeometry.PauliCommutatorFullEnsembleLowerTail

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace GaloisForLFunctions.HTGeometry

noncomputable section

def fullActivePauliCommutatorFiniteTargetTube
    {n q : ℕ} {K : Type*} [Fintype K]
    (target : K → NonzeroPauliCharacter (Fin n)) (θ : ℝ) :
    Set (PauliTracelessLabel n q → ℝ) :=
  {J | ∃ k, J ∈ fullActivePauliCommutatorTube (target k) θ}

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
