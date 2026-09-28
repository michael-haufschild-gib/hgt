import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# Bochner identity for jump generators with variable rates

The iterated energy density is the sum of squared second differences and two exact
rate-variation terms. Commuting shifts need not have constant or positive rates.
A cutoff or a change of profile therefore remains visible in the identity.
-/

noncomputable section

open scoped BigOperators

namespace HTGeometry.JumpBochner

variable {ι X : Type*}

/-- Increment of a function along one shift. -/
def difference (shift : ι → X → X) (i : ι) (f : X → ℝ) (x : X) : ℝ :=
  f (shift i x) - f x

/-- Finite jump generator with position-dependent rates. -/
def generator (s : Finset ι) (rate : ι → X → ℝ) (shift : ι → X → X)
    (f : X → ℝ) (x : X) : ℝ :=
  ∑ i ∈ s, rate i x * difference shift i f x

/-- Bilinear carré du champ of the jump generator. -/
def energyDensity (s : Finset ι) (rate : ι → X → ℝ) (shift : ι → X → X)
    (f g : X → ℝ) (x : X) : ℝ :=
  (∑ i ∈ s, rate i x * difference shift i f x * difference shift i g x) / 2

/-- Iterated carré du champ, including all rate-variation contributions. -/
def gammaTwo (s : Finset ι) (rate : ι → X → ℝ) (shift : ι → X → X)
    (f : X → ℝ) (x : X) : ℝ :=
  generator s rate shift (energyDensity s rate shift f f) x / 2 -
    energyDensity s rate shift f (generator s rate shift f) x

/-- Exact two-jump expansion, without assuming that shifts commute. -/
theorem gammaTwo_eq_pairSum (s : Finset ι) (rate : ι → X → ℝ)
    (shift : ι → X → X) (f : X → ℝ) (x : X) :
    gammaTwo s rate shift f x =
      ∑ i ∈ s, ∑ j ∈ s,
        (rate j x * (rate i (shift j x) * (difference shift i f (shift j x)) ^ 2 -
          rate i x * (difference shift i f x) ^ 2) / 4 -
          rate i x * difference shift i f x *
            (rate j (shift i x) * difference shift j f (shift i x) -
              rate j x * difference shift j f x) / 2) := by
  have hL : generator s rate shift (energyDensity s rate shift f f) x / 2 =
      ∑ i ∈ s, ∑ j ∈ s,
        rate j x * (rate i (shift j x) * (difference shift i f (shift j x)) ^ 2 -
          rate i x * (difference shift i f x) ^ 2) / 4 := by
    unfold generator
    rw [Finset.sum_div, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j hj
    simp only [difference, energyDensity, ← Finset.sum_div, ← Finset.mul_sum,
      Finset.sum_sub_distrib, pow_two, mul_assoc]
    ring
  have hG : energyDensity s rate shift f (generator s rate shift f) x =
      ∑ i ∈ s, ∑ j ∈ s,
        rate i x * difference shift i f x *
          (rate j (shift i x) * difference shift j f (shift i x) -
            rate j x * difference shift j f x) / 2 := by
    unfold energyDensity
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [difference, generator, ← Finset.sum_div, ← Finset.mul_sum,
      Finset.sum_sub_distrib]
  rw [gammaTwo, hL, hG]
  simp only [Finset.sum_sub_distrib]

/-- For commuting shifts, squared second differences plus the full rate defect. -/
theorem gammaTwo_eq_squares_add_rateDefect (s : Finset ι) (rate : ι → X → ℝ)
    (shift : ι → X → X) (f : X → ℝ) (x : X)
    (hcomm : ∀ i ∈ s, ∀ j ∈ s, shift i (shift j x) = shift j (shift i x)) :
    gammaTwo s rate shift f x =
      ∑ i ∈ s, ∑ j ∈ s,
        (rate i x * rate j x * (difference shift j (difference shift i f) x) ^ 2 / 4 +
          rate j x * difference shift j (rate i) x *
            (difference shift i f (shift j x)) ^ 2 / 4 -
          rate i x * difference shift i (rate j) x * difference shift i f x *
            difference shift j f (shift i x) / 2) := by
  rw [gammaTwo_eq_pairSum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  simp only [difference, hcomm i hi j hj]
  ring

end HTGeometry.JumpBochner
