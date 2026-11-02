import GaloisForLFunctions.CompletedArithmeticForms.RamanujanConductorFrames
import GaloisForLFunctions.CriticalScaleArithmeticRigidity.PrimeCoherenceCalculus

/-!
# Large prime conductors have disjoint horizon spikes

Above the square-root horizon, distinct prime divisibility supports are disjoint.
Their common constant mode is paid by the harmonic mass below those supports.
This gives lower frame bounds beyond the square-root range for prime conductors.
-/

noncomputable section
set_option autoImplicit false
open Finset Filter Topology
open scoped Classical RealInnerProductSpace

namespace GaloisForLFunctions.CompletedArithmeticForms
open RenormalizedArithmeticPotentialTheory CriticalScaleArithmeticRigidity
  CriticalArithmeticCorrelationTheory ArithmeticIntersectionTheory

private theorem norm_sub_scalar_ge_missing_support {ι : Type*} (S : Finset ι)
    (P : ι → Prop) (f g : ι → ℝ) (s : ℝ)
    (hf : ∀ i ∈ S, P i → f i = 0) :
    (∑ i ∈ S, g i ^ 2) * (∑ i ∈ S, (f i - s * g i) ^ 2) ≥
      (∑ i ∈ S, if P i then g i ^ 2 else 0) * (∑ i ∈ S, f i ^ 2) := by
  let tail := fun i => if P i then 0 else g i
  let G := ∑ i ∈ S, g i ^ 2
  let H := ∑ i ∈ S, if P i then g i ^ 2 else 0
  let A := ∑ i ∈ S, f i ^ 2
  let F := ∑ i ∈ S, f i * g i
  have hcross : (∑ i ∈ S, f i * tail i) = F := by
    apply sum_congr rfl
    intro i hi
    by_cases hP : P i
    · simp only [tail, if_pos hP, hf i hi hP, zero_mul]
    · simp only [tail, if_neg hP]
  have htail : (∑ i ∈ S, tail i ^ 2) = G - H := by
    have hh : (∑ i ∈ S, tail i ^ 2) + H = G := by
      dsimp only [H, G]
      rw [← sum_add_distrib]
      apply sum_congr rfl
      intro i _
      by_cases hP : P i <;> simp only [tail, hP, if_true, if_false, zero_pow (by decide : 2 ≠ 0),
        zero_add, add_zero]
    linarith only [hh]
  have hcs := sum_mul_sq_le_sq_mul_sq S f tail
  rw [hcross, htail] at hcs
  change F ^ 2 ≤ A * (G - H) at hcs
  have henergy : (∑ i ∈ S, (f i - s * g i) ^ 2) = A - 2 * s * F + s ^ 2 * G := by
    dsimp only [A, F, G]
    rw [mul_sum, mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
    apply sum_congr rfl
    intro i _
    ring
  change G * (∑ i ∈ S, (f i - s * g i) ^ 2) ≥ H * A
  rw [henergy]
  nlinarith only [hcs, sq_nonneg (s * G - F)]

end GaloisForLFunctions.CompletedArithmeticForms
