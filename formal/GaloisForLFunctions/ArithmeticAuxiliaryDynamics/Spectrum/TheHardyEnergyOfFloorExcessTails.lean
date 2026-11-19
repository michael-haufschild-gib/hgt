import GaloisForLFunctions.ArithmeticAuxiliaryDynamics.TheCoefficientMassOfAProducer
import GaloisForLFunctions.ArithmeticHarmonicAnalysis.HardyEnergyOnAFiniteMesh

/-!
# Hardy energy of the tails of a floor row

The reciprocal-integer mesh has exactly the pronic widths in the floor
excess. Its quadratic Hardy inequality controls all remaining tails
simultaneously by the peak and the total excess.
-/

open Finset GaloisForLFunctions.ArithmeticKreinLangerTheory
open GaloisForLFunctions.ArithmeticHarmonicAnalysis
namespace GaloisForLFunctions.ArithmeticAuxiliaryDynamics.FloorSpectrum
noncomputable section

/-- Signed tail of the pronic excess through `M`, obtained by subtracting the
prefix ending at `i`. -/
def floorExcessTail (c : ℕ →₀ ℤ) (m B M i : ℕ) : ℝ :=
  (∑ j ∈ range M, IsProducer.excessTerm m B c j) - ∑ j ∈ range i, IsProducer.excessTerm m B c j

/-- The reciprocal grid converts the mesh estimate into an unweighted
square-tail estimate, with the exact factor `(i+1)/(i+2)` at each site. -/
theorem floorExcessTail_energy (c : ℕ →₀ ℤ) (m B M : ℕ) :
    (∑ i ∈ range M, ((i:ℝ)+1)/((i:ℝ)+2) * (floorExcessTail c m B M (i+1))^2) +
      2*(floorExcessTail c m B M 0)^2 ≤
      4*∑ i ∈ range M, (((i:ℝ)+1)*((i:ℝ)+2) * (IsProducer.excessTerm m B c i)^2) := by
  let h (i : ℕ) : ℝ := 1/((i:ℝ)+1)
  let z := floorExcessTail c m B M
  have width (i : ℕ) : h i - h (i+1) = 1/(((i:ℝ)+1)*((i:ℝ)+2)) := by
    dsimp only [h]
    push_cast
    field_simp
    ring
  have hp (i : ℕ) : 0 < h i := by dsimp [h]; positivity
  have H := mesh_hardy_energy h z M (fun i _ => ⟨(hp _).le,
    sub_pos.mp ((width i).symm ▸ (by positivity))⟩) (fun i _ he => ((hp _).ne' he).elim)
  have finalZ : z M = 0 := sub_self _
  have diff (i : ℕ) : z i-z (i+1) = IsProducer.excessTerm m B c i := by
    dsimp only [z, floorExcessTail]
    rw [Finset.sum_range_succ (IsProducer.excessTerm m B c) i]
    ring
  have value (i : ℕ) : (h i-h (i+1))*z (i+1)^2/(h i)^2 = ((i:ℝ)+1)/((i:ℝ)+2)*z (i+1)^2 := by
    rw [width]
    dsimp only [h]
    field_simp
  have cost (i : ℕ) : (z i-z (i+1))^2/(h i-h (i+1)) =
      ((i:ℝ)+1)*((i:ℝ)+2)*(IsProducer.excessTerm m B c i)^2 := by rw [width, diff, div_div_eq_mul_div, div_one, mul_comm]
  simp only [value, cost, finalZ, h, Nat.cast_zero, zero_add, div_one,
    ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, zero_div, add_zero] at H
  exact H

#print axioms floorExcessTail_energy

/-- For an admissible row the squared remaining excesses are paid for by
the peak times the excess already accumulated through the terminal index. -/
theorem producer_floorExcessTail_budget {c : ℕ →₀ ℤ} {m B : ℕ} (hP : IsProducer c m B) (M : ℕ) :
    (∑ i ∈ range M, ((i:ℝ)+1)/((i:ℝ)+2) * (floorExcessTail c m B M (i+1))^2) +
      2*(floorExcessTail c m B M 0)^2 ≤ 4*(peak c : ℝ)*floorExcessTail c m B M 0 := by
  have term (i : ℕ) : ((i:ℝ)+1)*((i:ℝ)+2)*IsProducer.excessTerm m B c i ≤ peak c := by
    unfold IsProducer.excessTerm
    rw [mul_div_cancel₀ _ (by positivity)]
    have hp : (stepWeight c (i+1) : ℝ) ≤ peak c := by exact_mod_cast hP.stepWeight_le_peak (i+1)
    split_ifs <;> linarith only [hp, Nat.cast_nonneg (α:=ℝ) m]
  have point (i : ℕ) : ((i:ℝ)+1)*((i:ℝ)+2)*(IsProducer.excessTerm m B c i)^2 ≤
      (peak c:ℝ)*IsProducer.excessTerm m B c i := by
    rw [sq, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (term i) (hP.excessTerm_nonneg i)
  apply (floorExcessTail_energy c m B M).trans
  have hs := sum_le_sum (s:=range M) (fun i _ => point i)
  rw [← mul_sum] at hs
  simpa only [floorExcessTail, range_zero, sum_empty, sub_zero, mul_assoc] using
    mul_le_mul_of_nonneg_left hs (by norm_num : (0:ℝ) ≤ 4)

/-- Every finite window of the infinite tail satisfies the same bound.
The loss at the outer boundary is the square of the total excess itself. -/
theorem producer_infinite_tail_budget {c : ℕ →₀ ℤ} {m B : ℕ} (hP : IsProducer c m B) (K : ℕ) :
    (∑ i ∈ range K, ((i:ℝ)+1)/((i:ℝ)+2) *
      (excess c m B - ∑ j ∈ range (i+1), IsProducer.excessTerm m B c j)^2) +
      2*(excess c m B)^2 ≤ 4*(peak c:ℝ)*excess c m B := by
  let E := excess c m B
  let e := IsProducer.excessTerm m B c
  let P (M : ℕ) := ∑ j ∈ range M, e j
  have ht : Filter.Tendsto P Filter.atTop (nhds E) := hP.hasSum_excess.tendsto_sum_nat
  have limit (i : ℕ) : Filter.Tendsto (fun M => floorExcessTail c m B M i) Filter.atTop
      (nhds (E-P i)) := ht.sub_const _
  have hzero : Filter.Tendsto (fun M => floorExcessTail c m B M 0) Filter.atTop (nhds E) := by
    simpa only [P, range_zero, sum_empty, sub_zero] using limit 0
  have hsum := tendsto_finsetSum (range K) (fun i _ =>
    ((limit (i+1)).pow 2).const_mul (((i:ℝ)+1)/((i:ℝ)+2)))
  apply le_of_tendsto_of_tendsto (hsum.add ((hzero.pow 2).const_mul 2)) (hzero.const_mul (4*(peak c:ℝ)))
  filter_upwards [Filter.eventually_ge_atTop K] with M hKM
  apply le_trans _ (producer_floorExcessTail_budget hP M)
  apply add_le_add _ le_rfl
  exact sum_le_sum_of_subset_of_nonneg (range_mono hKM) fun i _ _ => by positivity

#print axioms producer_floorExcessTail_budget
#print axioms producer_infinite_tail_budget

end
end GaloisForLFunctions.ArithmeticAuxiliaryDynamics.FloorSpectrum
