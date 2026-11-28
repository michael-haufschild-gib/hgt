import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Composite.Collisions.Limits
import GaloisForLFunctions.HTGeometry.CountableWeightedDirac

/-! # Reciprocal prime labels as an atomic moment measure -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Composite.Collisions.Reconstruction

open Finset Filter Real MeasureTheory
open scoped Topology

/-- At a positive label this coordinate is the exponential of its negative energy. -/
def node (n : ℕ) := (n:ℝ)⁻¹

def weight (n : ℕ) := if n.Prime then (node n)^2 else 0

def intensity : Measure ℝ := _root_.HTGeometry.countableWeightedDirac weight node

private theorem node_nonneg (n : ℕ) : 0≤node n := inv_nonneg.mpr (Nat.cast_nonneg _)

theorem weight_nonneg (n : ℕ) : 0≤weight n := by
  rw [weight]
  split_ifs <;> positivity

private theorem weighted_node (k n : ℕ) :
    weight n*(node n)^k=(if n.Prime then (n:ℝ)^(-((k+2:ℕ):ℝ)) else 0) := by
  by_cases h : n.Prime
  · simp only [weight,if_pos h,node,rpow_neg (Nat.cast_nonneg n),rpow_natCast,←inv_pow,
      ←pow_add,Nat.add_comm 2 k]
  · simp only [weight,if_neg h,zero_mul]

private theorem weighted_summable (k : ℕ) : Summable (fun n => weight n*(node n)^k) := by
  have hk : (1:ℝ)<((k+2:ℕ):ℝ) := by exact_mod_cast (show 1<k+2 by omega)
  exact (_root_.RHTower.summable_primeIndicatorRpow hk).congr fun n => (weighted_node k n).symm

private theorem weight_summable : Summable weight := by
  simpa only [pow_zero,mul_one] using weighted_summable 0

instance : IsFiniteMeasure intensity := ⟨by
  rw [intensity,_root_.HTGeometry.countableWeightedDirac_univ_ofReal weight_nonneg weight_summable]
  exact ENNReal.ofReal_lt_top⟩

/-- All reciprocal labels lie in this compact interval. -/
theorem carried : intensity (Set.Icc (-1:ℝ) 1)ᶜ=0 := by
  have hi (n : ℕ) : node n≤1 := by
    by_cases e : n=0
    · simp [node,e]
    · exact inv_le_one_of_one_le₀ (by exact_mod_cast (show 1≤n from Nat.pos_of_ne_zero e))
  have off (n : ℕ) : (Set.Icc (-1:ℝ) 1)ᶜ.indicator (1 : ℝ → ENNReal) (node n)=0 := by
    apply Set.indicator_of_notMem
    intro h
    exact h ⟨(by linarith only [node_nonneg n]),hi n⟩
  rw [intensity,_root_.HTGeometry.countableWeightedDirac_apply _ _ measurableSet_Icc.compl]
  simp only [off,mul_zero,tsum_zero]

theorem integrable_moment (k : ℕ) : Integrable (fun x : ℝ => x^k) intensity := by
  apply _root_.HTGeometry.integrable_countableWeightedDirac weight_nonneg
    ((continuous_id.pow k).aestronglyMeasurable)
  refine (weighted_summable k).congr fun n => ?_
  change weight n*(node n)^k=weight n*|(node n)^k|
  rw [abs_of_nonneg (pow_nonneg (node_nonneg n) k)]

/-- The measured prime zeta constants are exactly the moments of the explicit intensity. -/
theorem moment (k : ℕ) : (∫ x,(x:ℝ)^k ∂intensity)=_root_.RHTower.primeZeta ((k+2:ℕ):ℝ) := by
  rw [intensity,_root_.HTGeometry.integral_countableWeightedDirac weight_nonneg (integrable_moment k),
    tsum_congr (weighted_node k)]
  exact _root_.RHTower.tsum_primeIndicatorRpow

theorem atom (n : ℕ) : intensity.real {node n}=weight n := by
  have inj : Function.Injective node := by
    intro i j h
    have e : (i:ℝ)=(j:ℝ) := inv_injective h
    exact_mod_cast e
  exact _root_.HTGeometry.countableWeightedDirac_real_singleton weight inj weight_nonneg n

#print axioms carried
#print axioms moment
#print axioms atom

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Composite.Collisions.Reconstruction
