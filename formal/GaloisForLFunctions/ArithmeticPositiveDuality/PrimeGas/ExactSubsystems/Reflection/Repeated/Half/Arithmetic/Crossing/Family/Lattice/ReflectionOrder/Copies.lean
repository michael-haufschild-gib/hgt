import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Family.Lattice.PrimeCalibration.Multiplicity.Resolution.Variation

/-! # Reflection response under independent quantum composition -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Lattice.ReflectionOrder

open Filter Finset Real
open scoped Topology
open _root_.HTGeometry (finiteGibbsPartition)

variable {I : Type*} [Fintype I]

/-- The multiplier relating one heat-trace difference to that of k+1
independent copies. The geometric sum also applies at an exact tie. -/
def copyFactor (E : I → ℝ) (k : ℕ) (t : ℝ) :=
  ∑ j ∈ range (k+1), (finiteGibbsPartition (-t) E)^j*(finiteGibbsPartition t E)^(k-j)

theorem copy_response (E : I → ℝ) (k : ℕ) (t : ℝ) :
    oddTrace (copyEnergy E (k+1)) t=copyFactor E k t*oddTrace E t := by
  rw [oddTrace_eq,oddTrace_eq,partition_copies,partition_copies]
  exact (geom_sum₂_mul _ _ (k+1)).symm

/-- The trace multiplier at zero is (k+1) times the kth power of the state
count. Normalizing each trace by its own state count leaves factor k+1. -/
theorem copy_factor_origin (E : I → ℝ) (k : ℕ) :
    copyFactor E k 0=(k+1 : ℝ)*(Fintype.card I : ℝ)^k := by
  have term (j : ℕ) (hj : j∈range (k+1)) :
      (Fintype.card I : ℝ)^j*(Fintype.card I : ℝ)^(k-j)=(Fintype.card I : ℝ)^k := by
    rw [←pow_add,Nat.add_sub_of_le (Nat.le_of_lt_succ (mem_range.mp hj))]
  simp only [copyFactor,finiteGibbsPartition,neg_zero,zero_mul,exp_zero,sum_const,
    card_univ,nsmul_eq_mul,mul_one]
  rw [sum_congr rfl term,sum_const,card_range,nsmul_eq_mul,Nat.cast_succ]

theorem copy_factor_pos [Nonempty I] (E : I → ℝ) (k : ℕ) (t : ℝ) : 0<copyFactor E k t := by
  unfold copyFactor
  have h (j : ℕ) : 0<(finiteGibbsPartition (-t) E)^j*(finiteGibbsPartition t E)^(k-j) :=
    mul_pos (pow_pos (_root_.HTGeometry.finiteGibbsPartition_pos _ _) _)
      (pow_pos (_root_.HTGeometry.finiteGibbsPartition_pos _ _) _)
  exact sum_pos (fun j _ => h j) ⟨0,mem_range.mpr (Nat.zero_lt_succ _)⟩

/-- Every finite leading order is preserved by independent copies.
The multiplier is positive for every nonempty state space. -/
theorem copy_leading (E : I → ℝ) (k m : ℕ) :
    ∀ c : ℝ, Tendsto (fun t => oddTrace E t/t^m) (𝓝[≠] 0) (𝓝 c) →
      Tendsto (fun t => oddTrace (copyEnergy E (k+1)) t/t^m) (𝓝[≠] 0)
        (𝓝 (((k+1 : ℝ)*(Fintype.card I : ℝ)^k)*c)) := by
  intro c hc
  have cont : Continuous (copyFactor E k) := by
    unfold copyFactor finiteGibbsPartition
    fun_prop
  have h : Tendsto (copyFactor E k) (𝓝[≠] 0) (𝓝 (copyFactor E k 0)) :=
    cont.continuousAt.continuousWithinAt.tendsto
  rw [copy_factor_origin] at h
  simpa only [copy_response,mul_div_assoc] using h.mul hc

#print axioms copy_response
#print axioms copy_factor_origin
#print axioms copy_factor_pos
#print axioms copy_leading

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Lattice.ReflectionOrder
