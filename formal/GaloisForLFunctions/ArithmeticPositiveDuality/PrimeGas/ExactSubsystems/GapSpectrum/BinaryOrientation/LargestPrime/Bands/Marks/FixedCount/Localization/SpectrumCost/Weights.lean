import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.GapSpectrum.BinaryOrientation.LargestPrime.Bands.Marks.FixedCount.Localization.Endpoints.Geometry

/-! # Finite Gibbs transforms on the physical count sector -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.BinaryOrientation.LargestPrime.Bands.Marks.FixedCount.Localization.SpectrumCost

open Filter Topology Set MeasureTheory Endpoints _root_.RHTower
open scoped NNReal
attribute [local instance] Classical.propDecidable

/-- Unnormalized partition sum with the observable F in the exponent. -/
def partitionWith (S : Finset Nat.Primes) (β : ℝ) (h : Ioi (0:ℝ)) {k : ℕ} (F : (Fin k → ℝ) → ℝ) :=
  ∑ R : BreadthSubset k ↥S, Real.exp (-β*energyOf R)*Real.exp (F (spectrum h R)/h.val)

/-- Changing inverse temperature adds a linear observable to the exponent at unit temperature. -/
def tiltedObservable {k : ℕ} (β : ℝ) (F : (Fin k → ℝ) → ℝ) (v : Fin k → ℝ) :=
  F v+(1-β)*∑ i, v i

theorem partitionWith_tilt (S : Finset Nat.Primes) (β : ℝ) (h : Ioi (0:ℝ)) {k : ℕ} (F : (Fin k → ℝ) → ℝ) :
    partitionWith S β h F = partitionWith S 1 h (tiltedObservable β F) := by
  unfold partitionWith
  apply Finset.sum_congr rfl
  intro R _
  rw [← Real.exp_add,← Real.exp_add,tiltedObservable,sum_spectrum]
  congr 1
  field_simp [(show 0 < h.val from h.property).ne']
  ring

/-- Normalizing the finite count slice recovers the Born expectation of its exponential reading. -/
theorem partitionWith_eq (c d β : ℝ) (h : Ioi (0:ℝ)) {k : ℕ} (F : (Fin k → ℝ) → ℝ) :
    partitionWith (added c d h) β h F = coefficient (added c d h) β k *
      ∫ v, Real.exp (F v/h.val) ∂(thermalLaw c d h β k : Measure _) := by
  let S := added c d h
  let μ := slice S β h k
  let g (v : Fin k → ℝ) := Real.exp (F v/h.val)
  have H := congrArg (fun ν : FiniteMeasure (Fin k → ℝ) => ∫ v, g v ∂(ν : Measure _)) μ.self_eq_mass_smul_normalize
  have hm : (μ.mass:ℝ)*(∫ v, g v ∂(μ.normalize : Measure _)) = ∫ v, g v ∂(μ : Measure _) :=
    (H.trans (integral_smul_nnreal_measure g μ.mass)).symm
  change partitionWith S β h F = coefficient S β k * ∫ v, g v ∂(μ.normalize : Measure _)
  rw [coefficient,← slice_mass S β h k, mul_assoc,hm]
  change _ = finiteSquarefreePartition S β * ∫ v, g v ∂(slice S β h k : Measure _)
  rw [slice,atomic_integral,Finset.mul_sum,partitionWith]
  apply Finset.sum_congr rfl
  intro R _
  change _ = finiteSquarefreePartition S β * (finiteSquarefreeBornWeight S β _ * g _)
  rw [← mul_assoc,finiteSquarefreeBornWeight_eq,energyOf_eq,mul_div_cancel₀ _ (finiteSquarefreePartition_pos S β).ne']

/-- Once the count exists at one temperature it has strictly positive weight at every temperature. -/
theorem eventually_positive {c d : ℝ} (hc : 0 < c) (hcd : c < d) (β : ℝ) {k : ℕ} (F : (Fin k → ℝ) → ℝ) :
    ∀ᶠ h in criticalApproach, 0 < coefficient (added c d h) β k ∧ 0 < partitionWith (added c d h) β h F := by
  filter_upwards [(coefficient_limit hc hcd k).eventually_const_lt (critical_limit_pos hc hcd k)] with h hh
  rw [coefficient_exp_sum _ 1 h k] at hh
  obtain ⟨R,hR,_⟩ := (Finset.sum_pos_iff_of_nonneg (fun T _ => (Real.exp_pos (-(1:ℝ)*energyOf T)).le)).mp hh
  rw [coefficient_exp_sum _ β h k,partitionWith]
  exact ⟨Finset.sum_pos (fun _ _ => Real.exp_pos _) ⟨R,hR⟩,
    Finset.sum_pos (fun _ _ => mul_pos (Real.exp_pos _) (Real.exp_pos _)) ⟨R,hR⟩⟩

/-- An upper bound on a reading over all configurations bounds its critical transform. -/
theorem total_upper (S : Finset Nat.Primes) (h : Ioi (0:ℝ)) {k : ℕ} (F : (Fin k → ℝ) → ℝ)
    (M : ℝ) (hM : ∀ R : BreadthSubset k ↥S, F (spectrum h R) ≤ M) :
    partitionWith S 1 h F ≤ Real.exp (M/h.val)*coefficient S 1 k := by
  rw [coefficient_exp_sum S 1 h k,Finset.mul_sum,partitionWith]
  apply Finset.sum_le_sum
  intro R _
  rw [mul_comm (Real.exp (M/h.val))]
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (div_le_div_of_nonneg_right (hM R) h.property.le)) (Real.exp_pos _).le

/-- A neighborhood on which F exceeds t contributes its critical event weight times exp(t/h). -/
theorem event_lower (S : Finset Nat.Primes) (h : Ioi (0:ℝ)) {k : ℕ} (F : (Fin k → ℝ) → ℝ)
    (G : Set (Fin k → ℝ)) (t : ℝ) (ht : ∀ R : BreadthSubset k ↥S, spectrum h R ∈ G → t ≤ F (spectrum h R)) :
    Real.exp (t/h.val)*eventWeight S 1 h k G ≤ partitionWith S 1 h F := by
  rw [eventWeight,Finset.mul_sum,partitionWith]
  apply Finset.sum_le_sum
  intro R _
  by_cases hr : spectrum h R ∈ G
  · rw [if_pos hr,mul_comm (Real.exp (t/h.val))]
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (div_le_div_of_nonneg_right (ht R hr) h.property.le)) (Real.exp_pos _).le
  · rw [if_neg hr,mul_zero]
    exact (mul_pos (Real.exp_pos _) (Real.exp_pos _)).le

#print axioms partitionWith_tilt
#print axioms partitionWith_eq
#print axioms eventually_positive
#print axioms event_lower

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.BinaryOrientation.LargestPrime.Bands.Marks.FixedCount.Localization.SpectrumCost
