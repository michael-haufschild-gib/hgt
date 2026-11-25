import Mathlib.MeasureTheory.Measure.FiniteMeasurePi
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-! # Finite weighted sampling and independent ordered draws -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.BinaryOrientation.LargestPrime.Bands.Marks.FixedCount

open Filter Topology Set MeasureTheory
open scoped NNReal ENNReal
attribute [local instance] Classical.propDecidable

/-- Push finite nonnegative weights to the values of an observable. -/
def atomic {ι X : Type*} [Fintype ι] [MeasurableSpace X] (q : ι → ℝ≥0) (x : ι → X) : FiniteMeasure X :=
  ⟨Measure.sum (fun i => (q i : ℝ≥0∞) • Measure.dirac (x i)), ⟨by
    rw [Measure.sum_apply _ MeasurableSet.univ,tsum_fintype]
    simp⟩⟩

theorem atomic_apply {ι X : Type*} [Fintype ι] [MeasurableSpace X] (q : ι → ℝ≥0) (x : ι → X)
    {s : Set X} (hs : MeasurableSet s) :
    (atomic q x : Measure X) s = ∑ i, if x i ∈ s then (q i : ℝ≥0∞) else 0 := by
  change Measure.sum _ s = _
  rw [Measure.sum_apply _ hs,tsum_fintype]
  exact Finset.sum_congr rfl fun i _ => by
    by_cases hi : x i ∈ s <;> simp [Measure.smul_apply,Measure.dirac_apply' _ hs,hi]

theorem atomic_integral {ι X : Type*} [Fintype ι] [MeasurableSpace X] [MeasurableSingletonClass X]
    (q : ι → ℝ≥0) (x : ι → X) (f : X → ℝ) :
    (∫ t, f t ∂(atomic q x : Measure X)) = ∑ i, (q i:ℝ)*f (x i) := by
  change (∫ t, f t ∂Measure.sum (fun i => (q i:ℝ≥0∞) • Measure.dirac (x i))) = _
  rw [integral_sum_dirac (by simp),tsum_fintype]
  simp only [ENNReal.coe_toReal,smul_eq_mul]

theorem atomic_mass {ι X : Type*} [Fintype ι] [MeasurableSpace X] (q : ι → ℝ≥0) (x : ι → X) :
    (atomic q x).mass = ∑ i, q i := by
  apply ENNReal.coe_injective
  rw [FiniteMeasure.mass,FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure,atomic_apply q x MeasurableSet.univ]
  simp

/-- Law of k independent draws, with their original order retained. -/
def iid (k : ℕ) (μ : ProbabilityMeasure ℝ) : ProbabilityMeasure (Fin k → ℝ) :=
  ProbabilityMeasure.pi fun _ => μ

theorem iid_continuous (k : ℕ) : Continuous (iid k) :=
  ProbabilityMeasure.continuous_pi.comp (continuous_pi fun _ => continuous_id)

private theorem atomic_pi {ι : Type*} [Fintype ι] (q : ι → ℝ≥0) (x : ι → ℝ) (k : ℕ) :
    (atomic (fun y : Fin k → ι => ∏ i, q (y i)) (fun y => x ∘ y) : Measure (Fin k → ℝ)) =
      Measure.pi (fun _ : Fin k => (atomic q x : Measure ℝ)) := by
  symm
  apply Measure.pi_eq
  intro s hs
  rw [atomic_apply _ _ (MeasurableSet.univ_pi hs)]
  simp_rw [atomic_apply q x (hs _)]
  rw [Fintype.prod_sum]
  exact Finset.sum_congr rfl fun y _ => by
    simp only [Finset.prod_ite_zero,Finset.mem_univ,forall_const,ENNReal.ofNNReal_finsetProd,
      Set.mem_univ_pi,Function.comp_apply]

private theorem pi_normalized (μ : FiniteMeasure ℝ) (k : ℕ) :
    Measure.pi (fun _ : Fin k => (μ : Measure ℝ)) =
      ((μ.mass : ℝ≥0∞)^k) • (iid k μ.normalize : Measure (Fin k → ℝ)) := by
  apply Measure.pi_eq
  intro s hs
  rw [Measure.smul_apply,smul_eq_mul]
  change _ * Measure.pi (fun _ : Fin k => (μ.normalize : Measure ℝ)) (univ.pi s) = _
  rw [Measure.pi_pi]
  have hm (i : Fin k) : (μ : Measure ℝ) (s i) = (μ.mass:ℝ≥0∞)*(μ.normalize : Measure ℝ) (s i) := by
    rw [← FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure,← ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure,
      μ.self_eq_mass_mul_normalize (s i),ENNReal.coe_mul]
  simp only [hm,Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin]

/-- The unnormalized sum over all ordered tuples equals the product mass times iid expectation. -/
theorem tuple_sum {ι : Type*} [Fintype ι] (q : ι → ℝ≥0) (x : ι → ℝ) (k : ℕ) (f : (Fin k → ℝ) → ℝ) :
    (∑ y : Fin k → ι, (∏ i, (q (y i):ℝ))*f (x ∘ y)) =
      ((atomic q x).mass:ℝ)^k*(∫ t, f t ∂(iid k (atomic q x).normalize : Measure (Fin k → ℝ))) := by
  have H := atomic_integral (fun y : Fin k → ι => ∏ i, q (y i)) (fun y => x ∘ y) f
  rw [atomic_pi,pi_normalized,integral_smul_measure] at H
  simpa only [NNReal.coe_prod,ENNReal.toReal_pow,ENNReal.coe_toReal,smul_eq_mul] using H.symm

#print axioms atomic_apply
#print axioms atomic_integral
#print axioms atomic_mass
#print axioms iid_continuous
#print axioms tuple_sum

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.BinaryOrientation.LargestPrime.Bands.Marks.FixedCount
