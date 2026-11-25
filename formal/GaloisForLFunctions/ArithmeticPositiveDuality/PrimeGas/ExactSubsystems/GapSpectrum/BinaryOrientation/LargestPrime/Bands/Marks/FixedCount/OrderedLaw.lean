import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.GapSpectrum.BinaryOrientation.LargestPrime.Bands.Marks.FixedCount.Occupation

/-! # Conditional order statistics of the occupied prime energies -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.BinaryOrientation.LargestPrime.Bands.Marks.FixedCount

open Filter Topology Set MeasureTheory _root_.RHTower
open GaloisForLFunctions.HTGeometry
open scoped NNReal ENNReal
attribute [local instance] Classical.propDecidable

/-- Conditional law of the ordered energies on the Born count slice. -/
def conditional (c d a : ℝ) (h : Ioi (0:ℝ)) (k : ℕ) :=
  (slice (added c d h) (1+a*h.val) h k).normalize

/-- Order statistics of k independent draws. -/
def orderStatistics (k : ℕ) (μ : ProbabilityMeasure ℝ) : ProbabilityMeasure (Fin k → ℝ) :=
  (iid k μ).map (continuous_sort k).measurable.aemeasurable

theorem orderStatistics_continuous (k : ℕ) : Continuous (orderStatistics k) :=
  (ProbabilityMeasure.continuous_map (continuous_sort k)).comp (iid_continuous k)

private theorem mass_mul_integral {X : Type*} [Nonempty X] [MeasurableSpace X] (μ : FiniteMeasure X) (F : X → ℝ) :
    (μ.mass:ℝ)*(∫ t,F t ∂(μ.normalize : Measure X)) = ∫ t,F t ∂(μ : Measure X) := by
  have H := congrArg (fun ν : FiniteMeasure X => ∫ t,F t ∂(ν : Measure X)) μ.self_eq_mass_smul_normalize
  exact (H.trans (integral_smul_nnreal_measure F μ.mass)).symm

/-- Total iid weight of the tuples with distinct prime labels. -/
def distinctMass (c d a : ℝ) (h : Ioi (0:ℝ)) (k : ℕ) :=
  (k.factorial:ℝ)*finiteSquarefreePartition (added c d h) (1+a*h.val)*atom (added c d h) (1+a*h.val) k

private theorem distinct_eq (c d a : ℝ) (h : Ioi (0:ℝ)) (k : ℕ) (F : (Fin k → ℝ) → ℝ) :
    distinctSum (fun p : ↥(added c d h) => (odds a h p.val:ℝ)) (fun p => location h p.val) k F =
      distinctMass c d a h k*(∫ t,F t ∂(conditional c d a h k : Measure _)) := by
  rw [distinct_born,← mass_mul_integral,slice_mass]
  exact (mul_assoc _ _ _).symm

theorem distinctMass_limit {c d : ℝ} (hc : 0 < c) (hcd : c < d) (a : ℝ) (k : ℕ) :
    Tendsto (fun h => distinctMass c d a h k) criticalApproach (𝓝 ((VacuumCalibration.mass c d a)^k)) := by
  let m := VacuumCalibration.mass c d a
  have H := ((partition_limit hc hcd a).const_mul (k.factorial:ℝ)).mul (atom_limit hc hcd a k)
  have he : (k.factorial:ℝ)*Real.exp m*(Real.exp (-m)*m^k/k.factorial) = m^k := by
    rw [Real.exp_neg]
    field_simp [(Real.exp_pos m).ne',Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)]
  rwa [show VacuumCalibration.mass c d a = m from rfl,he] at H

private def allSum {ι : Type*} [Fintype ι] (q : ι → ℝ≥0) (x : ι → ℝ) (k : ℕ) (F : (Fin k → ℝ) → ℝ) :=
  ∑ y : Fin k → ι, (∏ i,(q (y i):ℝ))*F (sortedTuple (x ∘ y))

private theorem all_eq {ι : Type*} [Fintype ι] (q : ι → ℝ≥0) (x : ι → ℝ) (k : ℕ)
    (F : BoundedContinuousFunction (Fin k → ℝ) ℝ) :
    allSum q x k F = ((atomic q x).mass:ℝ)^k*(∫ t,F t ∂(orderStatistics k (atomic q x).normalize : Measure _)) := by
  rw [orderStatistics,ProbabilityMeasure.toMeasure_map,integral_map (continuous_sort k).measurable.aemeasurable
    F.continuous.aestronglyMeasurable]
  exact tuple_sum q x k (fun t => F (sortedTuple t))

/-- Removing collisions costs at most their total weight times the supremum norm of the test. -/
private theorem collision_bound {ι : Type*} [Fintype ι] (q : ι → ℝ≥0) (x : ι → ℝ) (k : ℕ)
    (F : BoundedContinuousFunction (Fin k → ℝ) ℝ) :
    |allSum q x k F-distinctSum (fun p => (q p:ℝ)) x k F| ≤
      ‖F‖*(allSum q x k 1-distinctSum (fun p => (q p:ℝ)) x k 1) := by
  unfold allSum distinctSum
  simp only [Pi.one_apply,mul_one,← Finset.sum_sub_distrib,Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun y _ => ?_)
  by_cases hy : Function.Injective y
  · simp [hy]
  · have hw : 0 ≤ ∏ i, (q (y i):ℝ) := Finset.prod_nonneg fun i _ => (q (y i)).property
    simp only [hy,if_false,sub_zero,abs_mul,abs_of_nonneg hw]
    rw [mul_comm ‖F‖]
    exact mul_le_mul_of_nonneg_left (F.norm_coe_le_norm _) hw

theorem onePrime_mass_limit {c d : ℝ} (hc : 0 < c) (hcd : c < d) (a : ℝ) :
    Tendsto (fun h => ((onePrime c d a h).mass:ℝ)) criticalApproach (𝓝 (VacuumCalibration.mass c d a)) := by
  have H := (NNReal.continuous_coe.tendsto _).comp (onePrime_limit hc hcd a).mass
  rwa [intensity_mass] at H

/-- The entire repeated-prime weight vanishes, including the zero- and one-draw cases. -/
theorem repeated_mass_limit {c d : ℝ} (hc : 0 < c) (hcd : c < d) (a : ℝ) (k : ℕ) :
    Tendsto (fun h => ((onePrime c d a h).mass:ℝ)^k-distinctMass c d a h k) criticalApproach (𝓝 0) := by
  simpa only [sub_self] using ((onePrime_mass_limit hc hcd a).pow k).sub (distinctMass_limit hc hcd a k)

/-- Exact conditioning has positive probability for every sufficiently small h. -/
theorem eventual_count_positive {c d : ℝ} (hc : 0 < c) (hcd : c < d) (a : ℝ) (k : ℕ) :
    ∀ᶠ h in criticalApproach, 0 < atom (added c d h) (1+a*h.val) k :=
  (atom_limit hc hcd a k).eventually_const_lt
    (div_pos (mul_pos (Real.exp_pos _) (pow_pos (mass_pos hc hcd a) k)) (Nat.cast_pos.mpr (Nat.factorial_pos k)))

/-- Conditional on the actual count, the ordered energies converge jointly to iid order statistics. -/
theorem conditional_limit {c d : ℝ} (hc : 0 < c) (hcd : c < d) (a : ℝ) (k : ℕ) :
    Tendsto (fun h => conditional c d a h k) criticalApproach (𝓝 (orderStatistics k (draw hc hcd.le a))) := by
  apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro F
  let test (μ : ProbabilityMeasure (Fin k → ℝ)) := ∫ t,F t ∂(μ : Measure _)
  let full (h : Ioi (0:ℝ)) := ((onePrime c d a h).mass:ℝ)^k*test (orderStatistics k (onePrime c d a h).normalize)
  let kept (h : Ioi (0:ℝ)) := distinctMass c d a h k*test (conditional c d a h k)
  let m := (VacuumCalibration.mass c d a)^k
  let μ := orderStatistics k (draw hc hcd.le a)
  have hP := ((orderStatistics_continuous k).tendsto _).comp (draw_limit hc hcd a)
  have hf : Tendsto full criticalApproach (𝓝 (m*test μ)) :=
    ((onePrime_mass_limit hc hcd a).pow k).mul (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hP F)
  have hd : Tendsto (fun h => |full h-kept h|) criticalApproach (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall fun _ => abs_nonneg _) _
      (show Tendsto (fun h => ‖F‖*(((onePrime c d a h).mass:ℝ)^k-distinctMass c d a h k)) _ (𝓝 0)
        by simpa only [mul_zero] using (repeated_mass_limit hc hcd a k).const_mul ‖F‖)
    apply Eventually.of_forall
    intro h
    let q (p : ↥(added c d h)) := odds a h p.val
    let x (p : ↥(added c d h)) := location h p.val
    have hb := collision_bound q x k F
    have ha : atomic q x = onePrime c d a h := rfl
    have h1 : allSum q x k 1 = ((atomic q x).mass:ℝ)^k := by
      simpa only [BoundedContinuousFunction.coe_one,Pi.one_apply,integral_const,probReal_univ,one_smul,mul_one]
        using all_eq q x k (1 : BoundedContinuousFunction (Fin k → ℝ) ℝ)
    rw [h1,all_eq,distinct_eq,distinct_eq,ha] at hb
    simp only [Pi.one_apply,integral_const,probReal_univ,one_smul,mul_one] at hb
    exact hb
  have hk : Tendsto kept criticalApproach (𝓝 (m*test μ)) := hf.congr_dist (by simpa only [Real.dist_eq] using hd)
  have hm := (pow_pos (mass_pos hc hcd a) k).ne'
  have H := hk.div (distinctMass_limit hc hcd a k) hm
  rw [mul_div_cancel_left₀ _ hm] at H
  apply H.congr'
  filter_upwards [(distinctMass_limit hc hcd a k).eventually_ne hm] with h hh
  exact mul_div_cancel_left₀ _ hh

#print axioms orderStatistics_continuous
#print axioms distinctMass_limit
#print axioms onePrime_mass_limit
#print axioms repeated_mass_limit
#print axioms eventual_count_positive
#print axioms conditional_limit

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.BinaryOrientation.LargestPrime.Bands.Marks.FixedCount
