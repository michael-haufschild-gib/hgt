import GaloisForLFunctions.HTGeometry.CompactMomentWeakConvergence
import Mathlib.MeasureTheory.Constructions.UnitInterval
import Mathlib.MeasureTheory.Integral.Layercake

/-! # Weak laws and endpoint mass from interior cumulative probabilities -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Crossover.Bulk

open Filter MeasureTheory Set Real
open GaloisForLFunctions.HTGeometry
open scoped Topology

/-- Interior cumulative probability of a compact energy reading. -/
def cdf (μ : ProbabilityMeasure unitInterval) (u : ℝ) :=
  (μ : Measure unitInterval).real {x | (x:ℝ)≤u}

private def tail (μ : ProbabilityMeasure unitInterval) (k : ℕ) (t : ℝ) :=
  (μ : Measure unitInterval).real {x | t<(x:ℝ)^k}

private theorem moment_tail (μ : ProbabilityMeasure unitInterval) (k : ℕ) :
    (∫ x : unitInterval, (x:ℝ)^k ∂(μ : Measure unitInterval)) =
      ∫ t in Ioo (0:ℝ) 1, tail μ k t := by
  have hi : Integrable (fun x : unitInterval => (x:ℝ)^k) (μ : Measure unitInterval) :=
    (show Continuous (fun x : unitInterval => (x:ℝ)^k) from continuous_subtype_val.pow k).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  rw [hi.integral_eq_integral_meas_lt (Eventually.of_forall fun x => pow_nonneg x.property.1 _)]
  apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi Ioo_subset_Ioi_self
  intro t ht
  have h1 : 1≤t := le_of_not_gt fun h => ht.2 ⟨ht.1,h⟩
  have empty : {x : unitInterval | t<(x:ℝ)^k} = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro x
    exact not_lt.mpr ((pow_le_one₀ x.property.1 x.property.2).trans h1)
  rw [empty,measureReal_empty]

private theorem tail_cdf (μ : ProbabilityMeasure unitInterval) (n : ℕ) {t : ℝ} (ht : 0<t) :
    tail μ (n+1) t = 1-cdf μ (t^((n+1:ℕ):ℝ)⁻¹) := by
  let k := n+1
  have kp : 0<(k:ℝ) := by dsimp [k]; positivity
  let u := t^(k:ℝ)⁻¹
  have up : 0≤u := (rpow_pos_of_pos ht _).le
  have power : u^k=t := by
    dsimp [u]
    rw [←rpow_natCast,←rpow_mul ht.le,inv_mul_cancel₀ kp.ne',rpow_one]
  have es : {x : unitInterval | t<(x:ℝ)^k} = {x : unitInterval | (x:ℝ)≤u}ᶜ := by
    ext x
    simp only [mem_setOf_eq,mem_compl_iff,not_le]
    rw [←power,pow_lt_pow_iff_left₀ up x.property.1 (Nat.succ_ne_zero n)]
  change (μ : Measure unitInterval).real {x | t<(x:ℝ)^k} = 1-cdf μ u
  rw [es,measureReal_compl (measurableSet_le measurable_subtype_coe measurable_const),probReal_univ,cdf]

/-- Convergence of the cumulative probabilities at the interior thresholds
of the unit interval suffices even if the limiting law has endpoint atoms. -/
theorem weak_of_interior_cdf (μ : ℕ → ProbabilityMeasure unitInterval) (ν : ProbabilityMeasure unitInterval)
    (h : ∀ u : ℝ, 0<u → u<1 → Tendsto (fun N => cdf (μ N) u) atTop (𝓝 (cdf ν u))) :
    Tendsto μ atTop (𝓝 ν) := by
  apply probabilityMeasure_tendsto_of_integral_pow_tendsto
  intro k
  cases k with
  | zero =>
    simp only [pow_zero,integral_const,probReal_univ,one_smul]
    exact tendsto_const_nhds
  | succ n =>
    simp only [moment_tail]
    apply tendsto_integral_of_dominated_convergence (fun _ : ℝ => (1:ℝ))
    · intro N
      have anti : Antitone (fun t : ℝ => (μ N : Measure unitInterval) {x | t<(x:ℝ)^(n+1)}) :=
        fun _ _ le => measure_mono (fun _ hx => le.trans_lt hx)
      exact anti.measurable.ennreal_toReal.aestronglyMeasurable
    · exact integrableOn_const (by simp [Real.volume_Ioo])
    · intro N
      exact Eventually.of_forall (fun t => by
        rw [Real.norm_eq_abs,abs_of_nonneg (show 0≤tail (μ N) (n+1) t from ENNReal.toReal_nonneg)]
        exact measureReal_le_one)
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
      have hu := rpow_pos_of_pos ht.1 (((n+1:ℕ):ℝ)⁻¹)
      have hu' := rpow_lt_one ht.1.le ht.2 (show 0<((n+1:ℕ):ℝ)⁻¹ by positivity)
      simpa only [tail_cdf _ _ ht.1] using (h _ hu hu').const_sub 1

#print axioms weak_of_interior_cdf

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Crossover.Bulk
