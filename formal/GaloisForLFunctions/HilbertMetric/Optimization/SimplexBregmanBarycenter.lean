import GaloisForLFunctions.HilbertMetric.Optimization.WeightedSimplexResponse
import GaloisForLFunctions.HilbertMetric.Probability.BregmanCalibration

/-!
# The geometric barycenter of positive simplex observations

The exponential-chart part of Navas, arXiv:2611.18141, applies to the
corpus's inverse-metric simplex laws. Averaging their log-ratios yields
the normalized geometric mean. Exponential Bregman prediction in these
coordinates has exactly this unique probability-law minimizer.
-/

open scoped BigOperators
namespace GaloisForLFunctions.HilbertMetric.Optimization
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HilbertMetric.Probability
noncomputable section
variable {ι : Type*} [Fintype ι] {n : ℕ}

/-- Normalization cancels from ratios of positive simplex coordinates. -/
theorem simplexSampling_ratio (c : Fin (n + 1) → ℝ) (i j : Fin (n + 1)) :
    simplexSampling c i / simplexSampling c j = Real.exp (c j - c i) := by
  have hm : 0 < simplexComplianceMass c :=
    Finset.sum_pos (fun _ _ => inv_pos.mpr (Real.exp_pos _)) Finset.univ_nonempty
  rw [Real.exp_sub]
  unfold simplexSampling simplexCompliance
  field_simp [hm.ne', Real.exp_ne_zero]

/-- Log-ratio coordinates based at the zeroth component. -/
def simplexLogChart (c : Fin (n + 1) → ℝ) (i : Fin (n + 1)) : ℝ :=
  Real.log (simplexSampling c i / simplexSampling c 0)

theorem simplexLogChart_eq (c : Fin (n + 1) → ℝ) (i : Fin (n + 1)) :
    simplexLogChart c i = c 0 - c i := by
  rw [simplexLogChart, simplexSampling_ratio, Real.log_exp]

/-- Log-ratios determine the full probability law, including its normalization. -/
theorem simplexLogChart_eq_iff (c d : Fin (n + 1) → ℝ) :
    simplexLogChart c = simplexLogChart d ↔ simplexSampling c = simplexSampling d := by
  constructor
  · intro h
    have hp (i : Fin (n + 1)) :
        simplexSampling c i * simplexSampling d 0 =
          simplexSampling d i * simplexSampling c 0 := by
      apply (div_eq_div_iff (simplexSampling_pos c 0).ne'
        (simplexSampling_pos d 0).ne').mp
      rw [simplexSampling_ratio, simplexSampling_ratio]
      apply congrArg Real.exp
      simpa only [simplexLogChart_eq] using congrFun h i
    have hzero : simplexSampling c 0 = simplexSampling d 0 := by
      have hs := Finset.sum_congr (s₁ := Finset.univ) rfl (fun i _ => hp i)
      rw [← Finset.sum_mul, ← Finset.sum_mul,
        simplexSampling_sum, simplexSampling_sum, one_mul, one_mul] at hs
      exact hs.symm
    funext i
    have hi := hp i
    rw [hzero] at hi
    exact mul_right_cancel₀ (simplexSampling_pos d 0).ne' hi
  · intro h
    funext i
    simp only [simplexLogChart, h]

/-- Mean natural parameter of a finite family of positive simplex laws. -/
def simplexMeanParameter (p : FiniteProbabilityLaw ι)
    (c : ι → Fin (n + 1) → ℝ) (j : Fin (n + 1)) : ℝ :=
  finiteWeightedMean p.prob (fun i => c i j)

/-- The simplex output has exactly the averaged observation log-ratios. -/
theorem simplexLogChart_mean (p : FiniteProbabilityLaw ι)
    (c : ι → Fin (n + 1) → ℝ) (j : Fin (n + 1)) :
    simplexLogChart (simplexMeanParameter p c) j =
      finiteWeightedMean p.prob (fun i => simplexLogChart (c i) j) := by
  simp only [simplexLogChart_eq, simplexMeanParameter, finiteWeightedMean,
    mul_sub, Finset.sum_sub_distrib]

/-- Averaging the parameters really gives the normalized geometric mean
of the probabilities, with every source normalizer retained. -/
theorem simplexSampling_geometric_mean (p : FiniteProbabilityLaw ι)
    (c : ι → Fin (n + 1) → ℝ) (j : Fin (n + 1)) :
    simplexSampling (simplexMeanParameter p c) j =
      Real.exp (finiteWeightedMean p.prob (fun i => Real.log (simplexSampling (c i) j))) /
      ∑ k, Real.exp (finiteWeightedMean p.prob (fun i => Real.log (simplexSampling (c i) k))) := by
  let d : Fin (n + 1) → ℝ :=
    fun k => -finiteWeightedMean p.prob (fun i => Real.log (simplexSampling (c i) k))
  have hc : simplexLogChart (simplexMeanParameter p c) = simplexLogChart d := by
    funext k
    rw [simplexLogChart_mean, simplexLogChart_eq]
    simp only [simplexLogChart, Real.log_div (simplexSampling_pos (c _) _).ne'
      (simplexSampling_pos (c _) _).ne', finiteWeightedMean, mul_sub,
      Finset.sum_sub_distrib, d]
    ring
  rw [congrFun ((simplexLogChart_eq_iff _ _).mp hc) j]
  simp only [simplexSampling, simplexComplianceMass, simplexCompliance, d,
    Real.exp_neg, inv_inv]

/-- Expected loss summed over the actual log-ratio coordinates. -/
def simplexBregmanRisk (p : FiniteProbabilityLaw ι) (φ : ℝ → ℝ)
    (c : ι → Fin (n + 1) → ℝ) (d : Fin (n + 1) → ℝ) : ℝ :=
  ∑ j, bregmanRisk p φ (fun i => simplexLogChart (c i) j) (simplexLogChart d j)

/-- Exact Pythagorean risk split in the exponential chart. -/
theorem simplexBregmanRisk_split (p : FiniteProbabilityLaw ι) (φ : ℝ → ℝ)
    (c : ι → Fin (n + 1) → ℝ) (d : Fin (n + 1) → ℝ) :
    simplexBregmanRisk p φ c d = simplexBregmanRisk p φ c (simplexMeanParameter p c) +
      ∑ j, scalarBregman φ (simplexLogChart (simplexMeanParameter p c) j)
        (simplexLogChart d j) := by
  unfold simplexBregmanRisk
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [bregmanRisk_mean_split p φ _ (simplexLogChart d j), simplexLogChart_mean]

/-- Exponential-chart estimation selects one probability law; additive parameter
shifts do not create distinct forecasts. -/
theorem simplexExponentialRisk_minimizer_iff (p : FiniteProbabilityLaw ι)
    (c : ι → Fin (n + 1) → ℝ) (d : Fin (n + 1) → ℝ) :
    (∀ e, simplexBregmanRisk p Real.exp c d ≤ simplexBregmanRisk p Real.exp c e) ↔
      simplexSampling d = simplexSampling (simplexMeanParameter p c) := by
  constructor
  · intro h
    have hb := h (simplexMeanParameter p c)
    rw [simplexBregmanRisk_split p Real.exp c d] at hb
    have hz : (∑ j, scalarBregman Real.exp
        (simplexLogChart (simplexMeanParameter p c) j) (simplexLogChart d j)) = 0 :=
      le_antisymm (by linarith only [hb])
        (Finset.sum_nonneg fun j _ => scalarBregman_exp_nonneg _ _)
    have hall := (Finset.sum_eq_zero_iff_of_nonneg
      (fun j (_ : j ∈ Finset.univ) => scalarBregman_exp_nonneg
        (simplexLogChart (simplexMeanParameter p c) j) (simplexLogChart d j))).mp hz
    apply (simplexLogChart_eq_iff _ _).mp
    funext j
    exact ((scalarBregman_exp_eq_zero_iff _ _).mp (hall j (Finset.mem_univ j))).symm
  · intro h e
    have hc := (simplexLogChart_eq_iff _ _).mpr h
    have heq : simplexBregmanRisk p Real.exp c d =
        simplexBregmanRisk p Real.exp c (simplexMeanParameter p c) := by
      simp only [simplexBregmanRisk, hc]
    rw [heq, simplexBregmanRisk_split p Real.exp c e]
    exact le_add_of_nonneg_right (Finset.sum_nonneg fun j _ => scalarBregman_exp_nonneg _ _)

#print axioms simplexSampling_geometric_mean
#print axioms simplexBregmanRisk_split
#print axioms simplexExponentialRisk_minimizer_iff

end
end GaloisForLFunctions.HilbertMetric.Optimization
