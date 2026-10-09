import GaloisForLFunctions.HTGeometry.FiniteGibbsDifferentialBoundary
import GaloisForLFunctions.HTGeometry.SelectionSynthesisDivergence

/-!
# Size bias and relative entropy along a finite Gibbs family

The size-bias identity in arXiv:2610.10584, Proposition 8.1, applies to
every finite Gibbs spectrum. The statistic `exp (-t E)` changes inverse
temperature from `β` to `β + t`. Its normalizer is a partition-function
ratio, and its relative entropy is the logarithmic normalizer minus the
expected logarithm of the statistic.
-/

noncomputable section
open scoped BigOperators
open GaloisForLFunctions.HTGeometry

namespace HTGeometry

variable {n : ℕ}

/-- The exponential energy statistic has an exact partition-ratio mean. -/
theorem finiteGibbs_exp_mean (β t : ℝ) (E : Fin (n + 1) → ℝ) :
    (∑ i, finiteGibbsStateWeight β E i * Real.exp (-t * E i)) =
      finiteGibbsPartition (β + t) E / finiteGibbsPartition β E := by
  simp only [finiteGibbsStateWeight, div_mul_eq_mul_div, ← Real.exp_add,
    ← Finset.sum_div]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  ring

/-- Size bias by an exponential statistic is a temperature shift. -/
theorem finiteGibbs_sizeBias (β t : ℝ) (E : Fin (n + 1) → ℝ) (i : Fin (n + 1)) :
    finiteGibbsStateWeight β E i * Real.exp (-t * E i) /
        (∑ j, finiteGibbsStateWeight β E j * Real.exp (-t * E j)) =
      finiteGibbsStateWeight (β + t) E i := by
  rw [finiteGibbs_exp_mean]
  simp only [finiteGibbsStateWeight, div_mul_eq_mul_div, ← Real.exp_add]
  rw [show -β * E i + -t * E i = -(β + t) * E i by ring]
  exact div_div_div_cancel_right₀ (finiteGibbsPartition_pos β E).ne' _ _

/-- The log likelihood ratio is affine in the observed energy. -/
theorem finiteGibbs_log_ratio (β γ : ℝ) (E : Fin (n + 1) → ℝ) (i : Fin (n + 1)) :
    Real.log (finiteGibbsStateWeight β E i / finiteGibbsStateWeight γ E i) =
      Real.log (finiteGibbsPartition γ E) - Real.log (finiteGibbsPartition β E) +
        (γ - β) * E i := by
  rw [Real.log_div (finiteGibbsStateWeight_pos β E i).ne'
    (finiteGibbsStateWeight_pos γ E i).ne']
  simp only [finiteGibbsStateWeight,
    Real.log_div (Real.exp_ne_zero _) (finiteGibbsPartition_pos _ E).ne', Real.log_exp]
  ring

/-- Exact relative entropy between any two temperatures of the same spectrum. -/
theorem finiteGibbs_relativeEntropy (β γ : ℝ) (E : Fin (n + 1) → ℝ) :
    relEntropy (finiteGibbsStateWeight β E) (finiteGibbsStateWeight γ E) =
      Real.log (finiteGibbsPartition γ E) - Real.log (finiteGibbsPartition β E) +
        (γ - β) * finiteGibbsEnergyMean β E := by
  simp only [relEntropy, tsum_fintype, finiteGibbs_log_ratio, mul_add,
    Finset.sum_add_distrib, ← Finset.sum_mul, sum_finiteGibbsStateWeight_eq_one,
    one_mul]
  congr 1
  rw [finiteGibbsEnergyMean, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The paper's size-bias entropy formula, for the existing Gibbs probabilities. -/
theorem finiteGibbs_sizeBias_entropy (β t : ℝ) (E : Fin (n + 1) → ℝ) :
    relEntropy (finiteGibbsStateWeight β E) (finiteGibbsStateWeight (β + t) E) =
      Real.log (∑ i, finiteGibbsStateWeight β E i * Real.exp (-t * E i)) -
        ∑ i, finiteGibbsStateWeight β E i * Real.log (Real.exp (-t * E i)) := by
  rw [finiteGibbs_relativeEntropy, finiteGibbs_exp_mean,
    Real.log_div (finiteGibbsPartition_pos (β + t) E).ne'
      (finiteGibbsPartition_pos β E).ne']
  simp only [Real.log_exp]
  rw [show β + t - β = t by ring, finiteGibbsEnergyMean, Finset.mul_sum]
  have hs : (∑ i, finiteGibbsStateWeight β E i * (-t * E i)) =
      -(∑ i, t * (finiteGibbsStateWeight β E i * E i)) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hs]
  ring

/-- Nonnegative divergence gives the global tangent inequality for log partition. -/
theorem finiteGibbs_logPartition_tangent (β γ : ℝ) (E : Fin (n + 1) → ℝ) :
    Real.log (finiteGibbsPartition β E) + (β - γ) * finiteGibbsEnergyMean β E ≤
      Real.log (finiteGibbsPartition γ E) := by
  have h := relEntropy_nonneg
    (fun i => (finiteGibbsStateWeight_pos β E i).le)
    (finiteGibbsStateWeight_pos γ E)
    (by simpa only [sum_finiteGibbsStateWeight_eq_one] using
      hasSum_fintype (finiteGibbsStateWeight β E))
    (by simpa only [sum_finiteGibbsStateWeight_eq_one] using
      hasSum_fintype (finiteGibbsStateWeight γ E))
    (hasSum_fintype _).summable
  rw [finiteGibbs_relativeEntropy] at h
  nlinarith

/-- Symmetrized divergence is exactly the temperature/energy response product. -/
theorem finiteGibbs_symmetric_relativeEntropy (β γ : ℝ) (E : Fin (n + 1) → ℝ) :
    relEntropy (finiteGibbsStateWeight β E) (finiteGibbsStateWeight γ E) +
      relEntropy (finiteGibbsStateWeight γ E) (finiteGibbsStateWeight β E) =
        (γ - β) * (finiteGibbsEnergyMean β E - finiteGibbsEnergyMean γ E) := by
  rw [finiteGibbs_relativeEntropy, finiteGibbs_relativeEntropy]
  ring

/-- The energy response has the opposite sign to the temperature change. -/
theorem finiteGibbs_temperature_energy_sign (β γ : ℝ) (E : Fin (n + 1) → ℝ) :
    0 ≤ (γ - β) * (finiteGibbsEnergyMean β E - finiteGibbsEnergyMean γ E) := by
  have h₁ := finiteGibbs_logPartition_tangent β γ E
  have h₂ := finiteGibbs_logPartition_tangent γ β E
  nlinarith

/-- Probability of an energy value, including its spectral multiplicity. -/
def finiteGibbsEnergyWeight (β : ℝ) (E : Fin (n + 1) → ℝ) (e : ℝ) : ℝ :=
  ∑ i ∈ Finset.univ.filter (fun i => E i = e), finiteGibbsStateWeight β E i

private theorem energyWeight_formula (β : ℝ) (E : Fin (n + 1) → ℝ) (e : ℝ) :
    finiteGibbsEnergyWeight β E e =
      (Finset.univ.filter (fun i => E i = e)).card *
        (Real.exp (-β * e) / finiteGibbsPartition β E) := by
  classical
  unfold finiteGibbsEnergyWeight
  calc
    _ = ∑ _i ∈ Finset.univ.filter (fun i => E i = e),
        Real.exp (-β * e) / finiteGibbsPartition β E := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [finiteGibbsStateWeight, (Finset.mem_filter.mp hi).2]
    _ = _ := by simp

private theorem energyWeight_log_ratio (β γ : ℝ) (E : Fin (n + 1) → ℝ)
    (e : ℝ) (he : e ∈ Finset.univ.image E) :
    Real.log (finiteGibbsEnergyWeight β E e / finiteGibbsEnergyWeight γ E e) =
      Real.log (finiteGibbsPartition γ E) - Real.log (finiteGibbsPartition β E) +
        (γ - β) * e := by
  classical
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp he
  have hc : ((Finset.univ.filter (fun j => E j = E i)).card : ℝ) ≠ 0 := by
    have hp : 0 < (Finset.univ.filter (fun j => E j = E i)).card :=
      Finset.card_pos.mpr ⟨i, by simp⟩
    exact_mod_cast hp.ne'
  rw [energyWeight_formula, energyWeight_formula, mul_div_mul_left _ _ hc]
  exact finiteGibbs_log_ratio β γ E i

/-- Energy is a sufficient statistic for every pair of Gibbs temperatures:
combining degenerate energy levels loses exactly zero relative entropy. -/
theorem finiteGibbs_energy_lossless (β γ : ℝ) (E : Fin (n + 1) → ℝ) :
    (∑ e ∈ Finset.univ.image E, finiteGibbsEnergyWeight β E e *
      Real.log (finiteGibbsEnergyWeight β E e / finiteGibbsEnergyWeight γ E e)) =
        relEntropy (finiteGibbsStateWeight β E) (finiteGibbsStateWeight γ E) := by
  classical
  rw [relEntropy, tsum_fintype]
  calc
    _ = ∑ e ∈ Finset.univ.image E, ∑ i ∈ Finset.univ.filter (fun i => E i = e),
        finiteGibbsStateWeight β E i *
          Real.log (finiteGibbsStateWeight β E i / finiteGibbsStateWeight γ E i) := by
      apply Finset.sum_congr rfl
      intro e he
      rw [energyWeight_log_ratio β γ E e he, finiteGibbsEnergyWeight, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      rw [finiteGibbs_log_ratio, (Finset.mem_filter.mp hi).2]
    _ = _ := Finset.sum_fiberwise_of_maps_to
      (fun i hi => Finset.mem_image_of_mem E hi) _

end HTGeometry
