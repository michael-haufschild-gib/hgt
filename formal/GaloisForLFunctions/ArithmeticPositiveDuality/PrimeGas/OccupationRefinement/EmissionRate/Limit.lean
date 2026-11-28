import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.EmissionRate.Readout

/-! # The initial vacuum loss measures the extended Hamiltonian energy -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.EmissionRate

open ModeCapacities Filter Topology
open scoped ENNReal

/-- The energy form is allowed to diverge for a Hilbert-space state. -/
def form (f : Gas) : ℝ≥0∞ := ∑' n : ℕ+, ENNReal.ofReal (energy n * ‖f n‖ ^ 2)

/-- Extension of the positive-time instrument reading to a real time axis. -/
def reading (s : Conserving) (f : Gas) (t : ℝ) : ℝ≥0∞ :=
  if ht : 0 < t then ENNReal.ofReal (loss s f ⟨t, ht⟩) else 0

private def term (f : Gas) (n : ℕ+) (t : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (increment t (energy n) * ‖f n‖ ^ 2)

private theorem reading_eq (s : Conserving) (f : Gas) {t : ℝ} (ht : 0 < t) :
    reading s f t = ∑' n, term f n t := by
  have H := loss_sum s f ⟨t, ht⟩
  rw [reading, dif_pos ht, ← H.tsum_eq]
  exact ENNReal.ofReal_tsum_of_nonneg (fun n =>
    mul_nonneg (increment_nonneg ht (energy_nonneg n)) (sq_nonneg _)) H.summable

theorem reading_le (s : Conserving) (f : Gas) (t : ℝ) : reading s f t ≤ form f := by
  by_cases ht : 0 < t
  · rw [reading_eq s f ht, form]
    exact ENNReal.tsum_le_tsum fun n => ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (increment_le ht (energy n)) (sq_nonneg _))
  · simp only [reading, dif_neg ht, zero_le]

/-- At short times every finite partial energy is recovered. Taking their
supremum gives the two-sided order limit even when the energy is infinite. -/
theorem initial_rate (s : Conserving) (f : Gas) :
    Tendsto (reading s f) (𝓝[>] 0) (𝓝 (form f)) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    rw [form, ENNReal.tsum_eq_iSup_sum, lt_iSup_iff] at ha
    obtain ⟨S, hS⟩ := ha
    have lim : Tendsto (fun t => ∑ n ∈ S, term f n t) (𝓝[>] 0)
        (𝓝 (∑ n ∈ S, ENNReal.ofReal (energy n * ‖f n‖ ^ 2))) :=
      tendsto_finsetSum S fun n _ => ENNReal.continuous_ofReal.continuousAt.tendsto.comp
        ((increment_limit (energy n)).mul_const (‖f n‖ ^ 2))
    filter_upwards [(tendsto_order.mp lim).1 a hS,
      (self_mem_nhdsWithin : ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < t)] with t h ht
    rw [reading_eq s f ht]
    exact h.trans_le (ENNReal.sum_le_tsum S)
  · intro a ha
    exact Filter.Eventually.of_forall fun t => (reading_le s f t).trans_lt ha

/-- The largest possible measured rate is already the initial rate. -/
theorem supremum_rate (s : Conserving) (f : Gas) :
    (⨆ t : Duration, ENNReal.ofReal (loss s f t)) = form f := by
  apply le_antisymm
  · apply iSup_le
    intro t
    have ht : 0 < t.val := t.property
    simpa only [reading, dif_pos ht] using reading_le s f t.val
  · apply le_of_tendsto (initial_rate s f)
    filter_upwards [(self_mem_nhdsWithin : ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < t)] with t ht
    change 0 < t at ht
    rw [reading, dif_pos ht]
    exact le_iSup (fun u : Duration => ENNReal.ofReal (loss s f u)) ⟨t, ht⟩

#print axioms initial_rate
#print axioms supremum_rate

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.EmissionRate
