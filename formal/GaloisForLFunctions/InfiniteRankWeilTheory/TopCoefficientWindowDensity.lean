import GaloisForLFunctions.HTGeometry.UnitPowerSumOscillation
import GaloisForLFunctions.HTGeometry.RootOfUnityPacketFilter

/-!
# Top coefficients control excursion density

Demodulating a finite unit power sum recovers each coefficient with a bounded error on every
window. Summable errors therefore affect excursion counts by only a bounded discrepancy.
The resulting lower density is the largest coefficient norm divided by their total norm.
-/

open Complex Finset

noncomputable section

namespace GaloisForLFunctions.InfiniteRankWeilTheory

/-- Interference with one chosen frequency in a finite unit power sum. -/
def coefficientInterference {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (p c : ι → ℂ) (j : ι) : ℝ :=
  ∑ i ∈ s.erase j, ‖c i‖ * (2 / ‖p i / p j - 1‖)

/-- Demodulation recovers a coefficient up to an error independent of both window endpoints. -/
theorem coefficient_le_window_norm_add_interference {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (p c : ι → ℂ) (hp : Set.InjOn p (s : Set ι))
    (hu : ∀ i ∈ s, ‖p i‖ = 1) {j : ι} (hj : j ∈ s) (M N : ℕ) :
    (N : ℝ) * ‖c j‖ ≤
      (∑ n ∈ range N, ‖∑ i ∈ s, c i * p i ^ (M + n)‖) +
        coefficientInterference s p c j := by
  have hpj : p j ≠ 0 := by
    intro h
    have := hu j hj
    rw [h, norm_zero] at this
    norm_num at this
  let A : ℂ := ∑ n ∈ range N, (∑ i ∈ s, c i * p i ^ (M + n)) / p j ^ (M + n)
  let E : ℂ := ∑ i ∈ s.erase j,
    c i * (p i / p j) ^ M * ∑ n ∈ range N, (p i / p j) ^ n
  have hsplit : A = (N : ℂ) * c j + E := by
    have hswap : A = ∑ i ∈ s, c i * (p i / p j) ^ M *
        ∑ n ∈ range N, (p i / p j) ^ n := by
      unfold A
      simp only [Finset.sum_div]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [mul_div_assoc, ← div_pow, pow_add]
      ring
    rw [hswap, ← Finset.add_sum_erase s _ hj]
    simp only [div_self hpj, one_pow, mul_one, Finset.sum_const, card_range,
      nsmul_eq_mul]
    ring
  have hE : ‖E‖ ≤ coefficientInterference s p c j := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i hi => ?_)
    have his := mem_of_mem_erase hi
    have hratio : ‖p i / p j‖ = 1 := by rw [norm_div, hu i his, hu j hj, div_self one_ne_zero]
    have hne : p i / p j ≠ 1 := by
      intro h
      exact (ne_of_mem_erase hi) (hp his hj ((div_eq_one_iff_eq hpj).mp h))
    rw [norm_mul, norm_mul, norm_pow, hratio, one_pow, mul_one]
    exact mul_le_mul_of_nonneg_left
      (HTGeometry.norm_geom_sum_le_of_norm_le_one hratio.le hne N) (norm_nonneg _)
  have hA : ‖A‖ ≤ ∑ n ∈ range N, ‖∑ i ∈ s, c i * p i ^ (M + n)‖ := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n _ => ?_)
    rw [norm_div, norm_pow, hu j hj, one_pow, div_one]
  have htri := norm_sub_le A E
  rw [hsplit, add_sub_cancel_right, norm_mul, Complex.norm_natCast] at htri
  rw [← hsplit] at htri
  exact htri.trans (add_le_add hA hE)

/-- The total coefficient norm bounds every value of a unit power sum. -/
theorem norm_unit_power_sum_le {ι : Type*} (s : Finset ι) (p c : ι → ℂ)
    (hu : ∀ i ∈ s, ‖p i‖ = 1) (n : ℕ) :
    ‖∑ i ∈ s, c i * p i ^ n‖ ≤ ∑ i ∈ s, ‖c i‖ := by
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i hi => ?_)
  rw [norm_mul, norm_pow, hu i hi, one_pow, mul_one]

/-- A geometric error has bounded mass on every window, including windows starting at zero. -/
theorem sum_window_pow_le {q : ℝ} (hq : 0 ≤ q) (hq1 : q < 1) (M N : ℕ) :
    ∑ n ∈ range N, q ^ (M + n) ≤ 1 / (1 - q) := by
  have hbase : ∑ n ∈ range N, q ^ n ≤ 1 / (1 - q) := by
    have hpos : 0 < 1 - q := sub_pos.mpr hq1
    rw [geom_sum_eq hq1.ne,
      show q ^ N - 1 = -(1 - q ^ N) by ring,
      show q - 1 = -(1 - q) by ring, neg_div_neg_eq,
      div_le_div_iff₀ hpos hpos]
    nlinarith [pow_nonneg hq N]
  calc ∑ n ∈ range N, q ^ (M + n) ≤ ∑ n ∈ range N, q ^ n := by
        refine Finset.sum_le_sum fun n _ => ?_
        rw [pow_add]
        exact mul_le_of_le_one_left (pow_nonneg hq n) (pow_le_one₀ hq hq1.le)
    _ ≤ 1 / (1 - q) := hbase

/-- Recovering one coefficient forces many exceptional levels. Only the total mass of the
permitted small values enters the discrepancy. -/
theorem coefficient_le_excursion_count_add_error {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (p c : ι → ℂ) (hp : Set.InjOn p (s : Set ι))
    (hu : ∀ i ∈ s, ‖p i‖ = 1) {j : ι} (hj : j ∈ s)
    (E : ℕ → Prop) [DecidablePred E] (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n)
    (hsmall : ∀ n, ¬ E n → ‖∑ i ∈ s, c i * p i ^ n‖ ≤ a n) (M N : ℕ) :
    (N : ℝ) * ‖c j‖ ≤ (∑ i ∈ s, ‖c i‖) *
      ((range N).filter (fun n => E (M + n))).card +
        (∑ n ∈ range N, a (M + n)) + coefficientInterference s p c j := by
  have hsum : (∑ n ∈ range N, ‖∑ i ∈ s, c i * p i ^ (M + n)‖) ≤
      (∑ i ∈ s, ‖c i‖) * ((range N).filter (fun n => E (M + n))).card +
        ∑ n ∈ range N, a (M + n) := by
    calc (∑ n ∈ range N, ‖∑ i ∈ s, c i * p i ^ (M + n)‖) ≤
        ∑ n ∈ range N, ((if E (M + n) then ∑ i ∈ s, ‖c i‖ else 0) + a (M + n)) := by
          refine Finset.sum_le_sum fun n _ => ?_
          by_cases hn : E (M + n)
          · rw [if_pos hn]
            exact (norm_unit_power_sum_le s p c hu _).trans (le_add_of_nonneg_right (ha _))
          · rw [if_neg hn, zero_add]
            exact hsmall _ hn
      _ = _ := by simp [Finset.sum_add_distrib, ← Finset.sum_filter, mul_comm]
  exact (coefficient_le_window_norm_add_interference s p c hp hu hj M N).trans
    (add_le_add hsum le_rfl)

/-- Equal coefficients on a primitive root packet attain density `1/k`: exactly `N` of the
first `kN` positive levels are nonzero. Thus the coefficient-share bound is sharp. -/
theorem root_packet_excursion_count {k : ℕ} (hk : 0 < k) {ω : ℂ}
    (hω : IsPrimitiveRoot ω k) (N : ℕ) :
    ((Ioc 0 (k * N)).filter fun n =>
      0 < ‖∑ i ∈ range k, (1 : ℂ) * (ω ^ i) ^ n‖).card = N := by
  classical
  have heq (n : ℕ) : (0 < ‖∑ i ∈ range k, (1 : ℂ) * (ω ^ i) ^ n‖) ↔ k ∣ n := by
    simp only [one_mul, ← pow_mul, _root_.HTGeometry.sum_primitiveRoot_pow_mul hω]
    by_cases h : k ∣ n
    · simp [h, hk]
    · simp [h]
  simp only [heq]
  rw [Nat.Ioc_filter_dvd_card_eq_div, Nat.mul_div_cancel_left _ hk]

#print axioms coefficient_le_window_norm_add_interference
#print axioms coefficient_le_excursion_count_add_error
#print axioms root_packet_excursion_count

end GaloisForLFunctions.InfiniteRankWeilTheory
