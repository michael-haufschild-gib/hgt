import GaloisForLFunctions.TransThresholdPairCorrelation.OddStabilizerExactPoisson
import GaloisForLFunctions.TransThresholdPairCorrelation.OddStabilizerPoissonHorizon

/-!
# Sharp support-horizon calibration and positive stabilizer rows

The complete stabilizer row at `m = bQ/π`, divided by `log Q`, tends to minus
one half of the window mass. Beyond the support horizon, a smooth window
with a surviving primitive sample gives a positive row at cutoff seven;
all sufficiently long finite truncations are positive as well.
-/

noncomputable section
open Complex MeasureTheory Real Filter Topology

namespace GaloisForLFunctions.TransThresholdPairCorrelation

/-- Along the exact support horizon, the complete signed stabilizer row has
logarithmic coefficient minus one half of the window mass. -/
theorem tendsto_stabilizerLinearRow_horizon_div_log {Ω : ℝ → ℝ} {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hΩ : ContDiff ℝ 2 Ω)
    (hsupp : ∀ u, u ∉ Set.Icc a b → Ω u = 0) :
    Tendsto (fun Q : ℕ => stabilizerLinearRow Q Ω (b * Q / π) / Real.log Q)
      atTop (𝓝 (-cosTransform Ω 0 / 2)) := by
  have h := tendsto_sum_odd_sqfreeTotientInv_div_log_half.const_mul (-cosTransform Ω 0)
  have hv : -cosTransform Ω 0 * (1 / 2 : ℝ) = -cosTransform Ω 0 / 2 := by ring
  rw [hv] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with Q hQ
  have hQ0 : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hb0 : 0 < b := ha.trans_le hab
  have hm : 0 < b * (Q : ℝ) / π := by positivity
  have hhor : (Q : ℝ) * b ≤ π * (b * Q / π) := by
    apply le_of_eq
    field_simp <;> ring
  rw [stabilizerLinearRow_eq_neg_of_horizon Q ha hab hm hhor hΩ hsupp]
  ring

private theorem exists_narrow_unit_window {δ : ℝ} (hδ : 0 < δ) : ∃ Ω : ℝ → ℝ,
    (∀ k : ℕ, ContDiff ℝ k Ω) ∧ (∀ u, 0 ≤ Ω u) ∧ (∀ u, Ω u ≤ 1) ∧
    (∀ u, u ∉ Set.Icc (1 - δ) (1 + δ) → Ω u = 0) ∧ Ω 1 = 1 := by
  obtain ⟨u, hu⟩ := exists_windowProfile (ε₁ := (1 / 8 : ℝ)) (by norm_num) (by norm_num)
  refine ⟨fun t => u ((t - 1) / (2 * δ) + 1 / 2),
    fun k => (hu.smooth k).comp (by fun_prop),
    fun t => hu.nonneg _, fun t => hu.le_one _, ?_, ?_⟩
  · intro t ht
    apply hu.zero_of
    intro h
    apply ht
    have hlo : -(1 / 2 : ℝ) ≤ (t - 1) / (2 * δ) := by linarith [h.1]
    have hhi : (t - 1) / (2 * δ) ≤ (1 / 2 : ℝ) := by linarith [h.2]
    rw [le_div_iff₀ (by positivity)] at hlo
    rw [div_le_iff₀ (by positivity)] at hhi
    constructor <;> linarith
  · apply hu.one_of
    norm_num

private theorem window_integral_le_length {Ω : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hn : ∀ u, 0 ≤ Ω u) (h1 : ∀ u, Ω u ≤ 1)
    (hsupp : ∀ u, u ∉ Set.Icc a b → Ω u = 0) : (∫ u, Ω u) ≤ b - a := by
  have hi : Integrable ((Set.Icc a b).indicator (fun _ : ℝ => (1 : ℝ))) :=
    (integrableOn_const (by simp)).integrable_indicator measurableSet_Icc
  have hle (u : ℝ) : Ω u ≤ (Set.Icc a b).indicator (fun _ : ℝ => (1 : ℝ)) u := by
    by_cases hmem : u ∈ Set.Icc a b
    · simpa only [Set.indicator_of_mem hmem] using h1 u
    · rw [Set.indicator_of_notMem hmem, hsupp u hmem]
  have h := integral_mono_of_nonneg (Eventually.of_forall hn) hi (Eventually.of_forall hle)
  simpa only [integral_indicator_const _ measurableSet_Icc,
    Real.volume_real_Icc_of_le hab, smul_eq_mul, mul_one] using h


private theorem odd_totient_sum_seven :
    (∑ q ∈ (Finset.Icc 1 7).filter (fun q => q % 2 = 1),
      RHTower.Sieve.sqfreeTotientInv q) = (23 / 12 : ℝ) := by
  have h3 : Nat.Prime 3 := by norm_num
  have h5 : Nat.Prime 5 := by norm_num
  have h7 : Nat.Prime 7 := by norm_num
  have hs : (Finset.Icc 1 7).filter (fun q => q % 2 = 1) = {1, 3, 5, 7} := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]
    omega
  rw [hs]
  norm_num [RHTower.Sieve.sqfreeTotientInv_apply, h3.squarefree, h5.squarefree, h7.squarefree,
    Nat.totient_prime h3, Nat.totient_prime h5, Nat.totient_prime h7]

private theorem stabilizerSpatialDual_seven_ge {Ω : ℝ → ℝ} {A : ℝ}
    (hsupp : ∀ u, Ω u ≠ 0 → |u| ≤ A) (hΩ : ∀ u, 0 ≤ Ω u) (h1 : Ω 1 = 1) :
    (1 / 36 : ℝ) ≤ stabilizerSpatialDual 7 Ω (7 / π) := by
  have h7 : Nat.Prime 7 := by norm_num
  have hg : RHTower.Sieve.sqfreeTotientInv 7 = (1 / 6 : ℝ) := by
    rw [RHTower.Sieve.sqfreeTotientInv_apply, if_pos h7.squarefree, Nat.totient_prime h7]
    norm_num
  have hm : (0 : ℝ) < 7 / π := by positivity
  have hsample := primitive_sample_le_ramanujanSpatialDual hm (q := 7) (by omega)
    hsupp hΩ (1 : ℤ) (by norm_num)
  have hx : ((1 : ℤ) : ℝ) * (π * (7 / π) / (7 : ℕ)) = (1 : ℝ) := by
    push_cast
    field_simp
  rw [hx, h1] at hsample
  have hmem : 7 ∈ (Finset.Icc 1 7).filter (fun q => q % 2 = 1) := by norm_num
  have hterm := Finset.single_le_sum (s := (Finset.Icc 1 7).filter (fun q => q % 2 = 1))
    (f := fun q => (RHTower.Sieve.sqfreeTotientInv q / (q.totient : ℝ)) *
      ramanujanSpatialDual q Ω (7 / π)) (a := 7)
    (fun q hq => mul_nonneg
      (div_nonneg (RHTower.Sieve.sqfreeTotientInv_nonneg q) (Nat.cast_nonneg _))
      (ramanujanSpatialDual_nonneg hm (Finset.mem_Icc.mp (Finset.mem_filter.mp hq).1).1 hsupp hΩ)) hmem
  rw [hg, Nat.totient_prime h7] at hterm
  norm_num at hterm
  change _ ≤ stabilizerSpatialDual 7 Ω (7 / π) at hterm
  linarith

/-- A smooth nonnegative window gives a strictly positive complete stabilizer
row at cutoff seven, arbitrarily close to the support horizon. Fixed-cutoff
negative cancellation fails as soon as primitive spatial samples can survive. -/
theorem exists_positive_stabilizerLinearRow {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 32) :
    ∃ Ω : ℝ → ℝ,
    (∀ k : ℕ, ContDiff ℝ k Ω) ∧ (∀ u, 0 ≤ Ω u) ∧ (∀ u, Ω u ≤ 1) ∧
    (∀ u, u ∉ Set.Icc (1 - δ) (1 + δ) → Ω u = 0) ∧ Ω 1 = 1 ∧
    (43 / 576 : ℝ) ≤ stabilizerLinearRow 7 Ω (7 / π) := by
  obtain ⟨Ω, hΩ, hn, hle, hsp, h1⟩ := exists_narrow_unit_window hδ
  refine ⟨Ω, hΩ, hn, hle, hsp, h1, ?_⟩
  have hsupp : ∀ u, Ω u ≠ 0 → |u| ≤ 1 + δ := by
    intro u hu
    have hmem : u ∈ Set.Icc (1 - δ) (1 + δ) := by
      by_contra h
      exact hu (hsp u h)
    rw [abs_of_nonneg (by linarith [hmem.1])]
    exact hmem.2
  have hmass : cosTransform Ω 0 ≤ (1 / 16 : ℝ) := by
    rw [cosTransform_zero_eq_integral]
    have h := window_integral_le_length (by linarith : 1 - δ ≤ 1 + δ) hn hle hsp
    linarith
  have hdual := stabilizerSpatialDual_seven_ge hsupp hn h1
  rw [stabilizerLinearRow_eq_dual (m := 7 / π) 7 (by positivity) (hΩ 2) hsupp, odd_totient_sum_seven]
  have hπ : π * (7 / π) = (7 : ℝ) := by field_simp
  rw [hπ]
  linarith

/-- The fixed-cutoff obstruction persists for all sufficiently long finite rows. -/
theorem exists_eventually_positive_finite_stabilizerRow : ∃ Ω : ℝ → ℝ,
    (∀ k : ℕ, ContDiff ℝ k Ω) ∧ (∀ u, 0 ≤ Ω u) ∧ (∀ u, Ω u ≤ 1) ∧
    (∀ u, u ∉ Set.Icc (31 / 32 : ℝ) (33 / 32) → Ω u = 0) ∧ Ω 1 = 1 ∧
    ∃ R₀ : ℕ, ∀ R ≥ R₀, (43 / 1152 : ℝ) ≤
      ∑ n ∈ Finset.range R, parityStabilizerWeight 7 (2 * (n + 1)) *
        cosTransform Ω (((2 * (n + 1) : ℕ) : ℝ) / (7 / π)) := by
  obtain ⟨Ω, hΩ, hn, hle, hsp, h1, hrow⟩ :=
    exists_positive_stabilizerLinearRow (δ := (1 / 32 : ℝ)) (by norm_num) le_rfl
  norm_num at hsp
  refine ⟨Ω, hΩ, hn, hle, hsp, h1, ?_⟩
  have hsupp : ∀ u, Ω u ≠ 0 → |u| ≤ (33 / 32 : ℝ) := by
    intro u hu
    have hmem : u ∈ Set.Icc (31 / 32 : ℝ) (33 / 32) := by
      by_contra h
      exact hu (hsp u h)
    rw [abs_of_nonneg (by linarith [hmem.1])]
    exact hmem.2
  have hlim := (parityStabilizer_hasSum_dual (m := 7 / π) 7 (by positivity) (hΩ 2) hsupp).summable.hasSum.tendsto_sum_nat
  change Tendsto (fun R : ℕ => ∑ n ∈ Finset.range R, parityStabilizerWeight 7 (2 * (n + 1)) *
    cosTransform Ω (((2 * (n + 1) : ℕ) : ℝ) / (7 / π))) atTop
    (𝓝 (stabilizerLinearRow 7 Ω (7 / π))) at hlim
  have hstrict : (43 / 1152 : ℝ) < stabilizerLinearRow 7 Ω (7 / π) := by linarith
  obtain ⟨R₀, hR⟩ := eventually_atTop.mp (hlim.eventually (eventually_gt_nhds hstrict))
  exact ⟨R₀, fun R h => (hR R h).le⟩
end GaloisForLFunctions.TransThresholdPairCorrelation
