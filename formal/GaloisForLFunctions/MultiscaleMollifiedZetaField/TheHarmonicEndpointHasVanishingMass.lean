import GaloisForLFunctions.RHTower.Sieve.HarmonicLogWindowGeneralMoment

/-!
# The endpoint of the normalized harmonic logarithm has vanishing mass

Existing logarithmic moments converge to `1/(k+1)`. Near the upper
endpoint the indicator is bounded by twice a sufficiently high power.
This makes the endpoint strip arbitrarily small in harmonic mass, as
needed for uniformly bounded Möbius profiles.
-/

open Finset Filter Set Topology
open RHTower.Sieve
open scoped BigOperators

noncomputable section

namespace GaloisForLFunctions.MultiscaleMollifiedZetaField

/-- A logarithmic moment of the harmonic measure at a fixed rectangular dilation. -/
def normalizedHarmonicLogMoment (m c N : ℕ) : ℝ :=
  (∑ d ∈ Finset.Icc 1 (N / c), (Real.log d / Real.log N) ^ m / (d : ℝ)) / Real.log N

private theorem normalizedHarmonicLogMoment_eq (m c N : ℕ) (hN : 1 < N) :
    normalizedHarmonicLogMoment m c N =
      harmonicLogWindowMoment m 0 (N / c) / Real.log N ^ (m + 1) := by
  have hlog : Real.log (N : ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast hN)).ne'
  have hset : Finset.Ioc 0 (N / c) = Finset.Icc 1 (N / c) := by
    ext d
    simp only [Finset.mem_Ioc, Finset.mem_Icc]
    omega
  rw [normalizedHarmonicLogMoment, harmonicLogWindowMoment, hset, Finset.sum_div, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro d hd
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (Finset.mem_Icc.mp hd).1)
  rw [div_pow, pow_succ]
  field_simp [hlog, hd0]

/-- Every fixed normalized harmonic logarithmic moment has its unit-interval value. -/
theorem tendsto_normalizedHarmonicLogMoment (m : ℕ) {c : ℕ} (hc : 0 < c) :
    Tendsto (normalizedHarmonicLogMoment m c) atTop (𝓝 (1 / ((m : ℝ) + 1))) := by
  refine (tendsto_harmonicLogWindowMoment_natDiv_div_log_pow m hc).congr' ?_
  filter_upwards [eventually_ge_atTop 2] with N hN
  exact (normalizedHarmonicLogMoment_eq m c N (by omega)).symm

/-- The logarithmic coordinate of each retained harmonic atom lies in the unit interval. -/
theorem harmonicLogCoordinate_mem_unit {c N d : ℕ} (hN : 1 < N)
    (hd : d ∈ Finset.Icc 1 (N / c)) : Real.log d / Real.log N ∈ Icc (0 : ℝ) 1 := by
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast hN)
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast (Finset.mem_Icc.mp hd).1
  have hdN : (d : ℝ) ≤ N := by
    exact_mod_cast (Finset.mem_Icc.mp hd).2.trans (Nat.div_le_self N c)
  exact ⟨div_nonneg (Real.log_nonneg hd1) hlog.le,
    (div_le_one hlog).mpr (Real.log_le_log (zero_lt_one.trans_le hd1) hdN)⟩

/-- The normalized harmonic mass in an upper logarithmic endpoint strip. -/
def upperHarmonicLogMass (c N : ℕ) (δ : ℝ) : ℝ := by
  classical
  exact (∑ d ∈ Finset.Icc 1 (N / c),
    if 1 - δ ≤ Real.log d / Real.log N then 1 / (d : ℝ) else 0) / Real.log N

private theorem exists_endpoint_power_floor (k : ℕ) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ (1 / 2 : ℝ) ≤ (1 - δ) ^ k := by
  have hc : ContinuousAt (fun x : ℝ => (1 - x) ^ k) 0 := by fun_prop
  obtain ⟨r, hr, hsmall⟩ := Metric.continuousAt_iff.mp hc (1 / 2) (by norm_num)
  let δ : ℝ := min (r / 2) (1 / 2)
  have hδ : 0 < δ := lt_min (half_pos hr) (by norm_num)
  have hδ1 : δ < 1 := (min_le_right _ _).trans_lt (by norm_num)
  have hδr : dist δ 0 < r := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hδ]
    exact (min_le_left _ _).trans_lt (half_lt_self hr)
  have hh := hsmall hδr
  simp only [Real.dist_eq, sub_zero, one_pow] at hh
  refine ⟨δ, hδ, hδ1, ?_⟩
  have hl := (abs_lt.mp hh).1
  linarith only [hl]

/-- A high harmonic moment dominates a sufficiently narrow upper endpoint strip. -/
theorem upperHarmonicLogMass_le_moment (k c N : ℕ) (hN : 1 < N)
    {δ : ℝ} (hδ : δ < 1) (hfloor : (1 / 2 : ℝ) ≤ (1 - δ) ^ k) :
    upperHarmonicLogMass c N δ ≤ 2 * normalizedHarmonicLogMoment k c N := by
  classical
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast hN)
  rw [upperHarmonicLogMass, normalizedHarmonicLogMoment, ← mul_div_assoc, Finset.mul_sum]
  apply div_le_div_of_nonneg_right _ hlog.le
  apply Finset.sum_le_sum
  intro d hd
  by_cases hx : 1 - δ ≤ Real.log d / Real.log N
  · rw [if_pos hx]
    have hp : (1 - δ) ^ k ≤ (Real.log d / Real.log N) ^ k :=
      pow_le_pow_left₀ (by linarith only [hδ]) hx k
    have hh : (1 : ℝ) ≤ 2 * (Real.log d / Real.log N) ^ k := by linarith only [hfloor, hp]
    exact (div_le_div_of_nonneg_right hh (Nat.cast_nonneg d)).trans_eq (by ring)
  · rw [if_neg hx]
    have ht := harmonicLogCoordinate_mem_unit hN hd
    exact mul_nonneg (by norm_num) (div_nonneg (pow_nonneg ht.1 _) (Nat.cast_nonneg _))

/-- For every positive mass tolerance, one endpoint strip is eventually smaller than that tolerance. -/
theorem upperHarmonicLogMass_eventually_small {c : ℕ} (hc : 0 < c)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ ∀ᶠ N : ℕ in atTop, upperHarmonicLogMass c N δ < ε := by
  obtain ⟨k, hk⟩ := exists_nat_gt (4 / ε)
  have hk0 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hcoef : 4 / ((k : ℝ) + 1) < ε := by
    apply (div_lt_iff₀ hk0).2
    have hh := (div_lt_iff₀ hε).mp hk
    nlinarith only [hh, hε]
  obtain ⟨δ, hδ0, hδ1, hfloor⟩ := exists_endpoint_power_floor k
  have hm : ∀ᶠ N : ℕ in atTop,
      normalizedHarmonicLogMoment k c N < 2 / ((k : ℝ) + 1) := by
    exact (tendsto_normalizedHarmonicLogMoment k hc).eventually_lt_const
      ((div_lt_div_iff_of_pos_right hk0).mpr (by norm_num))
  refine ⟨δ, hδ0, hδ1, ?_⟩
  filter_upwards [eventually_ge_atTop 2, hm] with N hN hM
  refine (upperHarmonicLogMass_le_moment k c N (by omega) hδ1 hfloor).trans_lt ?_
  calc
    _ < 2 * (2 / ((k : ℝ) + 1)) := mul_lt_mul_of_pos_left hM (by norm_num)
    _ = 4 / ((k : ℝ) + 1) := by ring
    _ < ε := hcoef

/-- Harmonic averaging of an array at a fixed rectangular dilation. -/
def normalizedHarmonicArray (c N : ℕ) (e : ℕ → ℝ) : ℝ :=
  (∑ d ∈ Finset.Icc 1 (N / c), e d / (d : ℝ)) / Real.log N

/-- A bounded array is controlled by its interior error and the endpoint mass. -/
theorem normalizedHarmonicArray_abs_le {c N : ℕ} (hN : 1 < N)
    {e : ℕ → ℝ} {B η δ : ℝ} (hB : 0 ≤ B) (hη : 0 ≤ η)
    (hb : ∀ d ∈ Finset.Icc 1 (N / c), |e d| ≤ B)
    (hi : ∀ d ∈ Finset.Icc 1 (N / c), Real.log d / Real.log N ≤ 1 - δ → |e d| ≤ η) :
    |normalizedHarmonicArray c N e| ≤
      η * normalizedHarmonicLogMoment 0 c N + B * upperHarmonicLogMass c N δ := by
  classical
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast hN)
  have hp (d : ℕ) (hd : d ∈ Finset.Icc 1 (N / c)) :
      |e d / (d : ℝ)| ≤ η / (d : ℝ) +
        B * (if 1 - δ ≤ Real.log d / Real.log N then 1 / (d : ℝ) else 0) := by
    rw [abs_div, abs_of_nonneg (Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
    by_cases ht : 1 - δ ≤ Real.log d / Real.log N
    · rw [if_pos ht]
      calc
        _ ≤ B / (d : ℝ) := div_le_div_of_nonneg_right (hb d hd) (Nat.cast_nonneg _)
        _ ≤ η / (d : ℝ) + B * (1 / (d : ℝ)) := by
          have hh := div_nonneg hη (Nat.cast_nonneg d)
          rw [mul_one_div]
          exact le_add_of_nonneg_left hh
    · rw [if_neg ht, mul_zero, add_zero]
      exact div_le_div_of_nonneg_right (hi d hd (le_of_not_ge ht)) (Nat.cast_nonneg _)
  rw [normalizedHarmonicArray, abs_div, abs_of_pos hlog]
  calc
    _ ≤ (∑ d ∈ Finset.Icc 1 (N / c), |e d / (d : ℝ)|) / Real.log N :=
      div_le_div_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) hlog.le
    _ ≤ (∑ d ∈ Finset.Icc 1 (N / c), (η / (d : ℝ) +
        B * (if 1 - δ ≤ Real.log d / Real.log N then 1 / (d : ℝ) else 0))) / Real.log N :=
      div_le_div_of_nonneg_right (Finset.sum_le_sum hp) hlog.le
    _ = _ := by
      simp only [normalizedHarmonicLogMoment, upperHarmonicLogMass, pow_zero,
        Finset.sum_add_distrib, ← Finset.mul_sum]
      rw [show (∑ d ∈ Finset.Icc 1 (N / c), η / (d : ℝ)) =
        η * ∑ d ∈ Finset.Icc 1 (N / c), 1 / (d : ℝ) by
          rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro d hd; ring]
      ring

/-- Uniformly bounded errors that vanish away from the endpoint vanish in harmonic mean. -/
theorem tendsto_normalizedHarmonicArray_zero {c : ℕ} (hc : 0 < c)
    {e : ℕ → ℕ → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ᶠ N : ℕ in atTop, ∀ d ∈ Finset.Icc 1 (N / c), |e N d| ≤ B)
    (hi : ∀ δ ε : ℝ, 0 < δ → 0 < ε → ∀ᶠ N : ℕ in atTop,
      ∀ d ∈ Finset.Icc 1 (N / c), Real.log d / Real.log N ≤ 1 - δ → |e N d| ≤ ε) :
    Tendsto (fun N : ℕ => normalizedHarmonicArray c N (e N)) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.2
  intro ε hε
  have htol : 0 < ε / (4 * (B + 1)) := by positivity
  obtain ⟨δ, hδ, _, ht⟩ := upperHarmonicLogMass_eventually_small hc htol
  have hm : ∀ᶠ N : ℕ in atTop, normalizedHarmonicLogMoment 0 c N < 2 := by
    apply (tendsto_normalizedHarmonicLogMoment 0 hc).eventually_lt_const
    norm_num
  filter_upwards [eventually_ge_atTop 2, hb, hi δ (ε / 8) hδ (by positivity), ht, hm]
    with N hN hbound hinter htail hmass
  rw [Real.dist_eq, sub_zero]
  have hh := normalizedHarmonicArray_abs_le (by omega : 1 < N) hB
    (by positivity : 0 ≤ ε / 8) hbound hinter
  have hfirst : ε / 8 * normalizedHarmonicLogMoment 0 c N ≤ ε / 4 := by
    have hh := mul_le_mul_of_nonneg_left hmass.le (by positivity : 0 ≤ ε / 8)
    linarith only [hh]
  have hsecond : B * upperHarmonicLogMass c N δ ≤ ε / 4 := by
    calc
      _ ≤ B * (ε / (4 * (B + 1))) := mul_le_mul_of_nonneg_left htail.le hB
      _ ≤ (B + 1) * (ε / (4 * (B + 1))) :=
        mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) htol.le
      _ = ε / 4 := by field_simp [show B + 1 ≠ 0 by positivity]
  linarith only [hh, hfirst, hsecond, hε]

end GaloisForLFunctions.MultiscaleMollifiedZetaField
