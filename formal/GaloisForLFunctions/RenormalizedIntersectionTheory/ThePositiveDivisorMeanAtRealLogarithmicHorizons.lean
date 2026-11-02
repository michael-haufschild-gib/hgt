import GaloisForLFunctions.RenormalizedIntersectionTheory.ThePositiveDivisorMeanSatisfiesTheRenewalEquation

/-!
# Real logarithmic horizons for the positive divisor mean

The polar moment is a locally finite sum of linear positive parts. It is continuous,
and its right derivative is the harmonic mean. This gives a direct calculus form of
the arithmetic renewal equation, including the logarithmic integer thresholds.
-/

noncomputable section

open Finset Filter Topology

namespace GaloisForLFunctions.RenormalizedIntersectionTheory

open GaloisForLFunctions.ArithmeticCountingPositivity
  GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
  GaloisForLFunctions.SelectiveMultiscaleArithmeticPositivity

/-- The harmonic mean at the real logarithmic horizon `u`. -/
def realLogHarmonicSum (g : ℕ → ℝ) (u : ℝ) : ℝ :=
  gaugeHarmonicSum g ⌊Real.exp u⌋₊

/-- The continuous polar moment at logarithmic horizon `u`. -/
def realPolarMoment (g : ℕ → ℝ) (u : ℝ) : ℝ :=
  ∑ n ∈ Icc 1 ⌊Real.exp u⌋₊, g n / n * (u - Real.log n)

private theorem le_log_horizon_iff {n : ℕ} (hn : 0 < n) (u : ℝ) :
    n ≤ ⌊Real.exp u⌋₊ ↔ Real.log n ≤ u := by
  exact (Nat.le_floor_iff (Real.exp_pos u).le).trans
    (Real.log_le_iff_le_exp (Nat.cast_pos.mpr hn)).symm

/-- On a bounded interval the moment is a fixed finite sum of positive parts. -/
theorem realPolarMoment_eq_sum_max (g : ℕ → ℝ) {u v : ℝ} (huv : u ≤ v) :
    realPolarMoment g u =
      ∑ n ∈ Icc 1 ⌊Real.exp v⌋₊, g n / n * max 0 (u - Real.log n) := by
  have hcut : ⌊Real.exp u⌋₊ ≤ ⌊Real.exp v⌋₊ := Nat.floor_mono (Real.exp_le_exp.mpr huv)
  calc
    _ = ∑ n ∈ Icc 1 ⌊Real.exp u⌋₊, g n / n * max 0 (u - Real.log n) := by
      apply sum_congr rfl
      intro n hn
      have hlog := (le_log_horizon_iff (mem_Icc.mp hn).1 u).mp (mem_Icc.mp hn).2
      rw [max_eq_right (sub_nonneg.mpr hlog)]
    _ = _ := by
      apply sum_subset (Icc_subset_Icc le_rfl hcut)
      intro n hn hnold
      have hn0 := (mem_Icc.mp hn).1
      have hnot : ¬ n ≤ ⌊Real.exp u⌋₊ := fun h => hnold (mem_Icc.mpr ⟨hn0, h⟩)
      have hlog : u < Real.log n := lt_of_not_ge fun h => hnot ((le_log_horizon_iff hn0 u).mpr h)
      rw [max_eq_left (sub_nonpos.mpr hlog.le), mul_zero]

/-- The moment remains continuous when a new integer enters the horizon. -/
theorem continuous_realPolarMoment (g : ℕ → ℝ) : Continuous (realPolarMoment g) := by
  apply continuous_iff_continuousAt.mpr
  intro u
  let F : ℝ → ℝ := fun v =>
    ∑ n ∈ Icc 1 ⌊Real.exp (u + 1)⌋₊, g n / n * max 0 (v - Real.log n)
  have hF : Continuous F := by dsimp only [F]; fun_prop
  apply hF.continuousAt.congr_of_eventuallyEq
  filter_upwards [eventually_lt_nhds (show u < u + 1 by linarith)] with v hv
  exact realPolarMoment_eq_sum_max g hv.le

private theorem log_horizon_eventuallyEq_right (u : ℝ) :
    (fun v : ℝ => ⌊Real.exp v⌋₊) =ᶠ[𝓝[Set.Ici u] u] (fun _ => ⌊Real.exp u⌋₊) := by
  let N := ⌊Real.exp u⌋₊
  have hupper : u < Real.log ((N : ℝ) + 1) :=
    (Real.lt_log_iff_exp_lt (by positivity : (0 : ℝ) < N + 1)).mpr
      (Nat.lt_floor_add_one (Real.exp u))
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds hupper).filter_mono nhdsWithin_le_nhds] with v hv hvupper
  apply (Nat.floor_eq_iff (Real.exp_pos v).le).mpr
  exact ⟨(Nat.floor_le (Real.exp_pos u).le).trans (Real.exp_le_exp.mpr hv),
    (Real.lt_log_iff_exp_lt (by positivity : (0 : ℝ) < N + 1)).mp hvupper⟩

/-- The right derivative is exact even at an integer threshold. -/
theorem hasDerivWithinAt_realPolarMoment (g : ℕ → ℝ) (u : ℝ) :
    HasDerivWithinAt (realPolarMoment g) (realLogHarmonicSum g u) (Set.Ici u) u := by
  let N := ⌊Real.exp u⌋₊
  let F : ℝ → ℝ := fun v => ∑ n ∈ Icc 1 N, g n / n * (v - Real.log n)
  have hF : HasDerivAt F (gaugeHarmonicSum g N) u := by
    change HasDerivAt (fun v => ∑ n ∈ Icc 1 N, g n / n * (v - Real.log n))
      (∑ n ∈ Icc 1 N, g n / n) u
    apply HasDerivAt.fun_sum
    intro n _
    simpa only [id_eq, mul_one] using ((hasDerivAt_id u).sub_const (Real.log n)).const_mul (g n / n)
  have hEq : realPolarMoment g =ᶠ[𝓝[Set.Ici u] u] F := by
    filter_upwards [log_horizon_eventuallyEq_right u] with v hv
    change (∑ n ∈ Icc 1 ⌊Real.exp v⌋₊, g n / n * (v - Real.log n)) = _
    rw [hv]
  exact hF.hasDerivWithinAt.congr_of_eventuallyEq_of_mem hEq (Set.mem_Ici.mpr le_rfl)

/-- The continuous moment interpolates the integer polar moment linearly in logarithmic scale. -/
theorem realPolarMoment_eq_polarMoment (g : ℕ → ℝ) (u : ℝ) :
    realPolarMoment g u = polarMoment g ⌊Real.exp u⌋₊ +
      (u - Real.log (⌊Real.exp u⌋₊ : ℕ)) * realLogHarmonicSum g u := by
  let N := ⌊Real.exp u⌋₊
  change (∑ n ∈ Icc 1 N, g n / n * (u - Real.log n)) =
    polarMoment g N + (u - Real.log N) * gaugeHarmonicSum g N
  rw [polarMoment, gaugeHarmonicSum, mul_sum, ← sum_add_distrib]
  refine sum_congr rfl fun n hn => ?_
  have hn0 : (n : ℝ) ≠ 0 := by have := (mem_Icc.mp hn).1; positivity
  have hN0 : (N : ℝ) ≠ 0 := by
    have := (mem_Icc.mp hn).1.trans (mem_Icc.mp hn).2
    positivity
  rw [Real.log_div hN0 hn0]
  ring

/-- Positive divisor coefficients make the real moment at least its first, linear term. -/
theorem le_realPolarMoment_signDivisorCount {ω : ℕ → ℝ} (hω : IsSignGauge ω)
    {u : ℝ} (hu : 0 ≤ u) : u ≤ realPolarMoment (signDivisorCount ω) u := by
  have hfirst : 1 ∈ Icc 1 ⌊Real.exp u⌋₊ :=
    mem_Icc.mpr ⟨le_rfl, (le_log_horizon_iff one_pos u).mpr (by simpa using hu)⟩
  have hnonneg : ∀ n ∈ Icc 1 ⌊Real.exp u⌋₊,
      0 ≤ signDivisorCount ω n / n * (u - Real.log n) := by
    intro n hn
    exact mul_nonneg (div_nonneg (signDivisorCount_nonneg hω n) (Nat.cast_nonneg _))
      (sub_nonneg.mpr ((le_log_horizon_iff (mem_Icc.mp hn).1 u).mp (mem_Icc.mp hn).2))
  have h := single_le_sum hnonneg hfirst
  simpa only [realPolarMoment, signDivisorCount_one hω, Nat.cast_one, div_one, Real.log_one,
    sub_zero, one_mul] using h

/-- The positive mean retains unit mass at every nonnegative logarithmic horizon. -/
theorem one_le_realLogHarmonicSum_signDivisorCount {ω : ℕ → ℝ} (hω : IsSignGauge ω)
    {u : ℝ} (hu : 0 ≤ u) : 1 ≤ realLogHarmonicSum (signDivisorCount ω) u := by
  have hfirst : 1 ∈ Icc 1 ⌊Real.exp u⌋₊ :=
    mem_Icc.mpr ⟨le_rfl, (le_log_horizon_iff one_pos u).mpr (by simpa using hu)⟩
  have hnonneg : ∀ n ∈ Icc 1 ⌊Real.exp u⌋₊, 0 ≤ signDivisorCount ω n / n :=
    fun n _ => div_nonneg (signDivisorCount_nonneg hω n) (Nat.cast_nonneg _)
  have h := single_le_sum hnonneg hfirst
  simpa only [realLogHarmonicSum, gaugeHarmonicSum, signDivisorCount_one hω,
    Nat.cast_one, div_one] using h

private theorem log_horizon_remainder_bounds {u : ℝ} (hu : 0 ≤ u) :
    0 ≤ u - Real.log (⌊Real.exp u⌋₊ : ℕ) ∧
      u - Real.log (⌊Real.exp u⌋₊ : ℕ) ≤ Real.log 2 := by
  let N := ⌊Real.exp u⌋₊
  have hN : 1 ≤ N := (le_log_horizon_iff one_pos u).mpr (by simpa using hu)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hlo : Real.log N ≤ u := (le_log_horizon_iff hN u).mp le_rfl
  have hfloor : Real.exp u < (N : ℝ) + 1 := Nat.lt_floor_add_one (Real.exp u)
  have hexp : Real.exp u ≤ 2 * (N : ℝ) := by linarith only [hfloor, hN1]
  have hhi := Real.log_le_log (Real.exp_pos u) hexp
  rw [Real.log_exp, Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hN0.ne'] at hhi
  exact ⟨sub_nonneg.mpr hlo, by linarith only [hhi]⟩

/-- The relative positive renewal estimate holds at every real logarithmic horizon. -/
theorem exists_abs_real_positive_divisor_renewal_equation_le (P : Set ℕ)
    (hP : Tendsto (fun N => primeSetLogMass P N / (1 + Real.log N)) atTop (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, ∀ u : ℝ, 0 ≤ u →
      |u * realLogHarmonicSum (signDivisorCount (primeSetFlip P)) u -
        3 * realPolarMoment (signDivisorCount (primeSetFlip P)) u| ≤
      ε * realPolarMoment (signDivisorCount (primeSetFlip P)) u +
        C * realLogHarmonicSum (signDivisorCount (primeSetFlip P)) u := by
  obtain ⟨C, hC⟩ := exists_abs_positive_divisor_renewal_equation_le P hP hε
  refine ⟨C + 2 * Real.log 2, fun u hu => ?_⟩
  let g := signDivisorCount (primeSetFlip P)
  let N := ⌊Real.exp u⌋₊
  have hG : 0 ≤ gaugeHarmonicSum g N :=
    sum_nonneg fun n _ => div_nonneg (signDivisorCount_nonneg (primeSetFlip_isSignGauge P) n)
      (Nat.cast_nonneg _)
  have hrem := log_horizon_remainder_bounds hu
  have hJ : polarMoment g N ≤ realPolarMoment g u := by
    rw [realPolarMoment_eq_polarMoment]
    exact le_add_of_nonneg_right (mul_nonneg hrem.1 hG)
  have heq : u * realLogHarmonicSum g u - 3 * realPolarMoment g u =
      (gaugeHarmonicSum g N * Real.log N - 3 * polarMoment g N) -
        2 * (u - Real.log N) * gaugeHarmonicSum g N := by
    rw [realPolarMoment_eq_polarMoment]
    change u * gaugeHarmonicSum g N -
      3 * (polarMoment g N + (u - Real.log N) * gaugeHarmonicSum g N) = _
    ring
  change |u * realLogHarmonicSum g u - 3 * realPolarMoment g u| ≤ _
  rw [heq]
  calc
    _ ≤ |gaugeHarmonicSum g N * Real.log N - 3 * polarMoment g N| +
        |2 * (u - Real.log N) * gaugeHarmonicSum g N| := abs_sub _ _
    _ ≤ (ε * polarMoment g N + C * gaugeHarmonicSum g N) +
        2 * Real.log 2 * gaugeHarmonicSum g N := by
      rw [abs_of_nonneg (mul_nonneg (mul_nonneg (by norm_num) hrem.1) hG)]
      exact add_le_add (hC N) (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hrem.2 (by norm_num)) hG)
    _ ≤ _ := by
      have hmono := mul_le_mul_of_nonneg_left hJ hε.le
      change _ ≤ ε * realPolarMoment g u + (C + 2 * Real.log 2) * gaugeHarmonicSum g N
      nlinarith only [hmono]

end GaloisForLFunctions.RenormalizedIntersectionTheory
