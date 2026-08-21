import GaloisForLFunctions.HTGeometry.GammaSixGlobalPolarity
import Mathlib.Probability.Distributions.Binomial
import Mathlib.MeasureTheory.Group.Convolution

/-!
# Poisson formation is forced by the native source laws

Vacuum, independent superposition, Bernoulli thinning and mean calibration determine the Poisson
formation species.  The proof runs through the probability generating function: superposition makes
it multiplicative in the rate, the small-rate bound supplied by mean calibration makes the resulting
Cauchy equation solvable, thinning makes its exponent affine, and calibration normalizes the
affine slope.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal

noncomputable section

/-! ## An additive nonnegative function of the rate is linear -/

theorem eq_mul_of_additive_of_nonneg {h : ℝ≥0 → ℝ}
    (hadd : ∀ a b : ℝ≥0, h (a + b) = h a + h b) (hnn : ∀ a, 0 ≤ h a) (a : ℝ≥0) :
    h a = (a : ℝ) * h 1 := by
  have h0 : h 0 = 0 := by
    have hd := hadd 0 0
    simp only [add_zero] at hd
    linarith
  have hmono : Monotone h := by
    intro x y hxy
    have hsplit : h y = h x + h (y - x) := by
      rw [← hadd, add_tsub_cancel_of_le hxy]
    linarith [hnn (y - x)]
  have hnat : ∀ (n : ℕ) (x : ℝ≥0), h ((n : ℝ≥0) * x) = (n : ℝ) * h x := by
    intro n
    induction n with
    | zero => intro x; simp [h0]
    | succ k ih =>
        intro x
        have : ((k + 1 : ℕ) : ℝ≥0) * x = (k : ℝ≥0) * x + x := by push_cast; ring
        rw [this, hadd, ih]
        push_cast
        ring
  have hfrac : ∀ (m n : ℕ), 0 < n → h ((m : ℝ≥0) / (n : ℝ≥0)) = ((m : ℝ) / (n : ℝ)) * h 1 := by
    intro m n hn
    have hn0 : ((n : ℝ≥0)) ≠ 0 := by
      simpa using hn.ne'
    have hkey : (n : ℝ≥0) * ((m : ℝ≥0) / (n : ℝ≥0)) = (m : ℝ≥0) := by
      field_simp
    have h1 := hnat n ((m : ℝ≥0) / (n : ℝ≥0))
    rw [hkey] at h1
    have h2 : h (m : ℝ≥0) = (m : ℝ) * h 1 := by
      have := hnat m 1
      simpa using this
    rw [h2] at h1
    have hnR : ((n : ℝ)) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
    field_simp
    linarith [h1]
  have h1nn : 0 ≤ h 1 := hnn 1
  by_contra hne
  obtain ⟨N, hN⟩ := exists_nat_gt (h 1 / |h a - (a : ℝ) * h 1|)
  have habs : 0 < |h a - (a : ℝ) * h 1| := abs_pos.2 (sub_ne_zero.2 hne)
  have hNpos : 0 < N := by
    rcases Nat.eq_zero_or_pos N with hz | hp
    · exfalso
      subst hz
      simp only [Nat.cast_zero] at hN
      have hq : 0 ≤ h 1 / |h a - (a : ℝ) * h 1| := by positivity
      linarith
    · exact hp
  set m : ℕ := ⌊(N : ℝ) * (a : ℝ)⌋₊ with hm
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hNpos
  have hle : (m : ℝ) ≤ (N : ℝ) * (a : ℝ) := Nat.floor_le (by positivity)
  have hlt : (N : ℝ) * (a : ℝ) < (m : ℝ) + 1 := Nat.lt_floor_add_one _
  have hlow : ((m : ℝ≥0) / (N : ℝ≥0)) ≤ a := by
    rw [div_le_iff₀ (show (0 : ℝ≥0) < (N : ℝ≥0) by exact_mod_cast hNpos)]
    have : (m : ℝ) ≤ (a : ℝ) * (N : ℝ) := by linarith
    exact_mod_cast this
  have hhigh : a ≤ ((m + 1 : ℕ) : ℝ≥0) / (N : ℝ≥0) := by
    rw [le_div_iff₀ (show (0 : ℝ≥0) < (N : ℝ≥0) by exact_mod_cast hNpos)]
    have : (a : ℝ) * (N : ℝ) ≤ ((m : ℝ) + 1) := by linarith
    have hcast : ((a * (N : ℝ≥0) : ℝ≥0) : ℝ) ≤ (((m + 1 : ℕ) : ℝ≥0) : ℝ) := by
      push_cast
      linarith
    exact_mod_cast hcast
  have hA := hmono hlow
  have hB := hmono hhigh
  rw [hfrac m N hNpos] at hA
  rw [hfrac (m + 1) N hNpos] at hB
  have hlow' : (m : ℝ) / (N : ℝ) ≤ (a : ℝ) := by
    rw [div_le_iff₀ hNR]
    linarith
  have hhigh' : (a : ℝ) ≤ ((m : ℝ) + 1) / (N : ℝ) := by
    rw [le_div_iff₀ hNR]
    linarith
  have hgap : |h a - (a : ℝ) * h 1| ≤ h 1 / (N : ℝ) := by
    have hbound1 : h a - (a : ℝ) * h 1 ≤ h 1 / (N : ℝ) := by
      have h1' : ((m : ℝ) + 1) / (N : ℝ) * h 1 - (m : ℝ) / (N : ℝ) * h 1 = h 1 / (N : ℝ) := by
        field_simp
        ring
      have hmul : (m : ℝ) / (N : ℝ) * h 1 ≤ (a : ℝ) * h 1 :=
        mul_le_mul_of_nonneg_right hlow' h1nn
      push_cast at hB
      linarith
    have hbound2 : -(h 1 / (N : ℝ)) ≤ h a - (a : ℝ) * h 1 := by
      have hmul : (a : ℝ) * h 1 ≤ ((m : ℝ) + 1) / (N : ℝ) * h 1 :=
        mul_le_mul_of_nonneg_right hhigh' h1nn
      have h1' : ((m : ℝ) + 1) / (N : ℝ) * h 1 - (m : ℝ) / (N : ℝ) * h 1 = h 1 / (N : ℝ) := by
        field_simp
        ring
      linarith
    exact abs_le.2 ⟨hbound2, hbound1⟩
  rw [div_lt_iff₀ habs] at hN
  have : h 1 / (N : ℝ) < |h a - (a : ℝ) * h 1| := by
    rw [div_lt_iff₀ hNR]
    linarith
  linarith

/-! ## The probability generating function -/

/-- Extended probability generating function of a law on `ℕ`. -/
def pgfE (μ : Measure ℕ) (z : ℝ) : ℝ≥0∞ := ∫⁻ n, ENNReal.ofReal (z ^ n) ∂μ

/-- Probability generating function of a law on `ℕ`. -/
def pgf (μ : Measure ℕ) (z : ℝ) : ℝ := (pgfE μ z).toReal

theorem integrable_pow_of_mem_unit (μ : Measure ℕ) [IsFiniteMeasure μ] {z : ℝ} (hz0 : 0 ≤ z)
    (hz1 : z ≤ 1) : Integrable (fun n : ℕ => z ^ n) μ := by
  refine (integrable_const (1 : ℝ)).mono' (by fun_prop) ?_
  filter_upwards with n
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact pow_le_one₀ hz0 hz1

theorem pgfE_ne_top (μ : Measure ℕ) [IsProbabilityMeasure μ] {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    pgfE μ z ≠ ⊤ := by
  have hle : pgfE μ z ≤ 1 := by
    rw [pgfE]
    calc ∫⁻ n, ENNReal.ofReal (z ^ n) ∂μ ≤ ∫⁻ _n, (1 : ℝ≥0∞) ∂μ := by
          refine lintegral_mono fun n => ?_
          rw [← ENNReal.ofReal_one]
          exact ENNReal.ofReal_le_ofReal (pow_le_one₀ hz0 hz1)
      _ = 1 := by simp
  exact ne_top_of_le_ne_top ENNReal.one_ne_top hle

/-- On the unit interval the generating function is the ordinary expectation of `z ^ n`. -/
theorem pgf_eq_integral (μ : Measure ℕ) [IsProbabilityMeasure μ] {z : ℝ} (hz0 : 0 ≤ z) :
    pgf μ z = ∫ n, z ^ n ∂μ := by
  rw [pgf, pgfE, integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall fun n => by positivity) (by fun_prop)]

theorem pgf_nonneg (μ : Measure ℕ) (z : ℝ) : 0 ≤ pgf μ z := ENNReal.toReal_nonneg

theorem pgf_le_one (μ : Measure ℕ) [IsProbabilityMeasure μ] {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    pgf μ z ≤ 1 := by
  rw [pgf_eq_integral μ hz0]
  calc ∫ n, z ^ n ∂μ ≤ ∫ _n : ℕ, (1 : ℝ) ∂μ := by
        refine integral_mono (integrable_pow_of_mem_unit μ hz0 hz1) (integrable_const 1) ?_
        intro n
        exact pow_le_one₀ hz0 hz1
    _ = 1 := by simp

theorem pgf_pos (μ : Measure ℕ) [IsProbabilityMeasure μ] {z : ℝ} (hz0 : 0 < z) (hz1 : z ≤ 1) :
    0 < pgf μ z := by
  rw [pgf_eq_integral μ hz0.le,
    integral_pos_iff_support_of_nonneg (fun n => by positivity)
      (integrable_pow_of_mem_unit μ hz0.le hz1)]
  have hsupp : Function.support (fun n : ℕ => z ^ n) = Set.univ := by
    ext n
    simp only [Function.mem_support, Set.mem_univ, iff_true]
    positivity
  rw [hsupp, measure_univ]
  norm_num

@[simp] theorem pgf_one (μ : Measure ℕ) [IsProbabilityMeasure μ] : pgf μ 1 = 1 := by
  rw [pgf_eq_integral μ zero_le_one]
  simp

theorem one_sub_pow_le {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1) (n : ℕ) :
    1 - z ^ n ≤ (1 - z) * (n : ℝ) := by
  induction n with
  | zero => simp
  | succ k ih =>
      have hpk : z ^ k ≤ 1 := pow_le_one₀ hz0 hz1
      have : 1 - z ^ (k + 1) = (1 - z ^ k) + z ^ k * (1 - z) := by ring
      rw [this]
      push_cast
      nlinarith [ih, hpk, sub_nonneg.2 hz1]

/-- Mean calibration bounds the generating-function defect linearly in the rate. -/
theorem one_sub_pgf_le (μ : Measure ℕ) [IsProbabilityMeasure μ] {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1)
    (hint : Integrable (fun n : ℕ => (n : ℝ)) μ) :
    1 - pgf μ z ≤ (1 - z) * ∫ n, (n : ℝ) ∂μ := by
  rw [pgf_eq_integral μ hz0]
  have hsub : ∫ n, (1 - z ^ n) ∂μ ≤ ∫ n, (1 - z) * (n : ℝ) ∂μ := by
    refine integral_mono ((integrable_const 1).sub (integrable_pow_of_mem_unit μ hz0 hz1))
      (hint.const_mul _) fun n => one_sub_pow_le hz0 hz1 n
  rw [integral_sub (integrable_const 1) (integrable_pow_of_mem_unit μ hz0 hz1),
    integral_const_mul] at hsub
  simpa using hsub

/-! ## Superposition and thinning -/

theorem pgfE_conv (μ η : Measure ℕ) [SFinite μ] [SFinite η] {z : ℝ} (hz0 : 0 ≤ z)
    (hη : pgfE η z ≠ ⊤) : pgfE (Measure.conv μ η) z = pgfE μ z * pgfE η z := by
  rw [pgfE, Measure.lintegral_conv (f := fun n : ℕ => ENNReal.ofReal (z ^ n))
    Measurable.of_discrete]
  have hstep : ∀ x : ℕ, ∫⁻ y, ENNReal.ofReal (z ^ (x + y)) ∂η
      = ENNReal.ofReal (z ^ x) * pgfE η z := by
    intro x
    rw [pgfE, ← lintegral_const_mul' _ _ (ENNReal.ofReal_ne_top)]
    refine lintegral_congr fun y => ?_
    rw [pow_add, ENNReal.ofReal_mul (by positivity)]
  rw [lintegral_congr hstep, lintegral_mul_const' _ _ hη]
  rfl

/-- Bernoulli thinning of a formation law. -/
def thinLaw (p : unitInterval) (μ : Measure ℕ) : Measure ℕ := μ.bind fun n => binomial n p

theorem integral_pow_binomial (n : ℕ) (p : unitInterval) (z : ℝ) :
    ∫ k, z ^ k ∂(binomial n p) = (1 - (p : ℝ) + (p : ℝ) * z) ^ n := by
  rw [integral_binomial, ← Nat.range_succ_eq_Iic,
    show (1 - (p : ℝ) + (p : ℝ) * z) = ((p : ℝ) * z) + (1 - (p : ℝ)) from by ring, add_pow]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [smul_eq_mul, mul_pow]
  ring

theorem unitInterval_affine_mem {p : unitInterval} {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    0 ≤ 1 - (p : ℝ) + (p : ℝ) * z ∧ 1 - (p : ℝ) + (p : ℝ) * z ≤ 1 := by
  have hp0 : (0 : ℝ) ≤ (p : ℝ) := p.2.1
  have hp1 : (p : ℝ) ≤ 1 := p.2.2
  constructor <;> nlinarith

theorem pgfE_binomial (n : ℕ) (p : unitInterval) {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    pgfE (binomial n p) z = ENNReal.ofReal ((1 - (p : ℝ) + (p : ℝ) * z) ^ n) := by
  have hval : pgf (binomial n p) z = (1 - (p : ℝ) + (p : ℝ) * z) ^ n := by
    rw [pgf_eq_integral _ hz0, integral_pow_binomial]
  have hne := pgfE_ne_top (binomial n p) hz0 hz1
  rw [← hval, pgf, ENNReal.ofReal_toReal hne]

theorem pgfE_thinLaw (p : unitInterval) (μ : Measure ℕ) [IsProbabilityMeasure μ] {z : ℝ}
    (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    pgfE (thinLaw p μ) z = pgfE μ (1 - (p : ℝ) + (p : ℝ) * z) := by
  rw [thinLaw, pgfE, Measure.lintegral_bind (Measurable.of_discrete).aemeasurable
    (Measurable.of_discrete).aemeasurable]
  refine lintegral_congr fun n => ?_
  exact pgfE_binomial n p hz0 hz1

/-! ## The Poisson generating function -/

theorem pgf_poissonMeasure (r : ℝ≥0) {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    pgf Po(r) z = Real.exp (-((r : ℝ) * (1 - z))) := by
  rw [pgf_eq_integral _ hz0]
  have hsum : HasSum (fun n : ℕ => (Po(r) {n}).toReal * z ^ n)
      (Real.exp (-((r : ℝ) * (1 - z)))) := by
    have hbase := (hasSum_pow_div_factorial ((r : ℝ) * z)).mul_left (Real.exp (-(r : ℝ)))
    have hval : Real.exp (-(r : ℝ)) * Real.exp ((r : ℝ) * z)
        = Real.exp (-((r : ℝ) * (1 - z))) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [hval] at hbase
    refine hbase.congr_fun fun n => ?_
    rw [poissonMeasure_singleton_toReal, mul_pow]
    ring
  rw [integral_countable (integrable_pow_of_mem_unit _ hz0 hz1)]
  simp only [Measure.real, smul_eq_mul]
  exact hsum.tsum_eq

/-! ## Generating functions determine the law -/

theorem summable_atom_pow (μ : Measure ℕ) [IsProbabilityMeasure μ] {z : ℝ} (hz0 : 0 ≤ z)
    (hz1 : z ≤ 1) : Summable fun n : ℕ => (μ {n}).toReal * z ^ n := by
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
    (hasSum_measure_singleton_toReal μ).summable
  calc (μ {n}).toReal * z ^ n ≤ (μ {n}).toReal * 1 :=
        mul_le_mul_of_nonneg_left (pow_le_one₀ hz0 hz1) ENNReal.toReal_nonneg
    _ = (μ {n}).toReal := mul_one _

theorem pgf_eq_tsum (μ : Measure ℕ) [IsProbabilityMeasure μ] {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    pgf μ z = ∑' n : ℕ, (μ {n}).toReal * z ^ n := by
  rw [pgf_eq_integral μ hz0, integral_countable (integrable_pow_of_mem_unit μ hz0 hz1)]
  simp only [Measure.real, smul_eq_mul]

/-- A power series with absolutely summable coefficients that vanishes on `(0,1]` has vanishing
coefficients. -/
theorem eq_zero_of_tsum_pow_eq_zero {d : ℕ → ℝ} (habs : Summable fun n => |d n|)
    (hzero : ∀ z : ℝ, 0 < z → z ≤ 1 → ∑' n : ℕ, d n * z ^ n = 0) : ∀ k : ℕ, d k = 0 := by
  have hsum : ∀ (j : ℕ) (z : ℝ), 0 ≤ z → z ≤ 1 → Summable fun m : ℕ => d (m + j) * z ^ m := by
    intro j z hz0 hz1
    have hsj : Summable fun m : ℕ => |d (m + j)| :=
      (summable_nat_add_iff (f := fun n : ℕ => |d n|) j).2 habs
    refine Summable.of_norm (Summable.of_nonneg_of_le (fun m => norm_nonneg _)
      (fun m => ?_) hsj)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ z ^ m)]
    exact mul_le_of_le_one_right (abs_nonneg _) (pow_le_one₀ hz0 hz1)
  have hsum0 : ∀ (z : ℝ), 0 ≤ z → z ≤ 1 → Summable fun n : ℕ => d n * z ^ n := by
    intro z hz0 hz1
    simpa using hsum 0 z hz0 hz1
  have hstep : ∀ k : ℕ, (∀ j, j < k → d j = 0) → d k = 0 := by
    intro k hk
    have hs2 : Summable fun m : ℕ => |d (m + (k + 1))| :=
      (summable_nat_add_iff (f := fun n : ℕ => |d n|) (k + 1)).2 habs
    have hshift : ∀ z : ℝ, 0 < z → z ≤ 1 → ∑' m : ℕ, d (m + k) * z ^ m = 0 := by
      intro z hz0 hz1
      have hsplit := (hsum0 z hz0.le hz1).sum_add_tsum_nat_add k
      have hfin : ∑ j ∈ Finset.range k, d j * z ^ j = 0 :=
        Finset.sum_eq_zero fun j hj => by rw [hk j (Finset.mem_range.1 hj), zero_mul]
      rw [hfin, zero_add, hzero z hz0 hz1] at hsplit
      have hfactor : ∑' m : ℕ, d (m + k) * z ^ (m + k) = z ^ k * ∑' m : ℕ, d (m + k) * z ^ m := by
        rw [← tsum_mul_left]
        exact tsum_congr fun m => by rw [pow_add]; ring
      rw [hfactor] at hsplit
      rcases mul_eq_zero.1 hsplit with hzk | hs
      · exact absurd hzk (by positivity)
      · exact hs
    have hbound : ∀ z : ℝ, 0 < z → z ≤ 1 → |d k| ≤ z * ∑' m : ℕ, |d (m + (k + 1))| := by
      intro z hz0 hz1
      have hsplit := (hsum k z hz0.le hz1).sum_add_tsum_nat_add 1
      rw [hshift z hz0 hz1] at hsplit
      simp only [Finset.sum_range_one, pow_zero, mul_one, zero_add] at hsplit
      have hterm : ∀ i : ℕ, |d (i + 1 + k) * z ^ (i + 1)| ≤ z * |d (i + (k + 1))| := by
        intro i
        rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ z ^ (i + 1)),
          show i + 1 + k = i + (k + 1) from by omega, mul_comm]
        refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
        calc z ^ (i + 1) = z ^ i * z := by ring
          _ ≤ 1 * z := mul_le_mul_of_nonneg_right (pow_le_one₀ hz0.le hz1) hz0.le
          _ = z := one_mul z
      have hsabs : Summable fun i : ℕ => |d (i + 1 + k) * z ^ (i + 1)| :=
        Summable.of_nonneg_of_le (fun i => abs_nonneg _) hterm (hs2.mul_left z)
      have hkey : d k = -∑' i : ℕ, d (i + 1 + k) * z ^ (i + 1) := by linarith
      calc |d k| = |∑' i : ℕ, d (i + 1 + k) * z ^ (i + 1)| := by rw [hkey, abs_neg]
        _ ≤ ∑' i : ℕ, |d (i + 1 + k) * z ^ (i + 1)| := by
            simpa [Real.norm_eq_abs] using
              norm_tsum_le_tsum_norm (f := fun i : ℕ => d (i + 1 + k) * z ^ (i + 1))
                (by simpa [Real.norm_eq_abs] using hsabs)
        _ ≤ ∑' i : ℕ, z * |d (i + (k + 1))| := hsabs.tsum_le_tsum hterm (hs2.mul_left z)
        _ = z * ∑' i : ℕ, |d (i + (k + 1))| := tsum_mul_left
    by_contra hne
    have hpos : 0 < |d k| := abs_pos.2 hne
    have hM0 : (0 : ℝ) ≤ ∑' m : ℕ, |d (m + (k + 1))| := tsum_nonneg fun m => abs_nonneg _
    have hzpos : 0 < min 1 (|d k| / (2 * ((∑' m : ℕ, |d (m + (k + 1))|) + 1))) := by
      refine lt_min one_pos ?_
      positivity
    have hzM : min 1 (|d k| / (2 * ((∑' m : ℕ, |d (m + (k + 1))|) + 1)))
        * ∑' m : ℕ, |d (m + (k + 1))| < |d k| := by
      have h1 : min 1 (|d k| / (2 * ((∑' m : ℕ, |d (m + (k + 1))|) + 1)))
          ≤ |d k| / (2 * ((∑' m : ℕ, |d (m + (k + 1))|) + 1)) := min_le_right _ _
      have h2 := mul_le_mul_of_nonneg_right h1 hM0
      have h3 : |d k| / (2 * ((∑' m : ℕ, |d (m + (k + 1))|) + 1))
          * ∑' m : ℕ, |d (m + (k + 1))| ≤ |d k| / 2 := by
        rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
        nlinarith [hpos, hM0]
      linarith
    exact absurd (hbound _ hzpos (min_le_left _ _)) (not_le.2 hzM)
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih => exact hstep k ih

/-- **Generating functions determine the law.** -/
theorem measure_eq_of_pgf_eq {μ η : Measure ℕ} [IsProbabilityMeasure μ] [IsProbabilityMeasure η]
    (h : ∀ z : ℝ, 0 < z → z ≤ 1 → pgf μ z = pgf η z) : μ = η := by
  have habs : Summable fun n : ℕ => |(μ {n}).toReal - (η {n}).toReal| := by
    refine Summable.of_nonneg_of_le (fun n => abs_nonneg _) (fun n => ?_)
      ((hasSum_measure_singleton_toReal μ).add (hasSum_measure_singleton_toReal η)).summable
    have h1 : (0 : ℝ) ≤ (μ {n}).toReal := ENNReal.toReal_nonneg
    have h2 : (0 : ℝ) ≤ (η {n}).toReal := ENNReal.toReal_nonneg
    rw [abs_le]
    constructor <;> linarith
  have hzero : ∀ z : ℝ, 0 < z → z ≤ 1 →
      ∑' n : ℕ, ((μ {n}).toReal - (η {n}).toReal) * z ^ n = 0 := by
    intro z hz0 hz1
    have hsplit : ∑' n : ℕ, ((μ {n}).toReal - (η {n}).toReal) * z ^ n
        = (∑' n : ℕ, (μ {n}).toReal * z ^ n) - ∑' n : ℕ, (η {n}).toReal * z ^ n := by
      rw [← (summable_atom_pow μ hz0.le hz1).tsum_sub (summable_atom_pow η hz0.le hz1)]
      exact tsum_congr fun n => by ring
    rw [hsplit, ← pgf_eq_tsum μ hz0.le hz1, ← pgf_eq_tsum η hz0.le hz1, h z hz0 hz1, sub_self]
  have hall := eq_zero_of_tsum_pow_eq_zero habs hzero
  refine Measure.ext_of_singleton fun n => ?_
  have hn := hall n
  rw [sub_eq_zero] at hn
  exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top μ _) (measure_ne_top η _)).1 hn

/-! ## The characterization -/

/-- The retention probability read as a nonnegative rate. -/
def unitToNN (p : unitInterval) : ℝ≥0 := ⟨(p : ℝ), p.2.1⟩

@[simp] theorem coe_unitToNN (p : unitInterval) : (unitToNN p : ℝ) = (p : ℝ) := rfl

/-- The four native source laws of a rate-indexed formation species: vacuum, independent
superposition, Bernoulli thinning and mean calibration. -/
structure IsFormationSpecies (ν : ℝ≥0 → Measure ℕ) : Prop where
  isProbability : ∀ r, IsProbabilityMeasure (ν r)
  vacuum : ν 0 = Measure.dirac 0
  superposition : ∀ r s, ν (r + s) = Measure.conv (ν r) (ν s)
  thinning : ∀ (p : unitInterval) (r : ℝ≥0), thinLaw p (ν r) = ν (unitToNN p * r)
  integrableMean : ∀ r, Integrable (fun n : ℕ => (n : ℝ)) (ν r)
  calibration : ∀ r, ∫ n, (n : ℝ) ∂(ν r) = (r : ℝ)

theorem integrable_id_poissonMeasure (r : ℝ≥0) :
    Integrable (fun n : ℕ => (n : ℝ)) Po(r) := by
  refine integrable_of_summable_singleton_weighted _ ?_
  refine ((hasSum_poissonMeasure_mean r).summable).congr fun n => ?_
  rw [abs_of_nonneg (Nat.cast_nonneg n)]

theorem integral_id_poissonMeasure (r : ℝ≥0) : ∫ n, (n : ℝ) ∂Po(r) = (r : ℝ) := by
  rw [integral_countable (integrable_id_poissonMeasure r)]
  simp only [Measure.real, smul_eq_mul]
  exact (hasSum_poissonMeasure_mean r).tsum_eq

/-- **Superposition--thinning characterization.**  Vacuum, independent superposition, Bernoulli
thinning and mean calibration force the Poisson formation species. -/
theorem eq_poissonMeasure_of_isFormationSpecies {ν : ℝ≥0 → Measure ℕ}
    (h : IsFormationSpecies ν) (r : ℝ≥0) : ν r = Po(r) := by
  haveI hprob := h.isProbability
  have hmul : ∀ (a b : ℝ≥0) {z : ℝ}, 0 ≤ z → z ≤ 1 →
      pgf (ν (a + b)) z = pgf (ν a) z * pgf (ν b) z := by
    intro a b z hz0 hz1
    rw [h.superposition a b, pgf,
      pgfE_conv _ _ hz0 (pgfE_ne_top (ν b) hz0 hz1), ENNReal.toReal_mul]
    rfl
  set c : ℝ → ℝ := fun z => -Real.log (pgf (ν 1) z) with hcdef
  have hexp : ∀ (a : ℝ≥0) {z : ℝ}, 0 < z → z ≤ 1 →
      pgf (ν a) z = Real.exp (-((a : ℝ) * c z)) := by
    intro a z hz0 hz1
    have hpos : ∀ s : ℝ≥0, 0 < pgf (ν s) z := fun s => pgf_pos (ν s) hz0 hz1
    have hle : ∀ s : ℝ≥0, pgf (ν s) z ≤ 1 := fun s => pgf_le_one (ν s) hz0.le hz1
    have hadd : ∀ x y : ℝ≥0, -Real.log (pgf (ν (x + y)) z)
        = -Real.log (pgf (ν x) z) + -Real.log (pgf (ν y) z) := by
      intro x y
      rw [hmul x y hz0.le hz1, Real.log_mul (hpos x).ne' (hpos y).ne']
      ring
    have hnn : ∀ x : ℝ≥0, 0 ≤ -Real.log (pgf (ν x) z) := by
      intro x
      simpa using Real.log_nonpos (hpos x).le (hle x)
    have hlin := eq_mul_of_additive_of_nonneg hadd hnn a
    have : Real.log (pgf (ν a) z) = -((a : ℝ) * c z) := by
      rw [hcdef]
      linarith [hlin]
    rw [← this, Real.exp_log (hpos a)]
  have hthin : ∀ (p : unitInterval) (a : ℝ≥0) {z : ℝ}, 0 ≤ z → z ≤ 1 →
      pgf (ν (unitToNN p * a)) z = pgf (ν a) (1 - (p : ℝ) + (p : ℝ) * z) := by
    intro p a z hz0 hz1
    rw [← h.thinning p a, pgf, pgfE_thinLaw p (ν a) hz0 hz1]
    rfl
  have hc : ∀ (p : unitInterval) {z : ℝ}, 0 < z → z ≤ 1 →
      c (1 - (p : ℝ) + (p : ℝ) * z) = (p : ℝ) * c z := by
    intro p z hz0 hz1
    obtain ⟨hw0, hw1⟩ := unitInterval_affine_mem (p := p) hz0.le hz1
    have hwpos : 0 < 1 - (p : ℝ) + (p : ℝ) * z := by
      rcases eq_or_lt_of_le p.2.2 with hp | hp
      · have : (p : ℝ) = 1 := hp
        rw [this]
        linarith
      · nlinarith [p.2.1, hz0.le]
    have h1 := hthin p 1 hz0.le hz1
    rw [mul_one, hexp (unitToNN p) hz0 hz1, hexp 1 hwpos hw1] at h1
    have := Real.exp_injective h1
    simp only [coe_unitToNN, NNReal.coe_one, one_mul] at this
    linarith
  set C : ℝ := 2 * c (1 / 2) with hCdef
  have hhalf : (0 : ℝ) < 1 / 2 := by norm_num
  have hcform : ∀ {z : ℝ}, 0 < z → z ≤ 1 → c z = C * (1 - z) := by
    intro z hz0 hz1
    rcases lt_trichotomy z (1 / 2) with hlt | heq | hgt
    · have hden : (0 : ℝ) < 1 - z := by linarith
      have hple : (1 : ℝ) / (2 * (1 - z)) ≤ 1 := by
        rw [div_le_one (by linarith)]
        linarith
      set p : unitInterval := ⟨1 / (2 * (1 - z)), ⟨by positivity, hple⟩⟩ with hp
      have hval : 1 - (p : ℝ) + (p : ℝ) * z = 1 / 2 := by
        simp only [hp]
        field_simp
        ring
      have := hc p hz0 hz1
      rw [hval] at this
      simp only [hp] at this
      rw [hCdef]
      field_simp at this ⊢
      linarith
    · rw [heq, hCdef]
      ring
    · have hple : 2 * (1 - z) ≤ 1 := by linarith
      have hpnn : (0 : ℝ) ≤ 2 * (1 - z) := by linarith
      set p : unitInterval := ⟨2 * (1 - z), ⟨hpnn, hple⟩⟩ with hp
      have hval : 1 - (p : ℝ) + (p : ℝ) * (1 / 2) = z := by
        simp only [hp]
        ring
      have := hc p hhalf (by norm_num)
      rw [hval] at this
      simp only [hp] at this
      rw [hCdef]
      linarith
  have hC0 : 0 ≤ C := by
    have := hc ⟨1 / 2, ⟨by norm_num, by norm_num⟩⟩ hhalf (by norm_num)
    have hcnn : ∀ {z : ℝ}, 0 < z → z ≤ 1 → 0 ≤ c z := by
      intro z hz0 hz1
      simpa [hcdef] using Real.log_nonpos (pgf_pos (ν 1) hz0 hz1).le (pgf_le_one (ν 1) hz0.le hz1)
    have h1 := hcnn hhalf (by norm_num)
    rw [hCdef]
    linarith
  have hpoisson : ∀ a : ℝ≥0, ν a = Po(((a : ℝ) * C).toNNReal) := by
    intro a
    refine measure_eq_of_pgf_eq fun z hz0 hz1 => ?_
    rw [hexp a hz0 hz1, pgf_poissonMeasure _ hz0.le hz1, hcform hz0 hz1,
      Real.coe_toNNReal _ (by positivity)]
    congr 1
    ring
  have hC1 : C = 1 := by
    have hmean := h.calibration 1
    rw [hpoisson 1, integral_id_poissonMeasure] at hmean
    rw [Real.coe_toNNReal _ (by positivity)] at hmean
    simpa using hmean
  rw [hpoisson r, hC1, mul_one]
  congr 1
  exact Real.toNNReal_coe

/-! ## Poisson splitting and recovery -/

theorem poissonMeasure_zero : Po((0 : ℝ≥0)) = Measure.dirac 0 := by
  refine Measure.ext_of_singleton fun n => ?_
  rw [poissonMeasure_singleton]
  cases n with
  | zero => simp
  | succ k => simp

/-- **Poisson splitting and recovery.**  Summing independent Poisson coordinates recovers a single
Poisson law of the total rate: the marked packet projects back onto the source packet. -/
theorem map_sum_pi_poissonMeasure : ∀ (n : ℕ) (a : Fin n → ℝ≥0),
    Measure.map (fun f : Fin n → ℕ => ∑ j, f j) (Measure.pi fun j => Po(a j)) = Po(∑ j, a j) := by
  intro n
  induction n with
  | zero =>
      intro a
      have hmap : (fun f : Fin 0 → ℕ => ∑ j, f j) = fun _ => 0 := by
        funext f
        simp
      rw [hmap, Finset.univ_eq_empty, Finset.sum_empty, poissonMeasure_zero,
        Measure.map_const]
      simp
  | succ k ih =>
      intro a
      have hmp := measurePreserving_piFinSuccAbove (fun j : Fin (k + 1) => Po(a j)) 0
      have hsum : (fun f : Fin (k + 1) → ℕ => ∑ j, f j)
          = (fun q : ℕ × ℕ => q.1 + q.2) ∘ (Prod.map (id : ℕ → ℕ)
              (fun g : Fin k → ℕ => ∑ j, g j)) ∘
            (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => ℕ) 0) := by
        funext f
        simp only [Function.comp_apply, Prod.map_apply, id_eq,
          MeasurableEquiv.piFinSuccAbove_apply, Fin.insertNthEquiv_symm_apply]
        rw [Fin.sum_univ_succ]
        rfl
      rw [hsum, ← Measure.map_map (by fun_prop) (by fun_prop),
        ← Measure.map_map (by fun_prop) (by fun_prop), hmp.map_eq,
        ← Measure.map_prod_map _ _ (by fun_prop) (by fun_prop), Measure.map_id, ih]
      have hconv : Measure.conv Po(a 0) Po(∑ j, a ((0 : Fin (k + 1)).succAbove j))
          = Po(a 0 + ∑ j, a ((0 : Fin (k + 1)).succAbove j)) :=
        poissonMeasure_conv_poissonMeasure _ _
      rw [Fin.sum_univ_succ]
      exact hconv

end

end GaloisForLFunctions.HTGeometry
