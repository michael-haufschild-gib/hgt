import GaloisForLFunctions.RHTower.ChiPrimeGaussianRationalSaddle
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Complete Gaussian prime cubic main

The literal adjacent cubic moment of the full Gaussian prime band is its complete
signed three-prime saddle sum, with error O(N/log(N)^3). Thus its analytic error
vanishes at the contraction scale N/log(N)^2. Both complete physical remainders,
every prime triple and the moving saddle window are retained.

The repeated-prime terms have an exact contraction identity with their all-equal
overlap subtracted once. The remaining phase is exactly the hyperbolic prime-gap
phase. Cancellation of that full signed remainder is a separate open problem;
no Gaussian moment law or positive BAG self-return certificate is asserted here.
-/

noncomputable section
open Complex MeasureTheory Set Filter Finset
open scoped Topology
namespace RHTower
open GaloisForLFunctions.RHTower

def primeGaussianCubicCoefficient (N : ℝ) (p q r : ℕ) : ℂ :=
  (smoothAFECutoff ((p : ℝ) / N) / (Real.sqrt p : ℂ)) *
  (smoothAFECutoff ((q : ℝ) / N) / (Real.sqrt q : ℂ)) *
  (starRingEnd ℂ) (smoothAFECutoff ((r : ℝ) / N) / (Real.sqrt r : ℂ))

def primeGaussianCubicKernel (N : ℝ) (p q r : ℕ) : ℂ :=
  ∫ t in (2 * Real.pi * N)..2 * (2 * Real.pi * N),
    (bagPhysicalHeightWindow (t / (2 * Real.pi * N)) : ℂ) *
      (zetaChi (linePt t) * Complex.exp
        ((((Real.log p + Real.log q - Real.log r) * t : ℝ) : ℂ) * I))

def primeGaussianCubicMainEntry (N : ℝ) (p q r : ℕ) : ℂ :=
  (2 * Real.pi : ℂ) * smoothAFECutoff ((p : ℝ) / N) *
    smoothAFECutoff ((q : ℝ) / N) * (starRingEnd ℂ) (smoothAFECutoff ((r : ℝ) / N)) / (r : ℂ) *
      (bagPhysicalHeightWindow ((p : ℝ) * q / ((r : ℝ) * N)) : ℂ) *
        bourgainOscillation (2 * Real.pi * ((p : ℝ) * q / r))

def primeGaussianCubicMain (N : ℝ) : ℂ :=
  ∑ p ∈ primeProfileBand N, ∑ q ∈ primeProfileBand N, ∑ r ∈ primeProfileBand N,
    primeGaussianCubicMainEntry N p q r

def primeGaussianCubicIntegral (N : ℝ) : ℂ :=
  ∫ t in (2 * Real.pi * N)..2 * (2 * Real.pi * N),
    (bagPhysicalHeightWindow (t / (2 * Real.pi * N)) : ℂ) *
      zetaChi (linePt t) * (primeGaussianChiField 1 N t)^2 *
        (starRingEnd ℂ) (primeGaussianChiField 1 N t)

private theorem cubic_saddle_mem {N : ℝ} (hN : 0 < N)
    {p q r : ℕ} (hp : p ∈ primeProfileBand N) (hq : q ∈ primeProfileBand N)
    (hr : r ∈ primeProfileBand N) :
    N ≤ 2 * Real.pi * ((p : ℝ) * q / r) ∧
    (2 * Real.pi * ((p : ℝ) * q / r)) / (2 * Real.pi * N) ∈ Icc (1 / 2 : ℝ) 4 := by
  obtain ⟨_, hpN, hp2⟩ := primeProfileBand_mem hN.le hp
  obtain ⟨_, hqN, hq2⟩ := primeProfileBand_mem hN.le hq
  obtain ⟨_, hrN, hr2⟩ := primeProfileBand_mem hN.le hr
  have hr0 : (0 : ℝ) < r := hN.trans hrN
  have hlo : N / 2 ≤ (p : ℝ) * q / r := by
    apply (le_div_iff₀ hr0).mpr
    have hmul := mul_le_mul hpN.le hqN.le hN.le (by linarith : (0 : ℝ) ≤ p)
    nlinarith
  have hhi : (p : ℝ) * q / r ≤ 4 * N := by
    apply (div_le_iff₀ hr0).mpr
    have hmul := mul_le_mul hp2 hq2 (by positivity : (0 : ℝ) ≤ q) (by positivity : 0 ≤ 2*N)
    nlinarith
  have hs : (2 * Real.pi * ((p : ℝ) * q / r)) / (2 * Real.pi * N) =
      ((p : ℝ) * q / r) / N := by field_simp
  constructor
  · have hh := mul_le_mul_of_nonneg_left hlo (by positivity : 0 ≤ 2*Real.pi)
    nlinarith [Real.pi_gt_three]
  · rw [hs]
    exact ⟨(le_div_iff₀ hN).mpr (by linarith), (div_le_iff₀ hN).mpr hhi⟩

private theorem cubic_main_eq {N : ℝ} (hN : 0 < N) {p q r : ℕ}
    (hp : (0 : ℝ) < p) (hq : (0 : ℝ) < q) (hr : (0 : ℝ) < r) :
    primeGaussianCubicCoefficient N p q r *
      physicalChiStationaryMain (2 * Real.pi * N) (2 * Real.pi * ((p : ℝ) * q / r)) 1 =
        primeGaussianCubicMainEntry N p q r := by
  let x : ℝ := (p : ℝ) * q / r
  have hx : 0 < x := by dsimp [x]; positivity
  have ha : 0 < 2 * Real.pi * x := by positivity
  have hamp : (2 * Real.pi * x) * Real.sqrt (2 * Real.pi / (2 * Real.pi * x)) =
      2 * Real.pi * Real.sqrt x := by
    calc
      _ = Real.sqrt ((2 * Real.pi * x)^2 * (2 * Real.pi / (2 * Real.pi * x))) := by
        rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq ha.le]
      _ = Real.sqrt ((2 * Real.pi)^2 * x) := by congr 1; field_simp
      _ = _ := by rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity : 0 ≤ 2*Real.pi)]
  have hsqrt : Real.sqrt x = Real.sqrt (p : ℝ) * Real.sqrt (q : ℝ) / Real.sqrt (r : ℝ) := by
    dsimp [x]
    rw [Real.sqrt_div (by positivity), Real.sqrt_mul hp.le]
  have hratio : (2 * Real.pi * x) / (2 * Real.pi * N) = (p : ℝ) * q / ((r : ℝ) * N) := by
    dsimp [x]; field_simp
  have hphase : bourgainOscillation (Real.pi / 4) *
      Complex.exp (I * ((2 * Real.pi * x - Real.pi / 4 : ℝ) : ℂ)) =
        bourgainOscillation (2 * Real.pi * x) := by
    unfold bourgainOscillation
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hsp : (Real.sqrt (p : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hp).ne'
  have hsq : (Real.sqrt (q : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hq).ne'
  have hsr : (Real.sqrt (r : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hr).ne'
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hrS : (Real.sqrt (r : ℝ) : ℂ)^2 = (r : ℂ) := by
    exact_mod_cast Real.sq_sqrt hr.le
  have hampC := congrArg (fun y : ℝ => (y : ℂ)) hamp
  push_cast at hampC
  change primeGaussianCubicCoefficient N p q r *
    physicalChiStationaryMain (2*Real.pi*N) (2*Real.pi*x) 1 = _
  unfold physicalChiStationaryMain
  simp only [zpow_one, Int.cast_one, one_mul, hratio]
  rw [show bourgainOscillation (Real.pi / 4) * (↑(2 * Real.pi * x) : ℂ) *
      ↑(bagPhysicalHeightWindow ((p : ℝ)*q/((r : ℝ)*N))) *
      ↑(Real.sqrt (2 * Real.pi / (2 * Real.pi * x))) *
      Complex.exp (I * ↑(2 * Real.pi * x - Real.pi/4)) =
      ((2 * Real.pi * x : ℝ) : ℂ) * ↑(Real.sqrt (2 * Real.pi / (2 * Real.pi * x))) *
      ↑(bagPhysicalHeightWindow ((p : ℝ)*q/((r : ℝ)*N))) *
      (bourgainOscillation (Real.pi / 4) * Complex.exp (I * ↑(2 * Real.pi * x - Real.pi/4))) by ring]
  push_cast at hphase ⊢
  rw [hampC, hphase, hsqrt]
  unfold primeGaussianCubicCoefficient primeGaussianCubicMainEntry
  simp only [map_div₀, Complex.conj_ofReal]
  push_cast
  dsimp [x]
  field_simp
  rw [hrS]
  ring

/-- Both complete physical kernel remainders, for every full-band prime triple. -/
theorem exists_primeGaussianCubic_entry_error :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℝ, 1 < N →
      ∀ p ∈ primeProfileBand N, ∀ q ∈ primeProfileBand N, ∀ r ∈ primeProfileBand N,
        ‖primeGaussianCubicCoefficient N p q r * primeGaussianCubicKernel N p q r -
          primeGaussianCubicMainEntry N p q r‖ ≤ C / N^2 := by
  obtain ⟨Cm, Ce, hCm, hCe, hk⟩ := exists_complete_physical_chi_positiveGrade_kernel
  refine ⟨Cm + 3120*Ce, by positivity, ?_⟩
  intro N hN p hp q hq r hr
  have hN0 : 0 < N := by linarith
  obtain ⟨_, hpN, _⟩ := primeProfileBand_mem hN0.le hp
  obtain ⟨_, hqN, _⟩ := primeProfileBand_mem hN0.le hq
  obtain ⟨_, hrN, _⟩ := primeProfileBand_mem hN0.le hr
  have hp0 : (0:ℝ)<p := hN0.trans hpN
  have hq0 : (0:ℝ)<q := hN0.trans hqN
  have hr0 : (0:ℝ)<r := hN0.trans hrN
  have hT : 4 ≤ 2*Real.pi*N := by nlinarith [Real.pi_gt_three]
  have hTN : N ≤ 2*Real.pi*N := by nlinarith [Real.pi_gt_three]
  obtain ⟨haN, har⟩ := cubic_saddle_mem hN0 hp hq hr
  have ha : 0 < 2*Real.pi*((p:ℝ)*q/r) := hN0.trans_le haN
  have hlog : Real.log ((2*Real.pi*((p:ℝ)*q/r))/(2*Real.pi)) =
      Real.log p + Real.log q - Real.log r := by
    rw [mul_div_cancel_left₀ _ (by positivity : 2*Real.pi ≠ 0),
      Real.log_div (by positivity) hr0.ne', Real.log_mul hp0.ne' hq0.ne']
  have hb := hk _ _ hT ha har 1 (by norm_num)
  simp only [Int.cast_one, zpow_one, one_mul, abs_one, mul_one, hlog] at hb
  rw [physicalChiGradeOne_second_error (by positivity)] at hb
  have hfirst : (2*Real.pi*((p:ℝ)*q/r))*Cm /
      ((2*Real.pi*((p:ℝ)*q/r))*Real.sqrt (2*Real.pi*((p:ℝ)*q/r))) ≤ Cm/Real.sqrt N := by
    rw [mul_div_mul_left Cm _ ha.ne']
    exact div_le_div_of_nonneg_left hCm.le (by positivity) (Real.sqrt_le_sqrt haN)
  have hsecond : (3120*Ce)/Real.sqrt (2*Real.pi*N) ≤ (3120*Ce)/Real.sqrt N :=
    div_le_div_of_nonneg_left (by positivity) (by positivity) (Real.sqrt_le_sqrt hTN)
  have hker := hb.trans (add_le_add hfirst hsecond)
  rw [← add_div] at hker
  have hcoeff (j : ℕ) (hj : N < j) :
      ‖smoothAFECutoff ((j:ℝ)/N)/(Real.sqrt j:ℂ)‖ ≤ 1/Real.sqrt N := by
    have hj0 : (0:ℝ) < j := hN0.trans hj
    rw [norm_div, Complex.norm_of_nonneg (Real.sqrt_nonneg _)]
    exact (div_le_div_of_nonneg_right (norm_smoothAFECutoff_le_one (by positivity))
      (Real.sqrt_nonneg _)).trans
      (div_le_div_of_nonneg_left (by norm_num) (by positivity) (Real.sqrt_le_sqrt hj.le))
  have hc : ‖primeGaussianCubicCoefficient N p q r‖ ≤ (1/Real.sqrt N)^3 := by
    dsimp [primeGaussianCubicCoefficient]
    rw [norm_mul, norm_mul, Complex.norm_conj]
    have hh := mul_le_mul (mul_le_mul (hcoeff p hpN) (hcoeff q hqN) (norm_nonneg _) (by positivity))
      (hcoeff r hrN) (norm_nonneg _) (by positivity)
    simpa only [pow_succ, pow_zero, mul_one, one_mul] using hh
  rw [← cubic_main_eq hN0 hp0 hq0 hr0, ← mul_sub, norm_mul]
  change ‖primeGaussianCubicCoefficient N p q r‖ * ‖_‖ ≤ _
  calc
    _ ≤ (1/Real.sqrt N)^3 * ((Cm+3120*Ce)/Real.sqrt N) :=
      mul_le_mul hc hker (norm_nonneg _) (by positivity)
    _ = _ := by
      have hs := Real.sq_sqrt hN0.le
      have hnS : Real.sqrt N ≠ 0 := (Real.sqrt_pos.mpr hN0).ne'
      field_simp
      nlinarith [sq_nonneg (Real.sqrt N)]

private theorem primeProfileBand_card_log_le {N : ℝ} (hN : 1 < N) :
    (primeProfileBand N).card * Real.log N ≤ (2 * Real.log 4) * N := by
  let S := primeProfileBand N
  have hsub : S ⊆ (Finset.Icc 0 ⌊2*N⌋₊).filter Nat.Prime := by
    intro p hp
    obtain ⟨hpr, _, hu⟩ := primeProfileBand_mem (by linarith : 0 ≤ N) hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨Nat.zero_le _, Nat.le_floor hu⟩, hpr⟩
  calc
    _ = ∑ _p ∈ S, Real.log N := by simp [S]
    _ ≤ ∑ p ∈ S, Real.log p := Finset.sum_le_sum fun p hp =>
      Real.log_le_log (by linarith) (primeProfileBand_mem (by linarith : 0 ≤ N) hp).2.1.le
    _ ≤ Chebyshev.theta (2*N) := by
      rw [Chebyshev.theta_eq_sum_Icc]
      exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p hp _ =>
        Real.log_nonneg (by exact_mod_cast (Finset.mem_filter.mp hp).2.one_lt.le))
    _ ≤ _ := by simpa only [mul_assoc, mul_left_comm] using
      Chebyshev.theta_le_log4_mul_x (x := 2*N) (by linarith)

private theorem cubic_integral_eq_sum (N : ℝ) :
    primeGaussianCubicIntegral N =
      ∑ p ∈ primeProfileBand N, ∑ q ∈ primeProfileBand N, ∑ r ∈ primeProfileBand N,
        primeGaussianCubicCoefficient N p q r * primeGaussianCubicKernel N p q r := by
  let f : ℕ → ℕ → ℕ → ℝ → ℂ := fun p q r t => primeGaussianCubicCoefficient N p q r *
    ((bagPhysicalHeightWindow (t/(2*Real.pi*N)) : ℂ) *
      (zetaChi (linePt t) * Complex.exp ((((Real.log p+Real.log q-Real.log r)*t:ℝ):ℂ)*I)))
  have hc (p q r : ℕ) : Continuous (f p q r) := by
    have hh := continuous_zetaChiCriticalGradeIntegrand (1:ℤ) (Real.log p+Real.log q-Real.log r)
    simp only [zpow_one] at hh
    exact continuous_const.mul ((Complex.continuous_ofReal.comp
      (bagPhysicalHeightWindow.continuous.comp (continuous_id.div_const _))).mul hh)
  have hphase (p q r : ℕ) (t : ℝ) :
      Complex.exp (((Real.log p*t:ℝ):ℂ)*I) * Complex.exp (((Real.log q*t:ℝ):ℂ)*I) *
        (starRingEnd ℂ) (Complex.exp (((Real.log r*t:ℝ):ℂ)*I)) =
      Complex.exp ((((Real.log p+Real.log q-Real.log r)*t:ℝ):ℂ)*I) := by
    rw [← Complex.exp_conj]
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  calc
    _ = ∫ t in (2*Real.pi*N)..2*(2*Real.pi*N),
        ∑ p ∈ primeProfileBand N, ∑ q ∈ primeProfileBand N, ∑ r ∈ primeProfileBand N, f p q r t := by
      apply intervalIntegral.integral_congr
      intro t _
      simp only [primeGaussianChiField, one_mul, pow_two, map_sum, map_mul,
        Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro p _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro q _
      apply Finset.sum_congr rfl
      intro r _
      dsimp only [f, primeGaussianCubicCoefficient]
      linear_combination (↑(bagPhysicalHeightWindow (t/(2*Real.pi*N))) * zetaChi (linePt t) *
        (smoothAFECutoff ((p:ℝ)/N)/(Real.sqrt p:ℂ)) *
        (smoothAFECutoff ((q:ℝ)/N)/(Real.sqrt q:ℂ)) *
        (starRingEnd ℂ) (smoothAFECutoff ((r:ℝ)/N)/(Real.sqrt r:ℂ))) * hphase p q r t
    _ = _ := by
      rw [intervalIntegral.integral_finsetSum (fun p _ =>
        (continuous_finsetSum _ (fun q _ => continuous_finsetSum _ (fun r _ => hc p q r))).intervalIntegrable _ _)]
      apply Finset.sum_congr rfl
      intro p _
      rw [intervalIntegral.integral_finsetSum (fun q _ =>
        (continuous_finsetSum _ (fun r _ => hc p q r)).intervalIntegrable _ _)]
      apply Finset.sum_congr rfl
      intro q _
      rw [intervalIntegral.integral_finsetSum (fun r _ => (hc p q r).intervalIntegrable _ _)]
      simp only [f, intervalIntegral.integral_const_mul, primeGaussianCubicKernel]

/-- Complete actual cubic moment and its signed arithmetic main, with an unconditional
logarithmic saving below the repeated-prime scale. No prime triple is omitted. -/
theorem exists_primeGaussianCubic_full_error :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℝ, 1 < N →
      ‖primeGaussianCubicIntegral N - primeGaussianCubicMain N‖ ≤
        C * N / (Real.log N)^3 := by
  obtain ⟨C, hC, hb⟩ := exists_primeGaussianCubic_entry_error
  refine ⟨C * (2*Real.log 4)^3, by positivity, ?_⟩
  intro N hN
  have hN0 : 0 < N := by linarith
  have hlog : 0 < Real.log N := Real.log_pos hN
  have hcard : ((primeProfileBand N).card : ℝ) ≤ (2*Real.log 4)*N/Real.log N :=
    (le_div_iff₀ hlog).mpr (primeProfileBand_card_log_le hN)
  rw [cubic_integral_eq_sum, primeGaussianCubicMain, ← Finset.sum_sub_distrib]
  simp_rw [← Finset.sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ p ∈ primeProfileBand N, ∑ q ∈ primeProfileBand N,
        ∑ r ∈ primeProfileBand N, C / N^2 := by
      apply Finset.sum_le_sum
      intro p hp
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro q hq
      apply (norm_sum_le _ _).trans
      exact Finset.sum_le_sum fun r hr => hb N hN p hp q hq r hr
    _ = ((primeProfileBand N).card : ℝ)^3 * (C/N^2) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      ring
    _ ≤ (((2*Real.log 4)*N/Real.log N)^3) * (C/N^2) := by gcongr
    _ = _ := by field_simp

/-- The full analytic error vanishes at the cubic contraction scale N/log(N)^2.
The signed off-diagonal arithmetic sum is retained in primeGaussianCubicMain. -/
theorem tendsto_primeGaussianCubic_normalized_error :
    Tendsto (fun N : ℝ => ((Real.log N)^2 : ℂ) *
      (primeGaussianCubicIntegral N - primeGaussianCubicMain N)/(N:ℂ)) atTop (𝓝 0) := by
  obtain ⟨C, hC, hb⟩ := exists_primeGaussianCubic_full_error
  have hz : Tendsto (fun N : ℝ => C / Real.log N) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop Real.tendsto_log_atTop
  apply squeeze_zero_norm' _ hz
  filter_upwards [eventually_gt_atTop (1:ℝ)] with N hN
  have hN0 : 0 < N := by linarith
  have hlog : 0 < Real.log N := Real.log_pos hN
  rw [norm_div, norm_mul, norm_pow, Complex.norm_of_nonneg hlog.le,
    Complex.norm_of_nonneg hN0.le]
  calc
    _ ≤ (Real.log N)^2 * (C*N/(Real.log N)^3)/N := by gcongr; exact hb N hN
    _ = _ := by field_simp

/-- The original signed prime triples with both contraction equalities excluded. -/
def primeGaussianCubicOffDiagonal (N : ℝ) : ℂ :=
  ∑ r ∈ primeProfileBand N, ∑ p ∈ primeProfileBand N, ∑ q ∈ primeProfileBand N,
    if p = r ∨ q = r then 0 else primeGaussianCubicMainEntry N p q r

/-- Literal quadratic coefficient energy, written in the complex field for the contraction law. -/
def primeGaussianBandEnergy (N : ℝ) : ℂ :=
  ∑ p ∈ primeProfileBand N,
    smoothAFECutoff ((p:ℝ)/N) * (starRingEnd ℂ) (smoothAFECutoff ((p:ℝ)/N)) / (p:ℂ)

private theorem cubic_sum_contractions (S : Finset ℕ) (F : ℕ → ℕ → ℂ)
    {r : ℕ} (hr : r ∈ S) :
    (∑ p ∈ S, ∑ q ∈ S, F p q) =
      (∑ q ∈ S, F r q) + (∑ p ∈ S, F p r) - F r r +
        ∑ p ∈ S, ∑ q ∈ S, if p = r ∨ q = r then 0 else F p q := by
  classical
  have he (p q : ℕ) : F p q =
      (if p = r then F p q else 0) + (if q = r then F p q else 0) -
      (if p = r then if q = r then F p q else 0 else 0) +
      (if p = r ∨ q = r then 0 else F p q) := by
    by_cases hp : p = r <;> by_cases hq : q = r <;> simp [hp, hq]
  conv_lhs => arg 2; ext p; arg 2; ext q; rw [he p q]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  congr 2
  · rw [Finset.sum_comm]
    simp [hr]
  · simp [hr]

private theorem cubic_saddle_phase_integer (p : ℕ) :
    bourgainOscillation (2*Real.pi*(p:ℝ)) = 1 := by
  unfold bourgainOscillation
  rw [show I * ((2*Real.pi*(p:ℝ):ℝ):ℂ) = (p:ℂ)*(2*Real.pi*I) by push_cast; ring]
  exact Complex.exp_nat_mul_two_pi_mul_I p

private theorem cubic_entry_contract_left {N : ℝ} (hN : 0 < N) {q r : ℕ}
    (hr : (0:ℝ) < r) :
    primeGaussianCubicMainEntry N r q r =
      (2*Real.pi:ℂ) *
        (smoothAFECutoff ((r:ℝ)/N) * (starRingEnd ℂ) (smoothAFECutoff ((r:ℝ)/N))/(r:ℂ)) *
          primeGaussianProfile ((q:ℝ)/N) := by
  have hratio : (r:ℝ)*q/((r:ℝ)*N) = (q:ℝ)/N := by field_simp
  have hfreq : (r:ℝ)*q/r = (q:ℝ) := by field_simp
  unfold primeGaussianCubicMainEntry
  rw [hratio, hfreq, cubic_saddle_phase_integer]
  unfold primeGaussianProfile
  ring

private theorem cubic_entry_symm (N : ℝ) (p q r : ℕ) :
    primeGaussianCubicMainEntry N p q r = primeGaussianCubicMainEntry N q p r := by
  unfold primeGaussianCubicMainEntry
  rw [mul_comm (p:ℝ) (q:ℝ)]
  ring

/-- Exact repeated-prime contractions and their all-equal overlap, with the full signed
noncontracting prime sum retained. This does not assert cancellation of that sum. -/
theorem primeGaussianCubicMain_eq_contractions {N : ℝ} (hN : 0 < N) :
    primeGaussianCubicMain N =
      2 * (2*Real.pi:ℂ) * primeGaussianBandEnergy N *
        (∑ p ∈ primeProfileBand N, primeGaussianProfile ((p:ℝ)/N)) -
      (2*Real.pi:ℂ) * (∑ r ∈ primeProfileBand N,
        (smoothAFECutoff ((r:ℝ)/N) * (starRingEnd ℂ) (smoothAFECutoff ((r:ℝ)/N))/(r:ℂ)) *
          primeGaussianProfile ((r:ℝ)/N)) + primeGaussianCubicOffDiagonal N := by
  classical
  unfold primeGaussianCubicMain
  have hreorder : (∑ p ∈ primeProfileBand N, ∑ q ∈ primeProfileBand N,
      ∑ r ∈ primeProfileBand N, primeGaussianCubicMainEntry N p q r) =
      ∑ r ∈ primeProfileBand N, ∑ p ∈ primeProfileBand N, ∑ q ∈ primeProfileBand N,
        primeGaussianCubicMainEntry N p q r := by
    simp_rw [Finset.sum_comm (s := primeProfileBand N) (t := primeProfileBand N)
      (f := fun q r => primeGaussianCubicMainEntry N _ q r)]
    rw [Finset.sum_comm]
  rw [hreorder]
  have hrow (r : ℕ) (hr : r ∈ primeProfileBand N) :
      (∑ p ∈ primeProfileBand N, ∑ q ∈ primeProfileBand N, primeGaussianCubicMainEntry N p q r) =
        2 * (2*Real.pi:ℂ) *
          (smoothAFECutoff ((r:ℝ)/N) * (starRingEnd ℂ) (smoothAFECutoff ((r:ℝ)/N))/(r:ℂ)) *
          (∑ p ∈ primeProfileBand N, primeGaussianProfile ((p:ℝ)/N)) -
        (2*Real.pi:ℂ) *
          (smoothAFECutoff ((r:ℝ)/N) * (starRingEnd ℂ) (smoothAFECutoff ((r:ℝ)/N))/(r:ℂ)) *
          primeGaussianProfile ((r:ℝ)/N) +
        ∑ p ∈ primeProfileBand N, ∑ q ∈ primeProfileBand N,
          if p = r ∨ q = r then 0 else primeGaussianCubicMainEntry N p q r := by
    have hr0 : (0:ℝ) < r := hN.trans (primeProfileBand_mem hN.le hr).2.1
    rw [cubic_sum_contractions _ _ hr]
    have hl (q : ℕ) := cubic_entry_contract_left (q:=q) hN hr0
    have hh (p : ℕ) : primeGaussianCubicMainEntry N p r r =
        (2*Real.pi:ℂ) *
          (smoothAFECutoff ((r:ℝ)/N) * (starRingEnd ℂ) (smoothAFECutoff ((r:ℝ)/N))/(r:ℂ)) *
          primeGaussianProfile ((p:ℝ)/N) := by rw [cubic_entry_symm]; exact hl p
    simp_rw [hh, hl, ← Finset.mul_sum]
    ring
  rw [Finset.sum_congr rfl hrow]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  unfold primeGaussianBandEnergy primeGaussianCubicOffDiagonal
  simp_rw [mul_assoc, ← Finset.mul_sum, ← Finset.sum_mul]

/-- The noncontracting phase is the exact hyperbolic prime-gap phase. -/
theorem primeGaussianCubic_phase_recenter (p q : ℕ) {r : ℕ} (hr : 0 < r) :
    bourgainOscillation (2*Real.pi*((p:ℝ)*q/r)) =
      bourgainOscillation (2*Real.pi*(((p:ℝ)-r)*((q:ℝ)-r)/r)) := by
  have hrR : (r:ℝ) ≠ 0 := by exact_mod_cast hr.ne'
  have he : 2*Real.pi*((p:ℝ)*q/r) =
      2*Real.pi*(((p:ℝ)-r)*((q:ℝ)-r)/r) + 2*Real.pi*((p:ℝ)+(q:ℝ)-r) := by
    field_simp
    ring
  rw [he]
  unfold bourgainOscillation
  rw [Complex.ofReal_add, mul_add, Complex.exp_add]
  have hi : Complex.exp (I * ((2*Real.pi*((p:ℝ)+(q:ℝ)-r):ℝ):ℂ)) = 1 := by
    have harg : I * ((2*Real.pi*((p:ℝ)+(q:ℝ)-r):ℝ):ℂ) =
        (((p:ℤ)+(q:ℤ)-r:ℤ):ℂ)*(2*Real.pi*I) := by push_cast; ring
    rw [harg]
    exact Complex.exp_int_mul_two_pi_mul_I _
  rw [hi, mul_one]

end RHTower
