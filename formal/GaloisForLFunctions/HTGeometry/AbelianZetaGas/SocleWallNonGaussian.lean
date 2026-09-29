import GaloisForLFunctions.HTGeometry.AbelianZetaGas.SocleCondensedVarianceAsymptotic
import GaloisForLFunctions.HTGeometry.LevyContinuityLimit
import GaloisForLFunctions.RHTower.EulerTiltCovariance
import GaloisForLFunctions.RHTower.Sieve.PrimeRangeLogLogMass
import GaloisForLFunctions.RHTower.Sieve.MertensSecond

/-!
# No Gaussian limit at the condensation wall

At `σ = 1` the variance of `S_P = ∑_{p ≤ P} ξ_p` is `s_P² = (1 + o(1)) (log P)²/2`: it differs from
`∑_{p ≤ P} log² p/p` by a convergent series, and Mertens' second moment gives
`∑_{p ≤ P} log² p/p = (log P)²/2 + O(log P)`.

The standardized sums `(S_P - E S_P)/s_P` converge to no nondegenerate Gaussian.  Their
characteristic function has modulus `exp(-∑_{p ≤ P} D_p(t/s_P))`, where the realization defect
`D_p(a) = -log|Γ_{1/p}(1 + ia)|` is at most `(1 - cos(a log p))/p + 16/p²`.  Splitting the primes
at `Y = P^{1/t}`, the small primes contribute at most `(t/s_P)² log Y · (log Y + O(1))/2 ≤ 3` and
the large primes at most `2(log log P - log log Y) + o(1) ≤ 2 log(2t) + 1`.  Hence
`|φ(t)| ≥ exp(-(60 + 2 log t))` for all large `P`, which no Gaussian `e^{-vt²/2}` with `v > 0`
satisfies at `t = 200/v + 1`.
-/

open Complex Filter MeasureTheory ProbabilityTheory
open scoped Topology

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-! ## The variance at the wall -/

theorem primeCutoffLogSqSum_one_eq (P : ℕ) :
    primeCutoffLogSqSum 1 P = RHTower.primeLogSqSumLE (P : ℝ) := by
  rw [primeCutoffLogSqSum, RHTower.primeLogSqSumLE, Nat.floor_natCast,
    sum_primeCutoff P (fun n => (n : ℝ) ^ (-(1 : ℝ)) * Real.log (n : ℝ) ^ 2)]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Real.rpow_neg_one]
  ring

/-- **The wall variance.**  At `σ = 1`, `s_P² / ((log P)²/2) → 1`. -/
theorem tendsto_wallVariance :
    Tendsto (fun P : ℕ => condensedSocleVariance one_pos P / (Real.log (P : ℝ) ^ 2 / 2)) atTop
      (𝓝 1) := by
  set B : ℝ := 192 * 1 ^ 2 * ∑' p : Nat.Primes,
    Real.log ((p : ℕ) : ℝ) ^ 2 * ((p : ℕ) : ℝ) ^ (-(2 * (1 : ℝ)))
  have hsum := summable_log_sq_mul_rpow_primes (σ := 1) (by norm_num)
  have hdiff : ∀ P : ℕ, 0 ≤ condensedSocleVariance one_pos P - primeCutoffLogSqSum 1 P ∧
      condensedSocleVariance one_pos P - primeCutoffLogSqSum 1 P ≤ B := by
    intro P
    have heq : condensedSocleVariance one_pos P - primeCutoffLogSqSum 1 P
        = ∑ p ∈ primeCutoff P, ((primeNome one_pos p).lawVariance
          - 1 ^ 2 * (((p : ℕ) : ℝ) ^ (-(1 : ℝ)) * Real.log ((p : ℕ) : ℝ) ^ 2)) := by
      rw [condensedSocleVariance, primeCutoffLogSqSum, ← Finset.sum_sub_distrib]
      simp
    rw [heq]
    refine ⟨Finset.sum_nonneg fun p _ => (lawVariance_sub_le one_pos (by norm_num) p).1, ?_⟩
    calc _ ≤ ∑ p ∈ primeCutoff P, 192 * 1 ^ 2
            * (Real.log ((p : ℕ) : ℝ) ^ 2 * ((p : ℕ) : ℝ) ^ (-(2 * (1 : ℝ)))) :=
          Finset.sum_le_sum fun p _ => (lawVariance_sub_le one_pos (by norm_num) p).2
      _ = 192 * 1 ^ 2 * ∑ p ∈ primeCutoff P,
            Real.log ((p : ℕ) : ℝ) ^ 2 * ((p : ℕ) : ℝ) ^ (-(2 * (1 : ℝ))) := by
          rw [Finset.mul_sum]
      _ ≤ B := mul_le_mul_of_nonneg_left (hsum.sum_le_tsum _ fun p _ => by positivity)
          (by norm_num)
  set C : ℝ := RHTower.mertensLogSqConst
  have hlog : Tendsto (fun P : ℕ => Real.log (P : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hinv : Tendsto (fun P : ℕ => (Real.log (P : ℝ))⁻¹) atTop (𝓝 0) := hlog.inv_tendsto_atTop
  have hinv2 : Tendsto (fun P : ℕ => ((Real.log (P : ℝ)) ^ 2)⁻¹) atTop (𝓝 0) :=
    (hlog.atTop_mul_atTop₀ hlog).inv_tendsto_atTop.congr fun P => by simp [sq]
  have hmaj : Tendsto (fun P : ℕ => 2 * (C * ((Real.log (P : ℝ)) ^ 2)⁻¹
      + C * (Real.log (P : ℝ))⁻¹ + Real.log 2 ^ 2 / 2 * ((Real.log (P : ℝ)) ^ 2)⁻¹)
      + 2 * B * ((Real.log (P : ℝ)) ^ 2)⁻¹) atTop (𝓝 0) := by
    have h := ((((hinv2.const_mul C).add (hinv.const_mul C)).add
      (hinv2.const_mul (Real.log 2 ^ 2 / 2))).const_mul 2).add (hinv2.const_mul (2 * B))
    simpa using h
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hmaj
  filter_upwards [eventually_gt_atTop 1] with P hP1
  have hP2 : (2 : ℝ) ≤ (P : ℝ) := by exact_mod_cast hP1
  have hL : 0 < Real.log (P : ℝ) := Real.log_pos (by linarith)
  have hmert := RHTower.abs_primeLogSqSumLE_sub_le hP2
  rw [← primeCutoffLogSqSum_one_eq] at hmert
  have hd := hdiff P
  rw [Real.norm_eq_abs]
  have hL2 : 0 < Real.log (P : ℝ) ^ 2 / 2 := by positivity
  rw [div_sub_one hL2.ne', abs_div, abs_of_pos hL2, div_le_iff₀ hL2]
  have habs : |condensedSocleVariance one_pos P - Real.log (P : ℝ) ^ 2 / 2|
      ≤ C * (1 + Real.log (P : ℝ)) + Real.log 2 ^ 2 / 2 + B := by
    rw [abs_le] at hmert ⊢
    constructor <;> linarith [hd.1, hd.2, hmert.1, hmert.2]
  refine habs.trans (le_of_eq ?_)
  field_simp

/-! ## The modulus of the standardized characteristic function -/

/-- The realization defect `D_p(a) = -log|Γ_q(1 + ia)|`. -/
def wallDefect (p : Nat.Primes) (a : ℝ) : ℝ :=
  -Real.log ‖qGammaOn (primeNome one_pos p) (1 + (a : ℂ) * I)‖

theorem re_cumulant_eq_neg_wallDefect (p : Nat.Primes) (a : ℝ) :
    ((primeNome one_pos p).cumulant a).re = -wallDefect p a := by
  have h := (primeNome one_pos p).qChar_eq_cexp_cumulant a
  rw [qChar_eq_qGammaOn_one_add_I] at h
  rw [wallDefect, neg_neg, h, Complex.norm_exp, Real.log_exp]

theorem norm_charFun_condensedSocleStandardized_wall (P : ℕ) (t : ℝ) :
    ‖charFun (condensedSocleStandardized one_pos P : Measure ℝ) t‖
      = Real.exp (-∑ p ∈ primeCutoff P, wallDefect p (t / condensedSocleScale one_pos P)) := by
  rw [charFun_condensedSocleStandardized, Complex.norm_exp]
  congr 1
  simp only [Complex.sub_re, Complex.re_sum, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero,
    re_cumulant_eq_neg_wallDefect, Finset.sum_neg_distrib]

theorem wallDefect_le (p : Nat.Primes) (a : ℝ) :
    wallDefect p a ≤ (1 - Real.cos (a * Real.log ((p : ℕ) : ℝ))) / ((p : ℕ) : ℝ)
      + 16 / ((p : ℕ) : ℝ) ^ 2 := by
  have h := abs_defect_sub_leading_le (primeNome one_pos p) a
  have hp2 : (2 : ℝ) ≤ ((p : ℕ) : ℝ) := by exact_mod_cast p.2.two_le
  have hq : (primeNome one_pos p).val = ((p : ℕ) : ℝ)⁻¹ := by
    rw [primeNome_val, Real.rpow_neg_one]
  have hphase : phaseAngle (primeNome one_pos p) a = a * Real.log ((p : ℕ) : ℝ) := by
    rw [phaseAngle, log_primeNome]
    ring
  rw [hphase, hq] at h
  have hq1 : ((p : ℕ) : ℝ)⁻¹ ≤ 1 / 2 := by
    rw [inv_eq_one_div, div_le_div_iff₀ (by linarith) (by norm_num)]
    linarith
  have hq0 : 0 < ((p : ℕ) : ℝ)⁻¹ := by positivity
  have hrem : 4 * ((p : ℕ) : ℝ)⁻¹ ^ 2 / (1 - ((p : ℕ) : ℝ)⁻¹) ^ 2 ≤ 16 / ((p : ℕ) : ℝ) ^ 2 := by
    have h1 : 1 / 2 ≤ 1 - ((p : ℕ) : ℝ)⁻¹ := by linarith
    have h2 : (1 / 2 : ℝ) ^ 2 ≤ (1 - ((p : ℕ) : ℝ)⁻¹) ^ 2 := pow_le_pow_left₀ (by norm_num) h1 2
    rw [div_le_div_iff₀ (by positivity) (by positivity), inv_pow]
    have hp0 : 0 < ((p : ℕ) : ℝ) ^ 2 := by positivity
    field_simp
    nlinarith
  rw [wallDefect]
  have := (abs_le.mp h).2
  have hlead : ((p : ℕ) : ℝ)⁻¹ * (1 - Real.cos (a * Real.log ((p : ℕ) : ℝ)))
      = (1 - Real.cos (a * Real.log ((p : ℕ) : ℝ))) / ((p : ℕ) : ℝ) := by
    rw [inv_mul_eq_div]
  linarith

/-! ## The splitting estimate -/

theorem sum_inv_sq_primesLE_le (P : ℕ) :
    ∑ n ∈ Nat.primesLE P, 16 / (n : ℝ) ^ 2 ≤ 48 := by
  have hs := hasSum_zeta_two
  have hle : ∑ n ∈ Nat.primesLE P, 1 / (n : ℝ) ^ 2 ≤ Real.pi ^ 2 / 6 := by
    rw [← hs.tsum_eq]
    exact hs.summable.sum_le_tsum _ fun n _ => by positivity
  have hpi : Real.pi ^ 2 / 6 ≤ 3 := by nlinarith [Real.pi_lt_four, Real.pi_pos]
  calc ∑ n ∈ Nat.primesLE P, 16 / (n : ℝ) ^ 2 = 16 * ∑ n ∈ Nat.primesLE P, 1 / (n : ℝ) ^ 2 := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun n _ => by ring
    _ ≤ 16 * 3 := by linarith
    _ = 48 := by norm_num

/-- The small primes: `∑_{p ≤ Y} (1 - cos(a log p))/p ≤ a²/2 · log Y (log Y + K)`. -/
theorem sum_small_primes_le {Y : ℕ} (hY : 1 ≤ Y) (a : ℝ) :
    ∑ n ∈ Nat.primesLE Y, (1 - Real.cos (a * Real.log (n : ℝ))) / (n : ℝ)
      ≤ a ^ 2 / 2 * (Real.log (Y : ℝ) * (Real.log (Y : ℝ) + RHTower.Sieve.mertensFirstConst)) := by
  have hmert := RHTower.Sieve.abs_mertensA_sub_log_le hY
  have hA : RHTower.Sieve.mertensA Y ≤ Real.log (Y : ℝ) + RHTower.Sieve.mertensFirstConst := by
    linarith [(abs_le.mp hmert).2]
  have hlogY : 0 ≤ Real.log (Y : ℝ) := Real.log_natCast_nonneg Y
  calc ∑ n ∈ Nat.primesLE Y, (1 - Real.cos (a * Real.log (n : ℝ))) / (n : ℝ)
      ≤ ∑ n ∈ Nat.primesLE Y, a ^ 2 / 2 * Real.log (Y : ℝ) * (Real.log (n : ℝ) / (n : ℝ)) := by
        refine Finset.sum_le_sum fun n hn => ?_
        have hn' := Nat.mem_primesLE.mp hn
        have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn'.2.two_le
        have hn0 : (0 : ℝ) < n := by linarith
        have hln : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by linarith)
        have hlnY : Real.log (n : ℝ) ≤ Real.log (Y : ℝ) :=
          Real.log_le_log hn0 (by exact_mod_cast hn'.1)
        have hcos := Real.one_sub_sq_div_two_le_cos (x := a * Real.log (n : ℝ))
        rw [div_le_iff₀ hn0]
        have hmul : a ^ 2 / 2 * Real.log (Y : ℝ) * (Real.log (n : ℝ) / (n : ℝ)) * (n : ℝ)
            = a ^ 2 / 2 * Real.log (Y : ℝ) * Real.log (n : ℝ) := by field_simp
        rw [hmul]
        have ha2 : 0 ≤ a ^ 2 / 2 := by positivity
        have := mul_le_mul_of_nonneg_left hlnY (mul_nonneg ha2 hln)
        nlinarith [sq_nonneg a, sq_nonneg (Real.log (n : ℝ))]
    _ = a ^ 2 / 2 * Real.log (Y : ℝ) * RHTower.Sieve.mertensA Y := by
        rw [← Finset.mul_sum, RHTower.Sieve.mertensA]
    _ ≤ a ^ 2 / 2 * Real.log (Y : ℝ) * (Real.log (Y : ℝ) + RHTower.Sieve.mertensFirstConst) :=
        mul_le_mul_of_nonneg_left hA (by positivity)
    _ = _ := by ring

/-- The large primes: `∑_{Y < p ≤ P} (1 - cos(a log p))/p ≤ 2 ∑_{Y < p ≤ P} 1/p`. -/
theorem sum_large_primes_le {Y P : ℕ} (hY : 2 ≤ Y) (hYP : Y ≤ P) (a : ℝ) :
    ∑ n ∈ RHTower.Sieve.primesRange Y P, (1 - Real.cos (a * Real.log (n : ℝ))) / (n : ℝ)
      ≤ 2 * (Real.log (Real.log (P : ℝ)) - Real.log (Real.log (Y : ℝ))
        + 2 * ((2 * RHTower.Sieve.mertensFirstConst + 1 / 2) / Real.log (Y : ℝ))) := by
  have h := RHTower.Sieve.sum_inv_primesRange_le_logLog_diff hY hYP
  calc ∑ n ∈ RHTower.Sieve.primesRange Y P, (1 - Real.cos (a * Real.log (n : ℝ))) / (n : ℝ)
      ≤ ∑ n ∈ RHTower.Sieve.primesRange Y P, 2 * (1 / (n : ℝ)) := by
        refine Finset.sum_le_sum fun n _ => ?_
        have hc := Real.neg_one_le_cos (a * Real.log (n : ℝ))
        calc (1 - Real.cos (a * Real.log (n : ℝ))) / (n : ℝ) ≤ 2 / (n : ℝ) :=
              div_le_div_of_nonneg_right (by linarith) (Nat.cast_nonneg n)
          _ = 2 * (1 / (n : ℝ)) := by ring
    _ = 2 * ∑ n ∈ RHTower.Sieve.primesRange Y P, 1 / (n : ℝ) := by rw [Finset.mul_sum]
    _ ≤ _ := by linarith

/-! ## The defect stays logarithmic -/

theorem eventually_wallScale_sq_ge :
    ∀ᶠ P : ℕ in atTop, Real.log (P : ℝ) ^ 2 / 4 ≤ condensedSocleScale one_pos P ^ 2 := by
  filter_upwards [tendsto_wallVariance.eventually (lt_mem_nhds (show (1 / 2 : ℝ) < 1 by norm_num)),
    eventually_gt_atTop 1] with P hP hP1
  have hP2 : (1 : ℝ) < (P : ℝ) := by exact_mod_cast hP1
  have hL : 0 < Real.log (P : ℝ) := Real.log_pos hP2
  have hL2 : 0 < Real.log (P : ℝ) ^ 2 / 2 := by positivity
  rw [condensedSocleScale_sq]
  rw [lt_div_iff₀ hL2] at hP
  linarith

/-- For every `t ≥ 1`, eventually `∑_{p ≤ P} D_p(t/s_P) ≤ 60 + 2 log t`. -/
theorem eventually_sum_wallDefect_le {t : ℝ} (ht : 1 ≤ t) :
    ∀ᶠ P : ℕ in atTop, ∑ p ∈ primeCutoff P, wallDefect p (t / condensedSocleScale one_pos P)
      ≤ 60 + 2 * Real.log t := by
  set K : ℝ := RHTower.Sieve.mertensFirstConst with hKdef
  have hK : 0 ≤ K := RHTower.Sieve.mertensFirstConst_nonneg
  have ht0 : 0 < t := by linarith
  have hlog : Tendsto (fun P : ℕ => Real.log (P : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hroot : Tendsto (fun P : ℕ => (P : ℝ) ^ (1 / t)) atTop atTop :=
    (tendsto_rpow_atTop (by positivity)).comp tendsto_natCast_atTop_atTop
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  filter_upwards [eventually_wallScale_sq_ge, hroot.eventually_ge_atTop 3,
    hlog.eventually_ge_atTop (4 * t * K + 8 * t * (2 * K + 1 / 2) + 4 * t * Real.log 2 + 1),
    eventually_gt_atTop 1] with P hs hroot3 hL hP1
  set L : ℝ := Real.log (P : ℝ) with hLdef
  set sP := condensedSocleScale one_pos P with hsdef
  set a : ℝ := t / sP with hadef
  set Y : ℕ := ⌊(P : ℝ) ^ (1 / t)⌋₊ with hYdef
  have hP0 : (0 : ℝ) < P := by exact_mod_cast (Nat.zero_lt_of_lt hP1)
  have hL0 : 0 < L := by
    have : (1 : ℝ) < P := by exact_mod_cast hP1
    exact Real.log_pos this
  have hsP : 0 < sP := by
    have h1 : 0 < L ^ 2 / 4 := by positivity
    have h2 : 0 < sP ^ 2 := lt_of_lt_of_le h1 hs
    have h3 : 0 ≤ sP := Real.sqrt_nonneg _
    rcases h3.lt_or_eq with h | h
    · exact h
    · rw [← h] at h2
      simp at h2
  -- the cut `Y = ⌊P^{1/t}⌋`
  have hYle : (Y : ℝ) ≤ (P : ℝ) ^ (1 / t) := Nat.floor_le (by positivity)
  have hYge : (P : ℝ) ^ (1 / t) / 2 ≤ (Y : ℝ) := by
    have := Nat.lt_floor_add_one ((P : ℝ) ^ (1 / t))
    linarith
  have hY2 : 2 ≤ Y := by
    have : (2 : ℝ) ≤ (Y : ℝ) := by
      have := Nat.lt_floor_add_one ((P : ℝ) ^ (1 / t))
      have h3 : (3 : ℝ) ≤ (P : ℝ) ^ (1 / t) := hroot3
      linarith
    exact_mod_cast this
  have hYP : Y ≤ P := by
    have hroot_le : (P : ℝ) ^ (1 / t) ≤ (P : ℝ) := by
      have h1 : (1 : ℝ) ≤ P := by exact_mod_cast hP1.le
      calc (P : ℝ) ^ (1 / t) ≤ (P : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le h1 (by rw [div_le_one ht0]; exact ht)
        _ = P := Real.rpow_one _
    exact_mod_cast hYle.trans hroot_le
  have hY0 : (0 : ℝ) < (Y : ℝ) := by exact_mod_cast (by omega : 0 < Y)
  have hlogroot : Real.log ((P : ℝ) ^ (1 / t)) = L / t := by
    rw [Real.log_rpow hP0]
    ring
  have hlogY_le : Real.log (Y : ℝ) ≤ L / t := by
    rw [← hlogroot]
    exact Real.log_le_log hY0 hYle
  have hlogY_ge : L / (2 * t) ≤ Real.log (Y : ℝ) := by
    have h1 : Real.log ((P : ℝ) ^ (1 / t) / 2) ≤ Real.log (Y : ℝ) :=
      Real.log_le_log (by positivity) hYge
    rw [Real.log_div (by positivity) (by norm_num), hlogroot] at h1
    have h2 : L / (2 * t) + Real.log 2 ≤ L / t := by
      have h4 : 2 * t * Real.log 2 ≤ L := by
        linarith [mul_nonneg ht0.le hK, mul_pos ht0 hlog2]
      have h5 : Real.log 2 ≤ L / (2 * t) := by
        rw [le_div_iff₀ (by positivity)]
        linarith
      have h6 : L / t = L / (2 * t) + L / (2 * t) := by
        field_simp
        ring
      linarith
    linarith
  have hlogY_pos : 0 < Real.log (Y : ℝ) := lt_of_lt_of_le (by positivity) hlogY_ge
  -- small primes
  have ha2 : a ^ 2 ≤ 4 * t ^ 2 / L ^ 2 := by
    rw [hadef, div_pow, div_le_div_iff₀ (by positivity) (by positivity)]
    have := mul_le_mul_of_nonneg_left (show L ^ 2 ≤ 4 * sP ^ 2 by linarith) (sq_nonneg t)
    linarith
  have hsmall := sum_small_primes_le (Y := Y) (by omega) a
  have hsmall' : a ^ 2 / 2 * (Real.log (Y : ℝ) * (Real.log (Y : ℝ) + K)) ≤ 5 / 2 := by
    have h1 : Real.log (Y : ℝ) * (Real.log (Y : ℝ) + K) ≤ L / t * (L / t + K) := by
      have := hlogY_pos.le
      gcongr
    have h2 : a ^ 2 / 2 * (Real.log (Y : ℝ) * (Real.log (Y : ℝ) + K))
        ≤ 4 * t ^ 2 / L ^ 2 / 2 * (L / t * (L / t + K)) := by
      gcongr
    have h3 : 4 * t ^ 2 / L ^ 2 / 2 * (L / t * (L / t + K)) = 2 + 2 * t * K / L := by
      field_simp
      norm_num
    have h4 : 2 * t * K / L ≤ 1 / 2 := by
      rw [div_le_iff₀ hL0]
      linarith [mul_nonneg ht0.le hK, mul_pos ht0 hlog2]
    linarith
  -- large primes
  have hlarge := sum_large_primes_le hY2 hYP a
  have hloglog : Real.log L - Real.log (Real.log (Y : ℝ)) ≤ Real.log (2 * t) := by
    have h1 : Real.log (L / (2 * t)) ≤ Real.log (Real.log (Y : ℝ)) :=
      Real.log_le_log (by positivity) hlogY_ge
    rw [Real.log_div hL0.ne' (by positivity)] at h1
    linarith
  have htail : 2 * ((2 * K + 1 / 2) / Real.log (Y : ℝ)) ≤ 1 / 2 := by
    have h1 : 8 * t * (2 * K + 1 / 2) ≤ L := by
      linarith [mul_nonneg ht0.le hK, mul_pos ht0 hlog2]
    have h2 : 4 * (2 * K + 1 / 2) ≤ Real.log (Y : ℝ) := by
      have : 4 * (2 * K + 1 / 2) ≤ L / (2 * t) := by
        rw [le_div_iff₀ (by positivity)]
        linarith
      linarith
    rw [← mul_div_assoc, div_le_iff₀ hlogY_pos]
    linarith
  have hlog2t : Real.log (2 * t) = Real.log 2 + Real.log t :=
    Real.log_mul (by norm_num) ht0.ne'
  have hlog2' : Real.log 2 < 1 := by
    have := Real.log_two_lt_d9
    linarith
  -- assemble
  have hsplit : ∑ n ∈ Nat.primesLE P, (1 - Real.cos (a * Real.log (n : ℝ))) / (n : ℝ)
      = ∑ n ∈ Nat.primesLE Y, (1 - Real.cos (a * Real.log (n : ℝ))) / (n : ℝ)
        + ∑ n ∈ RHTower.Sieve.primesRange Y P,
            (1 - Real.cos (a * Real.log (n : ℝ))) / (n : ℝ) := by
    rw [RHTower.Sieve.primesRange, add_comm,
      Finset.sum_sdiff (Nat.primesLE_mono hYP)]
  calc ∑ p ∈ primeCutoff P, wallDefect p a
      ≤ ∑ p ∈ primeCutoff P, ((1 - Real.cos (a * Real.log ((p : ℕ) : ℝ))) / ((p : ℕ) : ℝ)
          + 16 / ((p : ℕ) : ℝ) ^ 2) := Finset.sum_le_sum fun p _ => wallDefect_le p a
    _ = ∑ n ∈ Nat.primesLE P, (1 - Real.cos (a * Real.log (n : ℝ))) / (n : ℝ)
          + ∑ n ∈ Nat.primesLE P, 16 / (n : ℝ) ^ 2 := by
        rw [sum_primeCutoff P (fun n => (1 - Real.cos (a * Real.log (n : ℝ))) / (n : ℝ)
          + 16 / (n : ℝ) ^ 2), Finset.sum_add_distrib]
    _ ≤ 5 / 2 + 2 * (Real.log (2 * t) + 1 / 2) + 48 := by
        rw [hsplit]
        have h48 := sum_inv_sq_primesLE_le P
        have hl : Real.log L - Real.log (Real.log (Y : ℝ))
            + 2 * ((2 * K + 1 / 2) / Real.log (Y : ℝ)) ≤ Real.log (2 * t) + 1 / 2 := by linarith
        have hlarge' := hlarge.trans (mul_le_mul_of_nonneg_left hl (by norm_num))
        linarith
    _ ≤ 60 + 2 * Real.log t := by rw [hlog2t]; linarith

/-- **Theorem 3.2, second clause.**  At the wall `σ = 1` the standardized sums
`(S_P - E S_P)/s_P` converge in law to no Gaussian with nonzero variance. -/
theorem not_tendsto_condensedSocleStandardized_wall (μ₀ : ℝ) {v : NNReal} (hv : v ≠ 0) :
    ¬ Tendsto (condensedSocleStandardized one_pos) atTop
      (𝓝 (⟨gaussianReal μ₀ v, inferInstance⟩ : ProbabilityMeasure ℝ)) := by
  intro h
  have hV : 0 < (v : ℝ) := by
    have := v.2
    exact lt_of_le_of_ne this (fun h0 => hv (NNReal.coe_eq_zero.mp h0.symm))
  set t : ℝ := 200 / (v : ℝ) + 1 with htdef
  have ht1 : 1 ≤ t := by rw [htdef]; have := div_pos (by norm_num : (0 : ℝ) < 200) hV; linarith
  have hchar : Tendsto (fun P => charFun (condensedSocleStandardized one_pos P : Measure ℝ) t)
      atTop (𝓝 (charFun (gaussianReal μ₀ v) t)) := tendsto_charFun_of_tendsto h t
  have hG : ‖charFun (gaussianReal μ₀ v) t‖ = Real.exp (-((v : ℝ) * t ^ 2 / 2)) := by
    rw [charFun_gaussianReal, Complex.norm_exp]
    congr 1
    have hre : ((t : ℂ) * (μ₀ : ℂ) * I - ((v : ℝ) : ℂ) * (t : ℂ) ^ 2 / 2)
        = ((-((v : ℝ) * t ^ 2 / 2) : ℝ) : ℂ) + ((t * μ₀ : ℝ) : ℂ) * I := by
      push_cast
      ring
    rw [hre, Complex.add_re, Complex.ofReal_re, Complex.re_ofReal_mul, Complex.I_re, mul_zero,
      add_zero]
  have hnorm := (continuous_norm.tendsto _).comp hchar
  rw [hG] at hnorm
  have hlow : ∀ᶠ P : ℕ in atTop, Real.exp (-(60 + 2 * Real.log t))
      ≤ ‖charFun (condensedSocleStandardized one_pos P : Measure ℝ) t‖ := by
    filter_upwards [eventually_sum_wallDefect_le ht1] with P hP
    rw [norm_charFun_condensedSocleStandardized_wall]
    exact Real.exp_le_exp.mpr (by linarith)
  have hle := ge_of_tendsto hnorm hlow
  rw [Real.exp_le_exp] at hle
  have hlogt : Real.log t ≤ t := (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
  have hvt : 200 < (v : ℝ) * t := by
    rw [htdef, mul_add, mul_div_cancel₀ _ hV.ne', mul_one]
    linarith
  have hprod := mul_lt_mul_of_pos_right hvt (by linarith : (0 : ℝ) < t)
  have hsq : (v : ℝ) * t * t = (v : ℝ) * t ^ 2 := by ring
  linarith

end GaloisForLFunctions.HTGeometry
