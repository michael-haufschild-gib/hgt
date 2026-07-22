import GaloisForLFunctions.RHTower.SuzukiMangoldtApexCrossPrimeBlock
import GaloisForLFunctions.RHTower.WindowBudget
import GaloisForLFunctions.HTGeometry.TiltedTentRightFlank
import Mathlib.Analysis.SpecialFunctions.Log.Monotone

open Set Finset

noncomputable section

namespace RHTower

open GaloisForLFunctions.HTGeometry

/-!
# Macroscopic prime-block surplus at aligned Suzuki apices

At width `log 5`, align the moving Suzuki apex with the Mangoldt node `2 log n`.
Every prime node in the multiplicative block `(2n, 5n]` lies on the strictly decreasing
right flank.  Subcritical tilted-tent monotonicity gives one uniform contraction factor.

Chebyshev's theta bounds show symbolically that, once `exp 20 ≤ n`, the block carries at
least `1/10` of log-Haar mass.  The aggregate source surplus is therefore bounded below by
a positive constant times `sqrt n`, matching the scale of a fixed-width moving-apex seam.
No zero hypothesis or prime-gap estimate is used.
-/

/-- Width-five aperture whose moving apex is the node `2 * log n`. -/
def suzukiMangoldtFiveApexAperture (n : ℕ) : ℝ :=
  Real.log (5 * (n : ℝ)) / 2

/-- Prime block on the right flank of the width-five aligned moving tent. -/
def suzukiMangoldtFivePrimeBlock (n : ℕ) : Finset ℕ :=
  windowPrimes (2 * (n : ℝ)) (5 * (n : ℝ))

/-- Uniform contraction of the width-five right flank beyond the node `2n`. -/
def suzukiMangoldtFiveFlankContraction : ℝ :=
  Real.sqrt 2 * (1 - Real.log 2 / Real.log 5)

theorem suzukiMangoldtFiveFlankContraction_mem_Ioo :
    suzukiMangoldtFiveFlankContraction ∈ Set.Ioo (0 : ℝ) 1 := by
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlog5 : 0 < Real.log (5 : ℝ) := Real.log_pos (by norm_num)
  have hlog25 : Real.log 2 < Real.log 5 :=
    Real.strictMonoOn_log (by norm_num) (by norm_num) (by norm_num)
  have hL2 : (1 / 2 : ℝ) * Real.log 5 < 1 := by
    nlinarith [Real.log_five_lt_d9]
  have hright := tiltedTentRightProfile_lt_one (beta := (1 / 2 : ℝ))
    (L := Real.log 5) (d := Real.log 2) (by norm_num) hlog5 hL2 hlog2 hlog25.le
  have hsqrt : Real.exp (Real.log 2 / 2) = Real.sqrt 2 := by
    rw [← Real.log_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.exp_log (by positivity)]
  have heq : tiltedTentRightProfile (1 / 2 : ℝ) (Real.log 5) (Real.log 2) =
      suzukiMangoldtFiveFlankContraction := by
    rw [tiltedTentRightProfile, suzukiMangoldtFiveFlankContraction]
    rw [show (1 / 2 : ℝ) * Real.log 2 = Real.log 2 / 2 by ring, hsqrt]
  rw [heq] at hright
  exact ⟨mul_pos (Real.sqrt_pos.2 (by norm_num)) (sub_pos.2 (div_lt_one hlog5 |>.2 hlog25)),
    hright⟩

/-- The explicit width-five contraction is the exact least uniform ceiling on the continuous
right-flank tail from displacement `log 2` through the support endpoint `log 5`. -/
theorem suzukiMangoldtFiveFlankContraction_isSharp
    {C : ℝ} :
    (∀ d ∈ Set.Icc (Real.log 2) (Real.log 5),
        tiltedTentRightProfile (1 / 2 : ℝ) (Real.log 5) d ≤ C) ↔
      suzukiMangoldtFiveFlankContraction ≤ C := by
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlog5 : 0 < Real.log (5 : ℝ) := Real.log_pos (by norm_num)
  have hlog25 : Real.log 2 < Real.log 5 :=
    Real.strictMonoOn_log (by norm_num) (by norm_num) (by norm_num)
  have hsub : (1 / 2 : ℝ) * Real.log 5 < 1 := by
    nlinarith [Real.log_five_lt_d9]
  rw [tiltedTentRightProfile_tail_bound_iff (by norm_num) hlog5 hsub
    hlog2.le hlog25.le]
  have hsqrt : Real.exp (Real.log 2 / 2) = Real.sqrt 2 := by
    rw [← Real.log_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.exp_log (by positivity)]
  rw [tiltedTentRightProfile, suzukiMangoldtFiveFlankContraction,
    show (1 / 2 : ℝ) * Real.log 2 = Real.log 2 / 2 by ring, hsqrt]

/-- A symbolic exponential bound used to keep the Chebyshev threshold computation-free. -/
theorem exp_ten_gt_thousand : (1000 : ℝ) < Real.exp 10 := by
  have he1 : (2 : ℝ) < Real.exp 1 := by nlinarith [Real.exp_one_gt_d9]
  have hp : (2 : ℝ) ^ 10 < Real.exp 1 ^ 10 :=
    pow_lt_pow_left₀ he1 (by norm_num) (by norm_num)
  rw [← Real.exp_nat_mul] at hp
  norm_num at hp
  linarith

/-- Past `exp 20`, the logarithmic Chebyshev error at `5N` is below one fiftieth of
the square-root scale. -/
theorem five_mul_log_div_sqrt_le
    {N : ℝ} (hN : Real.exp 20 ≤ N) :
    Real.log (5 * N) / Real.sqrt (5 * N) < 1 / 50 := by
  have hNpos : 0 < N := (Real.exp_pos 20).trans_le hN
  have hexp2le20 : Real.exp 2 ≤ Real.exp 20 := Real.exp_le_exp.mpr (by norm_num)
  have hxmem : 5 * N ∈ Set.Ici (Real.exp 2) := by
    rw [Set.mem_Ici]
    exact hexp2le20.trans (hN.trans (by nlinarith [hNpos]))
  have he20mem : Real.exp 20 ∈ Set.Ici (Real.exp 2) := hexp2le20
  have hanti := Real.log_div_sqrt_antitoneOn he20mem hxmem
    (hN.trans (by nlinarith [hNpos]))
  change Real.log (5 * N) / Real.sqrt (5 * N) ≤
    Real.log (Real.exp 20) / Real.sqrt (Real.exp 20) at hanti
  rw [Real.log_exp, ← Real.exp_half] at hanti
  norm_num at hanti
  have hfrac : 20 / Real.exp 10 < (1 / 50 : ℝ) := by
    rw [div_lt_iff₀ (Real.exp_pos 10)]
    nlinarith [exp_ten_gt_thousand]
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 5)]
  exact hanti.trans_lt hfrac

/-- The primes in `(2n,5n]` carry at least `n/4` of theta mass beyond the symbolic threshold. -/
theorem chebyshev_fivePrimeBlock_logMass_floor
    {n : ℕ} (hn : Real.exp 20 ≤ (n : ℝ)) :
    (n : ℝ) / 4 ≤ ∑ p ∈ suzukiMangoldtFivePrimeBlock n, Real.log p := by
  have hNpos : (0 : ℝ) < n := (Real.exp_pos 20).trans_le hn
  have hN20 : (20 : ℝ) < n := by
    have he := Real.add_one_le_exp (20 : ℝ)
    linarith
  have hlog2lo : (1 / 2 : ℝ) < Real.log 2 := by
    nlinarith [Real.log_two_gt_d9]
  have hlog2hi : Real.log 2 < (1 : ℝ) := by
    have h := Real.log_lt_sub_one_of_pos (x := (2 : ℝ)) (by norm_num) (by norm_num)
    linarith
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
    ring
  have hratio := five_mul_log_div_sqrt_le hn
  have hxpos : 0 < 5 * (n : ℝ) := by positivity
  have hsqrtx : 0 < Real.sqrt (5 * (n : ℝ)) := Real.sqrt_pos.2 hxpos
  have herror1 : 2 * Real.sqrt (5 * (n : ℝ)) * Real.log (5 * (n : ℝ)) ≤
      (n : ℝ) / 5 := by
    have hsq := Real.sq_sqrt hxpos.le
    have hmul := mul_le_mul_of_nonneg_left hratio.le
      (show 0 ≤ 2 * (5 * (n : ℝ)) by positivity)
    field_simp at hmul ⊢
    nlinarith
  have hfiveTwo : 5 * (n : ℝ) + 2 ≤ 6 * (n : ℝ) := by linarith
  have hzpos : 0 < 5 * (n : ℝ) + 2 := by positivity
  have hlogSqrt := Real.log_le_sub_one_of_pos (Real.sqrt_pos.2 hzpos)
  rw [Real.log_sqrt hzpos.le] at hlogSqrt
  have hlogz : Real.log (5 * (n : ℝ) + 2) ≤ 2 * Real.sqrt (5 * (n : ℝ) + 2) := by
    linarith
  have hsqrtz : Real.sqrt (5 * (n : ℝ) + 2) ≤ Real.sqrt (6 * (n : ℝ)) :=
    Real.sqrt_le_sqrt hfiveTwo
  have hsqrt6 : Real.sqrt (6 : ℝ) < 3 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 6), Real.sqrt_nonneg (6 : ℝ)]
  have hsqrtN : Real.exp 10 ≤ Real.sqrt (n : ℝ) := by
    have hs := Real.sqrt_le_sqrt hn
    rw [← Real.exp_half] at hs
    norm_num at hs
    exact hs
  have hsqrtN1000 : (1000 : ℝ) < Real.sqrt (n : ℝ) :=
    exp_ten_gt_thousand.trans_le hsqrtN
  have herror2 : Real.log (5 * (n : ℝ) + 2) ≤ (n : ℝ) / 100 := by
    have hsqrtMul : Real.sqrt (6 * (n : ℝ)) = Real.sqrt 6 * Real.sqrt n := by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 6)]
    have hNroot := Real.mul_self_sqrt hNpos.le
    rw [hsqrtMul] at hsqrtz
    calc
      Real.log (5 * (n : ℝ) + 2) ≤ 2 * Real.sqrt (5 * (n : ℝ) + 2) := hlogz
      _ ≤ 2 * Real.sqrt (6 * (n : ℝ)) := by linarith
      _ ≤ 6 * Real.sqrt (n : ℝ) := by
        rw [hsqrtMul]
        nlinarith [Real.sqrt_nonneg (n : ℝ)]
      _ ≤ (n : ℝ) / 100 := by nlinarith
  have htheta5 := Chebyshev.theta_ge'
    (show (1 : ℝ) ≤ 5 * (n : ℝ) by nlinarith)
  have htheta2 := Chebyshev.theta_le_log4_mul_x
    (show (0 : ℝ) ≤ 2 * (n : ℝ) by positivity)
  have hbudget : (n : ℝ) / 4 ≤
      Chebyshev.theta (5 * (n : ℝ)) - Chebyshev.theta (2 * (n : ℝ)) := by
    rw [hlog4] at htheta2
    nlinarith
  rw [suzukiMangoldtFivePrimeBlock,
    sum_log_windowPrimes (by nlinarith [hNpos] : 2 * (n : ℝ) ≤ 5 * (n : ℝ))]
  exact hbudget

/-- Exact width-five sample at an aperture aligned with the node `2 * log n`. -/
theorem suzukiMangoldtFiveAlignedApex_sample_eq
    {n m : ℕ} (hn : 5 ≤ n) (hm : 5 ≤ m) :
    suzukiRectangularPositiveArchSampleChannel (Real.log 5)
        (suzukiMangoldtFiveApexAperture n) (mangoldtLogHaarNode m) =
      Real.sqrt m *
        max 0 (Real.log 5 - |Real.log ((m : ℝ) / (n : ℝ))|) := by
  have hnR : (0 : ℝ) < n := by positivity
  have hmR : (0 : ℝ) < m := by positivity
  have hlogFive : 0 < Real.log (5 : ℝ) := Real.log_pos (by norm_num)
  have hlogn : Real.log 5 ≤ Real.log (n : ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hn)
  have hlogm : Real.log 5 ≤ Real.log (m : ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hm)
  have hlogMulN : Real.log (5 * (n : ℝ)) = Real.log 5 + Real.log n :=
    Real.log_mul (by norm_num) hnR.ne'
  have ha : Real.log 5 ≤ suzukiMangoldtFiveApexAperture n := by
    rw [suzukiMangoldtFiveApexAperture, hlogMulN]
    linarith
  have ht : 0 ≤ mangoldtLogHaarNode m := by
    rw [mangoldtLogHaarNode]
    positivity
  rw [suzukiRectangularPositiveArchSampleChannel_eq_fixed_add_moving
    hlogFive.le ha ht]
  have hfixed : suzukiRectangularFixedArchChannel (Real.log 5)
      (mangoldtLogHaarNode m) = 0 := by
    rw [suzukiRectangularFixedArchChannel, mangoldtLogHaarNode]
    have hheight : Real.log 5 - (2 * Real.log (m : ℝ)) / 2 ≤ 0 := by
      linarith
    rw [max_eq_left hheight]
    ring
  rw [hfixed, zero_add, suzukiRectangularMovingArchChannel,
    mangoldtLogHaarNode, suzukiMangoldtFiveApexAperture, hlogMulN]
  have hcenter : 2 * ((Real.log 5 + Real.log (n : ℝ)) / 2) - Real.log 5 =
      Real.log (n : ℝ) := by ring
  rw [hcenter]
  have hexp : Real.exp (Real.log (m : ℝ) / 2) = Real.sqrt (m : ℝ) := by
    rw [← Real.log_sqrt hmR.le, Real.exp_log (Real.sqrt_pos.mpr hmR)]
  rw [show 2 * Real.log (m : ℝ) / 4 = Real.log (m : ℝ) / 2 by ring,
    show 2 * Real.log (m : ℝ) / 2 - Real.log (n : ℝ) =
      Real.log ((m : ℝ) / (n : ℝ)) by
        rw [Real.log_div hmR.ne' hnR.ne']
        ring,
    hexp]

/-- Exact height of the width-five aligned apex. -/
theorem suzukiMangoldtFiveAlignedApex_self_eq
    {n : ℕ} (hn : 5 ≤ n) :
    suzukiRectangularPositiveArchSampleChannel (Real.log 5)
        (suzukiMangoldtFiveApexAperture n) (mangoldtLogHaarNode n) =
      Real.sqrt n * Real.log 5 := by
  rw [suzukiMangoldtFiveAlignedApex_sample_eq hn hn]
  have hnR : (0 : ℝ) < n := by positivity
  have hlogFive : 0 < Real.log (5 : ℝ) := Real.log_pos (by norm_num)
  rw [div_self hnR.ne', Real.log_one, abs_zero, sub_zero,
    max_eq_right hlogFive.le]

theorem mem_suzukiMangoldtFivePrimeBlock
    {n p : ℕ} :
    p ∈ suzukiMangoldtFivePrimeBlock n ↔
      p.Prime ∧ 2 * n < p ∧ p ≤ 5 * n := by
  rw [suzukiMangoldtFivePrimeBlock,
    mem_windowPrimes (by positivity : (0 : ℝ) ≤ 2 * (n : ℝ))
      (by positivity : (0 : ℝ) ≤ 5 * (n : ℝ))]
  norm_cast

/-- Every prime in the fivefold block contracts by the same explicit factor. -/
theorem suzukiMangoldtFivePrimeBlock_sample_le
    {n p : ℕ} (hn : 5 ≤ n) (hp : p ∈ suzukiMangoldtFivePrimeBlock n) :
    suzukiRectangularPositiveArchSampleChannel (Real.log 5)
        (suzukiMangoldtFiveApexAperture n) (mangoldtLogHaarNode p) ≤
      suzukiMangoldtFiveFlankContraction *
        suzukiRectangularPositiveArchSampleChannel (Real.log 5)
          (suzukiMangoldtFiveApexAperture n) (mangoldtLogHaarNode n) := by
  obtain ⟨hpPrime, hpLower, hpUpper⟩ := mem_suzukiMangoldtFivePrimeBlock.mp hp
  have hpFive : 5 ≤ p := by omega
  have hnR : (0 : ℝ) < n := by positivity
  have hpR : (0 : ℝ) < p := by positivity
  let d := Real.log ((p : ℝ) / (n : ℝ))
  have hratioPos : 0 < (p : ℝ) / (n : ℝ) := div_pos hpR hnR
  have hratioLower : (2 : ℝ) < (p : ℝ) / (n : ℝ) := by
    rw [lt_div_iff₀ hnR]
    exact_mod_cast hpLower
  have hratioUpper : (p : ℝ) / (n : ℝ) ≤ 5 := by
    rw [div_le_iff₀ hnR]
    exact_mod_cast hpUpper
  have hlogLower : Real.log 2 < d := by
    dsimp [d]
    exact Real.log_lt_log (by norm_num) hratioLower
  have hlogUpper : d ≤ Real.log 5 := by
    dsimp [d]
    exact Real.log_le_log hratioPos hratioUpper
  have hdNonneg : 0 ≤ d := by
    dsimp [d]
    exact (Real.log_pos (by linarith : (1 : ℝ) < (p : ℝ) / (n : ℝ))).le
  have hsqrtP : Real.sqrt (p : ℝ) =
      Real.sqrt (n : ℝ) * Real.exp (d / 2) := by
    rw [← suzukiMangoldt_exp_log_div_two_eq_sqrt hpR,
      ← suzukiMangoldt_exp_log_div_two_eq_sqrt hnR, ← Real.exp_add]
    congr 1
    dsimp [d]
    rw [Real.log_div hpR.ne' hnR.ne']
    ring
  have hsample :
      suzukiRectangularPositiveArchSampleChannel (Real.log 5)
          (suzukiMangoldtFiveApexAperture n) (mangoldtLogHaarNode p) =
        (Real.sqrt n * Real.log 5) *
          tiltedTentRightProfile (1 / 2 : ℝ) (Real.log 5) d := by
    rw [suzukiMangoldtFiveAlignedApex_sample_eq hn hpFive,
      abs_of_nonneg hdNonneg, max_eq_right (sub_nonneg.mpr hlogUpper), hsqrtP,
      tiltedTentRightProfile]
    have hlogNe : Real.log (5 : ℝ) ≠ 0 := (Real.log_pos (by norm_num)).ne'
    field_simp [hlogNe]
  have hlogFive : 0 < Real.log (5 : ℝ) := Real.log_pos (by norm_num)
  have hsub : (1 / 2 : ℝ) * Real.log 5 < 1 := by
    nlinarith [Real.log_five_lt_d9]
  have hanti := tiltedTentRightProfile_strictAntiOn
    (beta := (1 / 2 : ℝ)) (L := Real.log 5) (by norm_num) hlogFive hsub
  have hprofile : tiltedTentRightProfile (1 / 2 : ℝ) (Real.log 5) d <
      tiltedTentRightProfile (1 / 2 : ℝ) (Real.log 5) (Real.log 2) :=
    hanti ⟨(Real.log_pos (by norm_num)).le, hlogLower.le.trans hlogUpper⟩
      ⟨hdNonneg, hlogUpper⟩ hlogLower
  have hsqrtTwo : Real.exp (Real.log 2 / 2) = Real.sqrt 2 := by
    rw [← Real.log_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.exp_log (by positivity)]
  have hq : tiltedTentRightProfile (1 / 2 : ℝ) (Real.log 5) (Real.log 2) =
      suzukiMangoldtFiveFlankContraction := by
    rw [tiltedTentRightProfile, suzukiMangoldtFiveFlankContraction,
      show (1 / 2 : ℝ) * Real.log 2 = Real.log 2 / 2 by ring, hsqrtTwo]
  have hselfNonneg : 0 ≤ Real.sqrt (n : ℝ) * Real.log 5 := by positivity
  rw [hsample, suzukiMangoldtFiveAlignedApex_self_eq hn, ← hq]
  simpa [mul_comm] using mul_le_mul_of_nonneg_left hprofile.le hselfNonneg

/-- The fivefold prime block carries at least one tenth of log-Haar mass. -/
theorem suzukiMangoldtFivePrimeBlock_atomMass_floor
    {n : ℕ} (hn : Real.exp 20 ≤ (n : ℝ)) :
    (1 / 10 : ℝ) ≤
      ∑ p ∈ suzukiMangoldtFivePrimeBlock n, mangoldtLogHaarAtomMass p := by
  have hNpos : (0 : ℝ) < n := (Real.exp_pos 20).trans_le hn
  have hlogMass := chebyshev_fivePrimeBlock_logMass_floor hn
  have hterm : ∀ p ∈ suzukiMangoldtFivePrimeBlock n,
      (2 / (5 * (n : ℝ))) * Real.log p ≤ mangoldtLogHaarAtomMass p := by
    intro p hp
    obtain ⟨hpPrime, _hpLower, hpUpper⟩ := mem_suzukiMangoldtFivePrimeBlock.mp hp
    have hpPos : (0 : ℝ) < p := by exact_mod_cast hpPrime.pos
    have hlogp : 0 ≤ Real.log (p : ℝ) :=
      Real.log_nonneg (by exact_mod_cast (show 1 ≤ p by omega))
    rw [mangoldtLogHaarAtomMass, ArithmeticFunction.vonMangoldt_apply_prime hpPrime]
    have hpUpperR : (p : ℝ) ≤ 5 * (n : ℝ) := by exact_mod_cast hpUpper
    calc
      (2 / (5 * (n : ℝ))) * Real.log p =
          (2 * Real.log p) / (5 * (n : ℝ)) := by ring
      _ ≤ (2 * Real.log p) / (p : ℝ) := by
        apply (div_le_div_iff₀ (by positivity : 0 < 5 * (n : ℝ)) hpPos).mpr
        nlinarith
  calc
    (1 / 10 : ℝ) = (2 / (5 * (n : ℝ))) * ((n : ℝ) / 4) := by
      field_simp
      ring
    _ ≤ (2 / (5 * (n : ℝ))) *
        (∑ p ∈ suzukiMangoldtFivePrimeBlock n, Real.log p) :=
      mul_le_mul_of_nonneg_left hlogMass (by positivity)
    _ = ∑ p ∈ suzukiMangoldtFivePrimeBlock n,
        (2 / (5 * (n : ℝ))) * Real.log p := by rw [Finset.mul_sum]
    _ ≤ ∑ p ∈ suzukiMangoldtFivePrimeBlock n, mangoldtLogHaarAtomMass p :=
      Finset.sum_le_sum hterm

/-- Aggregate source surplus of the fivefold prime block. -/
def suzukiMangoldtFivePrimeBlockSurplus (n : ℕ) : ℝ :=
  ∑ p ∈ suzukiMangoldtFivePrimeBlock n,
    mangoldtLogHaarAtomMass p *
      (suzukiRectangularPositiveArchSampleChannel (Real.log 5)
          (suzukiMangoldtFiveApexAperture n) (mangoldtLogHaarNode n) -
        suzukiRectangularPositiveArchSampleChannel (Real.log 5)
          (suzukiMangoldtFiveApexAperture n) (mangoldtLogHaarNode p))

/-- The actual-prime block surplus grows at least on the aligned apex scale `sqrt n`. -/
theorem suzukiMangoldtFivePrimeBlockSurplus_lower
    {n : ℕ} (hn : Real.exp 20 ≤ (n : ℝ)) :
    (1 - suzukiMangoldtFiveFlankContraction) / 10 *
        (Real.sqrt n * Real.log 5) ≤
      suzukiMangoldtFivePrimeBlockSurplus n := by
  have hnFive : 5 ≤ n := by
    have he := Real.add_one_le_exp (20 : ℝ)
    exact_mod_cast (show (5 : ℝ) ≤ n by linarith)
  have hmass := suzukiMangoldtFivePrimeBlock_atomMass_floor hn
  have hqNonneg : 0 ≤ 1 - suzukiMangoldtFiveFlankContraction :=
    sub_nonneg.mpr suzukiMangoldtFiveFlankContraction_mem_Ioo.2.le
  have hheightNonneg : 0 ≤ Real.sqrt (n : ℝ) * Real.log 5 := by positivity
  have hterm : ∀ p ∈ suzukiMangoldtFivePrimeBlock n,
      mangoldtLogHaarAtomMass p *
          ((1 - suzukiMangoldtFiveFlankContraction) *
            (Real.sqrt n * Real.log 5)) ≤
        mangoldtLogHaarAtomMass p *
          (suzukiRectangularPositiveArchSampleChannel (Real.log 5)
              (suzukiMangoldtFiveApexAperture n) (mangoldtLogHaarNode n) -
            suzukiRectangularPositiveArchSampleChannel (Real.log 5)
              (suzukiMangoldtFiveApexAperture n) (mangoldtLogHaarNode p)) := by
    intro p hp
    have hsample := suzukiMangoldtFivePrimeBlock_sample_le hnFive hp
    rw [suzukiMangoldtFiveAlignedApex_self_eq hnFive] at hsample
    apply mul_le_mul_of_nonneg_left _ (mangoldtLogHaarAtomMass_nonneg p)
    rw [suzukiMangoldtFiveAlignedApex_self_eq hnFive]
    nlinarith
  rw [suzukiMangoldtFivePrimeBlockSurplus]
  calc
    (1 - suzukiMangoldtFiveFlankContraction) / 10 *
        (Real.sqrt n * Real.log 5) =
      (1 / 10 : ℝ) * ((1 - suzukiMangoldtFiveFlankContraction) *
        (Real.sqrt n * Real.log 5)) := by ring
    _ ≤ (∑ p ∈ suzukiMangoldtFivePrimeBlock n, mangoldtLogHaarAtomMass p) *
        ((1 - suzukiMangoldtFiveFlankContraction) *
          (Real.sqrt n * Real.log 5)) :=
      mul_le_mul_of_nonneg_right hmass (mul_nonneg hqNonneg hheightNonneg)
    _ = ∑ p ∈ suzukiMangoldtFivePrimeBlock n,
        mangoldtLogHaarAtomMass p *
          ((1 - suzukiMangoldtFiveFlankContraction) *
            (Real.sqrt n * Real.log 5)) := by rw [Finset.sum_mul]
    _ ≤ _ := Finset.sum_le_sum hterm

/-- The macroscopic fivefold Suzuki--Mangoldt prime-block surplus is strictly positive. -/
theorem suzukiMangoldtFivePrimeBlockSurplus_pos
    {n : ℕ} (hn : Real.exp 20 ≤ (n : ℝ)) :
    0 < suzukiMangoldtFivePrimeBlockSurplus n := by
  have hlower := suzukiMangoldtFivePrimeBlockSurplus_lower hn
  have hcoeff : 0 < 1 - suzukiMangoldtFiveFlankContraction :=
    sub_pos.mpr suzukiMangoldtFiveFlankContraction_mem_Ioo.2
  have hnPos : (0 : ℝ) < n := (Real.exp_pos 20).trans_le hn
  have hpositive : 0 < (1 - suzukiMangoldtFiveFlankContraction) / 10 *
      (Real.sqrt n * Real.log 5) := by positivity
  exact hpositive.trans_le hlower

/-- The macroscopic prime-block surplus is unbounded: every prescribed real level is eventually
exceeded by an explicit block above the symbolic Chebyshev threshold. -/
theorem suzukiMangoldtFivePrimeBlockSurplus_unbounded
    (B : ℝ) :
    ∃ n : ℕ, Real.exp 20 ≤ (n : ℝ) ∧
      B < suzukiMangoldtFivePrimeBlockSurplus n := by
  let c : ℝ :=
    (1 - suzukiMangoldtFiveFlankContraction) / 10 * Real.log 5
  have hc : 0 < c := by
    dsimp [c]
    have hq : suzukiMangoldtFiveFlankContraction < 1 :=
      suzukiMangoldtFiveFlankContraction_mem_Ioo.2
    positivity
  obtain ⟨n, hn⟩ := exists_nat_gt
    (max (Real.exp 20) ((max B 0 / c) ^ 2))
  have hN : Real.exp 20 ≤ (n : ℝ) :=
    (le_max_left _ _).trans hn.le
  have hsq : (max B 0 / c) ^ 2 < (n : ℝ) :=
    (le_max_right _ _).trans_lt hn
  have hratioNonneg : 0 ≤ max B 0 / c := div_nonneg (le_max_right _ _) hc.le
  have hratioSqrt : max B 0 / c < Real.sqrt (n : ℝ) :=
    (Real.lt_sqrt hratioNonneg).2 hsq
  have hmax : max B 0 < c * Real.sqrt (n : ℝ) := by
    calc
      max B 0 = c * (max B 0 / c) := by field_simp
      _ < c * Real.sqrt (n : ℝ) := mul_lt_mul_of_pos_left hratioSqrt hc
  have hscale : B < c * Real.sqrt (n : ℝ) := (le_max_left _ _).trans_lt hmax
  have hlower := suzukiMangoldtFivePrimeBlockSurplus_lower hN
  have hcRewrite : c * Real.sqrt (n : ℝ) =
      (1 - suzukiMangoldtFiveFlankContraction) / 10 *
        (Real.sqrt n * Real.log 5) := by
    dsimp [c]
    ring
  rw [hcRewrite] at hscale
  exact ⟨n, hN, hscale.trans_le hlower⟩

end RHTower
