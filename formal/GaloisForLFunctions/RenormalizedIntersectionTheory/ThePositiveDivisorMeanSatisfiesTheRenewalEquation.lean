import GaloisForLFunctions.ArithmeticCountingPositivity.TheDivisorCountHasAPositiveRenewalKernel
import GaloisForLFunctions.RenormalizedIntersectionTheory.TheWirsingBoundForFlipTwins

/-!
# The positive divisor mean satisfies a renewal equation

The nonnegative convolution `1 * ω` lets a cumulative kernel estimate be summed without
paying total variation of the signed harmonic mean. Its error is proportional to its own
polar moment and harmonic mean. This is the positive equation behind the zero-density limit.
-/

noncomputable section

open Finset Filter Topology
open scoped ArithmeticFunction.vonMangoldt

namespace GaloisForLFunctions.RenormalizedIntersectionTheory

open GaloisForLFunctions.ArithmeticCountingPositivity
  GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
  GaloisForLFunctions.SelectiveMultiscaleArithmeticPositivity

/-- The positive harmonic mean is nondecreasing with the horizon. -/
theorem gaugeHarmonicSum_signDivisorCount_mono {ω : ℕ → ℝ} (hω : IsSignGauge ω) :
    Monotone (gaugeHarmonicSum (signDivisorCount ω)) := by
  intro M N hMN
  exact sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc le_rfl hMN)
    fun n _ _ => div_nonneg (signDivisorCount_nonneg hω n) (Nat.cast_nonneg _)

/-- The first divisor coefficient ensures that the positive polar moment never degenerates. -/
theorem log_le_polarMoment_signDivisorCount {ω : ℕ → ℝ} (hω : IsSignGauge ω)
    {N : ℕ} (hN : 1 ≤ N) : Real.log N ≤ polarMoment (signDivisorCount ω) N := by
  have hterm : ∀ n ∈ Icc 1 N,
      0 ≤ signDivisorCount ω n / n * Real.log ((N : ℝ) / n) := by
    intro n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
    have hnN : (n : ℝ) ≤ N := by exact_mod_cast (mem_Icc.mp hn).2
    exact mul_nonneg (div_nonneg (signDivisorCount_nonneg hω n) hn0.le)
      (Real.log_nonneg ((one_le_div hn0).mpr hnN))
  have h := single_le_sum hterm (mem_Icc.mpr ⟨le_rfl, hN⟩)
  simpa only [polarMoment, signDivisorCount_one hω, Nat.cast_one, div_one, one_mul] using h

private theorem hyperbolic_swap (a b : ℕ → ℝ) (N : ℕ) :
    ∑ d ∈ Icc 1 N, a d * ∑ m ∈ Icc 1 (N / d), b m =
      ∑ m ∈ Icc 1 N, b m * ∑ d ∈ Icc 1 (N / m), a d := by
  simp only [mul_sum]
  rw [sum_comm' (t' := Icc 1 N) (s' := fun m => Icc 1 (N / m))]
  · exact sum_congr rfl fun m _ => sum_congr rfl fun d _ => mul_comm _ _
  · intro d m
    simp only [mem_Icc]
    constructor
    · rintro ⟨⟨hd1, hdN⟩, hm1, hmd⟩
      have hmd' : m * d ≤ N := (Nat.le_div_iff_mul_le (by omega)).mp hmd
      refine ⟨⟨hd1, (Nat.le_div_iff_mul_le (by omega)).mpr (by simpa only [Nat.mul_comm] using hmd')⟩,
        hm1, ?_⟩
      exact (show m ≤ m * d by simpa only [mul_one] using Nat.mul_le_mul_left m hd1).trans hmd'
    · rintro ⟨⟨hd1, hdm⟩, hm1, hmN⟩
      have hdm' : d * m ≤ N := (Nat.le_div_iff_mul_le (by omega)).mp hdm
      refine ⟨⟨hd1, ?_⟩, hm1,
        (Nat.le_div_iff_mul_le (by omega)).mpr (by simpa only [Nat.mul_comm] using hdm')⟩
      exact (show d ≤ d * m by simpa only [mul_one] using Nat.mul_le_mul_left d hm1).trans hdm'

/-- Swapping the renewal sums exposes a positive average of the cumulative kernel. -/
theorem logMoment_signDivisorCount_eq {ω : ℕ → ℝ} (hω : IsSignGauge ω) (N : ℕ) :
    logMoment (signDivisorCount ω) N =
      ∑ m ∈ Icc 1 N, signDivisorCount ω m / m *
        gaugeHarmonicSum (signRenewalKernel ω) (N / m) := by
  rw [logMoment, signDivisorCount_logMoment_eq hω]
  exact hyperbolic_swap (fun d => signRenewalKernel ω d / d)
    (fun m => signDivisorCount ω m / m) N

private theorem log_quotient_sub_log_div_bounds {N m : ℕ} (hm : 1 ≤ m) (hmN : m ≤ N) :
    0 ≤ Real.log ((N : ℝ) / m) - Real.log (N / m : ℕ) ∧
      Real.log ((N : ℝ) / m) - Real.log (N / m : ℕ) ≤ Real.log 2 := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hq : 1 ≤ N / m := (Nat.le_div_iff_mul_le hm).mpr (by simpa using hmN)
  have hq0 : (0 : ℝ) < (N / m : ℕ) := by exact_mod_cast hq
  have hlo : ((N / m : ℕ) : ℝ) ≤ (N : ℝ) / m := Nat.cast_div_le
  have hhi : (N : ℝ) / m ≤ 2 * (N / m : ℕ) := by
    have hlt := Nat.lt_div_mul_add (a := N) (b := m) hm
    have hqm : m ≤ (N / m) * m := by simpa only [one_mul] using Nat.mul_le_mul_right m hq
    have hle : N ≤ 2 * (N / m) * m := by nlinarith only [hlt, hqm]
    apply (div_le_iff₀ hm0).mpr
    exact_mod_cast hle
  refine ⟨sub_nonneg.mpr (Real.log_le_log hq0 hlo), ?_⟩
  have hlog := Real.log_le_log (lt_of_lt_of_le hq0 hlo) hhi
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hq0.ne'] at hlog
  linarith only [hlog]

private theorem positive_polarMoment_sub_logWeightSum {g : ℕ → ℝ}
    (hg : ∀ n, 0 ≤ g n) (N : ℕ) :
    0 ≤ polarMoment g N - logWeightSum g N ∧
      polarMoment g N - logWeightSum g N ≤ Real.log 2 * gaugeHarmonicSum g N := by
  rw [polarMoment, logWeightSum_eq, ← sum_sub_distrib]
  have hterm : ∀ m ∈ Icc 1 N,
      0 ≤ g m / m * Real.log ((N : ℝ) / m) - g m / m * Real.log (N / m : ℕ) ∧
      g m / m * Real.log ((N : ℝ) / m) - g m / m * Real.log (N / m : ℕ) ≤
        Real.log 2 * (g m / m) := by
    intro m hm
    have hb := log_quotient_sub_log_div_bounds (mem_Icc.mp hm).1 (mem_Icc.mp hm).2
    have hw : 0 ≤ g m / m := div_nonneg (hg m) (Nat.cast_nonneg _)
    rw [← mul_sub]
    exact ⟨mul_nonneg hw hb.1, (mul_le_mul_of_nonneg_left hb.2 hw).trans_eq (mul_comm _ _)⟩
  refine ⟨sum_nonneg fun m hm => (hterm m hm).1, ?_⟩
  rw [gaugeHarmonicSum, mul_sum]
  exact sum_le_sum fun m hm => (hterm m hm).2

/-- A cumulative kernel error costs the positive polar moment, rather than the signed
mean's total variation. -/
theorem abs_positive_divisor_renewal_equation_le {ω : ℕ → ℝ} (hω : IsSignGauge ω)
    {β ε C : ℝ} (hβ : 0 ≤ β) (hε : 0 ≤ ε)
    (hA : ∀ n : ℕ, 1 ≤ n →
      |gaugeHarmonicSum (signRenewalKernel ω) n - β * Real.log n| ≤ ε * Real.log n + C)
    (N : ℕ) :
    |gaugeHarmonicSum (signDivisorCount ω) N * Real.log N -
      (1 + β) * polarMoment (signDivisorCount ω) N| ≤
      ε * polarMoment (signDivisorCount ω) N +
        (C + β * Real.log 2) * gaugeHarmonicSum (signDivisorCount ω) N := by
  let g := signDivisorCount ω
  have hg : ∀ n, 0 ≤ g n := signDivisorCount_nonneg hω
  have herr : |logMoment g N - β * logWeightSum g N| ≤
      ε * logWeightSum g N + C * gaugeHarmonicSum g N := by
    rw [logMoment_signDivisorCount_eq hω, logWeightSum_eq, mul_sum, ← sum_sub_distrib]
    calc
      _ ≤ ∑ m ∈ Icc 1 N, |g m / m * gaugeHarmonicSum (signRenewalKernel ω) (N / m) -
          β * (g m / m * Real.log (N / m : ℕ))| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ m ∈ Icc 1 N, g m / m * (ε * Real.log (N / m : ℕ) + C) := by
        apply sum_le_sum
        intro m hm
        have hw : 0 ≤ g m / m := div_nonneg (hg m) (Nat.cast_nonneg _)
        have hq : 1 ≤ N / m := (Nat.le_div_iff_mul_le (mem_Icc.mp hm).1).mpr
          (by simpa using (mem_Icc.mp hm).2)
        calc
          _ = |g m / m * (gaugeHarmonicSum (signRenewalKernel ω) (N / m) -
              β * Real.log (N / m : ℕ))| := by congr 1; ring
          _ = g m / m * |gaugeHarmonicSum (signRenewalKernel ω) (N / m) -
              β * Real.log (N / m : ℕ)| := by rw [abs_mul, abs_of_nonneg hw]
          _ ≤ _ := mul_le_mul_of_nonneg_left (hA _ hq) hw
      _ = _ := by
        rw [gaugeHarmonicSum, mul_sum, mul_sum, ← sum_add_distrib]
        exact sum_congr rfl fun m _ => by ring
  have hdiff := positive_polarMoment_sub_logWeightSum hg N
  have heq : gaugeHarmonicSum g N * Real.log N - (1 + β) * polarMoment g N =
      (logMoment g N - β * logWeightSum g N) -
        β * (polarMoment g N - logWeightSum g N) := by rw [logMoment_eq]; ring
  rw [show signDivisorCount ω = g from rfl, heq]
  calc
    _ ≤ |logMoment g N - β * logWeightSum g N| +
        |β * (polarMoment g N - logWeightSum g N)| := abs_sub _ _
    _ ≤ (ε * logWeightSum g N + C * gaugeHarmonicSum g N) +
        β * (Real.log 2 * gaugeHarmonicSum g N) := by
      rw [abs_of_nonneg (mul_nonneg hβ hdiff.1)]
      exact add_le_add herr (mul_le_mul_of_nonneg_left hdiff.2 hβ)
    _ ≤ _ := by
      have hmono := mul_le_mul_of_nonneg_left (sub_nonneg.mp hdiff.1) hε
      nlinarith only [hmono]

private theorem exists_abs_signRenewalMean_sub_log_add_logMass_le (P : Set ℕ) :
    ∃ K : ℝ, ∀ N : ℕ, 1 ≤ N →
      |gaugeHarmonicSum (signRenewalKernel (primeSetFlip P)) N -
        2 * Real.log N + 2 * primeSetLogMass P N| ≤ K := by
  let Cp := (Real.log 4 + 4) + (8 + RHTower.Mertens.mertensTail)
  let Ct := 2 * (Real.log 4 + 4) + (8 + RHTower.Mertens.mertensTail)
  refine ⟨2 * |Cp| + 2 * |Ct|, fun N hN => ?_⟩
  have hω := primeSetFlip_isSignGauge P
  have htail0 : 0 ≤ ∑ d ∈ Icc 1 N with ¬ d.Prime,
      signRenewalKernel (primeSetFlip P) d / d :=
    sum_nonneg fun d _ => div_nonneg (signRenewalKernel_nonneg hω d) (Nat.cast_nonneg _)
  have htail : (∑ d ∈ Icc 1 N with ¬ d.Prime,
      signRenewalKernel (primeSetFlip P) d / d) ≤ 2 * Ct := by
    calc
      _ ≤ ∑ d ∈ Icc 1 N with ¬ d.Prime, 2 * (Λ d / d) := by
        apply sum_le_sum
        intro d hd
        have hd0 : d ≠ 0 := Nat.ne_of_gt (mem_Icc.mp (mem_filter.mp hd).1).1
        have hw := le_abs_self (primeSetFlip P d)
        rw [abs_eq_one_of_mul_self_eq_one (hω.mul_self hd0)] at hw
        have hterm := mul_le_mul_of_nonneg_right
          (show 1 + primeSetFlip P d ≤ 2 by linarith only [hw])
          (show 0 ≤ Λ d / d by positivity)
        simpa only [signRenewalKernel, mul_div_assoc] using hterm
      _ ≤ 2 * Ct := by
        rw [← mul_sum]
        exact mul_le_mul_of_nonneg_left (sum_vonMangoldt_nonprime_le hN) (by norm_num)
  have hprime : (∑ d ∈ Icc 1 N with d.Prime,
      signRenewalKernel (primeSetFlip P) d / d) =
      2 * (∑ d ∈ Icc 1 N with d.Prime, Real.log d / d) - 2 * primeSetLogMass P N := by
    have hsum : (∑ d ∈ Icc 1 N with d.Prime,
        signRenewalKernel (primeSetFlip P) d / d) =
        (∑ d ∈ Icc 1 N with d.Prime, Real.log d / d) + primeMean (primeSetFlip P) N := by
      rw [primeMean, ← sum_add_distrib]
      refine sum_congr rfl fun d hd => ?_
      rw [signRenewalKernel, ArithmeticFunction.vonMangoldt_apply_prime (mem_filter.mp hd).2]
      ring
    rw [hsum, primeMean_primeSetFlip]
    ring
  have hsplit := sum_filter_add_sum_filter_not (Icc 1 N) Nat.Prime
    (fun d => signRenewalKernel (primeSetFlip P) d / d)
  rw [hprime] at hsplit
  have hM0 : |(∑ d ∈ Icc 1 N with d.Prime, Real.log d / d) - Real.log N| ≤ Cp :=
    RHTower.Mertens.mertens_first_prime N hN
  have hM := abs_le.mp hM0
  rw [abs_le]
  change - (2 * |Cp| + 2 * |Ct|) ≤ _ ∧ _ ≤ 2 * |Cp| + 2 * |Ct|
  unfold gaugeHarmonicSum
  constructor <;> linarith only [hsplit, htail0, htail, hM.1, hM.2,
    le_abs_self Cp, le_abs_self Ct, abs_nonneg Ct]

private theorem exists_signRenewalMean_log_error_le (P : Set ℕ)
    (hP : Tendsto (fun N => primeSetLogMass P N / (1 + Real.log N)) atTop (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N →
      |gaugeHarmonicSum (signRenewalKernel (primeSetFlip P)) N - 2 * Real.log N| ≤
        ε * Real.log N + C := by
  obtain ⟨K, hK⟩ := exists_abs_signRenewalMean_sub_log_add_logMass_le P
  have hlim : Tendsto (fun N => |primeSetLogMass P N / (1 + Real.log N)|) atTop (𝓝 0) :=
    by simpa only [abs_zero] using hP.abs
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp (hlim.eventually_le_const (half_pos hε))
  let R : ℕ → ℝ := fun N => gaugeHarmonicSum (signRenewalKernel (primeSetFlip P)) N - 2 * Real.log N
  let B := ∑ n ∈ range N₀, |R n|
  have hB : 0 ≤ B := sum_nonneg fun n _ => abs_nonneg _
  refine ⟨|K| + ε + B, fun N hN => ?_⟩
  have hlog : 0 ≤ Real.log N := Real.log_natCast_nonneg N
  change |R N| ≤ _
  by_cases hNN : N₀ ≤ N
  · have hden : 0 < 1 + Real.log N := by linarith only [hlog]
    have hmass := hN₀ N hNN
    rw [abs_div, abs_of_pos hden] at hmass
    have hmass' := (div_le_iff₀ hden).mp hmass
    have htriangle : |R N| ≤ K + 2 * |primeSetLogMass P N| := by
      calc
        _ = |(R N + 2 * primeSetLogMass P N) - 2 * primeSetLogMass P N| := by ring_nf
        _ ≤ |R N + 2 * primeSetLogMass P N| + |2 * primeSetLogMass P N| := abs_sub _ _
        _ ≤ K + 2 * |primeSetLogMass P N| := by
          rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
          exact add_le_add (hK N hN) le_rfl
    nlinarith only [hmass', htriangle, le_abs_self K, hB]
  · have hsmall : |R N| ≤ B := single_le_sum (fun n (_hn : n ∈ range N₀) => abs_nonneg (R n))
        (mem_range.mpr (lt_of_not_ge hNN))
    have hεlog : 0 ≤ ε * Real.log N := mul_nonneg hε.le hlog
    linarith only [hsmall, abs_nonneg K, hεlog, hε]

/-- Zero relative logarithmic prime density gives a relative renewal error for the positive
divisor mean, without a power-saving density error or an Euler-mass assumption. -/
theorem exists_abs_positive_divisor_renewal_equation_le (P : Set ℕ)
    (hP : Tendsto (fun N => primeSetLogMass P N / (1 + Real.log N)) atTop (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, ∀ N : ℕ,
      |gaugeHarmonicSum (signDivisorCount (primeSetFlip P)) N * Real.log N -
        3 * polarMoment (signDivisorCount (primeSetFlip P)) N| ≤
      ε * polarMoment (signDivisorCount (primeSetFlip P)) N +
        C * gaugeHarmonicSum (signDivisorCount (primeSetFlip P)) N := by
  obtain ⟨C, hC⟩ := exists_signRenewalMean_log_error_le P hP hε
  refine ⟨C + 2 * Real.log 2, fun N => ?_⟩
  simpa only [show (1 : ℝ) + 2 = 3 by norm_num] using
    abs_positive_divisor_renewal_equation_le (primeSetFlip_isSignGauge P)
      (by norm_num : (0 : ℝ) ≤ 2) hε.le hC N

end GaloisForLFunctions.RenormalizedIntersectionTheory
