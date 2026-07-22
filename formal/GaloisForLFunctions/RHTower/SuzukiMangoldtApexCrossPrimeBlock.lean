import GaloisForLFunctions.RHTower.SuzukiMangoldtApexRayIsolation
import GaloisForLFunctions.HTGeometry.TiltedTentGeometricBracketMinimax
import Mathlib.NumberTheory.Bertrand
import Mathlib.Analysis.SpecialFunctions.Log.Monotone

open MeasureTheory Set
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower

/-!
# Cross-prime block dilution at every aligned Suzuki--Mangoldt apex

For width `log 2`, positivity of the sample aligned at `n` is classified exactly by the
open multiplicative annulus `n < 2m` and `m < 2n`. Bertrand's theorem therefore supplies
a lower and an upper prime flank at every apex `n ≥ 4`.

The arithmetic weights are quantitative: the lower prime has at least the apex Mangoldt mass,
and twice the upper-prime mass is strictly larger than the apex mass. Consequently the apex
occupies strictly less than two fifths of the resulting three-atom block, and its weighted sample
average is strictly diluted below the apex value. Equivalently, the two cross-prime flanks produce
a strictly positive source-side block surplus.

A second, prime-gap-free law uses the adjacent powers of two bracketing `n`. Exact geometric
minimax gives the sharp continuous contraction factor
`exp (-((sqrt 2 - 1) * log 2) / 2) * (2 - sqrt 2)`, strictly improving `sqrt 2 / 2`.
The selected flank retains strictly positive Mangoldt mass.

All statements are unconditional. The theorem supplies the source-side block required by the
Suzuki apex seam; it does not assert the still-open continuum target-capacity domination.
-/

theorem suzukiMangoldtAlignedApex_sample_pos_iff_openAnnulus
    {n m : ℕ} (hn : 2 ≤ n) (hm : 2 ≤ m) :
    0 < suzukiRectangularPositiveArchSampleChannel (Real.log 2)
        (suzukiMangoldtApexAperture n) (mangoldtLogHaarNode m) ↔
      n < 2 * m ∧ m < 2 * n := by
  rw [suzukiMangoldtAlignedApex_sample_eq hn hm]
  have hnR : (0 : ℝ) < n := by positivity
  have hmR : (0 : ℝ) < m := by positivity
  have hsqrt : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.mpr hmR
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hratioPos : 0 < (m : ℝ) / (n : ℝ) := div_pos hmR hnR
  have hhalfPos : (0 : ℝ) < 1 / 2 := by norm_num
  have hlogHalf : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
    rw [Real.log_div (by norm_num : (1 : ℝ) ≠ 0) (by norm_num : (2 : ℝ) ≠ 0)]
    simp
  rw [mul_pos_iff]
  simp only [hsqrt, true_and, not_lt_of_ge hsqrt.le, false_and, or_false]
  rw [lt_max_iff]
  simp only [lt_irrefl, false_or]
  constructor
  · intro hpos
    have habs : |Real.log ((m : ℝ) / (n : ℝ))| < Real.log 2 := by linarith
    rcases (abs_lt.mp habs) with ⟨hloLog, hhiLog⟩
    have hloLog' : Real.log (1 / 2 : ℝ) < Real.log ((m : ℝ) / (n : ℝ)) := by
      rwa [hlogHalf]
    have hloRatio : (1 / 2 : ℝ) < (m : ℝ) / (n : ℝ) :=
      (Real.log_lt_log_iff hhalfPos hratioPos).mp hloLog'
    have hhiRatio : (m : ℝ) / (n : ℝ) < 2 :=
      (Real.log_lt_log_iff hratioPos (by norm_num)).mp hhiLog
    have hloReal : (n : ℝ) < 2 * (m : ℝ) := by
      rw [lt_div_iff₀ hnR] at hloRatio
      linarith
    have hhiReal : (m : ℝ) < 2 * (n : ℝ) := by
      rw [div_lt_iff₀ hnR] at hhiRatio
      exact hhiRatio
    exact ⟨by exact_mod_cast hloReal, by exact_mod_cast hhiReal⟩
  · rintro ⟨hlo, hhi⟩
    have hloReal : (n : ℝ) < 2 * (m : ℝ) := by exact_mod_cast hlo
    have hhiReal : (m : ℝ) < 2 * (n : ℝ) := by exact_mod_cast hhi
    have hloRatio : (1 / 2 : ℝ) < (m : ℝ) / (n : ℝ) := by
      rw [lt_div_iff₀ hnR]
      linarith
    have hhiRatio : (m : ℝ) / (n : ℝ) < 2 := by
      rw [div_lt_iff₀ hnR]
      exact hhiReal
    have hloLog : -Real.log 2 < Real.log ((m : ℝ) / (n : ℝ)) := by
      rw [← hlogHalf]
      exact Real.log_lt_log hhalfPos hloRatio
    have hhiLog : Real.log ((m : ℝ) / (n : ℝ)) < Real.log 2 :=
      Real.log_lt_log hratioPos hhiRatio
    have habs : |Real.log ((m : ℝ) / (n : ℝ))| < Real.log 2 :=
      abs_lt.mpr ⟨hloLog, hhiLog⟩
    linarith

theorem exists_prime_straddling_multiplicativeAnnulus
    {n : ℕ} (hn : 4 ≤ n) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧
      n < 2 * p ∧ p < n ∧ n < q ∧ q < 2 * n := by
  have hhalf0 : n / 2 ≠ 0 := by omega
  obtain ⟨p, hpPrime, hhalfP, hpUpper⟩ :=
    Nat.exists_prime_lt_and_le_two_mul (n / 2) hhalf0
  have hpnLe : p ≤ n := by omega
  have hpnNe : p ≠ n := by
    intro hpn
    have hpEven : Even p := by
      refine ⟨n / 2, ?_⟩
      omega
    have hpTwo : p = 2 := hpPrime.even_iff.mp hpEven
    omega
  have hpn : p < n := lt_of_le_of_ne hpnLe hpnNe
  have hn0 : n ≠ 0 := by omega
  obtain ⟨q, hqPrime, hnq, hqUpper⟩ :=
    Nat.exists_prime_lt_and_le_two_mul n hn0
  have hqNe : q ≠ 2 * n := by
    intro hq
    have hqEven : Even q := by
      refine ⟨n, ?_⟩
      omega
    have hqTwo : q = 2 := hqPrime.even_iff.mp hqEven
    omega
  have hqLt : q < 2 * n := lt_of_le_of_ne hqUpper hqNe
  exact ⟨p, q, hpPrime, hqPrime, by omega, hpn, hnq, hqLt⟩

theorem mangoldtLogHaarNode_injective_of_two_le
    {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n)
    (hnode : mangoldtLogHaarNode m = mangoldtLogHaarNode n) :
    m = n := by
  have hmPos : (0 : ℝ) < m := by positivity
  have hnPos : (0 : ℝ) < n := by positivity
  simp only [mangoldtLogHaarNode] at hnode
  have hlog : Real.log (m : ℝ) = Real.log (n : ℝ) := by linarith
  have hcast : (m : ℝ) = (n : ℝ) :=
    Real.strictMonoOn_log.injOn hmPos hnPos hlog
  exact_mod_cast hcast

theorem suzukiMangoldtAlignedApex_sample_lt_self_of_ne
    {n m : ℕ} (hn : 4 ≤ n) (hm : 2 ≤ m) (hmn : m ≠ n) :
    suzukiRectangularPositiveArchSampleChannel (Real.log 2)
        (suzukiMangoldtApexAperture n) (mangoldtLogHaarNode m) <
      suzukiRectangularPositiveArchSampleChannel (Real.log 2)
        (suzukiMangoldtApexAperture n) (mangoldtLogHaarNode n) := by
  apply lt_of_not_ge
  intro hge
  have hmNodePos : 0 < mangoldtLogHaarNode m := by
    rw [mangoldtLogHaarNode]
    have : (1 : ℝ) < m := by exact_mod_cast hm
    have : 0 < Real.log (m : ℝ) := Real.log_pos this
    linarith
  have hnodeEq :=
    (suzukiMangoldtApex_unique_positiveLag_maximizer hn hmNodePos).mp hge
  exact hmn (mangoldtLogHaarNode_injective_of_two_le hm (by omega) hnodeEq)

theorem mangoldtLogHaarAtomMass_le_lowerPrimeFlank
    {n p : ℕ} (hn : 4 ≤ n) (hpPrime : p.Prime)
    (hnp : n < 2 * p) (hpn : p < n) :
    mangoldtLogHaarAtomMass n ≤ mangoldtLogHaarAtomMass p := by
  have hpThree : 3 ≤ p := by
    have hpTwo := hpPrime.two_le
    by_contra h
    have hpEq : p = 2 := by omega
    subst p
    omega
  have hpExp : Real.exp 1 ≤ (p : ℝ) :=
    (Real.exp_one_lt_three.trans_le (by exact_mod_cast hpThree)).le
  have hnExp : Real.exp 1 ≤ (n : ℝ) :=
    hpExp.trans (by exact_mod_cast hpn.le)
  have hratio : Real.log (n : ℝ) / (n : ℝ) ≤
      Real.log (p : ℝ) / (p : ℝ) :=
    Real.log_div_self_antitoneOn hpExp hnExp (by exact_mod_cast hpn.le)
  have hnPos : (0 : ℝ) < n := by positivity
  rw [mangoldtLogHaarAtomMass, mangoldtLogHaarAtomMass,
    ArithmeticFunction.vonMangoldt_apply_prime hpPrime]
  calc
    2 * ArithmeticFunction.vonMangoldt n / (n : ℝ) ≤
        2 * Real.log (n : ℝ) / (n : ℝ) := by
      exact (div_le_div_iff_of_pos_right hnPos).mpr
        (mul_le_mul_of_nonneg_left ArithmeticFunction.vonMangoldt_le_log (by norm_num))
    _ = 2 * (Real.log (n : ℝ) / (n : ℝ)) := by ring
    _ ≤ 2 * (Real.log (p : ℝ) / (p : ℝ)) :=
      mul_le_mul_of_nonneg_left hratio (by norm_num)
    _ = 2 * Real.log (p : ℝ) / (p : ℝ) := by ring

theorem mangoldtLogHaarAtomMass_lt_twice_upperPrimeFlank
    {n q : ℕ} (hn : 4 ≤ n) (hqPrime : q.Prime)
    (hnq : n < q) (hqn : q < 2 * n) :
    mangoldtLogHaarAtomMass n < 2 * mangoldtLogHaarAtomMass q := by
  have hnPos : (0 : ℝ) < n := by positivity
  have hqPos : (0 : ℝ) < q := by exact_mod_cast hqPrime.pos
  have hlognPos : 0 < Real.log (n : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have hlogLt : Real.log (n : ℝ) < Real.log (q : ℝ) :=
    Real.strictMonoOn_log hnPos hqPos (by exact_mod_cast hnq)
  have hqnR : (q : ℝ) < 2 * (n : ℝ) := by exact_mod_cast hqn
  have hcross : Real.log (n : ℝ) * (q : ℝ) <
      (2 * Real.log (q : ℝ)) * (n : ℝ) := by
    have hfirst : Real.log (n : ℝ) * (q : ℝ) <
        Real.log (n : ℝ) * (2 * (n : ℝ)) :=
      mul_lt_mul_of_pos_left hqnR hlognPos
    have hsecond : Real.log (n : ℝ) * (2 * (n : ℝ)) <
        Real.log (q : ℝ) * (2 * (n : ℝ)) :=
      mul_lt_mul_of_pos_right hlogLt (by positivity)
    nlinarith
  have hratio : Real.log (n : ℝ) / (n : ℝ) <
      (2 * Real.log (q : ℝ)) / (q : ℝ) :=
    (div_lt_div_iff₀ hnPos hqPos).mpr hcross
  rw [mangoldtLogHaarAtomMass, mangoldtLogHaarAtomMass,
    ArithmeticFunction.vonMangoldt_apply_prime hqPrime]
  calc
    2 * ArithmeticFunction.vonMangoldt n / (n : ℝ) ≤
        2 * Real.log (n : ℝ) / (n : ℝ) := by
      exact (div_le_div_iff_of_pos_right hnPos).mpr
        (mul_le_mul_of_nonneg_left ArithmeticFunction.vonMangoldt_le_log (by norm_num))
    _ = 2 * (Real.log (n : ℝ) / (n : ℝ)) := by ring
    _ < 2 * ((2 * Real.log (q : ℝ)) / (q : ℝ)) :=
      mul_lt_mul_of_pos_left hratio (by norm_num)
    _ = 2 * (2 * Real.log (q : ℝ) / (q : ℝ)) := by ring

theorem exists_suzukiMangoldtCrossPrimeFlankSurplus
    {n : ℕ} (hn : 4 ≤ n) :
    ∃ p q : ℕ,
      p.Prime ∧ q.Prime ∧
      n < 2 * p ∧ p < n ∧ n < q ∧ q < 2 * n ∧
      0 < suzukiRectangularPositiveArchSampleChannel (Real.log 2)
        (suzukiMangoldtApexAperture n) (mangoldtLogHaarNode p) ∧
      0 < suzukiRectangularPositiveArchSampleChannel (Real.log 2)
        (suzukiMangoldtApexAperture n) (mangoldtLogHaarNode q) ∧
      0 < mangoldtLogHaarAtomMass p ∧
      0 < mangoldtLogHaarAtomMass q ∧
      0 < mangoldtLogHaarAtomMass p *
          (suzukiRectangularPositiveArchSampleChannel (Real.log 2)
              (suzukiMangoldtApexAperture n) (mangoldtLogHaarNode n) -
            suzukiRectangularPositiveArchSampleChannel (Real.log 2)
              (suzukiMangoldtApexAperture n) (mangoldtLogHaarNode p)) +
        mangoldtLogHaarAtomMass q *
          (suzukiRectangularPositiveArchSampleChannel (Real.log 2)
              (suzukiMangoldtApexAperture n) (mangoldtLogHaarNode n) -
            suzukiRectangularPositiveArchSampleChannel (Real.log 2)
              (suzukiMangoldtApexAperture n) (mangoldtLogHaarNode q)) := by
  obtain ⟨p, q, hpPrime, hqPrime, hnp, hpn, hnq, hqn⟩ :=
    exists_prime_straddling_multiplicativeAnnulus hn
  have hpTwo : 2 ≤ p := hpPrime.two_le
  have hqTwo : 2 ≤ q := hqPrime.two_le
  have hpSample : 0 < suzukiRectangularPositiveArchSampleChannel (Real.log 2)
      (suzukiMangoldtApexAperture n) (mangoldtLogHaarNode p) :=
    (suzukiMangoldtAlignedApex_sample_pos_iff_openAnnulus (by omega) hpTwo).mpr ⟨hnp, by omega⟩
  have hqSample : 0 < suzukiRectangularPositiveArchSampleChannel (Real.log 2)
      (suzukiMangoldtApexAperture n) (mangoldtLogHaarNode q) :=
    (suzukiMangoldtAlignedApex_sample_pos_iff_openAnnulus (by omega) hqTwo).mpr ⟨by omega, hqn⟩
  have hpMass : 0 < mangoldtLogHaarAtomMass p :=
    mangoldtLogHaarAtomMass_pos_of_vonMangoldt_pos hpPrime.pos
      (ArithmeticFunction.vonMangoldt_pos_iff.mpr hpPrime.prime.isPrimePow)
  have hqMass : 0 < mangoldtLogHaarAtomMass q :=
    mangoldtLogHaarAtomMass_pos_of_vonMangoldt_pos hqPrime.pos
      (ArithmeticFunction.vonMangoldt_pos_iff.mpr hqPrime.prime.isPrimePow)
  have hpDeficit : 0 <
      suzukiRectangularPositiveArchSampleChannel (Real.log 2)
          (suzukiMangoldtApexAperture n) (mangoldtLogHaarNode n) -
        suzukiRectangularPositiveArchSampleChannel (Real.log 2)
          (suzukiMangoldtApexAperture n) (mangoldtLogHaarNode p) :=
    sub_pos.mpr (suzukiMangoldtAlignedApex_sample_lt_self_of_ne hn hpTwo (by omega))
  have hqDeficit : 0 <
      suzukiRectangularPositiveArchSampleChannel (Real.log 2)
          (suzukiMangoldtApexAperture n) (mangoldtLogHaarNode n) -
        suzukiRectangularPositiveArchSampleChannel (Real.log 2)
          (suzukiMangoldtApexAperture n) (mangoldtLogHaarNode q) :=
    sub_pos.mpr (suzukiMangoldtAlignedApex_sample_lt_self_of_ne hn hqTwo (by omega))
  refine ⟨p, q, hpPrime, hqPrime, hnp, hpn, hnq, hqn,
    hpSample, hqSample, hpMass, hqMass, ?_⟩
  exact add_pos (mul_pos hpMass hpDeficit) (mul_pos hqMass hqDeficit)

theorem exists_suzukiMangoldtCrossPrimeThreeAtomBlockDilution
    {n : ℕ} (hn : 4 ≤ n) :
    ∃ p q : ℕ,
      p.Prime ∧ q.Prime ∧
      n < 2 * p ∧ p < n ∧ n < q ∧ q < 2 * n ∧
      mangoldtLogHaarAtomMass n ≤ mangoldtLogHaarAtomMass p ∧
      mangoldtLogHaarAtomMass n < 2 * mangoldtLogHaarAtomMass q ∧
      5 * mangoldtLogHaarAtomMass n <
        2 * (mangoldtLogHaarAtomMass n + mangoldtLogHaarAtomMass p +
          mangoldtLogHaarAtomMass q) ∧
      mangoldtLogHaarAtomMass n *
            suzukiRectangularPositiveArchSampleChannel (Real.log 2)
              (suzukiMangoldtApexAperture n) (mangoldtLogHaarNode n) +
          mangoldtLogHaarAtomMass p *
            suzukiRectangularPositiveArchSampleChannel (Real.log 2)
              (suzukiMangoldtApexAperture n) (mangoldtLogHaarNode p) +
          mangoldtLogHaarAtomMass q *
            suzukiRectangularPositiveArchSampleChannel (Real.log 2)
              (suzukiMangoldtApexAperture n) (mangoldtLogHaarNode q) <
        (mangoldtLogHaarAtomMass n + mangoldtLogHaarAtomMass p +
          mangoldtLogHaarAtomMass q) *
            suzukiRectangularPositiveArchSampleChannel (Real.log 2)
              (suzukiMangoldtApexAperture n) (mangoldtLogHaarNode n) := by
  obtain ⟨p, q, hpPrime, hqPrime, hnp, hpn, hnq, hqn⟩ :=
    exists_prime_straddling_multiplicativeAnnulus hn
  have hpMassCmp := mangoldtLogHaarAtomMass_le_lowerPrimeFlank hn hpPrime hnp hpn
  have hqMassCmp := mangoldtLogHaarAtomMass_lt_twice_upperPrimeFlank hn hqPrime hnq hqn
  have hmassDilution : 5 * mangoldtLogHaarAtomMass n <
      2 * (mangoldtLogHaarAtomMass n + mangoldtLogHaarAtomMass p +
        mangoldtLogHaarAtomMass q) := by
    nlinarith
  have hpMass : 0 < mangoldtLogHaarAtomMass p :=
    mangoldtLogHaarAtomMass_pos_of_vonMangoldt_pos hpPrime.pos
      (ArithmeticFunction.vonMangoldt_pos_iff.mpr hpPrime.prime.isPrimePow)
  have hqMass : 0 < mangoldtLogHaarAtomMass q :=
    mangoldtLogHaarAtomMass_pos_of_vonMangoldt_pos hqPrime.pos
      (ArithmeticFunction.vonMangoldt_pos_iff.mpr hqPrime.prime.isPrimePow)
  have hpLt := suzukiMangoldtAlignedApex_sample_lt_self_of_ne hn hpPrime.two_le (by omega : p ≠ n)
  have hqLt := suzukiMangoldtAlignedApex_sample_lt_self_of_ne hn hqPrime.two_le (by omega : q ≠ n)
  have hpGain : 0 < mangoldtLogHaarAtomMass p *
      (suzukiRectangularPositiveArchSampleChannel (Real.log 2)
          (suzukiMangoldtApexAperture n) (mangoldtLogHaarNode n) -
        suzukiRectangularPositiveArchSampleChannel (Real.log 2)
          (suzukiMangoldtApexAperture n) (mangoldtLogHaarNode p)) :=
    mul_pos hpMass (sub_pos.mpr hpLt)
  have hqGain : 0 < mangoldtLogHaarAtomMass q *
      (suzukiRectangularPositiveArchSampleChannel (Real.log 2)
          (suzukiMangoldtApexAperture n) (mangoldtLogHaarNode n) -
        suzukiRectangularPositiveArchSampleChannel (Real.log 2)
          (suzukiMangoldtApexAperture n) (mangoldtLogHaarNode q)) :=
    mul_pos hqMass (sub_pos.mpr hqLt)
  refine ⟨p, q, hpPrime, hqPrime, hnp, hpn, hnq, hqn,
    hpMassCmp, hqMassCmp, hmassDilution, ?_⟩
  nlinarith

theorem exists_dyadic_far_suzukiMangoldtFlank
    {n : ℕ} (hn : 2 ≤ n) :
    ∃ m : ℕ,
      2 ≤ m ∧ n < 2 * m ∧ m ≤ 2 * n ∧ m ≠ n ∧
      IsPrimePow m ∧
      Real.log 2 / 2 ≤ |Real.log ((m : ℝ) / (n : ℝ))| := by
  let k := Nat.log 2 n
  let lo := 2 ^ k
  let hi := 2 ^ (k + 1)
  have hn0 : n ≠ 0 := by omega
  have hkPos : 0 < k := by
    exact Nat.log_pos (by omega) hn
  have hloTwo : 2 ≤ lo := by
    dsimp [lo]
    have := Nat.pow_le_pow_right (by omega : 0 < 2) (show 1 ≤ k by omega)
    simpa using this
  have hloLe : lo ≤ n := by
    exact Nat.pow_log_le_self 2 hn0
  have hnHi : n < hi := by
    exact Nat.lt_pow_succ_log_self (by omega) n
  have hhiEq : hi = 2 * lo := by
    dsimp [hi, lo]
    rw [pow_succ']
  have hnTwoLo : n < 2 * lo := by rwa [← hhiEq]
  have hhiTwo : 2 ≤ hi := hloTwo.trans (by omega)
  have hhiLe : hi ≤ 2 * n := by omega
  have hnTwoHi : n < 2 * hi := by omega
  have hnR : (0 : ℝ) < n := by positivity
  have hloR : (0 : ℝ) < lo := by positivity
  have hhiR : (0 : ℝ) < hi := by positivity
  have hlogLo : Real.log (lo : ℝ) = (k : ℝ) * Real.log 2 := by
    dsimp [lo]
    push_cast
    rw [Real.log_pow]
  have hlogHi : Real.log (hi : ℝ) = ((k : ℝ) + 1) * Real.log 2 := by
    dsimp [hi]
    push_cast
    rw [Real.log_pow]
    push_cast
    rfl
  have hlogLoRatio : Real.log ((lo : ℝ) / (n : ℝ)) =
      (k : ℝ) * Real.log 2 - Real.log n := by
    rw [Real.log_div hloR.ne' hnR.ne', hlogLo]
  have hlogHiRatio : Real.log ((hi : ℝ) / (n : ℝ)) =
      ((k : ℝ) + 1) * Real.log 2 - Real.log n := by
    rw [Real.log_div hhiR.ne' hnR.ne', hlogHi]
  have hlogLoNonpos : Real.log ((lo : ℝ) / (n : ℝ)) ≤ 0 := by
    have : (lo : ℝ) / (n : ℝ) ≤ 1 := by
      rw [div_le_one hnR]
      exact_mod_cast hloLe
    exact Real.log_nonpos (by positivity) this
  have hlogHiPos : 0 < Real.log ((hi : ℝ) / (n : ℝ)) := by
    apply Real.log_pos
    rw [one_lt_div hnR]
    exact_mod_cast hnHi
  have hsum : |Real.log ((lo : ℝ) / (n : ℝ))| +
      |Real.log ((hi : ℝ) / (n : ℝ))| = Real.log 2 := by
    rw [abs_of_nonpos hlogLoNonpos, abs_of_pos hlogHiPos,
      hlogLoRatio, hlogHiRatio]
    ring
  by_cases hfar : Real.log 2 / 2 ≤
      |Real.log ((lo : ℝ) / (n : ℝ))|
  · refine ⟨lo, hloTwo, hnTwoLo, hloLe.trans (by omega), ?_, ?_, hfar⟩
    · intro hEq
      have hzero : Real.log ((lo : ℝ) / (n : ℝ)) = 0 := by
        rw [hEq, div_self (by positivity), Real.log_one]
      rw [hzero, abs_zero] at hfar
      have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
      linarith
    · exact Nat.prime_two.isPrimePow.pow (by omega)
  · refine ⟨hi, hhiTwo, hnTwoHi, hhiLe, ?_, ?_, ?_⟩
    · exact ne_of_gt hnHi
    · exact Nat.prime_two.isPrimePow.pow (by omega)
    · linarith

/-- Exact continuous minimax contraction for the dyadic Suzuki bracket. -/
def suzukiMangoldtDyadicSharpContraction : ℝ :=
  tiltedTentSharpContraction (1 / 2 : ℝ) (Real.log 2)

lemma suzukiMangoldt_exp_log_div_two_eq_sqrt {x : ℝ} (hx : 0 < x) :
    Real.exp (Real.log x / 2) = Real.sqrt x := by
  rw [← Real.log_sqrt hx.le, Real.exp_log (Real.sqrt_pos.mpr hx)]

lemma suzukiMangoldt_dyadic_balance_closedForm :
    tiltedTentBalance (1 / 2 : ℝ) (Real.log 2) = Real.sqrt 2 - 1 := by
  have hsqrtSq := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hsqrtNonneg := Real.sqrt_nonneg (2 : ℝ)
  rw [tiltedTentBalance, show (1 / 2 : ℝ) * Real.log 2 = Real.log 2 / 2 by ring,
    suzukiMangoldt_exp_log_div_two_eq_sqrt (by norm_num : (0 : ℝ) < 2)]
  have hdenom : 1 + Real.sqrt 2 ≠ 0 := by positivity
  field_simp
  nlinarith

theorem suzukiMangoldtDyadicSharpContraction_closedForm :
    suzukiMangoldtDyadicSharpContraction =
      Real.exp (-((Real.sqrt 2 - 1) * Real.log 2) / 2) * (2 - Real.sqrt 2) := by
  rw [suzukiMangoldtDyadicSharpContraction, tiltedTentSharpContraction,
    suzukiMangoldt_dyadic_balance_closedForm]
  congr 1 <;> ring

theorem suzukiMangoldtDyadicSharpContraction_mem_Ioo :
    suzukiMangoldtDyadicSharpContraction ∈ Set.Ioo (0 : ℝ) 1 := by
  exact tiltedTentSharpContraction_mem_Ioo
    (Real.log_pos (by norm_num : (1 : ℝ) < 2)) (by norm_num)

theorem suzukiMangoldtDyadicSharpContraction_lt_sqrtTwo_div_two :
    suzukiMangoldtDyadicSharpContraction < Real.sqrt 2 / 2 := by
  have hsqrtSq := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hsqrtNonneg := Real.sqrt_nonneg (2 : ℝ)
  have hsqrtOne : 1 < Real.sqrt 2 := by nlinarith
  have hsqrtTwo : Real.sqrt 2 < 2 := by nlinarith
  have hlogPos : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hargNeg : -((Real.sqrt 2 - 1) * Real.log 2) / 2 < 0 := by
    have hprodPos : 0 < (Real.sqrt 2 - 1) * Real.log 2 :=
      mul_pos (sub_pos.mpr hsqrtOne) hlogPos
    linarith
  have hexpLt : Real.exp (-((Real.sqrt 2 - 1) * Real.log 2) / 2) < 1 := by
    calc
      Real.exp (-((Real.sqrt 2 - 1) * Real.log 2) / 2) < Real.exp 0 :=
        Real.exp_lt_exp.mpr hargNeg
      _ = 1 := Real.exp_zero
  have hfactorPos : 0 < 2 - Real.sqrt 2 := by linarith
  have hfactorLt : 2 - Real.sqrt 2 < Real.sqrt 2 / 2 := by nlinarith
  rw [suzukiMangoldtDyadicSharpContraction_closedForm]
  calc
    Real.exp (-((Real.sqrt 2 - 1) * Real.log 2) / 2) * (2 - Real.sqrt 2) <
        1 * (2 - Real.sqrt 2) := mul_lt_mul_of_pos_right hexpLt hfactorPos
    _ < Real.sqrt 2 / 2 := by simpa using hfactorLt

/-- Every aligned Suzuki--Mangoldt apex has a positive-mass dyadic flank whose sample is
bounded by the exact geometric-bracket minimax factor. -/
theorem exists_dyadic_sharp_suzukiMangoldtFlankDilution
    {n : ℕ} (hn : 2 ≤ n) :
    ∃ m : ℕ,
      2 ≤ m ∧ n < 2 * m ∧ m ≤ 2 * n ∧ m ≠ n ∧
      IsPrimePow m ∧ 0 < mangoldtLogHaarAtomMass m ∧
      Real.log 2 / (n : ℝ) ≤ mangoldtLogHaarAtomMass m ∧
      suzukiRectangularPositiveArchSampleChannel (Real.log 2)
          (suzukiMangoldtApexAperture n) (mangoldtLogHaarNode m) ≤
        suzukiMangoldtDyadicSharpContraction *
          suzukiRectangularPositiveArchSampleChannel (Real.log 2)
            (suzukiMangoldtApexAperture n) (mangoldtLogHaarNode n) := by
  let k := Nat.log 2 n
  let lo := 2 ^ k
  let hi := 2 ^ (k + 1)
  let d := Real.log ((n : ℝ) / (lo : ℝ))
  have hn0 : n ≠ 0 := by omega
  have hkPos : 0 < k := Nat.log_pos (by omega) hn
  have hloTwo : 2 ≤ lo := by
    dsimp [lo]
    have := Nat.pow_le_pow_right (by omega : 0 < 2) (show 1 ≤ k by omega)
    simpa using this
  have hloLe : lo ≤ n := Nat.pow_log_le_self 2 hn0
  have hnHi : n < hi := Nat.lt_pow_succ_log_self (by omega) n
  have hhiEq : hi = 2 * lo := by
    dsimp [hi, lo]
    rw [pow_succ']
  have hnTwoLo : n < 2 * lo := by rwa [← hhiEq]
  have hhiTwo : 2 ≤ hi := hloTwo.trans (by omega)
  have hhiLe : hi ≤ 2 * n := by omega
  have hnTwoHi : n < 2 * hi := by omega
  have hnR : (0 : ℝ) < n := by positivity
  have hloR : (0 : ℝ) < lo := by positivity
  have hhiR : (0 : ℝ) < hi := by positivity
  have hlogPos : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlogNe : Real.log (2 : ℝ) ≠ 0 := hlogPos.ne'
  have hlogHi : Real.log (hi : ℝ) = Real.log 2 + Real.log lo := by
    rw [hhiEq]
    push_cast
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hloR.ne']
  have hdEq : d = Real.log (n : ℝ) - Real.log (lo : ℝ) := by
    dsimp [d]
    rw [Real.log_div hnR.ne' hloR.ne']
  have hdNonneg : 0 ≤ d := by
    rw [hdEq, sub_nonneg]
    exact Real.log_le_log hloR (by exact_mod_cast hloLe)
  have hdLt : d < Real.log 2 := by
    have hratio : (n : ℝ) / (lo : ℝ) < 2 := by
      rw [div_lt_iff₀ hloR]
      exact_mod_cast hnTwoLo
    dsimp [d]
    exact Real.log_lt_log (div_pos hnR hloR) hratio
  have hdMem : d ∈ Set.Icc (0 : ℝ) (Real.log 2) := ⟨hdNonneg, hdLt.le⟩
  have hself :
      suzukiRectangularPositiveArchSampleChannel (Real.log 2)
          (suzukiMangoldtApexAperture n) (mangoldtLogHaarNode n) =
        Real.sqrt n * Real.log 2 := by
    rw [suzukiMangoldtAlignedApex_sample_eq hn hn]
    rw [div_self hnR.ne', Real.log_one, abs_zero, sub_zero,
      max_eq_right hlogPos.le]
  have hsqrtLo : Real.sqrt (lo : ℝ) =
      Real.sqrt (n : ℝ) * Real.exp (-d / 2) := by
    rw [← suzukiMangoldt_exp_log_div_two_eq_sqrt hnR,
      ← suzukiMangoldt_exp_log_div_two_eq_sqrt hloR]
    rw [← Real.exp_add]
    congr 1
    rw [hdEq]
    ring
  have hsqrtHi : Real.sqrt (hi : ℝ) =
      Real.sqrt (n : ℝ) * Real.exp ((Real.log 2 - d) / 2) := by
    rw [← suzukiMangoldt_exp_log_div_two_eq_sqrt hnR,
      ← suzukiMangoldt_exp_log_div_two_eq_sqrt hhiR]
    rw [← Real.exp_add]
    congr 1
    rw [hlogHi, hdEq]
    ring
  have hlogLoRatio : Real.log ((lo : ℝ) / (n : ℝ)) = -d := by
    rw [Real.log_div hloR.ne' hnR.ne', hdEq]
    ring
  have hlogHiRatio : Real.log ((hi : ℝ) / (n : ℝ)) = Real.log 2 - d := by
    rw [Real.log_div hhiR.ne' hnR.ne', hlogHi, hdEq]
    ring
  have hloSample :
      suzukiRectangularPositiveArchSampleChannel (Real.log 2)
          (suzukiMangoldtApexAperture n) (mangoldtLogHaarNode lo) =
        (Real.sqrt n * Real.log 2) *
          tiltedTentLowerProfile (1 / 2 : ℝ) (Real.log 2) d := by
    rw [suzukiMangoldtAlignedApex_sample_eq hn hloTwo,
      hlogLoRatio, abs_neg, abs_of_nonneg hdNonneg,
      max_eq_right (sub_nonneg.mpr hdMem.2), hsqrtLo,
      tiltedTentLowerProfile]
    field_simp [hlogNe]
  have hhiSample :
      suzukiRectangularPositiveArchSampleChannel (Real.log 2)
          (suzukiMangoldtApexAperture n) (mangoldtLogHaarNode hi) =
        (Real.sqrt n * Real.log 2) *
          tiltedTentUpperProfile (1 / 2 : ℝ) (Real.log 2) d := by
    have hdistNonneg : 0 ≤ Real.log 2 - d := sub_nonneg.mpr hdMem.2
    rw [suzukiMangoldtAlignedApex_sample_eq hn hhiTwo,
      hlogHiRatio, abs_of_nonneg hdistNonneg,
      show Real.log 2 - (Real.log 2 - d) = d by ring,
      max_eq_right hdNonneg, hsqrtHi, tiltedTentUpperProfile]
    field_simp [hlogNe]
  have hmin := tiltedTent_geometricBracket_minimax hlogPos
    (by norm_num : (0 : ℝ) ≤ 1 / 2) hdMem
  have hselfNonneg : 0 ≤ Real.sqrt (n : ℝ) * Real.log 2 := by positivity
  by_cases hchoose : tiltedTentLowerProfile (1 / 2 : ℝ) (Real.log 2) d ≤
      tiltedTentUpperProfile (1 / 2 : ℝ) (Real.log 2) d
  · have hbound : tiltedTentLowerProfile (1 / 2 : ℝ) (Real.log 2) d ≤
        suzukiMangoldtDyadicSharpContraction := by
      rw [min_eq_left hchoose] at hmin
      exact hmin
    have hloNe : lo ≠ n := by
      intro hEq
      have hdZero : d = 0 := by
        dsimp [d]
        rw [hEq, div_self hnR.ne', Real.log_one]
      have hLowerOne : tiltedTentLowerProfile (1 / 2 : ℝ) (Real.log 2) d = 1 := by
        rw [hdZero, tiltedTentLowerProfile]
        norm_num
      have hUpperZero : tiltedTentUpperProfile (1 / 2 : ℝ) (Real.log 2) d = 0 := by
        rw [hdZero, tiltedTentUpperProfile]
        simp
      rw [hLowerOne, hUpperZero] at hchoose
      norm_num at hchoose
    have hloMass : 0 < mangoldtLogHaarAtomMass lo :=
      mangoldtLogHaarAtomMass_pos_of_vonMangoldt_pos (by omega)
        (ArithmeticFunction.vonMangoldt_pos_iff.mpr
          (Nat.prime_two.isPrimePow.pow (by omega)))
    have hloVM : ArithmeticFunction.vonMangoldt lo = Real.log 2 := by
      dsimp [lo]
      rw [ArithmeticFunction.vonMangoldt_apply_pow (by omega),
        ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
      norm_num
    have hloMassLower : Real.log 2 / (n : ℝ) ≤ mangoldtLogHaarAtomMass lo := by
      rw [mangoldtLogHaarAtomMass, hloVM]
      apply (div_le_div_iff₀ hnR hloR).mpr
      have hloLeR : (lo : ℝ) ≤ n := by exact_mod_cast hloLe
      nlinarith
    refine ⟨lo, hloTwo, hnTwoLo, hloLe.trans (by omega), hloNe,
      Nat.prime_two.isPrimePow.pow (by omega), hloMass, hloMassLower, ?_⟩
    rw [hloSample, hself]
    simpa [suzukiMangoldtDyadicSharpContraction, mul_comm] using
      mul_le_mul_of_nonneg_left hbound hselfNonneg
  · have hbound : tiltedTentUpperProfile (1 / 2 : ℝ) (Real.log 2) d ≤
        suzukiMangoldtDyadicSharpContraction := by
      rw [min_eq_right (le_of_not_ge hchoose)] at hmin
      exact hmin
    have hhiMass : 0 < mangoldtLogHaarAtomMass hi :=
      mangoldtLogHaarAtomMass_pos_of_vonMangoldt_pos (by omega)
        (ArithmeticFunction.vonMangoldt_pos_iff.mpr
          (Nat.prime_two.isPrimePow.pow (by omega)))
    have hhiVM : ArithmeticFunction.vonMangoldt hi = Real.log 2 := by
      dsimp [hi]
      rw [ArithmeticFunction.vonMangoldt_apply_pow (by omega),
        ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
      norm_num
    have hhiMassLower : Real.log 2 / (n : ℝ) ≤ mangoldtLogHaarAtomMass hi := by
      rw [mangoldtLogHaarAtomMass, hhiVM]
      apply (div_le_div_iff₀ hnR hhiR).mpr
      have hhiLeR : (hi : ℝ) ≤ 2 * n := by exact_mod_cast hhiLe
      nlinarith
    refine ⟨hi, hhiTwo, hnTwoHi, hhiLe, ne_of_gt hnHi,
      Nat.prime_two.isPrimePow.pow (by omega), hhiMass, hhiMassLower, ?_⟩
    rw [hhiSample, hself]
    simpa [suzukiMangoldtDyadicSharpContraction, mul_comm] using
      mul_le_mul_of_nonneg_left hbound hselfNonneg

theorem exists_dyadic_uniform_suzukiMangoldtFlankDilution
    {n : ℕ} (hn : 2 ≤ n) :
    ∃ m : ℕ,
      2 ≤ m ∧ n < 2 * m ∧ m ≤ 2 * n ∧ m ≠ n ∧
      IsPrimePow m ∧ 0 < mangoldtLogHaarAtomMass m ∧
      suzukiRectangularPositiveArchSampleChannel (Real.log 2)
          (suzukiMangoldtApexAperture n) (mangoldtLogHaarNode m) ≤
        (Real.sqrt 2 / 2) *
          suzukiRectangularPositiveArchSampleChannel (Real.log 2)
            (suzukiMangoldtApexAperture n) (mangoldtLogHaarNode n) := by
  obtain ⟨m, hmTwo, hnm, hmn, hmNe, hmPow, hmFar⟩ :=
    exists_dyadic_far_suzukiMangoldtFlank hn
  have hnR : (0 : ℝ) < n := by positivity
  have hmR : (0 : ℝ) < m := by positivity
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hmMass : 0 < mangoldtLogHaarAtomMass m :=
    mangoldtLogHaarAtomMass_pos_of_vonMangoldt_pos (by omega)
      (ArithmeticFunction.vonMangoldt_pos_iff.mpr hmPow)
  have hself :
      suzukiRectangularPositiveArchSampleChannel (Real.log 2)
          (suzukiMangoldtApexAperture n) (mangoldtLogHaarNode n) =
        Real.sqrt n * Real.log 2 := by
    rw [suzukiMangoldtAlignedApex_sample_eq hn hn]
    rw [div_self hnR.ne', Real.log_one, abs_zero, sub_zero,
      max_eq_right hlogTwo.le]
  have hheight : max 0
      (Real.log 2 - |Real.log ((m : ℝ) / (n : ℝ))|) ≤ Real.log 2 / 2 := by
    apply max_le
    · linarith
    · linarith
  have hmLeR : (m : ℝ) ≤ 2 * (n : ℝ) := by exact_mod_cast hmn
  have hsqrtLe : Real.sqrt (m : ℝ) ≤ Real.sqrt (2 * (n : ℝ)) :=
    Real.sqrt_le_sqrt hmLeR
  have hhalfNonneg : 0 ≤ Real.log 2 / 2 := by positivity
  refine ⟨m, hmTwo, hnm, hmn, hmNe, hmPow, hmMass, ?_⟩
  rw [suzukiMangoldtAlignedApex_sample_eq hn hmTwo, hself]
  calc
    Real.sqrt (m : ℝ) *
        max 0 (Real.log 2 - |Real.log ((m : ℝ) / (n : ℝ))|) ≤
      Real.sqrt (m : ℝ) * (Real.log 2 / 2) :=
        mul_le_mul_of_nonneg_left hheight (Real.sqrt_nonneg _)
    _ ≤ Real.sqrt (2 * (n : ℝ)) * (Real.log 2 / 2) :=
      mul_le_mul_of_nonneg_right hsqrtLe hhalfNonneg
    _ = (Real.sqrt 2 / 2) * (Real.sqrt (n : ℝ) * Real.log 2) := by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
      ring

theorem sqrtTwo_div_two_lt_one : Real.sqrt 2 / 2 < (1 : ℝ) := by
  have hsqrt : Real.sqrt 2 < 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
  linarith


def suzukiMangoldtAlignedFlankSurplus (n m : ℕ) : ℝ :=
  mangoldtLogHaarAtomMass m *
    (suzukiRectangularPositiveArchSampleChannel (Real.log 2)
        (suzukiMangoldtApexAperture n) (mangoldtLogHaarNode n) -
      suzukiRectangularPositiveArchSampleChannel (Real.log 2)
        (suzukiMangoldtApexAperture n) (mangoldtLogHaarNode m))

/-- Exact quantitative source surplus forced by the sharp dyadic minimax law. -/
theorem exists_dyadic_sharp_quantitative_suzukiMangoldtFlankSurplus
    {n : ℕ} (hn : 2 ≤ n) :
    ∃ m : ℕ,
      2 ≤ m ∧ n < 2 * m ∧ m ≤ 2 * n ∧ m ≠ n ∧
      IsPrimePow m ∧
      0 < (1 - suzukiMangoldtDyadicSharpContraction) * mangoldtLogHaarAtomMass m *
        suzukiRectangularPositiveArchSampleChannel (Real.log 2)
          (suzukiMangoldtApexAperture n) (mangoldtLogHaarNode n) ∧
      (1 - suzukiMangoldtDyadicSharpContraction) * mangoldtLogHaarAtomMass m *
          suzukiRectangularPositiveArchSampleChannel (Real.log 2)
            (suzukiMangoldtApexAperture n) (mangoldtLogHaarNode n) ≤
        suzukiMangoldtAlignedFlankSurplus n m := by
  obtain ⟨m, hmTwo, hnm, hmn, hmNe, hmPow, hmMass, _hmMassLower, hmSample⟩ :=
    exists_dyadic_sharp_suzukiMangoldtFlankDilution hn
  have hcPos : 0 < 1 - suzukiMangoldtDyadicSharpContraction :=
    sub_pos.mpr suzukiMangoldtDyadicSharpContraction_mem_Ioo.2
  have hselfPos := suzukiMangoldtAlignedApex_self_pos hn
  refine ⟨m, hmTwo, hnm, hmn, hmNe, hmPow,
    mul_pos (mul_pos hcPos hmMass) hselfPos, ?_⟩
  rw [suzukiMangoldtAlignedFlankSurplus]
  have hweighted := mul_le_mul_of_nonneg_left hmSample hmMass.le
  nlinarith

lemma suzukiMangoldt_logTwo_div_mul_alignedApex_eq
    {n : ℕ} (hn : 2 ≤ n) :
    (Real.log 2 / (n : ℝ)) *
        suzukiRectangularPositiveArchSampleChannel (Real.log 2)
          (suzukiMangoldtApexAperture n) (mangoldtLogHaarNode n) =
      (Real.log 2) ^ 2 / Real.sqrt n := by
  have hnR : (0 : ℝ) < n := by positivity
  have hsqrtPos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnR
  have hlogPos : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  rw [suzukiMangoldtAlignedApex_sample_eq hn hn]
  rw [div_self hnR.ne', Real.log_one, abs_zero, sub_zero,
    max_eq_right hlogPos.le]
  field_simp [hnR.ne', hsqrtPos.ne']
  nlinarith [Real.sq_sqrt hnR.le]

/-- Prime-gap-free absolute surplus law. The dyadic source surplus is bounded below solely in
terms of the apex scale, with the exact minimax coefficient. -/
theorem exists_dyadic_absolute_suzukiMangoldtFlankSurplus
    {n : ℕ} (hn : 2 ≤ n) :
    ∃ m : ℕ,
      2 ≤ m ∧ n < 2 * m ∧ m ≤ 2 * n ∧ m ≠ n ∧
      IsPrimePow m ∧
      0 < (1 - suzukiMangoldtDyadicSharpContraction) *
        (Real.log 2) ^ 2 / Real.sqrt n ∧
      (1 - suzukiMangoldtDyadicSharpContraction) *
          (Real.log 2) ^ 2 / Real.sqrt n ≤
        (1 - suzukiMangoldtDyadicSharpContraction) * mangoldtLogHaarAtomMass m *
          suzukiRectangularPositiveArchSampleChannel (Real.log 2)
            (suzukiMangoldtApexAperture n) (mangoldtLogHaarNode n) ∧
      (1 - suzukiMangoldtDyadicSharpContraction) * mangoldtLogHaarAtomMass m *
          suzukiRectangularPositiveArchSampleChannel (Real.log 2)
            (suzukiMangoldtApexAperture n) (mangoldtLogHaarNode n) ≤
        suzukiMangoldtAlignedFlankSurplus n m := by
  obtain ⟨m, hmTwo, hnm, hmn, hmNe, hmPow, hmMass, hmMassLower, hmSample⟩ :=
    exists_dyadic_sharp_suzukiMangoldtFlankDilution hn
  have hcPos : 0 < 1 - suzukiMangoldtDyadicSharpContraction :=
    sub_pos.mpr suzukiMangoldtDyadicSharpContraction_mem_Ioo.2
  have hselfPos := suzukiMangoldtAlignedApex_self_pos hn
  have hsqrtPos : 0 < Real.sqrt (n : ℝ) := by positivity
  have hlogPos : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have habsolutePos : 0 < (1 - suzukiMangoldtDyadicSharpContraction) *
      (Real.log 2) ^ 2 / Real.sqrt n := by positivity
  have hsurplusLower :
      (1 - suzukiMangoldtDyadicSharpContraction) * mangoldtLogHaarAtomMass m *
          suzukiRectangularPositiveArchSampleChannel (Real.log 2)
            (suzukiMangoldtApexAperture n) (mangoldtLogHaarNode n) ≤
        suzukiMangoldtAlignedFlankSurplus n m := by
    rw [suzukiMangoldtAlignedFlankSurplus]
    have hweighted := mul_le_mul_of_nonneg_left hmSample hmMass.le
    nlinarith
  have hmassScaled :
      (1 - suzukiMangoldtDyadicSharpContraction) * (Real.log 2 / (n : ℝ)) *
          suzukiRectangularPositiveArchSampleChannel (Real.log 2)
            (suzukiMangoldtApexAperture n) (mangoldtLogHaarNode n) ≤
        (1 - suzukiMangoldtDyadicSharpContraction) * mangoldtLogHaarAtomMass m *
          suzukiRectangularPositiveArchSampleChannel (Real.log 2)
            (suzukiMangoldtApexAperture n) (mangoldtLogHaarNode n) := by
    have hmassWeighted := mul_le_mul_of_nonneg_left hmMassLower hcPos.le
    exact mul_le_mul_of_nonneg_right hmassWeighted hselfPos.le
  have habsoluteLe :
      (1 - suzukiMangoldtDyadicSharpContraction) * (Real.log 2) ^ 2 / Real.sqrt n ≤
        (1 - suzukiMangoldtDyadicSharpContraction) * mangoldtLogHaarAtomMass m *
          suzukiRectangularPositiveArchSampleChannel (Real.log 2)
            (suzukiMangoldtApexAperture n) (mangoldtLogHaarNode n) := by
    calc
      (1 - suzukiMangoldtDyadicSharpContraction) * (Real.log 2) ^ 2 / Real.sqrt n =
          (1 - suzukiMangoldtDyadicSharpContraction) *
            ((Real.log 2) ^ 2 / Real.sqrt n) := by ring
      _ = (1 - suzukiMangoldtDyadicSharpContraction) *
          ((Real.log 2 / (n : ℝ)) *
            suzukiRectangularPositiveArchSampleChannel (Real.log 2)
              (suzukiMangoldtApexAperture n) (mangoldtLogHaarNode n)) := by
        rw [suzukiMangoldt_logTwo_div_mul_alignedApex_eq hn]
      _ =
        (1 - suzukiMangoldtDyadicSharpContraction) * (Real.log 2 / (n : ℝ)) *
          suzukiRectangularPositiveArchSampleChannel (Real.log 2)
            (suzukiMangoldtApexAperture n) (mangoldtLogHaarNode n) := by
        ring
      _ ≤ (1 - suzukiMangoldtDyadicSharpContraction) * mangoldtLogHaarAtomMass m *
            suzukiRectangularPositiveArchSampleChannel (Real.log 2)
              (suzukiMangoldtApexAperture n) (mangoldtLogHaarNode n) := hmassScaled
  exact ⟨m, hmTwo, hnm, hmn, hmNe, hmPow, habsolutePos, habsoluteLe, hsurplusLower⟩

theorem exists_dyadic_quantitative_suzukiMangoldtFlankSurplus
    {n : ℕ} (hn : 2 ≤ n) :
    ∃ m : ℕ,
      2 ≤ m ∧ n < 2 * m ∧ m ≤ 2 * n ∧ m ≠ n ∧
      IsPrimePow m ∧
      0 < (1 - Real.sqrt 2 / 2) * mangoldtLogHaarAtomMass m *
        suzukiRectangularPositiveArchSampleChannel (Real.log 2)
          (suzukiMangoldtApexAperture n) (mangoldtLogHaarNode n) ∧
      (1 - Real.sqrt 2 / 2) * mangoldtLogHaarAtomMass m *
          suzukiRectangularPositiveArchSampleChannel (Real.log 2)
            (suzukiMangoldtApexAperture n) (mangoldtLogHaarNode n) ≤
        suzukiMangoldtAlignedFlankSurplus n m := by
  obtain ⟨m, hmTwo, hnm, hmn, hmNe, hmPow, hmMass, hmSample⟩ :=
    exists_dyadic_uniform_suzukiMangoldtFlankDilution hn
  have hcPos : 0 < 1 - Real.sqrt 2 / 2 :=
    sub_pos.mpr sqrtTwo_div_two_lt_one
  have hselfPos := suzukiMangoldtAlignedApex_self_pos hn
  refine ⟨m, hmTwo, hnm, hmn, hmNe, hmPow,
    mul_pos (mul_pos hcPos hmMass) hselfPos, ?_⟩
  rw [suzukiMangoldtAlignedFlankSurplus]
  have hweighted := mul_le_mul_of_nonneg_left hmSample hmMass.le
  nlinarith


theorem suzukiMangoldtDyadicApex_successor_sample_eq_zero
    {k : ℕ} (hk : 1 ≤ k) :
    suzukiRectangularPositiveArchSampleChannel (Real.log 2)
        (suzukiMangoldtApexAperture (2 ^ k))
        (mangoldtLogHaarNode (2 ^ (k + 1))) = 0 := by
  have hnTwo : 2 ≤ 2 ^ k := by
    have := Nat.pow_le_pow_right (by omega : 0 < 2) hk
    simpa using this
  have hmTwo : 2 ≤ 2 ^ (k + 1) := hnTwo.trans (by
    rw [pow_succ']
    omega)
  apply suzukiMangoldtAlignedApex_sample_eq_zero_of_outside hnTwo hmTwo
  right
  rw [pow_succ']

theorem suzukiMangoldtDyadicApex_successor_surplus_eq_and_pos
    {k : ℕ} (hk : 1 ≤ k) :
    suzukiMangoldtAlignedFlankSurplus (2 ^ k) (2 ^ (k + 1)) =
        mangoldtLogHaarAtomMass (2 ^ (k + 1)) *
          suzukiRectangularPositiveArchSampleChannel (Real.log 2)
            (suzukiMangoldtApexAperture (2 ^ k)) (mangoldtLogHaarNode (2 ^ k)) ∧
      0 < suzukiMangoldtAlignedFlankSurplus (2 ^ k) (2 ^ (k + 1)) := by
  have hnTwo : 2 ≤ 2 ^ k := by
    have := Nat.pow_le_pow_right (by omega : 0 < 2) hk
    simpa using this
  have hmPow : IsPrimePow (2 ^ (k + 1)) :=
    Nat.prime_two.isPrimePow.pow (by omega)
  have hmMass : 0 < mangoldtLogHaarAtomMass (2 ^ (k + 1)) :=
    mangoldtLogHaarAtomMass_pos_of_vonMangoldt_pos (by positivity)
      (ArithmeticFunction.vonMangoldt_pos_iff.mpr hmPow)
  have hself := suzukiMangoldtAlignedApex_self_pos hnTwo
  rw [suzukiMangoldtAlignedFlankSurplus,
    suzukiMangoldtDyadicApex_successor_sample_eq_zero hk, sub_zero]
  exact ⟨rfl, mul_pos hmMass hself⟩


end RHTower
