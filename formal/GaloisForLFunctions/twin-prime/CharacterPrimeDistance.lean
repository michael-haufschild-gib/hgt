import GaloisForLFunctions.TransHorizonIncidenceMechanics.TheQuarterLawOfResidueFlips
import GaloisForLFunctions.RHTower.Sieve.PrimeCosineSum
import GaloisForLFunctions.RHTower.Sieve.PrimeSupportedConvolutionBound
import GaloisForLFunctions.RHTower.Sieve.DistanceAbscissaBridge
import Mathlib.NumberTheory.ArithmeticFunction.Liouville
import Mathlib.Data.PNat.Basic

/-!
# Character-uniform Liouville distance at middle frequencies

The finite inequality `1 - Re(z²) ≤ 4(1 + Re z)` on the unit disk
transfers an upper bound for the squared character's prime sum to a
lower bound for Liouville's distance. Euler comparison, prime-tail
control, and the abscissa shift have absolute errors. The resulting
modulus loss is only one quarter of its logarithm.
-/

open Finset RHTower RHTower.Sieve
open GaloisForLFunctions.TransHorizonIncidenceMechanics

namespace TwinPrime.CharacterDistance
noncomputable section

/-- A Dirichlet character multiplied by the archimedean character `n^(it)`. -/
def phase {q : ℕ} (χ : DirichletCharacter ℂ q) (t : ℝ) (n : ℕ) : ℂ :=
  χ n * charFn t n

/-- The real, harmonically weighted character prime sum. -/
def primeSum {q : ℕ} (N : ℕ) (χ : DirichletCharacter ℂ q) (t : ℝ) : ℝ :=
  ∑ p ∈ Nat.primesLE N, (phase χ t p).re / (p : ℝ)

/-- The squared pretentious distance of the actual Liouville row. -/
def distance {q : ℕ} (N : ℕ) (χ : DirichletCharacter ℂ q) (t : ℝ) : ℝ :=
  ∑ p ∈ Nat.primesLE N, (1 + (phase χ t p).re) / (p : ℝ)

/-- The absolute cost of Euler comparison, the prime tail, and the abscissa shift. -/
def comparisonError : ℝ :=
  primeSquareMass + 2 * (Real.log 2 + 2 * (2 * mertensFirstConst + 1 / 2)) /
    Real.log 2 + (1 + Real.log 4)

/-- The absolute additive loss in the quarter-distance bound. -/
def quarterError : ℝ :=
  (mertensSecondLowerConst + comparisonError + Real.log 2 +
    Real.log (8 * Real.exp 1 + 17)) / 4

theorem norm_phase_le_one {q : ℕ} (χ : DirichletCharacter ℂ q) (t : ℝ) (n : ℕ) :
    ‖phase χ t n‖ ≤ 1 := by
  rw [phase, norm_mul, norm_charFn, mul_one]
  exact χ.norm_le_one _

private theorem abs_re_phase_le_one {q : ℕ} (χ : DirichletCharacter ℂ q)
    (t : ℝ) (n : ℕ) : |(phase χ t n).re| ≤ 1 :=
  (Complex.abs_re_le_norm _).trans (norm_phase_le_one χ t n)

/-- Squaring doubles the frequency and squares the Dirichlet character. -/
theorem phase_sq {q : ℕ} (χ : DirichletCharacter ℂ q) (t : ℝ) (n : ℕ) :
    phase χ t n ^ 2 = phase (χ ^ 2) (2 * t) n := by
  rw [phase, phase, mul_pow, χ.pow_apply' two_ne_zero]
  congr 1
  rw [charFn, charFn, pow_two, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The finite 3–4–1 inequality retains primes at which the character vanishes. -/
theorem harmonic_sub_square_le_four_distance {q : ℕ} (N : ℕ)
    (χ : DirichletCharacter ℂ q) (t : ℝ) :
    mertensS N - primeSum N (χ ^ 2) (2 * t) ≤ 4 * distance N χ t := by
  rw [mertensS, primeSum, distance, ← Finset.sum_sub_distrib, Finset.mul_sum]
  refine Finset.sum_le_sum fun p hp => ?_
  have hz := norm_phase_le_one χ t p
  have hs : ‖phase χ t p‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg (phase χ t p)]
  rw [Complex.sq_norm, Complex.normSq_apply] at hs
  have hpoly : 1 - (phase (χ ^ 2) (2 * t) p).re ≤ 4 * (1 + (phase χ t p).re) := by
    rw [← phase_sq, pow_two, Complex.mul_re]
    nlinarith only [hs, sq_nonneg (1 + (phase χ t p).re)]
  convert div_le_div_of_nonneg_right hpoly (Nat.cast_nonneg p) using 1 <;> ring

private theorem log_ge_one {N : ℕ} (hN : 3 ≤ N) : 1 ≤ Real.log (N : ℝ) := by
  have hN' : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hexp : Real.exp 1 ≤ (N : ℝ) := le_trans (le_of_lt Real.exp_one_lt_d9) (by linarith)
  simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hexp

private theorem conj_charFn_neg (t : ℝ) (n : ℕ) :
    (starRingEnd ℂ) (charFn (-t) n) = charFn t n := by
  rw [conj_charFn, charFn]
  congr 3
  ring

private def primeTerm {q : ℕ} (χ : DirichletCharacter ℂ q) (σ t : ℝ)
    (p : Nat.Primes) : ℂ :=
  χ p * ((p : ℕ) : ℂ) ^ (-((σ : ℂ) - (t : ℂ) * Complex.I))

private theorem norm_primeTerm_le {q : ℕ} (χ : DirichletCharacter ℂ q)
    (σ t : ℝ) (p : Nat.Primes) :
    ‖primeTerm χ σ t p‖ ≤ ((p : ℕ) : ℝ) ^ (-σ) := by
  simpa only [primeTerm, Complex.sub_re, Complex.ofReal_re, Complex.mul_re,
    Complex.I_re, Complex.I_im, Complex.ofReal_im, mul_zero, zero_mul, sub_zero] using
    norm_char_prime_cpow_le χ (w := (σ : ℂ) - (t : ℂ) * Complex.I) p

private theorem primeTerm_re {q : ℕ} (χ : DirichletCharacter ℂ q)
    (σ t : ℝ) (p : Nat.Primes) :
    (primeTerm χ σ t p).re = ((p : ℕ) : ℝ) ^ (-σ) * (phase χ t p).re := by
  have hre : ((σ : ℂ) - (t : ℂ) * Complex.I).re = σ := by simp
  have him : ((σ : ℂ) - (t : ℂ) * Complex.I).im = -t := by simp
  rw [primeTerm, natCast_cpow_neg_eq_mul _ p.2.pos, hre, him,
    conj_charFn_neg, mul_left_comm, Complex.re_ofReal_mul]
  rfl

private theorem summable_primeTerm {q : ℕ} (χ : DirichletCharacter ℂ q)
    {σ : ℝ} (hσ : 1 < σ) (t : ℝ) : Summable (primeTerm χ σ t) :=
  (Nat.Primes.summable_rpow.mpr (by linarith)).of_norm_bounded
    (norm_primeTerm_le χ σ t)

private theorem norm_tail_le {q N : ℕ} (χ : DirichletCharacter ℂ q)
    (σ t : ℝ) (p : Nat.Primes) :
    ‖if N < (p : ℕ) then primeTerm χ σ t p else 0‖ ≤ primeTailTerm N σ p := by
  rw [primeTailTerm]
  split_ifs
  · exact norm_primeTerm_le χ σ t p
  · simp only [norm_zero, le_refl]

private theorem prime_series_split {q N : ℕ} (χ : DirichletCharacter ℂ q)
    {σ : ℝ} (hσ : 1 < σ) (t : ℝ) :
    (∑' p : Nat.Primes, primeTerm χ σ t p).re =
      (∑ p ∈ Nat.primesLE N, (p : ℝ) ^ (-σ) * (phase χ t p).re) +
        (∑' p : Nat.Primes, if N < (p : ℕ) then primeTerm χ σ t p else 0).re := by
  classical
  have hH : Summable (fun p : Nat.Primes =>
      if (p : ℕ) ≤ N then primeTerm χ σ t p else 0) := by
    refine summable_of_ne_finset_zero (s := primeSubtypeLE N) ?_
    intro p hp
    exact if_neg fun h => hp (mem_primeSubtypeLE.mpr h)
  have hT : Summable (fun p : Nat.Primes =>
      if N < (p : ℕ) then primeTerm χ σ t p else 0) :=
    (summable_primeTailTerm N hσ).of_norm_bounded (norm_tail_le χ σ t)
  have hadd (p : Nat.Primes) : primeTerm χ σ t p =
      (if (p : ℕ) ≤ N then primeTerm χ σ t p else 0) +
        (if N < (p : ℕ) then primeTerm χ σ t p else 0) := by
    by_cases h : (p : ℕ) ≤ N
    · rw [if_pos h, if_neg (by omega), add_zero]
    · rw [if_neg h, if_pos (by omega), zero_add]
  rw [tsum_congr hadd, hH.tsum_add hT, Complex.add_re]
  congr 1
  rw [tsum_eq_sum (s := primeSubtypeLE N) (fun p hp =>
    if_neg fun h => hp (mem_primeSubtypeLE.mpr h)), Complex.re_sum]
  calc
    _ = ∑ p ∈ primeSubtypeLE N, ((p : ℕ) : ℝ) ^ (-σ) * (phase χ t p).re := by
      refine Finset.sum_congr rfl fun p hp => ?_
      rw [if_pos (mem_primeSubtypeLE.mp hp), primeTerm_re]
    _ = _ := sum_primeSubtypeLE N
      (fun p : ℕ => (p : ℝ) ^ (-σ) * (phase χ t p).re)

private theorem primeSum_shift {q N : ℕ} (χ : DirichletCharacter ℂ q) (σ t : ℝ) :
    primeSum N χ t =
      (∑ p ∈ Nat.primesLE N, (p : ℝ) ^ (-σ) * (phase χ t p).re) +
      ∑ p ∈ Nat.primesLE N,
        (phase χ t p).re * (1 / (p : ℝ) - (p : ℝ) ^ (-σ)) := by
  rw [primeSum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun _ _ => by ring

private theorem abs_primeSum_sub_log_le {q N : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hN : 3 ≤ N) (t : ℝ) :
    |primeSum N χ t - Real.log ‖DirichletCharacter.LFunction χ
      (((1 + 1 / Real.log (N : ℝ) : ℝ) : ℂ) - (t : ℂ) * Complex.I)‖| ≤
      comparisonError := by
  have hlog := log_ge_one hN
  have hlog0 : 0 < Real.log (N : ℝ) := by linarith only [hlog]
  set σ : ℝ := 1 + 1 / Real.log (N : ℝ) with hσdef
  have hσ : 1 < σ := by
    dsimp [σ]
    linarith only [one_div_pos.mpr hlog0]
  set w : ℂ := (σ : ℂ) - (t : ℂ) * Complex.I with hwdef
  have hw : 1 < w.re := by simpa [w] using hσ
  have hEuler := norm_tsum_char_sub_eulerLog_le χ hw
  have hlogEuler : Real.log ‖DirichletCharacter.LFunction χ w‖ =
      (eulerLog χ w).re := by
    rw [← exp_eulerLog χ hw, Complex.norm_exp, Real.log_exp]
  have hcomp : |(∑' p : Nat.Primes, primeTerm χ σ t p).re -
      Real.log ‖DirichletCharacter.LFunction χ w‖| ≤ primeSquareMass := by
    rw [hlogEuler, ← Complex.sub_re]
    exact (Complex.abs_re_le_norm _).trans hEuler
  have htailSum : Summable (fun p : Nat.Primes =>
      ‖if N < (p : ℕ) then primeTerm χ σ t p else 0‖) :=
    (summable_primeTailTerm N hσ).of_nonneg_of_le (fun _ => norm_nonneg _)
      (norm_tail_le χ σ t)
  have htail : |(∑' p : Nat.Primes,
      if N < (p : ℕ) then primeTerm χ σ t p else 0).re| ≤
      2 * (Real.log 2 + 2 * (2 * mertensFirstConst + 1 / 2)) / Real.log 2 := by
    refine (Complex.abs_re_le_norm _).trans ((norm_tsum_le_tsum_norm htailSum).trans ?_)
    exact (htailSum.tsum_le_tsum (norm_tail_le χ σ t)
      (summable_primeTailTerm N hσ)).trans (tsum_primeTailTerm_le hN)
  have hshift := abs_sum_weight_shift_le (by omega : 1 ≤ N) hσ.le
    (abs_re_phase_le_one χ t)
  have hshiftBound : (σ - 1) * (Real.log N + Real.log 4) ≤ 1 + Real.log 4 := by
    have hval : (σ - 1) * (Real.log N + Real.log 4) =
        1 + Real.log 4 / Real.log N := by
      rw [hσdef]
      field_simp
      ring
    have hdiv : Real.log 4 / Real.log N ≤ Real.log 4 := by
      apply (div_le_iff₀ hlog0).mpr
      nlinarith only [hlog, Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4)]
    rw [hval]
    linarith only [hdiv]
  have hsplit := prime_series_split (N := N) χ hσ t
  have hident := primeSum_shift (N := N) χ σ t
  change |primeSum N χ t - Real.log ‖DirichletCharacter.LFunction χ w‖| ≤ _
  rw [comparisonError, abs_le]
  obtain ⟨hc₁, hc₂⟩ := abs_le.mp hcomp
  obtain ⟨ht₁, ht₂⟩ := abs_le.mp htail
  obtain ⟨hs₁, hs₂⟩ := abs_le.mp (hshift.trans hshiftBound)
  constructor <;> linarith only [hc₁, hc₂, ht₁, ht₂, hs₁, hs₂, hsplit, hident]

/-- Finite harmonic prime sums differ from the actual Euler logarithm by an absolute constant. -/
theorem primeSum_log_comparison (n : ℕ) (q : ℕ+)
    (χ : DirichletCharacter ℂ (q : ℕ)) (t : ℝ) :
    |primeSum (n + 3) χ t - Real.log ‖DirichletCharacter.LFunction χ
      (((1 + 1 / Real.log ((n + 3 : ℕ) : ℝ) : ℝ) : ℂ) - (t : ℂ) * Complex.I)‖| ≤
      comparisonError :=
  abs_primeSum_sub_log_le χ (by omega) t

/-- The explicit logarithmic-strip constant grows at most linearly with the modulus. -/
theorem character_constant_le (q : ℕ+) :
    characterLogStripConstant q ≤ (8 * Real.exp 1 + 17) * (q : ℝ) := by
  have hq : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast (Nat.succ_le_iff.mpr q.pos)
  have hp : (2 : ℝ) ^ (q : ℕ).primeFactors.card ≤ (q : ℝ) := by
    exact_mod_cast two_pow_card_primeFactors_le (Nat.succ_le_iff.mpr q.pos)
  unfold characterLogStripConstant
  nlinarith only [hp, hq, Real.exp_pos 1]

/-- Character multiplication agrees exactly with the actual Liouville distance. -/
theorem distance_eq_liouville {q : ℕ} (N : ℕ) (χ : DirichletCharacter ℂ q) (t : ℝ) :
    distance N χ t = mulDistSqPair
      (fun n => (ArithmeticFunction.liouville n : ℂ)) (phase χ t) (Nat.primesLE N) := by
  rw [distance, mulDistSqPair]
  refine Finset.sum_congr rfl fun p hp => ?_
  have hprime := (Nat.mem_primesLE.mp hp).2
  have hliouville : ArithmeticFunction.liouville p = -1 := by
    rw [ArithmeticFunction.liouville_apply hprime.ne_zero,
      ArithmeticFunction.cardFactors_apply_prime hprime, pow_one]
  simp only [hliouville, Int.cast_neg, Int.cast_one, neg_one_mul, Complex.neg_re,
    Complex.conj_re, sub_neg_eq_add]

private theorem primeSum_le_log_norm_bound {q N : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hN : 3 ≤ N) {t : ℝ} (ht : 8 ≤ |t|) :
    primeSum N χ t ≤ Real.log (characterLogStripConstant q) +
      Real.log (Real.log |t|) + comparisonError := by
  have hlogN := log_ge_one hN
  have hlogN0 : 0 < Real.log (N : ℝ) := by linarith only [hlogN]
  have hlogt : 0 < Real.log |t| := Real.log_pos (by linarith only [ht])
  have hK : 0 < characterLogStripConstant q :=
    lt_of_lt_of_le zero_lt_one (one_le_characterLogStripConstant q)
  set σ : ℝ := 1 + 1 / Real.log (N : ℝ) with hσdef
  have hσ : 1 < σ := by
    dsimp [σ]
    linarith only [one_div_pos.mpr hlogN0]
  have hσ2 : σ ≤ 2 := by
    have hinv := (div_le_one hlogN0).mpr hlogN
    dsimp [σ]
    linarith only [hinv]
  set w : ℂ := (σ : ℂ) - (t : ℂ) * Complex.I with hwdef
  have hw : 1 < w.re := by simpa [w] using hσ
  have hwpos : 0 < ‖DirichletCharacter.LFunction χ w‖ := by
    rw [← exp_eulerLog χ hw, Complex.norm_exp]
    exact Real.exp_pos _
  have hL : ‖DirichletCharacter.LFunction χ w‖ ≤
      characterLogStripConstant q * Real.log |t| := by
    have hb := norm_LFunction_le_log χ (σ := σ) (t := -t)
      (by simpa only [abs_neg] using ht)
      (by rw [abs_neg]; linarith only [hσ, (one_div_pos.mpr hlogt)]) hσ2
    simpa only [w, Complex.ofReal_neg, neg_mul, sub_eq_add_neg, abs_neg] using hb
  have hlogL := Real.log_le_log hwpos hL
  rw [Real.log_mul hK.ne' hlogt.ne'] at hlogL
  have hcomp := (abs_le.mp (abs_primeSum_sub_log_le χ hN t)).2
  change primeSum N χ t - Real.log ‖DirichletCharacter.LFunction χ w‖ ≤
    comparisonError at hcomp
  linarith only [hlogL, hcomp]

/-- The distance pays only a quarter logarithmic loss in frequency and modulus. -/
theorem quarter_distance (n : ℕ) (q : ℕ+) (χ : DirichletCharacter ℂ (q : ℕ))
    (t : {t : ℝ // 9 ≤ |t|}) :
    (Real.log (Real.log ((n + 3 : ℕ) : ℝ)) - Real.log (Real.log |(t : ℝ)|) -
      Real.log (q : ℝ)) / 4 - quarterError ≤ distance (n + 3) χ t := by
  have ht := t.property
  have habs : 0 < |(t : ℝ)| := by linarith only [ht]
  have hlogt : 0 < Real.log |(t : ℝ)| := Real.log_pos (by linarith only [ht])
  have hlog2t : 0 < Real.log (2 * |(t : ℝ)|) :=
    Real.log_pos (by linarith only [ht])
  have htwice : Real.log (2 * |(t : ℝ)|) ≤ 2 * Real.log |(t : ℝ)| := by
    rw [Real.log_mul (by norm_num) habs.ne']
    have hlog2 := Real.log_le_log (by norm_num : (0 : ℝ) < 2)
      (by linarith only [ht] : (2 : ℝ) ≤ |(t : ℝ)|)
    linarith only [hlog2]
  have hfreq : Real.log (Real.log (2 * |(t : ℝ)|)) ≤
      Real.log 2 + Real.log (Real.log |(t : ℝ)|) := by
    have h := Real.log_le_log hlog2t htwice
    rwa [Real.log_mul (by norm_num) hlogt.ne'] at h
  have hsum := primeSum_le_log_norm_bound (χ ^ 2) (N := n + 3) (by omega)
    (t := 2 * (t : ℝ)) (by
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      linarith only [ht])
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at hsum
  have hK : 0 < characterLogStripConstant q :=
    lt_of_lt_of_le zero_lt_one (one_le_characterLogStripConstant q)
  have hB : 0 < 8 * Real.exp 1 + 17 := by positivity
  have hq : (0 : ℝ) < (q : ℝ) := by exact_mod_cast q.pos
  have hmod := Real.log_le_log hK (character_constant_le q)
  rw [Real.log_mul hB.ne' hq.ne'] at hmod
  have hpoly := harmonic_sub_square_le_four_distance (n + 3) χ (t : ℝ)
  have hmass := le_mertensS (N := n + 3) (by omega)
  rw [logLog] at hmass
  rw [quarterError]
  linarith only [hpoly, hmass, hsum, hfreq, hmod]

/-- The growing-modulus middle-frequency domain has a fixed positive distance proportion. -/
theorem middle_frequency_distance (n : ℕ)
    (q : {q : ℕ+ // (q : ℝ) ≤ (Real.log ((n + 3 : ℕ) : ℝ)) ^ (1 / 125 : ℝ)})
    (χ : DirichletCharacter ℂ (q.val : ℕ))
    (t : {t : ℝ // 9 ≤ |t| ∧
      Real.log |t| ≤ (Real.log ((n + 3 : ℕ) : ℝ)) ^ (4 / 5 : ℝ)}) :
    (6 / 125 : ℝ) * Real.log (Real.log ((n + 3 : ℕ) : ℝ)) - quarterError ≤
      distance (n + 3) χ t := by
  have hN : 0 < Real.log ((n + 3 : ℕ) : ℝ) :=
    lt_of_lt_of_le zero_lt_one (log_ge_one (by omega))
  have hq : (0 : ℝ) < (q.val : ℝ) := by exact_mod_cast q.val.pos
  have ht : 0 < Real.log |(t : ℝ)| :=
    Real.log_pos (by linarith only [t.property.1])
  have hmod := Real.log_le_log hq q.property
  rw [Real.log_rpow hN] at hmod
  have hfreq := Real.log_le_log ht t.property.2
  rw [Real.log_rpow hN] at hfreq
  have hbase := quarter_distance n q.val χ ⟨t.val, t.property.1⟩
  linarith only [hbase, hmod, hfreq]

/-- The actual distance supplies the logarithmic decay of its exponential penalty. -/
theorem middle_frequency_decay (n : ℕ)
    (q : {q : ℕ+ // (q : ℝ) ≤ (Real.log ((n + 3 : ℕ) : ℝ)) ^ (1 / 125 : ℝ)})
    (χ : DirichletCharacter ℂ (q.val : ℕ))
    (t : {t : ℝ // 9 ≤ |t| ∧
      Real.log |t| ≤ (Real.log ((n + 3 : ℕ) : ℝ)) ^ (4 / 5 : ℝ)}) :
    Real.exp (-distance (n + 3) χ t / 20) ≤
      Real.exp (quarterError / 20) *
        (Real.log ((n + 3 : ℕ) : ℝ)) ^ (-3 / 1250 : ℝ) := by
  have hN : 0 < Real.log ((n + 3 : ℕ) : ℝ) :=
    lt_of_lt_of_le zero_lt_one (log_ge_one (by omega))
  have hD := middle_frequency_distance n q χ t
  calc
    _ ≤ Real.exp (quarterError / 20 +
        (-3 / 1250 : ℝ) * Real.log (Real.log ((n + 3 : ℕ) : ℝ))) := by
      apply Real.exp_le_exp.mpr
      linarith only [hD]
    _ = _ := by
      rw [Real.exp_add, Real.rpow_def_of_pos hN]
      congr 1
      congr 1
      ring

end
end TwinPrime.CharacterDistance
