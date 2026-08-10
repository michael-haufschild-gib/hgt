import GaloisForLFunctions.RHTower.Sieve.RamareEnergy
import GaloisForLFunctions.RHTower.Sieve.RoughCountTuran

/-!
# The square-multiple part of the Ramaré factorisation

The part of the Möbius polynomial that the bilinear form misses, beyond the rough integers, is
carried by the integers divisible by the square of a designated prime.  Assembled over the whole
prime set it is a single Dirichlet polynomial with coefficients

```text
c(n) = μ(n)·#{p ∈ P : p² ∣ n} / ω_P(n) ,        ‖c(n)‖ ≤ 1 ,
```

vanishing unless some `p² ∣ n`.  Its energy is therefore at most the number of such integers,

```text
∑_{n ≤ M} ‖c(n)‖²  ≤  ∑_{n ≤ M} #{p ∈ P : p² ∣ n}  =  ∑_{p ∈ P} ⌊M/p²⌋  ≤  M·∑_{p ∈ P} p^{-2} ,
```

so over a prime range starting above `1/ε` this part costs `ε·M²` in mean square and nothing in the
diagonal — a full power of the prime scale below the trivial size.
-/

noncomputable section

namespace RHTower.Sieve

open MeasureTheory Finset
open scoped ArithmeticFunction.Moebius

/-- The number of designated primes whose square divides `n`. -/
def sqMultCount (P : Finset ℕ) (n : ℕ) : ℕ := ({p ∈ P | p * p ∣ n}).card

theorem sqMultCount_le_card_primeFactorsIn (P : Finset ℕ) (n : ℕ) :
    sqMultCount P n ≤ (primeFactorsIn P n).card := by
  classical
  refine Finset.card_le_card fun p hp => ?_
  rw [Finset.mem_filter] at hp
  rw [mem_primeFactorsIn]
  exact ⟨hp.1, dvd_trans (Dvd.intro p rfl) hp.2⟩

/-- The coefficients of the square-multiple polynomial. -/
def sqMultCoeff (P : Finset ℕ) (n : ℕ) : ℂ :=
  ((μ n : ℤ) : ℂ) * (sqMultCount P n : ℂ) / ((primeFactorsIn P n).card : ℂ)

theorem norm_sqMultCoeff_le (P : Finset ℕ) (n : ℕ) :
    ‖sqMultCoeff P n‖ ≤ (sqMultCount P n : ℝ) := by
  classical
  rcases Nat.eq_zero_or_pos (sqMultCount P n) with h0 | h0
  · rw [sqMultCoeff, h0]
    norm_num
  · have hω : 1 ≤ (primeFactorsIn P n).card :=
      le_trans h0 (sqMultCount_le_card_primeFactorsIn P n)
    have hωR : (1 : ℝ) ≤ ((primeFactorsIn P n).card : ℝ) := by exact_mod_cast hω
    have hnum : ‖((μ n : ℤ) : ℂ)‖ ≤ 1 := by
      have hnorm : ‖((μ n : ℤ) : ℂ)‖ = |((μ n : ℤ) : ℝ)| := by
        rw [show (((μ n : ℤ)) : ℂ) = ((((μ n : ℤ) : ℝ)) : ℂ) by push_cast; ring,
          Complex.norm_real, Real.norm_eq_abs]
      rw [hnorm]
      exact abs_moebius_real_le_one n
    rw [sqMultCoeff, norm_div, norm_mul, Complex.norm_natCast, Complex.norm_natCast]
    rw [div_le_iff₀ (by linarith)]
    nlinarith [hnum, hωR, Nat.cast_nonneg (α := ℝ) (sqMultCount P n), norm_nonneg ((μ n : ℤ) : ℂ)]

theorem norm_sqMultCoeff_le_one (P : Finset ℕ) (n : ℕ) : ‖sqMultCoeff P n‖ ≤ 1 := by
  classical
  rcases Nat.eq_zero_or_pos (sqMultCount P n) with h0 | h0
  · rw [sqMultCoeff, h0]
    norm_num
  · have hω : 1 ≤ (primeFactorsIn P n).card :=
      le_trans h0 (sqMultCount_le_card_primeFactorsIn P n)
    have hle : (sqMultCount P n : ℝ) ≤ ((primeFactorsIn P n).card : ℝ) := by
      exact_mod_cast sqMultCount_le_card_primeFactorsIn P n
    have hωR : (1 : ℝ) ≤ ((primeFactorsIn P n).card : ℝ) := by exact_mod_cast hω
    have hnum : ‖((μ n : ℤ) : ℂ)‖ ≤ 1 := by
      have hnorm : ‖((μ n : ℤ) : ℂ)‖ = |((μ n : ℤ) : ℝ)| := by
        rw [show (((μ n : ℤ)) : ℂ) = ((((μ n : ℤ) : ℝ)) : ℂ) by push_cast; ring,
          Complex.norm_real, Real.norm_eq_abs]
      rw [hnorm]
      exact abs_moebius_real_le_one n
    rw [sqMultCoeff, norm_div, norm_mul, Complex.norm_natCast, Complex.norm_natCast]
    rw [div_le_one (by linarith)]
    nlinarith [hnum, hle, Nat.cast_nonneg (α := ℝ) (sqMultCount P n),
      norm_nonneg ((μ n : ℤ) : ℂ)]

/-- The number of square-multiples, as a sum of indicators. -/
theorem sqMultCount_eq_sum (P : Finset ℕ) (n : ℕ) :
    (sqMultCount P n : ℝ) = ∑ p ∈ P, if p * p ∣ n then (1 : ℝ) else 0 := by
  classical
  rw [sqMultCount, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]

/-- The total number of square-multiples in `[1, M]`. -/
theorem sum_sqMultCount_Icc (P : Finset ℕ) (M : ℕ) :
    ∑ n ∈ Finset.Icc 1 M, (sqMultCount P n : ℝ)
      = ∑ p ∈ P, ((M / (p * p) : ℕ) : ℝ) := by
  classical
  simp_rw [sqMultCount_eq_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one, card_Icc_filter_dvd]

/-- **The energy of the square-multiple polynomial.** -/
theorem sum_energy_sqMultCoeff_le (P : Finset ℕ) (M : ℕ) :
    ∑ n ∈ Finset.Icc 1 M, ‖sqMultCoeff P n‖ ^ 2
      ≤ ∑ p ∈ P, (M : ℝ) / ((p : ℝ) * (p : ℝ)) := by
  classical
  have hterm : ∀ n ∈ Finset.Icc 1 M, ‖sqMultCoeff P n‖ ^ 2 ≤ (sqMultCount P n : ℝ) := by
    intro n _
    have h1 := norm_sqMultCoeff_le P n
    have h2 := norm_sqMultCoeff_le_one P n
    nlinarith [norm_nonneg (sqMultCoeff P n)]
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [sum_sqMultCount_Icc]
  refine Finset.sum_le_sum fun p _ => ?_
  have hcast : ((M / (p * p) : ℕ) : ℝ) ≤ (M : ℝ) / ((p * p : ℕ) : ℝ) := Nat.cast_div_le
  have hpp : ((p * p : ℕ) : ℝ) = (p : ℝ) * (p : ℝ) := by push_cast; ring
  rw [hpp] at hcast
  exact hcast

/-- **The mean square of the square-multiple polynomial.** -/
theorem integral_Icc_normSq_sqMultPoly_le (P : Finset ℕ) (M : ℕ) {W : ℝ} (hW : 1 ≤ W) :
    (∫ w in Set.Icc (-W) W, ‖logPoly (sqMultCoeff P) (Finset.Icc 1 M) w‖ ^ 2)
      ≤ (5 * Real.pi / 2 * W + 5 * Real.exp 1 / 2 * (M : ℝ))
          * (∑ p ∈ P, (M : ℝ) / ((p : ℝ) * (p : ℝ))) := by
  classical
  have hs0 : (0 : ℕ) ∉ Finset.Icc 1 M := by
    rw [Finset.mem_Icc]
    omega
  have hsM : ∀ n ∈ Finset.Icc 1 M, n ≤ M := fun n hn => (Finset.mem_Icc.1 hn).2
  refine le_trans (integral_Icc_normSq_logPoly_le_energy (sqMultCoeff P) hs0 hsM hW) ?_
  have hcoef0 : (0 : ℝ) ≤ 5 * Real.pi / 2 * W + 5 * Real.exp 1 / 2 * (M : ℝ) := by
    have := Real.pi_pos
    have := (Real.exp_pos 1).le
    have hW0 : (0 : ℝ) < W := lt_of_lt_of_le zero_lt_one hW
    positivity
  exact mul_le_mul_of_nonneg_left (sum_energy_sqMultCoeff_le P M) hcoef0

/-- The multiples of `p` whose cofactor is again divisible by `p` are exactly the multiples of
`p²`. -/
theorem image_ramareCofactor_dvd (M : ℕ) {p : ℕ} (hp : 0 < p) :
    ({m ∈ ramareCofactorSet (Finset.Icc 1 M) p | p ∣ m}).image (fun m => p * m)
      = {n ∈ Finset.Icc 1 M | p * p ∣ n} := by
  classical
  ext n
  simp only [Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨m, ⟨hmcof, hpm⟩, rfl⟩
    rw [ramareCofactorSet, Finset.mem_image] at hmcof
    obtain ⟨k, hk, hkm⟩ := hmcof
    rw [Finset.mem_filter] at hk
    obtain ⟨hkI, hpk⟩ := hk
    have hkeq : p * (k / p) = k := Nat.mul_div_cancel' hpk
    refine ⟨by rw [← hkm, hkeq]; exact hkI, ?_⟩
    obtain ⟨j, rfl⟩ := hpm
    exact ⟨j, by ring⟩
  · rintro ⟨hnI, hpp⟩
    refine ⟨n / p, ⟨?_, ?_⟩, ?_⟩
    · rw [ramareCofactorSet, Finset.mem_image]
      exact ⟨n, Finset.mem_filter.2 ⟨hnI, dvd_trans (Dvd.intro p rfl) hpp⟩, rfl⟩
    · obtain ⟨j, rfl⟩ := hpp
      refine ⟨j, ?_⟩
      rw [show p * p * j = p * (p * j) by ring, Nat.mul_div_cancel_left _ hp]
    · exact Nat.mul_div_cancel' (dvd_trans (Dvd.intro p rfl) hpp)

/-- **The Ramaré remainders assemble into the square-multiple polynomial.** -/
theorem sum_ramare_remainder_eq_sqMult {P : Finset ℕ} (hPprime : ∀ q ∈ P, q.Prime) (M : ℕ)
    (w : ℝ) :
    ∑ p ∈ P, ∑ m ∈ {m ∈ ramareCofactorSet (Finset.Icc 1 M) p | p ∣ m},
        moebiusPhase w (p * m) / ((primeFactorsIn P (p * m)).card : ℂ)
      = logPoly (sqMultCoeff P) (Finset.Icc 1 M) w := by
  classical
  have hblock : ∀ p ∈ P,
      (∑ m ∈ {m ∈ ramareCofactorSet (Finset.Icc 1 M) p | p ∣ m},
          moebiusPhase w (p * m) / ((primeFactorsIn P (p * m)).card : ℂ))
        = ∑ n ∈ {n ∈ Finset.Icc 1 M | p * p ∣ n},
            moebiusPhase w n / ((primeFactorsIn P n).card : ℂ) := by
    intro p hp
    have hppos := (hPprime p hp).pos
    have hinj : ∀ x ∈ {m ∈ ramareCofactorSet (Finset.Icc 1 M) p | p ∣ m},
        ∀ y ∈ {m ∈ ramareCofactorSet (Finset.Icc 1 M) p | p ∣ m},
        p * x = p * y → x = y := fun x _ y _ hxy => Nat.eq_of_mul_eq_mul_left hppos hxy
    rw [← image_ramareCofactor_dvd M hppos,
      Finset.sum_image hinj (f := fun n => moebiusPhase w n / ((primeFactorsIn P n).card : ℂ))]
  rw [Finset.sum_congr rfl hblock]
  -- exchange the order of summation
  have hswap : ∑ p ∈ P, ∑ n ∈ {n ∈ Finset.Icc 1 M | p * p ∣ n},
        moebiusPhase w n / ((primeFactorsIn P n).card : ℂ)
      = ∑ n ∈ Finset.Icc 1 M, ∑ p ∈ P,
          (if p * p ∣ n then moebiusPhase w n / ((primeFactorsIn P n).card : ℂ) else 0) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun p _ => by rw [Finset.sum_filter]
  rw [hswap, logPoly]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, ← sqMultCount]
  rw [sqMultCoeff, moebiusPhase, unitLogPhase]
  push_cast
  ring

/-- **The exact three-way Ramaré decomposition of the Möbius Dirichlet polynomial.** -/
theorem logPoly_moebius_eq_ramare_decomp {P : Finset ℕ} (hPprime : ∀ q ∈ P, q.Prime) (M : ℕ)
    (w : ℝ) :
    logPoly (fun n => ((μ n : ℤ) : ℂ)) (Finset.Icc 1 M) w
      = ramareBilinear P M w
        + logPoly (sqMultCoeff P) (Finset.Icc 1 M) w
        + logPoly (fun n => ((μ n : ℤ) : ℂ)) (roughSet P M) w := by
  classical
  have hinner : ∀ p ∈ P,
      ∑ n ∈ {n ∈ Finset.Icc 1 M | p ∣ n}, moebiusPhase w n / ((primeFactorsIn P n).card : ℂ)
        = ∑ m ∈ ramareCofactorSet (Finset.Icc 1 M) p,
            moebiusPhase w (p * m) / ((primeFactorsIn P (p * m)).card : ℂ) :=
    fun p _ => (sum_div_image_complex p {n ∈ Finset.Icc 1 M | p ∣ n}
      (fun n hn => (Finset.mem_filter.1 hn).2)
      (fun n => moebiusPhase w n / ((primeFactorsIn P n).card : ℂ))).symm
  have hsplit : ∀ p ∈ P,
      (∑ m ∈ ramareCofactorSet (Finset.Icc 1 M) p,
          moebiusPhase w (p * m) / ((primeFactorsIn P (p * m)).card : ℂ))
        = moebiusPhase w p
            * (∑ m ∈ {m ∈ ramareCofactorSet (Finset.Icc 1 M) p | ¬ p ∣ m},
                moebiusPhase w m / (((primeFactorsIn P m).card : ℂ) + 1))
          + ∑ m ∈ {m ∈ ramareCofactorSet (Finset.Icc 1 M) p | p ∣ m},
              moebiusPhase w (p * m) / ((primeFactorsIn P (p * m)).card : ℂ) := by
    intro p hp
    exact sum_ramare_bilinear_split_complex hPprime (moebiusPhase_mul_of_coprime w)
      (hPprime p hp) hp _
  rw [logPoly_moebius_eq_sum_moebiusPhase,
    sum_eq_ramare_add_rough_complex P (Finset.Icc 1 M) (moebiusPhase w),
    Finset.sum_congr rfl hinner, Finset.sum_congr rfl hsplit, Finset.sum_add_distrib,
    sum_ramare_remainder_eq_sqMult hPprime M w]
  have hbil : ∑ p ∈ P, moebiusPhase w p
        * (∑ m ∈ {m ∈ ramareCofactorSet (Finset.Icc 1 M) p | ¬ p ∣ m},
            moebiusPhase w m / (((primeFactorsIn P m).card : ℂ) + 1))
      = ramareBilinear P M w := by
    rw [ramareBilinear]
    exact Finset.sum_congr rfl fun p _ => by rw [sum_moebiusPhase_div_eq_logPoly]
  have hrough : ∑ n ∈ {n ∈ Finset.Icc 1 M | primeFactorsIn P n = ∅}, moebiusPhase w n
      = logPoly (fun n => ((μ n : ℤ) : ℂ)) (roughSet P M) w := by
    rw [roughSet, logPoly_moebius_eq_sum_moebiusPhase]
  rw [hbil, hrough]

/-- A weighted triangle inequality for squared norms: the main term keeps a factor `1 + δ`. -/
theorem normSq_add_le_weighted (a u : ℂ) {δ : ℝ} (hδ : 0 < δ) :
    ‖a + u‖ ^ 2 ≤ (1 + δ) * ‖a‖ ^ 2 + (1 + 1 / δ) * ‖u‖ ^ 2 := by
  have h2 : ‖a + u‖ ^ 2 ≤ (‖a‖ + ‖u‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (norm_add_le a u) 2
  have h3 : 2 * ‖a‖ * ‖u‖ ≤ δ * ‖a‖ ^ 2 + (1 / δ) * ‖u‖ ^ 2 := by
    rw [← sub_nonneg]
    have hid : δ * ‖a‖ ^ 2 + (1 / δ) * ‖u‖ ^ 2 - 2 * ‖a‖ * ‖u‖
        = (1 / δ) * (δ * ‖a‖ - ‖u‖) ^ 2 := by
      field_simp
      ring
    rw [hid]
    positivity
  nlinarith [h2, h3]

/-- **The Möbius mean square splits into the bilinear form and two negligible polynomials.** -/
theorem integral_Icc_normSq_logPoly_moebius_le_decomp {P : Finset ℕ}
    (hPprime : ∀ q ∈ P, q.Prime) (M : ℕ) {W δ : ℝ} (hW : 1 ≤ W) (hδ : 0 < δ) :
    (∫ w in Set.Icc (-W) W, ‖logPoly (fun n => ((μ n : ℤ) : ℂ)) (Finset.Icc 1 M) w‖ ^ 2)
      ≤ (1 + δ) * (∫ w in Set.Icc (-W) W, ‖ramareBilinear P M w‖ ^ 2)
        + 2 * (1 + 1 / δ)
            * ((∫ w in Set.Icc (-W) W, ‖logPoly (sqMultCoeff P) (Finset.Icc 1 M) w‖ ^ 2)
              + (∫ w in Set.Icc (-W) W,
                  ‖logPoly (fun n => ((μ n : ℤ) : ℂ)) (roughSet P M) w‖ ^ 2)) := by
  classical
  have hW0 : (0 : ℝ) < W := lt_of_lt_of_le zero_lt_one hW
  have hcontF : Continuous fun w : ℝ =>
      ‖logPoly (fun n => ((μ n : ℤ) : ℂ)) (Finset.Icc 1 M) w‖ ^ 2 :=
    ((continuous_logPoly _ _).norm).pow 2
  have hcontB : Continuous fun w : ℝ => ‖ramareBilinear P M w‖ ^ 2 :=
    ((continuous_ramareBilinear P M).norm).pow 2
  have hcontS : Continuous fun w : ℝ => ‖logPoly (sqMultCoeff P) (Finset.Icc 1 M) w‖ ^ 2 :=
    ((continuous_logPoly _ _).norm).pow 2
  have hcontR : Continuous fun w : ℝ =>
      ‖logPoly (fun n => ((μ n : ℤ) : ℂ)) (roughSet P M) w‖ ^ 2 :=
    ((continuous_logPoly _ _).norm).pow 2
  set F : ℝ → ℝ := fun w =>
    (1 + δ) * ‖ramareBilinear P M w‖ ^ 2
      + 2 * (1 + 1 / δ) * (‖logPoly (sqMultCoeff P) (Finset.Icc 1 M) w‖ ^ 2
        + ‖logPoly (fun n => ((μ n : ℤ) : ℂ)) (roughSet P M) w‖ ^ 2) with hFdef
  have hcontMaj : Continuous F := by
    rw [hFdef]
    exact (hcontB.const_mul _).add ((hcontS.add hcontR).const_mul _)
  have hle : ∀ w ∈ Set.Icc (-W) W,
      ‖logPoly (fun n => ((μ n : ℤ) : ℂ)) (Finset.Icc 1 M) w‖ ^ 2 ≤ F w := by
    intro w _
    rw [logPoly_moebius_eq_ramare_decomp hPprime M w, hFdef]
    have hgroup : ramareBilinear P M w + logPoly (sqMultCoeff P) (Finset.Icc 1 M) w
        + logPoly (fun n => ((μ n : ℤ) : ℂ)) (roughSet P M) w
        = ramareBilinear P M w + (logPoly (sqMultCoeff P) (Finset.Icc 1 M) w
            + logPoly (fun n => ((μ n : ℤ) : ℂ)) (roughSet P M) w) := by ring
    rw [hgroup]
    refine le_trans (normSq_add_le_weighted _ _ hδ) ?_
    have hpair : ‖logPoly (sqMultCoeff P) (Finset.Icc 1 M) w
          + logPoly (fun n => ((μ n : ℤ) : ℂ)) (roughSet P M) w‖ ^ 2
        ≤ 2 * (‖logPoly (sqMultCoeff P) (Finset.Icc 1 M) w‖ ^ 2
            + ‖logPoly (fun n => ((μ n : ℤ) : ℂ)) (roughSet P M) w‖ ^ 2) := by
      have h1 := pow_le_pow_left₀ (norm_nonneg _)
        (norm_add_le (logPoly (sqMultCoeff P) (Finset.Icc 1 M) w)
          (logPoly (fun n => ((μ n : ℤ) : ℂ)) (roughSet P M) w)) 2
      nlinarith [h1, sq_nonneg (‖logPoly (sqMultCoeff P) (Finset.Icc 1 M) w‖
        - ‖logPoly (fun n => ((μ n : ℤ) : ℂ)) (roughSet P M) w‖)]
    have hc0 : (0 : ℝ) ≤ 1 + 1 / δ := by positivity
    nlinarith [hpair, hc0]
  have hintF : IntegrableOn (fun w : ℝ =>
      ‖logPoly (fun n => ((μ n : ℤ) : ℂ)) (Finset.Icc 1 M) w‖ ^ 2)
      (Set.Icc (-W) W) volume := hcontF.integrableOn_Icc
  have hintMaj : IntegrableOn F (Set.Icc (-W) W) volume := hcontMaj.integrableOn_Icc
  have hmono := setIntegral_mono_on hintF hintMaj measurableSet_Icc hle
  have hintB : IntegrableOn (fun w : ℝ => ‖ramareBilinear P M w‖ ^ 2)
      (Set.Icc (-W) W) volume := hcontB.integrableOn_Icc
  have hintS : IntegrableOn (fun w : ℝ => ‖logPoly (sqMultCoeff P) (Finset.Icc 1 M) w‖ ^ 2)
      (Set.Icc (-W) W) volume := hcontS.integrableOn_Icc
  have hintR : IntegrableOn (fun w : ℝ =>
      ‖logPoly (fun n => ((μ n : ℤ) : ℂ)) (roughSet P M) w‖ ^ 2)
      (Set.Icc (-W) W) volume := hcontR.integrableOn_Icc
  have h1 : IntegrableOn (fun w : ℝ => (1 + δ) * ‖ramareBilinear P M w‖ ^ 2)
      (Set.Icc (-W) W) volume := hintB.const_mul _
  have h2 : IntegrableOn (fun w : ℝ => 2 * (1 + 1 / δ) *
      (‖logPoly (sqMultCoeff P) (Finset.Icc 1 M) w‖ ^ 2
        + ‖logPoly (fun n => ((μ n : ℤ) : ℂ)) (roughSet P M) w‖ ^ 2))
      (Set.Icc (-W) W) volume := (hintS.add hintR).const_mul _
  refine le_trans hmono (le_of_eq ?_)
  show (∫ w in Set.Icc (-W) W, ((1 + δ) * ‖ramareBilinear P M w‖ ^ 2
      + 2 * (1 + 1 / δ) * (‖logPoly (sqMultCoeff P) (Finset.Icc 1 M) w‖ ^ 2
        + ‖logPoly (fun n => ((μ n : ℤ) : ℂ)) (roughSet P M) w‖ ^ 2))) = _
  rw [integral_add h1 h2, integral_const_mul, integral_const_mul, integral_add hintS hintR]

/-- **Everything except the bilinear form is inside the budget.**  With the designated primes
carrying harmonic mass `A ≥ 15e/(2ε)`, numbering at most `M`, and satisfying
`M·∑_{p ∈ P} p^{-2} ≤ ε·M`, the Möbius mean square is the bilinear one up to `O(W·M) + O(ε·M²)`. -/
theorem integral_Icc_normSq_logPoly_moebius_le_bilinear_budget {P : Finset ℕ}
    (hPprime : ∀ q ∈ P, q.Prime) (M : ℕ) {W δ ε : ℝ} (hW : 1 ≤ W) (hδ : 0 < δ)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hPM : (P.card : ℝ) ≤ (M : ℝ))
    (hA : 15 * Real.exp 1 / (2 * ε) ≤ ∑ p ∈ P, (1 : ℝ) / (p : ℝ))
    (hsq : ∑ p ∈ P, (M : ℝ) / ((p : ℝ) * (p : ℝ)) ≤ ε * (M : ℝ)) :
    (∫ w in Set.Icc (-W) W, ‖logPoly (fun n => ((μ n : ℤ) : ℂ)) (Finset.Icc 1 M) w‖ ^ 2)
      ≤ (1 + δ) * (∫ w in Set.Icc (-W) W, ‖ramareBilinear P M w‖ ^ 2)
        + 2 * (1 + 1 / δ)
            * (12 * W * (M : ℝ) + (1 + 5 * Real.exp 1 / 2) * ε * (M : ℝ) ^ 2) := by
  have hW0 : (0 : ℝ) < W := lt_of_lt_of_le zero_lt_one hW
  have hM0 : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
  have hpi : Real.pi ≤ 4 := Real.pi_le_four
  have hE : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  have hsqm : (∫ w in Set.Icc (-W) W, ‖logPoly (sqMultCoeff P) (Finset.Icc 1 M) w‖ ^ 2)
      ≤ 10 * W * (M : ℝ) + 5 * Real.exp 1 / 2 * ε * (M : ℝ) ^ 2 := by
    refine le_trans (integral_Icc_normSq_sqMultPoly_le P M hW) ?_
    have hc0 : (0 : ℝ) ≤ 5 * Real.pi / 2 * W + 5 * Real.exp 1 / 2 * (M : ℝ) := by
      have := Real.pi_pos
      positivity
    refine le_trans (mul_le_mul_of_nonneg_left hsq hc0) ?_
    have hexpand : (5 * Real.pi / 2 * W + 5 * Real.exp 1 / 2 * (M : ℝ)) * (ε * (M : ℝ))
        = (5 * Real.pi / 2 * ε) * (W * (M : ℝ)) + 5 * Real.exp 1 / 2 * ε * (M : ℝ) ^ 2 := by
      ring
    rw [hexpand]
    have hkey : 5 * Real.pi / 2 * ε ≤ 10 := by
      nlinarith [hpi, hε, hε1, mul_le_mul_of_nonneg_right hpi hε.le]
    have hWM : (0 : ℝ) ≤ W * (M : ℝ) := by positivity
    linarith [mul_le_mul_of_nonneg_right hkey hWM]
  have hro := integral_Icc_normSq_roughPoly_le_budget hPprime M hW hε hε1 hPM hA
  refine le_trans (integral_Icc_normSq_logPoly_moebius_le_decomp hPprime M hW hδ) ?_
  have hc0 : (0 : ℝ) ≤ 2 * (1 + 1 / δ) := by positivity
  refine add_le_add le_rfl (mul_le_mul_of_nonneg_left ?_ hc0)
  linarith [hsqm, hro]

end RHTower.Sieve

end
