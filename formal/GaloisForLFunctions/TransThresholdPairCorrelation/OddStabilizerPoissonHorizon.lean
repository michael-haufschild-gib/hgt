import GaloisForLFunctions.RHTower.Sieve.SquarefreeTotientLogMean
import GaloisForLFunctions.TransThresholdPairCorrelation.ParitySensitiveRamanujanStabilizerTransfer
import GaloisForLFunctions.RHTower.Sieve.ReciprocalTotientLogBound
import GaloisForLFunctions.RHTower.DirichletSummatorySwap
import Mathlib.NumberTheory.ArithmeticFunction.Misc

/-!
# The signed odd-stabilizer row at its Poisson horizon

The cotangent conductor coefficients have summatory bound `64Q`, obtained
from the multiplicative majorant `zeta * (mu²/phi)³`. At `Q=floor(m/b)`
this leaves a bounded error, while the odd reciprocal-totient main term
has exact logarithmic coefficient one half. Endpoint errors stay explicit.
-/

noncomputable section
open Finset ArithmeticFunction MeasureTheory Filter Topology Real
open RHTower.Sieve

namespace GaloisForLFunctions.TransThresholdPairCorrelation

private theorem convolution_nonneg (f g : ArithmeticFunction ℝ)
    (hf : ∀ n, 0 ≤ f n) (hg : ∀ n, 0 ≤ g n) (n : ℕ) : 0 ≤ (f * g) n := by
  rw [ArithmeticFunction.mul_apply]
  exact Finset.sum_nonneg fun p _ => mul_nonneg (hf p.1) (hg p.2)

private def harmonicTwist (f : ArithmeticFunction ℝ) : ArithmeticFunction ℝ :=
  ⟨fun n => f n / (n : ℝ), by simp⟩

private theorem harmonicTwist_mul (f g : ArithmeticFunction ℝ) :
    harmonicTwist (f * g) = harmonicTwist f * harmonicTwist g := by
  ext n
  change (f * g) n / (n : ℝ) = _
  rw [ArithmeticFunction.mul_apply, Finset.sum_div, ArithmeticFunction.mul_apply]
  refine Finset.sum_congr rfl fun p hp => ?_
  have hn : (n : ℝ) = (p.1 : ℝ) * (p.2 : ℝ) := by
    exact_mod_cast (Nat.mem_divisorsAntidiagonal.mp hp).1.symm
  change f p.1 * g p.2 / (n : ℝ) = (f p.1 / (p.1 : ℝ)) * (g p.2 / (p.2 : ℝ))
  rw [hn, div_mul_div_comm]

private theorem convolution_mass_le (f g : ArithmeticFunction ℝ)
    (hf : ∀ n, 0 ≤ f n) (hg : ∀ n, 0 ≤ g n) (N : ℕ) :
    (∑ n ∈ Icc 1 N, (f * g) n) ≤
      (∑ n ∈ Icc 1 N, f n) * (∑ n ∈ Icc 1 N, g n) := by
  rw [RHTower.sum_Icc_mul_apply, Finset.sum_mul]
  refine Finset.sum_le_sum fun d _ => mul_le_mul_of_nonneg_left ?_ (hf d)
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.Icc_subset_Icc le_rfl (Nat.div_le_self N d)) (fun n _ _ => hg n)

private theorem harmonic_convolution_mass_le (f g : ArithmeticFunction ℝ)
    (hf : ∀ n, 0 ≤ f n) (hg : ∀ n, 0 ≤ g n) (N : ℕ) :
    (∑ n ∈ Icc 1 N, (f * g) n / (n : ℝ)) ≤
      (∑ n ∈ Icc 1 N, f n / (n : ℝ)) * (∑ n ∈ Icc 1 N, g n / (n : ℝ)) := by
  change (∑ n ∈ Icc 1 N, harmonicTwist (f * g) n) ≤ _
  rw [harmonicTwist_mul]
  exact convolution_mass_le (harmonicTwist f) (harmonicTwist g)
    (fun n => div_nonneg (hf n) (Nat.cast_nonneg n))
    (fun n => div_nonneg (hg n) (Nat.cast_nonneg n)) N

private def conductorWeight : ArithmeticFunction ℝ :=
  ⟨fun q => sqfreeTotientInv q ^ 2 * (ArithmeticFunction.sigma 2 q : ℝ), by simp⟩

private theorem conductorWeight_nonneg (q : ℕ) : 0 ≤ conductorWeight q := by
  exact mul_nonneg (sq_nonneg _) (Nat.cast_nonneg _)

private theorem conductorWeight_multiplicative : conductorWeight.IsMultiplicative := by
  constructor
  · simp [conductorWeight, sqfreeTotientInv_apply]
  · intro m n hmn
    change sqfreeTotientInv (m * n) ^ 2 * (ArithmeticFunction.sigma 2 (m * n) : ℝ) = _
    rw [isMultiplicative_sqfreeTotientInv.map_mul_of_coprime hmn,
      ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hmn, Nat.cast_mul]
    change _ = (sqfreeTotientInv m ^ 2 * (ArithmeticFunction.sigma 2 m : ℝ)) *
      (sqfreeTotientInv n ^ 2 * (ArithmeticFunction.sigma 2 n : ℝ))
    ring

private theorem convolution_prime (f g : ArithmeticFunction ℝ) {p : ℕ} (hp : p.Prime) :
    (f * g) p = f 1 * g p + f p * g 1 := by
  rw [ArithmeticFunction.mul_apply, Nat.sum_divisorsAntidiagonal (fun a b => f a * g b)]
  rw [hp.divisors, Finset.sum_pair (Ne.symm hp.ne_one)]
  simp only [Nat.div_one, Nat.div_self hp.pos]

private theorem sqfreeTotientInv_prime {p : ℕ} (hp : p.Prime) :
    sqfreeTotientInv p = 1 / ((p : ℝ) - 1) := by
  rw [sqfreeTotientInv_apply, if_pos hp.squarefree, Nat.totient_prime hp,
    Nat.cast_sub hp.one_lt.le, Nat.cast_one]

private theorem sqfreeTotientInv_prime_pow_zero {p i : ℕ} (hp : p.Prime) (hi : 2 ≤ i) :
    sqfreeTotientInv (p ^ i) = 0 := by
  rw [sqfreeTotientInv_apply, if_neg]
  intro hsq
  have hdvd : p * p ∣ p ^ i := by simpa only [pow_two] using pow_dvd_pow p hi
  have hu := hsq p hdvd
  exact hp.ne_one (Nat.isUnit_iff.mp hu)

private theorem conductorWeight_prime {p : ℕ} (hp : p.Prime) :
    conductorWeight p = (1 / ((p : ℝ) - 1)) ^ 2 * (1 + (p : ℝ) ^ 2) := by
  change sqfreeTotientInv p ^ 2 * (ArithmeticFunction.sigma 2 p : ℝ) = _
  rw [sqfreeTotientInv_prime hp, ArithmeticFunction.sigma_apply, hp.divisors,
    Finset.sum_pair (Ne.symm hp.ne_one)]
  push_cast
  ring


private theorem prime_conductor_comparison (p : ℝ) (hp : 3 ≤ p) :
    (1 / (p - 1)) ^ 2 * (1 + p ^ 2) ≤ 1 + 3 / (p - 1) := by
  have hpos : 0 < p - 1 := by linarith only [hp]
  have he : (1 + 3 / (p - 1)) * (p - 1) ^ 2 = (p - 1) ^ 2 + 3 * (p - 1) := by
    field_simp
  calc
    (1 / (p - 1)) ^ 2 * (1 + p ^ 2) = (1 + p ^ 2) / (p - 1) ^ 2 := by
      simp only [div_pow, one_pow]
      ring
    _ ≤ 1 + 3 / (p - 1) := by
      rw [div_le_iff₀ (sq_pos_of_pos hpos), he]
      nlinarith only [hp]

-- Three convolution factors dominate the extra Euler factor at every odd prime.
private def conductorMajorant : ArithmeticFunction ℝ :=
  ((ArithmeticFunction.zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℝ) *
    ((sqfreeTotientInv * sqfreeTotientInv) * sqfreeTotientInv)

private theorem conductorMajorant_multiplicative : conductorMajorant.IsMultiplicative :=
  ArithmeticFunction.isMultiplicative_zeta.natCast.mul
    ((isMultiplicative_sqfreeTotientInv.mul isMultiplicative_sqfreeTotientInv).mul
      isMultiplicative_sqfreeTotientInv)

private theorem conductorMajorant_nonneg (n : ℕ) : 0 ≤ conductorMajorant n :=
  convolution_nonneg _ _ (fun _ => Nat.cast_nonneg _)
    (convolution_nonneg _ _
      (convolution_nonneg _ _ sqfreeTotientInv_nonneg sqfreeTotientInv_nonneg)
      sqfreeTotientInv_nonneg) n

private theorem conductorMajorant_prime {p : ℕ} (hp : p.Prime) :
    conductorMajorant p = 1 + 3 / ((p : ℝ) - 1) := by
  unfold conductorMajorant
  rw [convolution_prime _ _ hp, convolution_prime _ _ hp, convolution_prime _ _ hp]
  simp only [ArithmeticFunction.mul_apply_one]
  have hg1 : sqfreeTotientInv 1 = 1 := isMultiplicative_sqfreeTotientInv.1
  rw [hg1, sqfreeTotientInv_prime hp]
  simp only [ArithmeticFunction.natCoe_apply, ArithmeticFunction.zeta_apply,
    if_neg hp.ne_zero, if_neg (by norm_num : (1 : ℕ) ≠ 0), Nat.cast_one]
  ring

private theorem conductorWeight_prime_pow_le {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (i : ℕ) :
    conductorWeight (p ^ i) ≤ conductorMajorant (p ^ i) := by
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · rw [pow_zero, conductorWeight_multiplicative.1, conductorMajorant_multiplicative.1]
  · by_cases hi1 : i = 1
    · subst i
      rw [pow_one, conductorWeight_prime hp, conductorMajorant_prime hp]
      exact prime_conductor_comparison p (by exact_mod_cast hp3)
    · change sqfreeTotientInv (p ^ i) ^ 2 * (ArithmeticFunction.sigma 2 (p ^ i) : ℝ) ≤ _
      rw [sqfreeTotientInv_prime_pow_zero hp (by omega), zero_pow (by decide), zero_mul]
      exact conductorMajorant_nonneg _

private theorem conductorWeight_le_majorant {n : ℕ} (hn : n % 2 = 1) :
    conductorWeight n ≤ conductorMajorant n := by
  have hn0 : n ≠ 0 := by omega
  rw [conductorWeight_multiplicative.multiplicative_factorization _ hn0,
    conductorMajorant_multiplicative.multiplicative_factorization _ hn0]
  apply Finset.prod_le_prod
  · intro p _
    exact conductorWeight_nonneg _
  · intro p hp
    have hpP := Nat.prime_of_mem_primeFactors hp
    have hpd := Nat.dvd_of_mem_primeFactors hp
    have hp3 : 3 ≤ p := by
      have hp2 := hpP.two_le
      have hpne : p ≠ 2 := by
        intro h
        subst p
        obtain ⟨k, hk⟩ := hpd
        omega
      omega
    exact conductorWeight_prime_pow_le hpP hp3 _

-- Each reciprocal convolution factor has harmonic mass at most four.
private theorem triple_harmonic_mass_le (N : ℕ) :
    (∑ n ∈ Icc 1 N, ((sqfreeTotientInv * sqfreeTotientInv) * sqfreeTotientInv) n /
      (n : ℝ)) ≤ 64 := by
  have h0 : 0 ≤ ∑ n ∈ Icc 1 N, sqfreeTotientInv n / (n : ℝ) :=
    Finset.sum_nonneg fun n _ => div_nonneg (sqfreeTotientInv_nonneg n) (Nat.cast_nonneg n)
  have h4 := sum_sqfreeTotientInv_div_le N
  have h2 : (∑ n ∈ Icc 1 N, (sqfreeTotientInv * sqfreeTotientInv) n / (n : ℝ)) ≤ 16 := by
    calc _ ≤ (∑ n ∈ Icc 1 N, sqfreeTotientInv n / (n : ℝ)) *
          (∑ n ∈ Icc 1 N, sqfreeTotientInv n / (n : ℝ)) :=
        harmonic_convolution_mass_le _ _ sqfreeTotientInv_nonneg sqfreeTotientInv_nonneg N
      _ ≤ 4 * 4 := mul_le_mul h4 h4 h0 (by norm_num)
      _ = 16 := by norm_num
  calc _ ≤ (∑ n ∈ Icc 1 N, (sqfreeTotientInv * sqfreeTotientInv) n / (n : ℝ)) *
        (∑ n ∈ Icc 1 N, sqfreeTotientInv n / (n : ℝ)) :=
      harmonic_convolution_mass_le _ _
        (convolution_nonneg _ _ sqfreeTotientInv_nonneg sqfreeTotientInv_nonneg)
        sqfreeTotientInv_nonneg N
    _ ≤ 16 * 4 := mul_le_mul h2 h4 h0 (by norm_num)
    _ = 64 := by norm_num

private theorem zeta_convolution_mass_le (f : ArithmeticFunction ℝ)
    (hf : ∀ n, 0 ≤ f n) (N : ℕ) :
    (∑ n ∈ Icc 1 N, (((ArithmeticFunction.zeta : ArithmeticFunction ℕ) :
      ArithmeticFunction ℝ) * f) n) ≤ (N : ℝ) * (∑ n ∈ Icc 1 N, f n / (n : ℝ)) := by
  have hz (K : ℕ) : (∑ n ∈ Icc 1 K,
      (((ArithmeticFunction.zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℝ) n)) = (K : ℝ) := by
    calc _ = ∑ n ∈ Icc 1 K, (1 : ℝ) := by
          refine Finset.sum_congr rfl fun n hn => ?_
          have hn0 : n ≠ 0 := Nat.ne_of_gt (Finset.mem_Icc.mp hn).1
          simp only [ArithmeticFunction.natCoe_apply, ArithmeticFunction.zeta_apply,
            if_neg hn0, Nat.cast_one]
      _ = _ := by simp
  rw [mul_comm, RHTower.sum_Icc_mul_apply, Finset.mul_sum]
  refine Finset.sum_le_sum fun d hd => ?_
  rw [hz]
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (Finset.mem_Icc.mp hd).1
  have hdiv : ((N / d : ℕ) : ℝ) ≤ (N : ℝ) / (d : ℝ) := by
    apply (le_div_iff₀ hd0).mpr
    exact_mod_cast Nat.div_mul_le_self N d
  calc f d * ((N / d : ℕ) : ℝ) ≤ f d * ((N : ℝ) / (d : ℝ)) :=
      mul_le_mul_of_nonneg_left hdiv (hf d)
    _ = (N : ℝ) * (f d / (d : ℝ)) := by ring

private theorem conductorWeight_eq (q : ℕ) :
    conductorWeight q = (sqfreeTotientInv q / (q.totient : ℝ)) *
      (∑ d ∈ q.divisors, (d : ℝ) ^ 2) := by
  change sqfreeTotientInv q ^ 2 * (ArithmeticFunction.sigma 2 q : ℝ) = _
  rw [ArithmeticFunction.sigma_apply, Nat.cast_sum]
  simp only [Nat.cast_pow]
  rw [sqfreeTotientInv_apply]
  split_ifs <;> ring

/-- The odd squarefree cotangent coefficients have a uniform linear summatory bound. -/
theorem sum_odd_sqfree_sigma2_totient_sq_le (Q : ℕ) :
    (∑ q ∈ (Icc 1 Q).filter (fun q => q % 2 = 1),
      (sqfreeTotientInv q / (q.totient : ℝ)) * (∑ d ∈ q.divisors, (d : ℝ) ^ 2)) ≤
        64 * (Q : ℝ) := by
  simp only [← conductorWeight_eq]
  calc _ ≤ ∑ q ∈ (Icc 1 Q).filter (fun q => q % 2 = 1), conductorMajorant q :=
      Finset.sum_le_sum fun q hq => conductorWeight_le_majorant (Finset.mem_filter.mp hq).2
    _ ≤ ∑ q ∈ Icc 1 Q, conductorMajorant q :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun n _ _ => conductorMajorant_nonneg n)
    _ ≤ (Q : ℝ) * (∑ n ∈ Icc 1 Q,
        ((sqfreeTotientInv * sqfreeTotientInv) * sqfreeTotientInv) n / (n : ℝ)) :=
      zeta_convolution_mass_le _
        (convolution_nonneg _ _
          (convolution_nonneg _ _ sqfreeTotientInv_nonneg sqfreeTotientInv_nonneg)
          sqfreeTotientInv_nonneg) Q
    _ ≤ (Q : ℝ) * 64 := mul_le_mul_of_nonneg_left (triple_harmonic_mass_le Q) (Nat.cast_nonneg Q)
    _ = 64 * (Q : ℝ) := mul_comm _ _

/-- At the Poisson horizon, the full cotangent conductor error is uniformly bounded. -/
theorem poissonHorizon_conductor_error_le {Ω : ℝ → ℝ} {b m : ℝ}
    (hb : 0 < b) (hbm : b ≤ m) (hΩ0 : ∀ t, 0 ≤ Ω t) :
    (b / m) * cosTransform Ω 0 *
      (1 + ∑ q ∈ (Icc 3 ⌊m / b⌋₊).filter (fun q => q % 2 = 1),
        (sqfreeTotientInv q / (q.totient : ℝ)) * (∑ d ∈ q.divisors, (d : ℝ) ^ 2)) ≤
      64 * cosTransform Ω 0 := by
  have hm : 0 < m := hb.trans_le hbm
  let Q := ⌊m / b⌋₊
  have hQ1 : 1 ≤ Q := (Nat.le_floor_iff (by positivity)).mpr (by
    simpa only [Nat.cast_one] using (one_le_div hb).mpr hbm)
  have hQm : (Q : ℝ) * b ≤ m := by
    exact (mul_le_mul_of_nonneg_right (Nat.floor_le (by positivity : 0 ≤ m / b)) hb.le).trans_eq
      (div_mul_cancel₀ m hb.ne')
  have hset : (Icc 1 Q).filter (fun q => q % 2 = 1) =
      insert 1 ((Icc 3 Q).filter (fun q => q % 2 = 1)) := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_insert]
    omega
  have hraw := sum_odd_sqfree_sigma2_totient_sq_le Q
  rw [hset, Finset.sum_insert (by simp)] at hraw
  have hbase : (sqfreeTotientInv 1 / ((1 : ℕ).totient : ℝ)) *
      (∑ d ∈ (1 : ℕ).divisors, (d : ℝ) ^ 2) = 1 := by
    simp [RHTower.Sieve.sqfreeTotientInv_apply]
  rw [hbase] at hraw
  have hI : 0 ≤ cosTransform Ω 0 := by
    rw [cosTransform_zero_eq_integral]
    exact integral_nonneg hΩ0
  have hpay := mul_le_mul_of_nonneg_left hraw (mul_nonneg (div_nonneg hb.le hm.le) hI)
  have hscale : (b / m) * (Q : ℝ) ≤ 1 := by
    rw [div_mul_eq_mul_div, div_le_one hm]
    linarith only [hQm]
  have hscale' := mul_le_mul_of_nonneg_left hscale (by positivity : 0 ≤ 64 * cosTransform Ω 0)
  change (b / m) * cosTransform Ω 0 *
    (1 + ∑ q ∈ (Icc 3 Q).filter (fun q => q % 2 = 1),
      (sqfreeTotientInv q / (q.totient : ℝ)) * (∑ d ∈ q.divisors, (d : ℝ) ^ 2)) ≤ _
  nlinarith only [hpay, hscale']

/-- The signed dynamic-horizon row retains its negative main term with a conductor-independent error. -/
theorem abs_dynamic_poissonHorizon_row_add_le
    {Ω : ℝ → ℝ} {a b m : ℝ} {R : ℕ → ℕ}
    (ha : 0 < a) (hab : a ≤ b) (hbm : b ≤ m)
    (hR : ∀ q ∈ (Icc 1 ⌊m / b⌋₊).filter (fun q => q % 2 = 1), 1 ≤ R q)
    (hΩ1 : ContDiff ℝ 1 Ω) (hΩ0 : ∀ τ, 0 ≤ Ω τ)
    (hsupp : ∀ τ, τ ∉ Set.Icc a b → Ω τ = 0) :
    |(2 * ∑ q ∈ (Icc 1 ⌊m / b⌋₊).filter (fun q => q % 2 = 1),
          (sqfreeTotientInv q / (q.totient : ℝ)) *
            ∑ r ∈ Icc 1 (q * R q),
              GaloisForLFunctions.BezoutValuationIncidence.ramanujanLagCoefficient q (2 * r) *
                cosTransform Ω (((2 * r : ℕ) : ℝ) / m)) +
        cosTransform Ω 0 *
          ∑ q ∈ (Icc 1 ⌊m / b⌋₊).filter (fun q => q % 2 = 1), sqfreeTotientInv q| ≤
      (∑ q ∈ (Icc 1 ⌊m / b⌋₊).filter (fun q => q % 2 = 1),
        sqfreeTotientInv q * |cosTransform Ω (((2 * (q * R q) : ℕ) : ℝ) / m)|) +
      64 * cosTransform Ω 0 +
      (m ^ 2 / (2 * (R 1 : ℝ) * a ^ 2)) * ∫ τ in a..b, (a * |deriv Ω τ| + Ω τ) := by
  have h := abs_sum_dynamic_poissonHorizon_singularSeries_add_le ha hab hbm hR hΩ1 hΩ0 hsupp
  have hc := poissonHorizon_conductor_error_le (ha.trans_le hab) hbm hΩ0
  linarith only [h, hc]


private theorem odd_totient_sum_mono {M N : ℕ} (hMN : M ≤ N) :
    (∑ q ∈ (Icc 1 M).filter (fun q => q % 2 = 1), sqfreeTotientInv q) ≤
      ∑ q ∈ (Icc 1 N).filter (fun q => q % 2 = 1), sqfreeTotientInv q := by
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.filter_subset_filter _ (Finset.Icc_subset_Icc le_rfl hMN))
    (fun q _ _ => sqfreeTotientInv_nonneg q)

private theorem two_mul_odd_totient_sum_le_double_full (Q : ℕ) :
    2 * (∑ q ∈ (Icc 1 Q).filter (fun q => q % 2 = 1), sqfreeTotientInv q) ≤
      ∑ q ∈ Icc 1 (2 * Q), sqfreeTotientInv q := by
  rw [sum_sqfreeTotientInv_eq_odd_add_half_odd]
  have hhalf : 2 * Q / 2 = Q := by omega
  rw [hhalf]
  have h := odd_totient_sum_mono (show Q ≤ 2 * Q by omega)
  linarith only [h]

private theorem log_double_ratio_tendsto :
    Tendsto (fun Q : ℕ => Real.log (2 * Q : ℕ) / Real.log Q) atTop (𝓝 1) := by
  have hlog : Tendsto (fun Q : ℕ => Real.log Q) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have h := ((tendsto_const_nhds :
    Tendsto (fun _ : ℕ => Real.log 2) atTop (𝓝 (Real.log 2))).div_atTop hlog).add
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1))
  have h' : Tendsto (fun Q : ℕ => Real.log 2 / Real.log Q + 1) atTop (𝓝 1) := by
    simpa only [zero_add] using h
  apply h'.congr'
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with Q hQ
  have hQ0 : (Q : ℝ) ≠ 0 := by exact_mod_cast (show Q ≠ 0 by omega)
  have hQ1 : (1 : ℝ) < Q := by exact_mod_cast (show 1 < Q by omega)
  rw [Nat.cast_mul, Nat.cast_two, Real.log_mul (by norm_num) hQ0, add_div,
    div_self (Real.log_pos hQ1).ne']

/-- The odd squarefree reciprocal-totient sum has exact logarithmic mean one half. -/
theorem tendsto_sum_odd_sqfreeTotientInv_div_log_half :
    Tendsto (fun Q : ℕ =>
      (∑ q ∈ (Icc 1 Q).filter (fun q => q % 2 = 1), sqfreeTotientInv q) / Real.log Q)
      atTop (𝓝 (1 / 2 : ℝ)) := by
  have hdouble : Tendsto (fun Q : ℕ => 2 * Q) atTop atTop := by
    refine tendsto_atTop.2 fun n => ?_
    filter_upwards [eventually_ge_atTop n] with Q hQ
    omega
  have hF := tendsto_sum_sqfreeTotientInv_div_log_one
  have hF2 := (hF.comp hdouble).mul log_double_ratio_tendsto
  have hF2' : Tendsto (fun Q : ℕ =>
      (∑ n ∈ Icc 1 (2 * Q), sqfreeTotientInv n) / Real.log Q) atTop (𝓝 1) := by
    have hh : Tendsto (fun Q : ℕ =>
        ((∑ n ∈ Icc 1 (2 * Q), sqfreeTotientInv n) / Real.log (2 * Q : ℕ)) *
          (Real.log (2 * Q : ℕ) / Real.log Q)) atTop (𝓝 1) := by
      simpa only [one_mul, Function.comp_apply] using hF2
    apply hh.congr'
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with Q hQ
    have hlog : Real.log (2 * Q : ℕ) ≠ 0 := by
      exact (Real.log_pos (by exact_mod_cast (show 1 < 2 * Q by omega))).ne'
    field_simp [hlog]
  -- Parity squeezes twice the odd mass between the full masses at Q and 2Q.
  have htwo : Tendsto (fun Q : ℕ =>
      2 * (∑ q ∈ (Icc 1 Q).filter (fun q => q % 2 = 1), sqfreeTotientInv q) / Real.log Q)
      atTop (𝓝 1) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hF hF2'
    · filter_upwards [eventually_ge_atTop (2 : ℕ)] with Q hQ
      exact div_le_div_of_nonneg_right (sum_sqfreeTotientInv_le_two_mul_sum_odd Q)
        (Real.log_nonneg (by exact_mod_cast (show 1 ≤ Q by omega)))
    · filter_upwards [eventually_ge_atTop (2 : ℕ)] with Q hQ
      exact div_le_div_of_nonneg_right (two_mul_odd_totient_sum_le_double_full Q)
        (Real.log_nonneg (by exact_mod_cast (show 1 ≤ Q by omega)))
  have h := htwo.div_const 2
  convert h using 1
  funext Q
  ring

end GaloisForLFunctions.TransThresholdPairCorrelation
