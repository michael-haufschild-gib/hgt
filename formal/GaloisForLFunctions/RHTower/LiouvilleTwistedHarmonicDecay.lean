import GaloisForLFunctions.RHTower.Sieve.MoebiusHarmonicArbitraryLogRate
import GaloisForLFunctions.RHTower.LiouvilleDirichletSeries
import GaloisForLFunctions.HTGeometry.ZetaVerticalAlmostPeriodic
import GaloisForLFunctions.RHTower.LiouvilleTwistedDensityPhase
import Mathlib.NumberTheory.ArithmeticFunction.LFunction

/-!
# Harmonic cancellation for Liouville and its prime-two twist

The unconditional Mobius harmonic logarithmic limit transfers through the exact
square-dilation identity to Liouville. A second exact convolution, supported on powers
of two, transfers it to the completely multiplicative source with value `I` at two
and value `-1` at every other prime.

Both kernels have a summable absolute logarithmic moment. Dominated convergence
therefore retains the full source without an unproved uniform tail estimate. The final
limits have no analytic or arithmetic hypotheses. They supply the harmonic cancellation
input for MC-C12.92; the exponential-density transfer and moving-prime simple-zero
argument are separate obligations. This is not a critical power estimate or an RH proof.
-/

open ArithmeticFunction Filter
open scoped Topology BigOperators

namespace RHTower.LiouvilleHarmonic

noncomputable section

def harmonicCoeff (f : ArithmeticFunction ℂ) : ArithmeticFunction ℂ where
  toFun n := f n / n
  map_zero' := by simp

def harmonic (f : ArithmeticFunction ℂ) (N : ℕ) : ℂ :=
  ∑ n ∈ Finset.range (N + 1), f n / n

@[simp] theorem harmonic_zero (f : ArithmeticFunction ℂ) : harmonic f 0 = 0 := by
  simp [harmonic]

private theorem harmonicCoeff_mul (f g : ArithmeticFunction ℂ) :
    harmonicCoeff (f * g) = harmonicCoeff f * harmonicCoeff g := by
  ext n
  simp only [harmonicCoeff, ArithmeticFunction.coe_mk, ArithmeticFunction.mul_apply]
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun p hp => ?_
  have hmul := (Nat.mem_divisorsAntidiagonal.mp hp).1
  rw [← hmul, Nat.cast_mul]
  ring

private theorem harmonic_eq_Ioc (f : ArithmeticFunction ℂ) (N : ℕ) :
    harmonic f N = ∑ n ∈ Finset.Ioc 0 N, harmonicCoeff f n := by
  have hset : Finset.range (N + 1) = insert 0 (Finset.Ioc 0 N) := by
    ext n
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ioc]
    omega
  rw [harmonic, hset, Finset.sum_insert (by simp)]
  simp only [Nat.cast_zero, div_zero, zero_add]
  rfl

theorem harmonic_mul (f g : ArithmeticFunction ℂ) (N : ℕ) :
    harmonic (f * g) N =
      ∑ d ∈ Finset.Ioc 0 N, f d / d * harmonic g (N / d) := by
  rw [harmonic_eq_Ioc, harmonicCoeff_mul,
    ArithmeticFunction.sum_Ioc_mul_eq_sum_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [← harmonic_eq_Ioc]
  rfl

private def squares : ArithmeticFunction ℂ :=
  (ArithmeticFunction.zeta : ArithmeticFunction ℂ) * RHTower.liouvilleC

private theorem squares_apply {n : ℕ} (hn : n ≠ 0) :
    squares n = RHTower.squareIndicator n := by
  rw [squares, ArithmeticFunction.coe_zeta_mul_apply,
    RHTower.sum_divisors_liouvilleC hn]

private theorem squares_mul_moebius :
    squares * (ArithmeticFunction.moebius : ArithmeticFunction ℂ) = RHTower.liouvilleC := by
  rw [squares, mul_right_comm, ArithmeticFunction.coe_zeta_mul_coe_moebius, one_mul]

theorem harmonic_liouville_eq_square_dilation (N : ℕ) :
    harmonic RHTower.liouvilleC N =
      ∑' k : ℕ, (1 / (k : ℂ) ^ 2) *
        harmonic (ArithmeticFunction.moebius : ArithmeticFunction ℂ) (N / k ^ 2) := by
  let F : ℕ → ℂ := fun d => RHTower.squareIndicator d / d *
    harmonic (ArithmeticFunction.moebius : ArithmeticFunction ℂ) (N / d)
  have hfinite : harmonic RHTower.liouvilleC N = ∑ d ∈ Finset.Ioc 0 N, F d := by
    rw [← squares_mul_moebius, harmonic_mul]
    refine Finset.sum_congr rfl fun d hd => ?_
    rw [squares_apply (by have := (Finset.mem_Ioc.mp hd).1; omega)]
  have htsum : ∑' d : ℕ, F d = ∑ d ∈ Finset.Ioc 0 N, F d := by
    apply tsum_eq_sum
    intro d hd
    by_cases hd0 : d = 0
    · simp [F, hd0]
    · have hNd : N < d := by simpa [Finset.mem_Ioc, Nat.pos_of_ne_zero hd0] using hd
      simp [F, Nat.div_eq_of_lt hNd]
  have hsupp : Function.support F ⊆ Set.range (fun k : ℕ => k ^ 2) := by
    intro d hd
    have hsq : IsSquare d := by
      by_contra h
      exact hd (by simp [F, RHTower.squareIndicator, h])
    obtain ⟨k, hk⟩ := hsq
    exact ⟨k, by rw [hk]; ring⟩
  rw [hfinite, ← htsum, ← Function.Injective.tsum_eq
    (g := fun k : ℕ => k ^ 2)
    (fun p q h => by simpa using Nat.pow_left_injective (by norm_num) h) hsupp]
  refine tsum_congr fun k => ?_
  simp [F, RHTower.squareIndicator, show IsSquare (k ^ 2) from ⟨k, by ring⟩]

theorem harmonic_moebius_eq (N : ℕ) :
    harmonic (ArithmeticFunction.moebius : ArithmeticFunction ℂ) N =
      (RHTower.deningerHarmonicPartial N : ℂ) := by
  simp only [harmonic, RHTower.deningerHarmonicPartial]
  push_cast
  rfl

private theorem log_nat_nonneg (n : ℕ) : 0 ≤ Real.log (n : ℝ) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · exact Real.log_nonneg (by exact_mod_cast hn)

private theorem log_div_bound (N d : ℕ) (hd : 0 < d) :
    Real.log ((N : ℝ) + 1) ≤
      Real.log (d : ℝ) + Real.log ((N / d : ℕ) + 1 : ℝ) := by
  have hN : (N : ℝ) + 1 ≤ (d : ℝ) * (((N / d : ℕ) : ℝ) + 1) := by
    exact_mod_cast Nat.succ_le_of_lt (Nat.lt_mul_div_succ N hd)
  calc
    Real.log ((N : ℝ) + 1) ≤
        Real.log ((d : ℝ) * (((N / d : ℕ) : ℝ) + 1)) :=
      Real.log_le_log (by positivity) hN
    _ = _ := Real.log_mul (by positivity) (by positivity)

private theorem tendsto_log_dilate_mul {h : ℕ → ℂ}
    (hh : Tendsto h atTop (𝓝 0))
    (hl : Tendsto (fun N : ℕ => (Real.log ((N : ℝ) + 1) : ℂ) * h N) atTop (𝓝 0))
    {d : ℕ} (hd : 0 < d) :
    Tendsto (fun N : ℕ => (Real.log ((N : ℝ) + 1) : ℂ) * h (N / d)) atTop (𝓝 0) := by
  have hdiv := Nat.tendsto_div_const_atTop hd.ne'
  have hmajor : Tendsto (fun N : ℕ => Real.log (d : ℝ) * ‖h (N / d)‖ +
      ‖(Real.log (((N / d : ℕ) : ℝ) + 1) : ℂ) * h (N / d)‖) atTop (𝓝 0) := by
    simpa using (((hh.comp hdiv).norm.const_mul (Real.log (d : ℝ))).add
      (hl.comp hdiv).norm)
  apply squeeze_zero_norm (fun N => ?_) hmajor
  rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) N] : 1 ≤ (N : ℝ) + 1)),
    abs_of_nonneg (Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) (N / d)] : 1 ≤ ((N / d : ℕ) : ℝ) + 1))]
  have hbound := mul_le_mul_of_nonneg_right (log_div_bound N d hd) (norm_nonneg (h (N / d)))
  nlinarith

private theorem tendsto_log_dilation_tsum {c : ℕ → ℂ} {d : ℕ → ℕ} {h : ℕ → ℂ}
    (h0 : h 0 = 0) (hh : Tendsto h atTop (𝓝 0))
    (hl : Tendsto (fun N : ℕ => (Real.log ((N : ℝ) + 1) : ℂ) * h N) atTop (𝓝 0))
    (hc : Summable (fun k => ‖c k‖ * (1 + Real.log (d k : ℝ)))) :
    Tendsto (fun N : ℕ => (Real.log ((N : ℝ) + 1) : ℂ) * ∑' k, c k * h (N / d k))
      atTop (𝓝 0) := by
  obtain ⟨C₀, hC₀⟩ := RHTower.deningerBounded_of_tendsto hh.norm
  obtain ⟨C₁, hC₁⟩ := RHTower.deningerBounded_of_tendsto hl.norm
  simp only [abs_norm] at hC₀ hC₁
  let B : ℝ := max C₀ C₁
  have hB0 : 0 ≤ B := (norm_nonneg (h 0)).trans ((hC₀ 0).trans (le_max_left _ _))
  have hb₀ (n : ℕ) : ‖h n‖ ≤ B := (hC₀ n).trans (le_max_left _ _)
  have hb₁ (n : ℕ) : ‖(Real.log ((n : ℝ) + 1) : ℂ) * h n‖ ≤ B :=
    (hC₁ n).trans (le_max_right _ _)
  have hlimit := tendsto_tsum_of_dominated_convergence (𝓕 := atTop) (hc.mul_right B)
    (f := fun (N : ℕ) k => c k * ((Real.log ((N : ℝ) + 1) : ℂ) * h (N / d k)))
    (g := fun _ => (0 : ℂ)) (fun k => ?_) (Eventually.of_forall fun N k => ?_)
  · simpa only [tsum_zero, mul_assoc, mul_left_comm, ← tsum_mul_left] using hlimit
  · by_cases hd : d k = 0
    · simp [hd, h0]
    · simpa using (tendsto_log_dilate_mul hh hl (Nat.pos_of_ne_zero hd)).const_mul (c k)
  · by_cases hd : d k = 0
    · simpa [hd, h0] using mul_nonneg (norm_nonneg (c k)) hB0
    · have hd0 := Nat.pos_of_ne_zero hd
      have hbound : ‖(Real.log ((N : ℝ) + 1) : ℂ) * h (N / d k)‖ ≤
          (1 + Real.log (d k : ℝ)) * B := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) N] : 1 ≤ (N : ℝ) + 1))]
        have hfirst := mul_le_mul_of_nonneg_right (log_div_bound N (d k) hd0)
          (norm_nonneg (h (N / d k)))
        have hsecond := mul_le_mul_of_nonneg_left (hb₀ (N / d k)) (log_nat_nonneg (d k))
        have hthird := hb₁ (N / d k)
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) (N / d k)] : 1 ≤ ((N / d k : ℕ) : ℝ) + 1))]
          at hthird
        nlinarith
      rw [norm_mul]
      calc
        _ ≤ ‖c k‖ * ((1 + Real.log (d k : ℝ)) * B) :=
          mul_le_mul_of_nonneg_left hbound (norm_nonneg _)
        _ = _ := by ring

private theorem tendsto_harmonic_moebius_zero :
    Tendsto (harmonic (ArithmeticFunction.moebius : ArithmeticFunction ℂ)) atTop (𝓝 0) := by
  have hr : Tendsto RHTower.deningerHarmonicPartial atTop (𝓝 0) := by
    simpa only [pow_zero, one_mul] using
      Sieve.tendsto_log_pow_mul_deningerHarmonicPartial_zero 0
  change Tendsto (fun N => harmonic (ArithmeticFunction.moebius : ArithmeticFunction ℂ) N) atTop (𝓝 0)
  simpa only [harmonic_moebius_eq, Complex.ofReal_zero, Function.comp_def] using
    (Complex.continuous_ofReal.tendsto 0).comp hr

private theorem tendsto_log_harmonic_moebius_zero :
    Tendsto (fun N : ℕ => (Real.log ((N : ℝ) + 1) : ℂ) *
      harmonic (ArithmeticFunction.moebius : ArithmeticFunction ℂ) N) atTop (𝓝 0) := by
  have hr : Tendsto (fun N : ℕ => Real.log (N : ℝ) * RHTower.deningerHarmonicPartial N)
      atTop (𝓝 0) := by
    simpa only [pow_one] using Sieve.tendsto_log_pow_mul_deningerHarmonicPartial_zero 1
  have hmajor : Tendsto (fun N : ℕ => 2 * |Real.log (N : ℝ) *
      RHTower.deningerHarmonicPartial N|) atTop (𝓝 0) := by
    simpa only [Real.norm_eq_abs, norm_zero, mul_zero] using hr.norm.const_mul 2
  apply squeeze_zero_norm' ?_ hmajor
  filter_upwards [eventually_ge_atTop 2] with N hN
  have hNR : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hlog : Real.log ((N : ℝ) + 1) ≤ 2 * Real.log (N : ℝ) := by
    calc
      _ ≤ Real.log ((N : ℝ) ^ 2) := Real.log_le_log (by positivity) (by nlinarith)
      _ = _ := by rw [Real.log_pow]; norm_num
  rw [harmonic_moebius_eq, norm_mul, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) N] : 1 ≤ (N : ℝ) + 1)),
    abs_mul, abs_of_nonneg (log_nat_nonneg N)]
  have h := mul_le_mul_of_nonneg_right hlog (abs_nonneg (RHTower.deningerHarmonicPartial N))
  nlinarith

private theorem square_log_kernel_summable :
    Summable (fun k : ℕ => ‖(1 / (k : ℂ) ^ 2)‖ *
      (1 + Real.log ((k ^ 2 : ℕ) : ℝ))) := by
  have hzero : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 2) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  have hone : Summable (fun n : ℕ => Real.log (n : ℝ) / (n : ℝ) ^ 2) := by
    simpa only [pow_one, Real.rpow_two] using
      HTGeometry.summable_log_pow_div_nat_rpow 1 (sigma := 2) (by norm_num)
  apply (hzero.add (hone.mul_left 2)).congr
  intro k
  simp only [norm_div, norm_one, norm_pow, Complex.norm_natCast, Nat.cast_pow,
    Real.log_pow]
  norm_num
  ring

theorem tendsto_log_mul_harmonic_liouville_zero :
    Tendsto (fun N : ℕ => (Real.log ((N : ℝ) + 1) : ℂ) *
      harmonic RHTower.liouvilleC N) atTop (𝓝 0) := by
  simpa only [harmonic_liouville_eq_square_dilation] using
    tendsto_log_dilation_tsum
      (c := fun k : ℕ => 1 / (k : ℂ) ^ 2) (d := fun k : ℕ => k ^ 2)
      (harmonic_zero _) tendsto_harmonic_moebius_zero
      tendsto_log_harmonic_moebius_zero square_log_kernel_summable

theorem tendsto_harmonic_liouville_zero :
    Tendsto (harmonic RHTower.liouvilleC) atTop (𝓝 0) := by
  have hlog : Tendsto (fun N : ℕ => Real.log ((N : ℝ) + 1)) atTop atTop :=
    Real.tendsto_log_atTop.comp
      (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
  have hlim := tendsto_log_mul_harmonic_liouville_zero.norm
  simp only [norm_zero] at hlim
  apply squeeze_zero_norm' ?_ hlim
  filter_upwards [hlog.eventually_ge_atTop 1] with N hN
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
  exact le_mul_of_one_le_left (norm_nonneg _) hN

def twisted : ArithmeticFunction ℂ where
  toFun := RHTower.LiouvilleTwistedDensity.twist
  map_zero' := map_zero _

def etaCoeff (e : ℕ) : ℂ := if e = 0 then 1 else
  (1 + Complex.I) * Complex.I ^ (e - 1)

def primeTwoKernel : ArithmeticFunction ℂ :=
  ArithmeticFunction.ofPowerSeries 2 (PowerSeries.mk etaCoeff)

theorem primeTwoKernel_pow (e : ℕ) : primeTwoKernel (2 ^ e) = etaCoeff e := by
  rw [primeTwoKernel, ArithmeticFunction.ofPowerSeries_apply_pow (by norm_num)]
  exact PowerSeries.coeff_mk _ _

theorem primeTwoKernel_eq_zero {n : ℕ} (hn : n ∉ Set.range (fun e : ℕ => 2 ^ e)) :
    primeTwoKernel n = 0 := by
  rw [primeTwoKernel, ArithmeticFunction.ofPowerSeries_apply (by norm_num),
    Function.extend_apply' _ _ _ hn]
  rfl

private theorem primeTwoKernel_isMultiplicative : primeTwoKernel.IsMultiplicative := by
  apply ArithmeticFunction.isMultiplicative_ofPowerSeries_of_isPrimePow 2 Nat.prime_two.isPrimePow
  simp [etaCoeff]

private theorem primeTwoKernel_other_prime {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {e : ℕ} (he : e ≠ 0) : primeTwoKernel (p ^ e) = 0 := by
  apply primeTwoKernel_eq_zero
  rintro ⟨j, hj⟩
  change (2 : ℕ) ^ j = p ^ e at hj
  have hdiv : p ∣ 2 ^ j := by rw [hj]; exact dvd_pow_self p he
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hdiv))

private theorem convolution_prime_power (f g : ArithmeticFunction ℂ) (p i : ℕ)
    (hp : p.Prime) :
    (f * g) (p ^ i) = ∑ j ∈ Finset.range (i + 1), f (p ^ j) * g (p ^ (i - j)) := by
  rw [ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal (fun a b => f a * g b), Nat.sum_divisors_prime_pow hp]
  apply Finset.sum_congr rfl
  intro j hj
  have hji : j ≤ i := by simpa using Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  have he : p ^ i = p ^ (i - j) * p ^ j := by rw [← pow_add, Nat.sub_add_cancel hji]
  rw [he, Nat.mul_div_cancel _ (pow_pos hp.pos j)]

private theorem etaCoeff_convolution (k : ℕ) :
    (∑ j ∈ Finset.range (k + 1), etaCoeff j * (-1 : ℂ) ^ (k - j)) = Complex.I ^ k := by
  induction k with
  | zero => simp [etaCoeff]
  | succ k ih =>
    rw [Finset.sum_range_succ]
    have hs : (∑ j ∈ Finset.range (k + 1), etaCoeff j * (-1 : ℂ) ^ (k + 1 - j)) =
        -(∑ j ∈ Finset.range (k + 1), etaCoeff j * (-1 : ℂ) ^ (k - j)) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      have hji : j ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
      rw [show k + 1 - j = (k - j) + 1 by omega, pow_succ]
      ring
    rw [hs, ih]
    simp only [Nat.sub_self, pow_zero, mul_one,
      etaCoeff, Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte,
      Nat.add_sub_cancel, pow_succ]
    ring

theorem primeTwoKernel_mul_liouville : primeTwoKernel * RHTower.liouvilleC = twisted := by
  have ht : twisted.IsMultiplicative :=
    ⟨map_one RHTower.LiouvilleTwistedDensity.twist,
      fun {_ _} _ => map_mul RHTower.LiouvilleTwistedDensity.twist _ _⟩
  apply (ArithmeticFunction.IsMultiplicative.eq_iff_eq_on_prime_powers _
    (primeTwoKernel_isMultiplicative.mul RHTower.isMultiplicative_liouvilleC) _ ht).mpr
  intro p k hp
  have htw : twisted (p ^ k) =
      (RHTower.LiouvilleTwistedDensity.primePhase p) ^ k := by
    change RHTower.LiouvilleTwistedDensity.twist (p ^ k) = _
    rw [map_pow, RHTower.LiouvilleTwistedDensity.twist,
      GaloisForLFunctions.HTGeometry.phaseChar_prime _ hp]
  rw [convolution_prime_power _ _ _ _ hp, htw]
  by_cases hp2 : p = 2
  · subst p
    simp only [primeTwoKernel_pow, RHTower.liouvilleC_prime_pow Nat.prime_two,
      RHTower.LiouvilleTwistedDensity.primePhase, ↓reduceIte]
    exact etaCoeff_convolution k
  · rw [Finset.sum_eq_single 0]
    · simp [RHTower.liouvilleC_prime_pow hp,
        primeTwoKernel, ArithmeticFunction.ofPowerSeries_apply_one,
        etaCoeff, RHTower.LiouvilleTwistedDensity.primePhase, hp2]
    · intro j _ hj
      rw [primeTwoKernel_other_prime hp hp2 hj, zero_mul]
    · simp

theorem harmonic_twisted_eq_dilation (N : ℕ) :
    harmonic twisted N = ∑' e : ℕ, etaCoeff e / ((2 ^ e : ℕ) : ℂ) *
      harmonic RHTower.liouvilleC (N / 2 ^ e) := by
  let F : ℕ → ℂ := fun d => primeTwoKernel d / d * harmonic RHTower.liouvilleC (N / d)
  have hfinite : harmonic twisted N = ∑ d ∈ Finset.Ioc 0 N, F d := by
    rw [← primeTwoKernel_mul_liouville, harmonic_mul]
  have htsum : ∑' d : ℕ, F d = ∑ d ∈ Finset.Ioc 0 N, F d := by
    apply tsum_eq_sum
    intro d hd
    by_cases hd0 : d = 0
    · simp [F, hd0]
    · have hNd : N < d := by simpa [Finset.mem_Ioc, Nat.pos_of_ne_zero hd0] using hd
      simp [F, Nat.div_eq_of_lt hNd]
  have hsupp : Function.support F ⊆ Set.range (fun e : ℕ => 2 ^ e) := by
    intro d hd
    by_contra h
    exact hd (by simp [F, primeTwoKernel_eq_zero h])
  rw [hfinite, ← htsum, ← Function.Injective.tsum_eq
    (g := fun e : ℕ => 2 ^ e) (Nat.pow_right_injective (by norm_num)) hsupp]
  exact tsum_congr fun e => by simp only [F, primeTwoKernel_pow]

private theorem norm_etaCoeff_le (e : ℕ) : ‖etaCoeff e‖ ≤ 2 := by
  by_cases he : e = 0
  · simp [etaCoeff, he]
  · simp only [etaCoeff, he, ↓reduceIte, norm_mul, norm_pow, Complex.norm_I,
      one_pow, mul_one]
    have h := norm_add_le (1 : ℂ) Complex.I
    norm_num at h ⊢
    exact h

private theorem primeTwo_log_kernel_summable :
    Summable (fun e : ℕ => ‖etaCoeff e / ((2 ^ e : ℕ) : ℂ)‖ *
      (1 + Real.log ((2 ^ e : ℕ) : ℝ))) := by
  have hgeom : Summable (fun e : ℕ => (1 / 2 : ℝ) ^ e) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have hlin : Summable (fun e : ℕ => (e : ℝ) * (1 / 2 : ℝ) ^ e) :=
    (hasSum_coe_mul_geometric_of_norm_lt_one (r := (1 / 2 : ℝ)) (by norm_num)).summable
  have hmajor : Summable (fun e : ℕ => 2 * (1 / 2 : ℝ) ^ e +
      (2 * Real.log 2) * ((e : ℝ) * (1 / 2 : ℝ) ^ e)) :=
    (hgeom.mul_left 2).add (hlin.mul_left (2 * Real.log 2))
  apply hmajor.of_nonneg_of_le
  · intro e
    exact mul_nonneg (norm_nonneg _) (by linarith [log_nat_nonneg (2 ^ e)])
  · intro e
    norm_num only [norm_div, Nat.cast_pow, Nat.cast_ofNat, norm_pow, Complex.norm_ofNat,
      Real.log_pow]
    have hn := norm_etaCoeff_le e
    have hlog : 0 ≤ 1 + (e : ℝ) * Real.log 2 := by positivity
    calc
      _ ≤ (2 / (2 : ℝ) ^ e) * (1 + (e : ℝ) * Real.log 2) :=
        mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hn (by positivity)) hlog
      _ = _ := by rw [div_pow, one_pow]; ring

theorem tendsto_log_mul_harmonic_twisted_zero :
    Tendsto (fun N : ℕ => (Real.log ((N : ℝ) + 1) : ℂ) * harmonic twisted N)
      atTop (𝓝 0) := by
  simpa only [harmonic_twisted_eq_dilation] using tendsto_log_dilation_tsum
    (c := fun e : ℕ => etaCoeff e / ((2 ^ e : ℕ) : ℂ)) (d := fun e : ℕ => 2 ^ e)
    (harmonic_zero _) tendsto_harmonic_liouville_zero
    tendsto_log_mul_harmonic_liouville_zero primeTwo_log_kernel_summable

theorem tendsto_harmonic_twisted_zero :
    Tendsto (harmonic twisted) atTop (𝓝 0) := by
  have hlog : Tendsto (fun N : ℕ => Real.log ((N : ℝ) + 1)) atTop atTop :=
    Real.tendsto_log_atTop.comp
      (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
  have hlim := tendsto_log_mul_harmonic_twisted_zero.norm
  simp only [norm_zero] at hlim
  apply squeeze_zero_norm' ?_ hlim
  filter_upwards [hlog.eventually_ge_atTop 1] with N hN
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
  exact le_mul_of_one_le_left (norm_nonneg _) hN

end
end RHTower.LiouvilleHarmonic
