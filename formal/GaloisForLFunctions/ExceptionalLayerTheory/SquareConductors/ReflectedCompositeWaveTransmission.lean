import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.TheTotientTermInTheReflectedCompositePrice
import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.TheForbiddenLargePrimeInTheReflectedCofactorIntervals
import GaloisForLFunctions.ExceptionalLayerTheory.TruncatedHarmonicDensityOfDivisorFloors
import GaloisForLFunctions.ExceptionalLayerTheory.MixingTwoPrimeDilationsRemovesQuartetAliasing
import GaloisForLFunctions.RHTower.Sieve.ZetaTruncated
import GaloisForLFunctions.RHTower.ChebyshevLagZeroWindowTerm

/-!
# Wave Transmission and Cofactor Divisibility in the Reflected Composite Factorization

This module establishes the exact action of the large-prime reflected-composite factorization on
smooth linear baselines, oscillatory power waves `-2 m Re(x^z / z)`, cofactor-divisibility slices
`q ∣ v`, and log-twisted waves `-2 Re((x^z log x)/z - x^z / z²)`:

1. **Exact clipped-cofactor operator and nonvanishing midpoint multiplier**
   (`midpointMultiplier_ne_zero`, `largePrimeCofactorPrice_eq_clippedCofactorOp`):
   Above `⌊2√n⌋₊`, large prime divisors of `n` cancel identically across `(2n/p, 3n/p]` and
   `(3n/p, 4n/p]`, so `largePrimeCofactorPrice n P` equals the linear clipped-cofactor operator
   `clippedCofactorOp n P Chebyshev.theta`. On `0 < Re z < 1`, `midpointMultiplier z` never vanishes.

2. **Universal linear and oscillatory wave transmission across cofactor-divisibility slices**
   (`clippedCofactorSliceOp_linear`, `clippedCofactorSliceOp_wave`,
   `clippedCofactorSliceOp_theta_of_two_le`, `reflectedComposite_wave_compatible_iff_zeta_zero`):
   Inserting `x - 2 m Re(x^z / z)` into the `q`-divisible cofactor cells (`gcd(n, q) = 1`) yields
   `(reflectedDensity / q) φ(n)` plus `-2 m Re((M(z)/z)(1_{q=1} - q^{-z} ζ(z) E_n(z)) n^z)` up to
   `O_{z,m}((P^β + n P^{β-2}) squarefreeDivisorMass n)`. At `P = ⌊2√n⌋₊`, the wave defect against
   the midpoint `2 F(3n) - F(2n) - F(4n)` is `O(√n squarefreeDivisorMass n)` if and only if
   `ζ(z) = 0`. Every `q ≥ 2` cofactor slice of `Chebyshev.theta` has zero `n^z` wave unconditionally.

3. **Remainder cancellation at actual quartets and second-order multiplicity separation**
   (`singleQuartet_reflectedComposite_remainder_cancellation`,
   `singleQuartet_individual_cofactor_cell`, `clippedCofactorOp_logTwistedWave_at_zero`,
   `logTwisted_wave_compatible_iff_deriv_zero`):
   Under `HasSingleOffLineQuartet ρ₀`, the signed cofactor sum of `θ(x) - x - W_{ρ₀,m}(x)` cancels
   from `O(n^{3/4} log² n)` down to `O(√n (log² n + squarefreeDivisorMass n))`. Differentiating the
   complex remainder at a strip zero `ζ(ρ₀) = 0` isolates `+2 Re((M(ρ₀)/ρ₀) ζ'(ρ₀) E_n(ρ₀) n^{ρ₀})`,
   which is `O(√n squarefreeDivisorMass n)` iff `ζ'(ρ₀) = 0` (`2 ≤ quartetCopyMult ρ₀`).
-/

noncomputable section
set_option autoImplicit false

open Complex Finset Filter Topology Metric MeasureTheory ArithmeticFunction
open scoped ArithmeticFunction.Moebius BigOperators
open GaloisForLFunctions.ExclusionOfTheCriticalState

namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

/-! ### 1. Midpoint multiplier, coprime Euler factor, and prime-power lower bounds -/

/-- Mellin numerator `2 · 3^z − 2^z − 4^z` of the reflected midpoint difference `2 F(3n) - F(2n) - F(4n)`. -/
def midpointMultiplier (z : ℂ) : ℂ :=
  2 * (3 : ℂ) ^ z - (2 : ℂ) ^ z - (4 : ℂ) ^ z

/-- On the entire open critical strip `0 < Re z < 1`, `midpointMultiplier z` is bounded below by
`2 · 3^{Re z} - 2^{Re z} - 4^{Re z} > 0` and therefore never vanishes. -/
theorem midpointMultiplier_ne_zero {z : ℂ} (h0 : 0 < z.re) (h1 : z.re < 1) :
    midpointMultiplier z ≠ 0 := by
  obtain ⟨hpos, hle⟩ := midpoint_mellin_numerator_lower h0 h1
  intro hz
  unfold midpointMultiplier at hz
  rw [hz, norm_zero] at hle
  linarith only [hpos, hle]

/-- Finite coprime Euler factor `E_n(z) = ∑_{d ∣ n} μ(d) d^{-z}`. -/
def coprimeEulerFactor (n : ℕ) (z : ℂ) : ℂ :=
  ∑ d ∈ n.divisors, (μ d : ℂ) * ((d : ℝ) : ℂ) ^ (-z)

/-- On any prime power `p^k` (`k ≥ 1`), `coprimeEulerFactor (p^k) z = 1 - p^{-z}`. -/
theorem coprimeEulerFactor_prime_pow {p k : ℕ} (hp : p.Prime) (hk : 1 ≤ k) (z : ℂ) :
    coprimeEulerFactor (p ^ k) z = 1 - ((p : ℝ) : ℂ) ^ (-z) := by
  unfold coprimeEulerFactor
  rw [Nat.divisors_prime_pow hp, Finset.sum_map]
  simp only [Function.Embedding.coeFn_mk]
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hk
  have hsplit : Finset.range (m + 1 + 1) = insert 0 (insert 1 (Finset.Icc 2 (m + 1))) := by
    ext i
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
    omega
  rw [hsplit, Finset.sum_insert (by simp), Finset.sum_insert (by simp)]
  have htail : ∑ i ∈ Finset.Icc 2 (m + 1),
      (μ (p ^ i) : ℂ) * (((p ^ i : ℕ) : ℝ) : ℂ) ^ (-z) = 0 := by
    refine Finset.sum_eq_zero fun i hi => ?_
    have hi2 : 2 ≤ i := (Finset.mem_Icc.mp hi).1
    rw [ArithmeticFunction.moebius_apply_prime_pow hp (by omega), if_neg (by omega)]
    simp
  rw [htail, add_zero]
  simp [ArithmeticFunction.moebius_apply_prime hp, sub_eq_add_neg]

/-- On any prime power `p^k` (`k ≥ 1`), `squarefreeDivisorMass (p^k) = 2`. -/
theorem squarefreeDivisorMass_prime_pow {p k : ℕ} (hp : p.Prime) (hk : 1 ≤ k) :
    squarefreeDivisorMass (p ^ k) = 2 := by
  unfold squarefreeDivisorMass
  rw [Nat.divisors_prime_pow hp, Finset.sum_map]
  simp only [Function.Embedding.coeFn_mk]
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hk
  have hsplit : Finset.range (m + 1 + 1) = insert 0 (insert 1 (Finset.Icc 2 (m + 1))) := by
    ext i
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
    omega
  rw [hsplit, Finset.sum_insert (by simp), Finset.sum_insert (by simp)]
  have htail : ∑ i ∈ Finset.Icc 2 (m + 1), |(μ (p ^ i) : ℝ)| = 0 := by
    refine Finset.sum_eq_zero fun i hi => ?_
    have hi2 : 2 ≤ i := (Finset.mem_Icc.mp hi).1
    rw [ArithmeticFunction.moebius_apply_prime_pow hp (by omega), if_neg (by omega)]
    simp
  rw [htail, add_zero]
  simp [ArithmeticFunction.moebius_apply_prime hp]
  norm_num

private theorem sin_im_log_ne_zero_of_two_primes {p₁ p₂ : ℕ} (hp₁ : p₁.Prime) (hp₂ : p₂.Prime)
    (hne : p₁ ≠ p₂) {γ : ℝ} (hγ : γ ≠ 0) :
    Real.sin (γ * Real.log p₁) ≠ 0 ∨ Real.sin (γ * Real.log p₂) ≠ 0 := by
  by_contra! hall
  obtain ⟨m₁, hm₁⟩ := Real.sin_eq_zero_iff.mp hall.1
  obtain ⟨m₂, hm₂⟩ := Real.sin_eq_zero_iff.mp hall.2
  have ht₁ : Real.log p₁ * (2 * γ) = (m₁ : ℝ) * (2 * Real.pi) := by linarith only [hm₁]
  have ht₂ : Real.log p₂ * (2 * γ) = (m₂ : ℝ) * (2 * Real.pi) := by linarith only [hm₂]
  have hzero : 2 * γ = 0 :=
    _root_.RHTower.primeLogPhaseClockPair_injective hp₁ hp₂ hne
      (Prod.ext
        (HTGeometry.phaseClockValue_eq_zero_of_rate_mul_time_eq_int_two_pi _ _ m₁ ht₁)
        (HTGeometry.phaseClockValue_eq_zero_of_rate_mul_time_eq_int_two_pi _ _ m₂ ht₂))
  exact hγ (by linarith only [hzero])

private theorem abs_sin_mul_norm_le_two_re (u : ℂ) (θ : ℝ) :
    |Real.sin θ| * ‖u‖ ≤ 2 * |u.re| + |(Complex.exp ((θ : ℂ) * I) * u).re| := by
  have hrot : (Complex.exp ((θ : ℂ) * I) * u).re =
      Real.cos θ * u.re - Real.sin θ * u.im := by
    rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring
  have him : |Real.sin θ * u.im| ≤ |(Complex.exp ((θ : ℂ) * I) * u).re| + |u.re| := by
    have heq : Real.sin θ * u.im = Real.cos θ * u.re - (Complex.exp ((θ : ℂ) * I) * u).re := by
      linarith only [hrot]
    rw [heq]
    refine (abs_sub _ _).trans ?_
    rw [abs_mul, add_comm]
    exact add_le_add_right (mul_le_of_le_one_left (abs_nonneg _) (Real.abs_cos_le_one θ)) _
  rw [abs_mul] at him
  have hre : |Real.sin θ| * |u.re| ≤ |u.re| :=
    mul_le_of_le_one_left (abs_nonneg _) (Real.abs_sin_le_one θ)
  have hnorm : |Real.sin θ| * ‖u‖ ≤ |Real.sin θ| * |u.re| + |Real.sin θ| * |u.im| := by
    rw [← mul_add]
    exact mul_le_mul_of_nonneg_left (Complex.norm_le_abs_re_add_abs_im u) (abs_nonneg _)
  linarith only [hnorm, hre, him]

/-- **Prime-power lower bound for nonvanishing oscillatory amplitudes.**
For any modulus `Q ≥ 1`, any `z : ℂ` with `0 < Re z` and `Im z ≠ 0`, and any `A ≠ 0`, there exist a
prime `p > Q` and `c > 0` such that for every `k ≥ 1`, at least one of `n = p^k` or `n = p^{k+1}`
is coprime to `Q`, has `squarefreeDivisorMass n = 2`, and satisfies
`c * n^{Re z} ≤ |Re(A * coprimeEulerFactor n z * n^z)|`. -/
theorem exists_prime_power_re_lower_bound {Q : ℕ} (hQ : 1 ≤ Q) {z A : ℂ} (hz0 : 0 < z.re)
    (hzim : z.im ≠ 0) (hA : A ≠ 0) :
    ∃ (p : ℕ) (c : ℝ), p.Prime ∧ Q < p ∧ 0 < c ∧
      ∀ k : ℕ, 1 ≤ k →
        ∃ n ∈ ({p ^ k, p ^ (k + 1)} : Finset ℕ),
          n.Coprime Q ∧ squarefreeDivisorMass n = 2 ∧
          c * (n : ℝ) ^ z.re ≤ |(A * coprimeEulerFactor n z * ((n : ℝ) : ℂ) ^ z).re| := by
  obtain ⟨p₁, hp₁_ge, hp₁⟩ := Nat.exists_infinite_primes (Q + 1)
  obtain ⟨p₂, hp₂_ge, hp₂⟩ := Nat.exists_infinite_primes (p₁ + 1)
  have hQp₁ : Q < p₁ := by omega
  have hQp₂ : Q < p₂ := by omega
  have hne : p₁ ≠ p₂ := by omega
  obtain ⟨p, hp, hQp, hsin⟩ :
      ∃ p : ℕ, p.Prime ∧ Q < p ∧ Real.sin (z.im * Real.log p) ≠ 0 := by
    rcases sin_im_log_ne_zero_of_two_primes hp₁ hp₂ hne hzim with h1 | h2
    · exact ⟨p₁, hp₁, hQp₁, h1⟩
    · exact ⟨p₂, hp₂, hQp₂, h2⟩
  have hp_pos : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp_gt1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have heul_ne : 1 - ((p : ℝ) : ℂ) ^ (-z) ≠ 0 := by
    intro he
    have hn1 : ‖((p : ℝ) : ℂ) ^ (-z)‖ = 1 := by
      rw [← sub_eq_zero.mp he, norm_one]
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hp_pos, Complex.neg_re] at hn1
    have hlt : (p : ℝ) ^ (-z.re) < 1 := Real.rpow_lt_one_of_one_lt_of_neg hp_gt1 (by linarith)
    linarith only [hn1, hlt]
  set B : ℂ := A * (1 - ((p : ℝ) : ℂ) ^ (-z))
  have hB_pos : 0 < ‖B‖ := norm_pos_iff.mpr (mul_ne_zero hA heul_ne)
  set θ : ℝ := z.im * Real.log p
  have hsin_pos : 0 < |Real.sin θ| := abs_pos.mpr hsin
  set c : ℝ := |Real.sin θ| * ‖B‖ / 3
  refine ⟨p, c, hp, hQp, by dsimp [c]; positivity, fun k hk => ?_⟩
  have hcop_p : p.Coprime Q :=
    hp.coprime_iff_not_dvd.mpr fun hd => hQp.not_ge (Nat.le_of_dvd hQ hd)
  set n₁ : ℕ := p ^ k
  set n₂ : ℕ := p ^ (k + 1)
  have hn₁_pos : (0 : ℝ) < n₁ := by exact_mod_cast pow_pos hp.pos k
  set u : ℂ := B * ((n₁ : ℝ) : ℂ) ^ z
  have hu_norm : ‖u‖ = ‖B‖ * (n₁ : ℝ) ^ z.re := by
    rw [show u = B * ((n₁ : ℝ) : ℂ) ^ z from rfl, norm_mul,
      Complex.norm_cpow_eq_rpow_re_of_pos hn₁_pos]
  have hstep_cpow : ((n₂ : ℝ) : ℂ) ^ z =
      (((p : ℝ) ^ z.re : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * I) * ((n₁ : ℝ) : ℂ) ^ z := by
    have hn₂_pos : (0 : ℝ) < n₂ := by exact_mod_cast pow_pos hp.pos (k + 1)
    have hn₂_eq : (n₂ : ℝ) = (p : ℝ) * (n₁ : ℝ) := by
      dsimp [n₁, n₂]; rw [pow_succ']; push_cast; rfl
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hn₂_pos.ne'),
      Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hn₁_pos.ne'),
      ← Complex.ofReal_log hn₂_pos.le, ← Complex.ofReal_log hn₁_pos.le,
      hn₂_eq, Real.log_mul hp_pos.ne' hn₁_pos.ne', Real.rpow_def_of_pos hp_pos,
      Complex.ofReal_exp, ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    apply Complex.ext <;> simp [θ] <;> ring
  by_cases h1 : c * (n₁ : ℝ) ^ z.re ≤ |u.re|
  · refine ⟨n₁, by simp, hcop_p.pow_left k, squarefreeDivisorMass_prime_pow hp hk, ?_⟩
    rwa [coprimeEulerFactor_prime_pow hp hk z]
  · push Not at h1
    refine ⟨n₂, by simp, hcop_p.pow_left (k + 1),
      squarefreeDivisorMass_prime_pow hp (by omega), ?_⟩
    rw [coprimeEulerFactor_prime_pow hp (by omega) z]
    change c * (n₂ : ℝ) ^ z.re ≤ |(B * ((n₂ : ℝ) : ℂ) ^ z).re|
    have hrot_ge : c * (n₁ : ℝ) ^ z.re ≤ |(Complex.exp ((θ : ℂ) * I) * u).re| := by
      have htri := abs_sin_mul_norm_le_two_re u θ
      rw [hu_norm] at htri
      have h3 : |Real.sin θ| * (‖B‖ * (n₁ : ℝ) ^ z.re) = 3 * (c * (n₁ : ℝ) ^ z.re) := by
        dsimp [c]; ring
      linarith only [htri, h1, h3]
    have hre2 : (B * ((n₂ : ℝ) : ℂ) ^ z).re =
        (p : ℝ) ^ z.re * (Complex.exp ((θ : ℂ) * I) * u).re := by
      rw [hstep_cpow, show u = B * ((n₁ : ℝ) : ℂ) ^ z from rfl,
        show B * ((((p : ℝ) ^ z.re : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * I) * ((n₁ : ℝ) : ℂ) ^ z) =
          (((p : ℝ) ^ z.re : ℝ) : ℂ) * (Complex.exp ((θ : ℂ) * I) * (B * ((n₁ : ℝ) : ℂ) ^ z)) by ring,
        Complex.re_ofReal_mul]
    have hn₂_rpow : (n₂ : ℝ) ^ z.re = (p : ℝ) ^ z.re * (n₁ : ℝ) ^ z.re := by
      dsimp [n₁, n₂]
      rw [pow_succ', Nat.cast_mul, Real.mul_rpow hp_pos.le hn₁_pos.le]
    rw [hre2, abs_mul, abs_of_pos (Real.rpow_pos_of_pos hp_pos z.re), hn₂_rpow, ← mul_assoc,
      mul_comm c ((p : ℝ) ^ z.re), mul_assoc]
    exact mul_le_mul_of_nonneg_left hrot_ge (Real.rpow_pos_of_pos hp_pos z.re).le

/-! ### 2. Clipped-cofactor slice operator and exact prime-cofactor swap -/

/-- Clipped-cofactor reflected-composite operator on the `q`-divisible cofactor slice:
sums `F(max(P, 4n/v)) - 2 F(max(P, 3n/v)) + F(max(P, 2n/v))` over `2 ≤ v ≤ 4n` with `gcd(n, v) = 1`
and `q ∣ v`. -/
def clippedCofactorSliceOp (n P q : ℕ) (F : ℝ → ℝ) : ℝ :=
  ∑ v ∈ (Icc 2 (4 * n)).filter (fun v => n.Coprime v ∧ q ∣ v),
    (F (max P (4 * n / v) : ℕ) - 2 * F (max P (3 * n / v) : ℕ) + F (max P (2 * n / v) : ℕ))

/-- Full clipped-cofactor operator (`q = 1`) corresponding to all coprime cofactors `v ≥ 2`. -/
abbrev clippedCofactorOp (n P : ℕ) (F : ℝ → ℝ) : ℝ :=
  clippedCofactorSliceOp n P 1 F

/-- Second difference `2 F(3n) - F(2n) - F(4n)` at the reflected midpoint. -/
def midpointSecondDiff (n : ℕ) (F : ℝ → ℝ) : ℝ :=
  2 * F (3 * n : ℕ) - F (2 * n : ℕ) - F (4 * n : ℕ)

theorem clippedCofactorSliceOp_add (n P q : ℕ) (F G : ℝ → ℝ) :
    clippedCofactorSliceOp n P q (fun x => F x + G x) =
      clippedCofactorSliceOp n P q F + clippedCofactorSliceOp n P q G := by
  simp only [clippedCofactorSliceOp, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem clippedCofactorSliceOp_sub (n P q : ℕ) (F G : ℝ → ℝ) :
    clippedCofactorSliceOp n P q (fun x => F x - G x) =
      clippedCofactorSliceOp n P q F - clippedCofactorSliceOp n P q G := by
  simp only [clippedCofactorSliceOp, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun _ _ => by ring

private theorem theta_interval_nat {a b : ℕ} (hab : a ≤ b) :
    (∑ p ∈ (Ioc a b).filter Nat.Prime, Real.log p) = Chebyshev.theta b - Chebyshev.theta a := by
  simp only [Chebyshev.theta, Nat.floor_natCast, Finset.sum_filter]
  linarith only [Finset.sum_Ioc_consecutive (fun p : ℕ => if p.Prime then Real.log p else 0)
    (Nat.zero_le a) hab]

private theorem unrestricted_proper_cofactor_eq_zero_of_dvd {n p : ℕ} (hn : 1 ≤ n) (hp : p.Prime)
    (hdvd : p ∣ n) (hcut : ⌊2 * Real.sqrt n⌋₊ < p) :
    (((Icc 2 (4 * n / p)).filter (n.Coprime ·)).card : ℝ) -
      2 * (((Icc 2 (3 * n / p)).filter (n.Coprime ·)).card : ℝ) +
      (((Icc 2 (2 * n / p)).filter (n.Coprime ·)).card : ℝ) = 0 := by
  have hzero := forbidden_prime_at_square_root_cut hn hp hdvd hcut
  set a := n / p
  have ha : 1 ≤ a := Nat.div_pos (Nat.le_of_dvd hn hdvd) hp.pos
  have hq (j : ℕ) : j * n / p = j * a := Nat.mul_div_assoc j hdvd
  rw [unrestrictedPrimeCofactorCut, hq 4, hq 3, hq 2,
    max_eq_right (show 1 ≤ 3 * a by omega), max_eq_right (show 1 ≤ 2 * a by omega),
    min_self, min_eq_right (show 3 * a ≤ 4 * a by omega)] at hzero
  rw [hq 4, hq 3, hq 2]
  have split_card {l u : ℕ} (hl : 2 ≤ l) (hlu : l ≤ u) :
      (((Icc 2 u).filter (n.Coprime ·)).card : ℝ) =
        (((Icc 2 l).filter (n.Coprime ·)).card : ℝ) +
          (((Ioc l u).filter (n.Coprime ·)).card : ℝ) := by
    have hu_eq : Icc 2 u = Icc 2 l ∪ Ioc l u := by
      ext v; simp only [mem_Icc, mem_union, mem_Ioc]; omega
    have hdisj : Disjoint (Icc 2 l) (Ioc l u) :=
      Finset.disjoint_left.mpr fun _ h1 h2 => (mem_Ioc.mp h2).1.not_ge (mem_Icc.mp h1).2
    rw [hu_eq, Finset.filter_union, Finset.card_union_of_disjoint
      (Finset.disjoint_filter_filter hdisj), Nat.cast_add]
  rw [split_card (show 2 ≤ 3 * a by omega) (show 3 * a ≤ 4 * a by omega),
    split_card (show 2 ≤ 2 * a by omega) (show 2 * a ≤ 3 * a by omega)]
  linarith only [hzero]

/-- **Exact prime-cofactor swap above `⌊2√n⌋₊`.**
For every `n ≥ 1` and `P ≥ ⌊2√n⌋₊`, `largePrimeCofactorPrice n P` equals
`clippedCofactorOp n P Chebyshev.theta` identically. -/
theorem largePrimeCofactorPrice_eq_clippedCofactorOp {n P : ℕ} (hn : 1 ≤ n)
    (hlo : ⌊2 * Real.sqrt n⌋₊ ≤ P) :
    largePrimeCofactorPrice n P = clippedCofactorOp n P Chebyshev.theta := by
  classical
  let V := (Icc 2 (4 * n)).filter (fun v => n.Coprime v ∧ 1 ∣ v)
  let S := (Ioc P (4 * n)).filter Nat.Prime
  have hunr : ∀ p ∈ S, properCofactorMidpoint n p =
      (((Icc 2 (4 * n / p)).filter (n.Coprime ·)).card : ℝ) -
        2 * (((Icc 2 (3 * n / p)).filter (n.Coprime ·)).card : ℝ) +
        (((Icc 2 (2 * n / p)).filter (n.Coprime ·)).card : ℝ) := by
    intro p hpS
    obtain ⟨hpI, hp⟩ := mem_filter.mp hpS
    have hpP : ⌊2 * Real.sqrt n⌋₊ < p := hlo.trans_lt (mem_Ioc.mp hpI).1
    unfold properCofactorMidpoint
    by_cases hcop : n.Coprime p
    · rw [if_pos hcop]; rfl
    · rw [if_neg hcop]
      have hdvd : p ∣ n := by
        by_contra hnd
        exact hcop (hp.coprime_iff_not_dvd.mpr hnd).symm
      exact (unrestricted_proper_cofactor_eq_zero_of_dvd hn hp hdvd hpP).symm
  have hrow (k : ℕ) (hk : k ≤ 4) :
      (∑ p ∈ S, Real.log p * (((Icc 2 (k * n / p)).filter (n.Coprime ·)).card : ℝ)) =
        ∑ v ∈ V, (Chebyshev.theta (max P (k * n / v) : ℕ) - Chebyshev.theta P) := by
    have hcard (p : ℕ) (hpS : p ∈ S) :
        (((Icc 2 (k * n / p)).filter (n.Coprime ·)).card : ℝ) =
          ∑ v ∈ V, if v ≤ k * n / p then (1 : ℝ) else 0 := by
      have hsub : (Icc 2 (k * n / p)).filter (n.Coprime ·) =
          V.filter (fun v => v ≤ k * n / p) := by
        ext v
        simp only [V, mem_filter, mem_Icc, one_dvd, and_true]
        constructor
        · rintro ⟨⟨hv2, hvu⟩, hcop⟩
          have hkn : k * n / p ≤ 4 * n :=
            (Nat.div_le_self _ _).trans (Nat.mul_le_mul_right n hk)
          exact ⟨⟨⟨hv2, hvu.trans hkn⟩, hcop⟩, hvu⟩
        · rintro ⟨⟨⟨hv2, _⟩, hcop⟩, hvu⟩
          exact ⟨⟨hv2, hvu⟩, hcop⟩
      rw [hsub, Finset.card_eq_sum_ones, Finset.sum_filter]
      push_cast; rfl
    calc ∑ p ∈ S, Real.log p * (((Icc 2 (k * n / p)).filter (n.Coprime ·)).card : ℝ)
        = ∑ p ∈ S, ∑ v ∈ V, if v ≤ k * n / p then Real.log p else 0 := by
            refine Finset.sum_congr rfl fun p hpS => ?_
            rw [hcard p hpS, Finset.mul_sum]
            exact Finset.sum_congr rfl fun v _ => by split_ifs <;> ring
      _ = ∑ v ∈ V, ∑ p ∈ S, if v ≤ k * n / p then Real.log p else 0 := Finset.sum_comm
      _ = ∑ v ∈ V, (Chebyshev.theta (max P (k * n / v) : ℕ) - Chebyshev.theta P) := by
            refine Finset.sum_congr rfl fun v hv => ?_
            have hv2 : 2 ≤ v := (mem_Icc.mp (mem_filter.mp hv).1).1
            have hv0 : 0 < v := by omega
            have hset : S.filter (fun p => v ≤ k * n / p) =
                (Ioc P (max P (k * n / v))).filter Nat.Prime := by
              ext p
              simp only [S, mem_filter, mem_Ioc]
              constructor
              · rintro ⟨⟨⟨hPp, _⟩, hp⟩, hvp⟩
                have hp0 : 0 < p := hp.pos
                have hmul : v * p ≤ k * n := (Nat.le_div_iff_mul_le hp0).mp hvp
                have hpv : p ≤ k * n / v :=
                  (Nat.le_div_iff_mul_le hv0).mpr (by rwa [mul_comm])
                exact ⟨⟨hPp, le_max_of_le_right hpv⟩, hp⟩
              · rintro ⟨⟨hPp, hpmax⟩, hp⟩
                have hp0 : 0 < p := hp.pos
                have hp_le_knv : p ≤ k * n / v := by omega
                have hmul : p * v ≤ k * n := (Nat.le_div_iff_mul_le hv0).mp hp_le_knv
                have hvp : v ≤ k * n / p :=
                  (Nat.le_div_iff_mul_le hp0).mpr (by rwa [mul_comm])
                have hp4n : p ≤ 4 * n :=
                  calc p ≤ p * v := Nat.le_mul_of_pos_right p hv0
                    _ ≤ k * n := hmul
                    _ ≤ 4 * n := Nat.mul_le_mul_right n hk
                exact ⟨⟨⟨hPp, hp4n⟩, hp⟩, hvp⟩
            rw [← Finset.sum_filter, hset, theta_interval_nat (le_max_left P _)]
  rw [largePrimeCofactorPrice]
  have hexp : ∑ p ∈ S, Real.log p * properCofactorMidpoint n p =
      (∑ p ∈ S, Real.log p * (((Icc 2 (4 * n / p)).filter (n.Coprime ·)).card : ℝ)) -
        2 * (∑ p ∈ S, Real.log p * (((Icc 2 (3 * n / p)).filter (n.Coprime ·)).card : ℝ)) +
        (∑ p ∈ S, Real.log p * (((Icc 2 (2 * n / p)).filter (n.Coprime ·)).card : ℝ)) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p hpS => ?_
    rw [hunr p hpS]; ring
  change ∑ p ∈ S, Real.log p * properCofactorMidpoint n p = _
  rw [hexp, hrow 4 (by decide), hrow 3 (by decide), hrow 2 (by decide),
    clippedCofactorOp, clippedCofactorSliceOp, Finset.mul_sum, ← Finset.sum_sub_distrib,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun _ _ => by ring

/-! ### 3. Möbius inversion helpers and universal linear density transmission -/

private theorem sum_coprime_Icc_real {n M : ℕ} (hn : 1 ≤ n) (f : ℕ → ℝ) :
    ∑ u ∈ (Icc 1 M).filter (n.Coprime ·), f u =
      ∑ d ∈ n.divisors, (μ d : ℝ) * ∑ j ∈ Icc 1 (M / d), f (d * j) := by
  classical
  have detector (u : ℕ) :
      (if n.Coprime u then (1 : ℝ) else 0) =
        ∑ d ∈ n.divisors, if d ∣ u then (μ d : ℝ) else 0 := by
    rw [← Finset.sum_filter]
    have hset : n.divisors.filter (· ∣ u) = (n.gcd u).divisors := by
      ext d
      simp only [mem_filter, Nat.mem_divisors, Nat.dvd_gcd_iff]
      exact ⟨fun h => ⟨⟨h.1.1, h.2⟩, (Nat.gcd_pos_of_pos_left u hn).ne'⟩,
        fun h => ⟨⟨h.1.1, by omega⟩, h.1.2⟩⟩
    rw [hset, _root_.RHTower.Sieve.sum_divisors_moebius_real]
  rw [Finset.sum_filter]
  calc ∑ u ∈ Icc 1 M, (if n.Coprime u then f u else 0)
      = ∑ u ∈ Icc 1 M, ∑ d ∈ n.divisors, if d ∣ u then (μ d : ℝ) * f u else 0 := by
          refine Finset.sum_congr rfl fun u _ => ?_
          rw [show (if n.Coprime u then f u else 0) =
              (if n.Coprime u then (1 : ℝ) else 0) * f u by split_ifs <;> simp,
            detector, Finset.sum_mul]
          exact Finset.sum_congr rfl fun d _ => by split_ifs <;> simp
    _ = ∑ d ∈ n.divisors, ∑ u ∈ Icc 1 M, if d ∣ u then (μ d : ℝ) * f u else 0 := Finset.sum_comm
    _ = ∑ d ∈ n.divisors, (μ d : ℝ) * ∑ j ∈ Icc 1 (M / d), f (d * j) := by
          refine Finset.sum_congr rfl fun d hd => ?_
          have hd0 : 0 < d := Nat.pos_of_mem_divisors hd
          rw [← Finset.sum_filter,
            _root_.RHTower.Sieve.sum_filter_dvd_eq_sum_scaled hd0, Finset.mul_sum]

private theorem sum_coprime_Icc_complex {n M : ℕ} (hn : 1 ≤ n) (f : ℕ → ℂ) :
    ∑ u ∈ (Icc 1 M).filter (n.Coprime ·), f u =
      ∑ d ∈ n.divisors, (μ d : ℂ) * ∑ j ∈ Icc 1 (M / d), f (d * j) := by
  apply Complex.ext
  · simp only [Complex.re_sum, sum_coprime_Icc_real hn (fun u => (f u).re)]
    refine Finset.sum_congr rfl fun d _ => ?_
    have hcast : (μ d : ℂ) = ((μ d : ℝ) : ℂ) := by norm_cast
    rw [hcast, Complex.re_ofReal_mul, Complex.re_sum]
  · simp only [Complex.im_sum, sum_coprime_Icc_real hn (fun u => (f u).im)]
    refine Finset.sum_congr rfl fun d _ => ?_
    have hcast : (μ d : ℂ) = ((μ d : ℝ) : ℂ) := by norm_cast
    rw [hcast, Complex.im_ofReal_mul, Complex.im_sum]

private theorem one_le_squarefreeDivisorMass {n : ℕ} (hn : 1 ≤ n) :
    1 ≤ squarefreeDivisorMass n := by
  unfold squarefreeDivisorMass
  have h1 : 1 ∈ n.divisors := Nat.mem_divisors.mpr ⟨one_dvd n, by omega⟩
  calc (1 : ℝ) = |(μ 1 : ℝ)| := by simp
    _ ≤ ∑ d ∈ n.divisors, |(μ d : ℝ)| :=
        Finset.single_le_sum (f := fun d => |(μ d : ℝ)|) (fun _ _ => abs_nonneg _) h1

private theorem harmonic_floor_all_pos {t : ℝ} (ht : 0 < t) :
    |t * (harmonic ⌊t⌋₊ : ℝ) - (⌊t⌋₊ : ℝ) -
        t * (Real.log t + Real.eulerMascheroniConstant - 1)| ≤ 5 := by
  have hg0 : 0 ≤ Real.eulerMascheroniConstant := by
    linarith only [Real.one_half_lt_eulerMascheroniConstant]
  have hg1 : Real.eulerMascheroniConstant ≤ 1 := by
    linarith only [Real.eulerMascheroniConstant_lt_two_thirds]
  by_cases ht1 : 1 ≤ t
  · have hfl_le : (⌊t⌋₊ : ℝ) ≤ t := Nat.floor_le ht.le
    have hlt_fl : t ≤ (⌊t⌋₊ : ℝ) + 1 := (Nat.lt_floor_add_one t).le
    have hend := harmonic_endpoint ht hfl_le hlt_fl
    have h4 : 4 / t ≤ 4 := (div_le_iff₀ ht).mpr (by linarith only [ht1])
    have htri : |t * (harmonic ⌊t⌋₊ : ℝ) - (⌊t⌋₊ : ℝ) -
        t * (Real.log t + Real.eulerMascheroniConstant - 1)| ≤
        |t * (harmonic ⌊t⌋₊ : ℝ) - (⌊t⌋₊ : ℝ) -
          (t * (Real.log t + Real.eulerMascheroniConstant - 1) + 1 / 2)| + 1 / 2 := by
      have := abs_add_le
        (t * (harmonic ⌊t⌋₊ : ℝ) - (⌊t⌋₊ : ℝ) -
          (t * (Real.log t + Real.eulerMascheroniConstant - 1) + 1 / 2)) (1 / 2)
      ring_nf at this ⊢
      exact this
    linarith only [htri, hend, h4]
  · push Not at ht1
    have hfl0 : ⌊t⌋₊ = 0 := Nat.floor_eq_zero.mpr ht1
    rw [hfl0]
    simp only [harmonic_zero, Rat.cast_zero, mul_zero, Nat.cast_zero, sub_zero, zero_sub, abs_neg]
    have hlog_lo : -(1 - t) ≤ t * Real.log t := by
      have hl := Real.log_le_sub_one_of_pos (inv_pos.mpr ht)
      rw [Real.log_inv] at hl
      have hm := mul_le_mul_of_nonneg_left hl ht.le
      rw [mul_neg, mul_sub, mul_inv_cancel₀ ht.ne', mul_one] at hm
      linarith only [hm]
    have hlog_hi : t * Real.log t ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos ht.le (Real.log_nonpos ht.le ht1.le)
    rw [mul_sub, mul_add]
    rw [abs_le]
    constructor <;> nlinarith only [hlog_lo, hlog_hi, hg0, hg1, ht, ht1]

/-- **Universal linear baseline transmission on cofactor-divisibility slices.**
For `n ≥ 1`, `1 ≤ P ≤ 2n`, and `q ≥ 1` coprime to `n`, inserting `id` into
`clippedCofactorSliceOp n P q` yields `(reflectedDensity / q) φ(n)` up to
`(20(P + 1) + 12 n / (q(P + 1))) squarefreeDivisorMass n`. -/
theorem clippedCofactorSliceOp_linear {n P q : ℕ} (hn : 1 ≤ n) (hP1 : 1 ≤ P) (hP2 : P ≤ 2 * n)
    (hq : 1 ≤ q) (hcop : n.Coprime q) :
    |clippedCofactorSliceOp n P q id - (reflectedDensity / (q : ℝ)) * (n.totient : ℝ)| ≤
      (20 * ((P : ℝ) + 1) + 12 * (n : ℝ) / ((q : ℝ) * ((P : ℝ) + 1))) *
        squarefreeDivisorMass n := by
  classical
  have hq0 : 0 < q := hq
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq0
  have hP1R : (0 : ℝ) < (P : ℝ) + 1 := by positivity
  -- Rewrite slice sum over `u ∈ Icc 1 (4*n/q)` with `n.Coprime u` (since `v = 1` vanishes at `q = 1`)
  let g (v : ℕ) : ℝ :=
    ((max P (4 * n / v) : ℕ) : ℝ) - 2 * ((max P (3 * n / v) : ℕ) : ℝ) +
      ((max P (2 * n / v) : ℕ) : ℝ)
  have hg1 : g 1 = 0 := by
    dsimp [g]
    rw [Nat.div_one, Nat.div_one, Nat.div_one, max_eq_right (by omega), max_eq_right (by omega),
      max_eq_right hP2]
    push_cast; ring
  have hslice_eq : clippedCofactorSliceOp n P q id =
      ∑ u ∈ (Icc 1 (4 * n / q)).filter (n.Coprime ·), g (q * u) := by
    unfold clippedCofactorSliceOp
    change ∑ v ∈ (Icc 2 (4 * n)).filter (fun v => n.Coprime v ∧ q ∣ v), g v = _
    have hmap : ∑ u ∈ (Icc 1 (4 * n / q)).filter (n.Coprime ·), g (q * u) =
        ∑ v ∈ (Icc 1 (4 * n)).filter (fun v => n.Coprime v ∧ q ∣ v), g v := by
      refine Finset.sum_nbij' (fun u => q * u) (fun v => v / q) ?_ ?_ ?_ ?_ (fun _ _ => rfl)
      · intro u hu
        obtain ⟨huI, huc⟩ := mem_filter.mp hu
        obtain ⟨hu1, hu4⟩ := mem_Icc.mp huI
        exact mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.mul_pos hq0 hu1,
          (Nat.le_div_iff_mul_le hq0).mp hu4 |>.trans_eq' (mul_comm _ _)⟩,
          Nat.Coprime.mul_right hcop huc, dvd_mul_right q u⟩
      · intro v hv
        obtain ⟨hvI, hvc, hqv⟩ := mem_filter.mp hv
        obtain ⟨hv1, hv4⟩ := mem_Icc.mp hvI
        have hmul : q * (v / q) = v := Nat.mul_div_cancel' hqv
        have hu1 : 1 ≤ v / q := Nat.div_pos (Nat.le_of_dvd hv1 hqv) hq0
        have hu4 : v / q ≤ 4 * n / q := Nat.div_le_div_right hv4
        have huc : n.Coprime (v / q) :=
          (Nat.coprime_mul_iff_right.mp (hmul ▸ hvc)).2
        exact mem_filter.mpr ⟨mem_Icc.mpr ⟨hu1, hu4⟩, huc⟩
      · intro u _; exact Nat.mul_div_right u hq0
      · intro v hv; exact Nat.mul_div_cancel' (mem_filter.mp hv).2.2
    rw [hmap]
    symm
    have h12 : Icc 1 (4 * n) = insert 1 (Icc 2 (4 * n)) := by
      ext v; simp only [mem_Icc, mem_insert]; omega
    rw [h12, Finset.filter_insert]
    split_ifs with h1q
    · rw [Finset.sum_insert (by simp), hg1, zero_add]
    · rfl
  rw [hslice_eq]
  -- Compare `((max P (k*n/(q*u)) : ℕ) : ℝ) - P` with `(k*n)/(q*u) - (P + 1)` on `u ≤ (k*n)/((P+1)*q)`
  let Bk (k u : ℕ) : ℝ :=
    if u ≤ (k * n) / ((P + 1) * q) then ((k * n : ℕ) : ℝ) / ((q * u : ℕ) : ℝ) - ((P : ℝ) + 1)
    else 0
  have hgu_eq (u : ℕ) : g (q * u) =
      (((max P (4 * n / (q * u)) : ℕ) : ℝ) - P) -
        2 * (((max P (3 * n / (q * u)) : ℕ) : ℝ) - P) +
        (((max P (2 * n / (q * u)) : ℕ) : ℝ) - P) := by
    dsimp [g]; ring
  have hround_k (k : ℕ) (hk1 : 1 ≤ k) (hk4 : k ≤ 4) :
      |(∑ u ∈ (Icc 1 (4 * n / q)).filter (n.Coprime ·),
          (((max P (k * n / (q * u)) : ℕ) : ℝ) - P)) -
        ∑ u ∈ (Icc 1 ((k * n) / ((P + 1) * q))).filter (n.Coprime ·),
          (((k * n : ℕ) : ℝ) / ((q * u : ℕ) : ℝ) - ((P : ℝ) + 1))| ≤
        (k : ℝ) * (n : ℝ) / ((q : ℝ) * ((P : ℝ) + 1)) := by
    have hsub_u : ((Icc 1 ((k * n) / ((P + 1) * q))).filter (n.Coprime ·)) ⊆
        (Icc 1 (4 * n / q)).filter (n.Coprime ·) := by
      intro u hu
      obtain ⟨huI, huc⟩ := mem_filter.mp hu
      obtain ⟨hu1, huhi⟩ := mem_Icc.mp huI
      have hle : (k * n) / ((P + 1) * q) ≤ 4 * n / q := by
        calc (k * n) / ((P + 1) * q) ≤ (k * n) / (1 * q) :=
              Nat.div_le_div_left (Nat.mul_le_mul_right q (by omega)) (by positivity)
          _ = k * n / q := by rw [one_mul]
          _ ≤ 4 * n / q := Nat.div_le_div_right (Nat.mul_le_mul_right n hk4)
      exact mem_filter.mpr ⟨mem_Icc.mpr ⟨hu1, huhi.trans hle⟩, huc⟩
    have hBk_sum : ∑ u ∈ (Icc 1 ((k * n) / ((P + 1) * q))).filter (n.Coprime ·),
        (((k * n : ℕ) : ℝ) / ((q * u : ℕ) : ℝ) - ((P : ℝ) + 1)) =
        ∑ u ∈ (Icc 1 (4 * n / q)).filter (n.Coprime ·), Bk k u := by
      symm
      rw [← Finset.sum_subset hsub_u]
      · refine Finset.sum_congr rfl fun u hu => ?_
        dsimp [Bk]; rw [if_pos (mem_Icc.mp (mem_filter.mp hu).1).2]
      · intro u _ hunot
        dsimp [Bk]
        rw [if_neg (fun hle => hunot (mem_filter.mpr
          ⟨mem_Icc.mpr ⟨(mem_Icc.mp (mem_filter.mp ‹_›).1).1, hle⟩,
            (mem_filter.mp ‹_›).2⟩))]
    rw [hBk_sum, ← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hterm (u : ℕ) (hu : u ∈ (Icc 1 (4 * n / q)).filter (n.Coprime ·)) :
        |(((max P (k * n / (q * u)) : ℕ) : ℝ) - P) - Bk k u| ≤
          if u ≤ (k * n) / ((P + 1) * q) then 1 else 0 := by
      have hu1 : 1 ≤ u := (mem_Icc.mp (mem_filter.mp hu).1).1
      have hqu0 : 0 < q * u := Nat.mul_pos hq0 hu1
      dsimp [Bk]
      split_ifs with hle
      · have hm : ((P + 1) * q) * u ≤ k * n :=
          (Nat.le_div_iff_mul_le (Nat.mul_pos (by omega) hq0)).mp hle |>.trans_eq' (mul_comm _ _)
        have hP_le : P + 1 ≤ k * n / (q * u) :=
          (Nat.le_div_iff_mul_le hqu0).mpr (by linarith only [hm, show ((P + 1) * q) * u = (P + 1) * (q * u) by ring])
        rw [max_eq_right (by omega : P ≤ k * n / (q * u))]
        have hf := _root_.RHTower.Sieve.abs_natDiv_sub_div_le (N := k * n) hqu0
        have hlo_div : (((k * n / (q * u) : ℕ) : ℝ)) ≤ ((k * n : ℕ) : ℝ) / ((q * u : ℕ) : ℝ) :=
          Nat.cast_div_le
        have hhi_div : ((k * n : ℕ) : ℝ) / ((q * u : ℕ) : ℝ) ≤ ((k * n / (q * u) : ℕ) : ℝ) + 1 := by
          have := (abs_le.mp hf).1; linarith
        rw [abs_le]
        constructor <;> linarith only [hlo_div, hhi_div]
      · push Not at hle
        have hm : k * n < u * ((P + 1) * q) :=
          (Nat.div_lt_iff_lt_mul (Nat.mul_pos (by omega) hq0)).mp hle
        have hlt_P : k * n / (q * u) < P + 1 :=
          (Nat.div_lt_iff_lt_mul hqu0).mpr (by linarith only [hm, show u * ((P + 1) * q) = (P + 1) * (q * u) by ring])
        rw [max_eq_left (by omega : k * n / (q * u) ≤ P)]
        simp
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [← Finset.sum_filter]
    have hcard_le : (((Icc 1 (4 * n / q)).filter (n.Coprime ·) |>.filter
        (fun u => u ≤ (k * n) / ((P + 1) * q))).card : ℝ) ≤
        (((k * n) / ((P + 1) * q) : ℕ) : ℝ) := by
      have hsub2 : ((Icc 1 (4 * n / q)).filter (n.Coprime ·)).filter
          (fun u => u ≤ (k * n) / ((P + 1) * q)) ⊆ Icc 1 ((k * n) / ((P + 1) * q)) := by
        intro u hu
        obtain ⟨hu1, hu2⟩ := mem_filter.mp hu
        exact mem_Icc.mpr ⟨(mem_Icc.mp (mem_filter.mp hu1).1).1, hu2⟩
      exact_mod_cast (Finset.card_le_card hsub2).trans_eq (by simp)
    rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    refine hcard_le.trans ?_
    have hd : (((k * n) / ((P + 1) * q) : ℕ) : ℝ) ≤
        ((k * n : ℕ) : ℝ) / (((P + 1) * q : ℕ) : ℝ) := Nat.cast_div_le
    refine hd.trans_eq ?_
    push_cast; ring
  -- Evaluate the Möbius-inverted harmonic combination for each divisor `d ∣ n`
  let Hk (k : ℕ) : ℝ :=
    ∑ u ∈ (Icc 1 ((k * n) / ((P + 1) * q))).filter (n.Coprime ·),
      (((k * n : ℕ) : ℝ) / ((q * u : ℕ) : ℝ) - ((P : ℝ) + 1))
  have hmoeb_comb : |Hk 4 - 2 * Hk 3 + Hk 2 -
      (reflectedDensity / (q : ℝ)) * (n.totient : ℝ)| ≤
      20 * ((P : ℝ) + 1) * squarefreeDivisorMass n := by
    have hHk (k : ℕ) (hk : 1 ≤ k) : Hk k =
        ∑ d ∈ n.divisors, (μ d : ℝ) * (((P : ℝ) + 1) *
          (((k * n : ℕ) : ℝ) / (((P + 1) * q * d : ℕ) : ℝ) *
            (harmonic ⌊((k * n : ℕ) : ℝ) / (((P + 1) * q * d : ℕ) : ℝ)⌋₊ : ℝ) -
            (⌊((k * n : ℕ) : ℝ) / (((P + 1) * q * d : ℕ) : ℝ)⌋₊ : ℝ))) := by
      dsimp [Hk]
      rw [sum_coprime_Icc_real hn]
      refine Finset.sum_congr rfl fun d hd => ?_
      congr 1
      have hd0 : 0 < d := Nat.pos_of_mem_divisors hd
      have hdiv_eq : (k * n) / ((P + 1) * q) / d =
          ⌊((k * n : ℕ) : ℝ) / (((P + 1) * q * d : ℕ) : ℝ)⌋₊ := by
        rw [Nat.div_div_eq_div_mul, Nat.floor_div_natCast, Nat.floor_natCast]
      rw [hdiv_eq]
      set N := ⌊((k * n : ℕ) : ℝ) / (((P + 1) * q * d : ℕ) : ℝ)⌋₊
      set t := ((k * n : ℕ) : ℝ) / (((P + 1) * q * d : ℕ) : ℝ)
      have hh : (harmonic N : ℝ) = ∑ j ∈ Icc 1 N, 1 / (j : ℝ) :=
        (_root_.RHTower.Sieve.sum_Icc_one_div_eq_harmonic N).symm
      rw [Finset.sum_sub_distrib, Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul,
        hh, mul_sub, ← mul_assoc, Finset.mul_sum]
      congr 1
      · refine Finset.sum_congr rfl fun j _ => ?_
        dsimp [t]; push_cast; field_simp
      · ring
    have htot : (reflectedDensity / (q : ℝ)) * (n.totient : ℝ) =
        ∑ d ∈ n.divisors, (μ d : ℝ) * (reflectedDensity * (n : ℝ) / ((q : ℝ) * (d : ℝ))) := by
      rw [_root_.RHTower.Sieve.totient_eq_sum_moebius_mul n (by omega), Finset.mul_sum]
      refine Finset.sum_congr rfl fun d hd => ?_
      have hdvd : d ∣ n := Nat.dvd_of_mem_divisors hd
      have hd0 : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_mem_divisors hd
      have hnd : ((n / d : ℕ) : ℝ) = (n : ℝ) / (d : ℝ) := by
        exact_mod_cast Nat.cast_div hdvd hd0.ne'
      rw [hnd]; field_simp [hqR.ne', hd0.ne']
    rw [hHk 4 (by decide), hHk 3 (by decide), hHk 2 (by decide), htot,
      Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib,
      ← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [squarefreeDivisorMass, Finset.mul_sum]
    refine Finset.sum_le_sum fun d hd => ?_
    have hd0 : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_mem_divisors hd
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    set u : ℝ := (n : ℝ) / (((P : ℝ) + 1) * (q : ℝ) * (d : ℝ))
    have hu : 0 < u := by dsimp [u]; positivity
    have ht_eq (k : ℕ) : ((k * n : ℕ) : ℝ) / (((P + 1) * q * d : ℕ) : ℝ) = (k : ℝ) * u := by
      dsimp [u]; push_cast; ring
    rw [ht_eq 4, ht_eq 3, ht_eq 2]
    simp only [Nat.cast_ofNat]
    let Ek (k : ℕ) : ℝ :=
      ((k : ℝ) * u) * (harmonic ⌊(k : ℝ) * u⌋₊ : ℝ) - (⌊(k : ℝ) * u⌋₊ : ℝ) -
        ((k : ℝ) * u) * (Real.log ((k : ℝ) * u) + Real.eulerMascheroniConstant - 1)
    have hmain_d : ((P : ℝ) + 1) *
        (4 * u * (Real.log (4 * u) + Real.eulerMascheroniConstant - 1) -
          2 * (3 * u * (Real.log (3 * u) + Real.eulerMascheroniConstant - 1)) +
          2 * u * (Real.log (2 * u) + Real.eulerMascheroniConstant - 1)) =
        reflectedDensity * (n : ℝ) / ((q : ℝ) * (d : ℝ)) := by
      have hl4 : Real.log (4 * u) = 2 * Real.log 2 + Real.log u := by
        rw [Real.log_mul (by norm_num) hu.ne', show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
        norm_num
      have hl3 : Real.log (3 * u) = Real.log 3 + Real.log u :=
        Real.log_mul (by norm_num) hu.ne'
      have hl2 : Real.log (2 * u) = Real.log 2 + Real.log u :=
        Real.log_mul (by norm_num) hu.ne'
      rw [hl4, hl3, hl2, reflectedDensity]
      have hpu : ((P : ℝ) + 1) * u = (n : ℝ) / ((q : ℝ) * (d : ℝ)) := by
        dsimp [u]; field_simp [hP1R.ne', hqR.ne', hd0.ne']
      linear_combination (10 * Real.log 2 - 6 * Real.log 3) * hpu
    have hdiff_d : (μ d : ℝ) * (((P : ℝ) + 1) *
          (4 * u * (harmonic ⌊4 * u⌋₊ : ℝ) - (⌊4 * u⌋₊ : ℝ))) -
        2 * ((μ d : ℝ) * (((P : ℝ) + 1) *
          (3 * u * (harmonic ⌊3 * u⌋₊ : ℝ) - (⌊3 * u⌋₊ : ℝ)))) +
        (μ d : ℝ) * (((P : ℝ) + 1) *
          (2 * u * (harmonic ⌊2 * u⌋₊ : ℝ) - (⌊2 * u⌋₊ : ℝ))) -
        (μ d : ℝ) * (reflectedDensity * (n : ℝ) / ((q : ℝ) * (d : ℝ))) =
        (μ d : ℝ) * (((P : ℝ) + 1) * (Ek 4 - 2 * Ek 3 + Ek 2)) := by
      rw [← hmain_d]
      dsimp [Ek]; ring
    rw [hdiff_d, abs_mul, abs_mul, abs_of_pos hP1R, mul_comm (20 * ((P : ℝ) + 1)) |(μ d : ℝ)|]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    have hb4 := harmonic_floor_all_pos (show 0 < (4 : ℝ) * u by positivity)
    have hb3 := harmonic_floor_all_pos (show 0 < (3 : ℝ) * u by positivity)
    have hb2 := harmonic_floor_all_pos (show 0 < (2 : ℝ) * u by positivity)
    change |((4 : ℕ) : ℝ) * u * _ - _ - _| ≤ 5 at hb4
    have hE4 : |Ek 4| ≤ 5 := by simpa [Ek] using hb4
    have hE3 : |Ek 3| ≤ 5 := by simpa [Ek] using hb3
    have hE2 : |Ek 2| ≤ 5 := by simpa [Ek] using hb2
    have hcomb : |Ek 4 - 2 * Ek 3 + Ek 2| ≤ 20 := by
      obtain ⟨l4, u4⟩ := abs_le.mp hE4
      obtain ⟨l3, u3⟩ := abs_le.mp hE3
      obtain ⟨l2, u2⟩ := abs_le.mp hE2
      rw [abs_le]; constructor <;> linarith only [l4, u4, l3, u3, l2, u2]
    nlinarith only [hcomb, hP1R]
  -- Combine rounding error and Möbius harmonic bound
  have hsum_split : (∑ u ∈ (Icc 1 (4 * n / q)).filter (n.Coprime ·), g (q * u)) =
      (∑ u ∈ (Icc 1 (4 * n / q)).filter (n.Coprime ·), (((max P (4 * n / (q * u)) : ℕ) : ℝ) - P)) -
        2 * (∑ u ∈ (Icc 1 (4 * n / q)).filter (n.Coprime ·),
          (((max P (3 * n / (q * u)) : ℕ) : ℝ) - P)) +
        (∑ u ∈ (Icc 1 (4 * n / q)).filter (n.Coprime ·),
          (((max P (2 * n / (q * u)) : ℕ) : ℝ) - P)) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun u _ => hgu_eq u
  rw [hsum_split]
  have hr4 := hround_k 4 (by decide) (by decide)
  have hr3 := hround_k 3 (by decide) (by decide)
  have hr2 := hround_k 2 (by decide) (by decide)
  have hr_all : |((∑ u ∈ (Icc 1 (4 * n / q)).filter (n.Coprime ·),
        (((max P (4 * n / (q * u)) : ℕ) : ℝ) - P)) -
      2 * (∑ u ∈ (Icc 1 (4 * n / q)).filter (n.Coprime ·),
        (((max P (3 * n / (q * u)) : ℕ) : ℝ) - P)) +
      (∑ u ∈ (Icc 1 (4 * n / q)).filter (n.Coprime ·),
        (((max P (2 * n / (q * u)) : ℕ) : ℝ) - P))) - (Hk 4 - 2 * Hk 3 + Hk 2)| ≤
      12 * (n : ℝ) / ((q : ℝ) * ((P : ℝ) + 1)) := by
    dsimp [Hk] at hr4 hr3 hr2 ⊢
    obtain ⟨l4, u4⟩ := abs_le.mp hr4
    obtain ⟨l3, u3⟩ := abs_le.mp hr3
    obtain ⟨l2, u2⟩ := abs_le.mp hr2
    rw [abs_le]
    constructor <;>
      linarith only [l4, u4, l3, u3, l2, u2,
        show (4 : ℝ) * n / (q * (P + 1)) + 2 * ((3 : ℝ) * n / (q * (P + 1))) +
          (2 : ℝ) * n / (q * (P + 1)) = 12 * n / (q * (P + 1)) by ring]
  have hmass1 := one_le_squarefreeDivisorMass hn
  have hr_mass : 12 * (n : ℝ) / ((q : ℝ) * ((P : ℝ) + 1)) ≤
      (12 * (n : ℝ) / ((q : ℝ) * ((P : ℝ) + 1))) * squarefreeDivisorMass n :=
    le_mul_of_one_le_right (by positivity) hmass1
  have htri := abs_add_le
    (((∑ u ∈ (Icc 1 (4 * n / q)).filter (n.Coprime ·),
        (((max P (4 * n / (q * u)) : ℕ) : ℝ) - P)) -
      2 * (∑ u ∈ (Icc 1 (4 * n / q)).filter (n.Coprime ·),
        (((max P (3 * n / (q * u)) : ℕ) : ℝ) - P)) +
      (∑ u ∈ (Icc 1 (4 * n / q)).filter (n.Coprime ·),
        (((max P (2 * n / (q * u)) : ℕ) : ℝ) - P))) - (Hk 4 - 2 * Hk 3 + Hk 2))
    (Hk 4 - 2 * Hk 3 + Hk 2 - (reflectedDensity / (q : ℝ)) * (n.totient : ℝ))
  rw [sub_add_sub_cancel] at htri
  linarith only [htri, hr_all, hr_mass, hmoeb_comb]

/-! ### 4. Universal complex and real oscillatory wave transmission -/

/-- Explicit strip rate governing the wave-transmission remainder on `0 < Re z < 1`. -/
def waveTransmissionRate (z : ℂ) : ℝ :=
  (12 * (3 + 2 / ‖1 - z‖ + 3 * ‖z‖ / z.re) + 4) / ‖z‖ + 12

theorem waveTransmissionRate_nonneg {z : ℂ} (hz0 : 0 < z.re) :
    0 ≤ waveTransmissionRate z := by
  unfold waveTransmissionRate
  positivity

private theorem cpow_pos_mul {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (w : ℂ) :
    ((a * b : ℝ) : ℂ) ^ w = (a : ℂ) ^ w * (b : ℂ) ^ w := by
  have hab : 0 < a * b := mul_pos ha hb
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hab.ne'),
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr ha.ne'),
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hb.ne'),
    ← Complex.ofReal_log hab.le, ← Complex.ofReal_log ha.le, ← Complex.ofReal_log hb.le,
    Real.log_mul ha.ne' hb.ne', Complex.ofReal_add, add_mul, Complex.exp_add]

private theorem cpow_pos_div {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (w : ℂ) :
    ((a / b : ℝ) : ℂ) ^ w = (a : ℂ) ^ w / (b : ℂ) ^ w := by
  have hdiv : 0 < a / b := div_pos ha hb
  rw [eq_div_iff (Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.ofReal_ne_zero.mpr hb.ne'))),
    ← cpow_pos_mul hdiv hb w, div_mul_cancel₀ a hb.ne']

/-- Unified partial-sum approximation for `∑_{1 ≤ j ≤ ⌊t⌋₊} j^{-z}` across **all** real `t > 0`
and `0 < Re z < 1`, eliminating small-vs-large divisor case splits in Möbius inversion. -/
private theorem zeta_partial_sum_all_pos {z : ℂ} (hz0 : 0 < z.re) (hz1 : z.re < 1)
    {t : ℝ} (ht : 0 < t) :
    ‖(∑ j ∈ Icc 1 ⌊t⌋₊, ((j : ℝ) : ℂ) ^ (-z)) - riemannZeta z -
        (t : ℂ) ^ (1 - z) / (1 - z)‖ ≤
      (3 + 2 / ‖1 - z‖ + 3 * ‖z‖ / z.re) * t ^ (-z.re) := by
  have hzne1 : z ≠ 1 := fun he => by rw [he, Complex.one_re] at hz1; exact lt_irrefl 1 hz1
  have h1z_ne : 1 - z ≠ 0 := sub_ne_zero.mpr hzne1.symm
  have h1z_pos : 0 < ‖1 - z‖ := norm_pos_iff.mpr h1z_ne
  by_cases ht1 : 1 ≤ t
  · set N := ⌊t⌋₊
    have hN1 : 1 ≤ N := Nat.le_floor (by exact_mod_cast ht1)
    have hNR1 : (1 : ℝ) ≤ N := by exact_mod_cast hN1
    have hN_pos : (0 : ℝ) < N := by linarith
    have hNt : (N : ℝ) ≤ t := Nat.floor_le ht.le
    have ht_lt : t < (N : ℝ) + 1 := Nat.lt_floor_add_one t
    have ht_le_2N : t ≤ 2 * (N : ℝ) := by linarith only [hNR1, ht_lt]
    have hN_rpow_le : (N : ℝ) ^ (-z.re) ≤ 2 * t ^ (-z.re) := by
      have hdiv : t / 2 ≤ (N : ℝ) := by linarith only [ht_le_2N]
      have h1 : (N : ℝ) ^ (-z.re) ≤ (t / 2) ^ (-z.re) :=
        Real.rpow_le_rpow_of_nonpos (half_pos ht) hdiv (by linarith)
      have h2 : (t / 2) ^ (-z.re) = 2 ^ z.re * t ^ (-z.re) := by
        rw [div_eq_mul_inv, Real.mul_rpow ht.le (by norm_num),
          Real.inv_rpow (by norm_num : (0 : ℝ) ≤ 2), ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2),
          neg_neg, mul_comm]
      have h2pow : (2 : ℝ) ^ z.re ≤ 2 := by
        simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hz1.le
      exact h1.trans (h2.trans_le (mul_le_mul_of_nonneg_right h2pow (Real.rpow_nonneg ht.le _)))
    have htrunc := _root_.RHTower.Sieve.riemannZeta_eq_sum_add_tail hz0 hzne1 hN1
    have htail := _root_.RHTower.Sieve.norm_integral_Ioi_fract_cpow_le hz0 hN1
    have hmvt : ‖((t : ℂ) ^ (1 - z) - ((N : ℝ) : ℂ) ^ (1 - z)) / (1 - z)‖ ≤ (N : ℝ) ^ (-z.re) := by
      rw [norm_div, div_le_iff₀ h1z_pos]
      have hm := _root_.RHTower.norm_ofReal_cpow_sub_cpow_le hN_pos hNt (ρ := 1 - z)
        (by simp; linarith) (by simp; linarith)
      have hexp : (1 - z).re - 1 = -z.re := by simp
      rw [hexp] at hm
      have hdiff1 : t - (N : ℝ) ≤ 1 := by linarith only [ht_lt]
      calc ‖(t : ℂ) ^ (1 - z) - ((N : ℝ) : ℂ) ^ (1 - z)‖
          ≤ ‖1 - z‖ * (t - (N : ℝ)) * (N : ℝ) ^ (-z.re) := hm
        _ ≤ ‖1 - z‖ * (N : ℝ) ^ (-z.re) :=
            mul_le_mul_of_nonneg_right (mul_le_of_le_one_right (norm_nonneg _) hdiff1)
              (Real.rpow_nonneg hN_pos.le _)
        _ = (N : ℝ) ^ (-z.re) * ‖1 - z‖ := by ring
    have hid : (∑ j ∈ Icc 1 N, ((j : ℝ) : ℂ) ^ (-z)) - riemannZeta z -
        (t : ℂ) ^ (1 - z) / (1 - z) =
        z * (∫ u in Set.Ioi (N : ℝ), ((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-(z + 1))) -
          ((t : ℂ) ^ (1 - z) - ((N : ℝ) : ℂ) ^ (1 - z)) / (1 - z) := by
      have hsub1 : z - 1 = -(1 - z) := by ring
      linear_combination (norm := (field_simp [h1z_ne, sub_ne_zero.mpr hzne1]; ring)) -htrunc
    rw [hid]
    refine (norm_sub_le _ _).trans ?_
    rw [norm_mul]
    have h1 : ‖z‖ * ‖∫ u in Set.Ioi (N : ℝ), ((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-(z + 1))‖ ≤
        (2 * ‖z‖ / z.re) * t ^ (-z.re) := by
      calc ‖z‖ * ‖∫ u in Set.Ioi (N : ℝ), ((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-(z + 1))‖
          ≤ ‖z‖ * ((N : ℝ) ^ (-z.re) / z.re) := mul_le_mul_of_nonneg_left htail (norm_nonneg z)
        _ ≤ ‖z‖ * (2 * t ^ (-z.re) / z.re) :=
            mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hN_rpow_le hz0.le) (norm_nonneg z)
        _ = (2 * ‖z‖ / z.re) * t ^ (-z.re) := by ring
    have h2 : ‖((t : ℂ) ^ (1 - z) - ((N : ℝ) : ℂ) ^ (1 - z)) / (1 - z)‖ ≤ 2 * t ^ (-z.re) :=
      hmvt.trans hN_rpow_le
    have hnn : 0 ≤ t ^ (-z.re) := Real.rpow_nonneg ht.le _
    have hextra : 0 ≤ (1 + 2 / ‖1 - z‖ + ‖z‖ / z.re) * t ^ (-z.re) := by positivity
    have hcomb_t : (2 * ‖z‖ / z.re) * t ^ (-z.re) + 2 * t ^ (-z.re) +
        (1 + 2 / ‖1 - z‖ + ‖z‖ / z.re) * t ^ (-z.re) =
        (3 + 2 / ‖1 - z‖ + 3 * ‖z‖ / z.re) * t ^ (-z.re) := by ring
    linarith only [h1, h2, hextra, hcomb_t]
  · push Not at ht1
    have hfl0 : ⌊t⌋₊ = 0 := Nat.floor_eq_zero.mpr ht1
    rw [hfl0]
    simp only [Icc_eq_empty (by decide : ¬ 1 ≤ 0), Finset.sum_empty, zero_sub]
    have hzeta := _root_.RHTower.Sieve.norm_riemannZeta_le_truncated hz0 hzne1 (N := 1) le_rfl
    simp only [Icc_self, Finset.sum_singleton, Nat.cast_one, Real.one_rpow,
      norm_sub_rev z 1, mul_one_div] at hzeta
    have h1_le_t : 1 ≤ t ^ (-z.re) :=
      (Real.one_lt_rpow_of_pos_of_lt_one_of_neg ht ht1 (by linarith)).le
    have ht_1b : t ^ (1 - z.re) ≤ 1 :=
      Real.rpow_le_one ht.le ht1.le (by linarith)
    have ht_term : ‖(t : ℂ) ^ (1 - z) / (1 - z)‖ ≤ 1 / ‖1 - z‖ := by
      rw [norm_div, Complex.norm_cpow_eq_rpow_re_of_pos ht, show (1 - z).re = 1 - z.re by simp]
      exact div_le_div_of_nonneg_right ht_1b h1z_pos.le
    calc ‖-riemannZeta z - (t : ℂ) ^ (1 - z) / (1 - z)‖
        ≤ ‖riemannZeta z‖ + ‖(t : ℂ) ^ (1 - z) / (1 - z)‖ :=
            (norm_sub_le (-riemannZeta z) _).trans_eq (by rw [norm_neg])
      _ ≤ (1 + 1 / ‖1 - z‖ + ‖z‖ / z.re) + 1 / ‖1 - z‖ := add_le_add hzeta ht_term
      _ ≤ (3 + 2 / ‖1 - z‖ + 3 * ‖z‖ / z.re) * 1 := by
            have h0 : 0 ≤ ‖z‖ / z.re := by positivity
            have h2 : 2 / ‖1 - z‖ = 1 / ‖1 - z‖ + 1 / ‖1 - z‖ := by ring
            have h3 : 3 * ‖z‖ / z.re = 3 * (‖z‖ / z.re) := mul_div_assoc 3 ‖z‖ z.re
            linarith only [h0, h2, h3]
      _ ≤ (3 + 2 / ‖1 - z‖ + 3 * ‖z‖ / z.re) * t ^ (-z.re) :=
            mul_le_mul_of_nonneg_left h1_le_t (by positivity)

/-- Complex clipped-cofactor slice operator acting on `G : ℝ → ℂ`. -/
def clippedCofactorComplexSliceOp (n P q : ℕ) (G : ℝ → ℂ) : ℂ :=
  ∑ v ∈ (Icc 2 (4 * n)).filter (fun v => n.Coprime v ∧ q ∣ v),
    (G (max P (4 * n / v) : ℕ) - 2 * G (max P (3 * n / v) : ℕ) + G (max P (2 * n / v) : ℕ))

/-- Complex second difference `2 G(3n) - G(2n) - G(4n)` at the reflected midpoint. -/
def midpointComplexSecondDiff (n : ℕ) (G : ℝ → ℂ) : ℂ :=
  2 * G (3 * n : ℕ) - G (2 * n : ℕ) - G (4 * n : ℕ)

/-- **Universal complex power-mode transmission across cofactor-divisibility slices.** -/
theorem clippedCofactorComplexSliceOp_cpow {n P q : ℕ} (hn : 1 ≤ n) (hP1 : 1 ≤ P)
    (hP2 : P ≤ 2 * n) (hq : 1 ≤ q) (hcop : n.Coprime q) {z : ℂ} (hz0 : 0 < z.re)
    (hz1 : z.re < 1) :
    ‖clippedCofactorComplexSliceOp n P q (fun x => (x : ℂ) ^ z / z) -
        (midpointMultiplier z / z) *
          ((if q = 1 then (1 : ℂ) else 0) -
            ((q : ℝ) : ℂ) ^ (-z) * riemannZeta z * coprimeEulerFactor n z) *
          ((n : ℝ) : ℂ) ^ z‖ ≤
      waveTransmissionRate z *
        ((P : ℝ) ^ z.re + (n : ℝ) * (P : ℝ) ^ (z.re - 2)) * squarefreeDivisorMass n := by
  classical
  have hzne0 : z ≠ 0 := fun he => by rw [he, Complex.zero_re] at hz0; exact lt_irrefl 0 hz0
  have hzne1 : z ≠ 1 := fun he => by rw [he, Complex.one_re] at hz1; exact lt_irrefl 1 hz1
  have h1z_ne : 1 - z ≠ 0 := sub_ne_zero.mpr hzne1.symm
  have hz_pos : 0 < ‖z‖ := norm_pos_iff.mpr hzne0
  have hq0 : 0 < q := hq
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq0
  have hPR : (0 : ℝ) < P := by exact_mod_cast hP1
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  let gz (x : ℝ) : ℂ := (x : ℂ) ^ z / z
  let gv (v : ℕ) : ℂ :=
    gz (max P (4 * n / v) : ℕ) - 2 * gz (max P (3 * n / v) : ℕ) + gz (max P (2 * n / v) : ℕ)
  have hgv1 : gv 1 = -(midpointMultiplier z / z) * ((n : ℝ) : ℂ) ^ z := by
    have hc (k : ℕ) (hk : 0 < k) : (((k * n : ℕ) : ℝ) : ℂ) ^ z =
        ((k : ℝ) : ℂ) ^ z * ((n : ℝ) : ℂ) ^ z := by
      have hkR : (0 : ℝ) < k := by exact_mod_cast hk
      simpa only [Nat.cast_mul] using cpow_pos_mul hkR hnR z
    change gz ((max P (4 * n / 1) : ℕ) : ℝ) - 2 * gz ((max P (3 * n / 1) : ℕ) : ℝ) +
        gz ((max P (2 * n / 1) : ℕ) : ℝ) = _
    rw [Nat.div_one, Nat.div_one, Nat.div_one, max_eq_right (by omega), max_eq_right (by omega),
      max_eq_right hP2]
    change (((4 * n : ℕ) : ℝ) : ℂ) ^ z / z - 2 * ((((3 * n : ℕ) : ℝ) : ℂ) ^ z / z) +
        ((((2 * n : ℕ) : ℝ) : ℂ) ^ z / z) = _
    rw [hc 4 (by decide), hc 3 (by decide), hc 2 (by decide), midpointMultiplier]
    simp only [Nat.cast_ofNat, Complex.ofReal_ofNat]
    ring
  -- Relate `clippedCofactorComplexSliceOp` to full `u ∈ Icc 1 (4*n/q)` sum minus `1_{q=1} * gv 1`
  have hslice_u : clippedCofactorComplexSliceOp n P q gz =
      (∑ u ∈ (Icc 1 (4 * n / q)).filter (n.Coprime ·), gv (q * u)) -
        (if q = 1 then gv 1 else 0) := by
    unfold clippedCofactorComplexSliceOp
    change ∑ v ∈ (Icc 2 (4 * n)).filter (fun v => n.Coprime v ∧ q ∣ v), gv v = _
    have hmap : ∑ u ∈ (Icc 1 (4 * n / q)).filter (n.Coprime ·), gv (q * u) =
        ∑ v ∈ (Icc 1 (4 * n)).filter (fun v => n.Coprime v ∧ q ∣ v), gv v := by
      refine Finset.sum_nbij' (fun u => q * u) (fun v => v / q) ?_ ?_ ?_ ?_ (fun _ _ => rfl)
      · intro u hu
        obtain ⟨huI, huc⟩ := mem_filter.mp hu
        obtain ⟨hu1, hu4⟩ := mem_Icc.mp huI
        exact mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.mul_pos hq0 hu1,
          (Nat.le_div_iff_mul_le hq0).mp hu4 |>.trans_eq' (mul_comm _ _)⟩,
          Nat.Coprime.mul_right hcop huc, dvd_mul_right q u⟩
      · intro v hv
        obtain ⟨hvI, hvc, hqv⟩ := mem_filter.mp hv
        obtain ⟨hv1, hv4⟩ := mem_Icc.mp hvI
        have hmul : q * (v / q) = v := Nat.mul_div_cancel' hqv
        exact mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.div_pos (Nat.le_of_dvd hv1 hqv) hq0,
          Nat.div_le_div_right hv4⟩, (Nat.coprime_mul_iff_right.mp (hmul ▸ hvc)).2⟩
      · intro u _; exact Nat.mul_div_right u hq0
      · intro v hv; exact Nat.mul_div_cancel' (mem_filter.mp hv).2.2
    rw [hmap]
    have h12 : Icc 1 (4 * n) = insert 1 (Icc 2 (4 * n)) := by
      ext v; simp only [mem_Icc, mem_insert]; omega
    rw [h12, Finset.filter_insert]
    by_cases hq1 : q = 1
    · subst hq1; simp [Nat.coprime_one_right_eq_true]
    · have hnd : ¬ q ∣ 1 := fun hd => hq1 (Nat.eq_one_of_dvd_one hd)
      rw [if_neg (fun h => hnd h.2), if_neg hq1, sub_zero]
  -- Compare integer quotient `gz (max P (k*n/(q*u))) - gz P` with smooth quotient on `u ≤ (k*n)/(P*q)`
  let Wk (k : ℕ) : ℂ :=
    ∑ u ∈ (Icc 1 ((k * n) / (P * q))).filter (n.Coprime ·),
      (gz (((k * n : ℕ) : ℝ) / ((q * u : ℕ) : ℝ)) - gz (P : ℝ))
  have hround_k (k : ℕ) (hk1 : 1 ≤ k) (hk4 : k ≤ 4) :
      ‖(∑ u ∈ (Icc 1 (4 * n / q)).filter (n.Coprime ·),
          (gz (max P (k * n / (q * u)) : ℕ) - gz (P : ℝ))) - Wk k‖ ≤
        (k : ℝ) * (n : ℝ) * (P : ℝ) ^ (z.re - 2) := by
    let Bku (u : ℕ) : ℂ :=
      if u ≤ (k * n) / (P * q) then gz (((k * n : ℕ) : ℝ) / ((q * u : ℕ) : ℝ)) - gz (P : ℝ)
      else 0
    have hsub_u : ((Icc 1 ((k * n) / (P * q))).filter (n.Coprime ·)) ⊆
        (Icc 1 (4 * n / q)).filter (n.Coprime ·) := by
      intro u hu
      obtain ⟨huI, huc⟩ := mem_filter.mp hu
      obtain ⟨hu1, huhi⟩ := mem_Icc.mp huI
      have hle : (k * n) / (P * q) ≤ 4 * n / q := by
        calc (k * n) / (P * q) ≤ (k * n) / (1 * q) :=
              Nat.div_le_div_left (Nat.mul_le_mul_right q hP1) (by positivity)
          _ = k * n / q := by rw [one_mul]
          _ ≤ 4 * n / q := Nat.div_le_div_right (Nat.mul_le_mul_right n hk4)
      exact mem_filter.mpr ⟨mem_Icc.mpr ⟨hu1, huhi.trans hle⟩, huc⟩
    have hWk_eq : Wk k = ∑ u ∈ (Icc 1 (4 * n / q)).filter (n.Coprime ·), Bku u := by
      dsimp [Wk, Bku]
      rw [← Finset.sum_subset hsub_u]
      · refine Finset.sum_congr rfl fun u hu => by rw [if_pos (mem_Icc.mp (mem_filter.mp hu).1).2]
      · intro u _ hunot
        rw [if_neg (fun hle => hunot (mem_filter.mpr
          ⟨mem_Icc.mpr ⟨(mem_Icc.mp (mem_filter.mp ‹_›).1).1, hle⟩,
            (mem_filter.mp ‹_›).2⟩))]
    rw [hWk_eq, ← Finset.sum_sub_distrib]
    refine (norm_sum_le _ _).trans ?_
    have hterm (u : ℕ) (hu : u ∈ (Icc 1 (4 * n / q)).filter (n.Coprime ·)) :
        ‖(gz (max P (k * n / (q * u)) : ℕ) - gz (P : ℝ)) - Bku u‖ ≤
          if u ≤ (k * n) / (P * q) then (P : ℝ) ^ (z.re - 1) else 0 := by
      have hu1 : 1 ≤ u := (mem_Icc.mp (mem_filter.mp hu).1).1
      have hqu0 : 0 < q * u := Nat.mul_pos hq0 hu1
      dsimp [Bku]
      split_ifs with hle
      · have hm : (P * q) * u ≤ k * n :=
          (Nat.le_div_iff_mul_le (Nat.mul_pos hP1 hq0)).mp hle |>.trans_eq' (mul_comm _ _)
        have hP_le : P ≤ k * n / (q * u) :=
          (Nat.le_div_iff_mul_le hqu0).mpr (by linarith only [hm, show (P * q) * u = P * (q * u) by ring])
        rw [max_eq_right hP_le]
        set x₁ : ℝ := ((k * n / (q * u) : ℕ) : ℝ)
        set x₂ : ℝ := ((k * n : ℕ) : ℝ) / ((q * u : ℕ) : ℝ)
        have hPx₁ : (P : ℝ) ≤ x₁ := by dsimp [x₁]; exact_mod_cast hP_le
        have hx₁_pos : 0 < x₁ := hPR.trans_le hPx₁
        have hx₁₂ : x₁ ≤ x₂ := Nat.cast_div_le
        have hdiff1 : x₂ - x₁ ≤ 1 := by
          have := (abs_le.mp (_root_.RHTower.Sieve.abs_natDiv_sub_div_le (N := k * n) hqu0)).1
          dsimp [x₁, x₂]; linarith
        have hsub_gz : (gz x₁ - gz (P : ℝ)) - (gz x₂ - gz (P : ℝ)) =
            -((x₂ : ℂ) ^ z - (x₁ : ℂ) ^ z) / z := by
          dsimp [gz]; ring
        rw [hsub_gz, norm_div, norm_neg, div_le_iff₀ hz_pos]
        have hmvt := _root_.RHTower.norm_ofReal_cpow_sub_cpow_le hx₁_pos hx₁₂ hz0 hz1.le
        have hrpow : x₁ ^ (z.re - 1) ≤ (P : ℝ) ^ (z.re - 1) :=
          Real.rpow_le_rpow_of_nonpos hPR hPx₁ (by linarith)
        calc ‖(x₂ : ℂ) ^ z - (x₁ : ℂ) ^ z‖
            ≤ ‖z‖ * (x₂ - x₁) * x₁ ^ (z.re - 1) := hmvt
          _ ≤ ‖z‖ * (P : ℝ) ^ (z.re - 1) :=
              mul_le_mul (mul_le_of_le_one_right (norm_nonneg z) hdiff1) hrpow
                (Real.rpow_nonneg hx₁_pos.le _) (norm_nonneg z)
          _ = (P : ℝ) ^ (z.re - 1) * ‖z‖ := by ring
      · push Not at hle
        have hm : k * n < u * (P * q) :=
          (Nat.div_lt_iff_lt_mul (Nat.mul_pos hP1 hq0)).mp hle
        have hlt_P : k * n / (q * u) < P :=
          (Nat.div_lt_iff_lt_mul hqu0).mpr (by linarith only [hm, show u * (P * q) = P * (q * u) by ring])
        rw [max_eq_left hlt_P.le]
        simp
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    have hcard_le : (((Icc 1 (4 * n / q)).filter (n.Coprime ·) |>.filter
        (fun u => u ≤ (k * n) / (P * q))).card : ℝ) ≤ (k : ℝ) * (n : ℝ) / (P : ℝ) := by
      have hsub2 : ((Icc 1 (4 * n / q)).filter (n.Coprime ·)).filter
          (fun u => u ≤ (k * n) / (P * q)) ⊆ Icc 1 ((k * n) / (P * q)) := by
        intro u hu
        obtain ⟨hu1, hu2⟩ := mem_filter.mp hu
        exact mem_Icc.mpr ⟨(mem_Icc.mp (mem_filter.mp hu1).1).1, hu2⟩
      have hc1 : (((Icc 1 (4 * n / q)).filter (n.Coprime ·) |>.filter
          (fun u => u ≤ (k * n) / (P * q))).card : ℝ) ≤ (((k * n) / (P * q) : ℕ) : ℝ) := by
        exact_mod_cast (Finset.card_le_card hsub2).trans_eq (by simp)
      have hc2 : (((k * n) / (P * q) : ℕ) : ℝ) ≤ ((k * n : ℕ) : ℝ) / (((P * q : ℕ) : ℝ)) :=
        Nat.cast_div_le
      have hc3 : ((k * n : ℕ) : ℝ) / (((P * q : ℕ) : ℝ)) ≤ (k : ℝ) * (n : ℝ) / (P : ℝ) := by
        push_cast
        exact div_le_div_of_nonneg_left (by positivity) hPR
          (le_mul_of_one_le_right hPR.le (by exact_mod_cast hq))
      exact hc1.trans (hc2.trans hc3)
    calc _ ≤ ((k : ℝ) * (n : ℝ) / (P : ℝ)) * (P : ℝ) ^ (z.re - 1) :=
            mul_le_mul_of_nonneg_right hcard_le (Real.rpow_nonneg hPR.le _)
      _ = (k : ℝ) * (n : ℝ) * ((P : ℝ) ^ (-1 : ℝ) * (P : ℝ) ^ (z.re - 1)) := by
            rw [Real.rpow_neg_one]; ring
      _ = (k : ℝ) * (n : ℝ) * (P : ℝ) ^ (z.re - 2) := by
            rw [← Real.rpow_add hPR]; congr 2; ring
  -- Möbius inversion of `Wk 4 - 2 * Wk 3 + Wk 2`
  set Kz : ℝ := 3 + 2 / ‖1 - z‖ + 3 * ‖z‖ / z.re
  have hmoeb_w : ‖(Wk 4 - 2 * Wk 3 + Wk 2) -
      (-(midpointMultiplier z / z) *
        (((q : ℝ) : ℂ) ^ (-z) * riemannZeta z * coprimeEulerFactor n z) *
        ((n : ℝ) : ℂ) ^ z)‖ ≤
      ((12 * Kz + 4) / ‖z‖) * (P : ℝ) ^ z.re * squarefreeDivisorMass n := by
    have hWk_moeb (k : ℕ) (hk : 1 ≤ k) : Wk k =
        ∑ d ∈ n.divisors, (μ d : ℂ) *
          ((((k * n : ℕ) : ℝ) : ℂ) ^ z / z * ((q : ℝ) : ℂ) ^ (-z) * ((d : ℝ) : ℂ) ^ (-z) *
            (∑ j ∈ Icc 1 ⌊((k * n : ℕ) : ℝ) / (((P * q * d : ℕ) : ℝ))⌋₊, ((j : ℝ) : ℂ) ^ (-z)) -
            (P : ℂ) ^ z / z *
              ((⌊((k * n : ℕ) : ℝ) / (((P * q * d : ℕ) : ℝ))⌋₊ : ℝ) : ℂ)) := by
      dsimp [Wk]
      rw [sum_coprime_Icc_complex hn]
      refine Finset.sum_congr rfl fun d hd => ?_
      congr 1
      have hd0 : 0 < d := Nat.pos_of_mem_divisors hd
      have hdR : (0 : ℝ) < d := by exact_mod_cast hd0
      have hdiv_eq : (k * n) / (P * q) / d =
          ⌊((k * n : ℕ) : ℝ) / (((P * q * d : ℕ) : ℝ))⌋₊ := by
        rw [Nat.div_div_eq_div_mul, Nat.floor_div_natCast, Nat.floor_natCast]
      rw [hdiv_eq]
      set N := ⌊((k * n : ℕ) : ℝ) / (((P * q * d : ℕ) : ℝ))⌋₊
      rw [Finset.sum_sub_distrib, Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul,
        Finset.mul_sum]
      congr 1
      · refine Finset.sum_congr rfl fun j hj => ?_
        have hj1 : 1 ≤ j := (mem_Icc.mp hj).1
        have hjR : (0 : ℝ) < j := by exact_mod_cast hj1
        have hknR : (0 : ℝ) < (k * n : ℕ) := by exact_mod_cast Nat.mul_pos hk hn
        have hqdj : (0 : ℝ) < (q * (d * j) : ℕ) := by
          exact_mod_cast Nat.mul_pos hq0 (Nat.mul_pos hd0 hj1)
        rw [show gz (((k * n : ℕ) : ℝ) / ((q * (d * j) : ℕ) : ℝ)) =
            ((((k * n : ℕ) : ℝ) / ((q * (d * j) : ℕ) : ℝ) : ℝ) : ℂ) ^ z / z from rfl,
          cpow_pos_div hknR hqdj z]
        have hden_pow : (((q * (d * j) : ℕ) : ℝ) : ℂ) ^ z =
            ((q : ℝ) : ℂ) ^ z * ((d : ℝ) : ℂ) ^ z * ((j : ℝ) : ℂ) ^ z := by
          have hd_j : (0 : ℝ) < (d * j : ℕ) := by exact_mod_cast Nat.mul_pos hd0 hj1
          rw [show ((q * (d * j) : ℕ) : ℝ) = (q : ℝ) * ((d * j : ℕ) : ℝ) by push_cast; rfl,
            cpow_pos_mul hqR hd_j z,
            show ((d * j : ℕ) : ℝ) = (d : ℝ) * (j : ℝ) by push_cast; rfl,
            cpow_pos_mul hdR hjR z, mul_assoc]
        rw [hden_pow, Complex.cpow_neg, Complex.cpow_neg, Complex.cpow_neg]
        field_simp [hzne0]
        simp only [Complex.ofReal_natCast]
      · dsimp [gz]; ring
    have htarget_moeb :
        -(midpointMultiplier z / z) *
            (((q : ℝ) : ℂ) ^ (-z) * riemannZeta z * coprimeEulerFactor n z) *
            ((n : ℝ) : ℂ) ^ z =
          ∑ d ∈ n.divisors, (μ d : ℂ) *
            (-(midpointMultiplier z / z) * ((q : ℝ) : ℂ) ^ (-z) * ((d : ℝ) : ℂ) ^ (-z) *
              riemannZeta z * ((n : ℝ) : ℂ) ^ z) := by
      unfold coprimeEulerFactor
      rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun d _ => by ring
    rw [hWk_moeb 4 (by decide), hWk_moeb 3 (by decide), hWk_moeb 2 (by decide), htarget_moeb,
      Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib,
      ← Finset.sum_sub_distrib]
    refine (norm_sum_le _ _).trans ?_
    rw [squarefreeDivisorMass, Finset.mul_sum]
    refine Finset.sum_le_sum fun d hd => ?_
    have hd0 : 0 < d := Nat.pos_of_mem_divisors hd
    have hdR : (0 : ℝ) < d := by exact_mod_cast hd0
    have hmu_norm : ‖(μ d : ℂ)‖ = |(μ d : ℝ)| := by
      have hc : (μ d : ℂ) = ((μ d : ℝ) : ℂ) := by norm_cast
      rw [hc, Complex.norm_real, Real.norm_eq_abs]
    set u : ℝ := (n : ℝ) / ((P : ℝ) * (q : ℝ) * (d : ℝ))
    have hu : 0 < u := by dsimp [u]; positivity
    have ht_eq (k : ℕ) : ((k * n : ℕ) : ℝ) / (((P * q * d : ℕ) : ℝ)) = (k : ℝ) * u := by
      dsimp [u]; push_cast; ring
    rw [ht_eq 4, ht_eq 3, ht_eq 2]
    let Sk (k : ℕ) : ℂ := ∑ j ∈ Icc 1 ⌊(k : ℝ) * u⌋₊, ((j : ℝ) : ℂ) ^ (-z)
    let Ek (k : ℕ) : ℂ := Sk k - riemannZeta z - (((k : ℝ) * u : ℝ) : ℂ) ^ (1 - z) / (1 - z)
    have hkn_pow (k : ℕ) (hk : 0 < k) :
        (((k * n : ℕ) : ℝ) : ℂ) ^ z = ((k : ℝ) : ℂ) ^ z * ((n : ℝ) : ℂ) ^ z := by
      have hkR : (0 : ℝ) < k := by exact_mod_cast hk
      simpa only [Nat.cast_mul] using cpow_pos_mul hkR hnR z
    -- Key algebraic cancellation of `(k n)^z (q d)^{-z} (k u)^{1 - z}` across `4 - 2*3 + 2 = 0`
    have hlin_id (k : ℕ) (hk : 0 < k) :
        (((k * n : ℕ) : ℝ) : ℂ) ^ z / z * ((q : ℝ) : ℂ) ^ (-z) * ((d : ℝ) : ℂ) ^ (-z) *
            ((((k : ℝ) * u : ℝ) : ℂ) ^ (1 - z) / (1 - z)) =
          (k : ℂ) * ((u : ℂ) * ((P : ℝ) : ℂ) ^ z / (z * (1 - z))) := by
      have hkR : (0 : ℝ) < k := by exact_mod_cast hk
      have hku : 0 < (k : ℝ) * u := mul_pos hkR hu
      have hknR : (0 : ℝ) < (k * n : ℕ) := by exact_mod_cast Nat.mul_pos hk hn
      have hprod : ((k * n : ℕ) : ℝ) = ((k : ℝ) * u) * ((P : ℝ) * ((q : ℝ) * (d : ℝ))) := by
        dsimp [u]; push_cast; field_simp [hPR.ne', hqR.ne', hdR.ne']
      have hcp1 : (((k * n : ℕ) : ℝ) : ℂ) ^ z =
          (((k : ℝ) * u : ℝ) : ℂ) ^ z * ((P : ℝ) : ℂ) ^ z * ((q : ℝ) : ℂ) ^ z *
            ((d : ℝ) : ℂ) ^ z := by
        rw [hprod, cpow_pos_mul hku (by positivity) z, cpow_pos_mul hPR (by positivity) z,
          cpow_pos_mul hqR hdR z]
        ring
      have hcp_ku : (((k : ℝ) * u : ℝ) : ℂ) ^ z * (((k : ℝ) * u : ℝ) : ℂ) ^ (1 - z) =
          (k : ℂ) * (u : ℂ) := by
        rw [← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hku.ne'), add_sub_cancel,
          Complex.cpow_one]
        push_cast; rfl
      have hq_inv : ((q : ℝ) : ℂ) ^ z * ((q : ℝ) : ℂ) ^ (-z) = 1 := by
        rw [← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hqR.ne'), add_neg_cancel,
          Complex.cpow_zero]
      have hd_inv : ((d : ℝ) : ℂ) ^ z * ((d : ℝ) : ℂ) ^ (-z) = 1 := by
        rw [← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hdR.ne'), add_neg_cancel,
          Complex.cpow_zero]
      rw [hcp1]
      calc ((((k : ℝ) * u : ℝ) : ℂ) ^ z * ((P : ℝ) : ℂ) ^ z * ((q : ℝ) : ℂ) ^ z * ((d : ℝ) : ℂ) ^ z) /
              z * ((q : ℝ) : ℂ) ^ (-z) * ((d : ℝ) : ℂ) ^ (-z) *
              ((((k : ℝ) * u : ℝ) : ℂ) ^ (1 - z) / (1 - z))
          = ((((k : ℝ) * u : ℝ) : ℂ) ^ z * (((k : ℝ) * u : ℝ) : ℂ) ^ (1 - z)) *
              (((q : ℝ) : ℂ) ^ z * ((q : ℝ) : ℂ) ^ (-z)) *
              (((d : ℝ) : ℂ) ^ z * ((d : ℝ) : ℂ) ^ (-z)) *
              (((P : ℝ) : ℂ) ^ z / (z * (1 - z))) := by field_simp [hzne0, h1z_ne]
        _ = (k : ℂ) * ((u : ℂ) * ((P : ℝ) : ℂ) ^ z / (z * (1 - z))) := by
              rw [hcp_ku, hq_inv, hd_inv]; ring
    have hfl_fract (k : ℕ) (hk : 0 < k) :
        ((⌊(k : ℝ) * u⌋₊ : ℝ) : ℂ) = (k : ℂ) * (u : ℂ) - ((Int.fract ((k : ℝ) * u) : ℝ) : ℂ) := by
      have hkR : (0 : ℝ) < k := by exact_mod_cast hk
      have hf := _root_.RHTower.natFloor_cast_eq_sub_fract (mul_pos hkR hu).le
      have hc := congrArg Complex.ofReal hf
      simpa only [Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_natCast] using hc
    -- Express the `d`-th summand in terms of `Ek` and `Int.fract`
    let Ak (k : ℕ) : ℂ :=
      (((k * n : ℕ) : ℝ) : ℂ) ^ z / z * ((q : ℝ) : ℂ) ^ (-z) * ((d : ℝ) : ℂ) ^ (-z)
    have hSk_eq (k : ℕ) : Sk k = riemannZeta z + (((k : ℝ) * u : ℝ) : ℂ) ^ (1 - z) / (1 - z) +
        Ek k := by dsimp [Ek]; ring
    have hterm_id :
        (μ d : ℂ) * (Ak 4 * Sk 4 - (P : ℂ) ^ z / z * ((⌊(4 : ℝ) * u⌋₊ : ℝ) : ℂ)) -
          2 * ((μ d : ℂ) * (Ak 3 * Sk 3 - (P : ℂ) ^ z / z * ((⌊(3 : ℝ) * u⌋₊ : ℝ) : ℂ))) +
          (μ d : ℂ) * (Ak 2 * Sk 2 - (P : ℂ) ^ z / z * ((⌊(2 : ℝ) * u⌋₊ : ℝ) : ℂ)) -
          (μ d : ℂ) * (-(midpointMultiplier z / z) * ((q : ℝ) : ℂ) ^ (-z) *
            ((d : ℝ) : ℂ) ^ (-z) * riemannZeta z * ((n : ℝ) : ℂ) ^ z) =
          (μ d : ℂ) * ((Ak 4 * Ek 4 - 2 * (Ak 3 * Ek 3) + Ak 2 * Ek 2) +
            (P : ℂ) ^ z / z *
              (((Int.fract ((4 : ℝ) * u) : ℝ) : ℂ) -
                2 * ((Int.fract ((3 : ℝ) * u) : ℝ) : ℂ) +
                ((Int.fract ((2 : ℝ) * u) : ℝ) : ℂ))) := by
      rw [hSk_eq 4, hSk_eq 3, hSk_eq 2]
      have hl4 := hlin_id 4 (by decide)
      have hl3 := hlin_id 3 (by decide)
      have hl2 := hlin_id 2 (by decide)
      have hf4 := hfl_fract 4 (by decide)
      have hf3 := hfl_fract 3 (by decide)
      have hf2 := hfl_fract 2 (by decide)
      have hz_part : Ak 4 * riemannZeta z - 2 * (Ak 3 * riemannZeta z) +
          Ak 2 * riemannZeta z =
          -(midpointMultiplier z / z) * ((q : ℝ) : ℂ) ^ (-z) * ((d : ℝ) : ℂ) ^ (-z) *
            riemannZeta z * ((n : ℝ) : ℂ) ^ z := by
        change ((((4 * n : ℕ) : ℝ) : ℂ) ^ z / z * ((q : ℝ) : ℂ) ^ (-z) * ((d : ℝ) : ℂ) ^ (-z)) *
            riemannZeta z -
          2 * (((((3 * n : ℕ) : ℝ) : ℂ) ^ z / z * ((q : ℝ) : ℂ) ^ (-z) * ((d : ℝ) : ℂ) ^ (-z)) *
            riemannZeta z) +
          ((((2 * n : ℕ) : ℝ) : ℂ) ^ z / z * ((q : ℝ) : ℂ) ^ (-z) * ((d : ℝ) : ℂ) ^ (-z)) *
            riemannZeta z = _
        rw [hkn_pow 4 (by decide), hkn_pow 3 (by decide), hkn_pow 2 (by decide), midpointMultiplier]
        simp only [Nat.cast_ofNat, Complex.ofReal_ofNat]
        ring
      have hP_cast : ((P : ℝ) : ℂ) = (P : ℂ) := Complex.ofReal_natCast P
      rw [hP_cast] at hl4 hl3 hl2
      simp only [Nat.cast_ofNat] at hl4 hl3 hl2 hf4 hf3 hf2
      change (μ d : ℂ) * (Ak 4 * _ - (P : ℂ) ^ z / z * _) -
          2 * ((μ d : ℂ) * (Ak 3 * _ - (P : ℂ) ^ z / z * _)) +
          (μ d : ℂ) * (Ak 2 * _ - (P : ℂ) ^ z / z * _) - _ = _
      have hl4' : Ak 4 * ((((4 : ℝ) * u : ℝ) : ℂ) ^ (1 - z) / (1 - z)) =
          4 * ((u : ℂ) * (P : ℂ) ^ z / (z * (1 - z))) := hl4
      have hl3' : Ak 3 * ((((3 : ℝ) * u : ℝ) : ℂ) ^ (1 - z) / (1 - z)) =
          3 * ((u : ℂ) * (P : ℂ) ^ z / (z * (1 - z))) := hl3
      have hl2' : Ak 2 * ((((2 : ℝ) * u : ℝ) : ℂ) ^ (1 - z) / (1 - z)) =
          2 * ((u : ℂ) * (P : ℂ) ^ z / (z * (1 - z))) := hl2
      linear_combination (μ d : ℂ) * hz_part +
        (μ d : ℂ) * hl4' - 2 * (μ d : ℂ) * hl3' + (μ d : ℂ) * hl2' -
        (μ d : ℂ) * ((P : ℂ) ^ z / z) * hf4 +
        2 * (μ d : ℂ) * ((P : ℂ) ^ z / z) * hf3 -
        (μ d : ℂ) * ((P : ℂ) ^ z / z) * hf2
    simp only [Nat.cast_ofNat]
    change ‖(μ d : ℂ) * (Ak 4 * Sk 4 - (P : ℂ) ^ z / z * ((⌊(4 : ℝ) * u⌋₊ : ℝ) : ℂ)) -
        2 * ((μ d : ℂ) * (Ak 3 * Sk 3 - (P : ℂ) ^ z / z * ((⌊(3 : ℝ) * u⌋₊ : ℝ) : ℂ))) +
        (μ d : ℂ) * (Ak 2 * Sk 2 - (P : ℂ) ^ z / z * ((⌊(2 : ℝ) * u⌋₊ : ℝ) : ℂ)) -
        (μ d : ℂ) * (-(midpointMultiplier z / z) * ((q : ℝ) : ℂ) ^ (-z) *
          ((d : ℝ) : ℂ) ^ (-z) * riemannZeta z * ((n : ℝ) : ℂ) ^ z)‖ ≤ _
    rw [hterm_id, norm_mul, hmu_norm,
      mul_comm (((12 * Kz + 4) / ‖z‖) * (P : ℝ) ^ z.re) |(μ d : ℝ)|]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    -- Bound `‖Ak k * Ek k‖ ≤ (Kz / ‖z‖) * P^{z.re}` for `k ∈ {2, 3, 4}`!
    have hAkEk (k : ℕ) (hk : 1 ≤ k) :
        ‖Ak k * Ek k‖ ≤ (Kz / ‖z‖) * (P : ℝ) ^ z.re := by
      have hkR : (0 : ℝ) < k := by exact_mod_cast hk
      have hku : 0 < (k : ℝ) * u := mul_pos hkR hu
      have hknR : (0 : ℝ) < (k * n : ℕ) := by exact_mod_cast Nat.mul_pos hk hn
      have hEk_b : ‖Ek k‖ ≤ Kz * ((k : ℝ) * u) ^ (-z.re) :=
        zeta_partial_sum_all_pos hz0 hz1 hku
      have hAk_n : ‖Ak k‖ = ((k * n : ℕ) : ℝ) ^ z.re / ‖z‖ *
          (q : ℝ) ^ (-z.re) * (d : ℝ) ^ (-z.re) := by
        rw [show Ak k = (((k * n : ℕ) : ℝ) : ℂ) ^ z / z * ((q : ℝ) : ℂ) ^ (-z) *
            ((d : ℝ) : ℂ) ^ (-z) from rfl,
          norm_mul, norm_mul, norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hknR,
          Complex.norm_cpow_eq_rpow_re_of_pos hqR, Complex.norm_cpow_eq_rpow_re_of_pos hdR,
          Complex.neg_re]
      have hcancel_pow : ((k * n : ℕ) : ℝ) ^ z.re * (q : ℝ) ^ (-z.re) * (d : ℝ) ^ (-z.re) *
          ((k : ℝ) * u) ^ (-z.re) = (P : ℝ) ^ z.re := by
        have hku_eq : (k : ℝ) * u = ((k * n : ℕ) : ℝ) / ((P : ℝ) * ((q : ℝ) * (d : ℝ))) := by
          dsimp [u]; push_cast; ring
        rw [hku_eq, div_eq_mul_inv,
          Real.mul_rpow hknR.le (by positivity),
          Real.inv_rpow (by positivity : (0 : ℝ) ≤ (P : ℝ) * ((q : ℝ) * (d : ℝ))),
          ← Real.rpow_neg (by positivity : (0 : ℝ) ≤ (P : ℝ) * ((q : ℝ) * (d : ℝ))),
          neg_neg, Real.mul_rpow hPR.le (by positivity), Real.mul_rpow hqR.le hdR.le]
        have h1 : ((k * n : ℕ) : ℝ) ^ z.re * ((k * n : ℕ) : ℝ) ^ (-z.re) = 1 := by
          rw [← Real.rpow_add hknR, add_neg_cancel, Real.rpow_zero]
        have h2 : (q : ℝ) ^ (-z.re) * (q : ℝ) ^ z.re = 1 := by
          rw [← Real.rpow_add hqR, neg_add_cancel, Real.rpow_zero]
        have h3 : (d : ℝ) ^ (-z.re) * (d : ℝ) ^ z.re = 1 := by
          rw [← Real.rpow_add hdR, neg_add_cancel, Real.rpow_zero]
        linear_combination (P : ℝ) ^ z.re *
          (((k * n : ℕ) : ℝ) ^ z.re * ((k * n : ℕ) : ℝ) ^ (-z.re)) *
          ((q : ℝ) ^ (-z.re) * (q : ℝ) ^ z.re) * h3 +
          (P : ℝ) ^ z.re * (((k * n : ℕ) : ℝ) ^ z.re * ((k * n : ℕ) : ℝ) ^ (-z.re)) * h2 +
          (P : ℝ) ^ z.re * h1
      rw [norm_mul, hAk_n]
      calc (((k * n : ℕ) : ℝ) ^ z.re / ‖z‖ * (q : ℝ) ^ (-z.re) * (d : ℝ) ^ (-z.re)) * ‖Ek k‖
          ≤ (((k * n : ℕ) : ℝ) ^ z.re / ‖z‖ * (q : ℝ) ^ (-z.re) * (d : ℝ) ^ (-z.re)) *
              (Kz * ((k : ℝ) * u) ^ (-z.re)) :=
            mul_le_mul_of_nonneg_left hEk_b (by positivity)
        _ = (Kz / ‖z‖) * (((k * n : ℕ) : ℝ) ^ z.re * (q : ℝ) ^ (-z.re) * (d : ℝ) ^ (-z.re) *
              ((k : ℝ) * u) ^ (-z.re)) := by ring
        _ = (Kz / ‖z‖) * (P : ℝ) ^ z.re := by rw [hcancel_pow]
    have hfr_b : ‖(P : ℂ) ^ z / z *
        (((Int.fract ((4 : ℝ) * u) : ℝ) : ℂ) -
          2 * ((Int.fract ((3 : ℝ) * u) : ℝ) : ℂ) +
          ((Int.fract ((2 : ℝ) * u) : ℝ) : ℂ))‖ ≤ (4 / ‖z‖) * (P : ℝ) ^ z.re := by
      have hfn (x : ℝ) : ‖((Int.fract x : ℝ) : ℂ)‖ ≤ 1 := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Int.fract_nonneg x)]
        exact (Int.fract_lt_one x).le
      have hcomb_f : ‖(((Int.fract ((4 : ℝ) * u) : ℝ) : ℂ) -
          2 * ((Int.fract ((3 : ℝ) * u) : ℝ) : ℂ) +
          ((Int.fract ((2 : ℝ) * u) : ℝ) : ℂ))‖ ≤ 4 := by
        refine (norm_add_le _ _).trans ?_
        refine (add_le_add (norm_sub_le _ _) (hfn _)).trans ?_
        rw [norm_mul, Complex.norm_ofNat]
        linarith only [hfn ((4 : ℝ) * u), hfn ((3 : ℝ) * u)]
      rw [norm_mul, norm_div,
        show (P : ℂ) = ((P : ℝ) : ℂ) by push_cast; rfl,
        Complex.norm_cpow_eq_rpow_re_of_pos hPR]
      calc (P : ℝ) ^ z.re / ‖z‖ * _ ≤ (P : ℝ) ^ z.re / ‖z‖ * 4 :=
            mul_le_mul_of_nonneg_left hcomb_f (by positivity)
        _ = (4 / ‖z‖) * (P : ℝ) ^ z.re := by ring
    have hb4 := hAkEk 4 (by decide)
    have hb3 := hAkEk 3 (by decide)
    have hb2 := hAkEk 2 (by decide)
    have hb_sum : ‖Ak 4 * Ek 4 - 2 * (Ak 3 * Ek 3) + Ak 2 * Ek 2‖ ≤
        (4 * Kz / ‖z‖) * (P : ℝ) ^ z.re := by
      refine (norm_add_le _ _).trans ?_
      refine (add_le_add (norm_sub_le _ _) hb2).trans ?_
      rw [norm_mul (2 : ℂ) (Ak 3 * Ek 3), Complex.norm_ofNat,
        show (4 * Kz / ‖z‖) * (P : ℝ) ^ z.re = 4 * ((Kz / ‖z‖) * (P : ℝ) ^ z.re) by ring]
      linarith only [hb4, hb3]
    refine (norm_add_le _ _).trans ?_
    calc ‖Ak 4 * Ek 4 - 2 * (Ak 3 * Ek 3) + Ak 2 * Ek 2‖ + _
        ≤ (4 * Kz / ‖z‖) * (P : ℝ) ^ z.re + (4 / ‖z‖) * (P : ℝ) ^ z.re :=
          add_le_add hb_sum hfr_b
      _ ≤ ((12 * Kz + 4) / ‖z‖) * (P : ℝ) ^ z.re := by
          have hKz_nn : 0 ≤ (8 * Kz / ‖z‖) * (P : ℝ) ^ z.re := by
            dsimp [Kz]; positivity
          rw [show ((12 * Kz + 4) / ‖z‖) * (P : ℝ) ^ z.re =
            (4 * Kz / ‖z‖) * (P : ℝ) ^ z.re + (4 / ‖z‖) * (P : ℝ) ^ z.re +
              (8 * Kz / ‖z‖) * (P : ℝ) ^ z.re by ring]
          linarith only [hKz_nn]
  -- Assemble `hslice_u`, `hround_k`, `hgv1`, and `hmoeb_w`
  have hsum_gv : (∑ u ∈ (Icc 1 (4 * n / q)).filter (n.Coprime ·), gv (q * u)) =
      (∑ u ∈ (Icc 1 (4 * n / q)).filter (n.Coprime ·),
          (gz (max P (4 * n / (q * u)) : ℕ) - gz (P : ℝ))) -
        2 * (∑ u ∈ (Icc 1 (4 * n / q)).filter (n.Coprime ·),
          (gz (max P (3 * n / (q * u)) : ℕ) - gz (P : ℝ))) +
        (∑ u ∈ (Icc 1 (4 * n / q)).filter (n.Coprime ·),
          (gz (max P (2 * n / (q * u)) : ℕ) - gz (P : ℝ))) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun u _ => by dsimp [gv]; ring
  have hround_all :
      ‖(∑ u ∈ (Icc 1 (4 * n / q)).filter (n.Coprime ·), gv (q * u)) -
          (Wk 4 - 2 * Wk 3 + Wk 2)‖ ≤
        12 * (n : ℝ) * (P : ℝ) ^ (z.re - 2) * squarefreeDivisorMass n := by
    rw [hsum_gv]
    have hr4 := hround_k 4 (by decide) (by decide)
    have hr3 := hround_k 3 (by decide) (by decide)
    have hr2 := hround_k 2 (by decide) (by decide)
    simp only [Nat.cast_ofNat] at hr4 hr3 hr2
    set S4 := ∑ u ∈ (Icc 1 (4 * n / q)).filter (n.Coprime ·),
      (gz (max P (4 * n / (q * u)) : ℕ) - gz (P : ℝ))
    set S3 := ∑ u ∈ (Icc 1 (4 * n / q)).filter (n.Coprime ·),
      (gz (max P (3 * n / (q * u)) : ℕ) - gz (P : ℝ))
    set S2 := ∑ u ∈ (Icc 1 (4 * n / q)).filter (n.Coprime ·),
      (gz (max P (2 * n / (q * u)) : ℕ) - gz (P : ℝ))
    have hsplit : (S4 - 2 * S3 + S2) - (Wk 4 - 2 * Wk 3 + Wk 2) =
        (S4 - Wk 4) - 2 * (S3 - Wk 3) + (S2 - Wk 2) := by ring
    rw [hsplit]
    have h12 : ‖(S4 - Wk 4) - 2 * (S3 - Wk 3) + (S2 - Wk 2)‖ ≤
        12 * (n : ℝ) * (P : ℝ) ^ (z.re - 2) := by
      refine (norm_add_le _ _).trans ?_
      refine (add_le_add (norm_sub_le _ _) hr2).trans ?_
      rw [norm_mul, Complex.norm_ofNat]
      linarith only [hr4, hr3]
    exact h12.trans (le_mul_of_one_le_right (by positivity) (one_le_squarefreeDivisorMass hn))
  have hmain_eq :
      -((if q = 1 then gv 1 else 0)) +
        (-(midpointMultiplier z / z) *
          (((q : ℝ) : ℂ) ^ (-z) * riemannZeta z * coprimeEulerFactor n z) *
          ((n : ℝ) : ℂ) ^ z) =
        (midpointMultiplier z / z) *
          ((if q = 1 then (1 : ℂ) else 0) -
            ((q : ℝ) : ℂ) ^ (-z) * riemannZeta z * coprimeEulerFactor n z) *
          ((n : ℝ) : ℂ) ^ z := by
    by_cases hq1 : q = 1
    · rw [if_pos hq1, if_pos hq1, hgv1]; ring
    · rw [if_neg hq1, if_neg hq1]; ring
  have htot_id :
      (∑ u ∈ (Icc 1 (4 * n / q)).filter (n.Coprime ·), gv (q * u)) -
          (if q = 1 then gv 1 else 0) -
          (midpointMultiplier z / z) *
            ((if q = 1 then (1 : ℂ) else 0) -
              ((q : ℝ) : ℂ) ^ (-z) * riemannZeta z * coprimeEulerFactor n z) *
            ((n : ℝ) : ℂ) ^ z =
        ((∑ u ∈ (Icc 1 (4 * n / q)).filter (n.Coprime ·), gv (q * u)) -
          (Wk 4 - 2 * Wk 3 + Wk 2)) +
        ((Wk 4 - 2 * Wk 3 + Wk 2) -
          (-(midpointMultiplier z / z) *
            (((q : ℝ) : ℂ) ^ (-z) * riemannZeta z * coprimeEulerFactor n z) *
            ((n : ℝ) : ℂ) ^ z)) := by
    linear_combination hmain_eq
  change ‖clippedCofactorComplexSliceOp n P q gz - _‖ ≤ _
  rw [hslice_u, htot_id]
  refine (norm_add_le _ _).trans ?_
  calc _ ≤ 12 * (n : ℝ) * (P : ℝ) ^ (z.re - 2) * squarefreeDivisorMass n +
            ((12 * Kz + 4) / ‖z‖) * (P : ℝ) ^ z.re * squarefreeDivisorMass n :=
          add_le_add hround_all hmoeb_w
    _ ≤ waveTransmissionRate z *
          ((P : ℝ) ^ z.re + (n : ℝ) * (P : ℝ) ^ (z.re - 2)) * squarefreeDivisorMass n := by
          unfold waveTransmissionRate
          dsimp [Kz]
          have hnn1 : 0 ≤ ((12 * Kz + 4) / ‖z‖) * ((n : ℝ) * (P : ℝ) ^ (z.re - 2)) *
              squarefreeDivisorMass n := by
            have : 0 ≤ Kz := by dsimp [Kz]; positivity
            have : 0 ≤ squarefreeDivisorMass n := sum_nonneg fun _ _ => abs_nonneg _
            positivity
          have hnn2 : 0 ≤ 12 * (P : ℝ) ^ z.re * squarefreeDivisorMass n := by
            have : 0 ≤ squarefreeDivisorMass n := sum_nonneg fun _ _ => abs_nonneg _
            positivity
          dsimp [Kz] at hnn1
          linarith only [hnn1, hnn2]

/-- Real oscillatory prime-error wave `-2 m Re(x^z / z)` predicted by a quartet `(z, m)`. -/
def quartetWaveModel (z : ℂ) (m : ℝ) (x : ℝ) : ℝ :=
  -(2 * m * ((x : ℂ) ^ z / z).re)

/-- Exact midpoint evaluation of `quartetWaveModel z m`. -/
theorem midpointSecondDiff_quartetWaveModel (n : ℕ) (z : ℂ) (m : ℝ) :
    midpointSecondDiff n (quartetWaveModel z m) =
      -(2 * m * ((midpointMultiplier z / z) * ((n : ℝ) : ℂ) ^ z).re) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · by_cases hz : z = 0
    · subst hz; simp [midpointSecondDiff, quartetWaveModel]
    · simp [midpointSecondDiff, quartetWaveModel, Complex.zero_cpow hz]
  · have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hc (k : ℕ) (hk : 0 < k) : (((k * n : ℕ) : ℝ) : ℂ) ^ z =
        ((k : ℝ) : ℂ) ^ z * ((n : ℝ) : ℂ) ^ z := by
      have hkR : (0 : ℝ) < k := by exact_mod_cast hk
      simpa only [Nat.cast_mul] using cpow_pos_mul hkR hnR z
    unfold midpointSecondDiff quartetWaveModel
    have hid : ((2 : ℝ) : ℂ) * ((((3 * n : ℕ) : ℝ) : ℂ) ^ z / z) -
        ((((2 * n : ℕ) : ℝ) : ℂ) ^ z / z) -
        ((((4 * n : ℕ) : ℝ) : ℂ) ^ z / z) =
        (midpointMultiplier z / z) * ((n : ℝ) : ℂ) ^ z := by
      rw [hc 3 (by decide), hc 2 (by decide), hc 4 (by decide), midpointMultiplier]
      simp only [Nat.cast_ofNat, Complex.ofReal_ofNat]
      ring
    have hre := congrArg Complex.re hid
    simp only [Complex.sub_re, Complex.re_ofReal_mul] at hre
    linarith only [congrArg (fun u => -(2 * m * u)) hre]

/-- **Universal real wave transmission across `q`-divisible cofactor slices.** -/
theorem clippedCofactorSliceOp_wave {n P q : ℕ} (hn : 1 ≤ n) (hP1 : 1 ≤ P) (hP2 : P ≤ 2 * n)
    (hq : 1 ≤ q) (hcop : n.Coprime q) {z : ℂ} (hz0 : 0 < z.re) (hz1 : z.re < 1) (m : ℝ) :
    |clippedCofactorSliceOp n P q (quartetWaveModel z m) -
        (-(2 * m * ((midpointMultiplier z / z) *
          ((if q = 1 then (1 : ℂ) else 0) -
            ((q : ℝ) : ℂ) ^ (-z) * riemannZeta z * coprimeEulerFactor n z) *
          ((n : ℝ) : ℂ) ^ z).re))| ≤
      2 * |m| * waveTransmissionRate z *
        ((P : ℝ) ^ z.re + (n : ℝ) * (P : ℝ) ^ (z.re - 2)) * squarefreeDivisorMass n := by
  have heq : clippedCofactorSliceOp n P q (quartetWaveModel z m) =
      -(2 * m * (clippedCofactorComplexSliceOp n P q (fun x => (x : ℂ) ^ z / z)).re) := by
    unfold clippedCofactorSliceOp clippedCofactorComplexSliceOp quartetWaveModel
    rw [Complex.re_sum, Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun v _ => ?_
    simp only [Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.re_ofNat,
      Complex.im_ofNat, zero_mul, sub_zero]
    ring
  rw [heq, show -(2 * m * (clippedCofactorComplexSliceOp n P q (fun x => (x : ℂ) ^ z / z)).re) -
      -(2 * m * _) =
      -(2 * m * (clippedCofactorComplexSliceOp n P q (fun x => (x : ℂ) ^ z / z) -
        (midpointMultiplier z / z) *
          ((if q = 1 then (1 : ℂ) else 0) -
            ((q : ℝ) : ℂ) ^ (-z) * riemannZeta z * coprimeEulerFactor n z) *
          ((n : ℝ) : ℂ) ^ z).re) by rw [Complex.sub_re]; ring,
    abs_neg, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hb := (Complex.abs_re_le_norm _).trans
    (clippedCofactorComplexSliceOp_cpow hn hP1 hP2 hq hcop hz0 hz1)
  exact (mul_le_mul_of_nonneg_left hb (mul_nonneg zero_le_two (abs_nonneg m))).trans_eq (by ring)

/-! ### 5. Exact `ζ(z) = 0` selectivity and actual-prime cofactor-slice vanishing -/

private theorem floor_two_sqrt_bounds {n : ℕ} (hn : 1 ≤ n) :
    1 ≤ ⌊2 * Real.sqrt n⌋₊ ∧ ⌊2 * Real.sqrt n⌋₊ ≤ 2 * n ∧
      Real.sqrt n ≤ (⌊2 * Real.sqrt n⌋₊ : ℝ) ∧ (⌊2 * Real.sqrt n⌋₊ : ℝ) ≤ 2 * Real.sqrt n := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hsq1 : 1 ≤ Real.sqrt n := Real.one_le_sqrt.mpr hnR
  have hfl_le : (⌊2 * Real.sqrt n⌋₊ : ℝ) ≤ 2 * Real.sqrt n := Nat.floor_le (by positivity)
  have hlt_fl : 2 * Real.sqrt n < (⌊2 * Real.sqrt n⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
  have hsq_le_fl : Real.sqrt n ≤ (⌊2 * Real.sqrt n⌋₊ : ℝ) := by linarith only [hsq1, hlt_fl]
  have h1_fl : 1 ≤ ⌊2 * Real.sqrt n⌋₊ :=
    Nat.le_floor (by exact_mod_cast (show (1 : ℝ) ≤ 2 * Real.sqrt n by linarith only [hsq1]))
  have hfl_2n : ⌊2 * Real.sqrt n⌋₊ ≤ 2 * n := by
    have hsq_n : Real.sqrt n ≤ n := by
      nlinarith only [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ n), hsq1]
    have hR : (⌊2 * Real.sqrt n⌋₊ : ℝ) ≤ 2 * n := by linarith only [hfl_le, hsq_n]
    exact_mod_cast hR
  exact ⟨h1_fl, hfl_2n, hsq_le_fl, hfl_le⟩

private theorem wave_cut_rpow_le {n : ℕ} (hn : 1 ≤ n) {β : ℝ} (h0 : 0 < β) (h1 : β < 1) :
    (⌊2 * Real.sqrt n⌋₊ : ℝ) ^ β + (n : ℝ) * (⌊2 * Real.sqrt n⌋₊ : ℝ) ^ (β - 2) ≤
      3 * (n : ℝ) ^ (β / 2) := by
  set P := ⌊2 * Real.sqrt n⌋₊
  obtain ⟨_, _, hlo, hhi⟩ := floor_two_sqrt_bounds hn
  have hloP : Real.sqrt n ≤ (P : ℝ) := hlo
  have hhiP : (P : ℝ) ≤ 2 * Real.sqrt n := hhi
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hsq0 : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn0
  have h1_term : (P : ℝ) ^ β ≤ 2 * (n : ℝ) ^ (β / 2) := by
    have ha := Real.rpow_le_rpow (by positivity) hhiP h0.le
    rw [Real.mul_rpow (by norm_num) hsq0.le, Real.sqrt_eq_rpow, ← Real.rpow_mul hn0.le,
      show (1 / 2 : ℝ) * β = β / 2 by ring] at ha
    have h2 : (2 : ℝ) ^ β ≤ 2 := by
      simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) h1.le
    exact ha.trans (mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg hn0.le _))
  have h2_term : (n : ℝ) * (P : ℝ) ^ (β - 2) ≤ (n : ℝ) ^ (β / 2) := by
    have hb := Real.rpow_le_rpow_of_nonpos hsq0 hloP (by linarith : β - 2 ≤ 0)
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hn0.le] at hb
    calc (n : ℝ) * (P : ℝ) ^ (β - 2)
        ≤ (n : ℝ) ^ (1 : ℝ) * (n : ℝ) ^ ((1 / 2 : ℝ) * (β - 2)) := by
            rw [Real.rpow_one]; exact mul_le_mul_of_nonneg_left hb hn0.le
      _ = (n : ℝ) ^ (β / 2) := by
            rw [← Real.rpow_add hn0]; congr 1; ring
  linarith only [h1_term, h2_term]

/-- Explicit reflected-composite defect formula on `x + quartetWaveModel z m x` (`0 < Re z < 1`,
`n ≥ 1`): isolates the exact `ζ(z)`-proportional oscillatory obstruction
`2 m Re((M(z)/z) ζ(z) E_n(z) n^z)` up to `(68 + 6 |m| waveTransmissionRate z) √n squarefreeDivisorMass n`. -/
theorem clippedCofactorOp_linear_add_wave_defect {n : ℕ} (hn : 1 ≤ n) {z : ℂ} (hz0 : 0 < z.re)
    (h1 : z.re < 1) (m : ℝ) :
    |(clippedCofactorOp n ⌊2 * Real.sqrt n⌋₊ (fun x => x + quartetWaveModel z m x) -
        reflectedDensity * (n.totient : ℝ) -
        midpointSecondDiff n (fun x => x + quartetWaveModel z m x)) -
      2 * m * ((midpointMultiplier z / z) * riemannZeta z * coprimeEulerFactor n z *
        ((n : ℝ) : ℂ) ^ z).re| ≤
      (68 + 6 * |m| * waveTransmissionRate z) * Real.sqrt n * squarefreeDivisorMass n := by
  set P := ⌊2 * Real.sqrt n⌋₊
  obtain ⟨hP1, hP2, hlo, hhi⟩ := floor_two_sqrt_bounds hn
  have hnR1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hsq1 : 1 ≤ Real.sqrt n := Real.one_le_sqrt.mpr hnR1
  have hmass_nn : 0 ≤ squarefreeDivisorMass n := sum_nonneg fun _ _ => abs_nonneg _
  have hlin := clippedCofactorSliceOp_linear hn hP1 hP2 le_rfl (Nat.coprime_one_right n)
  rw [Nat.cast_one, div_one, one_mul] at hlin
  have hlin_cost : 20 * ((P : ℝ) + 1) + 12 * (n : ℝ) / ((P : ℝ) + 1) ≤ 68 * Real.sqrt n := by
    have hlt_fl : 2 * Real.sqrt n < (P : ℝ) + 1 := Nat.lt_floor_add_one _
    have hdiv : 12 * (n : ℝ) / ((P : ℝ) + 1) ≤ 6 * Real.sqrt n := by
      rw [div_le_iff₀ (by positivity)]
      have hsq := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ n)
      nlinarith only [hlt_fl, hsq, Real.sqrt_nonneg n]
    linarith only [hhi, hsq1, hdiv]
  have hlin' : |clippedCofactorOp n P id - reflectedDensity * (n.totient : ℝ)| ≤
      68 * Real.sqrt n * squarefreeDivisorMass n :=
    hlin.trans ((mul_le_mul_of_nonneg_right hlin_cost hmass_nn).trans_eq (by ring))
  have hwave := clippedCofactorSliceOp_wave hn hP1 hP2 le_rfl (Nat.coprime_one_right n) hz0 h1 m
  rw [if_pos rfl, Nat.cast_one, Complex.ofReal_one, Complex.one_cpow, one_mul] at hwave
  have hw_pow : (P : ℝ) ^ z.re + (n : ℝ) * (P : ℝ) ^ (z.re - 2) ≤ 3 * Real.sqrt n := by
    refine (wave_cut_rpow_le hn hz0 h1).trans ?_
    rw [Real.sqrt_eq_rpow]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hnR1 (by linarith)) (by norm_num)
  have hwave' : |clippedCofactorOp n P (quartetWaveModel z m) -
      (-(2 * m * ((midpointMultiplier z / z) *
        (1 - riemannZeta z * coprimeEulerFactor n z) * ((n : ℝ) : ℂ) ^ z).re))| ≤
      (6 * |m| * waveTransmissionRate z) * Real.sqrt n * squarefreeDivisorMass n := by
    refine hwave.trans ?_
    have h1_w := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hw_pow
        (mul_nonneg (mul_nonneg zero_le_two (abs_nonneg m)) (waveTransmissionRate_nonneg hz0)))
      hmass_nn
    exact h1_w.trans_eq (by ring)
  have hmid_split : midpointSecondDiff n (fun x => x + quartetWaveModel z m x) =
      midpointSecondDiff n (quartetWaveModel z m) := by
    unfold midpointSecondDiff; push_cast; ring
  have hmid_w := midpointSecondDiff_quartetWaveModel n z m
  have hre_split : ((midpointMultiplier z / z) *
      (1 - riemannZeta z * coprimeEulerFactor n z) * ((n : ℝ) : ℂ) ^ z).re =
      ((midpointMultiplier z / z) * ((n : ℝ) : ℂ) ^ z).re -
        ((midpointMultiplier z / z) * riemannZeta z * coprimeEulerFactor n z *
          ((n : ℝ) : ℂ) ^ z).re := by
    rw [← Complex.sub_re]; congr 1; ring
  have hclip_add : clippedCofactorOp n P (fun x => x + quartetWaveModel z m x) =
      clippedCofactorOp n P id + clippedCofactorOp n P (quartetWaveModel z m) :=
    clippedCofactorSliceOp_add n P 1 id (quartetWaveModel z m)
  rw [hclip_add, hmid_split, hmid_w]
  have hid : (clippedCofactorOp n P id + clippedCofactorOp n P (quartetWaveModel z m) -
        reflectedDensity * (n.totient : ℝ) -
        -(2 * m * ((midpointMultiplier z / z) * ((n : ℝ) : ℂ) ^ z).re)) -
      2 * m * ((midpointMultiplier z / z) * riemannZeta z * coprimeEulerFactor n z *
        ((n : ℝ) : ℂ) ^ z).re =
      (clippedCofactorOp n P id - reflectedDensity * (n.totient : ℝ)) +
        (clippedCofactorOp n P (quartetWaveModel z m) -
          -(2 * m * ((midpointMultiplier z / z) *
            (1 - riemannZeta z * coprimeEulerFactor n z) * ((n : ℝ) : ℂ) ^ z).re)) := by
    rw [hre_split]; ring
  rw [hid]
  exact (abs_add_le _ _).trans ((add_le_add hlin' hwave').trans_eq (by ring))

/-- **Exact `ζ(z) = 0` selectivity of reflected-composite wave transmission.**
For `1/2 < Re z < 1`, `Im z ≠ 0`, and `m ≠ 0`, inserting `x + quartetWaveModel z m x` into
`clippedCofactorOp n ⌊2√n⌋₊` reproduces `reflectedDensity * φ(n) + midpointSecondDiff` within
`O(√n squarefreeDivisorMass n)` across `n ≥ 2` **if and only if** `riemannZeta z = 0`. -/
theorem reflectedComposite_wave_compatible_iff_zeta_zero {z : ℂ} (hhalf : 1 / 2 < z.re)
    (h1 : z.re < 1) (him : z.im ≠ 0) {m : ℝ} (hm : m ≠ 0) :
    (∃ C : ℝ, ∀ n : ℕ, 2 ≤ n →
      |clippedCofactorOp n ⌊2 * Real.sqrt n⌋₊ (fun x => x + quartetWaveModel z m x) -
          reflectedDensity * (n.totient : ℝ) -
          midpointSecondDiff n (fun x => x + quartetWaveModel z m x)| ≤
        C * Real.sqrt n * squarefreeDivisorMass n) ↔
      riemannZeta z = 0 := by
  have hz0 : 0 < z.re := by linarith
  have hzne0 : z ≠ 0 := fun he => by rw [he, Complex.zero_re] at hz0; exact lt_irrefl 0 hz0
  constructor
  · rintro ⟨C, hC⟩
    by_contra hζ_ne
    have hA_ne : (midpointMultiplier z / z) * riemannZeta z ≠ 0 :=
      mul_ne_zero (div_ne_zero (midpointMultiplier_ne_zero hz0 h1) hzne0) hζ_ne
    obtain ⟨p, c, hp, _, hc_pos, hpeaks⟩ :=
      exists_prime_power_re_lower_bound (le_refl 1) hz0 him hA_ne
    set K_tot : ℝ := 2 * (|C| + 68 + 6 * |m| * waveTransmissionRate z)
    have hgap : 0 < z.re - 1 / 2 := sub_pos.mpr hhalf
    have htend : Tendsto (fun k : ℕ => ((p ^ k : ℕ) : ℝ) ^ (z.re - 1 / 2)) atTop atTop := by
      refine tendsto_atTop_mono (fun k => Real.rpow_le_rpow (Nat.cast_nonneg k)
        (by exact_mod_cast (Nat.lt_pow_self hp.one_lt).le) hgap.le) ?_
      exact (_root_.tendsto_rpow_atTop hgap).comp tendsto_natCast_atTop_atTop
    obtain ⟨k, hk1, hbig⟩ :=
      ((eventually_ge_atTop 1).and
        (htend.eventually_gt_atTop ((K_tot + 1) / (2 * |m| * c)))).exists
    obtain ⟨n, hn_mem, _, hmass2, hpk⟩ := hpeaks k hk1
    have hn_ge_pk : p ^ k ≤ n := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hn_mem
      rcases hn_mem with rfl | rfl
      · exact le_rfl
      · exact Nat.pow_le_pow_right hp.pos (Nat.le_succ k)
    have hn2 : 2 ≤ n := by
      calc 2 ≤ p ^ 1 := by simpa using hp.two_le
        _ ≤ p ^ k := Nat.pow_le_pow_right hp.pos hk1
        _ ≤ n := hn_ge_pk
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hb1 := (hC n hn2).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_abs_self C) (Real.sqrt_nonneg n))
        (by rw [hmass2]; norm_num))
    have hb2 := clippedCofactorOp_linear_add_wave_defect (n := n) (by omega) hz0 h1 m
    rw [hmass2] at hb1 hb2
    have hupper : |2 * m * ((midpointMultiplier z / z) * riemannZeta z * coprimeEulerFactor n z *
        ((n : ℝ) : ℂ) ^ z).re| ≤ K_tot * Real.sqrt n := by
      set D := clippedCofactorOp n ⌊2 * Real.sqrt n⌋₊ (fun x => x + quartetWaveModel z m x) -
        reflectedDensity * (n.totient : ℝ) -
        midpointSecondDiff n (fun x => x + quartetWaveModel z m x)
      have htri := abs_sub D
        (D - 2 * m * ((midpointMultiplier z / z) * riemannZeta z * coprimeEulerFactor n z *
          ((n : ℝ) : ℂ) ^ z).re)
      rw [sub_sub_cancel] at htri
      rw [show K_tot = 2 * (|C| + 68 + 6 * |m| * waveTransmissionRate z) from rfl]
      linarith only [htri, hb1, hb2]
    have hlower : 2 * |m| * c * (n : ℝ) ^ z.re ≤
        |2 * m * ((midpointMultiplier z / z) * riemannZeta z * coprimeEulerFactor n z *
          ((n : ℝ) : ℂ) ^ z).re| := by
      rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      calc 2 * |m| * c * (n : ℝ) ^ z.re
          = 2 * |m| * (c * (n : ℝ) ^ z.re) := by ring
        _ ≤ 2 * |m| * |((midpointMultiplier z / z) * riemannZeta z * coprimeEulerFactor n z *
              ((n : ℝ) : ℂ) ^ z).re| :=
            mul_le_mul_of_nonneg_left hpk (mul_nonneg zero_le_two (abs_nonneg m))
    have hrpow_n : (K_tot + 1) / (2 * |m| * c) < (n : ℝ) ^ (z.re - 1 / 2) :=
      hbig.trans_le (Real.rpow_le_rpow (by positivity) (by exact_mod_cast hn_ge_pk) hgap.le)
    have h2mc_pos : 0 < 2 * |m| * c := mul_pos (mul_pos two_pos (abs_pos.mpr hm)) hc_pos
    have hm1 := (div_lt_iff₀ h2mc_pos).mp hrpow_n
    have hm2 := mul_lt_mul_of_pos_right hm1 (Real.sqrt_pos.mpr hn0)
    rw [mul_comm _ (2 * |m| * c), mul_assoc, Real.sqrt_eq_rpow, ← Real.rpow_add hn0,
      sub_add_cancel, ← Real.sqrt_eq_rpow] at hm2
    have hle_K : K_tot * Real.sqrt n < (K_tot + 1) * Real.sqrt n :=
      mul_lt_mul_of_pos_right (by linarith) (Real.sqrt_pos.mpr hn0)
    linarith only [hupper, hlower, hm2, hle_K]
  · intro hζ0
    refine ⟨68 + 6 * |m| * waveTransmissionRate z, fun n hn => ?_⟩
    have hd := clippedCofactorOp_linear_add_wave_defect (n := n) (by omega) hz0 h1 m
    simpa [hζ0] using hd

/-- **Zero off-line wave on every `q ≥ 2` cofactor-divisibility slice of actual primes.**
For every integer `q ≥ 2`, on centers `n` with `q² ≤ 4n` and `gcd(n, q) = 1`, the `q`-divisible
cofactor slice `clippedCofactorSliceOp n ⌊2√n⌋₊ q Chebyshev.theta` equals
`(reflectedDensity / q) φ(n) + O_q(√n squarefreeDivisorMass n)` unconditionally — carrying zero
`n^ρ` wave because `q ℤ ∩ (2n, 4n]` contains only composites. -/
theorem clippedCofactorSliceOp_theta_of_two_le {q : ℕ} (hq : 2 ≤ q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {n : ℕ}, q ^ 2 ≤ 4 * n → n.Coprime q →
      |clippedCofactorSliceOp n ⌊2 * Real.sqrt n⌋₊ q Chebyshev.theta -
          (reflectedDensity / (q : ℝ)) * (n.totient : ℝ)| ≤
        C * Real.sqrt n * squarefreeDivisorMass n := by
  classical
  obtain ⟨A_pt, hA_pt⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  have hq0 : 0 < q := by omega
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq0
  refine ⟨52 + 2 * |A_pt|, by positivity, fun {n} hq_sq hcop => ?_⟩
  have hn1 : 1 ≤ n := by nlinarith only [hq_sq, hq]
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hsq1 : 1 ≤ Real.sqrt n := Real.one_le_sqrt.mpr hnR
  set P := ⌊2 * Real.sqrt n⌋₊
  obtain ⟨hP1, hP2, hlo, hhi⟩ := floor_two_sqrt_bounds hn1
  have hqP : q ≤ P := by
    apply Nat.le_floor
    have hR : (q : ℝ) ^ 2 ≤ (2 * Real.sqrt n) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by positivity)]; exact_mod_cast hq_sq
    nlinarith only [hR, hqR, Real.sqrt_nonneg n]
  let cp (m : ℕ) : ℝ := (((Icc 1 m).filter (n.Coprime ·)).card : ℝ)
  let wq (r : ℕ) : ℝ := cp (4 * n / (q * r)) - 2 * cp (3 * n / (q * r)) + cp (2 * n / (q * r))
  have hwq_le (r : ℕ) (hr : 1 ≤ r) : |wq r| ≤ squarefreeDivisorMass n := by
    dsimp [wq, cp]
    simp only [_root_.RHTower.Sieve.coprimeCount_eq_sum_divisors hn1, Nat.div_div_eq_div_mul,
      Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine Finset.sum_le_sum fun d hd => ?_
    have hd0 : 0 < d := Nat.pos_of_mem_divisors hd
    have hb := abs_midpoint_division_le_one (Nat.mul_pos (Nat.mul_pos hq0 hr) hd0) n
    have hid : (μ d : ℝ) * (((4 * n / (q * r * d) : ℕ) : ℝ)) -
        2 * ((μ d : ℝ) * (((3 * n / (q * r * d) : ℕ) : ℝ))) +
        (μ d : ℝ) * (((2 * n / (q * r * d) : ℕ) : ℝ)) =
        (μ d : ℝ) * (((4 * n / (q * r * d) : ℕ) : ℝ) -
          2 * ((3 * n / (q * r * d) : ℕ) : ℝ) +
          ((2 * n / (q * r * d) : ℕ) : ℝ)) := by ring
    rw [hid, abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) hb
  have hswap_q : clippedCofactorSliceOp n P q Chebyshev.theta =
      ∑ p ∈ (Ioc P (4 * n)).filter Nat.Prime, Real.log p * wq p := by
    let V := (Icc 2 (4 * n)).filter (fun v => n.Coprime v ∧ q ∣ v)
    let S := (Ioc P (4 * n)).filter Nat.Prime
    have hrow (k : ℕ) (hk : k ≤ 4) :
        (∑ p ∈ S, Real.log p * cp (k * n / (q * p))) =
          ∑ v ∈ V, (Chebyshev.theta (max P (k * n / v) : ℕ) - Chebyshev.theta P) := by
      have hcp_v (p : ℕ) (hpS : p ∈ S) : cp (k * n / (q * p)) =
          ∑ v ∈ V, if v ≤ k * n / p then (1 : ℝ) else 0 := by
        have hp_pos : 0 < p := (mem_filter.mp hpS).2.pos
        dsimp [cp]
        rw [Finset.card_eq_sum_ones, ← Finset.sum_filter]
        push_cast
        refine Finset.sum_nbij' (fun u => q * u) (fun v => v / q) ?_ ?_ ?_ ?_ (fun _ _ => rfl)
        · intro u hu
          obtain ⟨huI, huc⟩ := mem_filter.mp hu
          obtain ⟨hu1, hu_hi⟩ := mem_Icc.mp huI
          have hqu2 : 2 ≤ q * u := by nlinarith only [hq, hu1]
          have hqu_knp : q * u ≤ k * n / p := by
            have hm : u * (q * p) ≤ k * n :=
              (Nat.le_div_iff_mul_le (Nat.mul_pos hq0 hp_pos)).mp hu_hi
            exact (Nat.le_div_iff_mul_le hp_pos).mpr
              (by rw [show (q * u) * p = u * (q * p) by ring]; exact hm)
          have hqu_4n : q * u ≤ 4 * n :=
            hqu_knp.trans ((Nat.div_le_self _ _).trans (Nat.mul_le_mul_right n hk))
          exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_Icc.mpr ⟨hqu2, hqu_4n⟩,
            Nat.Coprime.mul_right hcop huc, dvd_mul_right q u⟩, hqu_knp⟩
        · intro v hv
          obtain ⟨hvV, hvp⟩ := mem_filter.mp hv
          obtain ⟨hvI, hvc, hqv⟩ := mem_filter.mp hvV
          have hmul : q * (v / q) = v := Nat.mul_div_cancel' hqv
          have hu1 : 1 ≤ v / q :=
            Nat.div_pos (Nat.le_of_dvd (by linarith [(mem_Icc.mp hvI).1]) hqv) hq0
          have hu_hi : v / q ≤ k * n / (q * p) := by
            have hm : v * p ≤ k * n := (Nat.le_div_iff_mul_le hp_pos).mp hvp
            exact (Nat.le_div_iff_mul_le (Nat.mul_pos hq0 hp_pos)).mpr
              (by rw [show (v / q) * (q * p) = (q * (v / q)) * p by ring, hmul]; exact hm)
          exact mem_filter.mpr ⟨mem_Icc.mpr ⟨hu1, hu_hi⟩,
            (Nat.coprime_mul_iff_right.mp (hmul ▸ hvc)).2⟩
        · intro u _; exact Nat.mul_div_right u hq0
        · intro v hv; exact Nat.mul_div_cancel' (mem_filter.mp (mem_filter.mp hv).1).2.2
      calc ∑ p ∈ S, Real.log p * cp (k * n / (q * p))
          = ∑ p ∈ S, ∑ v ∈ V, if v ≤ k * n / p then Real.log p else 0 := by
              refine Finset.sum_congr rfl fun p hp => ?_
              rw [hcp_v p hp, Finset.mul_sum]
              exact Finset.sum_congr rfl fun _ _ => by split_ifs <;> ring
        _ = ∑ v ∈ V, ∑ p ∈ S, if v ≤ k * n / p then Real.log p else 0 := Finset.sum_comm
        _ = ∑ v ∈ V, (Chebyshev.theta (max P (k * n / v) : ℕ) - Chebyshev.theta P) := by
              refine Finset.sum_congr rfl fun v hv => ?_
              have hv0 : 0 < v := by linarith [(mem_Icc.mp (mem_filter.mp hv).1).1]
              have hset : S.filter (fun p => v ≤ k * n / p) =
                  (Ioc P (max P (k * n / v))).filter Nat.Prime := by
                ext p
                simp only [S, mem_filter, mem_Ioc]
                constructor
                · rintro ⟨⟨⟨hPp, _⟩, hp⟩, hvp⟩
                  have hmul : v * p ≤ k * n := (Nat.le_div_iff_mul_le hp.pos).mp hvp
                  exact ⟨⟨hPp, le_max_of_le_right
                    ((Nat.le_div_iff_mul_le hv0).mpr (by rwa [mul_comm]))⟩, hp⟩
                · rintro ⟨⟨hPp, hpmax⟩, hp⟩
                  have hp_knv : p ≤ k * n / v := by omega
                  have hmul : p * v ≤ k * n := (Nat.le_div_iff_mul_le hv0).mp hp_knv
                  have hkn : k * n ≤ 4 * n := Nat.mul_le_mul_right n hk
                  have hp4n : p ≤ 4 * n := calc
                    p ≤ p * v := Nat.le_mul_of_pos_right p hv0
                    _ ≤ k * n := hmul
                    _ ≤ 4 * n := hkn
                  exact ⟨⟨⟨hPp, hp4n⟩, hp⟩,
                    (Nat.le_div_iff_mul_le hp.pos).mpr (by rwa [mul_comm])⟩
              rw [← Finset.sum_filter, hset, theta_interval_nat (le_max_left P _)]
    calc clippedCofactorSliceOp n P q Chebyshev.theta
        = ∑ v ∈ V, (Chebyshev.theta (max P (4 * n / v) : ℕ) - Chebyshev.theta P) -
            2 * ∑ v ∈ V, (Chebyshev.theta (max P (3 * n / v) : ℕ) - Chebyshev.theta P) +
            ∑ v ∈ V, (Chebyshev.theta (max P (2 * n / v) : ℕ) - Chebyshev.theta P) := by
            rw [clippedCofactorSliceOp, Finset.mul_sum, ← Finset.sum_sub_distrib,
              ← Finset.sum_add_distrib]
            exact Finset.sum_congr rfl fun _ _ => by ring
      _ = ∑ p ∈ S, Real.log p * wq p := by
            rw [← hrow 4 (by decide), ← hrow 3 (by decide), ← hrow 2 (by decide),
              Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
            exact Finset.sum_congr rfl fun _ _ => by dsimp [wq]; ring
  let Tq : ℝ :=
    (∑ b ∈ (Ioc (3 * n / q) (4 * n / q)).filter (n.Coprime ·), Real.log ((q * b : ℕ) : ℝ)) -
      (∑ b ∈ (Ioc (2 * n / q) (3 * n / q)).filter (n.Coprime ·), Real.log ((q * b : ℕ) : ℝ))
  let rStep (r : ℕ) : ℕ := r / Nat.gcd q r
  let wqr (r : ℕ) : ℝ :=
    if n.Coprime (rStep r) then
      cp (4 * n / (q * rStep r)) - 2 * cp (3 * n / (q * rStep r)) + cp (2 * n / (q * rStep r))
    else 0
  have hwqr_le (r : ℕ) (hr : 1 ≤ r) : |wqr r| ≤ squarefreeDivisorMass n := by
    dsimp [wqr]
    split_ifs with hc
    · have hrs : 1 ≤ rStep r :=
        Nat.div_pos (Nat.le_of_dvd hr (Nat.gcd_dvd_right q r)) (Nat.gcd_pos_of_pos_left r hq0)
      exact hwq_le (rStep r) hrs
    · rw [abs_zero]
      exact sum_nonneg fun _ _ => abs_nonneg _
  have hTq_mangoldt : Tq = ∑ r ∈ Icc 1 (4 * n), vonMangoldt r * wqr r := by
    have hpre (k : ℕ) (hk : k ≤ 4) :
        ∑ b ∈ (Icc 1 (k * n / q)).filter (n.Coprime ·), Real.log ((q * b : ℕ) : ℝ) =
          ∑ r ∈ Icc 1 (4 * n),
            vonMangoldt r * (if n.Coprime (rStep r) then cp (k * n / (q * rStep r)) else 0) := by
      have hlog_qb (b : ℕ) (hb : b ∈ (Icc 1 (k * n / q)).filter (n.Coprime ·)) :
          Real.log ((q * b : ℕ) : ℝ) =
            ∑ r ∈ Icc 1 (4 * n), if rStep r ∣ b then vonMangoldt r else 0 := by
        have hb1 : 1 ≤ b := (mem_Icc.mp (mem_filter.mp hb).1).1
        have hqb_le : q * b ≤ 4 * n := calc
          q * b = b * q := mul_comm q b
          _ ≤ k * n := (Nat.le_div_iff_mul_le hq0).mp (mem_Icc.mp (mem_filter.mp hb).1).2
          _ ≤ 4 * n := Nat.mul_le_mul_right n hk
        have hdiv_iff (r : ℕ) : r ∣ q * b ↔ rStep r ∣ b := by
          dsimp [rStep]
          set g := Nat.gcd q r
          have hg0 : 0 < g := Nat.gcd_pos_of_pos_left r hq0
          have hrg : g * (r / g) = r := Nat.mul_div_cancel' (Nat.gcd_dvd_right q r)
          have hqg : g * (q / g) = q := Nat.mul_div_cancel' (Nat.gcd_dvd_left q r)
          have hcop_g : Nat.Coprime (r / g) (q / g) :=
            (Nat.coprime_div_gcd_div_gcd hg0).symm
          constructor
          · intro hdvd
            have hd1 : g * (r / g) ∣ g * ((q / g) * b) := by
              rwa [hrg, ← mul_assoc, hqg]
            exact hcop_g.dvd_of_dvd_mul_left ((mul_dvd_mul_iff_left hg0.ne').mp hd1)
          · rintro ⟨m, rfl⟩
            refine ⟨(q / g) * m, ?_⟩
            calc q * (r / g * m) = (g * (q / g)) * (r / g * m) := by rw [hqg]
              _ = (g * (r / g)) * ((q / g) * m) := by ring
              _ = r * ((q / g) * m) := by rw [hrg]
        have hset : (Icc 1 (4 * n)).filter (fun r => rStep r ∣ b) = (q * b).divisors := by
          ext r
          simp only [mem_filter, mem_Icc, Nat.mem_divisors, ← hdiv_iff]
          have hqb0 : 0 < q * b := Nat.mul_pos hq0 hb1
          exact ⟨fun h => ⟨h.2, hqb0.ne'⟩,
            fun h => ⟨⟨Nat.pos_of_dvd_of_pos h.1 hqb0, (Nat.le_of_dvd hqb0 h.1).trans hqb_le⟩, h.1⟩⟩
        rw [← Finset.sum_filter, hset, vonMangoldt_sum]
      calc ∑ b ∈ (Icc 1 (k * n / q)).filter (n.Coprime ·), Real.log ((q * b : ℕ) : ℝ)
          = ∑ b ∈ (Icc 1 (k * n / q)).filter (n.Coprime ·),
              ∑ r ∈ Icc 1 (4 * n), if rStep r ∣ b then vonMangoldt r else 0 :=
            Finset.sum_congr rfl hlog_qb
        _ = ∑ r ∈ Icc 1 (4 * n),
              ∑ b ∈ (Icc 1 (k * n / q)).filter (n.Coprime ·),
                if rStep r ∣ b then vonMangoldt r else 0 := Finset.sum_comm
        _ = ∑ r ∈ Icc 1 (4 * n),
              vonMangoldt r * (if n.Coprime (rStep r) then cp (k * n / (q * rStep r)) else 0) := by
              refine Finset.sum_congr rfl fun r hr => ?_
              have hr1 : 1 ≤ r := (mem_Icc.mp hr).1
              have hrs0 : 0 < rStep r :=
                Nat.div_pos (Nat.le_of_dvd hr1 (Nat.gcd_dvd_right q r))
                  (Nat.gcd_pos_of_pos_left r hq0)
              by_cases hrcop : n.Coprime (rStep r)
              · rw [if_pos hrcop, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
                congr 1
                dsimp [cp]
                congr 1
                refine Finset.card_nbij' (fun b => b / rStep r) (fun u => rStep r * u) ?_ ?_ ?_ ?_
                · intro b hb
                  obtain ⟨hb1, hbr⟩ := mem_filter.mp hb
                  obtain ⟨hbI, hbc⟩ := mem_filter.mp hb1
                  have hmul : rStep r * (b / rStep r) = b := Nat.mul_div_cancel' hbr
                  have hu_hi : b / rStep r ≤ k * n / (q * rStep r) := by
                    have hm : b * q ≤ k * n := (Nat.le_div_iff_mul_le hq0).mp (mem_Icc.mp hbI).2
                    exact (Nat.le_div_iff_mul_le (Nat.mul_pos hq0 hrs0)).mpr
                      (by rw [show (b / rStep r) * (q * rStep r) = (rStep r * (b / rStep r)) * q by ring, hmul]; exact hm)
                  exact mem_filter.mpr ⟨mem_Icc.mpr
                    ⟨Nat.div_pos (Nat.le_of_dvd (mem_Icc.mp hbI).1 hbr) hrs0, hu_hi⟩,
                    (Nat.coprime_mul_iff_right.mp (hmul ▸ hbc)).2⟩
                · intro u hu
                  obtain ⟨huI, huc⟩ := mem_filter.mp hu
                  have hm : u * (q * rStep r) ≤ k * n :=
                    (Nat.le_div_iff_mul_le (Nat.mul_pos hq0 hrs0)).mp (mem_Icc.mp huI).2
                  have hbu_hi : rStep r * u ≤ k * n / q :=
                    (Nat.le_div_iff_mul_le hq0).mpr
                      (by rw [show (rStep r * u) * q = u * (q * rStep r) by ring]; exact hm)
                  exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_Icc.mpr
                    ⟨Nat.mul_pos hrs0 (mem_Icc.mp huI).1, hbu_hi⟩,
                    Nat.Coprime.mul_right hrcop huc⟩, dvd_mul_right _ _⟩
                · intro b hb; exact Nat.mul_div_cancel' (mem_filter.mp hb).2
                · intro u _; exact Nat.mul_div_right u hrs0
              · rw [if_neg hrcop, mul_zero]
                refine Finset.sum_eq_zero fun b hb => ?_
                rw [if_neg]
                intro hdvd
                exact hrcop ((mem_filter.mp hb).2.coprime_dvd_right hdvd)
    have hsplit_b {l u : ℕ} (hlu : l ≤ u) :
        (∑ b ∈ (Ioc l u).filter (n.Coprime ·), Real.log ((q * b : ℕ) : ℝ)) =
          (∑ b ∈ (Icc 1 u).filter (n.Coprime ·), Real.log ((q * b : ℕ) : ℝ)) -
            (∑ b ∈ (Icc 1 l).filter (n.Coprime ·), Real.log ((q * b : ℕ) : ℝ)) := by
      simp only [Finset.sum_filter, show Icc 1 u = Ioc 0 u by ext x; simp [mem_Icc, mem_Ioc]; omega,
        show Icc 1 l = Ioc 0 l by ext x; simp [mem_Icc, mem_Ioc]; omega]
      linarith only [Finset.sum_Ioc_consecutive
        (fun b : ℕ => if n.Coprime b then Real.log ((q * b : ℕ) : ℝ) else 0) (Nat.zero_le l) hlu]
    dsimp [Tq]
    rw [hsplit_b (Nat.div_le_div_right (show 3 * n ≤ 4 * n by omega)),
      hsplit_b (Nat.div_le_div_right (show 2 * n ≤ 3 * n by omega)),
      hpre 4 (by decide), hpre 3 (by decide), hpre 2 (by decide),
      ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun r _ => ?_
    dsimp [wqr]; split_ifs <;> ring
  have hlog4n_2 : Real.log (4 * (n : ℝ)) ≤ 2 * Real.sqrt n := by
    have hl1 := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < Real.sqrt n)
    have hl2 : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
    have h4n : Real.log (4 * (n : ℝ)) = 2 * Real.log 2 + 2 * Real.log (Real.sqrt n) := by
      have hsq_eq : (n : ℝ) = (Real.sqrt n) ^ 2 := (Real.sq_sqrt (by linarith)).symm
      conv_lhs =>
        rw [Real.log_mul (by norm_num) (by linarith),
          show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow, hsq_eq, Real.log_pow]
      push_cast; ring
    linarith only [h4n, hl1, hl2]
  have hslice_sub_Tq :
      |clippedCofactorSliceOp n P q Chebyshev.theta - Tq| ≤
        (18 + 2 * |A_pt|) * Real.sqrt n * squarefreeDivisorMass n := by
    rw [hswap_q, hTq_mangoldt]
    have hIcc_split : Icc 1 (4 * n) = Icc 1 P ∪ Ioc P (4 * n) := by
      ext r; simp only [mem_Icc, mem_union, mem_Ioc]; omega
    have hdisj : Disjoint (Icc 1 P) (Ioc P (4 * n)) :=
      Finset.disjoint_left.mpr fun _ h1 h2 => (mem_Ioc.mp h2).1.not_ge (mem_Icc.mp h1).2
    rw [hIcc_split, Finset.sum_union hdisj,
      ← Finset.sum_filter_add_sum_filter_not (Ioc P (4 * n)) Nat.Prime]
    have hsmall : |∑ r ∈ Icc 1 P, vonMangoldt r * wqr r| ≤
        14 * Real.sqrt n * squarefreeDivisorMass n := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      have h1 : ∑ r ∈ Icc 1 P, |vonMangoldt r * wqr r| ≤
          (∑ r ∈ Icc 1 P, vonMangoldt r) * squarefreeDivisorMass n := by
        rw [Finset.sum_mul]
        refine Finset.sum_le_sum fun r hr => ?_
        rw [abs_mul, abs_of_nonneg vonMangoldt_nonneg]
        exact mul_le_mul_of_nonneg_left (hwqr_le r (mem_Icc.mp hr).1) vonMangoldt_nonneg
      have h7 : ∑ r ∈ Icc 1 P, vonMangoldt r ≤ 14 * Real.sqrt n :=
        (_root_.RHTower.sum_vonMangoldt_Icc_le_seven P).trans (by linarith only [hhi])
      exact h1.trans (mul_le_mul_of_nonneg_right h7 (sum_nonneg fun _ _ => abs_nonneg _))
    have hpow : |∑ r ∈ (Ioc P (4 * n)).filter (fun r => ¬ r.Prime), vonMangoldt r * wqr r| ≤
        2 * |A_pt| * Real.sqrt n * squarefreeDivisorMass n := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      have h1 : ∑ r ∈ (Ioc P (4 * n)).filter (fun r => ¬ r.Prime), |vonMangoldt r * wqr r| ≤
          (∑ r ∈ (Ioc 0 (4 * n)).filter (fun r => ¬ r.Prime), vonMangoldt r) *
            squarefreeDivisorMass n := by
        rw [Finset.sum_mul]
        refine (Finset.sum_le_sum fun r hr => ?_).trans
          (Finset.sum_le_sum_of_subset_of_nonneg ?_
            (fun _ _ _ => mul_nonneg vonMangoldt_nonneg (sum_nonneg fun _ _ => abs_nonneg _)))
        · rw [abs_mul, abs_of_nonneg vonMangoldt_nonneg]
          exact mul_le_mul_of_nonneg_left
            (hwqr_le r (by linarith [(mem_Ioc.mp (mem_filter.mp hr).1).1])) vonMangoldt_nonneg
        · intro r hr
          obtain ⟨hrI, hrnp⟩ := mem_filter.mp hr
          exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨by linarith [(mem_Ioc.mp hrI).1], (mem_Ioc.mp hrI).2⟩,
            hrnp⟩
      have hsum_pt : (∑ r ∈ (Ioc 0 (4 * n)).filter (fun r => ¬ r.Prime), vonMangoldt r) =
          Chebyshev.psi (4 * n : ℕ) - Chebyshev.theta (4 * n : ℕ) := by
        rw [Chebyshev.psi_sub_theta_eq_sum_not_prime, Nat.floor_natCast]
      rw [hsum_pt] at h1
      have hpt : Chebyshev.psi (4 * n : ℕ) - Chebyshev.theta (4 * n : ℕ) ≤
          2 * |A_pt| * Real.sqrt n := by
        have hsq4 : Real.sqrt (4 * n : ℕ) = 2 * Real.sqrt n := by
          rw [Nat.cast_mul, Nat.cast_ofNat, Real.sqrt_mul (by norm_num),
            show Real.sqrt 4 = 2 by norm_num]
        exact (hA_pt (4 * n : ℕ)).trans
          ((mul_le_mul_of_nonneg_right (le_abs_self A_pt) (Real.sqrt_nonneg _)).trans_eq
            (by rw [hsq4]; ring))
      exact h1.trans (mul_le_mul_of_nonneg_right hpt (sum_nonneg fun _ _ => abs_nonneg _))
    have hforb : |(∑ p ∈ (Ioc P (4 * n)).filter Nat.Prime, Real.log p * wq p) -
        (∑ p ∈ (Ioc P (4 * n)).filter Nat.Prime, vonMangoldt p * wqr p)| ≤
        4 * Real.sqrt n * squarefreeDivisorMass n := by
      rw [← Finset.sum_sub_distrib]
      let Fb := ((Ioc P (4 * n)).filter Nat.Prime).filter (· ∣ n)
      have hcard_Fb : Fb.card ≤ 1 := by
        rw [Finset.card_le_one_iff]
        intro p₁ p₂ hp₁ hp₂
        by_contra hne
        obtain ⟨hp₁S, hd₁⟩ := mem_filter.mp hp₁
        obtain ⟨hp₂S, hd₂⟩ := mem_filter.mp hp₂
        obtain ⟨hp₁I, hpr₁⟩ := mem_filter.mp hp₁S
        obtain ⟨hp₂I, hpr₂⟩ := mem_filter.mp hp₂S
        have hgt₁ : 2 * Real.sqrt n < p₁ := (Nat.floor_lt (by positivity)).mp (mem_Ioc.mp hp₁I).1
        have hgt₂ : 2 * Real.sqrt n < p₂ := (Nat.floor_lt (by positivity)).mp (mem_Ioc.mp hp₂I).1
        have hcop₁₂ : Nat.Coprime p₁ p₂ :=
          hpr₁.coprime_iff_not_dvd.mpr fun hd =>
            hne ((Nat.dvd_prime hpr₂).mp hd |>.resolve_left hpr₁.ne_one)
        have hmul_dvd : p₁ * p₂ ∣ n := hcop₁₂.mul_dvd_of_dvd_of_dvd hd₁ hd₂
        have hmul_le : (p₁ : ℝ) * (p₂ : ℝ) ≤ n := by
          exact_mod_cast Nat.le_of_dvd hn1 hmul_dvd
        have hmul_gt : 4 * (n : ℝ) < (p₁ : ℝ) * (p₂ : ℝ) := by
          have hm := mul_lt_mul'' hgt₁ hgt₂ (by positivity) (by positivity)
          nlinarith only [hm, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ n)]
        linarith only [hmul_le, hmul_gt, hnR]
      have hsupp : ∑ p ∈ (Ioc P (4 * n)).filter Nat.Prime,
          (Real.log p * wq p - vonMangoldt p * wqr p) =
          ∑ p ∈ Fb, Real.log p * wq p := by
        rw [← Finset.sum_subset (Finset.filter_subset (· ∣ n) ((Ioc P (4 * n)).filter Nat.Prime))]
        · refine Finset.sum_congr rfl fun p hpFb => ?_
          obtain ⟨hpS, hdvd⟩ := mem_filter.mp hpFb
          obtain ⟨hpI, hpr⟩ := mem_filter.mp hpS
          have hPp : P < p := (mem_Ioc.mp hpI).1
          have hcop_qp : Nat.Coprime q p :=
            (hpr.coprime_iff_not_dvd.mpr fun hd =>
              (hqP.trans_lt hPp).not_ge (Nat.le_of_dvd hq0 hd)).symm
          have hrp : rStep p = p := by dsimp [rStep]; rw [hcop_qp.gcd_eq_one, Nat.div_one]
          have hncop : ¬ n.Coprime (rStep p) := by
            rw [hrp]
            intro hc
            exact hpr.ne_one (Nat.eq_one_of_dvd_one (hc.gcd_eq_one ▸ Nat.dvd_gcd hdvd dvd_rfl))
          dsimp [wqr]
          rw [if_neg hncop, mul_zero, sub_zero]
        · intro p hpS hpnot
          obtain ⟨hpI, hpr⟩ := mem_filter.mp hpS
          have hndvd : ¬ p ∣ n := fun hd => hpnot (mem_filter.mpr ⟨hpS, hd⟩)
          have hPp : P < p := (mem_Ioc.mp hpI).1
          have hcop_qp : Nat.Coprime q p :=
            (hpr.coprime_iff_not_dvd.mpr fun hd =>
              (hqP.trans_lt hPp).not_ge (Nat.le_of_dvd hq0 hd)).symm
          have hrp : rStep p = p := by dsimp [rStep]; rw [hcop_qp.gcd_eq_one, Nat.div_one]
          have hcop_np : n.Coprime (rStep p) := by
            rw [hrp]; exact (hpr.coprime_iff_not_dvd.mpr hndvd).symm
          rw [vonMangoldt_apply_prime hpr]
          dsimp [wqr]
          rw [if_pos hcop_np, hrp, sub_self]
      rw [hsupp]
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      have hpt_Fb : ∀ p ∈ Fb, |Real.log p * wq p| ≤
          4 * Real.sqrt n * squarefreeDivisorMass n := by
        intro p hpFb
        obtain ⟨hpS, _⟩ := mem_filter.mp hpFb
        have hpr := (mem_filter.mp hpS).2
        have hpn : p ≤ 4 * n := (mem_Ioc.mp (mem_filter.mp hpS).1).2
        have hlp : Real.log p ≤ 4 * Real.sqrt n := by
          have hp0 : (0 : ℝ) < p := by exact_mod_cast hpr.pos
          have hp4n : (p : ℝ) ≤ 4 * (n : ℝ) := by exact_mod_cast hpn
          have hl1 := (Real.log_le_log hp0 hp4n).trans hlog4n_2
          linarith only [hl1, Real.sqrt_nonneg n]
        rw [abs_mul, abs_of_nonneg (Real.log_nonneg (by exact_mod_cast hpr.one_lt.le))]
        exact mul_le_mul hlp (hwq_le p hpr.one_lt.le) (abs_nonneg _) (by positivity)
      calc ∑ p ∈ Fb, |Real.log p * wq p|
          ≤ ∑ _p ∈ Fb, 4 * Real.sqrt n * squarefreeDivisorMass n := Finset.sum_le_sum hpt_Fb
        _ = (Fb.card : ℝ) * (4 * Real.sqrt n * squarefreeDivisorMass n) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ 1 * (4 * Real.sqrt n * squarefreeDivisorMass n) :=
            mul_le_mul_of_nonneg_right (by exact_mod_cast hcard_Fb)
              (mul_nonneg (by positivity) (sum_nonneg fun _ _ => abs_nonneg _))
        _ = 4 * Real.sqrt n * squarefreeDivisorMass n := one_mul _
    set S_sm := ∑ r ∈ Icc 1 P, vonMangoldt r * wqr r
    set S_pr := ∑ p ∈ (Ioc P (4 * n)).filter Nat.Prime, vonMangoldt p * wqr p
    set S_pw := ∑ r ∈ (Ioc P (4 * n)).filter (fun r => ¬ r.Prime), vonMangoldt r * wqr r
    set S_sl := ∑ p ∈ (Ioc P (4 * n)).filter Nat.Prime, Real.log p * wq p
    have hsplit_eq : S_sl - (S_sm + (S_pr + S_pw)) = (S_sl - S_pr) - S_sm - S_pw := by ring
    rw [hsplit_eq]
    have ht1 := (abs_sub (S_sl - S_pr - S_sm) S_pw).trans
      (add_le_add (abs_sub (S_sl - S_pr) S_sm) le_rfl)
    linarith only [ht1, hforb, hsmall, hpow]
  have hTq_totient :
      |Tq - (reflectedDensity / (q : ℝ)) * (n.totient : ℝ)| ≤
        34 * Real.sqrt n * squarefreeDivisorMass n := by
    have hstirling_all {t : ℝ} (ht : 0 < t) (ht_hi : t ≤ 4 * (n : ℝ)) :
        |(∑ j ∈ Icc 1 ⌊t⌋₊, Real.log (j : ℝ)) - (t * Real.log t - t)| ≤
          3 * Real.sqrt n + 4 := by
      by_cases ht1 : 1 ≤ t
      · set M := ⌊t⌋₊
        have hM1 : 1 ≤ M := Nat.le_floor (by exact_mod_cast ht1)
        have hMR1 : (1 : ℝ) ≤ M := by exact_mod_cast hM1
        have hMt : (M : ℝ) ≤ t := Nat.floor_le ht.le
        have ht_M1 : t ≤ (M : ℝ) + 1 := (Nat.lt_floor_add_one t).le
        obtain ⟨hlo_st, hhi_st⟩ := _root_.RHTower.sum_log_Icc_exact_stirling_bounds hM1
        have hlogt_2 : Real.log t ≤ 2 * Real.sqrt n :=
          (Real.log_le_log ht ht_hi).trans hlog4n_2
        have hlogM_2 : Real.log (M : ℝ) ≤ 2 * Real.sqrt n :=
          (Real.log_le_log (by positivity) (hMt.trans ht_hi)).trans hlog4n_2
        have hpi_le : Real.log (2 * Real.pi) / 2 ≤ 2 := by
          have h2pi : 2 * Real.pi ≤ Real.exp 4 := by
            have hpi : Real.pi < 4 := Real.pi_lt_four
            have he1 : (2 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
            have he4 : (16 : ℝ) ≤ Real.exp 4 := by
              rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) * 1 by norm_num, Real.exp_nat_mul]
              exact (show (16 : ℝ) = 2 ^ 4 by norm_num).trans_le
                (pow_le_pow_left₀ (by norm_num) he1.le 4)
            linarith
          have hl := Real.log_le_log (by positivity) h2pi
          rw [Real.log_exp] at hl; linarith
        have hst_M : |(∑ j ∈ Icc 1 M, Real.log (j : ℝ)) - ((M : ℝ) * Real.log M - M)| ≤
            Real.sqrt n + 3 := by
          have h12 : 1 / (12 * (M : ℝ)) ≤ 1 := by
            rw [div_le_iff₀ (by positivity)]; linarith only [hMR1]
          have hlogM_nn : 0 ≤ Real.log (M : ℝ) := Real.log_nonneg hMR1
          have hpi_nn : 0 ≤ Real.log (2 * Real.pi) :=
            Real.log_nonneg (by linarith [Real.pi_gt_three])
          rw [abs_le]
          constructor <;> linarith only [hlo_st, hhi_st, hlogM_2, hlogM_nn, hpi_le, hpi_nn, h12]
        have hmvt_st : |(t * Real.log t - t) - ((M : ℝ) * Real.log M - M)| ≤ 2 * Real.sqrt n := by
          have hlo_d : 0 ≤ (t * Real.log t - t) - ((M : ℝ) * Real.log M - M) := by
            have hl := Real.log_le_sub_one_of_pos (div_pos (by positivity : (0 : ℝ) < M) ht)
            rw [Real.log_div (by positivity) ht.ne'] at hl
            have hm := mul_le_mul_of_nonneg_left hl ht.le
            rw [mul_sub, mul_sub, mul_div_cancel₀ _ ht.ne'] at hm
            have hlogM_le_t : Real.log M ≤ Real.log t := Real.log_le_log (by positivity) hMt
            have hdiff_nn : 0 ≤ t - M := sub_nonneg.mpr hMt
            nlinarith only [hm, hlogM_le_t, hdiff_nn, Real.log_nonneg hMR1]
          have hhi_d : (t * Real.log t - t) - ((M : ℝ) * Real.log M - M) ≤ 2 * Real.sqrt n := by
            have hl := Real.log_le_sub_one_of_pos (div_pos ht (by positivity : (0 : ℝ) < M))
            rw [Real.log_div ht.ne' (by positivity)] at hl
            have hm := mul_le_mul_of_nonneg_left hl (by positivity : (0 : ℝ) ≤ M)
            rw [mul_sub, mul_sub, mul_div_cancel₀ _ (by positivity : (M : ℝ) ≠ 0)] at hm
            have hdiff1 : t - M ≤ 1 := by linarith only [ht_M1]
            have hlogt_nn : 0 ≤ Real.log t := Real.log_nonneg ht1
            have h1 : (t - M) * Real.log t ≤ 1 * (2 * Real.sqrt n) :=
              mul_le_mul hdiff1 hlogt_2 hlogt_nn zero_le_one
            nlinarith only [hm, h1]
          exact abs_le.mpr ⟨by linarith only [hlo_d, Real.sqrt_nonneg n], hhi_d⟩
        have htri := abs_sub ((∑ j ∈ Icc 1 M, Real.log (j : ℝ)) - ((M : ℝ) * Real.log M - M))
          ((t * Real.log t - t) - ((M : ℝ) * Real.log M - M))
        rw [sub_sub_sub_cancel_right] at htri
        linarith only [htri, hst_M, hmvt_st]
      · push Not at ht1
        have hfl0 : ⌊t⌋₊ = 0 := Nat.floor_eq_zero.mpr ht1
        rw [hfl0]
        simp only [Icc_eq_empty (by decide : ¬ 1 ≤ 0), Finset.sum_empty, zero_sub, abs_neg]
        have hl := Real.log_le_sub_one_of_pos (inv_pos.mpr ht)
        rw [Real.log_inv] at hl
        have hm := mul_le_mul_of_nonneg_left hl ht.le
        rw [mul_neg, mul_sub, mul_inv_cancel₀ ht.ne', mul_one] at hm
        have hhi_0 : t * Real.log t ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos ht.le (Real.log_nonpos ht.le ht1.le)
        rw [abs_le]
        constructor <;> linarith only [hm, hhi_0, ht, ht1, Real.sqrt_nonneg n]
    have hTq_moeb : Tq = ∑ d ∈ n.divisors, (μ d : ℝ) *
        (Real.log ((q * d : ℕ) : ℝ) *
          (((4 * n / (q * d) : ℕ) : ℝ) - 2 * ((3 * n / (q * d) : ℕ) : ℝ) +
            ((2 * n / (q * d) : ℕ) : ℝ)) +
          ((∑ j ∈ Icc 1 (4 * n / (q * d)), Real.log (j : ℝ)) -
            2 * (∑ j ∈ Icc 1 (3 * n / (q * d)), Real.log (j : ℝ)) +
            (∑ j ∈ Icc 1 (2 * n / (q * d)), Real.log (j : ℝ)))) := by
      have hpre_b (k : ℕ) :
          ∑ b ∈ (Icc 1 (k * n / q)).filter (n.Coprime ·), Real.log ((q * b : ℕ) : ℝ) =
            ∑ d ∈ n.divisors, (μ d : ℝ) *
              (Real.log ((q * d : ℕ) : ℝ) * ((k * n / (q * d) : ℕ) : ℝ) +
                ∑ j ∈ Icc 1 (k * n / (q * d)), Real.log (j : ℝ)) := by
        rw [sum_coprime_Icc_real hn1]
        refine Finset.sum_congr rfl fun d hd => ?_
        congr 1
        have hd0 : 0 < d := Nat.pos_of_mem_divisors hd
        rw [Nat.div_div_eq_div_mul]
        have hlj (j : ℕ) (hj : j ∈ Icc 1 (k * n / (q * d))) :
            Real.log ((q * (d * j) : ℕ) : ℝ) = Real.log ((q * d : ℕ) : ℝ) + Real.log (j : ℝ) := by
          have hj1 : 1 ≤ j := (mem_Icc.mp hj).1
          rw [show (q * (d * j) : ℕ) = (q * d) * j by ring, Nat.cast_mul,
            Real.log_mul (by exact_mod_cast (Nat.mul_pos hq0 hd0).ne')
              (by exact_mod_cast (by omega : j ≠ 0))]
        rw [Finset.sum_congr rfl hlj, Finset.sum_add_distrib, Finset.sum_const, Nat.card_Icc,
          Nat.add_sub_cancel, nsmul_eq_mul, mul_comm _ (Real.log ((q * d : ℕ) : ℝ))]
      have hsplit_b {l u : ℕ} (hlu : l ≤ u) :
          (∑ b ∈ (Ioc l u).filter (n.Coprime ·), Real.log ((q * b : ℕ) : ℝ)) =
            (∑ b ∈ (Icc 1 u).filter (n.Coprime ·), Real.log ((q * b : ℕ) : ℝ)) -
              (∑ b ∈ (Icc 1 l).filter (n.Coprime ·), Real.log ((q * b : ℕ) : ℝ)) := by
        simp only [Finset.sum_filter, show Icc 1 u = Ioc 0 u by ext x; simp [mem_Icc, mem_Ioc]; omega,
          show Icc 1 l = Ioc 0 l by ext x; simp [mem_Icc, mem_Ioc]; omega]
        linarith only [Finset.sum_Ioc_consecutive
          (fun b : ℕ => if n.Coprime b then Real.log ((q * b : ℕ) : ℝ) else 0) (Nat.zero_le l) hlu]
      dsimp [Tq]
      rw [hsplit_b (Nat.div_le_div_right (show 3 * n ≤ 4 * n by omega)),
        hsplit_b (Nat.div_le_div_right (show 2 * n ≤ 3 * n by omega)),
        hpre_b 4, hpre_b 3, hpre_b 2,
        ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun _ _ => by ring
    have htot : (reflectedDensity / (q : ℝ)) * (n.totient : ℝ) =
        ∑ d ∈ n.divisors, (μ d : ℝ) * (reflectedDensity * (n : ℝ) / ((q : ℝ) * (d : ℝ))) := by
      rw [_root_.RHTower.Sieve.totient_eq_sum_moebius_mul n hn1, Finset.mul_sum]
      refine Finset.sum_congr rfl fun d hd => ?_
      have hdvd : d ∣ n := Nat.dvd_of_mem_divisors hd
      have hd0 : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_mem_divisors hd
      have hnd : ((n / d : ℕ) : ℝ) = (n : ℝ) / (d : ℝ) := by
        exact_mod_cast Nat.cast_div hdvd hd0.ne'
      rw [hnd]; field_simp [hqR.ne', hd0.ne']
    rw [hTq_moeb, htot, ← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [squarefreeDivisorMass, Finset.mul_sum]
    refine Finset.sum_le_sum fun d hd => ?_
    have hd0 : 0 < d := Nat.pos_of_mem_divisors hd
    have hdR : (0 : ℝ) < d := by exact_mod_cast hd0
    have hdn : d ≤ n := Nat.le_of_dvd hn1 (Nat.dvd_of_mem_divisors hd)
    rw [← mul_sub, abs_mul, mul_comm (34 * Real.sqrt n) |(μ d : ℝ)|]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    have hlog_qd : |Real.log ((q * d : ℕ) : ℝ) *
        (((4 * n / (q * d) : ℕ) : ℝ) - 2 * ((3 * n / (q * d) : ℕ) : ℝ) +
          ((2 * n / (q * d) : ℕ) : ℝ))| ≤ 6 * Real.sqrt n := by
      have hqd1 : (1 : ℝ) ≤ (q * d : ℕ) := by exact_mod_cast Nat.mul_pos hq0 hd0
      have hqd_le : ((q * d : ℕ) : ℝ) ≤ (2 * Real.sqrt n) ^ 3 := by
        have hq_le : (q : ℝ) ≤ 2 * Real.sqrt n := (by exact_mod_cast hqP : (q : ℝ) ≤ P).trans hhi
        have hd_le : (d : ℝ) ≤ (Real.sqrt n) ^ 2 := by
          rw [Real.sq_sqrt (by positivity)]; exact_mod_cast hdn
        push_cast
        nlinarith only [hq_le, hd_le, hsq1, hqR, hdR]
      have hl_qd : Real.log ((q * d : ℕ) : ℝ) ≤ 6 * Real.sqrt n := by
        have hl1 := Real.log_le_log (by positivity) hqd_le
        rw [Real.log_pow] at hl1
        simp only [Nat.cast_ofNat] at hl1
        have hl2 := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < 2 * Real.sqrt n)
        linarith only [hl1, hl2, hsq1]
      rw [abs_mul, abs_of_nonneg (Real.log_nonneg hqd1)]
      exact mul_le_of_le_one_right (by positivity)
        (abs_midpoint_division_le_one (Nat.mul_pos hq0 hd0) n) |>.trans hl_qd
    set u : ℝ := (n : ℝ) / ((q : ℝ) * (d : ℝ))
    have hu : 0 < u := by dsimp [u]; positivity
    have hfl_u (k : ℕ) : k * n / (q * d) = ⌊(k : ℝ) * u⌋₊ := by
      have he : (k : ℝ) * u = ((k * n : ℕ) : ℝ) / (((q * d : ℕ) : ℝ)) := by
        dsimp [u]; push_cast; ring
      rw [he, Nat.floor_div_natCast, Nat.floor_natCast]
    have hu_le (k : ℕ) (hk : k ≤ 4) : (k : ℝ) * u ≤ 4 * (n : ℝ) := by
      dsimp [u]
      have hqd1 : (1 : ℝ) ≤ (q : ℝ) * (d : ℝ) := by
        exact_mod_cast Nat.mul_pos hq0 hd0
      calc (k : ℝ) * ((n : ℝ) / ((q : ℝ) * (d : ℝ)))
          = ((k : ℝ) * (n : ℝ)) / ((q : ℝ) * (d : ℝ)) := by ring
        _ ≤ (4 * (n : ℝ)) / 1 :=
            div_le_div₀ (by positivity)
              (mul_le_mul_of_nonneg_right (by exact_mod_cast hk) (by positivity)) zero_lt_one hqd1
        _ = 4 * (n : ℝ) := div_one _
    have hmain_st :
        ((4 : ℝ) * u * Real.log ((4 : ℝ) * u) - (4 : ℝ) * u) -
          2 * ((3 : ℝ) * u * Real.log ((3 : ℝ) * u) - (3 : ℝ) * u) +
          ((2 : ℝ) * u * Real.log ((2 : ℝ) * u) - (2 : ℝ) * u) =
          reflectedDensity * (n : ℝ) / ((q : ℝ) * (d : ℝ)) := by
      have hl4 : Real.log ((4 : ℝ) * u) = 2 * Real.log 2 + Real.log u := by
        rw [Real.log_mul (by norm_num) hu.ne', show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
        norm_num
      have hl3 : Real.log ((3 : ℝ) * u) = Real.log 3 + Real.log u :=
        Real.log_mul (by norm_num) hu.ne'
      have hl2 : Real.log ((2 : ℝ) * u) = Real.log 2 + Real.log u :=
        Real.log_mul (by norm_num) hu.ne'
      rw [hl4, hl3, hl2, reflectedDensity]
      dsimp [u]; ring
    rw [hfl_u 4, hfl_u 3, hfl_u 2] at hlog_qd ⊢
    rw [← hmain_st]
    have hs4 := hstirling_all (show 0 < ((4 : ℕ) : ℝ) * u by positivity) (hu_le 4 (by decide))
    have hs3 := hstirling_all (show 0 < ((3 : ℕ) : ℝ) * u by positivity) (hu_le 3 (by decide))
    have hs2 := hstirling_all (show 0 < ((2 : ℕ) : ℝ) * u by positivity) (hu_le 2 (by decide))
    simp only [Nat.cast_ofNat] at hlog_qd hs4 hs3 hs2 ⊢
    obtain ⟨l4, u4⟩ := abs_le.mp hs4
    obtain ⟨l3, u3⟩ := abs_le.mp hs3
    obtain ⟨l2, u2⟩ := abs_le.mp hs2
    have hst_comb : |((∑ j ∈ Icc 1 ⌊4 * u⌋₊, Real.log (j : ℝ)) -
          2 * (∑ j ∈ Icc 1 ⌊3 * u⌋₊, Real.log (j : ℝ)) +
          (∑ j ∈ Icc 1 ⌊2 * u⌋₊, Real.log (j : ℝ))) -
        ((4 * u * Real.log (4 * u) - 4 * u) -
          2 * (3 * u * Real.log (3 * u) - 3 * u) +
          (2 * u * Real.log (2 * u) - 2 * u))| ≤ 12 * Real.sqrt n + 16 := by
      rw [abs_le]; constructor <;> linarith only [l4, u4, l3, u3, l2, u2]
    have hadd_sub :
        Real.log ((q * d : ℕ) : ℝ) *
            ((⌊4 * u⌋₊ : ℝ) - 2 * (⌊3 * u⌋₊ : ℝ) + (⌊2 * u⌋₊ : ℝ)) +
          ((∑ j ∈ Icc 1 ⌊4 * u⌋₊, Real.log (j : ℝ)) -
            2 * (∑ j ∈ Icc 1 ⌊3 * u⌋₊, Real.log (j : ℝ)) +
            (∑ j ∈ Icc 1 ⌊2 * u⌋₊, Real.log (j : ℝ))) -
          ((4 * u * Real.log (4 * u) - 4 * u) -
            2 * (3 * u * Real.log (3 * u) - 3 * u) +
            (2 * u * Real.log (2 * u) - 2 * u)) =
        Real.log ((q * d : ℕ) : ℝ) *
            ((⌊4 * u⌋₊ : ℝ) - 2 * (⌊3 * u⌋₊ : ℝ) + (⌊2 * u⌋₊ : ℝ)) +
          (((∑ j ∈ Icc 1 ⌊4 * u⌋₊, Real.log (j : ℝ)) -
              2 * (∑ j ∈ Icc 1 ⌊3 * u⌋₊, Real.log (j : ℝ)) +
              (∑ j ∈ Icc 1 ⌊2 * u⌋₊, Real.log (j : ℝ))) -
            ((4 * u * Real.log (4 * u) - 4 * u) -
              2 * (3 * u * Real.log (3 * u) - 3 * u) +
              (2 * u * Real.log (2 * u) - 2 * u))) := by ring
    rw [hadd_sub]
    have htri := abs_add_le _ _
    linarith only [htri, hlog_qd, hst_comb, hsq1]
  have htri := abs_add_le (clippedCofactorSliceOp n P q Chebyshev.theta - Tq)
    (Tq - (reflectedDensity / (q : ℝ)) * (n.totient : ℝ))
  rw [sub_add_sub_cancel] at htri
  linarith only [htri, hslice_sub_Tq, hTq_totient]

/-! ### 6. Remainder cancellation and individual cofactor cells under `HasSingleOffLineQuartet` -/

private theorem singleQuartet_theta_mode_all {ρ₀ : ℂ} (hq : HasSingleOffLineQuartet ρ₀) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x : ℝ, 1 ≤ x →
      |Chebyshev.theta x - x - quartetWaveModel ρ₀ (quartetCopyMult ρ₀ : ℝ) x| ≤
        K * Real.sqrt x * (1 + Real.log x) ^ 2 := by
  obtain ⟨K₀, hK₀⟩ := (hasSingleOffLineQuartet_iff_chebyshevPsi_singleWave hq.1 hq.2.1).mp hq
  obtain ⟨A_pt, hA_pt⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  have hρ_ne : ρ₀ ≠ 0 := fun he => by
    have h := hq.1; rw [he, Complex.zero_re] at h; linarith
  set D_w : ℝ := 2 * (quartetCopyMult ρ₀ : ℝ) / ‖ρ₀‖
  set M₁₆ : ℝ := Chebyshev.psi 16 + 16
  have hM₁₆_nn : 0 ≤ M₁₆ := by
    have := Chebyshev.psi_nonneg 16
    dsimp [M₁₆]; linarith
  refine ⟨|K₀| + |A_pt| + M₁₆ + 16 * D_w, by dsimp [D_w]; positivity, fun x hx => ?_⟩
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hsq1 : 1 ≤ Real.sqrt x := Real.one_le_sqrt.mpr hx
  have hlog_nn : 0 ≤ Real.log x := Real.log_nonneg hx
  have h1_sq : 1 ≤ (1 + Real.log x) ^ 2 := by nlinarith
  have hpt : |Chebyshev.psi x - Chebyshev.theta x| ≤
      |A_pt| * Real.sqrt x * (1 + Real.log x) ^ 2 := by
    rw [abs_of_nonneg (sub_nonneg.mpr (Chebyshev.theta_le_psi x))]
    exact (hA_pt x).trans
      ((mul_le_mul_of_nonneg_right (le_abs_self A_pt) (Real.sqrt_nonneg x)).trans
        (le_mul_of_one_le_right (by positivity) h1_sq))
  by_cases hx16 : 16 ≤ x
  · have hpsi := hK₀ x hx16
    have hsq_le : (Real.log x) ^ 2 ≤ (1 + Real.log x) ^ 2 := by nlinarith
    have hpsi' : |Chebyshev.psi x - x - quartetWaveModel ρ₀ (quartetCopyMult ρ₀ : ℝ) x| ≤
        |K₀| * Real.sqrt x * (1 + Real.log x) ^ 2 := by
      rw [quartetWaveModel, sub_neg_eq_add]
      refine hpsi.trans ?_
      exact (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_abs_self K₀) (Real.sqrt_nonneg x)) (sq_nonneg _)).trans
        (mul_le_mul_of_nonneg_left hsq_le (by positivity))
    have htri := abs_sub (Chebyshev.psi x - x - quartetWaveModel ρ₀ (quartetCopyMult ρ₀ : ℝ) x)
      (Chebyshev.psi x - Chebyshev.theta x)
    rw [show (Chebyshev.psi x - x - quartetWaveModel ρ₀ (quartetCopyMult ρ₀ : ℝ) x) -
        (Chebyshev.psi x - Chebyshev.theta x) =
        Chebyshev.theta x - x - quartetWaveModel ρ₀ (quartetCopyMult ρ₀ : ℝ) x by ring] at htri
    have hextra : 0 ≤ (M₁₆ + 16 * D_w) * Real.sqrt x * (1 + Real.log x) ^ 2 := by
      dsimp [D_w]; positivity
    linarith only [htri, hpsi', hpt, hextra]
  · push Not at hx16
    have h5 : |Chebyshev.psi x - x| ≤ M₁₆ := by
      have hnn := Chebyshev.psi_nonneg x
      have hmo := Chebyshev.psi_mono hx16.le
      dsimp [M₁₆]
      rw [abs_le]
      constructor <;> linarith only [hnn, hmo, hx, hx16]
    have hw_le : |quartetWaveModel ρ₀ (quartetCopyMult ρ₀ : ℝ) x| ≤ 16 * D_w := by
      rw [quartetWaveModel, abs_neg, abs_mul, abs_of_nonneg (by positivity)]
      have h1 := (Complex.abs_re_le_norm ((x : ℂ) ^ ρ₀ / ρ₀)).trans_eq (norm_div _ _)
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hx0] at h1
      have hrp : x ^ ρ₀.re ≤ 16 :=
        (Real.rpow_le_rpow_of_exponent_le hx hq.re_lt_one.le).trans
          (by rw [Real.rpow_one]; exact hx16.le)
      calc 2 * (quartetCopyMult ρ₀ : ℝ) * |((x : ℂ) ^ ρ₀ / ρ₀).re|
          ≤ 2 * (quartetCopyMult ρ₀ : ℝ) * (16 / ‖ρ₀‖) :=
            mul_le_mul_of_nonneg_left (h1.trans (div_le_div_of_nonneg_right hrp (norm_nonneg _)))
              (by positivity)
        _ = 16 * D_w := by dsimp [D_w]; ring
    have hpsi_low : |Chebyshev.psi x - x - quartetWaveModel ρ₀ (quartetCopyMult ρ₀ : ℝ) x| ≤
        M₁₆ + 16 * D_w :=
      (abs_sub _ _).trans (by linarith only [h5, hw_le])
    have hprod1 : 1 ≤ Real.sqrt x * (1 + Real.log x) ^ 2 :=
      one_le_mul_of_one_le_of_one_le hsq1 h1_sq
    have hlow_scaled : M₁₆ + 16 * D_w ≤ (M₁₆ + 16 * D_w) * (Real.sqrt x * (1 + Real.log x) ^ 2) :=
      le_mul_of_one_le_right (by dsimp [D_w]; positivity) hprod1
    have htri := abs_sub (Chebyshev.psi x - x - quartetWaveModel ρ₀ (quartetCopyMult ρ₀ : ℝ) x)
      (Chebyshev.psi x - Chebyshev.theta x)
    rw [show (Chebyshev.psi x - x - quartetWaveModel ρ₀ (quartetCopyMult ρ₀ : ℝ) x) -
        (Chebyshev.psi x - Chebyshev.theta x) =
        Chebyshev.theta x - x - quartetWaveModel ρ₀ (quartetCopyMult ρ₀ : ℝ) x by ring] at htri
    have hextra : 0 ≤ |K₀| * Real.sqrt x * (1 + Real.log x) ^ 2 := by positivity
    nlinarith only [htri, hpsi_low, hlow_scaled, hpt, hextra]

/-- **Signed remainder cancellation in the reflected composite factorization at an actual quartet.**
Under `HasSingleOffLineQuartet ρ₀`, although the triangle inequality over `v ≤ 2√n` would give only
`O(n^{3/4} log² n)`, the signed cofactor sum of `θ(x) - x - quartetWaveModel ρ₀ m x` cancels down
to `O(√n ((log n)² + squarefreeDivisorMass n))` across all `n ≥ 2`. -/
theorem singleQuartet_reflectedComposite_remainder_cancellation {ρ₀ : ℂ}
    (hq : HasSingleOffLineQuartet ρ₀) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 2 ≤ n →
      |clippedCofactorOp n ⌊2 * Real.sqrt n⌋₊
          (fun x => Chebyshev.theta x - x - quartetWaveModel ρ₀ (quartetCopyMult ρ₀ : ℝ) x)| ≤
        C * Real.sqrt n * ((Real.log n) ^ 2 + squarefreeDivisorMass n) := by
  set m : ℝ := (quartetCopyMult ρ₀ : ℝ)
  have hm_ne : m ≠ 0 := by dsimp [m]; exact_mod_cast hq.quartetCopyMult_pos.ne'
  obtain ⟨C_w, hC_w⟩ := (reflectedComposite_wave_compatible_iff_zeta_zero hq.1 hq.re_lt_one
    hq.im_ne_zero hm_ne).mpr hq.2.1.1
  obtain ⟨A_pt, hA_pt⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  obtain ⟨K_θ, hK_θ, hmode⟩ := singleQuartet_theta_mode_all hq
  -- Note `1 + log(4 n) ≤ 6 * log n` for `n ≥ 2` since `log 2 ≥ 1/2`
  set C_all : ℝ := |C_w| + 15 + 2 * |A_pt| + 288 * K_θ
  refine ⟨C_all, by dsimp [C_all]; positivity, fun n hn => ?_⟩
  have hn1 : 1 < n := by omega
  have hnR2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hsq1 : 1 ≤ Real.sqrt n := Real.one_le_sqrt.mpr (by linarith)
  set P := ⌊2 * Real.sqrt n⌋₊
  obtain ⟨_, hP2, _, hhi⟩ := floor_two_sqrt_bounds (n := n) (by omega)
  let E_rem (x : ℝ) : ℝ := Chebyshev.theta x - x - quartetWaveModel ρ₀ m x
  have hlin_op : clippedCofactorOp n P E_rem =
      largePrimeCofactorPrice n P -
        clippedCofactorOp n P (fun x => x + quartetWaveModel ρ₀ m x) := by
    rw [largePrimeCofactorPrice_eq_clippedCofactorOp (by omega) le_rfl,
      ← clippedCofactorSliceOp_sub]
    unfold clippedCofactorOp clippedCofactorSliceOp
    refine Finset.sum_congr rfl fun _ _ => by dsimp [E_rem]; ring
  have hmid_eq : primeMidpointPrice n -
      midpointSecondDiff n (fun x => x + quartetWaveModel ρ₀ m x) =
      midpointSecondDiff n E_rem := by
    rw [prime_midpoint_price_eq]
    unfold midpointSecondDiff; dsimp [E_rem]; push_cast; ring
  have hcent := large_prime_cofactor_centering hn1 hP2
  have hcent_cost :
      7 * (P : ℝ) + (Chebyshev.psi (4 * n : ℕ) - Chebyshev.theta (4 * n : ℕ)) + 1 ≤
        (15 + 2 * |A_pt|) * Real.sqrt n := by
    have hsq4 : Real.sqrt (4 * n : ℕ) = 2 * Real.sqrt n := by
      rw [Nat.cast_mul, Nat.cast_ofNat, Real.sqrt_mul (by norm_num),
        show Real.sqrt 4 = 2 by norm_num]
    have hpt : Chebyshev.psi (4 * n : ℕ) - Chebyshev.theta (4 * n : ℕ) ≤
        2 * |A_pt| * Real.sqrt n :=
      (hA_pt (4 * n : ℕ)).trans
        ((mul_le_mul_of_nonneg_right (le_abs_self A_pt) (Real.sqrt_nonneg _)).trans_eq
          (by rw [hsq4]; ring))
    linarith only [hhi, hsq1, hpt]
  have hcent' : |largePrimeCofactorPrice n P - reflectedDensity * (n.totient : ℝ) -
      primeMidpointPrice n| ≤
      (15 + 2 * |A_pt|) * Real.sqrt n * squarefreeDivisorMass n :=
    hcent.trans ((mul_le_mul_of_nonneg_right hcent_cost
      (sum_nonneg fun _ _ => abs_nonneg _)).trans_eq (by unfold squarefreeDivisorMass; ring))
  have hw_b : |clippedCofactorOp n P (fun x => x + quartetWaveModel ρ₀ m x) -
      reflectedDensity * (n.totient : ℝ) -
      midpointSecondDiff n (fun x => x + quartetWaveModel ρ₀ m x)| ≤
      |C_w| * Real.sqrt n * squarefreeDivisorMass n :=
    (hC_w n hn).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_abs_self C_w) (Real.sqrt_nonneg n))
      (sum_nonneg fun _ _ => abs_nonneg _))
  -- Bound `|midpointSecondDiff n E_rem|`
  have hlog2_lo : (1 / 2 : ℝ) ≤ Real.log n := by
    have hl2 : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
    exact hl2.trans (Real.log_le_log (by norm_num) hnR2)
  have hmid_b : |midpointSecondDiff n E_rem| ≤ 288 * K_θ * Real.sqrt n * (Real.log n) ^ 2 := by
    have hk_b (k : ℕ) (hk1 : 1 ≤ k) (hk4 : k ≤ 4) :
        |E_rem (k * n : ℕ)| ≤ 72 * K_θ * Real.sqrt n * (Real.log n) ^ 2 := by
      have hkn1 : (1 : ℝ) ≤ (k * n : ℕ) := by exact_mod_cast Nat.mul_pos hk1 (by omega)
      have hb := hmode (k * n : ℕ) hkn1
      have hsq_kn : Real.sqrt (k * n : ℕ) ≤ 2 * Real.sqrt n := by
        have hle : ((k * n : ℕ) : ℝ) ≤ 4 * (n : ℝ) := by
          push_cast; exact mul_le_mul_of_nonneg_right (by exact_mod_cast hk4) (by positivity)
        exact (Real.sqrt_le_sqrt hle).trans_eq
          (by rw [Real.sqrt_mul (by norm_num), show Real.sqrt 4 = 2 by norm_num])
      have hlg_kn : 1 + Real.log (k * n : ℕ) ≤ 6 * Real.log n := by
        have hle : ((k * n : ℕ) : ℝ) ≤ (n : ℝ) ^ 3 := by
          have : (k : ℝ) ≤ (n : ℝ) ^ 2 := by
            have hkR : (k : ℝ) ≤ 4 := by exact_mod_cast hk4
            nlinarith only [hkR, hnR2]
          push_cast; nlinarith only [this, hnR2]
        have hl1 := Real.log_le_log (by positivity) hle
        rw [Real.log_pow] at hl1
        simp only [Nat.cast_ofNat] at hl1
        linarith only [hl1, hlog2_lo]
      have hsq_lg : (1 + Real.log (k * n : ℕ)) ^ 2 ≤ 36 * (Real.log n) ^ 2 := by
        have := pow_le_pow_left₀ (by linarith [Real.log_nonneg hkn1]) hlg_kn 2
        linarith only [this]
      calc |E_rem (k * n : ℕ)|
          ≤ K_θ * Real.sqrt (k * n : ℕ) * (1 + Real.log (k * n : ℕ)) ^ 2 := hb
        _ ≤ K_θ * (2 * Real.sqrt n) * (36 * (Real.log n) ^ 2) :=
            mul_le_mul (mul_le_mul_of_nonneg_left hsq_kn hK_θ) hsq_lg (sq_nonneg _)
              (by positivity)
        _ = 72 * K_θ * Real.sqrt n * (Real.log n) ^ 2 := by ring
    unfold midpointSecondDiff
    obtain ⟨l2, u2⟩ := abs_le.mp (hk_b 2 (by decide) (by decide))
    obtain ⟨l3, u3⟩ := abs_le.mp (hk_b 3 (by decide) (by decide))
    obtain ⟨l4, u4⟩ := abs_le.mp (hk_b 4 (by decide) (by decide))
    rw [abs_le]; constructor <;> linarith only [l2, u2, l3, u3, l4, u4]
  rw [hlin_op]
  set A₁ := largePrimeCofactorPrice n P - reflectedDensity * (n.totient : ℝ) - primeMidpointPrice n
  set A₂ := clippedCofactorOp n P (fun x => x + quartetWaveModel ρ₀ m x) -
    reflectedDensity * (n.totient : ℝ) -
    midpointSecondDiff n (fun x => x + quartetWaveModel ρ₀ m x)
  have hid_tot :
      largePrimeCofactorPrice n P -
          clippedCofactorOp n P (fun x => x + quartetWaveModel ρ₀ m x) =
        A₁ - A₂ + midpointSecondDiff n E_rem := by
    dsimp [A₁, A₂]; linear_combination hmid_eq
  rw [hid_tot]
  have htri := (abs_add_le (A₁ - A₂) (midpointSecondDiff n E_rem)).trans
    (add_le_add (abs_sub A₁ A₂) le_rfl)
  have hextra1 : 0 ≤ (|C_w| + 15 + 2 * |A_pt|) * Real.sqrt n * (Real.log n) ^ 2 := by positivity
  have hextra2 : 0 ≤ 288 * K_θ * Real.sqrt n * squarefreeDivisorMass n := by
    have : 0 ≤ squarefreeDivisorMass n := sum_nonneg fun _ _ => abs_nonneg _
    positivity
  rw [show C_all = |C_w| + 15 + 2 * |A_pt| + 288 * K_θ from rfl]
  linarith only [htri, hcent', hw_b, hmid_b, hextra1, hextra2]

/-- **Single-cell prime-cofactor wave transmission under `HasSingleOffLineQuartet`.**
For every fixed cofactor `v₀ ≥ 2` and `n ≥ 2 * v₀`, the single cell `(4n/v₀, 3n/v₀, 2n/v₀)`
transmits `+2 m Re((midpointMultiplier ρ₀ / ρ₀) v₀^{-ρ₀} n^{ρ₀})` up to `O(√(n/v₀) (1 + log n)²)`. -/
theorem singleQuartet_individual_cofactor_cell {ρ₀ : ℂ} (hq : HasSingleOffLineQuartet ρ₀)
    {v₀ : ℕ} (hv₀ : 2 ≤ v₀) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 2 * v₀ ≤ n →
      |(Chebyshev.theta (4 * n / v₀ : ℕ) - 2 * Chebyshev.theta (3 * n / v₀ : ℕ) +
            Chebyshev.theta (2 * n / v₀ : ℕ)) -
          2 * (quartetCopyMult ρ₀ : ℝ) *
            ((midpointMultiplier ρ₀ / ρ₀) * ((v₀ : ℝ) : ℂ) ^ (-ρ₀) * ((n : ℝ) : ℂ) ^ ρ₀).re| ≤
        C * Real.sqrt ((n : ℝ) / v₀) * (1 + Real.log n) ^ 2 := by
  obtain ⟨K_θ, hK_θ, hmode⟩ := singleQuartet_theta_mode_all hq
  set m : ℝ := (quartetCopyMult ρ₀ : ℝ)
  have hv0_pos : 0 < v₀ := by omega
  have hv0R : (0 : ℝ) < v₀ := by exact_mod_cast hv0_pos
  have hρ0 : 0 < ρ₀.re := by linarith [hq.1]
  have hρ_ne : ρ₀ ≠ 0 := fun he => by rw [he, Complex.zero_re] at hρ0; exact lt_irrefl 0 hρ0
  refine ⟨32 * K_θ + 8 * m + 1, by dsimp [m]; positivity, fun n hn => ?_⟩
  have hn0 : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  have hnR1 : (1 : ℝ) ≤ n := by exact_mod_cast hn0
  have hnv1 : 1 ≤ (n : ℝ) / v₀ := by
    rw [le_div_iff₀ hv0R]
    have : (2 * v₀ : ℝ) ≤ n := by exact_mod_cast hn
    linarith only [this, hv0R]
  have hsq_nv1 : 1 ≤ Real.sqrt ((n : ℝ) / v₀) := Real.one_le_sqrt.mpr hnv1
  have h1_lg : 1 ≤ (1 + Real.log n) ^ 2 := by nlinarith [Real.log_nonneg hnR1]
  have hprod1 : 1 ≤ Real.sqrt ((n : ℝ) / v₀) * (1 + Real.log n) ^ 2 :=
    one_le_mul_of_one_le_of_one_le hsq_nv1 h1_lg
  let E_rem (x : ℝ) : ℝ := Chebyshev.theta x - x - quartetWaveModel ρ₀ m x
  have hθ_expand (k : ℕ) : Chebyshev.theta (k * n / v₀ : ℕ) =
      ((k * n / v₀ : ℕ) : ℝ) + quartetWaveModel ρ₀ m (k * n / v₀ : ℕ) + E_rem (k * n / v₀ : ℕ) := by
    dsimp [E_rem]; ring
  have hlin_b : |((4 * n / v₀ : ℕ) : ℝ) - 2 * ((3 * n / v₀ : ℕ) : ℝ) + ((2 * n / v₀ : ℕ) : ℝ)| ≤ 1 :=
    abs_midpoint_division_le_one hv0_pos n
  have hw_round (k : ℕ) (hk2 : 2 ≤ k) :
      |quartetWaveModel ρ₀ m (k * n / v₀ : ℕ) -
          quartetWaveModel ρ₀ m (((k * n : ℕ) : ℝ) / v₀)| ≤ 2 * m := by
    have hq1 : 1 ≤ k * n / v₀ :=
      (Nat.le_div_iff_mul_le hv0_pos).mpr (by nlinarith only [hn, hk2])
    set x₁ : ℝ := ((k * n / v₀ : ℕ) : ℝ)
    set x₂ : ℝ := ((k * n : ℕ) : ℝ) / v₀
    have hx₁_1 : 1 ≤ x₁ := by dsimp [x₁]; exact_mod_cast hq1
    have hx₁_pos : 0 < x₁ := by linarith
    have hx₁₂ : x₁ ≤ x₂ := Nat.cast_div_le
    have hdiff1 : x₂ - x₁ ≤ 1 := by
      have := (abs_le.mp (_root_.RHTower.Sieve.abs_natDiv_sub_div_le (N := k * n) hv0_pos)).1
      dsimp [x₁, x₂]; linarith
    unfold quartetWaveModel
    rw [show -(2 * m * ((x₁ : ℂ) ^ ρ₀ / ρ₀).re) - -(2 * m * ((x₂ : ℂ) ^ ρ₀ / ρ₀).re) =
        2 * m * (((x₂ : ℂ) ^ ρ₀ - (x₁ : ℂ) ^ ρ₀) / ρ₀).re by
          rw [sub_div, Complex.sub_re]; ring,
      abs_mul, abs_of_nonneg (by dsimp [m]; positivity)]
    refine mul_le_of_le_one_right (by dsimp [m]; positivity) ?_
    refine ((Complex.abs_re_le_norm _).trans_eq (norm_div _ _)).trans ?_
    rw [div_le_one (norm_pos_iff.mpr hρ_ne)]
    have hmvt := _root_.RHTower.norm_ofReal_cpow_sub_cpow_le hx₁_pos hx₁₂ hρ0 hq.re_lt_one.le
    have hrp1 : x₁ ^ (ρ₀.re - 1) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hx₁_1 (by linarith [hq.re_lt_one])
    calc ‖(x₂ : ℂ) ^ ρ₀ - (x₁ : ℂ) ^ ρ₀‖
        ≤ ‖ρ₀‖ * (x₂ - x₁) * x₁ ^ (ρ₀.re - 1) := hmvt
      _ ≤ (‖ρ₀‖ * 1) * 1 :=
          mul_le_mul (mul_le_mul_of_nonneg_left hdiff1 (norm_nonneg _)) hrp1
            (Real.rpow_nonneg hx₁_pos.le _) (by positivity)
      _ = ‖ρ₀‖ := by ring
  have hw_exact :
      quartetWaveModel ρ₀ m (((4 * n : ℕ) : ℝ) / v₀) -
        2 * quartetWaveModel ρ₀ m (((3 * n : ℕ) : ℝ) / v₀) +
        quartetWaveModel ρ₀ m (((2 * n : ℕ) : ℝ) / v₀) =
        2 * m * ((midpointMultiplier ρ₀ / ρ₀) * ((v₀ : ℝ) : ℂ) ^ (-ρ₀) * ((n : ℝ) : ℂ) ^ ρ₀).re := by
    have hkc (k : ℕ) (hk : 0 < k) :
        ((((k * n : ℕ) : ℝ) / v₀ : ℝ) : ℂ) ^ ρ₀ =
          ((k : ℝ) : ℂ) ^ ρ₀ * ((v₀ : ℝ) : ℂ) ^ (-ρ₀) * ((n : ℝ) : ℂ) ^ ρ₀ := by
      have hkR : (0 : ℝ) < k := by exact_mod_cast hk
      have hknR : (0 : ℝ) < (k * n : ℕ) := by exact_mod_cast Nat.mul_pos hk hn0
      rw [cpow_pos_div hknR hv0R ρ₀, show ((k * n : ℕ) : ℝ) = (k : ℝ) * (n : ℝ) by push_cast; rfl,
        cpow_pos_mul hkR hnR ρ₀, Complex.cpow_neg, div_eq_mul_inv]
      ring
    unfold quartetWaveModel
    have hid : ((((4 * n : ℕ) : ℝ) / v₀ : ℝ) : ℂ) ^ ρ₀ / ρ₀ -
        ((2 : ℝ) : ℂ) * (((((3 * n : ℕ) : ℝ) / v₀ : ℝ) : ℂ) ^ ρ₀ / ρ₀) +
        ((((2 * n : ℕ) : ℝ) / v₀ : ℝ) : ℂ) ^ ρ₀ / ρ₀ =
        -((midpointMultiplier ρ₀ / ρ₀) * ((v₀ : ℝ) : ℂ) ^ (-ρ₀) * ((n : ℝ) : ℂ) ^ ρ₀) := by
      rw [hkc 4 (by decide), hkc 3 (by decide), hkc 2 (by decide), midpointMultiplier]
      simp only [Nat.cast_ofNat, Complex.ofReal_ofNat]
      ring
    have hre := congrArg Complex.re hid
    simp only [Complex.sub_re, Complex.add_re, Complex.neg_re, Complex.re_ofReal_mul] at hre
    linarith only [congrArg (fun u => -(2 * m * u)) hre]
  have hrem_k (k : ℕ) (hk2 : 2 ≤ k) (hk4 : k ≤ 4) :
      |E_rem (k * n / v₀ : ℕ)| ≤ 8 * K_θ * Real.sqrt ((n : ℝ) / v₀) * (1 + Real.log n) ^ 2 := by
    have hq1 : 1 ≤ k * n / v₀ :=
      (Nat.le_div_iff_mul_le hv0_pos).mpr (by nlinarith only [hn, hk2])
    have hqR1 : (1 : ℝ) ≤ (k * n / v₀ : ℕ) := by exact_mod_cast hq1
    have hq_le_4 : ((k * n / v₀ : ℕ) : ℝ) ≤ 4 * ((n : ℝ) / v₀) := by
      refine Nat.cast_div_le.trans ?_
      push_cast
      calc ((k : ℝ) * (n : ℝ)) / v₀ ≤ (4 * (n : ℝ)) / v₀ :=
            div_le_div_of_nonneg_right
              (mul_le_mul_of_nonneg_right (by exact_mod_cast hk4) hnR.le) hv0R.le
        _ = 4 * ((n : ℝ) / v₀) := by ring
    have hq_le_2n : ((k * n / v₀ : ℕ) : ℝ) ≤ 2 * (n : ℝ) := by
      have h4_2 : 4 * ((n : ℝ) / v₀) ≤ 2 * (n : ℝ) := by
        rw [mul_div_assoc', div_le_iff₀ hv0R]
        have hv2 : (2 : ℝ) ≤ v₀ := by exact_mod_cast hv₀
        nlinarith only [hv2, hnR]
      exact hq_le_4.trans h4_2
    have hsq_q : Real.sqrt (k * n / v₀ : ℕ) ≤ 2 * Real.sqrt ((n : ℝ) / v₀) :=
      (Real.sqrt_le_sqrt hq_le_4).trans_eq
        (by rw [Real.sqrt_mul (by norm_num), show Real.sqrt 4 = 2 by norm_num])
    have hlg_q : (1 + Real.log (k * n / v₀ : ℕ)) ^ 2 ≤ 4 * (1 + Real.log n) ^ 2 := by
      have hl1 := Real.log_le_log (by positivity) hq_le_2n
      rw [Real.log_mul (by norm_num) hnR.ne'] at hl1
      have hl2 : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
      have hlin_lg : 1 + Real.log (k * n / v₀ : ℕ) ≤ 2 * (1 + Real.log n) := by
        linarith only [hl1, hl2, Real.log_nonneg hnR1]
      exact (pow_le_pow_left₀ (by linarith [Real.log_nonneg hqR1]) hlin_lg 2).trans_eq (by ring)
    calc |E_rem (k * n / v₀ : ℕ)|
        ≤ K_θ * Real.sqrt (k * n / v₀ : ℕ) * (1 + Real.log (k * n / v₀ : ℕ)) ^ 2 :=
          hmode _ hqR1
      _ ≤ K_θ * (2 * Real.sqrt ((n : ℝ) / v₀)) * (4 * (1 + Real.log n) ^ 2) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hsq_q hK_θ) hlg_q (sq_nonneg _) (by positivity)
      _ = 8 * K_θ * Real.sqrt ((n : ℝ) / v₀) * (1 + Real.log n) ^ 2 := by ring
  rw [hθ_expand 4, hθ_expand 3, hθ_expand 2, ← hw_exact]
  obtain ⟨r4l, r4u⟩ := abs_le.mp (hw_round 4 (by decide))
  obtain ⟨r3l, r3u⟩ := abs_le.mp (hw_round 3 (by decide))
  obtain ⟨r2l, r2u⟩ := abs_le.mp (hw_round 2 (by decide))
  obtain ⟨e4l, e4u⟩ := abs_le.mp (hrem_k 4 (by decide) (by decide))
  obtain ⟨e3l, e3u⟩ := abs_le.mp (hrem_k 3 (by decide) (by decide))
  obtain ⟨e2l, e2u⟩ := abs_le.mp (hrem_k 2 (by decide) (by decide))
  obtain ⟨ll, lu⟩ := abs_le.mp hlin_b
  have hconst_scaled : 8 * m + 1 ≤
      (8 * m + 1) * (Real.sqrt ((n : ℝ) / v₀) * (1 + Real.log n) ^ 2) :=
    le_mul_of_one_le_right (by dsimp [m]; positivity) hprod1
  rw [abs_le]
  constructor <;>
    linarith only [r4l, r4u, r3l, r3u, r2l, r2u, e4l, e4u, e3l, e3u, e2l, e2u, ll, lu,
      hconst_scaled]

/-! ### 7. Second-order (log-twisted) wave transmission and multiplicity separation -/

/-- Log-twisted single-mode wave `-2 Re((x^z log x) / z - x^z / z²)` obtained by differentiating
`quartetWaveModel z 1 x` with respect to `z`. -/
def logTwistedWaveModel (z : ℂ) (x : ℝ) : ℝ :=
  -(2 * ((x : ℂ) ^ z * (Real.log x : ℂ) / z - (x : ℂ) ^ z / z ^ 2).re)

private def complexWaveRemainder (n : ℕ) (z : ℂ) : ℂ :=
  clippedCofactorComplexSliceOp n ⌊2 * Real.sqrt n⌋₊ 1 (fun x => (x : ℂ) ^ z / z) -
    midpointComplexSecondDiff n (fun x => (x : ℂ) ^ z / z) +
    riemannZeta z * ((midpointMultiplier z / z) * coprimeEulerFactor n z * ((n : ℝ) : ℂ) ^ z)

private theorem hasDerivAt_pos_cpow_div {a : ℝ} (ha : 0 < a) {z : ℂ} (hz0 : z ≠ 0) :
    HasDerivAt (fun w : ℂ => (a : ℂ) ^ w / w)
      ((a : ℂ) ^ z * (Real.log a : ℂ) / z - (a : ℂ) ^ z / z ^ 2) z := by
  have haC : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha.ne'
  have hc := (hasDerivAt_id z).const_cpow (c := (a : ℂ)) (Or.inl haC)
  rw [← Complex.ofReal_log ha.le, mul_one] at hc
  refine (hc.div (hasDerivAt_id z) hz0).congr_deriv ?_
  dsimp [id]
  field_simp [hz0]

private theorem differentiableAt_complexWaveRemainder {n : ℕ} (hn : 1 ≤ n) {z : ℂ}
    (hz0 : z ≠ 0) (hz1 : z ≠ 1) :
    DifferentiableAt ℂ (complexWaveRemainder n) z := by
  unfold complexWaveRemainder clippedCofactorComplexSliceOp midpointComplexSecondDiff
  obtain ⟨hP1, _, _, _⟩ := floor_two_sqrt_bounds hn
  have hd_g (m : ℕ) (hm : 1 ≤ m) : DifferentiableAt ℂ (fun w : ℂ => ((m : ℝ) : ℂ) ^ w / w) z :=
    (hasDerivAt_pos_cpow_div (by exact_mod_cast hm) hz0).differentiableAt
  have hd_clip : DifferentiableAt ℂ
      (fun w : ℂ => ∑ v ∈ (Icc 2 (4 * n)).filter (fun v => n.Coprime v ∧ 1 ∣ v),
        ((((max ⌊2 * Real.sqrt n⌋₊ (4 * n / v) : ℕ) : ℝ) : ℂ) ^ w / w -
          2 * ((((max ⌊2 * Real.sqrt n⌋₊ (3 * n / v) : ℕ) : ℝ) : ℂ) ^ w / w) +
          ((((max ⌊2 * Real.sqrt n⌋₊ (2 * n / v) : ℕ) : ℝ) : ℂ) ^ w / w))) z := by
    refine DifferentiableAt.fun_sum fun v _ => ?_
    exact ((hd_g _ (hP1.trans (le_max_left _ _))).sub
      ((hd_g _ (hP1.trans (le_max_left _ _))).const_mul 2)).add
      (hd_g _ (hP1.trans (le_max_left _ _)))
  have hd_mid : DifferentiableAt ℂ
      (fun w : ℂ => 2 * ((((3 * n : ℕ) : ℝ) : ℂ) ^ w / w) -
        ((((2 * n : ℕ) : ℝ) : ℂ) ^ w / w) -
        ((((4 * n : ℕ) : ℝ) : ℂ) ^ w / w)) z :=
    (((hd_g (3 * n) (by omega)).const_mul 2).sub (hd_g (2 * n) (by omega))).sub
      (hd_g (4 * n) (by omega))
  have hd_mult : DifferentiableAt ℂ midpointMultiplier z := by
    unfold midpointMultiplier
    exact (((differentiableAt_id.const_cpow (Or.inl (by norm_num : (3 : ℂ) ≠ 0))).const_mul 2).sub
      (differentiableAt_id.const_cpow (Or.inl (by norm_num : (2 : ℂ) ≠ 0)))).sub
      (differentiableAt_id.const_cpow (Or.inl (by norm_num : (4 : ℂ) ≠ 0)))
  have hd_eul : DifferentiableAt ℂ (coprimeEulerFactor n) z := by
    unfold coprimeEulerFactor
    refine DifferentiableAt.fun_sum fun d hd => ?_
    have hdR : ((d : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (Nat.pos_of_mem_divisors hd).ne'
    exact (differentiableAt_id.neg.const_cpow (Or.inl hdR)).const_mul (μ d : ℂ)
  have hd_npow : DifferentiableAt ℂ (fun w : ℂ => ((n : ℝ) : ℂ) ^ w) z :=
    differentiableAt_id.const_cpow (Or.inl (by exact_mod_cast (by omega : n ≠ 0)))
  have hd_prod : DifferentiableAt ℂ
      (fun w : ℂ => riemannZeta w * ((midpointMultiplier w / w) * coprimeEulerFactor n w *
        ((n : ℝ) : ℂ) ^ w)) z :=
    (differentiableAt_riemannZeta hz1).mul
      (((hd_mult.div differentiableAt_id hz0).mul hd_eul).mul hd_npow)
  exact (hd_clip.sub hd_mid).add hd_prod

private theorem deriv_complexWaveRemainder_at_zero {n : ℕ} (hn : 1 ≤ n) {ρ₀ : ℂ}
    (h0 : ρ₀ ≠ 0) (h1 : ρ₀ ≠ 1) (hζ : riemannZeta ρ₀ = 0) :
    deriv (complexWaveRemainder n) ρ₀ =
      clippedCofactorComplexSliceOp n ⌊2 * Real.sqrt n⌋₊ 1
          (fun x => (x : ℂ) ^ ρ₀ * (Real.log x : ℂ) / ρ₀ - (x : ℂ) ^ ρ₀ / ρ₀ ^ 2) -
        midpointComplexSecondDiff n
          (fun x => (x : ℂ) ^ ρ₀ * (Real.log x : ℂ) / ρ₀ - (x : ℂ) ^ ρ₀ / ρ₀ ^ 2) +
        deriv riemannZeta ρ₀ *
          ((midpointMultiplier ρ₀ / ρ₀) * coprimeEulerFactor n ρ₀ * ((n : ℝ) : ℂ) ^ ρ₀) := by
  obtain ⟨hP1, _, _, _⟩ := floor_two_sqrt_bounds hn
  let dg (x : ℝ) : ℂ := (x : ℂ) ^ ρ₀ * (Real.log x : ℂ) / ρ₀ - (x : ℂ) ^ ρ₀ / ρ₀ ^ 2
  have h1_der : HasDerivAt
      (fun w : ℂ => clippedCofactorComplexSliceOp n ⌊2 * Real.sqrt n⌋₊ 1 (fun x => (x : ℂ) ^ w / w))
      (clippedCofactorComplexSliceOp n ⌊2 * Real.sqrt n⌋₊ 1 dg) ρ₀ := by
    unfold clippedCofactorComplexSliceOp
    refine HasDerivAt.fun_sum fun v _ => ?_
    have hd4 := hasDerivAt_pos_cpow_div
      (a := ((max ⌊2 * Real.sqrt n⌋₊ (4 * n / v) : ℕ) : ℝ))
      (by exact_mod_cast hP1.trans (le_max_left _ _)) h0
    have hd3 := hasDerivAt_pos_cpow_div
      (a := ((max ⌊2 * Real.sqrt n⌋₊ (3 * n / v) : ℕ) : ℝ))
      (by exact_mod_cast hP1.trans (le_max_left _ _)) h0
    have hd2 := hasDerivAt_pos_cpow_div
      (a := ((max ⌊2 * Real.sqrt n⌋₊ (2 * n / v) : ℕ) : ℝ))
      (by exact_mod_cast hP1.trans (le_max_left _ _)) h0
    exact (hd4.sub (hd3.const_mul 2)).add hd2
  have h2_der : HasDerivAt
      (fun w : ℂ => midpointComplexSecondDiff n (fun x => (x : ℂ) ^ w / w))
      (midpointComplexSecondDiff n dg) ρ₀ := by
    unfold midpointComplexSecondDiff
    have hm3 := hasDerivAt_pos_cpow_div (a := ((3 * n : ℕ) : ℝ)) (by exact_mod_cast (by omega : 0 < 3 * n)) h0
    have hm2 := hasDerivAt_pos_cpow_div (a := ((2 * n : ℕ) : ℝ)) (by exact_mod_cast (by omega : 0 < 2 * n)) h0
    have hm4 := hasDerivAt_pos_cpow_div (a := ((4 * n : ℕ) : ℝ)) (by exact_mod_cast (by omega : 0 < 4 * n)) h0
    exact ((hm3.const_mul 2).sub hm2).sub hm4
  let Hn (w : ℂ) : ℂ := (midpointMultiplier w / w) * coprimeEulerFactor n w * ((n : ℝ) : ℂ) ^ w
  have hd_Hn : DifferentiableAt ℂ Hn ρ₀ := by
    dsimp [Hn]
    have hd_mult : DifferentiableAt ℂ midpointMultiplier ρ₀ := by
      unfold midpointMultiplier
      exact (((differentiableAt_id.const_cpow (Or.inl (by norm_num : (3 : ℂ) ≠ 0))).const_mul 2).sub
        (differentiableAt_id.const_cpow (Or.inl (by norm_num : (2 : ℂ) ≠ 0)))).sub
        (differentiableAt_id.const_cpow (Or.inl (by norm_num : (4 : ℂ) ≠ 0)))
    have hd_eul : DifferentiableAt ℂ (coprimeEulerFactor n) ρ₀ := by
      unfold coprimeEulerFactor
      refine DifferentiableAt.fun_sum fun d hd => ?_
      have hdR : ((d : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (Nat.pos_of_mem_divisors hd).ne'
      exact (differentiableAt_id.neg.const_cpow (Or.inl hdR)).const_mul (μ d : ℂ)
    have hd_npow : DifferentiableAt ℂ (fun w : ℂ => ((n : ℝ) : ℂ) ^ w) ρ₀ :=
      differentiableAt_id.const_cpow (Or.inl (by exact_mod_cast (by omega : n ≠ 0)))
    exact ((hd_mult.div differentiableAt_id h0).mul hd_eul).mul hd_npow
  have h3_der : HasDerivAt (fun w : ℂ => riemannZeta w * Hn w)
      (deriv riemannZeta ρ₀ * Hn ρ₀) ρ₀ := by
    have hm := (differentiableAt_riemannZeta h1).hasDerivAt.mul hd_Hn.hasDerivAt
    rw [hζ, zero_mul, add_zero] at hm
    exact hm
  exact ((h1_der.sub h2_der).add h3_der).deriv

/-- **Second-order (log-twisted) reflected-composite wave transmission at a strip zero `ζ(ρ₀) = 0`.**
Differentiating the reflected-composite remainder on a disc around `ρ₀` (`1/2 < Re ρ₀ < 1`,
`ζ(ρ₀) = 0`) proves that `logTwistedWaveModel ρ₀` has reflected-composite defect
`+2 Re((midpointMultiplier ρ₀ / ρ₀) ζ'(ρ₀) coprimeEulerFactor n ρ₀ n^{ρ₀})` up to a strictly
sub-square-root remainder `O_{ρ₀}(n^{(1 + Re ρ₀)/4} squarefreeDivisorMass n)`. -/
theorem clippedCofactorOp_logTwistedWave_at_zero {ρ₀ : ℂ} (hhalf : 1 / 2 < ρ₀.re)
    (h1 : ρ₀.re < 1) (hζ : riemannZeta ρ₀ = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 2 ≤ n →
      |clippedCofactorOp n ⌊2 * Real.sqrt n⌋₊ (logTwistedWaveModel ρ₀) -
          midpointSecondDiff n (logTwistedWaveModel ρ₀) -
          2 * ((midpointMultiplier ρ₀ / ρ₀) * deriv riemannZeta ρ₀ * coprimeEulerFactor n ρ₀ *
            ((n : ℝ) : ℂ) ^ ρ₀).re| ≤
        C * (n : ℝ) ^ ((1 + ρ₀.re) / 4) * squarefreeDivisorMass n := by
  set r : ℝ := (1 - ρ₀.re) / 2
  have hr_pos : 0 < r := by dsimp [r]; linarith
  -- Uniform bound on `waveTransmissionRate z` over `closedBall ρ₀ r`
  set M_rate : ℝ :=
    4 * (12 * (3 + 2 / r + 12 * (‖ρ₀‖ + r)) + 4) + 12
  have hM_rate_nn : 0 ≤ M_rate := by dsimp [M_rate]; positivity
  have hball_bounds {z : ℂ} (hz : z ∈ closedBall ρ₀ r) :
      1 / 4 < z.re ∧ z.re ≤ (1 + ρ₀.re) / 2 ∧ z.re < 1 ∧
        waveTransmissionRate z ≤ M_rate := by
    rw [mem_closedBall, dist_eq_norm] at hz
    have hre_diff := abs_le.mp ((Complex.abs_re_le_norm (z - ρ₀)).trans hz)
    rw [Complex.sub_re] at hre_diff
    have hz_lo : 1 / 4 < z.re := by dsimp [r] at hre_diff; linarith
    have hz_mid : z.re ≤ (1 + ρ₀.re) / 2 := by dsimp [r] at hre_diff; linarith
    have hz_hi : z.re < 1 := by linarith
    have h1z_ge : r ≤ ‖1 - z‖ := by
      have hre1 : r ≤ (1 - z).re := by
        rw [Complex.sub_re, Complex.one_re]; dsimp [r]; linarith
      exact hre1.trans (Complex.re_le_norm (1 - z))
    have hz_ge : 1 / 4 ≤ ‖z‖ := hz_lo.le.trans (Complex.re_le_norm z)
    have hz_le : ‖z‖ ≤ ‖ρ₀‖ + r := by
      have ht := norm_add_le (z - ρ₀) ρ₀
      rw [sub_add_cancel] at ht
      linarith only [ht, hz]
    have hinv_1z : 2 / ‖1 - z‖ ≤ 2 / r :=
      div_le_div_of_nonneg_left zero_le_two hr_pos h1z_ge
    have hinv_zre : 3 * ‖z‖ / z.re ≤ 12 * (‖ρ₀‖ + r) := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith only [hz_lo, hz_le, norm_nonneg z]
    have hnum_le : 12 * (3 + 2 / ‖1 - z‖ + 3 * ‖z‖ / z.re) + 4 ≤
        12 * (3 + 2 / r + 12 * (‖ρ₀‖ + r)) + 4 := by
      linarith only [hinv_1z, hinv_zre]
    have hdiv_z : (12 * (3 + 2 / ‖1 - z‖ + 3 * ‖z‖ / z.re) + 4) / ‖z‖ ≤
        4 * (12 * (3 + 2 / r + 12 * (‖ρ₀‖ + r)) + 4) := by
      rw [div_le_iff₀ (by linarith)]
      have hnum_nn : 0 ≤ 12 * (3 + 2 / r + 12 * (‖ρ₀‖ + r)) + 4 := by positivity
      nlinarith only [hnum_le, hz_ge, hnum_nn]
    refine ⟨hz_lo, hz_mid, hz_hi, ?_⟩
    unfold waveTransmissionRate
    dsimp [M_rate]
    linarith only [hdiv_z]
  refine ⟨6 * M_rate / r, by positivity, fun n hn => ?_⟩
  have hn1 : 1 ≤ n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hnR1 : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  obtain ⟨hP1, hP2, _, _⟩ := floor_two_sqrt_bounds hn1
  have hdiffCont : DiffContOnCl ℂ (complexWaveRemainder n) (ball ρ₀ r) := by
    refine DifferentiableOn.diffContOnCl ?_
    rw [closure_ball ρ₀ hr_pos.ne']
    intro z hz
    obtain ⟨hz_lo, _, hz_hi, _⟩ := hball_bounds hz
    have hz0 : z ≠ 0 := fun he => by rw [he, Complex.zero_re] at hz_lo; linarith
    have hz1 : z ≠ 1 := fun he => by rw [he, Complex.one_re] at hz_hi; linarith
    exact (differentiableAt_complexWaveRemainder hn1 hz0 hz1).differentiableWithinAt
  have hsphere : ∀ z ∈ sphere ρ₀ r,
      ‖complexWaveRemainder n z‖ ≤
        3 * M_rate * (n : ℝ) ^ ((1 + ρ₀.re) / 4) * squarefreeDivisorMass n := by
    intro z hz
    obtain ⟨hz_lo, hz_mid, hz_hi, hrate⟩ := hball_bounds (sphere_subset_closedBall hz)
    have hz0 : 0 < z.re := by linarith
    have hmid_eq : midpointComplexSecondDiff n (fun x => (x : ℂ) ^ z / z) =
        (midpointMultiplier z / z) * ((n : ℝ) : ℂ) ^ z := by
      unfold midpointComplexSecondDiff
      have hc (k : ℕ) (hk : 0 < k) : (((k * n : ℕ) : ℝ) : ℂ) ^ z =
          ((k : ℝ) : ℂ) ^ z * ((n : ℝ) : ℂ) ^ z := by
        have hkR : (0 : ℝ) < k := by exact_mod_cast hk
        simpa only [Nat.cast_mul] using cpow_pos_mul hkR hnR z
      dsimp only
      rw [hc 3 (by decide), hc 2 (by decide), hc 4 (by decide), midpointMultiplier]
      simp only [Nat.cast_ofNat, Complex.ofReal_ofNat]
      ring
    have hrem_eq : complexWaveRemainder n z =
        clippedCofactorComplexSliceOp n ⌊2 * Real.sqrt n⌋₊ 1 (fun x => (x : ℂ) ^ z / z) -
          (midpointMultiplier z / z) *
            ((if (1 : ℕ) = 1 then (1 : ℂ) else 0) -
              (((1 : ℕ) : ℝ) : ℂ) ^ (-z) * riemannZeta z * coprimeEulerFactor n z) *
            ((n : ℝ) : ℂ) ^ z := by
      unfold complexWaveRemainder
      rw [hmid_eq, if_pos rfl, Nat.cast_one, Complex.ofReal_one, Complex.one_cpow, one_mul]
      ring
    rw [hrem_eq]
    have hb := clippedCofactorComplexSliceOp_cpow hn1 hP1 hP2 le_rfl (Nat.coprime_one_right n)
      hz0 hz_hi
    have hcut := wave_cut_rpow_le hn1 hz0 hz_hi
    have hexp_le : (n : ℝ) ^ (z.re / 2) ≤ (n : ℝ) ^ ((1 + ρ₀.re) / 4) :=
      Real.rpow_le_rpow_of_exponent_le hnR1 (by linarith only [hz_mid])
    have hmass_nn : 0 ≤ squarefreeDivisorMass n := sum_nonneg fun _ _ => abs_nonneg _
    calc ‖_‖
        ≤ waveTransmissionRate z *
            ((⌊2 * Real.sqrt n⌋₊ : ℝ) ^ z.re +
              (n : ℝ) * (⌊2 * Real.sqrt n⌋₊ : ℝ) ^ (z.re - 2)) *
            squarefreeDivisorMass n := hb
      _ ≤ M_rate * (3 * (n : ℝ) ^ (z.re / 2)) * squarefreeDivisorMass n :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul hrate hcut (by positivity) hM_rate_nn) hmass_nn
      _ ≤ M_rate * (3 * (n : ℝ) ^ ((1 + ρ₀.re) / 4)) * squarefreeDivisorMass n :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hexp_le (by norm_num)) hM_rate_nn) hmass_nn
      _ = 3 * M_rate * (n : ℝ) ^ ((1 + ρ₀.re) / 4) * squarefreeDivisorMass n := by ring
  have hcauchy := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr_pos hdiffCont hsphere
  have hρ0_ne0 : ρ₀ ≠ 0 := fun he => by rw [he, Complex.zero_re] at hhalf; linarith
  have hρ0_ne1 : ρ₀ ≠ 1 := fun he => by rw [he, Complex.one_re] at h1; linarith
  have hder_eq := deriv_complexWaveRemainder_at_zero hn1 hρ0_ne0 hρ0_ne1 hζ
  rw [hder_eq] at hcauchy
  have hre_id :
      clippedCofactorOp n ⌊2 * Real.sqrt n⌋₊ (logTwistedWaveModel ρ₀) -
          midpointSecondDiff n (logTwistedWaveModel ρ₀) -
          2 * ((midpointMultiplier ρ₀ / ρ₀) * deriv riemannZeta ρ₀ * coprimeEulerFactor n ρ₀ *
            ((n : ℝ) : ℂ) ^ ρ₀).re =
        -(2 * (clippedCofactorComplexSliceOp n ⌊2 * Real.sqrt n⌋₊ 1
              (fun x => (x : ℂ) ^ ρ₀ * (Real.log x : ℂ) / ρ₀ - (x : ℂ) ^ ρ₀ / ρ₀ ^ 2) -
            midpointComplexSecondDiff n
              (fun x => (x : ℂ) ^ ρ₀ * (Real.log x : ℂ) / ρ₀ - (x : ℂ) ^ ρ₀ / ρ₀ ^ 2) +
            deriv riemannZeta ρ₀ *
              ((midpointMultiplier ρ₀ / ρ₀) * coprimeEulerFactor n ρ₀ * ((n : ℝ) : ℂ) ^ ρ₀)).re) := by
    let dg (x : ℝ) : ℂ := (x : ℂ) ^ ρ₀ * (Real.log x : ℂ) / ρ₀ - (x : ℂ) ^ ρ₀ / ρ₀ ^ 2
    have h2 (z : ℂ) : (2 * z).re = 2 * z.re := by simp
    have hclip_re : clippedCofactorOp n ⌊2 * Real.sqrt n⌋₊ (logTwistedWaveModel ρ₀) =
        -2 * (clippedCofactorComplexSliceOp n ⌊2 * Real.sqrt n⌋₊ 1 dg).re := by
      unfold clippedCofactorOp clippedCofactorSliceOp clippedCofactorComplexSliceOp logTwistedWaveModel
      rw [Complex.re_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun v _ => ?_
      simp only [dg, Complex.add_re, Complex.sub_re, h2]
      ring
    have hmid_re : midpointSecondDiff n (logTwistedWaveModel ρ₀) =
        -2 * (midpointComplexSecondDiff n dg).re := by
      unfold midpointSecondDiff midpointComplexSecondDiff logTwistedWaveModel
      simp only [dg, Complex.sub_re, h2]
      ring
    have hmul_re : (deriv riemannZeta ρ₀ *
        ((midpointMultiplier ρ₀ / ρ₀) * coprimeEulerFactor n ρ₀ * ((n : ℝ) : ℂ) ^ ρ₀)).re =
        ((midpointMultiplier ρ₀ / ρ₀) * deriv riemannZeta ρ₀ * coprimeEulerFactor n ρ₀ *
          ((n : ℝ) : ℂ) ^ ρ₀).re := by congr 1; ring
    change clippedCofactorOp n ⌊2 * Real.sqrt n⌋₊ (logTwistedWaveModel ρ₀) -
        midpointSecondDiff n (logTwistedWaveModel ρ₀) -
        2 * ((midpointMultiplier ρ₀ / ρ₀) * deriv riemannZeta ρ₀ * coprimeEulerFactor n ρ₀ *
          ((n : ℝ) : ℂ) ^ ρ₀).re =
      -(2 * (clippedCofactorComplexSliceOp n ⌊2 * Real.sqrt n⌋₊ 1 dg -
          midpointComplexSecondDiff n dg +
          deriv riemannZeta ρ₀ *
            ((midpointMultiplier ρ₀ / ρ₀) * coprimeEulerFactor n ρ₀ * ((n : ℝ) : ℂ) ^ ρ₀)).re)
    rw [Complex.add_re, Complex.sub_re, hclip_re, hmid_re, hmul_re]
    ring
  rw [hre_id, abs_neg, abs_mul, abs_of_pos two_pos]
  calc 2 * |_|
      ≤ 2 * ‖_‖ := mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) zero_le_two
    _ ≤ 2 * (3 * M_rate * (n : ℝ) ^ ((1 + ρ₀.re) / 4) * squarefreeDivisorMass n / r) :=
        mul_le_mul_of_nonneg_left hcauchy zero_le_two
    _ = 6 * M_rate / r * (n : ℝ) ^ ((1 + ρ₀.re) / 4) * squarefreeDivisorMass n := by ring

/-- **Exact `ζ'(ρ₀) = 0` characterization via the log-twisted reflected-composite defect.**
At any off-line zero `ρ₀` (`1/2 < Re ρ₀ < 1`, `Im ρ₀ ≠ 0`, `ζ(ρ₀) = 0`), the log-twisted wave
defect `clippedCofactorOp n ⌊2√n⌋₊ (logTwistedWaveModel ρ₀) - midpointSecondDiff n (logTwistedWaveModel ρ₀)`
is `O(√n squarefreeDivisorMass n)` across `n ≥ 2` **if and only if** `deriv riemannZeta ρ₀ = 0`
(equivalently, `ρ₀` has multiplicity `≥ 2`). -/
theorem logTwisted_wave_compatible_iff_deriv_zero {ρ₀ : ℂ} (hhalf : 1 / 2 < ρ₀.re)
    (h1 : ρ₀.re < 1) (him : ρ₀.im ≠ 0) (hζ : riemannZeta ρ₀ = 0) :
    (∃ C : ℝ, ∀ n : ℕ, 2 ≤ n →
      |clippedCofactorOp n ⌊2 * Real.sqrt n⌋₊ (logTwistedWaveModel ρ₀) -
          midpointSecondDiff n (logTwistedWaveModel ρ₀)| ≤
        C * Real.sqrt n * squarefreeDivisorMass n) ↔
      deriv riemannZeta ρ₀ = 0 := by
  have hz0 : 0 < ρ₀.re := by linarith
  have hzne0 : ρ₀ ≠ 0 := fun he => by rw [he, Complex.zero_re] at hz0; exact lt_irrefl 0 hz0
  obtain ⟨C₀, hC₀, htw⟩ := clippedCofactorOp_logTwistedWave_at_zero hhalf h1 hζ
  constructor
  · rintro ⟨C, hC⟩
    by_contra hder_ne
    have hA_ne : (midpointMultiplier ρ₀ / ρ₀) * deriv riemannZeta ρ₀ ≠ 0 :=
      mul_ne_zero (div_ne_zero (midpointMultiplier_ne_zero hz0 h1) hzne0) hder_ne
    obtain ⟨p, c, hp, _, hc_pos, hpeaks⟩ :=
      exists_prime_power_re_lower_bound (le_refl 1) hz0 him hA_ne
    set K_tot : ℝ := 2 * (|C| + C₀)
    have hgap : 0 < ρ₀.re - 1 / 2 := sub_pos.mpr hhalf
    have hpow_tend : Tendsto (fun k : ℕ => ((p ^ k : ℕ) : ℝ)) atTop atTop :=
      tendsto_atTop_mono (fun k => by exact_mod_cast (Nat.lt_pow_self hp.one_lt).le)
        tendsto_natCast_atTop_atTop
    have htend : Tendsto (fun k : ℕ => ((p ^ k : ℕ) : ℝ) ^ (ρ₀.re - 1 / 2)) atTop atTop :=
      (_root_.tendsto_rpow_atTop hgap).comp hpow_tend
    obtain ⟨k, hk1, hbig⟩ :=
      ((eventually_ge_atTop 1).and
        (htend.eventually_gt_atTop ((K_tot + 1) / (2 * c)))).exists
    obtain ⟨n, hn_mem, _, hmass2, hpk⟩ := hpeaks k hk1
    have hn_ge_pk : p ^ k ≤ n := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hn_mem
      rcases hn_mem with rfl | rfl
      · exact le_rfl
      · exact Nat.pow_le_pow_right hp.pos (Nat.le_succ k)
    have hn2 : 2 ≤ n := (by simpa using hp.two_le : 2 ≤ p ^ 1).trans
      ((Nat.pow_le_pow_right hp.pos hk1).trans hn_ge_pk)
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hnR1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
    have hb1 := (hC n hn2).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_abs_self C) (Real.sqrt_nonneg n))
      (by rw [hmass2]; norm_num))
    have hb2_raw := htw n hn2
    have hexp_le : (n : ℝ) ^ ((1 + ρ₀.re) / 4) ≤ Real.sqrt n := by
      rw [Real.sqrt_eq_rpow]
      exact Real.rpow_le_rpow_of_exponent_le hnR1 (by linarith)
    have hb2 : |(clippedCofactorOp n ⌊2 * Real.sqrt n⌋₊ (logTwistedWaveModel ρ₀) -
          midpointSecondDiff n (logTwistedWaveModel ρ₀)) -
        2 * ((midpointMultiplier ρ₀ / ρ₀) * deriv riemannZeta ρ₀ * coprimeEulerFactor n ρ₀ *
          ((n : ℝ) : ℂ) ^ ρ₀).re| ≤ C₀ * Real.sqrt n * squarefreeDivisorMass n :=
      hb2_raw.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hexp_le hC₀)
        (sum_nonneg fun _ _ => abs_nonneg _))
    rw [hmass2] at hb1 hb2
    have hupper : |2 * ((midpointMultiplier ρ₀ / ρ₀) * deriv riemannZeta ρ₀ *
        coprimeEulerFactor n ρ₀ * ((n : ℝ) : ℂ) ^ ρ₀).re| ≤ K_tot * Real.sqrt n := by
      set D := clippedCofactorOp n ⌊2 * Real.sqrt n⌋₊ (logTwistedWaveModel ρ₀) -
        midpointSecondDiff n (logTwistedWaveModel ρ₀)
      have htri := abs_sub D
        (D - 2 * ((midpointMultiplier ρ₀ / ρ₀) * deriv riemannZeta ρ₀ *
          coprimeEulerFactor n ρ₀ * ((n : ℝ) : ℂ) ^ ρ₀).re)
      rw [sub_sub_cancel] at htri
      rw [show K_tot = 2 * (|C| + C₀) from rfl]
      linarith only [htri, hb1, hb2]
    have hlower : 2 * c * (n : ℝ) ^ ρ₀.re ≤
        |2 * ((midpointMultiplier ρ₀ / ρ₀) * deriv riemannZeta ρ₀ *
          coprimeEulerFactor n ρ₀ * ((n : ℝ) : ℂ) ^ ρ₀).re| := by
      rw [abs_mul, abs_of_pos two_pos, mul_assoc]
      exact mul_le_mul_of_nonneg_left hpk zero_le_two
    have hrpow_n : (K_tot + 1) / (2 * c) < (n : ℝ) ^ (ρ₀.re - 1 / 2) :=
      hbig.trans_le (Real.rpow_le_rpow (by positivity) (by exact_mod_cast hn_ge_pk) hgap.le)
    have hm1 := (div_lt_iff₀ (mul_pos two_pos hc_pos)).mp hrpow_n
    have hm2 := mul_lt_mul_of_pos_right hm1 (Real.sqrt_pos.mpr hn0)
    rw [mul_comm _ (2 * c), mul_assoc, Real.sqrt_eq_rpow, ← Real.rpow_add hn0,
      sub_add_cancel, ← Real.sqrt_eq_rpow] at hm2
    have hle_K : K_tot * Real.sqrt n < (K_tot + 1) * Real.sqrt n :=
      mul_lt_mul_of_pos_right (by linarith) (Real.sqrt_pos.mpr hn0)
    linarith only [hupper, hlower, hm2, hle_K]
  · intro hder0
    refine ⟨C₀, fun n hn => ?_⟩
    have hnR1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
    have hexp_le : (n : ℝ) ^ ((1 + ρ₀.re) / 4) ≤ Real.sqrt n := by
      rw [Real.sqrt_eq_rpow]
      exact Real.rpow_le_rpow_of_exponent_le hnR1 (by linarith)
    have hb := htw n hn
    simp only [hder0, mul_zero, zero_mul, Complex.zero_re, sub_zero] at hb
    exact hb.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hexp_le hC₀)
      (sum_nonneg fun _ _ => abs_nonneg _))

#print axioms midpointMultiplier_ne_zero
#print axioms exists_prime_power_re_lower_bound
#print axioms largePrimeCofactorPrice_eq_clippedCofactorOp
#print axioms clippedCofactorSliceOp_linear
#print axioms clippedCofactorSliceOp_wave
#print axioms clippedCofactorOp_linear_add_wave_defect
#print axioms reflectedComposite_wave_compatible_iff_zeta_zero
#print axioms clippedCofactorSliceOp_theta_of_two_le
#print axioms singleQuartet_reflectedComposite_remainder_cancellation
#print axioms singleQuartet_individual_cofactor_cell
#print axioms clippedCofactorOp_logTwistedWave_at_zero
#print axioms logTwisted_wave_compatible_iff_deriv_zero

end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
