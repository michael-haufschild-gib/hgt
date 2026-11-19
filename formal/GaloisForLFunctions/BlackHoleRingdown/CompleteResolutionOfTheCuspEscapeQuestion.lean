import GaloisForLFunctions.BlackHoleRingdown.PassiveTwinEchoAndFiniteTimeDistinction
import GaloisForLFunctions.ExclusionOfTheCriticalState.Models.ThePositiveEulerTwinsHaveNoRealZero
import GaloisForLFunctions.SelbergClass.RationalEulerTwinsCannotHavePositiveLogarithms
import GaloisForLFunctions.ArithmeticHolographyOfTheModularHorizon.OneCavityFunctionIsASharpReceiver

/-!
# Complete Resolution of the Cusp-Escape and Mixed-Pulse Interference Question

This module completes the unconditional mathematical resolution of the cusp-escape and mixed-pulse
question:

1. **Higher-Order Positive Passive Twins Matching `ζ` at `p²` and Any Finite Traversal Depth**
   (`EvenPowerPositiveEulerTwin`, `no_uniform_escape_rate_from_prime_traversal_and_passivity`):
   - At `q = p ^ (2 * k)` (`p.Prime`, `k ≥ 2`) with `R = q^σ > 1`, `U = q^{1-σ} > 1`, `A = R + U`
     (`1/2 < σ < 1`), the ordinary Dirichlet series `localFactor q A s * riemannZeta s` has real,
     bounded, multiplicative coefficients `≥ 1` equal to `1` for all `1 ≤ n < p^{2k}` (agreeing
     with `ζ` past any preassigned prefix `N`, at `p`, at `p²`, and on mixed primes `p q'`).
   - Its Euler logarithm `b = eulerLogCoeff q (-R) (-U)` is supported strictly on prime powers,
     converges on `Re s > 1` with `exp (LSeries b s) = localFactor q A s * riemannZeta s`, agrees
     identically with `eulerLogDirichletCoeff` away from powers of `p` and at all `p^j` for
     `1 ≤ j < 2k` (**in particular `b (p ^ 2) = 1 / 2` identically**), and satisfies
     `(b (p ^ (2 * k))).re = 1 / (2k) + R + U > 1 / (2k) > 0`.
   - `PositiveEulerHorizon.completedXi q A` is entire, `s ↦ 1 - s` symmetric, strictly positive on
     `ℝ`, globally Schur-passive with nonnegative Herglotz admittance on `Re w ≥ 0`, unitary on
     `i ℝ`, and has retarded causal echo kernel `twinEchoKernel q R U` (`= 0` on `τ ≤ 0`).
   - Yet for every `δ > 0`, choosing `σ ∈ (max(1/2, 1 - 2δ), 1)` places a zero of `completedXi q A`
     at `Re s = σ > 1 - 2δ` where `twinReflected q A` violates `O(e^{-δ τ})`. Conversely, requiring
     `∀ n, 0 ≤ (b n).re` simultaneously across all prime powers on a single-prime rational edit
     collapses to the trivial edit `W = 0 ∧ V = 0` (`not_exists_nontrivial_positive_rational_twin`).

2. **Finite Decay-Curve Indecisiveness Theorem**
   (`quartetGate`, `finite_decay_curve_cannot_decide_asymptotic_exponent`):
   For **every** nonzero `h : CompactPulse`, **every** tolerance `ε > 0`, and **every**
   `σ ∈ (1/2, 1)`, there exists `γ > 0` producing an entire, reflection-symmetric, real-axis-positive,
   globally Schur-passive, continuous-spectrum-unitary, retarded-causal model `xiQuartet σ γ` whose
   reflected wavepacket **for that very same pulse `h`** satisfies
   `∀ T : ℝ, ‖quartetReflected σ γ h T - pulseReflected h T‖ < ε`
   while violating `O(e^{-δ T})` for every `δ > (1 - σ) / 2`.

3. **Master Synthesis Theorem** (`complete_resolution_of_cusp_escape_question`):
   Unconditionally unites the five-channel mixed-pulse interference and Plancherel cusp-escape law,
   actual-`ζ` sub-`7/8` escape (`0 < σ < 3001/48000`), the two finite-time passive-twin
   distinguishing inequalities, the negative growing-window resolution at `b(p²) = +1/2`, and
   finite-curve indecisiveness.
-/

set_option autoImplicit false

open Complex MeasureTheory Set Filter Topology
open scoped ContDiff FourierTransform Classical BoundedContinuousFunction

noncomputable section

namespace GaloisForLFunctions.BlackHoleRingdown

open _root_.RHTower
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.SelbergClass.PositiveFiniteEuler
open GaloisForLFunctions.SelbergClass.FiniteEuler (multiplier not_exists_nontrivial_positive_rational_twin)
open GaloisForLFunctions.ExclusionOfTheCriticalState (positiveEuler_completedXi_real_pos)

/-! ## 1. Higher-Order Positive Passive Twins Matching `ζ` at `p²` and Arbitrary Traversal Depth -/

namespace EvenPowerPositiveEulerTwin

private theorem coeff_mul_of_not_dvd_prime_pow {p k m n : ℕ} (hp : p.Prime) (hk : 1 ≤ k)
    (hm : m ≠ 0) (hn : n ≠ 0) (hpn : ¬ p ∣ n) (A : ℝ) :
    coeff (p ^ k) A (m * n) = coeff (p ^ k) A m := by
  set q : ℕ := p ^ k
  have hqn : ¬ q ∣ n := fun h => hpn ((dvd_pow_self p (by omega)).trans h)
  have hq2n : ¬ q ^ 2 ∣ n := fun h => hqn ((dvd_pow_self q (by decide)).trans h)
  have hcop_qn : Nat.Coprime q n :=
    (Nat.Coprime.pow_left k ((hp.coprime_iff_not_dvd).mpr hpn))
  have hcop_q2n : Nat.Coprime (q ^ 2) n := hcop_qn.pow_left 2
  have hd1 : q ∣ m * n ↔ q ∣ m :=
    ⟨fun h => hcop_qn.dvd_of_dvd_mul_right h, fun h => dvd_mul_of_dvd_left h n⟩
  have hd2 : q ^ 2 ∣ m * n ↔ q ^ 2 ∣ m :=
    ⟨fun h => hcop_q2n.dvd_of_dvd_mul_right h, fun h => dvd_mul_of_dvd_left h n⟩
  simp only [coeff, if_neg (mul_ne_zero hm hn), if_neg hm, hd1, hd2]

/-- Multiplicativity of `arithmeticCoeffs (p ^ k) A` for any prime power `p ^ k` (`k ≥ 1`). -/
theorem arithmeticCoeffs_prime_pow_isMultiplicative {p k : ℕ} (hp : p.Prime) (hk : 1 ≤ k)
    (A : ℝ) : (arithmeticCoeffs (p ^ k) A).IsMultiplicative := by
  have hq1 : 1 < p ^ k := one_lt_pow₀ hp.one_lt (by omega)
  apply ArithmeticFunction.IsMultiplicative.iff_ne_zero.mpr
  refine ⟨?_, fun {m n} hm hn hcop => ?_⟩
  · simp only [arithmeticCoeffs_apply, coeff_eq_one_of_lt one_ne_zero hq1 A, Complex.ofReal_one]
  · have hnot : ¬ p ∣ m ∨ ¬ p ∣ n := by
      by_contra h
      push Not at h
      have hd : p ∣ Nat.gcd m n := Nat.dvd_gcd h.1 h.2
      rw [hcop] at hd
      exact hp.not_dvd_one hd
    have hone : ∀ {j : ℕ}, j ≠ 0 → ¬ p ∣ j → coeff (p ^ k) A j = 1 := by
      intro j hj hpj
      have hqj : ¬ p ^ k ∣ j := fun h => hpj ((dvd_pow_self p (by omega)).trans h)
      have hq2j : ¬ (p ^ k) ^ 2 ∣ j := fun h => hqj ((dvd_pow_self _ (by decide)).trans h)
      simp only [coeff, if_neg hj, if_neg hqj, if_neg hq2j, add_zero]
    simp only [arithmeticCoeffs_apply, ← Complex.ofReal_mul]
    congr 1
    rcases hnot with hpm | hpn
    · rw [mul_comm m n, coeff_mul_of_not_dvd_prime_pow hp hk hn hm hpm A, hone hm hpm, one_mul]
    · rw [coeff_mul_of_not_dvd_prime_pow hp hk hm hn hpn A, hone hn hpn, mul_one]

/-- Dirichlet series representation of `localFactor q A s * riemannZeta s` for any `q ≥ 2`. -/
theorem lSeriesHasSum_of_one_lt {q : ℕ} (hq : 1 < q) (A : ℝ) {s : ℂ} (hs : 1 < s.re) :
    LSeriesHasSum (arithmeticCoeffs q A) s (localFactor q A s * riemannZeta s) := by
  have hq0 : q ≠ 0 := by omega
  set single : ℕ → ℂ → ℕ → ℂ := fun d b n => if n = d then b else 0
  have hsingle : ∀ {d : ℕ} (hd : d ≠ 0) (b : ℂ),
      LSeriesHasSum (single d b) s (b / (d : ℂ) ^ s) := by
    intro d hd b
    refine (hasSum_ite_eq d (b / (d : ℂ) ^ s)).congr_fun fun n => ?_
    by_cases hnd : n = d
    · subst n; simp [LSeries.term_of_ne_zero hd, single]
    · rcases eq_or_ne n 0 with rfl | hn
      · simp [single, hnd]
      · simp [LSeries.term_of_ne_zero hn, single, hnd]
  set loc : ℕ → ℂ := single 1 1 + single q A + single (q ^ 2) q
  have hloc : LSeriesHasSum loc s (localFactor q A s) := by
    have h := (hsingle one_ne_zero 1 |>.add (hsingle hq0 A)).add (hsingle (pow_ne_zero 2 hq0) q)
    have hpow : ((q ^ 2 : ℕ) : ℂ) ^ s = ((q : ℂ) ^ s) ^ 2 := by
      rw [show ((q ^ 2 : ℕ) : ℂ) = (q : ℂ) * q by push_cast; ring, pow_two]
      exact Complex.natCast_mul_natCast_cpow q q s
    simpa only [loc, localFactor, Nat.cast_one, one_cpow, div_one, hpow, cpow_neg, div_eq_mul_inv,
      inv_pow, inv_one, mul_one] using h
  have hz : LSeriesHasSum (1 : ℕ → ℂ) s (riemannZeta s) := by
    refine (ArithmeticFunction.LSeriesHasSum_zeta hs).congr_fun fun n => ?_
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · simp [hn, one_div]
  have hconv_eq : (arithmeticCoeffs q A : ℕ → ℂ) = LSeries.convolution loc 1 := by
    funext n
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · simp only [arithmeticCoeffs_apply, LSeries.convolution_def, Pi.one_apply, mul_one]
      rw [Nat.sum_divisorsAntidiagonal (fun i _ => loc i)]
      simp only [loc, Pi.add_apply, single, Finset.sum_add_distrib, Finset.sum_ite_eq',
        Nat.mem_divisors]
      by_cases hqn : q ∣ n <;> by_cases hq2n : q ^ 2 ∣ n <;> simp [coeff, hn, hqn, hq2n]
  rw [show (↑(arithmeticCoeffs q A) : ℕ → ℂ) = LSeries.convolution loc 1 from hconv_eq]
  exact hloc.convolution hz

/-- Euler-logarithm properties at `q = p ^ (2 * k)` (`k ≥ 1`, `1 < R`, `1 < U`, `R * U = q`):
prime-power support, convergence and exponentiation on `Re s > 1`, exact agreement with `ζ`'s
Euler logarithm at all `p^j` for `1 ≤ j < 2k` (`b(p²) = 1/2` when `k ≥ 2`), and strict positivity
`(b(p^{2k})).re > 1 / (2k) > 0` at the first modified power `p^{2k}`. -/
theorem eulerLog_even_power_properties {p k : ℕ} (hp : p.Prime) (hk : 1 ≤ k) {R U : ℝ}
    (hR : 1 < R) (hU : 1 < U) (hRU : R * U = (p ^ (2 * k) : ℕ)) :
    let q : ℕ := p ^ (2 * k)
    let b : ℕ → ℂ := eulerLogCoeff q (-(R : ℂ)) (-(U : ℂ))
    (∀ n : ℕ, b n ≠ 0 → IsPrimePow n) ∧
    (∀ s : ℂ, 1 < s.re → LSeriesSummable b s ∧
      Complex.exp (LSeries b s) = localFactor q (R + U) s * riemannZeta s) ∧
    (∀ n : ℕ, (¬ ∃ m : ℕ, 1 ≤ m ∧ q ^ m = n) → b n = RHTower.eulerLogDirichletCoeff n) ∧
    (∀ j : ℕ, 1 ≤ j → j < 2 * k → b (p ^ j) = 1 / (j : ℂ)) ∧
    (b (p ^ (2 * k))).re = 1 / (2 * (k : ℝ)) + R + U := by
  dsimp only
  set q : ℕ := p ^ (2 * k)
  have h2k : 2 ≤ 2 * k := by omega
  have hq : 1 < q := one_lt_pow₀ hp.one_lt (by omega)
  have hqR : (1 : ℝ) < q := by exact_mod_cast hq
  have hq0 : (0 : ℝ) < q := zero_lt_one.trans hqR
  set b : ℕ → ℂ := eulerLogCoeff q (-(R : ℂ)) (-(U : ℂ))
  have hpow_zero : ∀ {n : ℕ}, (¬ ∃ m : ℕ, q ^ m = n) → ∀ α : ℂ, powerLogCoeff q α n = 0 :=
    fun hn α => Function.extend_apply' _ _ _ hn
  -- 1. Prime-power support
  have hsupp : ∀ n : ℕ, b n ≠ 0 → IsPrimePow n := by
    intro n hn
    by_contra hnot
    have hc := RHTower.eulerLogDirichletCoeff_eq_zero_of_not_primePower hnot
    by_cases hpow : ∃ m : ℕ, q ^ m = n
    · obtain ⟨m, rfl⟩ := hpow
      rcases eq_or_ne m 0 with rfl | hm0
      · exact hn (eulerLogCoeff_one hq _ _)
      · have hqm : q ^ m = p ^ (2 * k * m) := (pow_mul p (2 * k) m).symm
        rw [hqm] at hnot
        exact hnot ((isPrimePow_nat_iff _).mpr ⟨p, 2 * k * m, hp, by positivity, rfl⟩)
    · exact hn (by simp [b, eulerLogCoeff, hc, hpow_zero hpow])
  -- 2. Convergence and exponentiation on `Re s > 1`
  have hexp : ∀ s : ℂ, 1 < s.re → LSeriesSummable b s ∧
      Complex.exp (LSeries b s) = localFactor q (R + U) s * riemannZeta s := by
    intro s hs
    have hRq : R ≤ q := by
      calc R ≤ R * U := le_mul_of_one_le_right (zero_lt_one.trans hR).le hU.le
        _ = q := hRU
    have hUq : U ≤ q := by
      calc U ≤ R * U := le_mul_of_one_le_left (zero_lt_one.trans hU).le hR.le
        _ = q := hRU
    have hconv : ∀ {a : ℝ}, 0 < a → a ≤ q → ‖(-(a : ℂ)) * (q : ℂ) ^ (-s)‖ < 1 := by
      intro a ha0 haq
      rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_of_nonneg ha0.le,
        Complex.norm_natCast_cpow_of_pos (by omega), Complex.neg_re, Real.rpow_def_of_pos hq0]
      calc a * Real.exp (Real.log q * -s.re)
          ≤ (q : ℝ) * Real.exp (Real.log q * -s.re) :=
            mul_le_mul_of_nonneg_right haq (Real.exp_pos _).le
        _ = Real.exp (Real.log q * (1 - s.re)) := by
            conv_lhs => lhs; rw [← Real.exp_log hq0]
            rw [← Real.exp_add]; congr 1; ring
        _ < 1 := Real.exp_lt_one_iff.mpr
            (mul_neg_of_pos_of_neg (Real.log_pos hqR) (by linarith))
    have hcR := hconv (zero_lt_one.trans hR) hRq
    have hcU := hconv (zero_lt_one.trans hU) hUq
    have hHS : LSeriesHasSum b s
        (RHTower.canonicalEulerLogZeta s + Complex.log (1 - (-(R : ℂ)) * (q : ℂ) ^ (-s)) +
          Complex.log (1 - (-(U : ℂ)) * (q : ℂ) ^ (-s))) :=
      ((RHTower.canonicalEulerLogZeta_summable hs).LSeriesHasSum.add
        (hasSum_powerLogCoeff hq (-(R : ℂ)) hcR)).add
        (hasSum_powerLogCoeff hq (-(U : ℂ)) hcU)
    refine ⟨hHS.LSeriesSummable, ?_⟩
    have hR0 : 1 - (-(R : ℂ)) * (q : ℂ) ^ (-s) ≠ 0 := fun h0 => by
      have h1 := sub_eq_zero.mp h0; rw [← h1, norm_one] at hcR; exact lt_irrefl _ hcR
    have hU0 : 1 - (-(U : ℂ)) * (q : ℂ) ^ (-s) ≠ 0 := fun h0 => by
      have h1 := sub_eq_zero.mp h0; rw [← h1, norm_one] at hcU; exact lt_irrefl _ hcU
    rw [hHS.LSeries_eq, Complex.exp_add, Complex.exp_add, Complex.exp_log hR0, Complex.exp_log hU0,
      RHTower.exp_canonicalEulerLogZeta_eq_riemannZeta hs]
    have hRUC : (R : ℂ) * (U : ℂ) = q := by exact_mod_cast hRU
    have hfac : (1 - (-(R : ℂ)) * (q : ℂ) ^ (-s)) * (1 - (-(U : ℂ)) * (q : ℂ) ^ (-s)) =
        localFactor q (R + U) s := by
      rw [localFactor]; push_cast; rw [← hRUC]; ring
    rw [mul_assoc, hfac, mul_comm]
  -- 3. Unchanged outside `q^m` (`m ≥ 1`)
  have hunchanged : ∀ n : ℕ, (¬ ∃ m : ℕ, 1 ≤ m ∧ q ^ m = n) →
      b n = RHTower.eulerLogDirichletCoeff n := by
    intro n hnot
    rcases eq_or_ne n 1 with rfl | hn1
    · dsimp only [b]
      rw [eulerLogCoeff_one hq, RHTower.eulerLogDirichletCoeff_one]
    · have hnpow : ¬ ∃ m : ℕ, q ^ m = n := by
        rintro ⟨m, rfl⟩
        rcases eq_or_ne m 0 with rfl | hm0
        · exact hn1 rfl
        · exact hnot ⟨m, by omega, rfl⟩
      simp [b, eulerLogCoeff, hpow_zero hnpow]
  -- 4. Agreement with `1 / j` at `p^j` for `1 ≤ j < 2k`
  have hlow : ∀ j : ℕ, 1 ≤ j → j < 2 * k → b (p ^ j) = 1 / (j : ℂ) := by
    intro j hj1 hjlt
    have hnot_q : ¬ ∃ m : ℕ, 1 ≤ m ∧ q ^ m = p ^ j := by
      rintro ⟨m, hm1, heq⟩
      have hqm : q ^ m = p ^ (2 * k * m) := (pow_mul p (2 * k) m).symm
      rw [hqm] at heq
      have hinj := (pow_right_strictMono₀ hp.one_lt).injective heq
      have hge : 2 * k ≤ 2 * k * m := Nat.le_mul_of_pos_right (2 * k) hm1
      omega
    obtain ⟨j₀, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
    rw [hunchanged (p ^ (j₀ + 1)) hnot_q,
      RHTower.eulerLogDirichletCoeff_prime_pow_succ p j₀ hp]
    push_cast; ring
  -- 5. First modified power `p^{2k} = q^1`
  have hfirst : (b (p ^ (2 * k))).re = 1 / (2 * (k : ℝ)) + R + U := by
    have hq_eq : p ^ (2 * k) = q ^ 1 := by simp [q]
    obtain ⟨j₀, hj₀⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : 2 * k ≠ 0)
    have hz_zeta : RHTower.eulerLogDirichletCoeff (p ^ (2 * k)) = 1 / (2 * (k : ℂ)) := by
      rw [hj₀, RHTower.eulerLogDirichletCoeff_prime_pow_succ p j₀ hp]
      have hcast : ((j₀ : ℂ) + 1) = 2 * (k : ℂ) := by exact_mod_cast hj₀.symm
      rw [hcast]
    have hpR1 : powerLogCoeff q (-(R : ℂ)) q = (R : ℂ) := by
      simpa using powerLogCoeff_pow hq (-(R : ℂ)) 1
    have hpU1 : powerLogCoeff q (-(U : ℂ)) q = (U : ℂ) := by
      simpa using powerLogCoeff_pow hq (-(U : ℂ)) 1
    change (RHTower.eulerLogDirichletCoeff (p ^ (2 * k)) +
      powerLogCoeff q (-(R : ℂ)) q + powerLogCoeff q (-(U : ℂ)) q).re = _
    rw [hz_zeta, hpR1, hpU1]
    have hreal : (1 / (2 * (k : ℂ)) + (R : ℂ) + (U : ℂ)) =
        ((1 / (2 * (k : ℝ)) + R + U : ℝ) : ℂ) := by push_cast; rfl
    rw [hreal, Complex.ofReal_re]
  exact ⟨hsupp, hexp, hunchanged, hlow, hfirst⟩

end EvenPowerPositiveEulerTwin

/-- **Negative Resolution of Growing-Window Uniform Constants.**
For every finite prefix `N : ℕ`, every prime-power traversal depth `M : ℕ`, and every target escape
rate `δ > 0`, there exist a prime `p > N`, `k ≥ max 2 M` (`q = p^{2k}`), and `1 < U < R`
(`R * U = q`, `A = R + U`) such that the horizon system `(q, A)` satisfies:
1. real, bounded, multiplicative ordinary Dirichlet coefficients `≥ 1` equal to `1` on
   `[1, p^{2k})` (hence past `N`, at `p`, at `p²`, and on mixed primes `p q'` with `q' < p^{2k-1}`);
2. prime-power-supported Euler logarithm `b` on `Re s > 1` matching `ζ`'s Euler logarithm at all
   `p^j` for `1 ≤ j < 2k` — **in particular `b(p²) = 1/2`** — and `(b(p^{2k})).re > 0`;
3. entire reflection-symmetric completion `completedXi q A` strictly positive on `ℝ`, globally
   Schur-passive with nonnegative Herglotz admittance on `Re w ≥ 0`, unitary on `i ℝ`, with causal
   retarded echo kernel `twinEchoKernel q R U` (`= 0` on `τ ≤ 0`) and exact Plancherel `L²`
   conservation;
4. yet `completedXi q A` has a zero at `Re s > 1 - 2δ` and an explicit compactly supported smooth
   pulse violates `O(e^{-δ τ})`;
5. whereas requiring `0 ≤ (b n).re` simultaneously across *all* powers on a single-prime rational
   edit leaves no nontrivial twin (`not_exists_nontrivial_positive_rational_twin`). -/
theorem no_uniform_escape_rate_from_prime_traversal_and_passivity
    (N M : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    (∃ (p k : ℕ) (_ : p.Prime) (R U : ℝ),
      N < p ∧ max 2 M ≤ k ∧ 1 < U ∧ U < R ∧ R * U = (p ^ (2 * k) : ℕ) ∧
      let q : ℕ := p ^ (2 * k)
      let A : ℝ := R + U
      let b : ℕ → ℂ := eulerLogCoeff q (-(R : ℂ)) (-(U : ℂ))
      (arithmeticCoeffs q A).IsMultiplicative ∧
      (∃ C : ℝ, ∀ n : ℕ, n ≠ 0 →
        (arithmeticCoeffs q A n).im = 0 ∧
        1 ≤ (arithmeticCoeffs q A n).re ∧ ‖arithmeticCoeffs q A n‖ ≤ C) ∧
      (∀ n : ℕ, n ≠ 0 → n < q → arithmeticCoeffs q A n = 1) ∧
      (∀ n : ℕ, b n ≠ 0 → IsPrimePow n) ∧
      (∀ s : ℂ, 1 < s.re → LSeriesSummable b s ∧
        Complex.exp (LSeries b s) = localFactor q A s * riemannZeta s) ∧
      (∀ j : ℕ, 1 ≤ j → j < 2 * k → b (p ^ j) = 1 / (j : ℂ)) ∧
      b (p ^ 2) = 1 / 2 ∧
      0 < (b (p ^ (2 * k))).re ∧
      Differentiable ℂ (PositiveEulerHorizon.completedXi q A) ∧
      (∀ s : ℂ, PositiveEulerHorizon.completedXi q A (1 - s) =
        PositiveEulerHorizon.completedXi q A s) ∧
      (∀ x : ℝ, 0 < (PositiveEulerHorizon.completedXi q A (x : ℂ)).re) ∧
      (∀ w : ℂ, 0 ≤ w.re → ‖PositiveEulerHorizon.reducedScattering q A w‖ ≤ 1 ∧
        0 ≤ ((1 - PositiveEulerHorizon.reducedScattering q A w) /
          (1 + PositiveEulerHorizon.reducedScattering q A w)).re) ∧
      (∀ t : ℝ, ‖PositiveEulerHorizon.scatteringPhase q A ((t : ℂ) * I)‖ = 1) ∧
      (∀ τ : ℝ, τ ≤ 0 → twinEchoKernel q R U τ = 0) ∧
      (∀ h : CompactPulse, (∫ T : ℝ, ‖twinReflected q A h T‖ ^ 2) = ∫ S : ℝ, ‖h S‖ ^ 2) ∧
      (∃ s₀ : ℂ, 1 - 2 * δ < s₀.re ∧ PositiveEulerHorizon.completedXi q A s₀ = 0) ∧
      (∃ h : CompactPulse, ¬ ∃ C : ℝ, ∀ τ : ℝ, 0 ≤ τ →
        ‖twinReflected q A h τ‖ ≤ C * Real.exp (-δ * τ))) ∧
    (∀ (p : ℕ), p.Prime →
      ¬ ∃ (W V : Multiset ℂ) (c : ℂ) (F : ℂ → ℂ) (b : ℕ → ℂ) (B : ℝ),
        (W ≠ 0 ∨ V ≠ 0) ∧ (∀ a ∈ W, a ≠ 0) ∧ (∀ a ∈ V, a ≠ 0) ∧
        (∀ v ∈ V, v ∉ W) ∧ Differentiable ℂ F ∧
        (∀ s : ℂ, F (1 - s) = F s) ∧ (∀ n : ℕ, 0 ≤ (b n).re) ∧
        (∀ s : ℂ, B < s.re → multiplier V ((p : ℂ) ^ (-s)) * F s =
          Complex.exp (c * s) * multiplier W ((p : ℂ) ^ (-s)) * xi s) ∧
        (∀ s : ℂ, B < s.re → LSeriesSummable b s ∧
          Complex.exp (LSeries b s) = riemannZeta s * multiplier W ((p : ℂ) ^ (-s)) /
            multiplier V ((p : ℂ) ^ (-s)))) := by
  refine ⟨?_, fun _ hp => not_exists_nontrivial_positive_rational_twin hp⟩
  obtain ⟨p, hpN, hp⟩ := Nat.exists_infinite_primes (N + 1)
  set k : ℕ := max 2 M
  have hk2 : 2 ≤ k := le_max_left 2 M
  have hk1 : 1 ≤ 2 * k := by omega
  set q : ℕ := p ^ (2 * k)
  have hq : 1 < q := one_lt_pow₀ hp.one_lt (by omega)
  have hqR : (1 : ℝ) < q := by exact_mod_cast hq
  have hq0 : (0 : ℝ) < q := zero_lt_one.trans hqR
  set σ : ℝ := (max (1 / 2 : ℝ) (1 - 2 * δ) + 1) / 2
  have hσ_lo : 1 / 2 < σ := by
    have : (1 / 2 : ℝ) ≤ max (1 / 2) (1 - 2 * δ) := le_max_left _ _
    dsimp only [σ]; linarith
  have hσ_δ : 1 - 2 * δ < σ := by
    have : 1 - 2 * δ ≤ max (1 / 2) (1 - 2 * δ) := le_max_right _ _
    dsimp only [σ]; linarith
  have hσ_hi : σ < 1 := by
    have : max (1 / 2 : ℝ) (1 - 2 * δ) < 1 := max_lt (by norm_num) (by linarith)
    dsimp only [σ]; linarith
  set R : ℝ := (q : ℝ) ^ σ
  set U : ℝ := (q : ℝ) ^ (1 - σ)
  have hR : 1 < R := Real.one_lt_rpow hqR (by linarith)
  have hU : 1 < U := Real.one_lt_rpow hqR (by linarith)
  have hUR : U < R := Real.rpow_lt_rpow_of_exponent_lt hqR (by linarith)
  have hRU : R * U = (q : ℝ) := by
    dsimp only [R, U]
    rw [← Real.rpow_add hq0, show σ + (1 - σ) = 1 by ring, Real.rpow_one]
  obtain ⟨hb_supp, hb_exp, _, hb_low, hb_first⟩ :=
    EvenPowerPositiveEulerTwin.eulerLog_even_power_properties hp (by omega : 1 ≤ k) hR hU hRU
  refine ⟨p, k, hp, R, U, by omega, le_rfl, hU, hUR, hRU, ?_⟩
  dsimp only
  refine ⟨EvenPowerPositiveEulerTwin.arithmeticCoeffs_prime_pow_isMultiplicative hp hk1 (R + U),
    ⟨1 + (R + U) + q, fun n hn => ?_⟩,
    fun n hn hnq => by rw [arithmeticCoeffs_apply, coeff_eq_one_of_lt hn hnq, Complex.ofReal_one],
    hb_supp, hb_exp, hb_low, ?_, ?_,
    PositiveEulerHorizon.differentiable_completedXi (by omega) (R + U),
    PositiveEulerHorizon.completedXi_one_sub q (R + U),
    positiveEuler_completedXi_real_pos (by omega) (by linarith),
    fun w hw => ⟨PositiveEulerHorizon.norm_reducedScattering_le_one hq hR hU hRU hw,
      PositiveEulerHorizon.herglotz_re_nonneg hq hR hU hRU hw⟩,
    PositiveEulerHorizon.norm_scatteringPhase_axis hq hR hU hRU,
    fun τ hτ => twinEchoKernel_eq_zero_of_nonpos q R U hτ,
    fun h => (integrable_and_integral_norm_sq_twinReflected hq hR hU hRU h).2,
    ?_, ?_⟩
  · have hb := coeff_bounds (p := q) (A := R + U) (by linarith) hn
    rw [arithmeticCoeffs_apply, Complex.ofReal_im, Complex.ofReal_re,
      Complex.norm_real, Real.norm_of_nonneg (zero_le_one.trans hb.1)]
    exact ⟨rfl, hb⟩
  · simpa using hb_low 2 (by decide) (by omega)
  · rw [hb_first]
    have hk_pos : (0 : ℝ) < 1 / (2 * (k : ℝ)) := by positivity
    linarith
  · refine ⟨factorZero q R, ?_, ?_⟩
    · rw [factorZero_re, show Real.log R = σ * Real.log q from Real.log_rpow hq0 σ,
        mul_div_cancel_right₀ _ (Real.log_pos hqR).ne']
      exact hσ_δ
    · have hparam : reciprocalParameter q R = R + U := by
        rw [reciprocalParameter, (div_eq_iff (zero_lt_one.trans hR).ne').mpr (by rw [mul_comm, hRU])]
      rw [PositiveEulerHorizon.completedXi, ← cpow_mul_localFactor (by omega),
        ← hparam, localFactor_factorZero hq (zero_lt_one.trans hR), mul_zero, zero_mul]
  · refine ⟨excitingPulse ((factorZero q R - 1) / 2), ?_⟩
    exact not_twinReflected_decay_gt hq hσ_lo hσ_hi (by linarith)

/-! ## 2. Finite Decay-Curve Indecisiveness (`quartetGate`) -/

/-- Off-line zero location `ρ = σ + i γ` of the quartet model. -/
def quartetZero (σ γ : ℝ) : ℂ := (σ : ℂ) + (γ : ℂ) * I

/-- Self-dual real-axis-positive quartet polynomial multiplier
`(1 - s(1-s)/(ρ(1-ρ))) (1 - s(1-s)/(conj ρ (1 - conj ρ)))`. -/
def quartetFactor (σ γ : ℝ) (s : ℂ) : ℂ :=
  (1 - s * (1 - s) / (quartetZero σ γ * (1 - quartetZero σ γ))) *
    (1 - s * (1 - s) / ((starRingEnd ℂ) (quartetZero σ γ) * (1 - (starRingEnd ℂ) (quartetZero σ γ))))

/-- Completed quartet zeta model `quartetFactor σ γ s * xi s`. -/
def xiQuartet (σ γ : ℝ) (s : ℂ) : ℂ :=
  quartetFactor σ γ s * xi s

/-- Reduced scattering function of `xiQuartet σ γ`. -/
def quartetReducedScattering (σ γ : ℝ) (w : ℂ) : ℂ :=
  xiQuartet σ γ (2 * w) / xiQuartet σ γ (1 + 2 * w)

/-- Full continuous-spectrum scattering phase of `xiQuartet σ γ`. -/
def quartetScatteringPhase (σ γ : ℝ) (w : ℂ) : ℂ :=
  ((1 + 2 * w) / (2 * w - 1)) * quartetReducedScattering σ γ w

/-- Degree-4 right-half-plane rational Blaschke gate `quartetFactor σ γ (2w) / quartetFactor σ γ (1+2w)`. -/
def quartetGate (σ γ : ℝ) (w : ℂ) : ℂ :=
  quartetFactor σ γ (2 * w) / quartetFactor σ γ (1 + 2 * w)

/-- Reflected cusp wavepacket of `xiQuartet σ γ` for a pulse `h`. -/
def quartetReflected (σ γ : ℝ) (h : ℝ → ℂ) (T : ℝ) : ℂ :=
  unitaryReflected (fun ξ => quartetScatteringPhase σ γ ((ξ : ℂ) * I)) h T

private theorem quartetProd_im {σ γ : ℝ} :
    (quartetZero σ γ * (1 - quartetZero σ γ)).im = γ * (1 - 2 * σ) := by
  simp only [quartetZero]
  simp [Complex.mul_im, Complex.sub_re, Complex.sub_im]
  ring

private theorem quartetProd_re {σ γ : ℝ} :
    (quartetZero σ γ * (1 - quartetZero σ γ)).re = σ * (1 - σ) + γ ^ 2 := by
  simp only [quartetZero]
  simp [Complex.mul_re, Complex.sub_re, Complex.sub_im]
  ring

private theorem quartetProd_ne_zero {σ γ : ℝ} (h0 : 1 / 2 < σ) (hγ : 0 < γ) :
    quartetZero σ γ * (1 - quartetZero σ γ) ≠ 0 ∧
      (starRingEnd ℂ) (quartetZero σ γ) * (1 - (starRingEnd ℂ) (quartetZero σ γ)) ≠ 0 := by
  have h1 : quartetZero σ γ * (1 - quartetZero σ γ) ≠ 0 := fun hz => by
    have him := quartetProd_im (σ := σ) (γ := γ)
    rw [hz, Complex.zero_im] at him
    nlinarith
  have h2 : (starRingEnd ℂ) (quartetZero σ γ) * (1 - (starRingEnd ℂ) (quartetZero σ γ)) =
      (starRingEnd ℂ) (quartetZero σ γ * (1 - quartetZero σ γ)) := by simp [map_mul, map_sub]
  exact ⟨h1, by rw [h2]; exact map_ne_zero_iff _ (RingHom.injective _) |>.mpr h1⟩

theorem differentiable_quartetFactor (σ γ : ℝ) : Differentiable ℂ (quartetFactor σ γ) := by
  unfold quartetFactor
  exact ((differentiable_const 1).sub
      ((differentiable_id.mul ((differentiable_const 1).sub differentiable_id)).div_const _)).mul
    ((differentiable_const 1).sub
      ((differentiable_id.mul ((differentiable_const 1).sub differentiable_id)).div_const _))

theorem differentiable_xiQuartet (σ γ : ℝ) : Differentiable ℂ (xiQuartet σ γ) :=
  (differentiable_quartetFactor σ γ).mul xi_differentiable

theorem xiQuartet_one_sub (σ γ : ℝ) (s : ℂ) :
    xiQuartet σ γ (1 - s) = xiQuartet σ γ s := by
  have hsym : (1 - s) * (1 - (1 - s)) = s * (1 - s) := by ring
  unfold xiQuartet quartetFactor
  rw [hsym, xi_one_sub]

/-- Strict real-axis positivity `0 < (xiQuartet σ γ x).re` for all `x : ℝ`. -/
theorem xiQuartet_real_pos {σ γ : ℝ} (h0 : 1 / 2 < σ) (hγ : 0 < γ) (x : ℝ) :
    0 < (xiQuartet σ γ (x : ℂ)).re := by
  set z : ℂ := 1 - (x : ℂ) * (1 - (x : ℂ)) / (quartetZero σ γ * (1 - quartetZero σ γ))
  have hconj : 1 - (x : ℂ) * (1 - (x : ℂ)) /
      ((starRingEnd ℂ) (quartetZero σ γ) * (1 - (starRingEnd ℂ) (quartetZero σ γ))) =
      (starRingEnd ℂ) z := by
    simp [z, map_sub, map_div₀, map_mul]
  have hz_ne : z ≠ 0 := by
    intro hz0
    have hq_ne := (quartetProd_ne_zero h0 hγ).1
    have hmul : (x : ℂ) * (1 - (x : ℂ)) = quartetZero σ γ * (1 - quartetZero σ γ) :=
      (div_eq_one_iff_eq hq_ne).mp (sub_eq_zero.mp hz0).symm
    have him := congrArg Complex.im hmul
    have hlhs : ((x : ℂ) * (1 - (x : ℂ))).im = 0 := by
      have : (x : ℂ) * (1 - (x : ℂ)) = ((x * (1 - x) : ℝ) : ℂ) := by push_cast; rfl
      rw [this, Complex.ofReal_im]
    rw [hlhs, quartetProd_im] at him
    nlinarith
  have hfac : quartetFactor σ γ (x : ℂ) = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
    unfold quartetFactor
    rw [hconj]
    change z * (starRingEnd ℂ) z = _
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [xiQuartet, hfac, Complex.re_ofReal_mul]
  exact mul_pos (sq_pos_of_pos (norm_pos_iff.mpr hz_ne)) (_root_.RHTower.XiGlobalKummer.xi_real_pos x)

theorem xiQuartet_eval_quartetZero {σ γ : ℝ} (h0 : 1 / 2 < σ) (hγ : 0 < γ) :
    xiQuartet σ γ (quartetZero σ γ) = 0 := by
  have hne := (quartetProd_ne_zero h0 hγ).1
  unfold xiQuartet quartetFactor
  rw [div_self hne, sub_self, zero_mul, zero_mul]

private theorem quartetGate_eq_blaschke_four {σ γ : ℝ} (h0 : 1 / 2 < σ) (h1 : σ < 1)
    (hγ : 0 < γ) (w : ℂ) :
    let w₁ : ℂ := (((1 - σ) / 2 : ℝ) : ℂ) + ((γ / 2 : ℝ) : ℂ) * I
    let w₂ : ℂ := ((σ / 2 : ℝ) : ℂ) + ((γ / 2 : ℝ) : ℂ) * I
    quartetFactor σ γ (2 * w) *
        ((quartetZero σ γ * (1 - quartetZero σ γ)) *
          ((starRingEnd ℂ) (quartetZero σ γ) * (1 - (starRingEnd ℂ) (quartetZero σ γ)))) =
      16 * (w - w₁) * (w - (starRingEnd ℂ) w₁) * (w - w₂) * (w - (starRingEnd ℂ) w₂) ∧
    quartetFactor σ γ (1 + 2 * w) *
        ((quartetZero σ γ * (1 - quartetZero σ γ)) *
          ((starRingEnd ℂ) (quartetZero σ γ) * (1 - (starRingEnd ℂ) (quartetZero σ γ)))) =
      16 * (w + (starRingEnd ℂ) w₁) * (w + w₁) * (w + (starRingEnd ℂ) w₂) * (w + w₂) ∧
    quartetGate σ γ w =
      ((w - w₁) / (w + (starRingEnd ℂ) w₁)) *
      ((w - (starRingEnd ℂ) w₁) / (w + w₁)) *
      ((w - w₂) / (w + (starRingEnd ℂ) w₂)) *
      ((w - (starRingEnd ℂ) w₂) / (w + w₂)) := by
  have _ := h1
  obtain ⟨hq1, hq2⟩ := quartetProd_ne_zero h0 hγ
  dsimp only
  set w₁ : ℂ := (((1 - σ) / 2 : ℝ) : ℂ) + ((γ / 2 : ℝ) : ℂ) * I
  set w₂ : ℂ := ((σ / 2 : ℝ) : ℂ) + ((γ / 2 : ℝ) : ℂ) * I
  have hp1 : (1 - (2 * w) * (1 - 2 * w) / (quartetZero σ γ * (1 - quartetZero σ γ))) *
      (quartetZero σ γ * (1 - quartetZero σ γ)) = 4 * (w - (starRingEnd ℂ) w₁) * (w - w₂) := by
    rw [sub_mul, one_mul, div_mul_cancel₀ _ hq1]
    simp only [w₁, w₂, quartetZero, map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
    push_cast; ring
  have hp2 : (1 - (2 * w) * (1 - 2 * w) /
      ((starRingEnd ℂ) (quartetZero σ γ) * (1 - (starRingEnd ℂ) (quartetZero σ γ)))) *
      ((starRingEnd ℂ) (quartetZero σ γ) * (1 - (starRingEnd ℂ) (quartetZero σ γ))) =
      4 * (w - w₁) * (w - (starRingEnd ℂ) w₂) := by
    rw [sub_mul, one_mul, div_mul_cancel₀ _ hq2]
    simp only [w₁, w₂, quartetZero, map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
    push_cast; ring
  have hnum' : quartetFactor σ γ (2 * w) *
      ((quartetZero σ γ * (1 - quartetZero σ γ)) *
        ((starRingEnd ℂ) (quartetZero σ γ) * (1 - (starRingEnd ℂ) (quartetZero σ γ)))) =
      16 * (w - w₁) * (w - (starRingEnd ℂ) w₁) * (w - w₂) * (w - (starRingEnd ℂ) w₂) := by
    calc quartetFactor σ γ (2 * w) * _
        = ((1 - (2 * w) * (1 - 2 * w) / (quartetZero σ γ * (1 - quartetZero σ γ))) *
            (quartetZero σ γ * (1 - quartetZero σ γ))) *
          ((1 - (2 * w) * (1 - 2 * w) /
            ((starRingEnd ℂ) (quartetZero σ γ) * (1 - (starRingEnd ℂ) (quartetZero σ γ)))) *
            ((starRingEnd ℂ) (quartetZero σ γ) * (1 - (starRingEnd ℂ) (quartetZero σ γ)))) := by
            unfold quartetFactor; ring
      _ = _ := by rw [hp1, hp2]; ring
  have hsym_den : quartetFactor σ γ (1 + 2 * w) = quartetFactor σ γ (2 * (-w)) := by
    have hq_sym : (1 + 2 * w) * (1 - (1 + 2 * w)) = (2 * (-w)) * (1 - 2 * (-w)) := by ring
    unfold quartetFactor; rw [hq_sym]
  have hp1_neg : (1 - (2 * (-w)) * (1 - 2 * (-w)) / (quartetZero σ γ * (1 - quartetZero σ γ))) *
      (quartetZero σ γ * (1 - quartetZero σ γ)) = 4 * (-w - (starRingEnd ℂ) w₁) * (-w - w₂) := by
    rw [sub_mul, one_mul, div_mul_cancel₀ _ hq1]
    simp only [w₁, w₂, quartetZero, map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
    push_cast; ring
  have hp2_neg : (1 - (2 * (-w)) * (1 - 2 * (-w)) /
      ((starRingEnd ℂ) (quartetZero σ γ) * (1 - (starRingEnd ℂ) (quartetZero σ γ)))) *
      ((starRingEnd ℂ) (quartetZero σ γ) * (1 - (starRingEnd ℂ) (quartetZero σ γ))) =
      4 * (-w - w₁) * (-w - (starRingEnd ℂ) w₂) := by
    rw [sub_mul, one_mul, div_mul_cancel₀ _ hq2]
    simp only [w₁, w₂, quartetZero, map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
    push_cast; ring
  have hden' : quartetFactor σ γ (1 + 2 * w) *
      ((quartetZero σ γ * (1 - quartetZero σ γ)) *
        ((starRingEnd ℂ) (quartetZero σ γ) * (1 - (starRingEnd ℂ) (quartetZero σ γ)))) =
      16 * (w + (starRingEnd ℂ) w₁) * (w + w₁) * (w + (starRingEnd ℂ) w₂) * (w + w₂) := by
    rw [hsym_den]
    calc quartetFactor σ γ (2 * (-w)) * _
        = ((1 - (2 * (-w)) * (1 - 2 * (-w)) / (quartetZero σ γ * (1 - quartetZero σ γ))) *
            (quartetZero σ γ * (1 - quartetZero σ γ))) *
          ((1 - (2 * (-w)) * (1 - 2 * (-w)) /
            ((starRingEnd ℂ) (quartetZero σ γ) * (1 - (starRingEnd ℂ) (quartetZero σ γ)))) *
            ((starRingEnd ℂ) (quartetZero σ γ) * (1 - (starRingEnd ℂ) (quartetZero σ γ)))) := by
            unfold quartetFactor; ring
      _ = _ := by rw [hp1_neg, hp2_neg]; ring
  refine ⟨hnum', hden', ?_⟩
  have hprod_ne : (quartetZero σ γ * (1 - quartetZero σ γ)) *
      ((starRingEnd ℂ) (quartetZero σ γ) * (1 - (starRingEnd ℂ) (quartetZero σ γ))) ≠ 0 :=
    mul_ne_zero hq1 hq2
  rw [quartetGate, ← mul_div_mul_right _ _ hprod_ne, hnum', hden']
  have h16 : (16 : ℂ) ≠ 0 := by norm_num
  calc (16 * (w - w₁) * (w - (starRingEnd ℂ) w₁) * (w - w₂) * (w - (starRingEnd ℂ) w₂)) /
          (16 * (w + (starRingEnd ℂ) w₁) * (w + w₁) * (w + (starRingEnd ℂ) w₂) * (w + w₂))
      = (16 * ((w - w₁) * (w - (starRingEnd ℂ) w₁) * (w - w₂) * (w - (starRingEnd ℂ) w₂))) /
          (16 * ((w + (starRingEnd ℂ) w₁) * (w + w₁) * (w + (starRingEnd ℂ) w₂) * (w + w₂))) := by
          congr 1 <;> ring
    _ = ((w - w₁) * (w - (starRingEnd ℂ) w₁) * (w - w₂) * (w - (starRingEnd ℂ) w₂)) /
          ((w + (starRingEnd ℂ) w₁) * (w + w₁) * (w + (starRingEnd ℂ) w₂) * (w + w₂)) :=
          mul_div_mul_left _ _ h16
    _ = _ := by simp only [div_mul_div_comm]

private theorem elem_blaschke_schur_and_axis {z w : ℂ} (hz : 0 < z.re) :
    (0 ≤ w.re → w + (starRingEnd ℂ) z ≠ 0 ∧ ‖(w - z) / (w + (starRingEnd ℂ) z)‖ ≤ 1) ∧
    (w.re = 0 → ‖(w - z) / (w + (starRingEnd ℂ) z)‖ = 1) := by
  have hne : 0 ≤ w.re → w + (starRingEnd ℂ) z ≠ 0 := fun hw h0 => by
    have hre := congrArg Complex.re h0
    simp at hre; linarith
  have hdiff : Complex.normSq (w + (starRingEnd ℂ) z) - Complex.normSq (w - z) = 4 * w.re * z.re := by
    simp [Complex.normSq_apply]; ring
  refine ⟨fun hw => ⟨hne hw, ?_⟩, fun hw0 => ?_⟩
  · rw [norm_div, div_le_one (norm_pos_iff.mpr (hne hw))]
    have hle : ‖w - z‖ ^ 2 ≤ ‖w + (starRingEnd ℂ) z‖ ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
      nlinarith [mul_nonneg hw hz.le]
    nlinarith [norm_nonneg (w - z), norm_nonneg (w + (starRingEnd ℂ) z)]
  · have hn := hne (by linarith)
    rw [norm_div, div_eq_one_iff_eq (norm_ne_zero_iff.mpr hn)]
    have heq2 : ‖w - z‖ ^ 2 = ‖w + (starRingEnd ℂ) z‖ ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
      rw [hw0] at hdiff; linarith
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp heq2

theorem quartet_schur_and_unitary {σ γ : ℝ} (h0 : 1 / 2 < σ) (h1 : σ < 1) (hγ : 0 < γ) :
    (∀ w : ℂ, 0 ≤ w.re →
      xiQuartet σ γ (1 + 2 * w) ≠ 0 ∧
      ‖quartetGate σ γ w‖ ≤ 1 ∧
      ‖quartetReducedScattering σ γ w‖ ≤ 1 ∧
      0 ≤ ((1 - quartetReducedScattering σ γ w) / (1 + quartetReducedScattering σ γ w)).re) ∧
    (∀ t : ℝ, ‖quartetGate σ γ ((t : ℂ) * I)‖ = 1 ∧
      ‖quartetScatteringPhase σ γ ((t : ℂ) * I)‖ = 1) := by
  set w₁ : ℂ := (((1 - σ) / 2 : ℝ) : ℂ) + ((γ / 2 : ℝ) : ℂ) * I
  set w₂ : ℂ := ((σ / 2 : ℝ) : ℂ) + ((γ / 2 : ℝ) : ℂ) * I
  have hw₁ : 0 < w₁.re := by simp [w₁]; linarith
  have hw₂ : 0 < w₂.re := by simp [w₂]; linarith
  have hw₁c : 0 < ((starRingEnd ℂ) w₁).re := by rw [Complex.conj_re]; exact hw₁
  have hw₂c : 0 < ((starRingEnd ℂ) w₂).re := by rw [Complex.conj_re]; exact hw₂
  refine ⟨fun w hw => ?_, fun t => ?_⟩
  · obtain ⟨_, hden, hgate⟩ := quartetGate_eq_blaschke_four h0 h1 hγ w
    obtain ⟨hn1, hb1⟩ := (elem_blaschke_schur_and_axis (z := w₁) (w := w) hw₁).1 hw
    obtain ⟨hn2, hb2⟩ := (elem_blaschke_schur_and_axis (z := (starRingEnd ℂ) w₁) (w := w) hw₁c).1 hw
    obtain ⟨hn3, hb3⟩ := (elem_blaschke_schur_and_axis (z := w₂) (w := w) hw₂).1 hw
    obtain ⟨hn4, hb4⟩ := (elem_blaschke_schur_and_axis (z := (starRingEnd ℂ) w₂) (w := w) hw₂c).1 hw
    simp only [RingHomCompTriple.comp_apply, RingHom.id_apply] at hn2 hb2 hn4 hb4
    have hfac_ne : quartetFactor σ γ (1 + 2 * w) ≠ 0 := fun hz => by
      rw [hz, zero_mul] at hden
      have hrhs : 16 * (w + (starRingEnd ℂ) w₁) * (w + w₁) * (w + (starRingEnd ℂ) w₂) * (w + w₂) ≠ 0 :=
        mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hn1) hn2) hn3) hn4
      exact hrhs hden.symm
    have hxi_ne : xiQuartet σ γ (1 + 2 * w) ≠ 0 :=
      mul_ne_zero hfac_ne (xi_ne_zero_of_one_le_re (by simp; linarith))
    have hg_le : ‖quartetGate σ γ w‖ ≤ 1 := by
      rw [hgate, norm_mul, norm_mul, norm_mul]
      have h12 : ‖(w - w₁) / (w + (starRingEnd ℂ) w₁)‖ * ‖(w - (starRingEnd ℂ) w₁) / (w + w₁)‖ ≤ 1 :=
        (mul_le_mul hb1 hb2 (norm_nonneg _) zero_le_one).trans_eq (mul_one 1)
      have h123 : ‖(w - w₁) / (w + (starRingEnd ℂ) w₁)‖ * ‖(w - (starRingEnd ℂ) w₁) / (w + w₁)‖ *
          ‖(w - w₂) / (w + (starRingEnd ℂ) w₂)‖ ≤ 1 :=
        (mul_le_mul h12 hb3 (norm_nonneg _) zero_le_one).trans_eq (mul_one 1)
      exact (mul_le_mul h123 hb4 (norm_nonneg _) zero_le_one).trans_eq (mul_one 1)
    have hred_eq : quartetReducedScattering σ γ w = quartetGate σ γ w * modularReducedScattering w := by
      unfold quartetReducedScattering xiQuartet quartetGate modularReducedScattering
      ring
    have hred_le : ‖quartetReducedScattering σ γ w‖ ≤ 1 := by
      rw [hred_eq, norm_mul]
      exact (mul_le_mul hg_le (norm_modularReducedScattering_le_one hw)
        (norm_nonneg _) zero_le_one).trans_eq (mul_one 1)
    have hherg : 0 ≤ ((1 - quartetReducedScattering σ γ w) / (1 + quartetReducedScattering σ γ w)).re := by
      set S := quartetReducedScattering σ γ w
      have hn : Complex.normSq S ≤ 1 := by
        rw [Complex.normSq_eq_norm_sq]; nlinarith [norm_nonneg S]
      by_cases hd : 1 + S = 0
      · rw [hd, div_zero, Complex.zero_re]
      · rw [Complex.div_re, ← add_div]
        have he : (1 - S).re * (1 + S).re + (1 - S).im * (1 + S).im = 1 - Complex.normSq S := by
          simp [Complex.normSq_apply]; ring
        rw [he]
        exact div_nonneg (sub_nonneg.mpr hn) (Complex.normSq_nonneg _)
    exact ⟨hxi_ne, hg_le, hred_le, hherg⟩
  · set w : ℂ := (t : ℂ) * I
    have hw0 : w.re = 0 := by simp [w]
    obtain ⟨_, _, hgate⟩ := quartetGate_eq_blaschke_four h0 h1 hγ w
    have hu1 := (elem_blaschke_schur_and_axis (z := w₁) (w := w) hw₁).2 hw0
    have hu2 := (elem_blaschke_schur_and_axis (z := (starRingEnd ℂ) w₁) (w := w) hw₁c).2 hw0
    have hu3 := (elem_blaschke_schur_and_axis (z := w₂) (w := w) hw₂).2 hw0
    have hu4 := (elem_blaschke_schur_and_axis (z := (starRingEnd ℂ) w₂) (w := w) hw₂c).2 hw0
    simp only [RingHomCompTriple.comp_apply, RingHom.id_apply] at hu2 hu4
    have hg1 : ‖quartetGate σ γ w‖ = 1 := by
      rw [hgate, norm_mul, norm_mul, norm_mul, hu1, hu2, hu3, hu4]; norm_num
    have hph_eq : quartetScatteringPhase σ γ w = quartetGate σ γ w * modularScatteringPhase w := by
      unfold quartetScatteringPhase quartetReducedScattering xiQuartet quartetGate
        modularScatteringPhase
      ring
    exact ⟨hg1, by rw [hph_eq, norm_mul, hg1, norm_modularScatteringPhase_axis t, one_mul]⟩

/-- Retarded four-pole exponential tail of `quartetGate σ γ` on `u > 0`, obtained from the product
of the two conjugate Blaschke pairs. -/
def quartetImpulseTail (σ γ : ℝ) (u : ℝ) : ℂ :=
  if 0 < u then
    let a₁ : ℝ := (1 - σ) / 2
    let a₂ : ℝ := σ / 2
    let b : ℝ := γ / 2
    let p₁ : ℂ := -((a₁ : ℂ)) + (b : ℂ) * I
    let p₂ : ℂ := -((a₁ : ℂ)) - (b : ℂ) * I
    let p₃ : ℂ := -((a₂ : ℂ)) + (b : ℂ) * I
    let p₄ : ℂ := -((a₂ : ℂ)) - (b : ℂ) * I
    let c₁ : ℂ := -(4 * (a₁ : ℂ) * p₁) / (2 * I * (b : ℂ))
    let c₂ : ℂ := (4 * (a₁ : ℂ) * p₂) / (2 * I * (b : ℂ))
    let d₁ : ℂ := -(4 * (a₂ : ℂ) * p₃) / (2 * I * (b : ℂ))
    let d₂ : ℂ := (4 * (a₂ : ℂ) * p₄) / (2 * I * (b : ℂ))
    let R₁ : ℂ := c₁ * (1 + d₁ / (p₁ - p₃) + d₂ / (p₁ - p₄))
    let R₂ : ℂ := c₂ * (1 + d₁ / (p₂ - p₃) + d₂ / (p₂ - p₄))
    let R₃ : ℂ := d₁ * (1 + c₁ / (p₃ - p₁) + c₂ / (p₃ - p₂))
    let R₄ : ℂ := d₂ * (1 + c₁ / (p₄ - p₁) + c₂ / (p₄ - p₂))
    R₁ * Complex.exp (p₁ * (u : ℂ)) + R₂ * Complex.exp (p₂ * (u : ℂ)) +
      R₃ * Complex.exp (p₃ * (u : ℂ)) + R₄ * Complex.exp (p₄ * (u : ℂ))
  else 0

/-- Retarded causal echo kernel of `xiQuartet σ γ`: prompt `echoKernel` plus causal convolution with
`quartetImpulseTail σ γ`. -/
def quartetEchoKernel (σ γ : ℝ) (τ : ℝ) : ℂ :=
  ((echoKernel τ : ℝ) : ℂ) +
    ∫ u : ℝ, quartetImpulseTail σ γ u * ((echoKernel (τ - u) : ℝ) : ℂ)

/-- **Strict Retarded Causality of `quartetEchoKernel`.** -/
theorem quartetEchoKernel_eq_zero_of_nonpos (σ γ : ℝ) {τ : ℝ} (hτ : τ ≤ 0) :
    quartetEchoKernel σ γ τ = 0 := by
  rw [quartetEchoKernel, echoKernel_eq_zero_of_nonpos hτ, Complex.ofReal_zero, zero_add]
  refine integral_eq_zero_of_ae (Eventually.of_forall fun u => ?_)
  dsimp only [Pi.zero_apply]
  rcases le_or_gt u 0 with hu | hu
  · simp [quartetImpulseTail, not_lt.mpr hu]
  · rw [echoKernel_eq_zero_of_nonpos (by linarith : τ - u ≤ 0)]
    simp

private theorem integral_Ioi_cexp_rate {z : ℂ} (hz : z.re < 0) :
    IntegrableOn (fun u : ℝ => Complex.exp (z * (u : ℂ))) (Ioi (0 : ℝ)) ∧
      (∫ u in Ioi (0 : ℝ), Complex.exp (z * (u : ℂ))) = (-z)⁻¹ := by
  have hz0 : z ≠ 0 := fun h0 => by rw [h0, Complex.zero_re] at hz; exact lt_irrefl 0 hz
  have hmeas : Measurable fun u : ℝ => Complex.exp (z * (u : ℂ)) := by fun_prop
  have hint : IntegrableOn (fun u : ℝ => Complex.exp (z * (u : ℂ))) (Ioi (0 : ℝ)) := by
    refine (integrableOn_exp_mul_Ioi hz 0).mono' hmeas.aestronglyMeasurable
      (Eventually.of_forall fun u => le_of_eq ?_)
    rw [Complex.norm_exp, Complex.re_mul_ofReal]
  refine ⟨hint, ?_⟩
  have hderiv : ∀ u : ℝ,
      HasDerivAt (fun s : ℝ => -(-z)⁻¹ * Complex.exp (z * (s : ℂ)))
        (Complex.exp (z * (u : ℂ))) u := by
    intro u
    have h1 : HasDerivAt (fun s : ℝ => z * (s : ℂ)) z u := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := u)).const_mul z
    refine (h1.cexp.const_mul (-(-z)⁻¹)).congr_deriv ?_
    rw [inv_neg, neg_neg, show z⁻¹ * (Complex.exp (z * (u : ℂ)) * z) =
      (z * z⁻¹) * Complex.exp (z * (u : ℂ)) by ring, mul_inv_cancel₀ hz0, one_mul]
  have hlim : Tendsto (fun s : ℝ => -(-z)⁻¹ * Complex.exp (z * (s : ℂ))) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have htop : Tendsto (fun s : ℝ => (-z.re) * s) atTop atTop :=
      Filter.Tendsto.const_mul_atTop (neg_pos.mpr hz) tendsto_id
    have hneg : Tendsto (fun s : ℝ => -(z.re * s)) atTop atTop :=
      htop.congr fun s => by ring
    have hbot : Tendsto (fun s : ℝ => z.re * s) atTop atBot :=
      (tendsto_neg_atBot_iff.mpr hneg).congr fun s => neg_neg (z.re * s)
    have hexp : Tendsto (fun s : ℝ => Real.exp (z.re * s)) atTop (𝓝 0) :=
      Real.tendsto_exp_atBot.comp hbot
    have hmul0 := hexp.const_mul ‖(-(-z)⁻¹ : ℂ)‖
    rw [mul_zero] at hmul0
    exact hmul0.congr fun s => by rw [norm_mul, Complex.norm_exp, Complex.re_mul_ofReal]
  rw [integral_Ioi_of_hasDerivAt_of_tendsto (hderiv 0).continuousAt.continuousWithinAt
    (fun u _ => hderiv u) hint hlim]
  simp

private theorem integral_add₄ {f₁ f₂ f₃ f₄ : ℝ → ℂ}
    (h₁ : Integrable f₁) (h₂ : Integrable f₂) (h₃ : Integrable f₃) (h₄ : Integrable f₄) :
    (∫ x : ℝ, f₁ x + f₂ x + f₃ x + f₄ x) =
      (∫ x : ℝ, f₁ x) + (∫ x : ℝ, f₂ x) + (∫ x : ℝ, f₃ x) + (∫ x : ℝ, f₄ x) := by
  have h12 : Integrable (fun x : ℝ => f₁ x + f₂ x) := h₁.add h₂
  have h123 : Integrable (fun x : ℝ => f₁ x + f₂ x + f₃ x) := h12.add h₃
  rw [integral_add h123 h₄, integral_add h12 h₃, integral_add h₁ h₂]

private theorem integral_add₅ {f₀ f₁ f₂ f₃ f₄ : ℝ → ℂ}
    (h₀ : Integrable f₀) (h₁ : Integrable f₁) (h₂ : Integrable f₂)
    (h₃ : Integrable f₃) (h₄ : Integrable f₄) :
    (∫ x : ℝ, f₀ x + f₁ x + f₂ x + f₃ x + f₄ x) =
      (∫ x : ℝ, f₀ x) + (∫ x : ℝ, f₁ x) + (∫ x : ℝ, f₂ x) + (∫ x : ℝ, f₃ x) + (∫ x : ℝ, f₄ x) := by
  have h0123 : Integrable (fun x : ℝ => f₀ x + f₁ x + f₂ x + f₃ x) :=
    ((h₀.add h₁).add h₂).add h₃
  rw [integral_add h0123 h₄, integral_add₄ h₀ h₁ h₂ h₃]

/-- **Laplace Transform of `quartetEchoKernel`.** On `Re w > 1/2`, `quartetEchoKernel σ γ`
transforms to `quartetGate σ γ w * (Λ(2w)/Λ(2w + 1))`. -/
theorem laplace_quartetEchoKernel {σ γ : ℝ} (h0 : 1 / 2 < σ) (h1 : σ < 1) (hγ : 0 < γ)
    {w : ℂ} (hw : 1 / 2 < w.re) :
    (∫ τ : ℝ, Complex.exp (-w * (τ : ℂ)) * quartetEchoKernel σ γ τ) =
      quartetGate σ γ w * (completedRiemannZeta (2 * w) / completedRiemannZeta (2 * w + 1)) := by
  set a₁ : ℝ := (1 - σ) / 2
  set a₂ : ℝ := σ / 2
  set b : ℝ := γ / 2
  have ha₁ : 0 < a₁ := by dsimp only [a₁]; linarith
  have ha₂ : 0 < a₂ := by dsimp only [a₂]; linarith
  have hb : 0 < b := by dsimp only [b]; linarith
  set p₁ : ℂ := -(a₁ : ℂ) + (b : ℂ) * I
  set p₂ : ℂ := -(a₁ : ℂ) - (b : ℂ) * I
  set p₃ : ℂ := -(a₂ : ℂ) + (b : ℂ) * I
  set p₄ : ℂ := -(a₂ : ℂ) - (b : ℂ) * I
  set c₁ : ℂ := -(4 * (a₁ : ℂ) * p₁) / (2 * I * (b : ℂ))
  set c₂ : ℂ := (4 * (a₁ : ℂ) * p₂) / (2 * I * (b : ℂ))
  set d₁ : ℂ := -(4 * (a₂ : ℂ) * p₃) / (2 * I * (b : ℂ))
  set d₂ : ℂ := (4 * (a₂ : ℂ) * p₄) / (2 * I * (b : ℂ))
  set R₁ : ℂ := c₁ * (1 + d₁ / (p₁ - p₃) + d₂ / (p₁ - p₄))
  set R₂ : ℂ := c₂ * (1 + d₁ / (p₂ - p₃) + d₂ / (p₂ - p₄))
  set R₃ : ℂ := d₁ * (1 + c₁ / (p₃ - p₁) + c₂ / (p₃ - p₂))
  set R₄ : ℂ := d₂ * (1 + c₁ / (p₄ - p₁) + c₂ / (p₄ - p₂))
  -- Single-pole convolution Laplace lemma
  have hpole_lap : ∀ p_z : ℂ, p_z.re < 0 →
      Integrable (fun τ : ℝ => Complex.exp (-w * (τ : ℂ)) *
        ∫ u : ℝ, (if 0 < u then Complex.exp (p_z * (u : ℂ)) else 0) *
          ((echoKernel (τ - u) : ℝ) : ℂ)) ∧
      (∫ τ : ℝ, Complex.exp (-w * (τ : ℂ)) *
        ∫ u : ℝ, (if 0 < u then Complex.exp (p_z * (u : ℂ)) else 0) *
          ((echoKernel (τ - u) : ℝ) : ℂ)) =
        (w - p_z)⁻¹ * (completedRiemannZeta (2 * w) / completedRiemannZeta (2 * w + 1)) := by
    intro p_z hpz
    have hre_diff : (p_z - w).re < 0 := by simp; linarith
    obtain ⟨h_exp_i, h_exp_val⟩ := integral_Ioi_cexp_rate hre_diff
    have hint_K := integrable_cexp_mul_echoKernel hw
    set g₁ : ℝ → ℂ := (Ioi (0 : ℝ)).indicator (fun u => Complex.exp ((p_z - w) * (u : ℂ)))
    set g₂ : ℝ → ℂ := fun v => Complex.exp (-w * (v : ℂ)) * ((echoKernel v : ℝ) : ℂ)
    have hg₁_int : Integrable g₁ := (integrable_indicator_iff measurableSet_Ioi).mpr h_exp_i
    have hconv_i : Integrable (fun p : ℝ × ℝ => g₁ p.2 * g₂ (p.1 - p.2)) (volume.prod volume) := by
      simpa using hg₁_int.convolution_integrand (ContinuousLinearMap.mul ℂ ℂ) hint_K
    have hpt_eq : ∀ τ u : ℝ,
        Complex.exp (-w * (τ : ℂ)) *
          ((if 0 < u then Complex.exp (p_z * (u : ℂ)) else 0) * ((echoKernel (τ - u) : ℝ) : ℂ)) =
        g₁ u * g₂ (τ - u) := by
      intro τ u
      rcases le_or_gt u 0 with hu | hu
      · simp [g₁, not_lt.mpr hu]
      · simp only [if_pos hu, g₁, indicator_of_mem (mem_Ioi.mpr hu), g₂]
        have he : Complex.exp (-w * (τ : ℂ)) * Complex.exp (p_z * (u : ℂ)) =
            Complex.exp ((p_z - w) * (u : ℂ)) * Complex.exp (-w * ((τ - u : ℝ) : ℂ)) := by
          rw [← Complex.exp_add, ← Complex.exp_add]; congr 1; push_cast; ring
        linear_combination ((echoKernel (τ - u) : ℝ) : ℂ) * he
    have hint_τ : Integrable fun τ : ℝ => Complex.exp (-w * (τ : ℂ)) *
        ∫ u : ℝ, (if 0 < u then Complex.exp (p_z * (u : ℂ)) else 0) *
          ((echoKernel (τ - u) : ℝ) : ℂ) := by
      refine hconv_i.integral_prod_left.congr (Eventually.of_forall fun τ => ?_)
      dsimp only
      rw [← integral_const_mul]
      exact integral_congr_ae (Eventually.of_forall fun u => (hpt_eq τ u).symm)
    refine ⟨hint_τ, ?_⟩
    have hswap := integral_integral_swap (f := fun τ u => g₁ u * g₂ (τ - u)) hconv_i
    have hlhs : (∫ τ : ℝ, Complex.exp (-w * (τ : ℂ)) *
        ∫ u : ℝ, (if 0 < u then Complex.exp (p_z * (u : ℂ)) else 0) *
          ((echoKernel (τ - u) : ℝ) : ℂ)) = ∫ τ : ℝ, ∫ u : ℝ, g₁ u * g₂ (τ - u) := by
      refine integral_congr_ae (Eventually.of_forall fun τ => ?_)
      dsimp only
      rw [← integral_const_mul]
      exact integral_congr_ae (Eventually.of_forall fun u => hpt_eq τ u)
    rw [hlhs, hswap]
    have hinner : ∀ u : ℝ, (∫ τ : ℝ, g₁ u * g₂ (τ - u)) =
        g₁ u * (completedRiemannZeta (2 * w) / completedRiemannZeta (2 * w + 1)) := by
      intro u
      rw [integral_const_mul, integral_sub_right_eq_self (μ := volume) g₂ u,
        integral_cexp_mul_echoKernel_eq_completed hw]
    simp_rw [hinner]
    rw [integral_mul_const, integral_indicator measurableSet_Ioi, h_exp_val,
      show -(p_z - w) = w - p_z by ring]
  have hp₁_re : p₁.re < 0 := by simp [p₁]; linarith [ha₁]
  have hp₂_re : p₂.re < 0 := by simp [p₂]; linarith [ha₁]
  have hp₃_re : p₃.re < 0 := by simp [p₃]; linarith [ha₂]
  have hp₄_re : p₄.re < 0 := by simp [p₄]; linarith [ha₂]
  obtain ⟨hi1, hv1⟩ := hpole_lap p₁ hp₁_re
  obtain ⟨hi2, hv2⟩ := hpole_lap p₂ hp₂_re
  obtain ⟨hi3, hv3⟩ := hpole_lap p₃ hp₃_re
  obtain ⟨hi4, hv4⟩ := hpole_lap p₄ hp₄_re
  -- Expand `quartetEchoKernel` into `echoKernel` + 4 single-pole convolutions
  have hker_split : ∀ τ : ℝ, Complex.exp (-w * (τ : ℂ)) * quartetEchoKernel σ γ τ =
      Complex.exp (-w * (τ : ℂ)) * ((echoKernel τ : ℝ) : ℂ) +
      R₁ * (Complex.exp (-w * (τ : ℂ)) *
        ∫ u : ℝ, (if 0 < u then Complex.exp (p₁ * (u : ℂ)) else 0) * ((echoKernel (τ - u) : ℝ) : ℂ)) +
      R₂ * (Complex.exp (-w * (τ : ℂ)) *
        ∫ u : ℝ, (if 0 < u then Complex.exp (p₂ * (u : ℂ)) else 0) * ((echoKernel (τ - u) : ℝ) : ℂ)) +
      R₃ * (Complex.exp (-w * (τ : ℂ)) *
        ∫ u : ℝ, (if 0 < u then Complex.exp (p₃ * (u : ℂ)) else 0) * ((echoKernel (τ - u) : ℝ) : ℂ)) +
      R₄ * (Complex.exp (-w * (τ : ℂ)) *
        ∫ u : ℝ, (if 0 < u then Complex.exp (p₄ * (u : ℂ)) else 0) * ((echoKernel (τ - u) : ℝ) : ℂ)) := by
    intro τ
    have hu_int : ∀ p_z : ℂ, p_z.re < 0 →
        Integrable fun u : ℝ => (if 0 < u then Complex.exp (p_z * (u : ℂ)) else 0) *
          ((echoKernel (τ - u) : ℝ) : ℂ) := by
      intro p_z _
      rcases le_or_gt τ 0 with hτ0 | hτ0
      · refine integrable_zero _ _ _ |>.congr (Eventually.of_forall fun u => ?_)
        dsimp only
        rcases le_or_gt u 0 with hu | hu
        · simp [not_lt.mpr hu]
        · rw [echoKernel_eq_zero_of_nonpos (by linarith : τ - u ≤ 0)]; simp
      · -- For `τ > 0`, `u` is supported in `(0, τ)`, and `echoKernel (τ - u)` is integrable via
        -- `e^{w(τ - u)}` weight!
        have hw_k := (integrable_cexp_mul_echoKernel hw).norm.comp_sub_left τ
        have hm : Measurable fun u : ℝ => (if 0 < u then Complex.exp (p_z * (u : ℂ)) else 0) *
            ((echoKernel (τ - u) : ℝ) : ℂ) :=
          (Measurable.ite measurableSet_Ioi (by fun_prop) measurable_const).mul
            (Complex.measurable_ofReal.comp (measurable_echoKernel.comp (measurable_const.sub measurable_id)))
        refine (hw_k.const_mul (Real.exp (w.re * τ))).mono' hm.aestronglyMeasurable
          (Eventually.of_forall fun u => ?_)
        rcases le_or_gt u 0 with hu | hu
        · simp [not_lt.mpr hu]; positivity
        · rcases le_or_gt (τ - u) 0 with htu | htu
          · simp [echoKernel_eq_zero_of_nonpos htu]
          · rw [if_pos hu, norm_mul, Complex.norm_exp, norm_mul, Complex.norm_exp,
              Complex.re_mul_ofReal, Complex.re_mul_ofReal, Complex.neg_re,
              ← mul_assoc, ← Real.exp_add]
            refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_) (norm_nonneg _)
            have hpz_neg : p_z.re ≤ 0 := by linarith [‹p_z.re < 0›]
            nlinarith
    have hu1 := (hu_int p₁ hp₁_re).const_mul R₁
    have hu2 := (hu_int p₂ hp₂_re).const_mul R₂
    have hu3 := (hu_int p₃ hp₃_re).const_mul R₃
    have hu4 := (hu_int p₄ hp₄_re).const_mul R₄
    have htail_pt : ∀ u : ℝ, quartetImpulseTail σ γ u * ((echoKernel (τ - u) : ℝ) : ℂ) =
        R₁ * ((if 0 < u then Complex.exp (p₁ * (u : ℂ)) else 0) * ((echoKernel (τ - u) : ℝ) : ℂ)) +
        R₂ * ((if 0 < u then Complex.exp (p₂ * (u : ℂ)) else 0) * ((echoKernel (τ - u) : ℝ) : ℂ)) +
        R₃ * ((if 0 < u then Complex.exp (p₃ * (u : ℂ)) else 0) * ((echoKernel (τ - u) : ℝ) : ℂ)) +
        R₄ * ((if 0 < u then Complex.exp (p₄ * (u : ℂ)) else 0) * ((echoKernel (τ - u) : ℝ) : ℂ)) := by
      intro u
      rcases le_or_gt u 0 with hu | hu
      · simp [quartetImpulseTail, not_lt.mpr hu]
      · simp only [quartetImpulseTail, if_pos hu]
        dsimp only [a₁, a₂, b, p₁, p₂, p₃, p₄, c₁, c₂, d₁, d₂, R₁, R₂, R₃, R₄]
        ring
    rw [quartetEchoKernel, mul_add, integral_congr_ae (Eventually.of_forall htail_pt),
      integral_add₄ hu1 hu2 hu3 hu4, integral_const_mul, integral_const_mul, integral_const_mul,
      integral_const_mul]
    ring
  have hint0 := integrable_cexp_mul_echoKernel hw
  rw [integral_congr_ae (Eventually.of_forall hker_split),
    integral_add₅ hint0 (hi1.const_mul R₁) (hi2.const_mul R₂) (hi3.const_mul R₃) (hi4.const_mul R₄),
    integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul,
    integral_cexp_mul_echoKernel_eq_completed hw, hv1, hv2, hv3, hv4]
  -- Identify `1 + ∑ R_j (w - p_j)⁻¹ = quartetGate σ γ w` by 2-pair partial fractions
  have hgate_pf : 1 + R₁ * (w - p₁)⁻¹ + R₂ * (w - p₂)⁻¹ + R₃ * (w - p₃)⁻¹ + R₄ * (w - p₄)⁻¹ =
      quartetGate σ γ w := by
    obtain ⟨_, _, hgate4⟩ := quartetGate_eq_blaschke_four h0 h1 hγ w
    set w₁ : ℂ := (a₁ : ℂ) + (b : ℂ) * I
    set w₂ : ℂ := (a₂ : ℂ) + (b : ℂ) * I
    have hib : 2 * I * (b : ℂ) ≠ 0 :=
      mul_ne_zero (mul_ne_zero two_ne_zero I_ne_zero) (Complex.ofReal_ne_zero.mpr hb.ne')
    have hwp : ∀ p_z : ℂ, p_z.re < 0 → w - p_z ≠ 0 := fun p_z hpz h0' => by
      have := congrArg Complex.re h0'; simp at this; linarith
    have hw1 := hwp p₁ hp₁_re
    have hw2 := hwp p₂ hp₂_re
    have hw3 := hwp p₃ hp₃_re
    have hw4 := hwp p₄ hp₄_re
    -- Conjugate-pair partial-fraction identity
    have hpair : ∀ (a : ℝ),
        let w_z : ℂ := (a : ℂ) + (b : ℂ) * I
        let q₁ : ℂ := -(a : ℂ) + (b : ℂ) * I
        let q₂ : ℂ := -(a : ℂ) - (b : ℂ) * I
        w - q₁ ≠ 0 → w - q₂ ≠ 0 →
        ((w - w_z) / (w + (starRingEnd ℂ) w_z)) * ((w - (starRingEnd ℂ) w_z) / (w + w_z)) =
          1 + (-(4 * (a : ℂ) * q₁) / (2 * I * (b : ℂ))) * (w - q₁)⁻¹ +
            ((4 * (a : ℂ) * q₂) / (2 * I * (b : ℂ))) * (w - q₂)⁻¹ := by
      intro a w_z q₁ q₂ hq1' hq2'
      have hd1 : w + (starRingEnd ℂ) w_z = w - q₁ := by
        simp [w_z, q₁, map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]; ring
      have hd2 : w + w_z = w - q₂ := by simp [w_z, q₂]; ring
      rw [hd1, hd2, div_mul_div_comm]
      apply mul_right_cancel₀ (mul_ne_zero (mul_ne_zero hq1' hq2') hib)
      have hlhs : ((w - w_z) * (w - (starRingEnd ℂ) w_z) / ((w - q₁) * (w - q₂))) *
          (((w - q₁) * (w - q₂)) * (2 * I * (b : ℂ))) =
          (w - w_z) * (w - (starRingEnd ℂ) w_z) * (2 * I * (b : ℂ)) := by
        rw [← mul_assoc, div_mul_cancel₀ _ (mul_ne_zero hq1' hq2')]
      have hrhs1 : (-(4 * (a : ℂ) * q₁) / (2 * I * (b : ℂ))) * (w - q₁)⁻¹ *
          (((w - q₁) * (w - q₂)) * (2 * I * (b : ℂ))) =
          -(4 * (a : ℂ) * q₁) * (w - q₂) := by
        calc (-(4 * (a : ℂ) * q₁) / (2 * I * (b : ℂ))) * (w - q₁)⁻¹ *
                (((w - q₁) * (w - q₂)) * (2 * I * (b : ℂ)))
            = ((-(4 * (a : ℂ) * q₁) / (2 * I * (b : ℂ))) * (2 * I * (b : ℂ))) *
                ((w - q₁)⁻¹ * (w - q₁)) * (w - q₂) := by ring
          _ = -(4 * (a : ℂ) * q₁) * (w - q₂) := by
                rw [div_mul_cancel₀ _ hib, inv_mul_cancel₀ hq1', mul_one]
      have hrhs2 : ((4 * (a : ℂ) * q₂) / (2 * I * (b : ℂ))) * (w - q₂)⁻¹ *
          (((w - q₁) * (w - q₂)) * (2 * I * (b : ℂ))) =
          (4 * (a : ℂ) * q₂) * (w - q₁) := by
        calc ((4 * (a : ℂ) * q₂) / (2 * I * (b : ℂ))) * (w - q₂)⁻¹ *
                (((w - q₁) * (w - q₂)) * (2 * I * (b : ℂ)))
            = (((4 * (a : ℂ) * q₂) / (2 * I * (b : ℂ))) * (2 * I * (b : ℂ))) *
                ((w - q₂)⁻¹ * (w - q₂)) * (w - q₁) := by ring
          _ = (4 * (a : ℂ) * q₂) * (w - q₁) := by
                rw [div_mul_cancel₀ _ hib, inv_mul_cancel₀ hq2', mul_one]
      rw [hlhs, add_mul, add_mul, one_mul, hrhs1, hrhs2]
      simp only [w_z, q₁, q₂, map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
      ring
    have hpair1 : ((w - w₁) / (w + (starRingEnd ℂ) w₁)) * ((w - (starRingEnd ℂ) w₁) / (w + w₁)) =
        1 + c₁ * (w - p₁)⁻¹ + c₂ * (w - p₂)⁻¹ := hpair a₁ hw1 hw2
    have hpair2 : ((w - w₂) / (w + (starRingEnd ℂ) w₂)) * ((w - (starRingEnd ℂ) w₂) / (w + w₂)) =
        1 + d₁ * (w - p₃)⁻¹ + d₂ * (w - p₄)⁻¹ := hpair a₂ hw3 hw4
    -- Pairwise resolvent splitting `(w - p)⁻¹ * (w - q)⁻¹`
    have hres_mul : ∀ {u_p v_p : ℂ}, u_p ≠ v_p → w - u_p ≠ 0 → w - v_p ≠ 0 →
        (w - u_p)⁻¹ * (w - v_p)⁻¹ =
          (u_p - v_p)⁻¹ * (w - u_p)⁻¹ + (v_p - u_p)⁻¹ * (w - v_p)⁻¹ := by
      intro u_p v_p huv hwu hwv
      have h1 : u_p - v_p ≠ 0 := sub_ne_zero.mpr huv
      have h2 : v_p - u_p ≠ 0 := sub_ne_zero.mpr huv.symm
      have hneg : v_p - u_p = -(u_p - v_p) := by ring
      rw [hneg, inv_neg]
      field_simp [h1, hwu, hwv]
      ring
    have hp13 : p₁ ≠ p₃ := fun h0' => by
      have := congrArg Complex.re h0'; simp [p₁, p₃, a₁, a₂] at this; linarith
    have hp14 : p₁ ≠ p₄ := fun h0' => by
      have := congrArg Complex.re h0'; simp [p₁, p₄, a₁, a₂] at this; linarith
    have hp23 : p₂ ≠ p₃ := fun h0' => by
      have := congrArg Complex.re h0'; simp [p₂, p₃, a₁, a₂] at this; linarith
    have hp24 : p₂ ≠ p₄ := fun h0' => by
      have := congrArg Complex.re h0'; simp [p₂, p₄, a₁, a₂] at this; linarith
    rw [hgate4, show ((w - w₁) / (w + (starRingEnd ℂ) w₁)) * ((w - (starRingEnd ℂ) w₁) / (w + w₁)) *
        ((w - w₂) / (w + (starRingEnd ℂ) w₂)) * ((w - (starRingEnd ℂ) w₂) / (w + w₂)) =
      (((w - w₁) / (w + (starRingEnd ℂ) w₁)) * ((w - (starRingEnd ℂ) w₁) / (w + w₁))) *
        (((w - w₂) / (w + (starRingEnd ℂ) w₂)) * ((w - (starRingEnd ℂ) w₂) / (w + w₂))) by ring,
      hpair1, hpair2]
    have hm13 := hres_mul hp13 hw1 hw3
    have hm14 := hres_mul hp14 hw1 hw4
    have hm23 := hres_mul hp23 hw2 hw3
    have hm24 := hres_mul hp24 hw2 hw4
    simp only [R₁, R₂, R₃, R₄, div_eq_mul_inv]
    linear_combination -c₁ * d₁ * hm13 - c₁ * d₂ * hm14 - c₂ * d₁ * hm23 - c₂ * d₂ * hm24
  rw [← hgate_pf]
  ring

private theorem quartetReflected_shift_and_neg_bound {σ γ : ℝ} (h0 : 1 / 2 < σ) (h1 : σ < 1)
    (hγ : 0 < γ) (h : CompactPulse) :
    Continuous (quartetReflected σ γ h) ∧
    ∃ B : ℝ, 0 ≤ B ∧
      (∀ w : ℂ, 0 ≤ w.re → w.re ≤ 3 / 8 →
        ‖pulseAmplitude h (-I * w) * quartetScatteringPhase σ γ w‖ ≤ B / (1 + w.im ^ 2)) ∧
      (∀ d : ℝ, 0 ≤ d → d ≤ 3 / 8 → ∀ τ : ℝ,
        quartetReflected σ γ h τ = ∫ t : ℝ,
          pulseAmplitude h (-I * ((d : ℂ) + (t : ℂ) * I)) *
            quartetScatteringPhase σ γ ((d : ℂ) + (t : ℂ) * I) *
            Complex.exp (((d : ℂ) + (t : ℂ) * I) * (τ : ℂ))) ∧
      (∀ τ : ℝ, τ ≤ 0 → ‖quartetReflected σ γ h τ‖ ≤ B * Real.pi * Real.exp ((3 / 8) * τ)) := by
  obtain ⟨hschur, hunit⟩ := quartet_schur_and_unitary h0 h1 hγ
  have hdiff_ph : ∀ {w : ℂ}, w ≠ 1 / 2 → xiQuartet σ γ (1 + 2 * w) ≠ 0 →
      DifferentiableAt ℂ (quartetScatteringPhase σ γ) w := by
    intro w hne hxi
    have hd : 2 * w - 1 ≠ 0 := fun h0' => hne (by linear_combination h0' / 2)
    unfold quartetScatteringPhase quartetReducedScattering
    exact ((by fun_prop : DifferentiableAt ℂ (fun v : ℂ => 1 + 2 * v) w).div (by fun_prop) hd).mul
      ((((differentiable_xiQuartet σ γ) _).comp w (by fun_prop)).div
        (((differentiable_xiQuartet σ γ) _).comp w (by fun_prop)) hxi)
  have hcont_line : Continuous fun ξ : ℝ => quartetScatteringPhase σ γ ((ξ : ℂ) * I) := by
    refine continuous_iff_continuousAt.mpr fun ξ => ?_
    have hne : ((ξ : ℂ) * I) ≠ 1 / 2 := fun he => by have := congrArg Complex.re he; simp at this
    exact ContinuousAt.comp (f := fun ξ : ℝ => (ξ : ℂ) * I)
      (hdiff_ph hne (hschur _ (by simp) |>.1)).continuousAt (by fun_prop)
  have hGc : Continuous (quartetReflected σ γ h) :=
    continuous_unitaryReflected hcont_line.measurable (fun ξ => ((hunit ξ).2).le) h
  obtain ⟨C₁, hC₁, hζ_log⟩ := exists_norm_inv_LFunction_le_log_pow (1 : DirichletCharacter ℂ 1)
  set boxR : Set ℂ := {z : ℂ | (1 ≤ z.re ∧ z.re ≤ 2) ∧ 2 ≤ |z.im| ∧ |z.im| ≤ 10}
  have hboxR_c : IsCompact boxR := by
    have heq : boxR = ((Icc (1 : ℝ) 2) ×ℂ (Icc (-10 : ℝ) 10)) ∩ {z : ℂ | 2 ≤ |z.im|} := by
      ext z; simp only [boxR, mem_inter_iff, Complex.mem_reProdIm, mem_Icc, mem_setOf_eq, abs_le]; tauto
    rw [heq]
    exact (isCompact_Icc.reProdIm isCompact_Icc).inter_right
      (isClosed_le continuous_const (continuous_abs.comp Complex.continuous_im))
  have hcont_ζ : ContinuousOn (fun z : ℂ => (riemannZeta z)⁻¹) boxR := by
    intro z hz
    have hne1 : z ≠ 1 := fun he => by have := hz.2.1; rw [he] at this; simp at this; linarith
    exact ((differentiableAt_riemannZeta hne1).continuousAt.inv₀
      (riemannZeta_ne_zero_of_one_le_re hz.1.1)).continuousWithinAt
  obtain ⟨M₁, hM₁⟩ := hboxR_c.exists_bound_of_continuousOn hcont_ζ
  have hζ_shift : ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 7 / 8 → 1 ≤ |s.im| →
      ‖(riemannZeta (2 * s))⁻¹‖ ≤ (max (max M₁ 0) (C₁ * 2 ^ 7)) * |s.im| ^ 7 := by
    intro s hs1 hs2 hsim
    set z : ℂ := 2 * s with hzdef
    have hzre1 : 1 ≤ z.re := by simp [hzdef]; linarith
    have hzre2 : z.re ≤ 2 := by simp [hzdef]; linarith
    have hzim : |z.im| = 2 * |s.im| := by
      have : z.im = 2 * s.im := by simp [hzdef]
      rw [this, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have hpow1 : (1 : ℝ) ≤ |s.im| ^ 7 := one_le_pow₀ hsim
    rcases le_or_gt |z.im| 10 with hsmall | hbig
    · calc ‖(riemannZeta z)⁻¹‖ ≤ M₁ := hM₁ z ⟨⟨hzre1, hzre2⟩, by linarith, hsmall⟩
        _ ≤ max (max M₁ 0) (C₁ * 2 ^ 7) * 1 := by
            rw [mul_one]; exact (le_max_left M₁ 0).trans (le_max_left _ _)
        _ ≤ max (max M₁ 0) (C₁ * 2 ^ 7) * |s.im| ^ 7 :=
            mul_le_mul_of_nonneg_left hpow1 (by positivity)
    · have hz_eq : z = (z.re : ℂ) + (z.im : ℂ) * I := by apply Complex.ext <;> simp
      have hb := hζ_log z.re z.im hzre1 hzre2 (by linarith)
      rw [DirichletCharacter.LFunction_modOne_eq, ← hz_eq] at hb
      have hlog_id : Real.log |z.im| ≤ 2 * |s.im| := by
        rw [← hzim]; exact (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
      have hlog : Real.log |z.im| ^ 7 ≤ (2 * |s.im|) ^ 7 :=
        pow_le_pow_left₀ (Real.log_nonneg (by linarith)) hlog_id 7
      calc ‖(riemannZeta z)⁻¹‖ ≤ C₁ * Real.log |z.im| ^ 7 := hb
        _ ≤ C₁ * (2 * |s.im|) ^ 7 := mul_le_mul_of_nonneg_left hlog hC₁.le
        _ = (C₁ * 2 ^ 7) * |s.im| ^ 7 := by ring
        _ ≤ max (max M₁ 0) (C₁ * 2 ^ 7) * |s.im| ^ 7 :=
            mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
  obtain ⟨CQ, NQ, hCQ, hQ⟩ := exists_norm_scatterQ_le (by positivity) hζ_shift
  obtain ⟨Ca, _, hrap⟩ := h.rapidAmplitude.decay (3 / 8) (NQ + 2)
  set Kbox : Set ℂ := Icc (0 : ℝ) (3 / 8) ×ℂ Icc (-1 : ℝ) 1
  have hKbox : IsCompact Kbox := isCompact_Icc.reProdIm isCompact_Icc
  have hcontK : ContinuousOn (fun w =>
      pulseAmplitude h (-I * w) * quartetScatteringPhase σ γ w) Kbox := by
    intro w hw
    have hw' := Complex.mem_reProdIm.1 hw
    have hne : w ≠ 1 / 2 := fun he => by have := hw'.1.2; rw [he] at this; norm_num at this
    exact (((h.differentiable_amplitude _).comp w (by fun_prop)).mul
      (hdiff_ph hne (hschur w hw'.1.1 |>.1))).continuousAt.continuousWithinAt
  obtain ⟨B₀, hB₀⟩ := hKbox.exists_bound_of_continuousOn hcontK
  set B : ℝ := max (2 * max B₀ 0) (CQ * Ca)
  have hB_nonneg : 0 ≤ B := le_trans (by positivity : (0 : ℝ) ≤ 2 * max B₀ 0) (le_max_left _ _)
  have hB : ∀ w : ℂ, 0 ≤ w.re → w.re ≤ 3 / 8 →
      ‖pulseAmplitude h (-I * w) * quartetScatteringPhase σ γ w‖ ≤ B / (1 + w.im ^ 2) := by
    intro w hw1 hw2
    by_cases hut : 1 ≤ |w.im|
    · have hφw : ‖quartetScatteringPhase σ γ w‖ ≤ CQ * |w.im| ^ NQ := by
        have hph : quartetScatteringPhase σ γ w =
            quartetGate σ γ w * (((2 : ℂ) / (2 * w - 1)) * scatterQ (w + 1 / 2)) := by
          unfold quartetScatteringPhase quartetReducedScattering xiQuartet quartetGate scatterQ
          rw [show 2 * (w + 1 / 2) - 1 = 2 * w by ring, show 2 * (w + 1 / 2) = 1 + 2 * w by ring]
          ring
        rw [hph, norm_mul, norm_mul]
        have h2le : ‖(2 : ℂ) / (2 * w - 1)‖ ≤ 1 := by
          have him2 : (2 : ℝ) ≤ |(2 * w - 1).im| := by simp; linarith
          have hle_norm : (2 : ℝ) ≤ ‖2 * w - 1‖ := him2.trans (Complex.abs_im_le_norm _)
          rw [norm_div, Complex.norm_ofNat, div_le_one (by linarith)]
          exact hle_norm
        have hQb : ‖scatterQ (w + 1 / 2)‖ ≤ CQ * |w.im| ^ NQ := by
          simpa using hQ (w + 1 / 2) (by simp; linarith) (by simp; linarith) (by simpa using hut)
        calc ‖quartetGate σ γ w‖ * (‖(2 : ℂ) / (2 * w - 1)‖ * ‖scatterQ (w + 1 / 2)‖)
            ≤ 1 * (1 * (CQ * |w.im| ^ NQ)) :=
              mul_le_mul (hschur w hw1).2.1 (mul_le_mul h2le hQb (norm_nonneg _) (by positivity))
                (by positivity) zero_le_one
          _ = CQ * |w.im| ^ NQ := by ring
      have hw_re : (-I * w).re = w.im := by simp
      have hw_im : (-I * w).im = -w.re := by simp
      have ha := hrap (-I * w) (by rw [hw_im, abs_neg, abs_le]; exact ⟨by linarith, hw2⟩)
      rw [hw_re] at ha
      have ht1 : |w.im| ^ NQ ≤ (1 + |w.im|) ^ NQ := pow_le_pow_left₀ (abs_nonneg _) (by linarith) NQ
      have ht2 : 1 + w.im ^ 2 ≤ (1 + |w.im|) ^ 2 := by nlinarith [abs_nonneg w.im, sq_abs w.im]
      rw [le_div_iff₀ (by positivity), norm_mul]
      calc ‖pulseAmplitude h (-I * w)‖ * ‖quartetScatteringPhase σ γ w‖ * (1 + w.im ^ 2)
          ≤ ‖pulseAmplitude h (-I * w)‖ * (CQ * (1 + |w.im|) ^ NQ) * (1 + |w.im|) ^ 2 := by
            gcongr; exact hφw.trans (mul_le_mul_of_nonneg_left ht1 hCQ)
        _ = CQ * (‖pulseAmplitude h (-I * w)‖ * (1 + |w.im|) ^ (NQ + 2)) := by ring
        _ ≤ CQ * Ca := mul_le_mul_of_nonneg_left ha hCQ
        _ ≤ B := le_max_right _ _
    · have hut' := abs_le.1 (not_le.1 hut).le
      have hb := hB₀ w (Complex.mem_reProdIm.2 ⟨⟨hw1, hw2⟩, hut'⟩)
      have hsq : w.im ^ 2 ≤ 1 := by nlinarith
      rw [le_div_iff₀ (by positivity)]
      calc ‖pulseAmplitude h (-I * w) * quartetScatteringPhase σ γ w‖ * (1 + w.im ^ 2)
          ≤ max B₀ 0 * 2 := mul_le_mul (hb.trans (le_max_left _ _)) (by linarith) (by positivity)
            (le_max_right _ _)
        _ ≤ B := by linarith [le_max_left (2 * max B₀ 0) (CQ * Ca)]
  have hshift_line : ∀ d : ℝ, 0 ≤ d → d ≤ 3 / 8 → ∀ τ : ℝ,
      quartetReflected σ γ h τ = ∫ t : ℝ,
        pulseAmplitude h (-I * ((d : ℂ) + (t : ℂ) * I)) *
          quartetScatteringPhase σ γ ((d : ℂ) + (t : ℂ) * I) *
          Complex.exp (((d : ℂ) + (t : ℂ) * I) * (τ : ℂ)) := by
    intro d hd0 hd1 τ
    set Φ : ℂ → ℂ := fun z => pulseAmplitude h (-I * z) *
      quartetScatteringPhase σ γ z * Complex.exp (z * (τ : ℂ)) with hΦ
    have hstrip : ∀ s : ℂ, s.re ∈ uIcc (0 : ℝ) d → 0 ≤ s.re ∧ s.re ≤ 3 / 8 := by
      intro s hs; rw [uIcc_of_le hd0] at hs; exact ⟨hs.1, hs.2.trans hd1⟩
    have hdΦ : ∀ s : ℂ, s.re ∈ uIcc (0 : ℝ) d → DifferentiableAt ℂ Φ s := by
      intro s hs
      obtain ⟨hs1, hs2⟩ := hstrip s hs
      have hne : s ≠ 1 / 2 := fun he => by rw [he] at hs2; norm_num at hs2
      exact ((((h.differentiable_amplitude _).comp s (by fun_prop)).mul
        (hdiff_ph hne (hschur s hs1 |>.1))).mul (by fun_prop))
    have hbΦ : ∀ s : ℂ, s.re ∈ uIcc (0 : ℝ) d →
        ‖Φ s‖ ≤ (B * Real.exp ((3 / 8) * |τ|)) / (1 + s.im ^ 2) := by
      intro s hs
      obtain ⟨hs1, hs2⟩ := hstrip s hs
      have hexp : ‖Complex.exp (s * (τ : ℂ))‖ ≤ Real.exp ((3 / 8) * |τ|) := by
        rw [Complex.norm_exp, show (s * (τ : ℂ)).re = s.re * τ by simp]
        refine Real.exp_le_exp.mpr ?_
        calc s.re * τ ≤ |s.re * τ| := le_abs_self _
          _ = |s.re| * |τ| := abs_mul _ _
          _ ≤ (3 / 8) * |τ| := mul_le_mul_of_nonneg_right (by rw [abs_of_nonneg hs1]; exact hs2)
              (abs_nonneg _)
      simp only [hΦ]; rw [norm_mul]
      calc ‖pulseAmplitude h (-I * s) * quartetScatteringPhase σ γ s‖ * ‖Complex.exp (s * (τ : ℂ))‖
          ≤ (B / (1 + s.im ^ 2)) * Real.exp ((3 / 8) * |τ|) :=
            mul_le_mul (hB s hs1 hs2) hexp (norm_nonneg _) (by positivity)
        _ = (B * Real.exp ((3 / 8) * |τ|)) / (1 + s.im ^ 2) := by ring
    have h0_eq : quartetReflected σ γ h τ = ∫ t : ℝ, Φ (((0 : ℝ) : ℂ) + (t : ℂ) * I) := by
      rw [quartetReflected, unitaryReflected]
      refine integral_congr_ae (Eventually.of_forall fun t => ?_)
      simp only [hΦ]
      have e : ((0 : ℝ) : ℂ) + (t : ℂ) * I = (t : ℂ) * I := by simp
      rw [e, show -I * ((t : ℂ) * I) = (t : ℂ) by linear_combination (-(t : ℂ)) * I_sq]
      congr 2; ring
    rw [h0_eq]
    exact integral_vertical_line_shift_of_decay hdΦ hbΦ
  have hGe : ∀ τ : ℝ, τ ≤ 0 → ‖quartetReflected σ γ h τ‖ ≤ B * Real.pi * Real.exp ((3 / 8) * τ) := by
    intro τ _
    rw [hshift_line (3 / 8) (by norm_num) le_rfl τ]
    have hpt : ∀ t : ℝ,
        ‖pulseAmplitude h (-I * (((3 / 8 : ℝ) : ℂ) + (t : ℂ) * I)) *
          quartetScatteringPhase σ γ (((3 / 8 : ℝ) : ℂ) + (t : ℂ) * I) *
          Complex.exp ((((3 / 8 : ℝ) : ℂ) + (t : ℂ) * I) * (τ : ℂ))‖ ≤
        B * (1 + t ^ 2)⁻¹ * Real.exp ((3 / 8) * τ) := by
      intro t
      rw [norm_mul, Complex.norm_exp,
        show ((((3 / 8 : ℝ) : ℂ) + (t : ℂ) * I) * (τ : ℂ)).re = (3 / 8) * τ by simp]
      have hb := hB (((3 / 8 : ℝ) : ℂ) + (t : ℂ) * I) (by simp; norm_num) (by simp)
      simpa [div_eq_mul_inv] using mul_le_mul_of_nonneg_right hb (Real.exp_pos _).le
    calc ‖∫ t : ℝ, _‖ ≤ ∫ t : ℝ, B * (1 + t ^ 2)⁻¹ * Real.exp ((3 / 8) * τ) :=
          norm_integral_le_of_norm_le ((integrable_inv_one_add_sq.const_mul B).mul_const _)
            (Eventually.of_forall hpt)
      _ = B * Real.pi * Real.exp ((3 / 8) * τ) := by
          rw [integral_mul_const, integral_const_mul, integral_univ_inv_one_add_sq]
  exact ⟨hGc, B, hB_nonneg, hB, hshift_line, hGe⟩

private theorem quartetReflected_bilateral_laplace {σ γ : ℝ} (h0 : 1 / 2 < σ) (h1 : σ < 1)
    (hγ : 0 < γ) (h : CompactPulse) :
    Continuous (quartetReflected σ γ h) ∧
    (∃ B : ℝ, 0 ≤ B ∧ ∀ τ : ℝ, τ ≤ 0 →
      ‖quartetReflected σ γ h τ‖ ≤ B * Real.pi * Real.exp ((3 / 8) * τ)) ∧
    (∀ w : ℂ, 1 / 8 < w.re → w.re < 5 / 16 →
      (∫ τ in Ioi (0 : ℝ), Complex.exp (-w * (τ : ℂ)) * quartetReflected σ γ h τ) +
        (∫ σ' in Ioi (0 : ℝ), Complex.exp (w * (σ' : ℂ)) * quartetReflected σ γ h (-σ')) =
        2 * Real.pi * pulseAmplitude h (-I * w) * quartetScatteringPhase σ γ w) := by
  obtain ⟨hschur, hunit⟩ := quartet_schur_and_unitary h0 h1 hγ
  obtain ⟨hGc, B, hB_nonneg, hB, hshift_line, hGe⟩ :=
    quartetReflected_shift_and_neg_bound h0 h1 hγ h
  refine ⟨hGc, ⟨B, hB_nonneg, hGe⟩, ?_⟩
  have hint_a : Integrable fun ξ : ℝ => ‖pulseAmplitude h (ξ : ℂ)‖ :=
    ((h.integrable_amplitude_line 0).norm).congr (Eventually.of_forall fun _ => by simp)
  set M₀ : ℝ := ∫ ξ : ℝ, ‖pulseAmplitude h (ξ : ℂ)‖
  have hGb : ∀ τ : ℝ, ‖quartetReflected σ γ h τ‖ ≤ M₀ := by
    intro τ
    rw [quartetReflected, unitaryReflected]
    refine norm_integral_le_of_norm_le hint_a (Eventually.of_forall fun ξ => le_of_eq ?_)
    rw [norm_mul, norm_mul, (hunit ξ).2, mul_one, norm_exp_I_mul, mul_one]
  have hdiff_ph : ∀ {w : ℂ}, w ≠ 1 / 2 → xiQuartet σ γ (1 + 2 * w) ≠ 0 →
      DifferentiableAt ℂ (quartetScatteringPhase σ γ) w := by
    intro w hne hxi
    have hd : 2 * w - 1 ≠ 0 := fun h0' => hne (by linear_combination h0' / 2)
    unfold quartetScatteringPhase quartetReducedScattering
    exact ((by fun_prop : DifferentiableAt ℂ (fun v : ℂ => 1 + 2 * v) w).div (by fun_prop) hd).mul
      ((((differentiable_xiQuartet σ γ) _).comp w (by fun_prop)).div
        (((differentiable_xiQuartet σ γ) _).comp w (by fun_prop)) hxi)
  intro w hw1 hw2
  set c : ℝ := w.re
  set η : ℝ := w.im
  have hc0 : 0 ≤ c := by linarith
  have hc1 : c ≤ 3 / 8 := by linarith
  have hw_eq : w = (c : ℂ) + (η : ℂ) * I := by apply Complex.ext <;> simp [c, η]
  set f : ℝ → ℂ := fun t => pulseAmplitude h (-I * ((c : ℂ) + (t : ℂ) * I)) *
    quartetScatteringPhase σ γ ((c : ℂ) + (t : ℂ) * I) with hf_def
  have hf_cont : Continuous f := by
    refine (h.differentiable_amplitude.continuous.comp (by fun_prop)).mul ?_
    refine continuous_iff_continuousAt.mpr fun t => ?_
    have hne : ((c : ℂ) + (t : ℂ) * I) ≠ 1 / 2 := fun he => by
      have := congrArg Complex.re he; simp at this; linarith
    exact ContinuousAt.comp (f := fun t : ℝ => (c : ℂ) + (t : ℂ) * I)
      (hdiff_ph hne (hschur _ (by simp [hc0]) |>.1)).continuousAt (by fun_prop)
  have hf_int : Integrable f := by
    refine (integrable_inv_one_add_sq.const_mul B).mono' hf_cont.aestronglyMeasurable
      (Eventually.of_forall fun t => ?_)
    simpa [hf_def, div_eq_mul_inv] using hB ((c : ℂ) + (t : ℂ) * I) (by simp [hc0]) (by simp [hc1])
  set g : ℝ → ℂ := fun τ => Complex.exp (-(c : ℂ) * (τ : ℂ)) * quartetReflected σ γ h τ with hg_def
  have hg_cont : Continuous g := (by fun_prop : Continuous fun τ : ℝ =>
    Complex.exp (-(c : ℂ) * (τ : ℂ))).mul hGc
  have hg_pos : IntegrableOn g (Ioi (0 : ℝ)) := by
    refine ((integrableOn_exp_mul_Ioi (by linarith : -c < 0) 0).const_mul M₀).mono'
      hg_cont.aestronglyMeasurable ((ae_restrict_iff' measurableSet_Ioi).2
        (Eventually.of_forall fun τ _ => ?_))
    simp only [hg_def]
    rw [norm_mul, Complex.norm_exp, show (-(c : ℂ) * (τ : ℂ)).re = -c * τ by simp, mul_comm]
    exact mul_le_mul_of_nonneg_right (hGb τ) (Real.exp_pos _).le
  have hg_neg : IntegrableOn g (Iic (0 : ℝ)) := by
    have hdom_i : IntegrableOn (fun σ' : ℝ => B * Real.pi * Real.exp (-(3 / 8 - c) * σ')) (Ioi 0) :=
      (integrableOn_exp_mul_Ioi (by linarith) 0).const_mul (B * Real.pi)
    have hdom : IntegrableOn (fun τ : ℝ => B * Real.pi * Real.exp ((3 / 8 - c) * τ)) (Iic 0) := by
      rw [← integrable_indicator_iff measurableSet_Iic]
      have h1' := (integrable_indicator_iff measurableSet_Ioi).mpr hdom_i
      refine (h1'.comp_neg).congr ?_
      have hae : ∀ᵐ τ : ℝ, τ ≠ 0 := by
        rw [ae_iff]
        have hset : {τ : ℝ | ¬ τ ≠ 0} = ({0} : Set ℝ) := by ext τ; simp
        rw [hset]; exact measure_singleton 0
      refine hae.mono fun τ hτ => ?_
      dsimp only
      rcases lt_or_gt_of_ne hτ with hlt | hgt
      · rw [indicator_of_mem (show -τ ∈ Ioi (0 : ℝ) by simp; linarith),
          indicator_of_mem (show τ ∈ Iic (0 : ℝ) from hlt.le)]; ring_nf
      · rw [indicator_of_notMem (show -τ ∉ Ioi (0 : ℝ) by simp; linarith),
          indicator_of_notMem (show τ ∉ Iic (0 : ℝ) by simp; linarith)]
    refine hdom.mono' hg_cont.aestronglyMeasurable
      ((ae_restrict_iff' measurableSet_Iic).2 (Eventually.of_forall fun τ hτ => ?_))
    simp only [hg_def]
    rw [norm_mul, Complex.norm_exp, show (-(c : ℂ) * (τ : ℂ)).re = -c * τ by simp]
    calc Real.exp (-c * τ) * ‖quartetReflected σ γ h τ‖
        ≤ Real.exp (-c * τ) * (B * Real.pi * Real.exp ((3 / 8) * τ)) :=
          mul_le_mul_of_nonneg_left (hGe τ hτ) (Real.exp_pos _).le
      _ = B * Real.pi * Real.exp ((3 / 8 - c) * τ) := by
          rw [mul_left_comm, ← Real.exp_add]; congr 2; ring
  have hg_int : Integrable g := by
    rw [← integrableOn_univ, ← Iic_union_Ioi (a := (0 : ℝ))]
    exact hg_neg.union hg_pos
  have hpi0 : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  have hpi : (2 * Real.pi : ℂ) ≠ 0 := by exact_mod_cast hpi0
  set F : ℝ → ℂ := fun v => (2 * Real.pi : ℂ) * f (2 * Real.pi * v) with hF_def
  have hF_cont : Continuous F := continuous_const.mul (hf_cont.comp (by fun_prop))
  have hF_int : Integrable F := (hf_int.comp_mul_left' hpi0).const_mul (2 * Real.pi : ℂ)
  have hFinv_eq : 𝓕⁻ F = g := by
    funext τ
    rw [fourierInv_eq_integral_exp]
    have hg_sub := Measure.integral_comp_mul_left
      (fun y : ℝ => f y * Complex.exp (I * (y : ℂ) * (τ : ℂ))) (2 * Real.pi)
    have habs : |(2 * Real.pi)⁻¹| = (2 * Real.pi)⁻¹ := abs_of_pos (by positivity)
    rw [habs, Complex.real_smul] at hg_sub
    have hrw : ∀ v : ℝ, Complex.exp (((2 * Real.pi * v * τ : ℝ)) * I) • F v =
        (2 * Real.pi : ℂ) * (f (2 * Real.pi * v) *
          Complex.exp (I * ((2 * Real.pi * v : ℝ) : ℂ) * (τ : ℂ))) := by
      intro v; simp only [hF_def, smul_eq_mul]
      have he : Complex.exp (((2 * Real.pi * v * τ : ℝ)) * I) =
          Complex.exp (I * ((2 * Real.pi * v : ℝ) : ℂ) * (τ : ℂ)) := by
        congr 1; push_cast; ring
      rw [he]; ring
    simp_rw [hrw]
    rw [integral_const_mul, hg_sub]
    push_cast
    rw [← mul_assoc, mul_inv_cancel₀ hpi, one_mul]
    simp only [hg_def]
    rw [hshift_line c hc0 hc1 τ, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only [hf_def]
    have he : Complex.exp (((c : ℂ) + (y : ℂ) * I) * (τ : ℂ)) =
        Complex.exp ((c : ℂ) * (τ : ℂ)) * Complex.exp (I * (y : ℂ) * (τ : ℂ)) := by
      rw [← Complex.exp_add]; congr 1; ring
    have hc_cancel : Complex.exp (-(c : ℂ) * (τ : ℂ)) * Complex.exp ((c : ℂ) * (τ : ℂ)) = 1 := by
      rw [← Complex.exp_add]
      have : -(c : ℂ) * (τ : ℂ) + (c : ℂ) * (τ : ℂ) = 0 := by ring
      rw [this, Complex.exp_zero]
    rw [he]
    linear_combination (f y * Complex.exp (I * (y : ℂ) * (τ : ℂ))) * (-hc_cancel)
  have hFF_int : Integrable (𝓕 F) := by
    have hFF_eq : 𝓕 F = fun x => g (-x) := funext fun x => by
      have h1' := Real.fourierInv_eq_fourier_neg F (-x)
      rw [neg_neg, hFinv_eq] at h1'; exact h1'.symm
    rw [hFF_eq]; exact hg_int.comp_neg
  have hinv := hF_cont.fourier_fourierInv_eq hF_int hFF_int
  rw [hFinv_eq] at hinv
  have hval := congrFun hinv (η / (2 * Real.pi))
  rw [Real.fourier_real_eq_integral_exp_smul] at hval
  have hF_eval : F (η / (2 * Real.pi)) =
      2 * Real.pi * pulseAmplitude h (-I * w) * quartetScatteringPhase σ γ w := by
    simp only [hF_def, hf_def]; rw [mul_div_cancel₀ _ hpi0, ← hw_eq]; ring
  set H : ℝ → ℂ := fun τ => Complex.exp (-w * (τ : ℂ)) * quartetReflected σ γ h τ with hH_def
  have hH_eq : ∀ τ : ℝ,
      Complex.exp ((-2 * Real.pi * τ * (η / (2 * Real.pi)) : ℝ) * I) • g τ = H τ := by
    intro τ; simp only [smul_eq_mul, hg_def, hH_def]
    have hexp : Complex.exp ((-2 * Real.pi * τ * (η / (2 * Real.pi)) : ℝ) * I) *
        Complex.exp (-(c : ℂ) * (τ : ℂ)) = Complex.exp (-w * (τ : ℂ)) := by
      rw [← Complex.exp_add]; congr 1
      have hdiv : -2 * Real.pi * τ * (η / (2 * Real.pi)) = -η * τ := by field_simp
      rw [hdiv, hw_eq]; push_cast; ring
    rw [← mul_assoc, hexp]
  have hH_int : Integrable H := by
    refine (hg_int.norm).mono' ((by fun_prop : Continuous fun τ : ℝ =>
      Complex.exp (-w * (τ : ℂ))).mul hGc).aestronglyMeasurable (Eventually.of_forall fun τ => ?_)
    rw [← hH_eq τ, smul_eq_mul, norm_mul, Complex.norm_exp]
    have hre : (((-2 * Real.pi * τ * (η / (2 * Real.pi)) : ℝ) : ℂ) * I).re = 0 := by
      generalize -2 * Real.pi * τ * (η / (2 * Real.pi)) = t; simp
    rw [hre, Real.exp_zero, one_mul]
  have hsplit : (∫ τ in Ioi (0 : ℝ), H τ) + (∫ τ in Iic (0 : ℝ), H τ) = ∫ τ : ℝ, H τ := by
    have h1' := integral_add_compl (s := Ioi (0 : ℝ)) measurableSet_Ioi hH_int
    rwa [compl_Ioi] at h1'
  have hneg_eq : (∫ τ in Iic (0 : ℝ), H τ) =
      ∫ σ' in Ioi (0 : ℝ), Complex.exp (w * (σ' : ℂ)) * quartetReflected σ γ h (-σ') := by
    rw [← integral_indicator measurableSet_Iic, ← integral_indicator measurableSet_Ioi,
      ← integral_neg_eq_self]
    have hae : ∀ᵐ σ' : ℝ, σ' ≠ 0 := by
      rw [ae_iff]
      have hset : {σ' : ℝ | ¬ σ' ≠ 0} = ({0} : Set ℝ) := by ext σ'; simp
      rw [hset]; exact measure_singleton 0
    refine integral_congr_ae (hae.mono fun σ' hσ' => ?_)
    dsimp only
    rcases lt_or_gt_of_ne hσ' with hlt | hgt
    · rw [indicator_of_notMem (show -σ' ∉ Iic (0 : ℝ) by simp; linarith),
        indicator_of_notMem (show σ' ∉ Ioi (0 : ℝ) by simp; linarith)]
    · rw [indicator_of_mem (show -σ' ∈ Iic (0 : ℝ) by simp; linarith),
        indicator_of_mem (show σ' ∈ Ioi (0 : ℝ) from hgt)]
      simp only [hH_def]; push_cast; ring_nf
  rw [← hneg_eq, hsplit]
  calc ∫ τ : ℝ, H τ
      = ∫ τ : ℝ, Complex.exp ((-2 * Real.pi * τ * (η / (2 * Real.pi)) : ℝ) * I) • g τ :=
        integral_congr_ae (Eventually.of_forall fun τ => (hH_eq τ).symm)
    _ = F (η / (2 * Real.pi)) := hval
    _ = 2 * Real.pi * pulseAmplitude h (-I * w) * quartetScatteringPhase σ γ w := hF_eval

/-- **Super-Threshold Decay Obstruction on `xiQuartet`.** Whenever `pulseAmplitude h` is nonvanishing
at `-I * ((quartetZero σ γ - 1) / 2)`, `quartetReflected σ γ h` violates `O(e^{-δ T})` for every
`δ > (1 - σ) / 2`. -/
theorem not_quartetReflected_decay_gt {σ γ δ : ℝ} (h0 : 1 / 2 < σ) (h1 : σ < 1) (hγ : 0 < γ)
    (h : CompactPulse) (ha_ne : pulseAmplitude h (-I * ((quartetZero σ γ - 1) / 2)) ≠ 0)
    (hδ : (1 - σ) / 2 < δ) :
    ¬ ∃ C : ℝ, ∀ T : ℝ, 0 ≤ T → ‖quartetReflected σ γ h T‖ ≤ C * Real.exp (-δ * T) := by
  rintro ⟨C₀, hC₀⟩
  obtain ⟨hschur, _⟩ := quartet_schur_and_unitary h0 h1 hγ
  obtain ⟨hGc, ⟨B, hB_nonneg, hGe⟩, hbilat⟩ := quartetReflected_bilateral_laplace h0 h1 hγ h
  set p : ℂ := (quartetZero σ γ - 1) / 2 with hpdef
  have hp1 : 1 + 2 * p = quartetZero σ γ := by rw [hpdef]; ring
  have hpxi : xiQuartet σ γ (1 + 2 * p) = 0 := by
    rw [hp1]; exact xiQuartet_eval_quartetZero h0 hγ
  have hpre : p.re = (σ - 1) / 2 := by rw [hpdef]; simp [quartetZero]
  have hp_gt : -δ < p.re := by rw [hpre]; linarith
  set Lpos : ℂ → ℂ := fun w => ∫ τ in Ioi (0 : ℝ),
    Complex.exp (-w * (τ : ℂ)) * quartetReflected σ γ h τ with hLpos
  have hC₀' : ∀ τ : ℝ, -(0 : ℝ) < τ →
      ‖quartetReflected σ γ h τ‖ ≤ max C₀ 0 * Real.exp (-δ * τ) :=
    fun τ hτ => (hC₀ τ (by linarith)).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)
  have hLpos_d : DifferentiableOn ℂ Lpos {w : ℂ | -δ < w.re} := by
    simpa [hLpos] using RingdownRate.differentiableOn_laplace hGc (le_max_right C₀ 0) hC₀'
  set Lneg₀ : ℂ → ℂ := fun z => ∫ σ' in Ioi (0 : ℝ),
    Complex.exp (-z * (σ' : ℂ)) * quartetReflected σ γ h (-σ') with hLneg₀
  have hGe' : ∀ σ' : ℝ, -(0 : ℝ) < σ' →
      ‖quartetReflected σ γ h (-σ')‖ ≤ B * Real.pi * Real.exp (-(3 / 8) * σ') := by
    intro σ' hσ'; simpa [mul_neg, neg_mul] using hGe (-σ') (by linarith)
  have hLneg₀_d : DifferentiableOn ℂ Lneg₀ {z : ℂ | -(3 / 8 : ℝ) < z.re} := by
    simpa [hLneg₀] using RingdownRate.differentiableOn_laplace (hGc.comp continuous_neg)
      (mul_nonneg hB_nonneg Real.pi_pos.le) hGe'
  set Lneg : ℂ → ℂ := fun w => Lneg₀ (-w) with hLneg
  have hLneg_d : DifferentiableOn ℂ Lneg {w : ℂ | w.re < 3 / 8} := by
    intro w hw
    have hw' : -w ∈ {z : ℂ | -(3 / 8 : ℝ) < z.re} := by show -(3 / 8 : ℝ) < (-w).re; simp; exact hw
    have hopen : IsOpen {z : ℂ | -(3 / 8 : ℝ) < z.re} :=
      isOpen_lt continuous_const Complex.continuous_re
    exact ((hLneg₀_d (-w) hw').differentiableAt (hopen.mem_nhds hw')).comp w differentiableAt_id.neg
      |>.differentiableWithinAt
  set S : Set ℂ := {w : ℂ | -δ < w.re ∧ w.re < 3 / 8}
  have hSo : IsOpen S := (isOpen_lt continuous_const Complex.continuous_re).inter
    (isOpen_lt Complex.continuous_re continuous_const)
  have hSconn : IsPreconnected S :=
    ((convex_halfSpace_re_gt (-δ)).inter (convex_halfSpace_re_lt (3 / 8))).isPreconnected
  set Φ₁ : ℂ → ℂ := fun w =>
    (2 * w - 1) * xiQuartet σ γ (1 + 2 * w) * (Lpos w + Lneg w)
  set Φ₂ : ℂ → ℂ := fun w =>
    2 * Real.pi * pulseAmplitude h (-I * w) * (1 + 2 * w) * xiQuartet σ γ (2 * w)
  have hUpos : IsOpen {w : ℂ | -δ < w.re} := isOpen_lt continuous_const Complex.continuous_re
  have hUneg : IsOpen {w : ℂ | w.re < 3 / 8} := isOpen_lt Complex.continuous_re continuous_const
  have hcx := differentiable_xiQuartet σ γ
  have hΦ₁a : AnalyticOnNhd ℂ Φ₁ S := by
    refine DifferentiableOn.analyticOnNhd ?_ hSo
    intro w hw
    have h1' := (hLpos_d w hw.1).differentiableAt (hUpos.mem_nhds hw.1)
    have h2' := (hLneg_d w hw.2).differentiableAt (hUneg.mem_nhds hw.2)
    exact (((by fun_prop : DifferentiableAt ℂ (fun v : ℂ => 2 * v - 1) w).mul
      ((hcx _).comp w (by fun_prop))).mul (h1'.add h2')).differentiableWithinAt
  have hΦ₂a : AnalyticOnNhd ℂ Φ₂ S := by
    refine DifferentiableOn.analyticOnNhd ?_ hSo
    intro w _
    exact ((((differentiableAt_const _).mul
      ((h.differentiable_amplitude _).comp w (by fun_prop))).mul (by fun_prop)).mul
      ((hcx _).comp w (by fun_prop))).differentiableWithinAt
  have hagree : ∀ w : ℂ, 1 / 8 < w.re → w.re < 5 / 16 → Φ₁ w = Φ₂ w := by
    intro w hw1 hw2
    have hlap : Lpos w + Lneg w =
        2 * Real.pi * pulseAmplitude h (-I * w) * quartetScatteringPhase σ γ w := by
      have hneg_rw : Lneg w = ∫ σ' in Ioi (0 : ℝ),
          Complex.exp (w * (σ' : ℂ)) * quartetReflected σ γ h (-σ') := by
        simp only [hLneg, hLneg₀, neg_neg]
      rw [hneg_rw]
      exact hbilat w hw1 hw2
    have h2w : 2 * w - 1 ≠ 0 := fun h0' => by
      have := congrArg Complex.re h0'; simp at this; linarith
    have hxi : xiQuartet σ γ (1 + 2 * w) ≠ 0 := (hschur w (by linarith)).1
    dsimp only [Φ₁, Φ₂]
    rw [hlap]
    unfold quartetScatteringPhase quartetReducedScattering
    calc (2 * w - 1) * xiQuartet σ γ (1 + 2 * w) *
            (2 * ↑Real.pi * pulseAmplitude h (-I * w) *
              ((1 + 2 * w) / (2 * w - 1) * (xiQuartet σ γ (2 * w) / xiQuartet σ γ (1 + 2 * w))))
        = ((2 * w - 1) * (2 * w - 1)⁻¹) *
            (xiQuartet σ γ (1 + 2 * w) * (xiQuartet σ γ (1 + 2 * w))⁻¹) *
            (2 * ↑Real.pi * pulseAmplitude h (-I * w) * (1 + 2 * w) * xiQuartet σ γ (2 * w)) := by
          simp only [div_eq_mul_inv]; ring
      _ = 2 * ↑Real.pi * pulseAmplitude h (-I * w) * (1 + 2 * w) * xiQuartet σ γ (2 * w) := by
          rw [mul_inv_cancel₀ h2w, mul_inv_cancel₀ hxi, one_mul, one_mul]
  have hEq : EqOn Φ₁ Φ₂ S := by
    have hmemS : (1 / 4 : ℂ) ∈ S := by
      show -δ < (1 / 4 : ℂ).re ∧ (1 / 4 : ℂ).re < 3 / 8
      have hre4 : (1 / 4 : ℂ).re = 1 / 4 := by simp
      rw [hre4]
      exact ⟨by linarith, by norm_num⟩
    refine hΦ₁a.eqOn_of_preconnected_of_eventuallyEq hΦ₂a hSconn hmemS ?_
    have hV : IsOpen {w : ℂ | 1 / 8 < w.re ∧ w.re < 5 / 16} :=
      (isOpen_lt continuous_const Complex.continuous_re).inter
        (isOpen_lt Complex.continuous_re continuous_const)
    have hmemV : (1 / 4 : ℂ) ∈ {w : ℂ | 1 / 8 < w.re ∧ w.re < 5 / 16} := by
      show (1 / 8 : ℝ) < (1 / 4 : ℂ).re ∧ (1 / 4 : ℂ).re < 5 / 16
      have hre4 : (1 / 4 : ℂ).re = 1 / 4 := by simp
      rw [hre4]; norm_num
    filter_upwards [hV.mem_nhds hmemV] with w hw
    exact hagree w hw.1 hw.2
  have hpS : p ∈ S := ⟨hp_gt, by rw [hpre]; linarith⟩
  have hp_eq := hEq hpS
  dsimp only [Φ₁, Φ₂] at hp_eq
  rw [hpxi, mul_zero, zero_mul] at hp_eq
  have hpi : (2 : ℂ) * (Real.pi : ℂ) ≠ 0 :=
    mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  have ha_p : pulseAmplitude h (-I * p) ≠ 0 := ha_ne
  have h12p : 1 + 2 * p ≠ 0 := by
    intro h0'; rw [hp1] at h0'
    have hre0 : σ = 0 := by
      have := congrArg Complex.re h0'
      simpa [quartetZero] using this
    linarith only [h0, hre0]
  have hxi2p : xiQuartet σ γ (2 * p) ≠ 0 := by
    rw [← xiQuartet_one_sub σ γ (2 * p), show (1 : ℂ) - 2 * p = 1 + 2 * (-p) by ring]
    have hre_np : 0 ≤ (-p).re := by
      rw [Complex.neg_re, hpre]
      linarith only [h1]
    exact (hschur (-p) hre_np).1
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero hpi ha_p) h12p) hxi2p hp_eq.symm

/-- **Finite Decay-Curve Indecisiveness Theorem.**
For **every** nonzero `h : CompactPulse` (`∃ S : ℝ, h S ≠ 0`), **every** tolerance `ε > 0`, and
**every** `σ ∈ (1/2, 1)`, there exists `γ > 0` such that `xiQuartet σ γ`:
1. is entire, `s ↦ 1 - s` symmetric, strictly positive on `ℝ`, globally Schur-passive with
   nonnegative Herglotz admittance on `Re w ≥ 0`, continuous-spectrum unitary, and has causal
   retarded echo kernel `quartetEchoKernel σ γ` (`= 0` on `τ ≤ 0`) whose Laplace transform on
   `Re w > 1/2` is `quartetGate σ γ w * (Λ(2w)/Λ(2w + 1))`;
2. approximates `pulseReflected h` within `ε` **uniformly across all `T ∈ ℝ`** (hence on every
   finite observation window);
3. yet for **that very same pulse `h`**, violates `O(e^{-δ T})` for every `δ > (1 - σ) / 2`. -/
theorem finite_decay_curve_cannot_decide_asymptotic_exponent
    (h : CompactPulse) (hne_h : ∃ S : ℝ, h S ≠ 0) {ε σ : ℝ}
    (hε : 0 < ε) (h0 : 1 / 2 < σ) (h1 : σ < 1) :
    ∃ γ : ℝ, 0 < γ ∧
      Differentiable ℂ (xiQuartet σ γ) ∧
      (∀ s : ℂ, xiQuartet σ γ (1 - s) = xiQuartet σ γ s) ∧
      (∀ x : ℝ, 0 < (xiQuartet σ γ (x : ℂ)).re) ∧
      (∀ w : ℂ, 0 ≤ w.re → ‖quartetReducedScattering σ γ w‖ ≤ 1 ∧
        0 ≤ ((1 - quartetReducedScattering σ γ w) / (1 + quartetReducedScattering σ γ w)).re) ∧
      (∀ t : ℝ, ‖quartetScatteringPhase σ γ ((t : ℂ) * I)‖ = 1) ∧
      (∀ τ : ℝ, τ ≤ 0 → quartetEchoKernel σ γ τ = 0) ∧
      (∀ w : ℂ, 1 / 2 < w.re →
        (∫ τ : ℝ, Complex.exp (-w * (τ : ℂ)) * quartetEchoKernel σ γ τ) =
          quartetGate σ γ w * (completedRiemannZeta (2 * w) / completedRiemannZeta (2 * w + 1))) ∧
      (∀ T : ℝ, ‖quartetReflected σ γ h T - pulseReflected h T‖ < ε) ∧
      (∀ δ : ℝ, (1 - σ) / 2 < δ →
        ¬ ∃ C : ℝ, ∀ T : ℝ, 0 ≤ T → ‖quartetReflected σ γ h T‖ ≤ C * Real.exp (-δ * T)) := by
  -- Step 1: Dominated convergence `∫ ‖a_h(ξ)‖ ‖quartetGate σ γ (iξ) - 1‖ dξ → 0` as `γ → ∞`
  have hint_a : Integrable fun ξ : ℝ => ‖pulseAmplitude h (ξ : ℂ)‖ :=
    ((h.integrable_amplitude_line 0).norm).congr (Eventually.of_forall fun _ => by simp)
  have hinv_tend : Tendsto (fun γ : ℝ => (quartetZero σ γ * (1 - quartetZero σ γ))⁻¹) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hsq_tend : Tendsto (fun γ : ℝ => (γ ^ 2)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp ((tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)))
    refine squeeze_zero_norm' ?_ hsq_tend
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with γ hγ1
    rw [norm_inv, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
    refine inv_anti₀ (by positivity) ?_
    have hre := quartetProd_re (σ := σ) (γ := γ)
    have hle_re : |(quartetZero σ γ * (1 - quartetZero σ γ)).re| ≤
        ‖quartetZero σ γ * (1 - quartetZero σ γ)‖ := Complex.abs_re_le_norm _
    rw [hre, abs_of_pos (by nlinarith)] at hle_re
    nlinarith
  have hfac_tend : ∀ s : ℂ, Tendsto (fun γ : ℝ => quartetFactor σ γ s) atTop (𝓝 1) := by
    intro s
    have h1_t : Tendsto (fun γ : ℝ =>
        1 - s * (1 - s) * (quartetZero σ γ * (1 - quartetZero σ γ))⁻¹) atTop (𝓝 1) := by
      simpa using tendsto_const_nhds.sub (hinv_tend.const_mul (s * (1 - s)))
    have h2_t : Tendsto (fun γ : ℝ =>
        1 - s * (1 - s) * ((starRingEnd ℂ) (quartetZero σ γ * (1 - quartetZero σ γ)))⁻¹) atTop (𝓝 1) := by
      have hc0 := (continuous_conj.continuousAt (x := (0 : ℂ))).tendsto.comp hinv_tend
      rw [map_zero] at hc0
      have hc : Tendsto (fun γ : ℝ =>
          ((starRingEnd ℂ) (quartetZero σ γ * (1 - quartetZero σ γ)))⁻¹) atTop (𝓝 0) :=
        hc0.congr fun γ => map_inv₀ (starRingEnd ℂ) _
      simpa using tendsto_const_nhds.sub (hc.const_mul (s * (1 - s)))
    simpa [quartetFactor, div_eq_mul_inv, map_mul, map_sub] using h1_t.mul h2_t
  have hgate_tend : ∀ ξ : ℝ, Tendsto (fun γ : ℝ =>
      ‖pulseAmplitude h (ξ : ℂ)‖ * ‖quartetGate σ γ ((ξ : ℂ) * I) - 1‖) atTop (𝓝 0) := by
    intro ξ
    have hg : Tendsto (fun γ : ℝ => quartetGate σ γ ((ξ : ℂ) * I)) atTop (𝓝 1) := by
      have hd := (hfac_tend (2 * ((ξ : ℂ) * I))).div (hfac_tend (1 + 2 * ((ξ : ℂ) * I))) one_ne_zero
      rwa [div_one] at hd
    have hn : Tendsto (fun γ : ℝ => ‖quartetGate σ γ ((ξ : ℂ) * I) - 1‖) atTop (𝓝 0) := by
      have hs := (hg.sub (tendsto_const_nhds (x := (1 : ℂ)))).norm
      rwa [sub_self, norm_zero] at hs
    have hm := hn.const_mul ‖pulseAmplitude h (ξ : ℂ)‖
    rwa [mul_zero] at hm
  have hdom_tend : Tendsto (fun γ : ℝ =>
      ∫ ξ : ℝ, ‖pulseAmplitude h (ξ : ℂ)‖ * ‖quartetGate σ γ ((ξ : ℂ) * I) - 1‖) atTop (𝓝 0) := by
    have h0_eq : (0 : ℝ) = ∫ _ξ : ℝ, (0 : ℝ) := by simp
    rw [h0_eq]
    refine tendsto_integral_filter_of_dominated_convergence (fun ξ => 2 * ‖pulseAmplitude h (ξ : ℂ)‖) ?_
      ?_ (hint_a.const_mul 2) (Eventually.of_forall hgate_tend)
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with γ hγ
      have hcont_g : Continuous fun ξ : ℝ => quartetGate σ γ ((ξ : ℂ) * I) := by
        unfold quartetGate
        refine ((differentiable_quartetFactor σ γ).continuous.comp (by fun_prop)).div
          ((differentiable_quartetFactor σ γ).continuous.comp (by fun_prop)) fun ξ hz => ?_
        exact (quartet_schur_and_unitary h0 h1 hγ).1 ((ξ : ℂ) * I) (by simp) |>.1
          (by rw [xiQuartet, hz, zero_mul])
      exact (((h.differentiable_amplitude.continuous.comp Complex.continuous_ofReal).norm).mul
        ((hcont_g.sub continuous_const).norm)).aestronglyMeasurable
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with γ hγ
      refine Eventually.of_forall fun ξ => ?_
      rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _)), mul_comm 2]
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      have hu1 := (quartet_schur_and_unitary h0 h1 hγ).2 ξ |>.1
      calc ‖quartetGate σ γ ((ξ : ℂ) * I) - 1‖
          ≤ ‖quartetGate σ γ ((ξ : ℂ) * I)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
        _ = 2 := by rw [hu1, norm_one]; norm_num
  obtain ⟨Γ₀, hΓ₀⟩ := eventually_atTop.mp ((tendsto_order.mp hdom_tend).2 ε hε)
  set Γ : ℝ := max Γ₀ 1
  -- Step 2: Find `γ ≥ Γ` where `pulseAmplitude h (-I * ((quartetZero σ γ - 1) / 2)) ≠ 0`
  have hex_γ : ∃ γ : ℝ, Γ ≤ γ ∧ pulseAmplitude h (-I * ((quartetZero σ γ - 1) / 2)) ≠ 0 := by
    by_contra hall_zero
    push Not at hall_zero
    set Ψ : ℂ → ℂ := fun z => pulseAmplitude h (-I * (((σ : ℂ) + z * I - 1) / 2)) with hΨ
    have hΨ_an : AnalyticOnNhd ℂ Ψ univ :=
      (Complex.analyticOnNhd_univ_iff_differentiable.mpr
        (h.differentiable_amplitude.comp (by fun_prop)))
    have hfreq : ∃ᶠ z in 𝓝[≠] (Γ : ℂ), Ψ z = 0 := by
      let g_seq : ℕ → ℝ := fun n => Γ + ((n : ℝ) + 1)⁻¹
      have hseq : Tendsto (fun n : ℕ => (g_seq n : ℂ)) atTop (𝓝[≠] (Γ : ℂ)) := by
        refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall fun n => ?_⟩
        · have ht : Tendsto g_seq atTop (𝓝 (Γ + 0)) :=
            tendsto_const_nhds.add (tendsto_inv_atTop_zero.comp
              (tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop))
          rw [add_zero] at ht
          exact (Complex.continuous_ofReal.continuousAt (x := Γ)).tendsto.comp ht
        · refine Set.mem_compl_singleton_iff.mpr fun heq => ?_
          have hr := Complex.ofReal_inj.mp heq
          dsimp only [g_seq] at hr
          have : (0 : ℝ) < ((n : ℝ) + 1)⁻¹ := by positivity
          linarith
      exact hseq.frequently ((Eventually.of_forall fun n => by
        have hge : Γ ≤ g_seq n := by
          dsimp only [g_seq]
          have : (0 : ℝ) ≤ ((n : ℝ) + 1)⁻¹ := by positivity
          linarith
        simpa [hΨ, quartetZero, g_seq] using hall_zero (g_seq n) hge).frequently)
    have hΨ_zero := hΨ_an.eqOn_zero_of_preconnected_of_frequently_eq_zero isPreconnected_univ
      (mem_univ (Γ : ℂ)) hfreq
    have hamp0 : ∀ ξ : ℝ, pulseAmplitude h (ξ : ℂ) = 0 := by
      intro ξ
      set z : ℂ := 2 * (ξ : ℂ) + ((σ - 1 : ℝ) : ℂ) * I
      have hz0 := hΨ_zero (mem_univ z)
      have hcoord : -I * (((σ : ℂ) + z * I - 1) / 2) = (ξ : ℂ) := by
        dsimp only [z]
        push_cast
        linear_combination (-(1 / 2 : ℂ) * ((σ : ℂ) - 1) * I - (ξ : ℂ)) * I_sq
      dsimp only [Ψ, Pi.zero_apply] at hz0
      rwa [hcoord] at hz0
    obtain ⟨S₀, hS₀_ne⟩ := hne_h
    apply hS₀_ne
    rw [h.eq_integral_amplitude S₀]
    simp [hamp0]
  obtain ⟨γ, hγΓ, ha_ne⟩ := hex_γ
  have hγ : 0 < γ := lt_of_lt_of_le (by positivity) ((le_max_right Γ₀ 1).trans hγΓ)
  obtain ⟨hschur, hunit⟩ := quartet_schur_and_unitary h0 h1 hγ
  refine ⟨γ, hγ, differentiable_xiQuartet σ γ, xiQuartet_one_sub σ γ, xiQuartet_real_pos h0 hγ,
    fun w hw => (hschur w hw).2.2,
    fun t => (hunit t).2,
    fun τ hτ => quartetEchoKernel_eq_zero_of_nonpos σ γ hτ,
    fun w hw => laplace_quartetEchoKernel h0 h1 hγ hw,
    ?_, ?_⟩
  -- Step 3: Uniform `< ε` bound across all `T ∈ ℝ`
  · intro T
    have hcont_q : Continuous fun ξ : ℝ => quartetScatteringPhase σ γ ((ξ : ℂ) * I) := by
      refine continuous_iff_continuousAt.mpr fun ξ => ?_
      have hd : 2 * ((ξ : ℂ) * I) - 1 ≠ 0 := fun h0' => by
        have := congrArg Complex.re h0'; simp at this
      have hdiff : DifferentiableAt ℂ (quartetScatteringPhase σ γ) ((ξ : ℂ) * I) :=
        ((by fun_prop : DifferentiableAt ℂ (fun v : ℂ => 1 + 2 * v) ((ξ : ℂ) * I)).div
          (by fun_prop) hd).mul
          ((((differentiable_xiQuartet σ γ) _).comp _ (by fun_prop)).div
            (((differentiable_xiQuartet σ γ) _).comp _ (by fun_prop))
            (hschur ((ξ : ℂ) * I) (by simp) |>.1))
      exact ContinuousAt.comp (f := fun ξ : ℝ => (ξ : ℂ) * I) hdiff.continuousAt (by fun_prop)
    have hq_int := h.integrable_amplitude_mul hcont_q.measurable
      (fun ξ => ((hunit ξ).2).le) T
    have hm_int := h.integrable_amplitude_mul continuous_scatteringPhase_line.measurable
      (fun ξ => (norm_scatteringPhase_line ξ).le) T
    have hdiff_int : quartetReflected σ γ h T - pulseReflected h T =
        ∫ ξ : ℝ, pulseAmplitude h (ξ : ℂ) * (quartetGate σ γ ((ξ : ℂ) * I) - 1) *
          scatteringPhase ((ξ : ℂ) * I) * Complex.exp (I * (ξ : ℂ) * (T : ℂ)) := by
      rw [quartetReflected, unitaryReflected, pulseReflected, ← integral_sub hq_int hm_int]
      refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
      have hph : quartetScatteringPhase σ γ ((ξ : ℂ) * I) =
          quartetGate σ γ ((ξ : ℂ) * I) * scatteringPhase ((ξ : ℂ) * I) := by
        unfold quartetScatteringPhase quartetReducedScattering xiQuartet quartetGate scatteringPhase
        ring
      dsimp only
      rw [hph]
      ring
    have hcont_g : Continuous fun ξ : ℝ => quartetGate σ γ ((ξ : ℂ) * I) := by
      unfold quartetGate
      refine ((differentiable_quartetFactor σ γ).continuous.comp (by fun_prop)).div
        ((differentiable_quartetFactor σ γ).continuous.comp (by fun_prop)) fun ξ hz =>
          (hschur ((ξ : ℂ) * I) (by simp)).1 (by rw [xiQuartet, hz, zero_mul])
    have hdom_g : Integrable fun ξ : ℝ =>
        ‖pulseAmplitude h (ξ : ℂ)‖ * ‖quartetGate σ γ ((ξ : ℂ) * I) - 1‖ := by
      refine (hint_a.const_mul 2).mono'
        (((h.differentiable_amplitude.continuous.comp Complex.continuous_ofReal).norm).mul
          ((hcont_g.sub continuous_const).norm)).aestronglyMeasurable
        (Eventually.of_forall fun ξ => ?_)
      rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _)), mul_comm 2]
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      calc ‖quartetGate σ γ ((ξ : ℂ) * I) - 1‖
          ≤ ‖quartetGate σ γ ((ξ : ℂ) * I)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
        _ = 2 := by rw [(hunit ξ).1, norm_one]; norm_num
    rw [hdiff_int]
    refine (norm_integral_le_of_norm_le hdom_g (Eventually.of_forall fun ξ => le_of_eq ?_)).trans_lt
      (hΓ₀ γ ((le_max_left Γ₀ 1).trans hγΓ))
    rw [norm_mul, norm_mul, norm_mul, norm_scatteringPhase_line ξ, mul_one, norm_exp_I_mul, mul_one]
  -- Step 4: Violation of `O(e^{-δ T})` for every `δ > (1 - σ) / 2` on `h` itself
  · exact fun δ hδ => not_quartetReflected_decay_gt h0 h1 hγ h ha_ne hδ

/-! ## 3. Sharp Cusp-Escape / Cavity-Receiver Equivalence and Master Resolution -/

/-- **Sharp Cusp-Escape / Cavity-Receiver Equivalence.** Universal compact-pulse ringdown at rate
`δ - ε` (`0 < δ ≤ 1/4`) is equivalent to the zero-free strip `Re ρ ≤ 1 - 2δ`, and RH (`δ = 1/4`)
is simultaneously equivalent to quarter-rate pulse escape and `y^{3/4 - ε}` horocycle convergence
of the sharp cuspidal Maass cavity energy receiver. -/
theorem cusp_escape_and_sharp_cavity_equivalence :
    (∀ δ : ℝ, 0 < δ → δ ≤ 1 / 4 →
      ((∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.re → ρ.re ≤ 1 - 2 * δ) ↔
        ∀ ε : ℝ, 0 < ε → ∀ (h : CompactPulse) (x Y : ℝ), 0 < Y → ∃ C : ℝ, ∀ τ : ℝ, 0 ≤ τ →
          ‖pulseField h τ x Y‖ ≤ C * Real.exp (-(δ - ε) * τ))) ∧
    (∃ (v : ℕ → UpperHalfPlane → ℂ) (lam : ℕ → ℝ) (M : ℕ → ℝ) (x : ℕ →ᵇ ℂ),
      (∀ n, v n ∈ HeckeCusp.cuspSpace (lam n)) ∧ (∀ n, 0 < M n) ∧
      (RiemannHypothesis ↔
        (∀ ε : ℝ, 0 < ε → ∀ (h : CompactPulse) (x₀ Y : ℝ), 0 < Y → ∃ C : ℝ, ∀ τ : ℝ, 0 ≤ τ →
          ‖pulseField h τ x₀ Y‖ ≤ C * Real.exp (-(1 / 4 - ε) * τ)) ∧
        (∀ ε : ℝ, 0 < ε → ∃ (c : ℂ) (C : ℝ), ∀ y : ℝ, 0 < y → y ≤ 1 →
          ‖ArithmeticHolographyOfTheModularHorizon.response
            (fun z => ((‖ArithmeticHolographyOfTheModularHorizon.cavity
              (ArithmeticHolographyOfTheModularHorizon.cuspFamily v M) x z‖ ^ 2 : ℝ) : ℂ)) y - c‖ ≤
            C * y ^ (3 / 4 - ε)))) := by
  refine ⟨fun δ h0 h1 => RingdownRate.zeroFreeStrip_iff_pulse_ringdown h0 h1, ?_⟩
  obtain ⟨v, lam, M, x, hv, hM, _, hRH_cav, _⟩ :=
    ArithmeticHolographyOfTheModularHorizon.exists_sharp_cavity_receiver
  refine ⟨v, lam, M, x, hv, hM, ?_⟩
  exact ⟨fun hRH => ⟨RingdownRate.riemannHypothesis_iff_pulse_ringdown.mp hRH, hRH_cav.mp hRH⟩,
    fun ⟨hpulse, _⟩ => RingdownRate.riemannHypothesis_iff_pulse_ringdown.mpr hpulse⟩

/-- **Complete Unconditional Resolution of the Cusp-Escape and Mixed-Pulse Interference Question.**
Packages in a single theorem:
1. Exact five-channel echo decomposition, Plancherel cusp-escape law, and Hermitian mixed-pulse
   interference expansion (`echoKernel_eq_five_channels`, `integral_Ioi_norm_sq_pulseReflected`,
   `setIntegral_norm_sq_mixedPulse_reflected`);
2. Unconditional sub-`7/8` cusp escape (`0 < σ < 3001/48000`) on actual `ζ`
   (`unconditional_cusp_escape_sub_seven_eighths`);
3. Finite-Time Distinguishing Inequality 1 (strict `(1 - 1/q²)` cusp tail escape separation on the
   predeclared window `[-S₀, 2 log q - S₀]`, `finite_time_cusp_escape_separation`);
4. Finite-Time Distinguishing Inequality 2 (mixed-pulse `p²` vs. `p q` boundary group-delay
   interference separation, `finite_time_mixed_pulse_prime_square_distinction`);
5. Negative resolution of growing-window uniform constants even with `b(p²) = +1/2`, positive
   bounded-depth prime-power returns, causality, passivity, unitarity, and real-axis positivity
   (`no_uniform_escape_rate_from_prime_traversal_and_passivity`);
6. Unconditional proof that a fit to a finite decay curve of any fixed nonzero pulse cannot decide
   the asymptotic exponent (`finite_decay_curve_cannot_decide_asymptotic_exponent`). -/
theorem complete_resolution_of_cusp_escape_question :
    -- (1) Five-channel split + exact escape identity + full mixed-pulse interference expansion
    (∀ τ : ℝ, echoKernel τ = promptEchoKernel τ + primitivePrimeEchoKernel τ +
      primeSquareEchoKernel τ + mixedTwoPrimeEchoKernel τ + higherCompositeEchoKernel τ) ∧
    (∀ (h : CompactPulse) {S₀ T₂ : ℝ}, (∀ s : ℝ, S₀ < |s| → h s = 0) → -S₀ ≤ T₂ →
      (∫ T in Ioi T₂, ‖pulseReflected h T‖ ^ 2) =
        (∫ S : ℝ, ‖h S‖ ^ 2) - ‖meanCoefficient h‖ ^ 2 * Real.exp (-S₀) -
          ∫ T in Ioc (-S₀) T₂, ‖pulseReflected h T‖ ^ 2) ∧
    (∀ (idx : Finset ℕ) (c : ℕ → ℂ) (f : ℕ → CompactPulse) (W : Set ℝ),
      (∫ T in W, ‖pulseReflected (mixedPulse idx c f) T‖ ^ 2) =
        (∑ i ∈ idx, ‖c i‖ ^ 2 * ∫ T in W, ‖pulseReflected (f i) T‖ ^ 2) +
          ∑ i ∈ idx, ∑ j ∈ idx.erase i,
            ((c i * (starRingEnd ℂ) (c j)) *
              ∫ T in W, pulseReflected (f i) T * (starRingEnd ℂ) (pulseReflected (f j) T)).re) ∧
    -- (2) Unconditional actual-`ζ` cusp escape for all `0 < σ < 3001/48000` (`> 1/16`)
    (∀ {σ : ℝ}, 0 < σ → σ < 3001 / 48000 → ∀ h : CompactPulse,
      ∃ C : ℝ, 0 ≤ C ∧
        (∀ T : ℝ, 0 ≤ T → ‖pulseReflected h T‖ ≤ C * Real.exp (-σ * T)) ∧
        (∀ T₂ : ℝ, 0 ≤ T₂ →
          (∫ T in Ioi T₂, ‖pulseReflected h T‖ ^ 2) ≤
            (C ^ 2 / (2 * σ)) * Real.exp (-2 * σ * T₂))) ∧
    -- (3) Finite-Time Inequality 1: strict `(1 - 1/q²)` cusp escape-energy separation
    (∀ {q : ℕ}, 1 < q → ∀ {σ S₀ : ℝ}, 1 / 2 < σ → σ < 1 → 0 < S₀ → S₀ < Real.log q →
      ∃ h : CompactPulse, (∀ s : ℝ, S₀ < |s| → h s = 0) ∧ meanCoefficient h = 0 ∧
        0 < (∫ T in Ioi (2 * Real.log q - S₀),
              ‖twinReflected q ((q : ℝ) ^ σ + (q : ℝ) ^ (1 - σ)) h T‖ ^ 2) -
            (∫ T in Ioi (2 * Real.log q - S₀), ‖pulseReflected h T‖ ^ 2)) ∧
    -- (4) Finite-Time Inequality 2: explicit mixed-pulse `p²` vs `p q` interference separation
    (∀ {p q : ℕ}, p.Prime → q.Prime → p ≠ q → ∀ {σ : ℝ}, 1 / 2 < σ → σ < 1 → ∀ c_pq : ℂ,
      ∃ h₀ : CompactPulse,
        let r : ℝ := (p : ℝ) ^ σ
        let u : ℝ := (p : ℝ) ^ (1 - σ)
        let h_plus := threeChannelMixedPulse p q 1 1 c_pq h₀
        let h_minus := threeChannelMixedPulse p q 1 (-1) c_pq h₀
        (∀ θ : ℝ, excessPulseGroupDelay p r u
            (threeChannelMixedPulse p q 1 1 (Complex.exp (I * (θ : ℂ)) * c_pq) h₀) =
          excessPulseGroupDelay p r u h_plus) ∧
        0 < excessPulseGroupDelay p r u h_plus - excessPulseGroupDelay p r u h_minus ∧
        (∃ Ω₀ : ℝ, 0 < Ω₀ ∧ ∀ Ω : ℝ, Ω₀ ≤ Ω →
          (bandGroupDelay modularReducedScattering Ω h_plus -
            bandGroupDelay modularReducedScattering Ω h_minus) <
          (bandGroupDelay (PositiveEulerHorizon.reducedScattering p (r + u)) Ω h_plus -
            bandGroupDelay (PositiveEulerHorizon.reducedScattering p (r + u)) Ω h_minus))) ∧
    -- (5) Negative resolution of growing-window uniform constants even with `b(p²) = +1/2`
    (∀ (N M : ℕ) {δ : ℝ}, 0 < δ →
      ∃ (p k : ℕ), p.Prime ∧ N < p ∧ max 2 M ≤ k ∧
        ∃ (R U : ℝ), 1 < U ∧ U < R ∧ R * U = (p ^ (2 * k) : ℕ) ∧
          eulerLogCoeff (p ^ (2 * k)) (-(R : ℂ)) (-(U : ℂ)) (p ^ 2) = 1 / 2 ∧
          0 < (eulerLogCoeff (p ^ (2 * k)) (-(R : ℂ)) (-(U : ℂ)) (p ^ (2 * k))).re ∧
          (∃ h : CompactPulse, ¬ ∃ C : ℝ, ∀ τ : ℝ, 0 ≤ τ →
            ‖twinReflected (p ^ (2 * k)) (R + U) h τ‖ ≤ C * Real.exp (-δ * τ))) ∧
    -- (6) Finite decay-curve indecisiveness for every fixed nonzero pulse
    (∀ (h : CompactPulse), (∃ S : ℝ, h S ≠ 0) → ∀ {ε σ : ℝ}, 0 < ε → 1 / 2 < σ → σ < 1 →
      ∃ γ : ℝ, 0 < γ ∧
        (∀ T : ℝ, ‖quartetReflected σ γ h T - pulseReflected h T‖ < ε) ∧
        (∀ δ : ℝ, (1 - σ) / 2 < δ →
          ¬ ∃ C : ℝ, ∀ T : ℝ, 0 ≤ T → ‖quartetReflected σ γ h T‖ ≤ C * Real.exp (-δ * T))) := by
  refine ⟨echoKernel_eq_five_channels,
    fun h {_ _} hS₀ hT₂ => integral_Ioi_norm_sq_pulseReflected h hS₀ hT₂,
    fun idx c f W => by
      rw [Subsingleton.elim instDecidableEqNat (Classical.decEq ℕ)]
      exact setIntegral_norm_sq_mixedPulse_reflected idx c f W,
    fun {_} hσ0 hσ h => (unconditional_cusp_escape_sub_seven_eighths hσ0 hσ h).2,
    fun {_} hq {_ _} h0 h1 hS₀_pos hS₀_lt =>
      (finite_time_cusp_escape_separation hq h0 h1 hS₀_pos hS₀_lt).2,
    ?_, ?_, ?_⟩
  · intro p q hp hq hpq σ h0 h1 c_pq
    set R₀ : ℝ := mixedPrimeGap p q / 4
    have hR₀ : 0 < R₀ := by dsimp only [R₀]; linarith [mixedPrimeGap_pos hp hq]
    set h₀ := scaledBumpPulse R₀ hR₀
    have hsupp : ∀ s : ℝ, R₀ < |s| → h₀ s = 0 := fun s hs => scaledBumpPulse_eq_zero_of_le hR₀ hs.le
    have hgap : 2 * R₀ < mixedPrimeGap p q := by dsimp only [R₀]; linarith [mixedPrimeGap_pos hp hq]
    have hpos := integral_norm_sq_scaledBumpPulse_pos hR₀
    obtain ⟨hinv, _, hdiff_pos, hband⟩ :=
      finite_time_mixed_pulse_prime_square_distinction hp hq hpq h0 h1 h₀ hsupp hgap hpos c_pq
    exact ⟨h₀, fun θ => hinv 1 1 θ, hdiff_pos, hband⟩
  · intro N M δ hδ
    obtain ⟨⟨p, k, hp, R, U, hpN, hkM, hU, hUR, hRU, _, _, _, _, _, _, hb2, hbk, _, _, _, _, _,
      _, _, _, hfail⟩, _⟩ := no_uniform_escape_rate_from_prime_traversal_and_passivity N M hδ
    exact ⟨p, k, hp, hpN, hkM, R, U, hU, hUR, hRU, hb2, hbk, hfail⟩
  · intro h hne ε σ hε h0 h1
    obtain ⟨γ, hγ, _, _, _, _, _, _, _, happrox, hfail⟩ :=
      finite_decay_curve_cannot_decide_asymptotic_exponent h hne hε h0 h1
    exact ⟨γ, hγ, happrox, hfail⟩

end GaloisForLFunctions.BlackHoleRingdown

end
