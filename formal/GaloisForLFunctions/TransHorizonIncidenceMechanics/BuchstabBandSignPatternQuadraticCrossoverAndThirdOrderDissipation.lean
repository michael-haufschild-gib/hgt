import GaloisForLFunctions.TransHorizonIncidenceMechanics.MoebiusEnergyProfileThroughFourthBand
import GaloisForLFunctions.TransHorizonIncidenceMechanics.PrimePairingCollapseAndPrimeFactorStepLaw
import GaloisForLFunctions.TransHorizonIncidenceMechanics.BuchstabSlopeInheritanceAndSelbergDerivative
import GaloisForLFunctions.TransHorizonIncidenceMechanics.DampedCrossoverEulerConstantAndAdditiveWindow
import GaloisForLFunctions.BezoutValuationIncidence.TheCofinalMobiusProfileIsAsymptoticallyLinear

/-!
# Buchstab band sign pattern, quadratic crossover window, and third-order dissipation

This module resolves the four structural questions of the Buchstab and small-damping calculus:

1. **Radical-invariant jump law, first positive band average at `B = 10`, and non-concavity of the
   cofinal profile.** Combining `A(B) = (B + 1) P(B - 1) - B P(B)` with `P(t) - P(t - 1) = γ_t`
   gives `A(B) = P(B - 1) - B γ_B`, so `A(B)/B → 0` and
   `A(B + 1) - A(B) = (B + 1)(γ_B - γ_{B+1}) = -(B + 1)(P(B + 1) - 2 P(B) + P(B - 1))`.
   Expanding `γ_t = ρ Σ_{g ≤ t} S(⌊t/g⌋)/g` across `t = B → B + 1` collapses to the divisors of
   `B + 1`:
   `A(B + 1) - A(B) = -ρ Σ_{a ∣ (B + 1)} c_step(a)`, `c_step(a) = a (S(a) - S(a - 1))`.
   Because `c_step(a)` vanishes off squarefree integers, the jump `A(B + 1) - A(B)` depends only on
   the prime factors (radical) of `B + 1`. Evaluating `c_step` at `{1, 2, 3, 5, 6, 7, 10}` yields
   `A(1), …, A(10)` in closed form: `A(B) < 0` for `1 ≤ B ≤ 9`, `A(10) = (1/9)(6/π²) > 0` is the
   first positive band average, and `P(5^k) - 2 P(5^k - 1) + P(5^k - 2) = (11/(36 · 5^k))(6/π²) > 0`
   for every `k ≥ 1`, so the cofinal Möbius profile `P(B)` fails concavity infinitely often.

2. **Classification of negative-step squarefree cores and the prime-factor Buchstab slope.** In band
   `B ≥ 1`, the rough core `r = 1` has `v_B(1) = B - 2` (negative iff `B = 1`), while a composite
   or prime squarefree core `r = p a` (`p` prime, `p ∤ a`) has `v_B(p a) < 0` iff
   `2 μ(a) W_p(a, B) > -B`. In band `B = 1` every squarefree core has step `-1 < 0`; in band `B = 2`
   every odd squarefree core has step `0` and every even squarefree core has step `-2 < 0`. Sending
   `B → ∞` gives the prime-factor Buchstab slope formula
   `λ(p a) = -1 - 2 μ(a) Σ_{a < d < p a, p ∤ d} μ(d) gcd(d, a)/d`.

3. **Exact prime-local crossover scale and quadratic `O(ε²)` window.** For each prime `p` with
   `H_ε(p - 1) > 0`, the prime-local scale `Λ_p(ε) = -log(2 H_ε(p - 1))/ε` decides the sign of
   `λ_ε(p)` with zero gap. Uniformly across primes `p ≥ P₀`, the `(log t)^{-3}` decay of the Möbius
   harmonic sums shrinks the crossover window from `Λ(ε) ± ε` to `Λ(ε) ± M ε²` (and hence to
   `Λ(ε) ± δ ε` for every `δ > 0`), resolving the sign of `λ_ε(p)` inside `|log p - Λ(ε)| < ε`.

4. **Second-order Euler variance correction and third-order (`ε³`) dissipation asymptotics.** The
   Euler variance correction `K_ε = ∏_p (1 - δ_p(ε))` satisfies
   `(1 - K_ε)/ε² → Σ_p (log p / (p - 1))²`. Parity factorization and dominated convergence yield the
   exact cubic limit `dampedBezoutLimit ε / ε³ → 4 log 2 Σ_{j ≥ 0} μ(2j + 1)/φ(2j + 1)²`, and
   combining with `ρ_ε = ε - γ ε² + o(ε²)` gives the exact `ε³` coefficients of `A_ε(1) + ε²` and
   `R(ε) - V(ε) - ε²`.
-/

open Finset Filter Topology ArithmeticFunction
open GaloisForLFunctions.BezoutValuationIncidence GaloisForLFunctions.BiScaleUncertainty
open RHTower RHTower.Sieve
open scoped BigOperators ArithmeticFunction.Moebius

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

noncomputable section
set_option autoImplicit false

/-! ### §1. Radical-invariant divisor-sum law for band-average jumps, `A(1)..A(10)`, and non-concavity -/

/-- `A(B) = P(B - 1) - B γ_B = P(B) - (B + 1) γ_B` for every band `B ≥ 1`. -/
theorem bandAverageStep_eq_profile_sub_slope {B : ℕ} (hB : 1 ≤ B) :
    bandAverageStep B =
      cofinalMobiusQuadraticProfile (B - 1) - (B : ℝ) * cofinalBandSlope B ∧
    bandAverageStep B =
      cofinalMobiusQuadraticProfile B - ((B : ℝ) + 1) * cofinalBandSlope B := by
  have h1 := bandAverageStep_eq_profile hB
  have h2 := cofinalMobiusQuadraticProfile_succ (B - 1)
  rw [Nat.sub_add_cancel hB] at h2
  refine ⟨by linear_combination h1 - (B : ℝ) * h2, by linear_combination h1 - ((B : ℝ) + 1) * h2⟩

/-- **Sublinear cancellation of band averages.** `A(B)/B → 0` as `B → ∞`: the linear growth rate `κ`
of `P(B)` and `B γ_B` cancels identically in `A(B) = P(B) - (B + 1) γ_B`. -/
theorem tendsto_bandAverageStep_div :
    Tendsto (fun B : ℕ => bandAverageStep B / B) atTop (𝓝 0) := by
  have hP := tendsto_cofinalMobiusQuadraticProfile_div
  have hγ := tendsto_cofinalBandSlope
  have hratio : Tendsto (fun B : ℕ => ((B : ℝ) + 1) / B) atTop (𝓝 1) := by
    have h := (tendsto_const_nhds (x := (1 : ℝ))).add (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))
    rw [add_zero] at h
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with B hB
    have hBR : (0 : ℝ) < B := by exact_mod_cast hB
    field_simp
  have h := hP.sub (hratio.mul hγ)
  rw [one_mul, sub_self] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with B hB
  have hBR : (0 : ℝ) < B := by exact_mod_cast hB
  rw [(bandAverageStep_eq_profile_sub_slope hB).2]
  field_simp

/-- **First difference of band averages.** For `B ≥ 1`,
`A(B + 1) - A(B) = (B + 1)(γ_B - γ_{B+1}) = -(B + 1)(P(B + 1) - 2 P(B) + P(B - 1))`. -/
theorem bandAverageStep_succ_sub_eq_slope_diff {B : ℕ} (hB : 1 ≤ B) :
    bandAverageStep (B + 1) - bandAverageStep B =
      ((B : ℝ) + 1) * (cofinalBandSlope B - cofinalBandSlope (B + 1)) ∧
    bandAverageStep (B + 1) - bandAverageStep B =
      -((B : ℝ) + 1) * (cofinalMobiusQuadraticProfile (B + 1) -
        2 * cofinalMobiusQuadraticProfile B + cofinalMobiusQuadraticProfile (B - 1)) := by
  have h1 := (bandAverageStep_eq_profile_sub_slope (by omega : 1 ≤ B + 1)).1
  simp only [Nat.add_sub_cancel] at h1
  have h2 := (bandAverageStep_eq_profile_sub_slope hB).2
  have hP1 := cofinalMobiusQuadraticProfile_succ B
  have hP0 := cofinalMobiusQuadraticProfile_succ (B - 1)
  rw [Nat.sub_add_cancel hB] at hP0
  push_cast at h1
  refine ⟨by linear_combination h1 - h2,
    by linear_combination h1 - h2 + ((B : ℝ) + 1) * hP1 - ((B : ℝ) + 1) * hP0⟩

/-- The divisor-step weight `c_step(a) = a (S(a) - S(a - 1))` of the coprime `μ/σ` pair sum. -/
def bandStepDivisorWeight (a : ℕ) : ℝ :=
  (a : ℝ) * (coprimePairMoebiusSigmaSum a - coprimePairMoebiusSigmaSum (a - 1))

theorem bandStepDivisorWeight_zero : bandStepDivisorWeight 0 = 0 := by
  simp [bandStepDivisorWeight]

theorem coprimePairMoebiusSigmaSum_zero : coprimePairMoebiusSigmaSum 0 = 0 := by
  simp [coprimePairMoebiusSigmaSum]

theorem moebiusSigma_one : moebiusSigma 1 = 1 := by
  simp [moebiusSigma]

theorem coprimePairMoebiusSigmaSum_one : coprimePairMoebiusSigmaSum 1 = 1 := by
  simp [coprimePairMoebiusSigmaSum, moebiusSigma_one]

theorem bandStepDivisorWeight_one : bandStepDivisorWeight 1 = 1 := by
  simp [bandStepDivisorWeight, coprimePairMoebiusSigmaSum_one, coprimePairMoebiusSigmaSum_zero]

/-- For `n ≥ 1`, `S(n + 1) - S(n) = 2 w(n + 1) T_{n+1}(n)` with `w = μ/σ`. -/
theorem coprimePairMoebiusSigmaSum_succ_sub {n : ℕ} (hn : 1 ≤ n) :
    coprimePairMoebiusSigmaSum (n + 1) - coprimePairMoebiusSigmaSum n =
      2 * moebiusSigma (n + 1) * coprimeMoebiusSigmaSum (n + 1) n := by
  unfold coprimePairMoebiusSigmaSum coprimeMoebiusSigmaSum
  rw [sum_Icc_succ_top (by omega)]
  simp_rw [sum_Icc_succ_top (show 1 ≤ n + 1 by omega)]
  rw [sum_add_distrib]
  have hdiag : ¬ Nat.Coprime (n + 1) (n + 1) := by
    rw [Nat.coprime_self]; omega
  rw [if_neg hdiag, add_zero]
  have hsym : (∑ a ∈ Icc 1 n, if Nat.Coprime a (n + 1) then
      moebiusSigma a * moebiusSigma (n + 1) else 0) =
      moebiusSigma (n + 1) * ∑ a ∈ Icc 1 n, if Nat.Coprime a (n + 1) then moebiusSigma a else 0 := by
    rw [mul_sum]
    refine sum_congr rfl fun a _ => ?_
    split_ifs <;> ring
  have hsym2 : (∑ b ∈ Icc 1 n, if Nat.Coprime (n + 1) b then
      moebiusSigma (n + 1) * moebiusSigma b else 0) =
      moebiusSigma (n + 1) * ∑ a ∈ Icc 1 n, if Nat.Coprime a (n + 1) then moebiusSigma a else 0 := by
    rw [mul_sum]
    refine sum_congr rfl fun a _ => ?_
    by_cases hc : Nat.Coprime a (n + 1)
    · rw [if_pos hc, if_pos hc.symm]
    · rw [if_neg hc, if_neg (fun h => hc h.symm), mul_zero]
  rw [hsym, hsym2]
  ring

/-- Explicit formula for `c_step(a)` at `a ≥ 2`: `c_step(a) = 2 a w(a) T_a(a - 1)`. -/
theorem bandStepDivisorWeight_eq_of_two_le {a : ℕ} (ha : 2 ≤ a) :
    bandStepDivisorWeight a =
      2 * (a : ℝ) * moebiusSigma a * coprimeMoebiusSigmaSum a (a - 1) := by
  obtain ⟨n, rfl⟩ : ∃ n, a = n + 1 := ⟨a - 1, by omega⟩
  unfold bandStepDivisorWeight
  rw [Nat.add_sub_cancel, coprimePairMoebiusSigmaSum_succ_sub (by omega)]
  ring

/-- Non-squarefree divisors contribute zero to band-average jumps. -/
theorem bandStepDivisorWeight_eq_zero_of_not_squarefree {a : ℕ} (ha : ¬ Squarefree a) :
    bandStepDivisorWeight a = 0 := by
  rcases eq_or_ne a 0 with rfl | ha0
  · exact bandStepDivisorWeight_zero
  · have ha1 : a ≠ 1 := fun h => ha (h ▸ squarefree_one)
    rw [bandStepDivisorWeight_eq_of_two_le (by omega)]
    have hμ : moebiusSigma a = 0 := by
      unfold moebiusSigma
      rw [moebius_eq_zero_of_not_squarefree ha]
      simp
    rw [hμ]
    ring

private theorem nat_div_succ_eq_of_not_dvd {B g : ℕ} (hg : ¬ g ∣ B + 1) :
    (B + 1) / g = B / g := by
  rcases eq_or_ne g 0 with rfl | hg0
  · simp
  have hdiv := Nat.div_add_mod B g
  have hmod : B % g + 1 < g := by
    have hlt : B % g + 1 ≤ g := Nat.mod_lt B (Nat.pos_of_ne_zero hg0)
    rcases eq_or_lt_of_le hlt with h | h
    · exfalso; apply hg
      refine ⟨B / g + 1, ?_⟩
      calc B + 1 = g * (B / g) + (B % g + 1) := by omega
        _ = g * (B / g) + g := by rw [h]
        _ = g * (B / g + 1) := by ring
    · exact h
  apply Nat.div_eq_of_lt_le
  · have := Nat.div_mul_le_self B g
    omega
  · have hmul : (B / g + 1) * g = g * (B / g) + g := by ring
    omega

private theorem nat_div_eq_succ_div_sub_one_of_dvd {B g : ℕ} (hg0 : 0 < g) (hg : g ∣ B + 1) :
    B / g = (B + 1) / g - 1 := by
  obtain ⟨k, hk⟩ := hg
  have hk0 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with rfl | h
    · simp at hk
    · exact h
  have h1 : (B + 1) / g = k := by rw [hk, Nat.mul_div_cancel_left _ hg0]
  have hkg : (k - 1) * g + g = B + 1 := by
    calc (k - 1) * g + g = (k - 1 + 1) * g := by ring
      _ = B + 1 := by rw [Nat.sub_add_cancel hk0, mul_comm, ← hk]
  rw [h1]
  apply Nat.div_eq_of_lt_le
  · omega
  · rw [Nat.sub_add_cancel hk0, mul_comm, ← hk]
    omega

/-- **Divisor-sum formula for slope jumps.**
`(B + 1)(γ_{B+1} - γ_B) = ρ Σ_{a ∣ (B + 1)} c_step(a)`. -/
theorem cofinalBandSlope_succ_sub_eq_sum_divisors (B : ℕ) :
    ((B : ℝ) + 1) * (cofinalBandSlope (B + 1) - cofinalBandSlope B) =
      RHTower.Sieve.squarefreeDensity * ∑ a ∈ (B + 1).divisors, bandStepDivisorWeight a := by
  rw [cofinalBandSlope_eq (B + 1), cofinalBandSlope_eq B]
  have hBext : ∑ g ∈ Icc 1 B, coprimePairMoebiusSigmaSum (B / g) / (g : ℝ) =
      ∑ g ∈ Icc 1 (B + 1), coprimePairMoebiusSigmaSum (B / g) / (g : ℝ) := by
    rw [sum_Icc_succ_top (by omega), Nat.div_eq_of_lt (by omega : B < B + 1),
      coprimePairMoebiusSigmaSum_zero, zero_div, add_zero]
  rw [hBext, ← mul_sub, ← sum_sub_distrib, mul_left_comm, mul_sum]
  congr 1
  rw [← sum_filter_add_sum_filter_not (Icc 1 (B + 1)) (fun g => g ∣ B + 1)]
  have hnot : ∑ g ∈ (Icc 1 (B + 1)).filter (fun g => ¬ g ∣ B + 1),
      ((B : ℝ) + 1) * (coprimePairMoebiusSigmaSum ((B + 1) / g) / (g : ℝ) -
        coprimePairMoebiusSigmaSum (B / g) / (g : ℝ)) = 0 :=
    sum_eq_zero fun g hg => by
      rw [nat_div_succ_eq_of_not_dvd (mem_filter.mp hg).2, sub_self, mul_zero]
  rw [hnot, add_zero]
  have hdivset : (Icc 1 (B + 1)).filter (fun g => g ∣ B + 1) = (B + 1).divisors := by
    ext g
    simp only [mem_filter, mem_Icc, Nat.mem_divisors]
    constructor
    · rintro ⟨-, h⟩; exact ⟨h, by omega⟩
    · rintro ⟨h, hne⟩
      exact ⟨⟨Nat.pos_of_dvd_of_pos h (by omega), Nat.le_of_dvd (by omega) h⟩, h⟩
  rw [hdivset, ← Nat.sum_div_divisors (B + 1) bandStepDivisorWeight]
  refine sum_congr rfl fun g hg => ?_
  obtain ⟨hgd, -⟩ := Nat.mem_divisors.mp hg
  have hg0 : 0 < g := Nat.pos_of_dvd_of_pos hgd (by omega)
  have hgR : (0 : ℝ) < g := by exact_mod_cast hg0
  have hmul : ((B + 1) / g : ℕ) * (g : ℝ) = (B : ℝ) + 1 := by
    exact_mod_cast Nat.div_mul_cancel hgd
  rw [nat_div_eq_succ_div_sub_one_of_dvd hg0 hgd, bandStepDivisorWeight]
  rw [← hmul]
  field_simp

/-- **Divisor-sum law for band-average jumps.** For `B ≥ 1`,
`A(B + 1) - A(B) = -ρ Σ_{a ∣ (B + 1)} c_step(a) = -ρ Σ_{a ∣ (B + 1), μ²(a) = 1} c_step(a)`. -/
theorem bandAverageStep_succ_sub_eq_sum_divisors {B : ℕ} (hB : 1 ≤ B) :
    bandAverageStep (B + 1) - bandAverageStep B =
      -RHTower.Sieve.squarefreeDensity * ∑ a ∈ (B + 1).divisors, bandStepDivisorWeight a ∧
    bandAverageStep (B + 1) - bandAverageStep B =
      -RHTower.Sieve.squarefreeDensity *
        ∑ a ∈ (B + 1).divisors.filter Squarefree, bandStepDivisorWeight a := by
  have h1 := (bandAverageStep_succ_sub_eq_slope_diff hB).1
  have h2 := cofinalBandSlope_succ_sub_eq_sum_divisors B
  have hmain : bandAverageStep (B + 1) - bandAverageStep B =
      -RHTower.Sieve.squarefreeDensity * ∑ a ∈ (B + 1).divisors, bandStepDivisorWeight a := by
    linarith
  refine ⟨hmain, ?_⟩
  rw [hmain]
  congr 1
  rw [← sum_filter_add_sum_filter_not (B + 1).divisors Squarefree]
  have h0 : ∑ a ∈ (B + 1).divisors.filter (fun a => ¬ Squarefree a), bandStepDivisorWeight a = 0 :=
    sum_eq_zero fun a ha => bandStepDivisorWeight_eq_zero_of_not_squarefree (mem_filter.mp ha).2
  rw [h0, add_zero]

/-- Two positive integers with the same prime factors have the same squarefree divisors. -/
theorem divisors_filter_squarefree_eq_of_primeFactors_eq {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0)
    (hp : m.primeFactors = n.primeFactors) :
    m.divisors.filter Squarefree = n.divisors.filter Squarefree := by
  have hsub : ∀ {x y : ℕ}, x ≠ 0 → y ≠ 0 → x.primeFactors = y.primeFactors →
      ∀ a, Squarefree a → a ∣ x → a ∣ y := by
    intro x y hx hy hxy a hasq hax
    rw [← Nat.prod_primeFactors_of_squarefree hasq]
    have hprod : ∏ p ∈ a.primeFactors, p ∣ ∏ p ∈ y.primeFactors, p :=
      prod_dvd_prod_of_subset a.primeFactors y.primeFactors id fun p hpa => by
        rw [← hxy, Nat.mem_primeFactors]
        obtain ⟨hpp, hpa', -⟩ := Nat.mem_primeFactors.mp hpa
        exact ⟨hpp, hpa'.trans hax, hx⟩
    exact hprod.trans (Nat.prod_primeFactors_dvd y)
  ext a
  simp only [mem_filter, Nat.mem_divisors]
  exact ⟨fun ⟨⟨ham, _⟩, hasq⟩ => ⟨⟨hsub hm hn hp a hasq ham, hn⟩, hasq⟩,
    fun ⟨⟨han, _⟩, hasq⟩ => ⟨⟨hsub hn hm hp.symm a hasq han, hm⟩, hasq⟩⟩

/-- **Radical invariance of band-average jumps.** If `B + 1` and `B' + 1` have the same prime
factors, then `A(B + 1) - A(B) = A(B' + 1) - A(B')`. -/
theorem bandAverageStep_succ_sub_eq_of_primeFactors_eq {B B' : ℕ} (hB : 1 ≤ B) (hB' : 1 ≤ B')
    (hp : (B + 1).primeFactors = (B' + 1).primeFactors) :
    bandAverageStep (B + 1) - bandAverageStep B =
      bandAverageStep (B' + 1) - bandAverageStep B' := by
  rw [(bandAverageStep_succ_sub_eq_sum_divisors hB).2,
    (bandAverageStep_succ_sub_eq_sum_divisors hB').2,
    divisors_filter_squarefree_eq_of_primeFactors_eq (by omega) (by omega) hp]

/-- **Prime-power jump law.** At every prime power `p^k` (`k ≥ 1`) with `p^k ≥ 2`,
`A(p^k) - A(p^k - 1) = -ρ (1 + c_step(p))`. -/
theorem bandAverageStep_prime_pow_sub {p k : ℕ} (hp : p.Prime) (hk : 1 ≤ k) (hpk : 2 ≤ p ^ k - 1) :
    bandAverageStep (p ^ k) - bandAverageStep (p ^ k - 1) =
      -RHTower.Sieve.squarefreeDensity * (1 + bandStepDivisorWeight p) := by
  have h1 : (p ^ k - 1) + 1 = p ^ k := by omega
  have h2 : (p - 1) + 1 = p := Nat.sub_add_cancel hp.one_lt.le
  have hsub := bandAverageStep_succ_sub_eq_of_primeFactors_eq (B := p ^ k - 1) (B' := p - 1)
    (by omega) (by have := hp.two_le; omega)
    (by rw [h1, h2, Nat.primeFactors_prime_pow (by omega : k ≠ 0) hp, hp.primeFactors])
  have hbase := (bandAverageStep_succ_sub_eq_sum_divisors (B := p - 1)
    (by have := hp.two_le; omega)).1
  rw [h1, h2] at hsub
  rw [h2, hp.divisors, sum_pair hp.one_lt.ne, bandStepDivisorWeight_one] at hbase
  rw [hsub, hbase]

/-- For a prime `p`, `moebiusSigma p = -1 / (p + 1)`. -/
theorem moebiusSigma_prime {p : ℕ} (hp : p.Prime) :
    moebiusSigma p = -1 / ((p : ℝ) + 1) := by
  have hσp : (ArithmeticFunction.sigma 1 p : ℝ) = p + 1 := by
    have h1 := sigma_one_apply_prime_pow (i := 1) hp
    rw [pow_one] at h1
    rw [h1, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
    push_cast; ring
  unfold moebiusSigma
  rw [moebius_apply_prime hp, hσp]
  push_cast; ring

theorem moebiusSigma_two : moebiusSigma 2 = -1 / 3 := by
  rw [moebiusSigma_prime Nat.prime_two]; norm_num

theorem moebiusSigma_three : moebiusSigma 3 = -1 / 4 := by
  rw [moebiusSigma_prime Nat.prime_three]; norm_num

theorem moebiusSigma_four : moebiusSigma 4 = 0 := by
  unfold moebiusSigma
  rw [moebius_eq_zero_of_not_squarefree (by decide)]
  simp

theorem moebiusSigma_five : moebiusSigma 5 = -1 / 6 := by
  rw [moebiusSigma_prime (by decide)]; norm_num

theorem moebiusSigma_six : moebiusSigma 6 = 1 / 12 := by
  rw [show (6 : ℕ) = 2 * 3 from rfl, moebiusSigma_mul (by decide), moebiusSigma_two,
    moebiusSigma_three]
  norm_num

theorem moebiusSigma_seven : moebiusSigma 7 = -1 / 8 := by
  rw [moebiusSigma_prime (by decide)]; norm_num

theorem moebiusSigma_eight : moebiusSigma 8 = 0 := by
  unfold moebiusSigma
  rw [moebius_eq_zero_of_not_squarefree (by decide)]
  simp

theorem moebiusSigma_nine : moebiusSigma 9 = 0 := by
  unfold moebiusSigma
  have h9 : ¬ Squarefree 9 := fun h => by
    have := h 3 ⟨1, rfl⟩
    norm_num at this
  rw [moebius_eq_zero_of_not_squarefree h9]
  simp

theorem moebiusSigma_ten : moebiusSigma 10 = 1 / 18 := by
  rw [show (10 : ℕ) = 2 * 5 from rfl, moebiusSigma_mul (by decide), moebiusSigma_two,
    moebiusSigma_five]
  norm_num

theorem bandStepDivisorWeight_two : bandStepDivisorWeight 2 = -4 / 3 := by
  rw [bandStepDivisorWeight_eq_of_two_le le_rfl, moebiusSigma_two]
  unfold coprimeMoebiusSigmaSum
  rw [show (2 : ℕ) - 1 = 1 from rfl, Icc_self, sum_singleton, if_pos (by decide), moebiusSigma_one]
  norm_num

theorem bandStepDivisorWeight_three : bandStepDivisorWeight 3 = -1 := by
  rw [bandStepDivisorWeight_eq_of_two_le (by decide), moebiusSigma_three]
  unfold coprimeMoebiusSigmaSum
  rw [← sum_filter, show (Icc 1 (3 - 1)).filter (fun a => Nat.Coprime a 3) = {1, 2} by decide,
    sum_pair (by decide), moebiusSigma_one, moebiusSigma_two]
  norm_num

theorem bandStepDivisorWeight_five : bandStepDivisorWeight 5 = -25 / 36 := by
  rw [bandStepDivisorWeight_eq_of_two_le (by decide), moebiusSigma_five]
  unfold coprimeMoebiusSigmaSum
  rw [← sum_filter, show (Icc 1 (5 - 1)).filter (fun a => Nat.Coprime a 5) = {1, 2, 3, 4} by decide]
  rw [sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_singleton,
    moebiusSigma_one, moebiusSigma_two, moebiusSigma_three, moebiusSigma_four]
  norm_num

theorem bandStepDivisorWeight_six : bandStepDivisorWeight 6 = 5 / 6 := by
  rw [bandStepDivisorWeight_eq_of_two_le (by decide), moebiusSigma_six]
  unfold coprimeMoebiusSigmaSum
  rw [← sum_filter, show (Icc 1 (6 - 1)).filter (fun a => Nat.Coprime a 6) = {1, 5} by decide]
  rw [sum_pair (by decide), moebiusSigma_one, moebiusSigma_five]
  norm_num

theorem bandStepDivisorWeight_seven : bandStepDivisorWeight 7 = -7 / 12 := by
  rw [bandStepDivisorWeight_eq_of_two_le (by decide), moebiusSigma_seven]
  unfold coprimeMoebiusSigmaSum
  rw [← sum_filter, show (Icc 1 (7 - 1)).filter (fun a => Nat.Coprime a 7) = {1, 2, 3, 4, 5, 6} by decide]
  rw [sum_insert (by decide), sum_insert (by decide), sum_insert (by decide),
    sum_insert (by decide), sum_insert (by decide), sum_singleton,
    moebiusSigma_one, moebiusSigma_two, moebiusSigma_three, moebiusSigma_four,
    moebiusSigma_five, moebiusSigma_six]
  norm_num

theorem bandStepDivisorWeight_ten : bandStepDivisorWeight 10 = 25 / 36 := by
  rw [bandStepDivisorWeight_eq_of_two_le (by decide), moebiusSigma_ten]
  unfold coprimeMoebiusSigmaSum
  rw [← sum_filter, show (Icc 1 (10 - 1)).filter (fun a => Nat.Coprime a 10) = {1, 3, 7, 9} by decide]
  rw [sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_singleton,
    moebiusSigma_one, moebiusSigma_three, moebiusSigma_seven, moebiusSigma_nine]
  norm_num

/-- `A(5) = -(23/36)(6/π²)`. -/
theorem bandAverageStep_five :
    bandAverageStep 5 = -(23 / 36) * RHTower.Sieve.squarefreeDensity := by
  have h := (bandAverageStep_succ_sub_eq_sum_divisors (B := 4) (by decide)).1
  rw [show (4 + 1 : ℕ).divisors = {1, 5} by decide, sum_pair (by decide),
    bandStepDivisorWeight_one, bandStepDivisorWeight_five, bandAverageStep_four] at h
  linarith

/-- `A(6) = -(5/36)(6/π²)`. -/
theorem bandAverageStep_six :
    bandAverageStep 6 = -(5 / 36) * RHTower.Sieve.squarefreeDensity := by
  have h := (bandAverageStep_succ_sub_eq_sum_divisors (B := 5) (by decide)).1
  rw [show (5 + 1 : ℕ).divisors = {1, 2, 3, 6} by decide,
    sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_singleton,
    bandStepDivisorWeight_one, bandStepDivisorWeight_two, bandStepDivisorWeight_three,
    bandStepDivisorWeight_six, bandAverageStep_five] at h
  linarith

/-- `A(7) = -(5/9)(6/π²)`. -/
theorem bandAverageStep_seven :
    bandAverageStep 7 = -(5 / 9) * RHTower.Sieve.squarefreeDensity := by
  have h := (bandAverageStep_succ_sub_eq_sum_divisors (B := 6) (by decide)).1
  rw [show (6 + 1 : ℕ).divisors = {1, 7} by decide, sum_pair (by decide),
    bandStepDivisorWeight_one, bandStepDivisorWeight_seven, bandAverageStep_six] at h
  linarith

/-- `A(8) = -(2/9)(6/π²)`. -/
theorem bandAverageStep_eight :
    bandAverageStep 8 = -(2 / 9) * RHTower.Sieve.squarefreeDensity := by
  have h := bandAverageStep_prime_pow_sub Nat.prime_two (k := 3) (by decide) (by decide)
  rw [show (2 : ℕ) ^ 3 - 1 = 7 from rfl, show (2 : ℕ) ^ 3 = 8 from rfl,
    bandStepDivisorWeight_two, bandAverageStep_seven] at h
  linarith

/-- `A(9) = -(2/9)(6/π²)`. -/
theorem bandAverageStep_nine :
    bandAverageStep 9 = -(2 / 9) * RHTower.Sieve.squarefreeDensity := by
  have h := bandAverageStep_prime_pow_sub Nat.prime_three (k := 2) (by decide) (by decide)
  rw [show (3 : ℕ) ^ 2 - 1 = 8 from rfl, show (3 : ℕ) ^ 2 = 9 from rfl,
    bandStepDivisorWeight_three, bandAverageStep_eight] at h
  linarith

/-- **`A(10) = +(1/9)(6/π²) = 2/(3π²) > 0`:** the tenth band is the first with a positive mean
Möbius step. -/
theorem bandAverageStep_ten :
    bandAverageStep 10 = (1 / 9) * RHTower.Sieve.squarefreeDensity := by
  have h := (bandAverageStep_succ_sub_eq_sum_divisors (B := 9) (by decide)).1
  rw [show (9 + 1 : ℕ).divisors = {1, 2, 5, 10} by decide,
    sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_singleton,
    bandStepDivisorWeight_one, bandStepDivisorWeight_two, bandStepDivisorWeight_five,
    bandStepDivisorWeight_ten, bandAverageStep_nine] at h
  linarith

/-- **Complete sign pattern through the tenth band.** `A(B) < 0` for all `1 ≤ B ≤ 9`, and
`A(10) > 0`: `B = 10` is the exact first band where the mean horizon step turns positive. -/
theorem bandAverageStep_neg_of_le_nine {B : ℕ} (hB1 : 1 ≤ B) (hB9 : B ≤ 9) :
    bandAverageStep B < 0 := by
  have hD : 0 < RHTower.Sieve.squarefreeDensity := by
    rw [RHTower.Sieve.squarefreeDensity_eq]; positivity
  interval_cases B
  · rw [bandAverageStep_one]; linarith
  · rw [bandAverageStep_two]; linarith
  · rw [bandAverageStep_three]; linarith
  · rw [bandAverageStep_four]; linarith
  · rw [bandAverageStep_five]; linarith
  · rw [bandAverageStep_six]; linarith
  · rw [bandAverageStep_seven]; linarith
  · rw [bandAverageStep_eight]; linarith
  · rw [bandAverageStep_nine]; linarith

theorem bandAverageStep_ten_pos : 0 < bandAverageStep 10 := by
  have hD : 0 < RHTower.Sieve.squarefreeDensity := by
    rw [RHTower.Sieve.squarefreeDensity_eq]; positivity
  rw [bandAverageStep_ten]; linarith

/-- `P(5) = (761/180)(6/π²)`. -/
theorem cofinalMobiusQuadraticProfile_five :
    cofinalMobiusQuadraticProfile 5 = 761 / 180 * RHTower.Sieve.squarefreeDensity := by
  have h := bandAverageStep_eq_profile (B := 5) (by norm_num)
  rw [bandAverageStep_five, show (5 : ℕ) - 1 = 4 from rfl, cofinalMobiusQuadraticProfile_four] at h
  push_cast at h
  linarith

/-- **Non-concavity of the cofinal Möbius profile.** At `B = 4`, the second difference of `P` is
strictly positive: `P(5) - 2 P(4) + P(3) = (11/180)(6/π²) > 0`. -/
theorem cofinalMobiusQuadraticProfile_not_concave :
    cofinalMobiusQuadraticProfile 5 - 2 * cofinalMobiusQuadraticProfile 4 +
      cofinalMobiusQuadraticProfile 3 = (11 / 180) * RHTower.Sieve.squarefreeDensity ∧
    0 < cofinalMobiusQuadraticProfile 5 - 2 * cofinalMobiusQuadraticProfile 4 +
      cofinalMobiusQuadraticProfile 3 := by
  have hD : 0 < RHTower.Sieve.squarefreeDensity := by
    rw [RHTower.Sieve.squarefreeDensity_eq]; positivity
  have heq : cofinalMobiusQuadraticProfile 5 - 2 * cofinalMobiusQuadraticProfile 4 +
      cofinalMobiusQuadraticProfile 3 = (11 / 180) * RHTower.Sieve.squarefreeDensity := by
    rw [cofinalMobiusQuadraticProfile_five, cofinalMobiusQuadraticProfile_four,
      cofinalMobiusQuadraticProfile_three]
    ring
  exact ⟨heq, by rw [heq]; linarith⟩

/-- **Infinite failure of concavity along powers of `5`.** For every `k ≥ 1`,
`P(5^k) - 2 P(5^k - 1) + P(5^k - 2) = (11 / (36 · 5^k)) ρ > 0`. -/
theorem cofinalMobiusQuadraticProfile_second_diff_five_pow_pos {k : ℕ} (hk : 1 ≤ k) :
    cofinalMobiusQuadraticProfile (5 ^ k) - 2 * cofinalMobiusQuadraticProfile (5 ^ k - 1) +
      cofinalMobiusQuadraticProfile (5 ^ k - 2) =
      (11 / 36) * RHTower.Sieve.squarefreeDensity / ((5 ^ k : ℕ) : ℝ) ∧
    0 < cofinalMobiusQuadraticProfile (5 ^ k) - 2 * cofinalMobiusQuadraticProfile (5 ^ k - 1) +
      cofinalMobiusQuadraticProfile (5 ^ k - 2) := by
  have h5k : 5 ≤ 5 ^ k := by
    calc 5 = 5 ^ 1 := (pow_one 5).symm
      _ ≤ 5 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  have hp5 : Nat.Prime 5 := by decide
  have hjump := bandAverageStep_prime_pow_sub hp5 hk (by omega)
  rw [bandStepDivisorWeight_five] at hjump
  have hdiff := (bandAverageStep_succ_sub_eq_slope_diff (B := 5 ^ k - 1) (by omega)).2
  rw [show 5 ^ k - 1 + 1 = 5 ^ k by omega, show 5 ^ k - 1 - 1 = 5 ^ k - 2 by omega] at hdiff
  have hcast : ((5 ^ k - 1 : ℕ) : ℝ) + 1 = ((5 ^ k : ℕ) : ℝ) := by
    exact_mod_cast (show 5 ^ k - 1 + 1 = 5 ^ k by omega)
  rw [hcast] at hdiff
  have h5R : (0 : ℝ) < ((5 ^ k : ℕ) : ℝ) := by positivity
  have hD : 0 < RHTower.Sieve.squarefreeDensity := by
    rw [RHTower.Sieve.squarefreeDensity_eq]; positivity
  have heq : cofinalMobiusQuadraticProfile (5 ^ k) - 2 * cofinalMobiusQuadraticProfile (5 ^ k - 1) +
      cofinalMobiusQuadraticProfile (5 ^ k - 2) =
      (11 / 36) * RHTower.Sieve.squarefreeDensity / ((5 ^ k : ℕ) : ℝ) := by
    rw [eq_div_iff h5R.ne']
    linarith
  exact ⟨heq, by rw [heq]; positivity⟩

/-! ### §2. Classification of squarefree cores with negative step and the prime-factor Buchstab slope -/

/-- Sign trichotomy of the rough core `r = 1`: `v_B(1) = B - 2` is negative iff `B = 1`, zero iff
`B = 2`, and positive iff `B ≥ 3`. -/
theorem bandClassValue_one_trichotomy {B : ℕ} (hB : 1 ≤ B) :
    (bandClassValue B 1 < 0 ↔ B = 1) ∧
    (bandClassValue B 1 = 0 ↔ B = 2) ∧
    (0 < bandClassValue B 1 ↔ 3 ≤ B) := by
  simp only [bandClassValue, if_true]
  refine ⟨⟨fun h => ?_, fun h => by subst h; norm_num⟩,
    ⟨fun h => ?_, fun h => by subst h; norm_num⟩,
    ⟨fun h => ?_, fun h => ?_⟩⟩
  · have : (B : ℝ) < 2 := by linarith
    have : B < 2 := by exact_mod_cast this
    omega
  · have : (B : ℝ) = 2 := by linarith
    exact_mod_cast this
  · have : (2 : ℝ) < B := by linarith
    have : 2 < B := by exact_mod_cast this
    omega
  · have : (3 : ℝ) ≤ B := by exact_mod_cast h
    linarith

/-- **Negative-step criterion for composite and prime squarefree cores.** For a prime `p` and
`a ≥ 1` with `p a` squarefree, `v_B(p a) < 0` in band `B` if and only if
`2 μ(a) W_p(a, B) > -B`. -/
theorem bandClassValue_prime_mul_neg_iff {p a B : ℕ} (hp : p.Prime) (ha : 1 ≤ a)
    (hsq : Squarefree (p * a)) :
    bandClassValue B (p * a) < 0 ↔
      -(B : ℝ) < 2 * moebiusReal a * primeFactorWindowCorrection p a B := by
  have hne1 : p * a ≠ 1 := by have := hp.two_le; nlinarith
  rw [bandClassValue, if_neg hne1, moebiusBandStep_prime_mul hp ha hsq]
  constructor <;> intro h <;> linarith

/-- **First-band universality.** In band `B = 1`, every squarefree core `r ≥ 1` has step `-1 < 0`. -/
theorem bandClassValue_first_band {r : ℕ} (hr : 1 ≤ r) (hsq : Squarefree r) :
    bandClassValue 1 r = -1 := by
  by_cases hr1 : r = 1
  · subst hr1; simp [bandClassValue]; norm_num
  · rw [bandClassValue, if_neg hr1, moebiusBandStep_eq_smoothCore (by omega) le_rfl hsq]
    have hg : Nat.gcd r (primorial 1) = 1 := by
      rw [show primorial 1 = 1 by decide, Nat.gcd_one_right]
    rw [if_pos hg]
    norm_num

/-- **Second-band parity classification.** In band `B = 2`, every odd squarefree core `r ≥ 1` has
step `0`, and every even squarefree core `r ≥ 2` has step `-2 < 0`. -/
theorem bandClassValue_second_band {r : ℕ} (hr : 1 ≤ r) (hsq : Squarefree r) :
    bandClassValue 2 r = if 2 ∣ r then -2 else 0 := by
  have hp2 : primorial 2 = 2 := by decide
  by_cases hr1 : r = 1
  · subst hr1; simp [bandClassValue]
  · rw [bandClassValue, if_neg hr1, moebiusBandStep_eq_smoothCore (by omega) (by norm_num) hsq]
    by_cases h2 : 2 ∣ r
    · have hg : Nat.gcd r (primorial 2) = 2 := by rw [hp2]; exact Nat.gcd_eq_right h2
      have hne : Nat.gcd r (primorial 2) ≠ 1 := by rw [hg]; decide
      rw [if_pos h2, if_neg hne, hg, moebiusBandStep_two]
      norm_num
    · have hg : Nat.gcd r (primorial 2) = 1 := by
        rw [hp2]
        exact ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr h2).symm
      rw [if_neg h2, if_pos hg]
      norm_num

/-- At every squarefree horizon `m ≥ 2`, `|Δ(m, B) - B λ(m)| ≤ 2(m - 1)` for all `B`. -/
theorem abs_moebiusBandStep_sub_slope_le {m : ℕ} (hm : 2 ≤ m) (hsq : Squarefree m) (B : ℕ) :
    |moebiusBandStep m B - (B : ℝ) * buchstabSlope m| ≤ 2 * ((m - 1 : ℕ) : ℝ) := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  have h := abs_horizon_step_sub_slope_le hsq ((n + 1) * B)
  rw [sieveL2PrefixEnergy_moebius_step_eq_bandStep,
    Nat.mul_div_cancel_left B (by omega)] at h
  simpa using h

/-- For every squarefree `m ≥ 2`, `Δ(m, B)/B → λ(m)` as `B → ∞`. -/
theorem tendsto_moebiusBandStep_div {m : ℕ} (hm : 2 ≤ m) (hsq : Squarefree m) :
    Tendsto (fun B : ℕ => moebiusBandStep m B / B) atTop (𝓝 (buchstabSlope m)) := by
  rw [← tendsto_sub_nhds_zero_iff]
  refine squeeze_zero_norm' ?_ (tendsto_const_div_atTop_nhds_zero_nat (2 * ((m - 1 : ℕ) : ℝ)))
  filter_upwards [eventually_ge_atTop 1] with B hB
  have hBR : (0 : ℝ) < B := by exact_mod_cast hB
  rw [Real.norm_eq_abs, div_sub' hBR.ne', abs_div, abs_of_pos hBR]
  exact div_le_div_of_nonneg_right (abs_moebiusBandStep_sub_slope_le hm hsq B) hBR.le

/-- **Prime-factor Buchstab slope law.** For a prime `p` and `a ≥ 1` with `p a` squarefree,
`λ(p a) = -1 - 2 μ(a) Σ_{a < d < p a, p ∤ d} μ(d) gcd(d, a)/d`. -/
theorem buchstabSlope_prime_mul {p a : ℕ} (hp : p.Prime) (ha : 1 ≤ a) (hsq : Squarefree (p * a)) :
    buchstabSlope (p * a) = -1 - 2 * moebiusReal a *
      ∑ d ∈ (Icc (a + 1) (p * a - 1)).filter (fun d => ¬ p ∣ d),
        moebiusReal d * ((Nat.gcd d a : ℕ) : ℝ) / d := by
  have hpa : 2 ≤ p * a := by have := hp.two_le; nlinarith
  have hW : Tendsto (fun B : ℕ => primeFactorWindowCorrection p a B / B) atTop
      (𝓝 (∑ d ∈ (Icc (a + 1) (p * a - 1)).filter (fun d => ¬ p ∣ d),
        moebiusReal d * ((Nat.gcd d a : ℕ) : ℝ) / d)) := by
    unfold primeFactorWindowCorrection
    simp_rw [sum_div]
    refine tendsto_finsetSum _ fun d hd => ?_
    have hd0 : 0 < d := by simp only [mem_filter, mem_Icc] at hd; omega
    have hg : 0 < Nat.gcd d a := Nat.gcd_pos_of_pos_left a hd0
    have hq : 1 ≤ d / Nat.gcd d a := Nat.div_pos (Nat.gcd_le_left a hd0) hg
    have hlim := (BezoutValuationIncidence.tendsto_natDiv_div_self hq).const_mul (moebiusReal d)
    have hval : moebiusReal d * (1 / ((d / Nat.gcd d a : ℕ) : ℝ)) =
        moebiusReal d * ((Nat.gcd d a : ℕ) : ℝ) / d := by
      have hd_eq : (d : ℝ) = ((d / Nat.gcd d a : ℕ) : ℝ) * (Nat.gcd d a : ℝ) := by
        exact_mod_cast (Nat.div_mul_cancel (Nat.gcd_dvd_left d a)).symm
      have hgR : (0 : ℝ) < Nat.gcd d a := by exact_mod_cast hg
      have hqR : (0 : ℝ) < ((d / Nat.gcd d a : ℕ) : ℝ) := by exact_mod_cast hq
      conv_rhs => rw [hd_eq]
      field_simp
    rw [hval] at hlim
    refine hlim.congr fun B => ?_
    ring
  have hstep : Tendsto (fun B : ℕ => moebiusBandStep (p * a) B / B) atTop
      (𝓝 (-1 - 2 * moebiusReal a *
        ∑ d ∈ (Icc (a + 1) (p * a - 1)).filter (fun d => ¬ p ∣ d),
          moebiusReal d * ((Nat.gcd d a : ℕ) : ℝ) / d)) := by
    have h := (tendsto_const_nhds (x := (-1 : ℝ))).sub (hW.const_mul (2 * moebiusReal a))
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with B hB
    have hBR : (0 : ℝ) < B := by exact_mod_cast hB
    rw [moebiusBandStep_prime_mul hp ha hsq]
    field_simp
  exact tendsto_nhds_unique (tendsto_moebiusBandStep_div hpa hsq) hstep

/-! ### §3. Exact prime-local crossover scale and quadratic `O(ε²)` window -/

/-- The **prime-local crossover scale** `Λ_p(ε) = -log(2 H_ε(p - 1)) / ε`. -/
def dampedPrimeLocalCrossoverScale (ε : ℝ) (p : ℕ) : ℝ :=
  -Real.log (2 * finiteHarmonicSum (p - 1) (pmPowerDampedRealWeight ε)) / ε

/-- **Exact prime-local sign trichotomy (zero gap).** For every `ε > 0` and prime `p` with
`H_ε(p - 1) > 0`, the sign of `λ_ε(p)` is decided by `log p` against `Λ_p(ε)` without any window
gap. -/
theorem dampedPrimeSlope_local_sign_trichotomy {ε : ℝ} (hε : 0 < ε) {p : ℕ} (hp : p.Prime)
    (hH : 0 < finiteHarmonicSum (p - 1) (pmPowerDampedRealWeight ε)) :
    (0 < dampedPrimeSlope ε p ↔ Real.log p < dampedPrimeLocalCrossoverScale ε p) ∧
    (dampedPrimeSlope ε p = 0 ↔ Real.log p = dampedPrimeLocalCrossoverScale ε p) ∧
    (dampedPrimeSlope ε p < 0 ↔ dampedPrimeLocalCrossoverScale ε p < Real.log p) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have h2H : 0 < 2 * finiteHarmonicSum (p - 1) (pmPowerDampedRealWeight ε) := by linarith
  have hpow : (p : ℝ) ^ (-ε) = Real.exp (-(ε * Real.log p)) := by
    rw [Real.rpow_def_of_pos hp0]; ring_nf
  unfold dampedPrimeSlope dampedPrimeLocalCrossoverScale
  rw [hpow]
  refine ⟨?_, ?_, ?_⟩
  · rw [sub_pos, ← Real.log_lt_log_iff h2H (Real.exp_pos _), Real.log_exp, lt_div_iff₀ hε]
    constructor <;> intro h <;> linarith
  · rw [sub_eq_zero, ← Real.exp_log h2H, Real.exp_injective.eq_iff, Real.log_exp, eq_div_iff hε.ne']
    constructor <;> intro h <;> linarith
  · rw [sub_neg, ← Real.log_lt_log_iff (Real.exp_pos _) h2H, Real.log_exp, div_lt_iff₀ hε]
    constructor <;> intro h <;> linarith

/-- `|m(t)| ≤ C (log t)^{-3}` at all large `t`. -/
private theorem exists_abs_finiteHarmonicSum_moebius_le_log_cube' :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ K : ℕ, ∀ t, K ≤ t →
      |finiteHarmonicSum t moebiusReal| ≤ C / Real.log t ^ 3 := by
  obtain ⟨B, hB, h⟩ := exists_abs_deningerHarmonicPartial_log_rate
  obtain ⟨K, hK⟩ := eventually_atTop.mp (h.and (eventually_ge_atTop 3))
  refine ⟨3 * B, by positivity, K, fun t ht => ?_⟩
  obtain ⟨hb, ht3⟩ := hK t ht
  have hlog : 1 ≤ Real.log t := by
    rw [Real.le_log_iff_exp_le (by positivity)]
    have h3 : (3 : ℝ) ≤ t := by exact_mod_cast ht3
    linarith [Real.exp_one_lt_d9]
  have hl3 : 0 < Real.log t ^ 3 := by positivity
  have hl4 : Real.log t ^ 3 ≤ Real.log t ^ 4 := pow_le_pow_right₀ hlog (by norm_num)
  have hden : finiteHarmonicSum t moebiusReal = deningerHarmonicPartial t := by
    unfold finiteHarmonicSum deningerHarmonicPartial
    change ∑ n ∈ Finset.Ico 1 (t + 1), moebiusReal n / n =
      ∑ n ∈ Finset.range (t + 1), ((moebius n : ℤ) : ℝ) / (n : ℝ)
    rw [Finset.sum_Ico_eq_sub _ (by omega : 1 ≤ t + 1)]
    simp [moebiusReal]
  rw [hden]
  refine hb.trans ?_
  calc 2 * B / Real.log t ^ 4 + B / (3 * Real.log t ^ 3)
      ≤ 2 * B / Real.log t ^ 3 + B / Real.log t ^ 3 := by
        gcongr
        · linarith
    _ = 3 * B / Real.log t ^ 3 := by ring

/-- **Quadratic crossover window (`Λ(ε) ± M ε²`).** There exist an absolute prime threshold `P₀`
and an absolute constant `M > 0` such that for all small `ε > 0` and primes `p ≥ P₀`:
`λ_ε(p) > 0` when `log p ≤ Λ(ε) - M ε²` and `λ_ε(p) < 0` when `log p ≥ Λ(ε) + M ε²`. -/
theorem dampedPrimeSlope_quadratic_crossover :
    ∃ P₀ : ℕ, ∃ M : ℝ, 0 < M ∧ ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ p : ℕ, P₀ ≤ p → p.Prime →
      (Real.log p ≤ dampedCrossoverScale ε - M * ε ^ 2 → 0 < dampedPrimeSlope ε p) ∧
      (dampedCrossoverScale ε + M * ε ^ 2 ≤ Real.log p → dampedPrimeSlope ε p < 0) := by
  obtain ⟨C, hC, K, hK⟩ := exists_abs_finiteHarmonicSum_moebius_le_log_cube'
  obtain ⟨T, hT⟩ := eventually_atTop.mp (tendsto_finiteHarmonicSum_moebiusReal_zero.eventually
    (Metric.closedBall_mem_nhds (0 : ℝ) (show (0 : ℝ) < 1 / 8 by norm_num)))
  set M : ℝ := 96 * C + 1
  refine ⟨T + K + 4, M, by positivity, ?_⟩
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 2 by norm_num),
    tendsto_pmPowerDampedDivisorDensity_re_zero.eventually
      (eventually_lt_nhds (show (0 : ℝ) < Real.exp (-1) / 6 by positivity))]
    with ε hε hρsmall p hpP hp
  obtain ⟨hε0, hεhalf⟩ := hε
  set ρ := (pmPowerDampedDivisorDensity ε).re
  have hρ : 0 < ρ := RHTower.pmPowerDampedDivisorDensity_re_pos hε0
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  set x := (p : ℝ) ^ (-ε)
  have hx0 : 0 < x := Real.rpow_pos_of_pos hp0 _
  have hpow : x = Real.exp (-(ε * Real.log p)) := by
    simp only [x]; rw [Real.rpow_def_of_pos hp0]; ring_nf
  set u := Real.log (2 * ρ)
  have hexpu : Real.exp u = 2 * ρ := Real.exp_log (by positivity)
  have hscale : ε * dampedCrossoverScale ε = -u := by
    unfold dampedCrossoverScale; field_simp; rfl
  have h8 : |ρ - finiteHarmonicSum (p - 1) (pmPowerDampedRealWeight ε)| ≤ 2 * (1 / 8) * x := by
    have h := abs_pmPowerDampedDivisorDensity_re_sub_le hε0 (n := p - 1) (η := 1 / 8)
      fun t ht => by
        have := hT t (by omega)
        simpa [Metric.mem_closedBall, Real.dist_eq] using this
    rwa [show p - 1 + 1 = p by have := hp.one_le; omega] at h
  have hfine : 1 / ε ≤ Real.log p →
      |ρ - finiteHarmonicSum (p - 1) (pmPowerDampedRealWeight ε)| ≤ 2 * (8 * C * ε ^ 3) * x := by
    intro hlp
    have h := abs_pmPowerDampedDivisorDensity_re_sub_le hε0 (n := p - 1) (η := 8 * C * ε ^ 3)
      fun t ht => by
        have htK : K ≤ t := by omega
        have ht1 : (p : ℝ) - 1 ≤ t := by
          have : ((p - 1 : ℕ) : ℝ) ≤ t := by exact_mod_cast ht
          rwa [Nat.cast_sub hp.one_le, Nat.cast_one] at this
        have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
        have hlt : Real.log p - 1 ≤ Real.log t := by
          have hhalf : (p : ℝ) / 2 ≤ t := by linarith
          have := Real.log_le_log (by positivity) hhalf
          rw [Real.log_div hp0.ne' two_ne_zero] at this
          linarith [Real.log_two_lt_d9]
        have hlt' : 1 / (2 * ε) ≤ Real.log t := by
          have : 1 / (2 * ε) ≤ 1 / ε - 1 := by
            rw [div_le_iff₀ (by positivity)]
            field_simp
            nlinarith
          linarith
        have hpos : 0 < 1 / (2 * ε) := by positivity
        calc |finiteHarmonicSum t moebiusReal| ≤ C / Real.log t ^ 3 := hK t htK
          _ ≤ C / (1 / (2 * ε)) ^ 3 :=
              div_le_div_of_nonneg_left hC (by positivity) (pow_le_pow_left₀ hpos.le hlt' 3)
          _ = 8 * C * ε ^ 3 := by field_simp; ring
    rwa [show p - 1 + 1 = p by have := hp.one_le; omega] at h
  have hlarge : x < 6 * ρ → 1 / ε ≤ Real.log p := by
    intro hx
    have h1 : Real.log (6 * ρ) ≤ -1 := by
      rw [Real.log_le_iff_le_exp (by positivity)]; linarith
    have h2 : -(ε * Real.log p) < Real.log (6 * ρ) := by
      rw [hpow] at hx
      exact (Real.exp_lt_exp.mp (by rw [Real.exp_log (by positivity)]; exact hx))
    rw [div_le_iff₀ hε0]; nlinarith
  have hε3 : 0 < ε ^ 3 := by positivity
  constructor
  · intro hle
    have hx : 2 * ρ * (1 + M * ε ^ 3) ≤ x := by
      have h1 : u + M * ε ^ 3 ≤ -(ε * Real.log p) := by
        have := mul_le_mul_of_nonneg_left hle hε0.le
        nlinarith
      rw [hpow]
      calc 2 * ρ * (1 + M * ε ^ 3) ≤ Real.exp u * Real.exp (M * ε ^ 3) := by
            rw [hexpu]; nlinarith [Real.add_one_le_exp (M * ε ^ 3)]
        _ = Real.exp (u + M * ε ^ 3) := (Real.exp_add _ _).symm
        _ ≤ _ := Real.exp_le_exp.mpr h1
    change 0 < x - 2 * finiteHarmonicSum (p - 1) (pmPowerDampedRealWeight ε)
    by_cases h6 : 6 * ρ ≤ x
    · have := abs_le.mp h8; nlinarith
    · have h6' : x < 6 * ρ := not_le.mp h6
      have hb := abs_le.mp (hfine (hlarge h6'))
      have hCx : C * ε ^ 3 * x ≤ 6 * (C * ε ^ 3 * ρ) := by nlinarith [mul_nonneg hC hε3.le]
      have hρe : 0 < ρ * ε ^ 3 := mul_pos hρ hε3
      simp only [M] at hx
      have hx' : 2 * ρ + 192 * (C * ε ^ 3 * ρ) + 2 * (ρ * ε ^ 3) ≤ x := by linear_combination hx
      have hb' : finiteHarmonicSum (p - 1) (pmPowerDampedRealWeight ε) ≤ ρ + 16 * (C * ε ^ 3 * x) := by
        linarith [hb.1]
      linarith
  · intro hge
    have hx : x * (1 + M * ε ^ 3) ≤ 2 * ρ := by
      have h1 : -(ε * Real.log p) ≤ u - M * ε ^ 3 := by
        have := mul_le_mul_of_nonneg_left hge hε0.le
        nlinarith
      have hxe : x ≤ Real.exp (u - M * ε ^ 3) := by rw [hpow]; exact Real.exp_le_exp.mpr h1
      have he : Real.exp (u - M * ε ^ 3) * (1 + M * ε ^ 3) ≤ 2 * ρ := by
        rw [Real.exp_sub, hexpu, div_mul_eq_mul_div, div_le_iff₀ (Real.exp_pos _)]
        nlinarith [Real.add_one_le_exp (M * ε ^ 3)]
      nlinarith
    have hM0 : 0 ≤ M * ε ^ 3 := by positivity
    have hlp : 1 / ε ≤ Real.log p := hlarge (by nlinarith)
    have hb := abs_le.mp (hfine hlp)
    change x - 2 * finiteHarmonicSum (p - 1) (pmPowerDampedRealWeight ε) < 0
    simp only [M] at hx
    nlinarith

/-- **Resolution of the sign inside the additive window `|log p - Λ(ε)| < ε`.** For every `δ > 0`,
there is an absolute `P₀` such that for all small `ε > 0` and primes `p ≥ P₀`, `λ_ε(p) > 0` on
`log p ≤ Λ(ε) - δ ε` and `λ_ε(p) < 0` on `log p ≥ Λ(ε) + δ ε`. -/
theorem dampedPrimeSlope_sublinear_additive_crossover {δ : ℝ} (hδ : 0 < δ) :
    ∃ P₀ : ℕ, ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ p : ℕ, P₀ ≤ p → p.Prime →
      (Real.log p ≤ dampedCrossoverScale ε - δ * ε → 0 < dampedPrimeSlope ε p) ∧
      (dampedCrossoverScale ε + δ * ε ≤ Real.log p → dampedPrimeSlope ε p < 0) := by
  obtain ⟨P₀, M, hM, hP₀⟩ := dampedPrimeSlope_quadratic_crossover
  refine ⟨P₀, ?_⟩
  filter_upwards [hP₀, Ioo_mem_nhdsGT (show (0 : ℝ) < δ / M by positivity)] with ε hε hεδ p hpP hp
  obtain ⟨hε0, hεδ⟩ := hεδ
  have hMε : M * ε ^ 2 ≤ δ * ε := by
    rw [lt_div_iff₀ hM] at hεδ
    nlinarith
  exact ⟨fun hle => (hε p hpP hp).1 (by linarith), fun hge => (hε p hpP hp).2 (by linarith)⟩

/-! ### §4. Second-order Euler variance correction and third-order (`ε³`) dissipation asymptotics -/

/-- Upper and lower second-order Bonferroni bounds on finite products `∏_{i ∈ s} (1 - d_i)`:
`1 - Σ d_i ≤ ∏ (1 - d_i) ≤ 1 - Σ d_i + (Σ d_i)²` for `0 ≤ d_i ≤ 1`. -/
theorem prod_one_sub_le_one_sub_sum_add_sq {ι : Type*} (s : Finset ι) (d : ι → ℝ)
    (hd0 : ∀ i, 0 ≤ d i) (hd1 : ∀ i, d i ≤ 1) :
    ∏ i ∈ s, (1 - d i) ≤ 1 - (∑ i ∈ s, d i) + (∑ i ∈ s, d i) ^ 2 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    set P := ∏ i ∈ s, (1 - d i)
    set S := ∑ i ∈ s, d i
    have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => hd0 i
    have hP_ge : 1 - S ≤ P := RHTower.pm_prod_one_sub_ge s d hd0 hd1
    have hda0 := hd0 a
    have hda1 := hd1 a
    nlinarith

/-- For an infinite product `∏ (1 - d_i) = C` with `0 ≤ d_i ≤ 1` summable,
`∑' d_i - (∑' d_i)² ≤ 1 - C ≤ ∑' d_i`. -/
theorem hasProd_one_sub_second_order_bounds {ι : Type*} {d : ι → ℝ} {C : ℝ}
    (hd0 : ∀ i, 0 ≤ d i) (hd1 : ∀ i, d i ≤ 1) (hs : Summable d)
    (hp : HasProd (fun i => 1 - d i) C) :
    (∑' i, d i) - (∑' i, d i) ^ 2 ≤ 1 - C ∧ 1 - C ≤ ∑' i, d i := by
  obtain ⟨hlo, _⟩ := RHTower.pm_hasProd_one_sub_bounds hd0 hd1 hs hp
  refine ⟨?_, by linarith⟩
  have ht : Tendsto (fun s : Finset ι => ∏ i ∈ s, (1 - d i)) atTop (𝓝 C) := hp
  have hsum : Tendsto (fun s : Finset ι => 1 - (∑ i ∈ s, d i) + (∑ i ∈ s, d i) ^ 2) atTop
      (𝓝 (1 - (∑' i, d i) + (∑' i, d i) ^ 2)) :=
    (tendsto_const_nhds.sub hs.hasSum).add (hs.hasSum.pow 2)
  have hle : C ≤ 1 - (∑' i, d i) + (∑' i, d i) ^ 2 :=
    le_of_tendsto_of_tendsto ht hsum
      (Eventually.of_forall fun s => prod_one_sub_le_one_sub_sum_add_sq s d hd0 hd1)
  linarith

/-- The second-order Euler variance constant `Σ_p (log p / (p - 1))²`. -/
def dampedVarianceSecondOrderConstant : ℝ :=
  ∑' p : Nat.Primes, (Real.log (p : ℝ) / ((p : ℝ) - 1)) ^ 2

/-- For `a > 0`, `((a : ℝ)^ε - 1)/ε → log a` as `ε → 0⁺`. -/
private theorem tendsto_rpow_sub_one_div {a : ℝ} (ha : 0 < a) :
    Tendsto (fun ε : ℝ => (a ^ ε - 1) / ε) (𝓝[>] 0) (𝓝 (Real.log a)) := by
  have hd : HasDerivAt (fun x : ℝ => a ^ x) (Real.log a) 0 := by
    have h := (hasDerivAt_id (0 : ℝ)).const_rpow ha
    simpa using h
  have hs := hd.tendsto_slope_zero_right
  refine hs.congr fun ε => ?_
  simp only [zero_add, Real.rpow_zero, smul_eq_mul]
  ring

/-- For `a > 0`, `(1 - a^(-ε))/ε → log a` as `ε → 0⁺`. -/
private theorem tendsto_one_sub_rpow_neg_div {a : ℝ} (ha : 0 < a) :
    Tendsto (fun ε : ℝ => (1 - a ^ (-ε)) / ε) (𝓝[>] 0) (𝓝 (Real.log a)) := by
  have hd : HasDerivAt (fun x : ℝ => a ^ (-x)) (-Real.log a) 0 := by
    have h := (hasDerivAt_id (0 : ℝ)).neg.const_rpow ha
    simpa using h
  have hs := hd.tendsto_slope_zero_right.neg
  rw [neg_neg] at hs
  refine hs.congr fun ε => ?_
  simp only [zero_add, neg_zero, Real.rpow_zero, smul_eq_mul]
  ring

/-- For each prime `p`, `δ_p(ε) / ε² → (log p / (p - 1))²` as `ε → 0⁺`. -/
theorem tendsto_pmPowerDampedVariancePrimeDeficit_div_sq (p : Nat.Primes) :
    Tendsto (fun ε : ℝ => RHTower.pmPowerDampedVariancePrimeDeficit ε p / ε ^ 2) (𝓝[>] 0)
      (𝓝 ((Real.log (p : ℝ) / ((p : ℝ) - 1)) ^ 2)) := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast p.property.one_lt
  have hp0 : (0 : ℝ) < p := by linarith
  have hc : Continuous (fun ε : ℝ => (p : ℝ) ^ (-ε)) :=
    (Real.continuous_const_rpow hp0.ne').comp continuous_neg
  have ht : Tendsto (fun ε : ℝ => (p : ℝ) ^ (-ε)) (𝓝[>] 0) (𝓝 1) := by
    simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  have hu := tendsto_one_sub_rpow_neg_div hp0
  have hquot := ((ht.mul hu).div (tendsto_const_nhds.sub ht) (by linarith)).pow 2
  rw [one_mul] at hquot
  refine hquot.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hε0 : ε ≠ 0 := ne_of_gt hε
  rw [Pi.div_apply]
  unfold RHTower.pmPowerDampedVariancePrimeDeficit
  have hsub : (p : ℝ) - (p : ℝ) ^ (-ε) ≠ 0 := by
    have ht1 : (p : ℝ) ^ (-ε) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hp1.le (by linarith [show (0 : ℝ) < ε from hε])
    linarith
  field_simp

private theorem summable_primes_rpow' :
    Summable (fun p : Nat.Primes => ((p : ℕ) : ℝ) ^ (-(3 / 2 : ℝ))) :=
  (Real.summable_nat_rpow.mpr (by norm_num : -(3 / 2 : ℝ) < -1)).comp_injective
    Subtype.val_injective

private theorem primeDeficit_div_sq_le {ε : ℝ} (hε : 0 < ε) (p : Nat.Primes) :
    RHTower.pmPowerDampedVariancePrimeDeficit ε p / ε ^ 2 ≤
      64 * ((p : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)) := by
  have hp2 : (2 : ℝ) ≤ ((p : ℕ) : ℝ) := by exact_mod_cast p.property.two_le
  set P : ℝ := ((p : ℕ) : ℝ)
  set t := P ^ (-ε)
  have hp0 : (0 : ℝ) < P := by linarith
  have ht0 : 0 ≤ t := Real.rpow_nonneg hp0.le _
  have ht1 : t ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)
  have hlog : Real.log P ≤ 4 * P ^ (1 / 4 : ℝ) := by
    calc Real.log P ≤ P ^ (1 / 4 : ℝ) / (1 / 4) :=
          Real.log_le_rpow_div hp0.le (by norm_num)
      _ = 4 * P ^ (1 / 4 : ℝ) := by ring
  have h1t : 1 - t ≤ ε * Real.log P := by
    have := Real.add_one_le_exp (Real.log P * (-ε))
    rw [← Real.rpow_def_of_pos hp0] at this
    linarith
  have hq0 : 0 ≤ (t - t ^ 2) / (P - t) := div_nonneg (by nlinarith) (by linarith)
  have hq : (t - t ^ 2) / (P - t) ≤ 8 * ε * P ^ (1 / 4 : ℝ) / P := by
    rw [div_le_div_iff₀ (by linarith) hp0]
    have hnum : t - t ^ 2 ≤ 4 * ε * P ^ (1 / 4 : ℝ) := by
      nlinarith [mul_le_mul_of_nonneg_left hlog hε.le]
    have hP4 : 0 ≤ P ^ (1 / 4 : ℝ) := Real.rpow_nonneg hp0.le _
    nlinarith [mul_nonneg hε.le hP4]
  have hpow : (8 * ε * P ^ (1 / 4 : ℝ) / P) ^ 2 = 64 * ε ^ 2 * P ^ (-(3 / 2 : ℝ)) := by
    rw [div_pow, mul_pow, mul_pow, ← Real.rpow_natCast (P ^ (1 / 4 : ℝ)) 2,
      ← Real.rpow_mul hp0.le, ← Real.rpow_natCast P 2, mul_div_assoc, ← Real.rpow_sub hp0]
    norm_num
  rw [div_le_iff₀ (by positivity)]
  unfold RHTower.pmPowerDampedVariancePrimeDeficit
  calc ((P ^ (-ε) - (P ^ (-ε)) ^ 2) / (P - P ^ (-ε))) ^ 2
      ≤ (8 * ε * P ^ (1 / 4 : ℝ) / P) ^ 2 := pow_le_pow_left₀ hq0 hq 2
    _ = 64 * P ^ (-(3 / 2 : ℝ)) * ε ^ 2 := by rw [hpow]; ring

/-- `(Σ_p δ_p(ε)) / ε² → Σ_p (log p / (p - 1))²` as `ε → 0⁺`. -/
theorem tendsto_tsum_pmPowerDampedVariancePrimeDeficit_div_sq :
    Tendsto (fun ε : ℝ => (∑' p : Nat.Primes, RHTower.pmPowerDampedVariancePrimeDeficit ε p) / ε ^ 2)
      (𝓝[>] 0) (𝓝 dampedVarianceSecondOrderConstant) := by
  have h := tendsto_tsum_of_dominated_convergence (summable_primes_rpow'.mul_left 64)
    tendsto_pmPowerDampedVariancePrimeDeficit_div_sq ?_
  · refine h.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε _
    rw [tsum_div_const]
  · filter_upwards [self_mem_nhdsWithin] with ε hε p
    have hε0 : 0 < ε := hε
    have h0 := (RHTower.pmPowerDampedVariancePrimeDeficit_bounds hε0.le p).1
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg h0 (sq_nonneg ε))]
    exact primeDeficit_div_sq_le hε0 p

/-- **Second-order Euler variance correction.**
`(1 - K_ε) / ε² → Σ_p (log p / (p - 1))²` as `ε → 0⁺`. -/
theorem tendsto_one_sub_varianceCorrection_div_sq :
    Tendsto (fun ε : ℝ => (1 - RHTower.pmPowerDampedVarianceCorrection ε) / ε ^ 2)
      (𝓝[>] 0) (𝓝 dampedVarianceSecondOrderConstant) := by
  have hS := tendsto_tsum_pmPowerDampedVariancePrimeDeficit_div_sq
  have h0 := RHTower.tendsto_tsum_pmPowerDampedVariancePrimeDeficit
  have hlo : Tendsto (fun ε : ℝ =>
      (∑' p : Nat.Primes, RHTower.pmPowerDampedVariancePrimeDeficit ε p) / ε ^ 2 *
        (1 - ∑' p : Nat.Primes, RHTower.pmPowerDampedVariancePrimeDeficit ε p))
      (𝓝[>] 0) (𝓝 dampedVarianceSecondOrderConstant) := by
    simpa using hS.mul ((tendsto_const_nhds (x := (1 : ℝ))).sub h0)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hS ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    have hε0 : (0 : ℝ) < ε := hε
    obtain ⟨hl, _⟩ := hasProd_one_sub_second_order_bounds
      (fun p => (RHTower.pmPowerDampedVariancePrimeDeficit_bounds hε0.le p).1)
      (fun p => (RHTower.pmPowerDampedVariancePrimeDeficit_bounds hε0.le p).2.1)
      (RHTower.summable_pmPowerDampedVariancePrimeDeficit hε0.le)
      (RHTower.pmPowerDampedVarianceCorrection_hasProd hε0)
    have hdiv := div_le_div_of_nonneg_right hl (sq_nonneg ε)
    linarith [show ((∑' i, RHTower.pmPowerDampedVariancePrimeDeficit ε i) -
        (∑' i, RHTower.pmPowerDampedVariancePrimeDeficit ε i) ^ 2) / ε ^ 2 =
      (∑' i, RHTower.pmPowerDampedVariancePrimeDeficit ε i) / ε ^ 2 *
        (1 - ∑' i, RHTower.pmPowerDampedVariancePrimeDeficit ε i) by ring]
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    have hε0 : (0 : ℝ) < ε := hε
    obtain ⟨_, hr⟩ := hasProd_one_sub_second_order_bounds
      (fun p => (RHTower.pmPowerDampedVariancePrimeDeficit_bounds hε0.le p).1)
      (fun p => (RHTower.pmPowerDampedVariancePrimeDeficit_bounds hε0.le p).2.1)
      (RHTower.summable_pmPowerDampedVariancePrimeDeficit hε0.le)
      (RHTower.pmPowerDampedVarianceCorrection_hasProd hε0)
    exact div_le_div_of_nonneg_right hr (sq_nonneg ε)

/-- The odd Bézout totient series `Σ_{j ≥ 0} μ(2j + 1) / φ(2j + 1)²`. -/
def oddMoebiusTotientSqSum : ℝ :=
  ∑' j : ℕ, moebiusReal (2 * j + 1) / (Nat.totient (2 * j + 1) : ℝ) ^ 2

/-- The parity factor obeys `(1 - (2^{1+ε} - 1)^{-2}) / ε → 4 log 2` as `ε → 0⁺`. -/
theorem tendsto_parity_factor_div :
    Tendsto (fun ε : ℝ => (1 - 1 / ((2 : ℝ) ^ (1 + ε) - 1) ^ 2) / ε) (𝓝[>] 0)
      (𝓝 (4 * Real.log 2)) := by
  have hu := tendsto_rpow_sub_one_div (show (0 : ℝ) < 2 by norm_num)
  have he : Tendsto (fun ε : ℝ => ε) (𝓝[>] 0) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
  have hnum : Tendsto (fun ε : ℝ => 4 * ((2 ^ ε - 1) / ε) + 4 * ε * ((2 ^ ε - 1) / ε) ^ 2)
      (𝓝[>] 0) (𝓝 (4 * Real.log 2)) := by
    have h := (hu.const_mul 4).add ((he.const_mul 4).mul (hu.pow 2))
    simpa using h
  have hden : Tendsto (fun ε : ℝ => (1 + 2 * ε * ((2 ^ ε - 1) / ε)) ^ 2) (𝓝[>] 0) (𝓝 1) := by
    have h := ((tendsto_const_nhds (x := (1 : ℝ))).add ((he.const_mul 2).mul hu)).pow 2
    simpa using h
  have h := hnum.div hden one_ne_zero
  rw [div_one] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hε0 : (0 : ℝ) < ε := hε
  have h2 : (2 : ℝ) ^ (1 + ε) = 2 * (2 : ℝ) ^ ε := by
    rw [Real.rpow_add (by norm_num), Real.rpow_one]
  have hy : (2 : ℝ) ^ (1 + ε) - 1 ≠ 0 := by
    have : (1 : ℝ) ≤ (2 : ℝ) ^ ε := Real.one_le_rpow (by norm_num) hε0.le
    rw [h2]; linarith
  have hy' : 1 + 2 * ε * (((2 : ℝ) ^ ε - 1) / ε) = (2 : ℝ) ^ (1 + ε) - 1 := by
    rw [h2]; field_simp; ring
  rw [Pi.div_apply, hy']
  field_simp
  rw [h2]
  ring

/-- `φ(e) = ∏_{p | e} (p - 1)` for squarefree `e`. -/
private theorem totient_eq_prod_of_squarefree' {e : ℕ} (he : Squarefree e) :
    (Nat.totient e : ℝ) = ∏ p ∈ e.primeFactors, ((p : ℝ) - 1) := by
  have h := Nat.totient_mul_prod_primeFactors e
  rw [Nat.prod_primeFactors_of_squarefree he] at h
  have he0 : 0 < e := Nat.pos_of_ne_zero he.ne_zero
  have h' : Nat.totient e = ∏ p ∈ e.primeFactors, (p - 1) := by
    rw [mul_comm] at h; exact Nat.eq_of_mul_eq_mul_left he0 h
  rw [h', Nat.cast_prod]
  exact prod_congr rfl fun p hp => by
    rw [Nat.cast_sub (Nat.prime_of_mem_primeFactors hp).one_lt.le, Nat.cast_one]

/-- For every `e ≥ 1`, `μ(e) (w_ε(e) / ρ_ε)² → μ(e) / φ(e)²` as `ε → 0⁺`. -/
theorem tendsto_moebius_mul_dampedRamanujanCoeff_div_density_sq {e : ℕ} (he : 1 ≤ e) :
    Tendsto (fun ε : ℝ => moebiusReal e *
        (dampedRamanujanCoeff ε e / (RHTower.pmPowerDampedDivisorDensity ε).re) ^ 2)
      (𝓝[>] 0) (𝓝 (moebiusReal e / (Nat.totient e : ℝ) ^ 2)) := by
  by_cases hsq : Squarefree e
  · have hD : Tendsto (fun ε : ℝ => RHTower.pmPowerDampedRamanujanDenominator ε e)
        (𝓝[>] 0) (𝓝 (Nat.totient e : ℝ)) := by
      rw [totient_eq_prod_of_squarefree' hsq]
      unfold RHTower.pmPowerDampedRamanujanDenominator
      refine tendsto_finsetProd _ fun p hp => ?_
      have hp0 : (0 : ℝ) < p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos
      have hc : Continuous (fun ε : ℝ => (p : ℝ) ^ (1 + ε) - 1) :=
        ((Real.continuous_const_rpow hp0.ne').comp (continuous_const.add continuous_id)).sub
          continuous_const
      simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
    have hφ0 : (Nat.totient e : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.totient_pos.mpr he).ne'
    have h := (tendsto_const_nhds (x := moebiusReal e)).div (hD.pow 2) (pow_ne_zero 2 hφ0)
    refine h.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hε0 : (0 : ℝ) < ε := hε
    have hρ := RHTower.pmPowerDampedDivisorDensity_re_ne_zero hε0
    have hD0 : RHTower.pmPowerDampedRamanujanDenominator ε e ≠ 0 :=
      (RHTower.pmPowerDampedRamanujanDenominator_pos hε0 e).ne'
    have hw : dampedRamanujanCoeff ε e =
        (RHTower.pmPowerDampedDivisorDensity ε).re * moebiusReal e /
          RHTower.pmPowerDampedRamanujanDenominator ε e := by
      rw [dampedRamanujanCoeff, RHTower.pmPowerDampedRamanujanWeight_eq_ofReal hε0,
        Complex.ofReal_re]
      rfl
    have hμ : moebiusReal e ^ 2 = 1 := by
      unfold moebiusReal
      exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree hsq
    rw [Pi.div_apply, hw]
    field_simp
    linear_combination -moebiusReal e * hμ
  · have h0 : moebiusReal e = 0 := moebiusReal_eq_zero_of_not_squarefree e hsq
    simp [h0]

/-- The normalized odd Bézout sum converges to `Σ_{j ≥ 0} μ(2j + 1) / φ(2j + 1)²`. -/
theorem tendsto_odd_bezout_sum_div_density_sq :
    Tendsto (fun ε : ℝ => (∑' j : ℕ, moebiusReal (2 * j + 1) * dampedRamanujanCoeff ε (2 * j + 1) ^ 2) /
        (RHTower.pmPowerDampedDivisorDensity ε).re ^ 2)
      (𝓝[>] 0) (𝓝 oddMoebiusTotientSqSum) := by
  set g : ℕ → ℝ := fun j =>
    RHTower.Sieve.sqfreeTotientInv (2 * j + 1) / (Nat.totient (2 * j + 1) : ℝ)
  have hinj : Function.Injective (fun j : ℕ => 2 * j + 1) :=
    fun a b (h : 2 * a + 1 = 2 * b + 1) => by omega
  have hg : Summable g := summable_sqfreeTotientInv_div_totient.1.comp_injective hinj
  have h := tendsto_tsum_of_dominated_convergence hg
    (fun j => tendsto_moebius_mul_dampedRamanujanCoeff_div_density_sq (by omega : 1 ≤ 2 * j + 1)) ?_
  · refine h.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    rw [← tsum_div_const]
    exact tsum_congr fun j => by ring
  · filter_upwards [self_mem_nhdsWithin] with ε hε j
    have hε0 : (0 : ℝ) < ε := hε
    have hρ : 0 < (RHTower.pmPowerDampedDivisorDensity ε).re :=
      RHTower.pmPowerDampedDivisorDensity_re_pos hε0
    have hμ : |moebiusReal (2 * j + 1)| ≤ 1 := by
      unfold moebiusReal; exact_mod_cast ArithmeticFunction.abs_moebius_le_one
    have hbd := dampedRamanujanCoeff_sq_le hε0 (2 * j + 1)
    rw [Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (sq_nonneg (dampedRamanujanCoeff ε (2 * j + 1) /
        (RHTower.pmPowerDampedDivisorDensity ε).re)),
      div_pow, ← mul_div_assoc, div_le_iff₀ (sq_pos_of_pos hρ)]
    calc |moebiusReal (2 * j + 1)| * dampedRamanujanCoeff ε (2 * j + 1) ^ 2
        ≤ 1 * dampedRamanujanCoeff ε (2 * j + 1) ^ 2 :=
          mul_le_mul_of_nonneg_right hμ (sq_nonneg _)
      _ ≤ g j * (RHTower.pmPowerDampedDivisorDensity ε).re ^ 2 := by
          rw [one_mul, mul_comm (g j)]; exact hbd

/-- **Exact third-order (`ε³`) law of the lag-one Bézout sum.**
`dampedBezoutLimit ε / ε³ → 4 log 2 Σ_{j ≥ 0} μ(2j + 1) / φ(2j + 1)²` as `ε → 0⁺`. -/
theorem tendsto_dampedBezoutLimit_div_cube :
    Tendsto (fun ε : ℝ => dampedBezoutLimit ε / ε ^ 3) (𝓝[>] 0)
      (𝓝 (4 * Real.log 2 * oddMoebiusTotientSqSum)) := by
  have h1 := tendsto_parity_factor_div
  have h2 := tendsto_odd_bezout_sum_div_density_sq
  have h3 := RHTower.tendsto_pmPowerDampedDivisorDensity_re_div_parameter.pow 2
  have h := (h1.mul h2).mul h3
  rw [one_pow, mul_one] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hε0 : (0 : ℝ) < ε := hε
  have hρ := RHTower.pmPowerDampedDivisorDensity_re_ne_zero hε0
  rw [dampedBezoutLimit_eq_parity hε0]
  field_simp

/-- `(ρ_ε² - ε²) / ε³ → -2 γ` as `ε → 0⁺`. -/
theorem tendsto_pmPowerDampedDivisorDensity_sq_sub_sq_div_cube :
    Tendsto (fun ε : ℝ => ((RHTower.pmPowerDampedDivisorDensity ε).re ^ 2 - ε ^ 2) / ε ^ 3)
      (𝓝[>] 0) (𝓝 (-2 * Real.eulerMascheroniConstant)) := by
  have h1 := tendsto_pmPowerDampedDivisorDensity_re_second_order
  have h2 := RHTower.tendsto_pmPowerDampedDivisorDensity_re_div_parameter.add
    (tendsto_const_nhds (x := (1 : ℝ)))
  have h := h1.mul h2
  rw [show -Real.eulerMascheroniConstant * (1 + 1) = -2 * Real.eulerMascheroniConstant by ring] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hε0 : ε ≠ 0 := ne_of_gt hε
  field_simp
  ring

/-- **Third-order law of the lag-one autocorrelation.**
`(A_ε(1) + ε²) / ε³ → 2 γ + 4 log 2 Σ_{j ≥ 0} μ(2j + 1) / φ(2j + 1)²` as `ε → 0⁺`. -/
theorem tendsto_dampedAutocorrelation_one_third_order :
    Tendsto (fun ε : ℝ => (dampedAutocorrelation ε 1 + ε ^ 2) / ε ^ 3) (𝓝[>] 0)
      (𝓝 (2 * Real.eulerMascheroniConstant + 4 * Real.log 2 * oddMoebiusTotientSqSum)) := by
  have h := tendsto_dampedBezoutLimit_div_cube.sub
    tendsto_pmPowerDampedDivisorDensity_sq_sub_sq_div_cube
  rw [show 4 * Real.log 2 * oddMoebiusTotientSqSum - -2 * Real.eulerMascheroniConstant =
    2 * Real.eulerMascheroniConstant + 4 * Real.log 2 * oddMoebiusTotientSqSum by ring] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hε0 : (0 : ℝ) < ε := hε
  have hR := dampedDissipationRate_eq_variance_sub_autocorrelation hε0
  unfold dampedDissipationRate RHTower.pmPowerDampedDivisorVariance at hR
  have hA : dampedAutocorrelation ε 1 =
      dampedBezoutLimit ε - (RHTower.pmPowerDampedDivisorDensity ε).re ^ 2 := by linarith
  rw [hA]
  ring

/-- **Third-order law of the dissipation–variance gap.**
`(R(ε) - V(ε) - ε²) / ε³ → -2 γ - 4 log 2 Σ_{j ≥ 0} μ(2j + 1) / φ(2j + 1)²` as `ε → 0⁺`. -/
theorem tendsto_dampedDissipationRate_sub_variance_third_order :
    Tendsto (fun ε : ℝ =>
        (dampedDissipationRate ε - RHTower.pmPowerDampedDivisorVariance ε - ε ^ 2) / ε ^ 3)
      (𝓝[>] 0)
      (𝓝 (-2 * Real.eulerMascheroniConstant - 4 * Real.log 2 * oddMoebiusTotientSqSum)) := by
  have h := tendsto_dampedAutocorrelation_one_third_order.neg
  rw [show -(2 * Real.eulerMascheroniConstant + 4 * Real.log 2 * oddMoebiusTotientSqSum) =
    -2 * Real.eulerMascheroniConstant - 4 * Real.log 2 * oddMoebiusTotientSqSum by ring] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  rw [dampedDissipationRate_eq_variance_sub_autocorrelation hε]
  ring

end

end GaloisForLFunctions.TransHorizonIncidenceMechanics
