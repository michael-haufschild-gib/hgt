import GaloisForLFunctions.ArithmeticCorrelationGeometry.TheCoalescentSurplusDecomposesOverItsStabilizers
import GaloisForLFunctions.TransThresholdPairCorrelation.ParitySensitiveRamanujanStabilizerTransfer
import GaloisForLFunctions.RHTower.Zeta23SimpleOffLineNearLine
import GaloisForLFunctions.RHTower.Zeta23CriticalOrdinateCensus

/-!
# Sub-Progression Dirichlet Stabilizer Inversion and the Simultaneous Near-Line / Coalescent Anatomy of `3/4`

This module couples `ACG`'s finite Dirichlet subgroup stabilizer decomposition with `TTPC`'s
multiplicity-refined bandwidth-`4/3` coalescent certificate, Montgomery–Taylor simple near-line
confinement, and the critical-ordinate reflection census.

## Main Unconditional Results

1. **Zero-Ramification Principal Gauge Identity (`dirichletGauge_one_eq_zero`,
   `twistedPrimeCoalSum_dirichletGauge_one`):**
   Because `dirichletGauge` resets non-coprime primes to `0` and `(1 : DirichletCharacter ℂ q)`
   evaluates to `1` (`arg 1 = 0`) on coprime primes, `dirichletGauge 1 = 0` holds pointwise on all
   primes for every `q : ℕ`, so `twistedPrimeCoalSum Ω g X θ₀ (dirichletGauge 1) = primeCoalSum`
   with **zero ramified-prime error**.

2. **Sub-Progression Congruent-Pair Annihilation and Pure Nontrivial-Character Inversion
   (`congruent_coalWeight_sum_eq_zero_of_mul_lt`, `primeCoalSum_eq_neg_sum_nontriv`,
   `exists_nontriv_neg_re_twistedPrimeCoalSum_ge`, `primeCoalSum_sq_le_totient_sub_one_mul_sum_sq`,
   `eventually_bandwidth43_subProgression_window`):**
   In the intermediate modulus window `θ₀ * X < q` and `2 * q * θ₀ < 1` (which is non-vacuous across
   every exponent `κ ∈ (1 / 3 + η, 1 - η)` at bandwidth `4/3`, e.g. `q = ⌊T^{2/3}⌋₊` or `⌊T^{1/2}⌋₊`),
   every coalescent prime pair `(n, m)` in `primeRange X` satisfies `1 ≤ |n - m| ≤ θ₀ * X < q`, so
   `(n : ZMod q) ≠ (m : ZMod q)`. Consequently the congruent stabilizer sum vanishes identically and
   `primeCoalSum Ω g X θ₀ = -∑_{χ ≠ 1 (mod q)} Re twistedPrimeCoalSum Ω g X θ₀ (dirichletGauge χ)`,
   forcing both a pigeonhole witness `≥ primeCoalSum / (φ(q) - 1)` and the Cauchy–Schwarz RMS lower
   bound `(primeCoalSum)^2 ≤ (φ(q) - 1) ∑_{χ ≠ 1} (Re twistedPrimeCoalSum)^2`.

3. **Coupled `65/72` `N₀` Lower Bound, `58/65` Critical-Ordinate Bound, and Five-Part Simultaneous
   `3/4` Dichotomy (`N0_ge_sixtyFive_seventySeconds_sub_half_near_sub_half_primeSurplus`,
   `criticalOrdinates_ge_fiftyEight_sixtyFifths_sub_primeSurplus`,
   `three_quarters_or_simultaneous_five_part_obstruction`):**
   Coupling `offLineSimple_add_two_offLineMultiple_le_seven_thirtySixths_add_primeCoalescentSurplus`
   with `offLineSimple_add_two_offLineMultiple_le_one_sub_HD_one`, `eventually_offLineFarMass_le`,
   and `two_mul_card_ordinates_le` proves unconditionally on `(T, 2T]` that:
   * `(65/72 - 1/(2A) - ε) N - (1/2) S_near(A/log T) - (1/2) primeCoalescentSurplus ≤ N₀`;
   * `(58/65 - ε) #zeroOrdinates - (36/65 + ε) max(0, primeCoalescentSurplus) ≤ #criticalOrdinates`;
   * Either `(3/4) N ≤ N₀`, or all five structural constraints hold simultaneously (`S_near`
     clustering `≥ (HD 1 - 1/2 - 1/A - ε) N`, off-line multiple suppression
     `M_off < (3/4 - HD 1 + ε) N`, multiplicity-penalized prime surplus floor
     `primeCoalescentSurplus > (1/18 - ε) N + M_off`, joint near-line + prime-surplus floor
     `S_near + primeCoalescentSurplus > (11/36 - 1/A - ε) N`, and the `58/65` ordinate bound).
-/

open Finset Filter Topology Real
open scoped BigOperators ComplexConjugate

open Zeta23 Zeta23.PrimeSide

noncomputable section

namespace GaloisForLFunctions.ArithmeticCorrelationGeometry

open HTGeometry TransThresholdPairCorrelation RHTower

/-! ## §1. Zero-Ramification Principal Gauge Identity and Sub-Progression Stabilizer Inversion -/

/-- **Zero-Ramification Principal Gauge Identity:**
For every modulus `q : ℕ`, the gauge point of the principal character `(1 : DirichletCharacter ℂ q)`
is identically `0 : GaugeTorus` on all primes, with zero ramified-prime error. -/
theorem dirichletGauge_one_eq_zero (q : ℕ) :
    dirichletGauge (1 : DirichletCharacter ℂ q) = 0 := by
  funext p
  simp only [dirichletGauge, Pi.zero_apply]
  split_ifs with hpq
  · have hunit : IsUnit (p : ZMod q) := (ZMod.unitOfCoprime p hpq).isUnit
    rw [MulChar.one_apply hunit, Complex.arg_one, zero_div, QuotientAddGroup.mk_zero]
  · rfl

/-- At the principal character `χ = 1 (mod q)`, `twistedPrimeCoalSum` equals `primeCoalSum`
identically for every `q : ℕ`, `X, θ₀ : ℝ`, with zero ramified-prime error. -/
theorem twistedPrimeCoalSum_dirichletGauge_one (q : ℕ) (Ω g : ℝ → ℝ) (X θ₀ : ℝ) :
    twistedPrimeCoalSum Ω g X θ₀ (dirichletGauge (1 : DirichletCharacter ℂ q)) =
      (primeCoalSum Ω g X θ₀ : ℂ) := by
  rw [dirichletGauge_one_eq_zero, twistedPrimeCoalSum_zero]

private theorem not_zmod_eq_of_lt_of_sub_lt {a b q : ℕ} (hab : a < b) (hlt : b - a < q) :
    (a : ZMod q) ≠ (b : ZMod q) := by
  intro hmod
  have hpos : 0 < b - a := Nat.sub_pos_of_lt hab
  have hadd : (b : ZMod q) = (a : ZMod q) + ((b - a : ℕ) : ZMod q) := by
    exact_mod_cast (Nat.add_sub_of_le hab.le).symm
  have hzero : ((b - a : ℕ) : ZMod q) = 0 := by
    have h1 : (a : ZMod q) + 0 = (a : ZMod q) + ((b - a : ℕ) : ZMod q) := by
      rw [add_zero, hmod, hadd]
    exact (add_left_cancel h1).symm
  have hdvd : q ∣ b - a := (ZMod.natCast_eq_zero_iff (b - a) q).mp hzero
  exact absurd (Nat.le_of_dvd hpos hdvd) (not_le.mpr hlt)

private theorem le_of_mem_primeRange {X : ℝ} {n : ℕ} (hn : n ∈ primeRange X) : (n : ℝ) ≤ X := by
  obtain ⟨hn1, hnf⟩ := Finset.mem_Ioc.mp hn
  have hX0 : 0 ≤ X := by
    by_contra hneg
    push Not at hneg
    have hf0 : ⌊X⌋₊ = 0 := Nat.floor_of_nonpos hneg.le
    omega
  exact (Nat.cast_le.mpr hnf).trans (Nat.floor_le hX0)

/-- **Sub-Progression Congruent-Pair Annihilation:**
Whenever `0 < θ₀` and `θ₀ * X < q`, every coalescent prime pair `(n, m)` in `primeRange X` satisfies
`1 ≤ |n - m| ≤ θ₀ * X < q`, so `(n : ZMod q) ≠ (m : ZMod q)` and the congruent stabilizer sum
vanishes identically. -/
theorem congruent_coalWeight_sum_eq_zero_of_mul_lt {Ω g : ℝ → ℝ} {X θ₀ : ℝ} {q : ℕ}
    (hθ0 : 0 < θ₀) (hqX : θ₀ * X < q) :
    (∑ n ∈ primeRange X, ∑ m ∈ primeRange X,
      if (n : ZMod q) = m then (coalWeight Ω g θ₀ n m : ℂ) else 0) = 0 := by
  refine Finset.sum_eq_zero fun n hn => Finset.sum_eq_zero fun m hm => ?_
  by_cases hw : coalWeight Ω g θ₀ n m = 0
  · simp [hw]
  · rw [if_neg]
    obtain ⟨hnp, hmp, hnm, hgap⟩ := coalescent_of_coalWeight_ne_zero hw
    have hnX : (n : ℝ) ≤ X := le_of_mem_primeRange hn
    have hmX : (m : ℝ) ≤ X := le_of_mem_primeRange hm
    set M := max (n : ℝ) (m : ℝ)
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hnp.pos
    have hMpos : 0 < M := lt_max_of_lt_left hn0
    have hMX : M ≤ X := max_le hnX hmX
    have hsep := (abs_log_sub_log_ge_abs_sub_div_max hmp.one_lt.le hnp.one_lt.le).trans hgap
    have habs_lt : |(n : ℝ) - m| < q := by
      have h1 : |(n : ℝ) - m| ≤ θ₀ * M := (div_le_iff₀ hMpos).mp hsep
      have h2 : θ₀ * M ≤ θ₀ * X := mul_le_mul_of_nonneg_left hMX hθ0.le
      linarith
    rcases lt_or_gt_of_ne hnm with hlt | hgt
    · have hsub_lt : m - n < q := by
        have hcast : ((m - n : ℕ) : ℝ) = |(n : ℝ) - m| := by
          have hnm_real : (n : ℝ) < m := by exact_mod_cast hlt
          rw [Nat.cast_sub hlt.le, abs_sub_comm, abs_of_pos (sub_pos.mpr hnm_real)]
        exact_mod_cast hcast.trans_lt habs_lt
      exact not_zmod_eq_of_lt_of_sub_lt hlt hsub_lt
    · have hsub_lt : n - m < q := by
        have hcast : ((n - m : ℕ) : ℝ) = |(n : ℝ) - m| := by
          have hmn_real : (m : ℝ) < n := by exact_mod_cast hgt
          rw [Nat.cast_sub hgt.le, abs_of_pos (sub_pos.mpr hmn_real)]
        exact_mod_cast hcast.trans_lt habs_lt
      exact fun heq => not_zmod_eq_of_lt_of_sub_lt hgt hsub_lt heq.symm

section CharacterInversion

variable {q : ℕ} [NeZero q]

/-- In the sub-progression window `θ₀ * X < q` and `2 * q * θ₀ < 1`, the full Dirichlet character
sum of `twistedPrimeCoalSum` vanishes identically. -/
theorem sum_twistedPrimeCoalSum_dirichletGauge_eq_zero {Ω g : ℝ → ℝ} {X θ₀ : ℝ}
    (hθ0 : 0 < θ₀) (hθ : θ₀ ≤ 1 / 2) (hq : 2 * (q : ℝ) * θ₀ < 1) (hqX : θ₀ * X < q) :
    ∑ χ : DirichletCharacter ℂ q, twistedPrimeCoalSum Ω g X θ₀ (dirichletGauge χ) = 0 := by
  rw [sum_twistedPrimeCoalSum_dirichletGauge hθ0 hθ hq,
    congruent_coalWeight_sum_eq_zero_of_mul_lt hθ0 hqX, mul_zero]

/-- **Pure Nontrivial-Character Inversion of `primeCoalSum`:**
For every modulus `q` (`[NeZero q]`) in the sub-progression window `θ₀ * X < q` and `2 * q * θ₀ < 1`,
`primeCoalSum` equals minus the sum of `Re twistedPrimeCoalSum` over **nontrivial** Dirichlet
characters `χ ≠ 1 (mod q)`, with zero congruent-pair error and zero ramified-prime error. -/
theorem primeCoalSum_eq_neg_sum_nontriv {Ω g : ℝ → ℝ} {X θ₀ : ℝ}
    (hθ0 : 0 < θ₀) (hθ : θ₀ ≤ 1 / 2) (hq : 2 * (q : ℝ) * θ₀ < 1) (hqX : θ₀ * X < q) :
    primeCoalSum Ω g X θ₀ =
      -∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
        (twistedPrimeCoalSum Ω g X θ₀ (dirichletGauge χ)).re := by
  have hsum := sum_twistedPrimeCoalSum_dirichletGauge_eq_zero (q := q) (Ω := Ω) (g := g)
    hθ0 hθ hq hqX
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (1 : DirichletCharacter ℂ q)),
    twistedPrimeCoalSum_dirichletGauge_one] at hsum
  have hre := congrArg Complex.re hsum
  simp only [Complex.add_re, Complex.ofReal_re, Complex.re_sum, Complex.zero_re] at hre
  linarith

/-- The number of nontrivial Dirichlet characters modulo `q` is `φ(q) - 1`. -/
theorem card_erase_one_dirichletCharacter :
    (Finset.univ.erase (1 : DirichletCharacter ℂ q)).card = q.totient - 1 := by
  rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, ← Nat.card_eq_fintype_card,
    DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ]

/-- **Pigeonhole Nontrivial-Character Witness:**
Whenever `2 ≤ φ(q)` (e.g. `q ≥ 3`) and `θ₀ * X < q`, `2 * q * θ₀ < 1`, there exists a nontrivial
character `χ ≠ 1 (mod q)` with
`primeCoalSum Ω g X θ₀ / (φ(q) - 1) ≤ -Re twistedPrimeCoalSum Ω g X θ₀ (dirichletGauge χ)`. -/
theorem exists_nontriv_neg_re_twistedPrimeCoalSum_ge {Ω g : ℝ → ℝ} {X θ₀ : ℝ}
    (hφ : 2 ≤ q.totient) (hθ0 : 0 < θ₀) (hθ : θ₀ ≤ 1 / 2)
    (hq : 2 * (q : ℝ) * θ₀ < 1) (hqX : θ₀ * X < q) :
    ∃ χ : DirichletCharacter ℂ q, χ ≠ 1 ∧
      primeCoalSum Ω g X θ₀ / ((q.totient : ℝ) - 1) ≤
        -(twistedPrimeCoalSum Ω g X θ₀ (dirichletGauge χ)).re := by
  set S := Finset.univ.erase (1 : DirichletCharacter ℂ q)
  have hcard : S.card = q.totient - 1 := card_erase_one_dirichletCharacter
  have hne : S.Nonempty := Finset.card_pos.mp (by omega)
  have hφ1 : (0 : ℝ) < (q.totient : ℝ) - 1 := by
    have : (2 : ℝ) ≤ q.totient := by exact_mod_cast hφ
    linarith
  have hcast : (S.card : ℝ) = (q.totient : ℝ) - 1 := by
    rw [hcard, Nat.cast_sub (by omega)]
    simp
  have hsum_eq : ∑ χ ∈ S, (primeCoalSum Ω g X θ₀ / ((q.totient : ℝ) - 1)) =
      ∑ χ ∈ S, -(twistedPrimeCoalSum Ω g X θ₀ (dirichletGauge χ)).re := by
    rw [Finset.sum_const, nsmul_eq_mul, hcast, mul_div_cancel₀ _ hφ1.ne',
      Finset.sum_neg_distrib, primeCoalSum_eq_neg_sum_nontriv hθ0 hθ hq hqX]
  obtain ⟨χ, hχS, hle⟩ := Finset.exists_le_of_sum_le hne hsum_eq.le
  exact ⟨χ, (Finset.mem_erase.mp hχS).1, hle⟩

/-- **Cauchy–Schwarz RMS Reciprocity Over Nontrivial Dirichlet Characters:**
In the sub-progression window `θ₀ * X < q` and `2 * q * θ₀ < 1`,
`(primeCoalSum Ω g X θ₀)^2 ≤ (φ(q) - 1) * ∑_{χ ≠ 1} (Re twistedPrimeCoalSum Ω g X θ₀ (dirichletGauge χ))^2`. -/
theorem primeCoalSum_sq_le_totient_sub_one_mul_sum_sq {Ω g : ℝ → ℝ} {X θ₀ : ℝ}
    (hθ0 : 0 < θ₀) (hθ : θ₀ ≤ 1 / 2) (hq : 2 * (q : ℝ) * θ₀ < 1) (hqX : θ₀ * X < q) :
    (primeCoalSum Ω g X θ₀) ^ 2 ≤
      ((q.totient - 1 : ℕ) : ℝ) *
        ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
          ((twistedPrimeCoalSum Ω g X θ₀ (dirichletGauge χ)).re) ^ 2 := by
  rw [primeCoalSum_eq_neg_sum_nontriv hθ0 hθ hq hqX, neg_sq,
    ← card_erase_one_dirichletCharacter (q := q)]
  exact sq_sum_le_card_mul_sum_sq

end CharacterInversion

/-- **Non-Vacuity of the Sub-Progression Inversion Window at Bandwidth `4/3`:**
For any `0 < η < 1/3` and any intermediate modulus exponent `κ` with `1 / 3 + η < κ` and
`κ < 1 - η` (for instance `κ = 2 / 3`), setting `X = (T / (2 * π)) ^ (4 / 3 : ℝ)`,
`θ₀ = T ^ (-1 + η)`, and `q = ⌊T ^ κ⌋₊` satisfies `3 ≤ q`, `0 < θ₀ ≤ 1 / 2`,
`2 * q * θ₀ < 1`, and `θ₀ * X < q` for all sufficiently large `T`. -/
theorem eventually_bandwidth43_subProgression_window {η κ : ℝ}
    (hη0 : 0 < η) (hlo : 1 / 3 + η < κ) (hhi : κ < 1 - η) :
    ∀ᶠ T in atTop,
      let q := ⌊T ^ κ⌋₊
      let θ₀ := T ^ (-1 + η)
      let X := (T / (2 * Real.pi)) ^ (4 / 3 : ℝ)
      3 ≤ q ∧ 0 < θ₀ ∧ θ₀ ≤ 1 / 2 ∧ 2 * (q : ℝ) * θ₀ < 1 ∧ θ₀ * X < q := by
  have hκ0 : 0 < κ := by linarith
  have ht_q : Tendsto (fun T : ℝ => T ^ κ) atTop atTop := tendsto_rpow_atTop hκ0
  have ht_θ : Tendsto (fun T : ℝ => T ^ (-1 + η)) atTop (𝓝 0) := by
    have h := tendsto_rpow_neg_atTop (by linarith : 0 < -(-1 + η))
    exact h.congr' (Eventually.of_forall fun T => by rw [neg_neg])
  have ht_hi : Tendsto (fun T : ℝ => 2 * T ^ (κ + (-1 + η))) atTop (𝓝 0) := by
    have h := tendsto_rpow_neg_atTop (by linarith : 0 < -(κ + (-1 + η)))
    simpa using (h.congr' (Eventually.of_forall fun T => by rw [neg_neg])).const_mul 2
  have ht_lo : Tendsto (fun T : ℝ => T ^ κ - T ^ (1 / 3 + η)) atTop atTop := by
    have hpos : 0 < κ - (1 / 3 + η) := by linarith
    have h1 := tendsto_rpow_atTop hκ0
    have h2 : Tendsto (fun T : ℝ => 1 - T ^ ((1 / 3 + η) - κ)) atTop (𝓝 1) := by
      have hr := tendsto_rpow_neg_atTop hpos
      have hr' : Tendsto (fun T : ℝ => T ^ ((1 / 3 + η) - κ)) atTop (𝓝 0) :=
        hr.congr' (Eventually.of_forall fun T => by congr 1; ring)
      simpa using tendsto_const_nhds.sub hr'
    refine (Tendsto.atTop_mul_pos zero_lt_one h1 h2).congr' ?_
    filter_upwards [eventually_gt_atTop 0] with T hT
    rw [mul_sub, mul_one, ← Real.rpow_add hT]
    congr 2
    ring
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    ht_q.eventually (eventually_ge_atTop (4 : ℝ)),
    ht_θ.eventually (Iic_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)),
    ht_hi.eventually (Iio_mem_nhds zero_lt_one),
    ht_lo.eventually (eventually_gt_atTop (1 : ℝ))] with T hT1 hTq hTθ hThi hTlo
  dsimp only
  have hT0 : 0 < T := zero_lt_one.trans_le hT1
  have hTκ0 : 0 ≤ T ^ κ := Real.rpow_nonneg hT0.le κ
  have hq3 : 3 ≤ ⌊T ^ κ⌋₊ := Nat.le_floor (by norm_num; linarith [hTq])
  have hθ_pos : 0 < T ^ (-1 + η) := Real.rpow_pos_of_pos hT0 _
  have hq_le : (⌊T ^ κ⌋₊ : ℝ) ≤ T ^ κ := Nat.floor_le hTκ0
  have hq_gt : T ^ κ - 1 < (⌊T ^ κ⌋₊ : ℝ) := Nat.sub_one_lt_floor (T ^ κ)
  have h2qθ : 2 * (⌊T ^ κ⌋₊ : ℝ) * T ^ (-1 + η) < 1 := by
    have hle : 2 * (⌊T ^ κ⌋₊ : ℝ) * T ^ (-1 + η) ≤ 2 * T ^ (κ + (-1 + η)) := by
      rw [Real.rpow_add hT0, ← mul_assoc]
      exact mul_le_mul_of_nonneg_right (by linarith) hθ_pos.le
    exact lt_of_le_of_lt hle hThi
  have hθX : T ^ (-1 + η) * (T / (2 * Real.pi)) ^ (4 / 3 : ℝ) < (⌊T ^ κ⌋₊ : ℝ) := by
    have h2pi_gt : (1 : ℝ) ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
    have hdiv_le : T / (2 * Real.pi) ≤ T := div_le_self hT0.le h2pi_gt
    have hrpow_le : (T / (2 * Real.pi)) ^ (4 / 3 : ℝ) ≤ T ^ (4 / 3 : ℝ) :=
      Real.rpow_le_rpow (by positivity) hdiv_le (by norm_num)
    have hprod_le : T ^ (-1 + η) * (T / (2 * Real.pi)) ^ (4 / 3 : ℝ) ≤ T ^ (1 / 3 + η) := by
      calc T ^ (-1 + η) * (T / (2 * Real.pi)) ^ (4 / 3 : ℝ)
          ≤ T ^ (-1 + η) * T ^ (4 / 3 : ℝ) := mul_le_mul_of_nonneg_left hrpow_le hθ_pos.le
        _ = T ^ (1 / 3 + η) := by
          rw [← Real.rpow_add hT0]
          congr 1
          ring
    linarith [hTlo, hq_gt]
  exact ⟨hq3, hθ_pos, hTθ, h2qθ, hθX⟩

/-! ## §2. Coupled `65/72` `N₀` Bound, `58/65` Critical Ordinates, and Five-Part `3/4` Dichotomy -/

private theorem criticalOrdinates_ge_of_simple_cert {u : ℝ → ℝ} {η ε ε' T : ℝ}
    (hε : 0 < ε) (hε'_pos : 0 < ε') (hε'_half : ε' ≤ ε / 2)
    (hε'_small : ε' ≤ 1 / 36) (hε'_rat : (1 + ε) * ε' ≤ (65 / 36) * ε)
    (hcert : (29 / 36 - ε') * (Ncount T (2 * T) : ℝ) - primeCoalescentSurplus u η T +
      (RHTower.offLineMultipleMass zetaZeroConfig T (2 * T) : ℝ) ≤ (N0simple T (2 * T) : ℝ)) :
    (58 / 65 - ε) * ((RHTower.zeroOrdinates zetaZeroConfig T (2 * T)).card : ℝ) -
      (36 / 65 + ε) * max 0 (primeCoalescentSurplus u η T) ≤
      ((RHTower.criticalOrdinates zetaZeroConfig T (2 * T)).card : ℝ) := by
  have hcensus := RHTower.two_mul_card_ordinates_le zetaZeroConfig T (2 * T)
  have hs := RHTower.N0s_le_card_criticalOrdinates zetaZeroConfig T (2 * T)
  have hsN0 := N0s_le_N0 zetaZeroConfig T (2 * T)
  rw [zetaZeroConfig_N] at hcensus
  rw [zetaZeroConfig_N0s] at hs hsN0
  have hcensus' : 2 * ((RHTower.zeroOrdinates zetaZeroConfig T (2 * T)).card : ℝ) +
      (zetaZeroConfig.N0 T (2 * T) : ℝ) ≤
      2 * ((RHTower.criticalOrdinates zetaZeroConfig T (2 * T)).card : ℝ) +
        (Ncount T (2 * T) : ℝ) := by
    exact_mod_cast hcensus
  have hs' : (N0simple T (2 * T) : ℝ) ≤
      ((RHTower.criticalOrdinates zetaZeroConfig T (2 * T)).card : ℝ) := by
    exact_mod_cast hs
  have hsN0' : (N0simple T (2 * T) : ℝ) ≤ (zetaZeroConfig.N0 T (2 * T) : ℝ) := by
    exact_mod_cast hsN0
  set o : ℝ := ((RHTower.zeroOrdinates zetaZeroConfig T (2 * T)).card : ℝ)
  set c : ℝ := ((RHTower.criticalOrdinates zetaZeroConfig T (2 * T)).card : ℝ)
  set N : ℝ := (Ncount T (2 * T) : ℝ)
  set Σ : ℝ := max 0 (primeCoalescentSurplus u η T)
  have ho : 0 ≤ o := Nat.cast_nonneg _
  have hc : 0 ≤ c := Nat.cast_nonneg _
  have hM : (0 : ℝ) ≤ RHTower.offLineMultipleMass zetaZeroConfig T (2 * T) := Nat.cast_nonneg _
  have hΣ0 : 0 ≤ Σ := le_max_left 0 _
  have hΣ_ge : primeCoalescentSurplus u η T ≤ Σ := le_max_right 0 _
  set h : ℝ := 29 / 36 - ε'
  have hh_lo : 7 / 9 ≤ h := by dsimp [h]; linarith
  have hh_hi : h < 29 / 36 := by dsimp [h]; linarith
  have hh_pos : 0 < h := by linarith
  have h1_sub_h : 0 < 1 - h := by linarith
  have h1h_pos : 0 < 1 + h := by linarith
  have hhN : h * N ≤ (N0simple T (2 * T) : ℝ) + Σ := by linarith
  have hhN_c : h * N ≤ c + Σ := by linarith
  have h2o : 2 * o ≤ 2 * c + (1 - h) * N + Σ := by linarith
  have h2ho : 2 * h * o ≤ (1 + h) * c + Σ := by
    have hm1 := mul_le_mul_of_nonneg_left h2o hh_pos.le
    have hm2 := mul_le_mul_of_nonneg_left hhN_c h1_sub_h.le
    nlinarith
  have hcoef_o : (58 / 65 - ε) * (1 + h) ≤ 2 * h := by
    dsimp [h]
    nlinarith
  have hcoef_Σ : 1 ≤ (36 / 65 + ε) * (1 + h) := by
    have hle : (36 / 65 + ε) * ε' ≤ (1 + ε) * ε' :=
      mul_le_mul_of_nonneg_right (by linarith) hε'_pos.le
    dsimp [h]
    linarith
  have hmul : ((58 / 65 - ε) * o - (36 / 65 + ε) * Σ) * (1 + h) ≤ c * (1 + h) := by
    have ho_mul := mul_le_mul_of_nonneg_right hcoef_o ho
    have hΣ_mul := mul_le_mul_of_nonneg_right hcoef_Σ hΣ0
    nlinarith
  exact le_of_mul_le_mul_right hmul h1h_pos

/-- **Coupled Unconditional `65/72` Lower Bound on `N₀`:**
Combining `offLineSimple_add_two_offLineMultiple_le_seven_thirtySixths_add_primeCoalescentSurplus`
with `offLineSimpleCount_le_near_add_far` and `eventually_offLineFarMass_le` proves unconditionally
that for every `0 < η < 1/3`, `A > 0`, and `ε > 0`, there exists a smooth window profile `u` such
that for all large `T`,
`(65/72 - 1/(2A) - ε) N(T, 2T) - (1/2) offLineSimpleNear (A / log T) - (1/2) primeCoalescentSurplus u η T ≤ N₀(T, 2T)`. -/
theorem N0_ge_sixtyFive_seventySeconds_sub_half_near_sub_half_primeSurplus
    {η A ε : ℝ} (hη0 : 0 < η) (hη3 : η < 1 / 3) (hA : 0 < A) (hε : 0 < ε) :
    ∃ (u : ℝ → ℝ) (ε₁ : ℝ), WindowProfile ε₁ u ∧ ∀ᶠ T in atTop,
      (65 / 72 - 1 / (2 * A) - ε) * (Ncount T (2 * T) : ℝ) -
        (1 / 2 : ℝ) * (RHTower.offLineSimpleNear zetaZeroConfig (A / Real.log T) T (2 * T) : ℝ) -
        (1 / 2 : ℝ) * primeCoalescentSurplus u η T ≤
        (N0 T (2 * T) : ℝ) := by
  obtain ⟨u, ε₁, hu, hcert⟩ :=
    offLineSimple_add_two_offLineMultiple_le_seven_thirtySixths_add_primeCoalescentSurplus
      hη0 hη3 (by positivity : 0 < 2 * ε)
  refine ⟨u, ε₁, hu, ?_⟩
  filter_upwards [hcert, RHTower.eventually_offLineFarMass_le A hA] with T hcoal hfar
  have hN := RHTower.zeta_N_eq_N0_add_offLineSimple_add_offLineMultiple T (2 * T)
  have hsplit : (RHTower.offLineSimpleCount zetaZeroConfig T (2 * T) : ℝ) ≤
      (RHTower.offLineSimpleNear zetaZeroConfig (A / Real.log T) T (2 * T) : ℝ) +
        (RHTower.offLineFarMass zetaZeroConfig (A / Real.log T) T (2 * T) : ℝ) := by
    exact_mod_cast RHTower.offLineSimpleCount_le_near_add_far zetaZeroConfig
      (A / Real.log T) T (2 * T)
  have hdiv : (1 / A) * (Ncount T (2 * T) : ℝ) =
      2 * (1 / (2 * A)) * (Ncount T (2 * T) : ℝ) := by ring
  linarith

/-- **Coupled Unconditional `58/65` Critical-Ordinate Census Bound (`58/65 ≈ 0.8923`):**
For every `0 < η < 1/3` and `ε > 0`, there exists a smooth window profile `u` such that for all
large `T`,
`(58/65 - ε) #zeroOrdinates(T, 2T) - (36/65 + ε) max(0, primeCoalescentSurplus u η T) ≤ #criticalOrdinates(T, 2T)`. -/
theorem criticalOrdinates_ge_fiftyEight_sixtyFifths_sub_primeSurplus
    {η ε : ℝ} (hη0 : 0 < η) (hη3 : η < 1 / 3) (hε : 0 < ε) :
    ∃ (u : ℝ → ℝ) (ε₁ : ℝ), WindowProfile ε₁ u ∧ ∀ᶠ T in atTop,
      (58 / 65 - ε) * ((RHTower.zeroOrdinates zetaZeroConfig T (2 * T)).card : ℝ) -
        (36 / 65 + ε) * max 0 (primeCoalescentSurplus u η T) ≤
        ((RHTower.criticalOrdinates zetaZeroConfig T (2 * T)).card : ℝ) := by
  set ε' := min (min (ε / 2) (1 / 36)) ((65 / 36) * ε / (1 + ε))
  have hε'_pos : 0 < ε' :=
    lt_min (lt_min (by positivity) (by norm_num)) (div_pos (by positivity) (by positivity))
  have hε'_half : ε' ≤ ε / 2 := (min_le_left _ _).trans (min_le_left _ _)
  have hε'_small : ε' ≤ 1 / 36 := (min_le_left _ _).trans (min_le_right _ _)
  have hε'_rat : (1 + ε) * ε' ≤ (65 / 36) * ε := by
    have hle : ε' ≤ (65 / 36) * ε / (1 + ε) := min_le_right _ _
    have hm := mul_le_mul_of_nonneg_left hle (by positivity : 0 ≤ 1 + ε)
    rwa [mul_div_cancel₀ _ (by positivity : (1 + ε) ≠ 0)] at hm
  obtain ⟨u, ε₁, hu, hcert⟩ :=
    zeta_primeCoalescent_certificate_simple_and_offLineMultiple hη0 hη3 hε'_pos
  refine ⟨u, ε₁, hu, ?_⟩
  filter_upwards [hcert] with T hT
  exact criticalOrdinates_ge_of_simple_cert hε hε'_pos hε'_half hε'_small hε'_rat hT

/-- **Simultaneous Five-Part Obstruction Dichotomy for `3/4` Critical-Line Zero Copies:**
Unconditionally, for every `0 < η < 1/3`, `A > 0`, and `ε > 0`, there exists a smooth window
profile `u` such that in every sufficiently large dyadic window `(T, 2T]`, **either** at least
`3/4` of all nontrivial zero copies lie on the critical line (`(3/4) N ≤ N₀`), **or all five**
structural constraints hold simultaneously:
1. Simple near-line clustering: `(HD 1 - 1/2 - 1/A - ε) N ≤ offLineSimpleNear (A / log T)`;
2. Off-line multiple suppression (`< 7.75%`): `offLineMultipleMass < (3/4 - HD 1 + ε) N`;
3. Multiplicity-penalized prime surplus floor: `(1/18 - ε) N + offLineMultipleMass < primeCoalescentSurplus u η T`;
4. Joint near-line + prime-surplus floor: `(11/36 - 1/A - ε) N < offLineSimpleNear (A / log T) + primeCoalescentSurplus u η T`;
5. Critical-ordinate bound: `(58/65 - ε) #zeroOrdinates - (36/65 + ε) max(0, primeCoalescentSurplus u η T) ≤ #criticalOrdinates`. -/
theorem three_quarters_or_simultaneous_five_part_obstruction
    {η A ε : ℝ} (hη0 : 0 < η) (hη3 : η < 1 / 3) (hA : 0 < A) (hε : 0 < ε) :
    ∃ (u : ℝ → ℝ) (ε₁ : ℝ), WindowProfile ε₁ u ∧ ∀ᶠ T in atTop,
      3 / 4 * (Ncount T (2 * T) : ℝ) ≤ (N0 T (2 * T) : ℝ) ∨
        ((Zeta23.ThmD.HD 1 - 1 / 2 - 1 / A - ε) * (Ncount T (2 * T) : ℝ) ≤
            (RHTower.offLineSimpleNear zetaZeroConfig (A / Real.log T) T (2 * T) : ℝ) ∧
          (RHTower.offLineMultipleMass zetaZeroConfig T (2 * T) : ℝ) <
            (3 / 4 - Zeta23.ThmD.HD 1 + ε) * (Ncount T (2 * T) : ℝ) ∧
          (1 / 18 - ε) * (Ncount T (2 * T) : ℝ) +
              (RHTower.offLineMultipleMass zetaZeroConfig T (2 * T) : ℝ) <
            primeCoalescentSurplus u η T ∧
          (11 / 36 - 1 / A - ε) * (Ncount T (2 * T) : ℝ) <
            (RHTower.offLineSimpleNear zetaZeroConfig (A / Real.log T) T (2 * T) : ℝ) +
              primeCoalescentSurplus u η T ∧
          (58 / 65 - ε) * ((RHTower.zeroOrdinates zetaZeroConfig T (2 * T)).card : ℝ) -
              (36 / 65 + ε) * max 0 (primeCoalescentSurplus u η T) ≤
            ((RHTower.criticalOrdinates zetaZeroConfig T (2 * T)).card : ℝ)) := by
  set ε' := min (min (ε / 2) (1 / 36)) ((65 / 36) * ε / (1 + ε))
  have hε'_pos : 0 < ε' :=
    lt_min (lt_min (by positivity) (by norm_num)) (div_pos (by positivity) (by positivity))
  have hε'_half : ε' ≤ ε / 2 := (min_le_left _ _).trans (min_le_left _ _)
  have hε'_small : ε' ≤ 1 / 36 := (min_le_left _ _).trans (min_le_right _ _)
  have hε'_rat : (1 + ε) * ε' ≤ (65 / 36) * ε := by
    have hle : ε' ≤ (65 / 36) * ε / (1 + ε) := min_le_right _ _
    have hm := mul_le_mul_of_nonneg_left hle (by positivity : 0 ≤ 1 + ε)
    rwa [mul_div_cancel₀ _ (by positivity : (1 + ε) ≠ 0)] at hm
  obtain ⟨u, ε₁, hu, hcert⟩ :=
    zeta_primeCoalescent_certificate_simple_and_offLineMultiple hη0 hη3 hε'_pos
  obtain ⟨T_mt, hT_mt⟩ := RHTower.offLineSimple_add_two_offLineMultiple_le_one_sub_HD_one
    (ε / 2) (by positivity)
  refine ⟨u, ε₁, hu, ?_⟩
  filter_upwards [hcert, RHTower.eventually_offLineFarMass_le A hA,
    eventually_ge_atTop T_mt] with T hcoal hfar hTmt
  by_cases h34 : 3 / 4 * (Ncount T (2 * T) : ℝ) ≤ (N0 T (2 * T) : ℝ)
  · exact Or.inl h34
  · right
    push Not at h34
    have hmt := hT_mt T hTmt
    have hN := RHTower.zeta_N_eq_N0_add_offLineSimple_add_offLineMultiple T (2 * T)
    have hsN0 : (N0simple T (2 * T) : ℝ) ≤ (N0 T (2 * T) : ℝ) := by
      exact_mod_cast RHTower.zeta_N0simple_le_N0 T (2 * T)
    have hsplit : (RHTower.offLineSimpleCount zetaZeroConfig T (2 * T) : ℝ) ≤
        (RHTower.offLineSimpleNear zetaZeroConfig (A / Real.log T) T (2 * T) : ℝ) +
          (RHTower.offLineFarMass zetaZeroConfig (A / Real.log T) T (2 * T) : ℝ) := by
      exact_mod_cast RHTower.offLineSimpleCount_le_near_add_far zetaZeroConfig
        (A / Real.log T) T (2 * T)
    have hN_nonneg : (0 : ℝ) ≤ (Ncount T (2 * T) : ℝ) := Nat.cast_nonneg _
    have hN_pos : (0 : ℝ) < (Ncount T (2 * T) : ℝ) := by
      have h0 : (0 : ℝ) ≤ N0 T (2 * T) := Nat.cast_nonneg _
      linarith
    have hε'_N : ε' * (Ncount T (2 * T) : ℝ) ≤ (ε / 2) * (Ncount T (2 * T) : ℝ) :=
      mul_le_mul_of_nonneg_right hε'_half hN_nonneg
    have hε_strict : (ε / 2) * (Ncount T (2 * T) : ℝ) < ε * (Ncount T (2 * T) : ℝ) :=
      mul_lt_mul_of_pos_right (by linarith) hN_pos
    have hcoal_sum : (RHTower.offLineSimpleCount zetaZeroConfig T (2 * T) : ℝ) +
        2 * (RHTower.offLineMultipleMass zetaZeroConfig T (2 * T) : ℝ) ≤
        (7 / 36 + ε') * (Ncount T (2 * T) : ℝ) + primeCoalescentSurplus u η T := by
      linarith
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · linarith
    · linarith
    · linarith
    · linarith
    · exact criticalOrdinates_ge_of_simple_cert hε hε'_pos hε'_half hε'_small hε'_rat hcoal

end GaloisForLFunctions.ArithmeticCorrelationGeometry

end
