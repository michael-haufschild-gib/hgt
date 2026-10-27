import GaloisForLFunctions.ArithmeticCorrelationGeometry.TheCoalescentSurplusDecomposesOverItsStabilizers
import GaloisForLFunctions.RenormalizedBiarithmeticGeometry.TheCellHolonomyDefectCountsChargedCells

/-!
# Sub-Progression Dirichlet Stabilizer Inversion and Universal Polynomial Cell-Holonomy Growth

This module advances the gauge-stabilizer and cell-holonomy theory across
`ArithmeticCorrelationGeometry`, `BiarithmeticGaugeGeometry`, and
`RenormalizedBiarithmeticGeometry` via two unconditional results:

1. **Zero-Ramification Sub-Progression Dirichlet Stabilizer Inversion
   (`dirichletGauge_one_eq_zero`, `congruent_coalWeight_sum_eq_zero_of_mul_lt`,
   `primeCoalSum_eq_neg_sum_nontriv`, `exists_nontriv_neg_re_twistedPrimeCoalSum_ge`,
   `primeCoalSum_sq_le_totient_sub_one_mul_sum_sq`, `eventually_bandwidth43_subProgression_window`):**
   * Pointwise on all primes (including ramified primes dividing `q`),
     `dirichletGauge (1 : DirichletCharacter ℂ q) = 0`, so `twistedPrimeCoalSum` at `χ = 1` equals
     `primeCoalSum` with **zero ramified-prime error**.
   * In the intermediate sub-progression window `θ₀ * X < q` and `2 * q * θ₀ < 1` (non-vacuous across
     `κ ∈ (1 / 3 + η, 1 - η)` at bandwidth `4 / 3`), every coalescent prime pair `(n, m)` in
     `primeRange X` satisfies `1 ≤ |n - m| ≤ θ₀ * X < q`, annihilating the congruent stabilizer sum
     and yielding pure nontrivial-character inversion:
     `primeCoalSum Ω g X θ₀ = -∑_{χ ≠ 1 (mod q)} Re twistedPrimeCoalSum Ω g X θ₀ (dirichletGauge χ)`.

2. **Universal Polynomial Cell-Holonomy and Liouville Agreement Growth Along `(+1, ×2)`
   (`two_mul_mul_succ_mem_chargedCells_iff`, `exists_realSignChar_ne_succ_in_block`,
   `card_chargedCells_ge_of_fourth_pow`, `sqrt_sqrt_div_sub_one_le_card_chargedCells`,
   `sqrt_sqrt_div_sub_one_le_card_liouvilleAgreements`, `hsDefect_liouville_ge_of_fourth_pow`,
   `eventually_forall_le_hsDefect_realSign`):**
   Establishes polynomial cell-holonomy growth unconditionally across **every** real sign gauge `ω`
   flipping `2` (`realSignChar ω 2 = -1`, in particular `PrimeGauge.liouvilleGauge`):
   * Along the quadratic square-absorber locus `a = 2 * t * (t + 1)`, `2 * a + 1 = (2 * t + 1) ^ 2`
     is an odd square (`σ_ω(2a + 1) = +1`), reducing the affine holonomy charge `a ∈ chargedCells ω X`
     to a unit-shift sign change `σ_ω(t) ≠ σ_ω(t + 1)`.
   * Using multiplicative halving `σ_ω(2D) = -σ_ω(D)` and progression lifting `q = ⌊(u + d - 1)/d⌋`,
     every short block `[u, u + L]` with `L ≥ 6` and `36 * u ≤ L ^ 2` contains a sign change
     `σ_ω(t) ≠ σ_ω(t + 1)`.
   * Summing over the disjoint parabolic blocks `[9k², 9k² + 18k]` produces at least `K` distinct
     charged cells below `162 * (K + 1) ^ 4`, proving unconditionally for every `X : ℕ`:
     `Nat.sqrt (Nat.sqrt (X / 162)) - 1 ≤ (chargedCells ω X).card` and
     `Nat.sqrt (Nat.sqrt (X / 162)) - 1 ≤ (liouvilleAgreements X).card`,
     upgrading `RBG.one_le_liouvilleAgreements` (`1 ≤ N₊`) to polynomial `X^{1/4}` growth.
-/

open Finset Filter Topology Real
open scoped BigOperators ComplexConjugate

open Zeta23 Zeta23.PrimeSide

noncomputable section

namespace GaloisForLFunctions.ArithmeticCorrelationGeometry

open HTGeometry BiarithmeticGaugeGeometry RenormalizedBiarithmeticGeometry
  TransThresholdPairCorrelation

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
    rw [← Nat.cast_add, Nat.add_sub_of_le hab.le]
  have hzero : ((b - a : ℕ) : ZMod q) = 0 := by
    have h1 : (a : ZMod q) + 0 = (a : ZMod q) + ((b - a : ℕ) : ZMod q) := by
      calc (a : ZMod q) + 0 = (b : ZMod q) := by rw [add_zero, hmod]
        _ = (a : ZMod q) + ((b - a : ℕ) : ZMod q) := hadd
    exact (add_left_cancel h1).symm
  have hdvd : q ∣ b - a := (ZMod.natCast_eq_zero_iff (b - a) q).mp hzero
  exact absurd (Nat.le_of_dvd hpos hdvd) (not_le.mpr hlt)

private theorem le_of_mem_primeRange {X : ℝ} {n : ℕ} (hn : n ∈ primeRange X) : (n : ℝ) ≤ X := by
  obtain ⟨hn1, hnf⟩ := Finset.mem_Ioc.mp hn
  have hX0 : 0 ≤ X := by
    by_contra hneg
    have hf0 : ⌊X⌋₊ = 0 := Nat.floor_of_nonpos (le_of_not_ge hneg)
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
      calc 2 * (⌊T ^ κ⌋₊ : ℝ) * T ^ (-1 + η)
          ≤ 2 * T ^ κ * T ^ (-1 + η) :=
            mul_le_mul_of_nonneg_right (by linarith) hθ_pos.le
        _ = 2 * (T ^ κ * T ^ (-1 + η)) := by ring
        _ = 2 * T ^ (κ + (-1 + η)) := by rw [← Real.rpow_add hT0]
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

/-! ## §2. Universal Polynomial Cell-Holonomy and Liouville Agreement Growth -/

/-- Discrete intermediate-value witness: if `f a ≠ f b` on `a < b`, some step `n ∈ [a, b - 1]`
changes value (`f n ≠ f (n + 1)`). -/
private theorem exists_ne_succ_in_Icc_of_ne {f : ℕ → ℝ} {a b : ℕ} (hab : a < b)
    (hne : f a ≠ f b) : ∃ n ∈ Icc a (b - 1), f n ≠ f (n + 1) := by
  by_contra hall
  simp only [not_exists, not_and, not_ne_iff] at hall
  have hconst : ∀ k : ℕ, k ≤ b - a → f (a + k) = f a := by
    intro k hk
    induction k with
    | zero => simp
    | succ j ih =>
      have hj_le : j ≤ b - a := by omega
      have hmem : a + j ∈ Icc a (b - 1) := mem_Icc.mpr ⟨by omega, by omega⟩
      rw [show a + (j + 1) = (a + j) + 1 by omega, ← hall (a + j) hmem, ih hj_le]
  have hb : f b = f a := by
    simpa [Nat.add_sub_of_le hab.le] using hconst (b - a) le_rfl
  exact hne hb.symm

/-- **Quadratic Square-Absorber Charged-Cell Law:**
Along `a = 2 * t * (t + 1)` (`1 ≤ t`, `a ≤ X`), `2 * a + 1 = (2 * t + 1) ^ 2` has sign `+1` for
every real sign gauge `ω`. Whenever `realSignChar ω 2 = -1`, the cell `2 * t * (t + 1)` is charged
if and only if `realSignChar ω` changes sign across the unit step `t ↦ t + 1`. -/
theorem two_mul_mul_succ_mem_chargedCells_iff {ω : PrimeGauge} (hω : IsRealSignGauge ω)
    (h2 : realSignChar ω 2 = -1) {t X : ℕ} (ht : 1 ≤ t) (hX : 2 * t * (t + 1) ≤ X) :
    2 * t * (t + 1) ∈ chargedCells ω X ↔ realSignChar ω t ≠ realSignChar ω (t + 1) := by
  have ha_pos : 1 ≤ 2 * t * (t + 1) := by nlinarith
  have hmem : 2 * t * (t + 1) ∈ Icc 1 X := mem_Icc.mpr ⟨ha_pos, hX⟩
  have hsq_odd : 2 * (2 * t * (t + 1)) + 1 = (2 * t + 1) * (2 * t + 1) := by ring
  have hodd_one : realSignChar ω (2 * (2 * t * (t + 1)) + 1) = 1 := by
    rw [hsq_odd, realSignChar_mul hω, ← sq]
    exact realSignChar_sq_eq_one hω (by omega)
  have hev_eq : realSignChar ω (2 * t * (t + 1)) =
      -(realSignChar ω t * realSignChar ω (t + 1)) := by
    rw [show 2 * t * (t + 1) = 2 * (t * (t + 1)) by ring,
      realSignChar_mul hω, realSignChar_mul hω, h2]
    ring
  simp only [chargedCells, mem_filter]
  rw [and_iff_right hmem, hodd_one, hev_eq, mul_one, h2]
  have ht_pm := realSignChar_eq_one_or hω (by omega : t ≠ 0)
  have ht1_pm := realSignChar_eq_one_or hω (by omega : t + 1 ≠ 0)
  rcases ht_pm with ht1 | ht1 <;> rcases ht1_pm with hs1 | hs1 <;> norm_num [ht1, hs1]

/-- **Universal Short-Block Sign-Change Witness:**
For every real sign gauge `ω` with `realSignChar ω 2 = -1` and every block `[u, u + L]` with
`1 ≤ u`, `6 ≤ L`, and `36 * u ≤ L ^ 2`, there exists `t ∈ Icc u (u + L - 1)` such that
`realSignChar ω t ≠ realSignChar ω (t + 1)`. -/
theorem exists_realSignChar_ne_succ_in_block {ω : PrimeGauge} (hω : IsRealSignGauge ω)
    (h2 : realSignChar ω 2 = -1) {u L : ℕ} (hu : 1 ≤ u) (hL : 6 ≤ L) (hsq : 36 * u ≤ L ^ 2) :
    ∃ t ∈ Icc u (u + L - 1), realSignChar ω t ≠ realSignChar ω (t + 1) := by
  set D : ℕ := 2 * u / L + 1
  have hD_pos : 1 ≤ D := Nat.le_add_left 1 (2 * u / L)
  have hD_nz : realSignChar ω D ≠ 0 := by
    intro h0
    have h1 := realSignChar_sq_eq_one hω (by omega : D ≠ 0)
    rw [h0] at h1
    norm_num at h1
  have hD_flip : realSignChar ω D ≠ realSignChar ω (2 * D) := by
    rw [realSignChar_mul hω, h2]
    intro heq
    exact hD_nz (by linarith)
  obtain ⟨d, hd_mem, hd_ne⟩ := exists_ne_succ_in_Icc_of_ne (by omega : D < 2 * D) hD_flip
  obtain ⟨hDd, hd_hi⟩ := mem_Icc.mp hd_mem
  have hd_pos : 1 ≤ d := le_trans hD_pos hDd
  set q : ℕ := (u + d - 1) / d
  have hq_pos : 1 ≤ q := Nat.div_pos (by omega) (by omega)
  have hdiv_mod : d * q + (u + d - 1) % d = u + d - 1 := Nat.div_add_mod (u + d - 1) d
  have hmod_lt : (u + d - 1) % d < d := Nat.mod_lt _ (by omega)
  have hdq_lo : u ≤ d * q := by omega
  have hdq_hi : d * q ≤ u + d - 1 := Nat.mul_div_le (u + d - 1) d
  have hd1q_le : (d + 1) * q ≤ u + L := by
    have hstep1 : d * ((d + 1) * q) ≤ (d + 1) * (u + d - 1) := by
      rw [show d * ((d + 1) * q) = (d + 1) * (d * q) by ring]
      exact Nat.mul_le_mul_left (d + 1) hdq_hi
    suffices hkey : (d + 1) * (u + d - 1) ≤ d * (u + L) by
      exact Nat.le_of_mul_le_mul_left (le_trans hstep1 hkey) (by omega : 0 < d)
    by_cases hsmall : 2 * u < L
    · have hdiv0 : 2 * u / L = 0 := Nat.div_eq_of_lt hsmall
      have hd1 : d = 1 := by omega
      subst hd1
      omega
    · have hL_le : L ≤ 2 * u := le_of_not_gt hsmall
      have hu9 : 9 ≤ u := by nlinarith
      have hDL_gt : 2 * u < D * L := by
        have hdm := Nat.div_add_mod (2 * u) L
        have hrm := Nat.mod_lt (2 * u) (by omega : 0 < L)
        have hDL_eq : D * L = L * (2 * u / L) + L := by dsimp [D]; ring
        omega
      have hdL_gt : 2 * u + 1 ≤ d * L := by
        have := Nat.mul_le_mul_right L hDd
        omega
      have hd1L_le : (d - 1) * L ≤ 4 * u := by
        have hd_sub : d - 1 ≤ 2 * (2 * u / L) := by omega
        calc (d - 1) * L
            ≤ (2 * (2 * u / L)) * L := Nat.mul_le_mul_right L hd_sub
          _ = 2 * (2 * u / L * L) := by ring
          _ ≤ 2 * (2 * u) := Nat.mul_le_mul_left 2 (Nat.div_mul_le_self (2 * u) L)
          _ = 4 * u := by ring
      have h9d_le : 9 * (d - 1) ^ 2 ≤ 4 * u := by
        have hmul1 : 36 * u * (d - 1) ^ 2 ≤ L ^ 2 * (d - 1) ^ 2 :=
          Nat.mul_le_mul_right ((d - 1) ^ 2) hsq
        have hmul2 : L ^ 2 * (d - 1) ^ 2 ≤ (4 * u) ^ 2 := by
          rw [show L ^ 2 * (d - 1) ^ 2 = ((d - 1) * L) ^ 2 by ring]
          exact Nat.pow_le_pow_left hd1L_le 2
        nlinarith
      have hd2_le : d ^ 2 ≤ u + 1 := by
        by_cases hd3 : 3 ≤ d
        · have hz1 : (3 : ℤ) ≤ (d : ℤ) := by exact_mod_cast hd3
          have hz9 : 9 * ((d : ℤ) - 1) ^ 2 ≤ 4 * (u : ℤ) := by
            have hcast : ((d - 1 : ℕ) : ℤ) = (d : ℤ) - 1 := Nat.cast_sub hd_pos
            have h0 : (9 * (d - 1) ^ 2 : ℤ) ≤ (4 * u : ℤ) := by exact_mod_cast h9d_le
            simpa [hcast] using h0
          have hquad : (0 : ℤ) ≤ ((d : ℤ) - 1) * (5 * (d : ℤ) - 13) :=
            mul_nonneg (by omega) (by omega)
          have h4 : 4 * ((d : ℤ) ^ 2 - 1) ≤ 9 * ((d : ℤ) - 1) ^ 2 := by linarith
          have hzu : (d : ℤ) ^ 2 ≤ (u : ℤ) + 1 := by omega
          exact_mod_cast hzu
        · have hd2 : d ≤ 2 := by omega
          have : d ^ 2 ≤ 4 := by nlinarith
          omega
      have hz_goal : ((d : ℤ) + 1) * ((u : ℤ) + d - 1) ≤ (d : ℤ) * ((u : ℤ) + L) := by
        have hz_dL : 2 * (u : ℤ) + 1 ≤ (d : ℤ) * L := by exact_mod_cast hdL_gt
        have hz_d2 : (d : ℤ) ^ 2 ≤ (u : ℤ) + 1 := by exact_mod_cast hd2_le
        linarith [show ((d : ℤ) + 1) * ((u : ℤ) + d - 1) = (d : ℤ) * u + u + (d : ℤ) ^ 2 - 1 by ring,
          show (d : ℤ) * ((u : ℤ) + L) = (d : ℤ) * u + (d : ℤ) * L by ring]
      have hcast_lhs : (((d + 1) * (u + d - 1) : ℕ) : ℤ) = ((d : ℤ) + 1) * ((u : ℤ) + d - 1) := by
        simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_sub (by omega : 1 ≤ u + d), Nat.cast_one]
      have hcast_rhs : ((d * (u + L) : ℕ) : ℤ) = (d : ℤ) * ((u : ℤ) + L) := by push_cast; rfl
      exact_mod_cast (hcast_lhs ▸ hcast_rhs ▸ hz_goal)
  have hq_nz : realSignChar ω q ≠ 0 := by
    intro h0
    have h1 := realSignChar_sq_eq_one hω (by omega : q ≠ 0)
    rw [h0] at h1
    norm_num at h1
  have hdq_ne : realSignChar ω (d * q) ≠ realSignChar ω ((d + 1) * q) := by
    rw [realSignChar_mul hω, realSignChar_mul hω]
    exact fun heq => hd_ne (mul_right_cancel₀ hq_nz heq)
  obtain ⟨t, ht_mem, ht_ne⟩ := exists_ne_succ_in_Icc_of_ne (by nlinarith : d * q < (d + 1) * q) hdq_ne
  obtain ⟨ht_lo, ht_hi⟩ := mem_Icc.mp ht_mem
  exact ⟨t, mem_Icc.mpr ⟨by omega, by omega⟩, ht_ne⟩

/-- **Universal Polynomial Charged-Cell Growth (`card_chargedCells_ge_of_fourth_pow`):**
For every real sign gauge `ω` with `realSignChar ω 2 = -1`, every `K : ℕ`, and every `X : ℕ` with
`162 * (K + 1) ^ 4 ≤ X`, at least `K` cells in `[1, X]` carry nonzero dyadic holonomy charge:
`K ≤ (chargedCells ω X).card`. -/
theorem card_chargedCells_ge_of_fourth_pow {ω : PrimeGauge} (hω : IsRealSignGauge ω)
    (h2 : realSignChar ω 2 = -1) {K X : ℕ} (hX : 162 * (K + 1) ^ 4 ≤ X) :
    K ≤ (chargedCells ω X).card := by
  classical
  rcases Nat.eq_zero_or_pos K with rfl | hK
  · exact Nat.zero_le _
  have hex : ∀ k : ℕ, 1 ≤ k →
      ∃ t ∈ Icc (9 * k ^ 2) (9 * k ^ 2 + 18 * k - 1),
        realSignChar ω t ≠ realSignChar ω (t + 1) := by
    intro k hk
    refine exists_realSignChar_ne_succ_in_block hω h2 (by nlinarith) (by omega) ?_
    nlinarith
  let t : ℕ → ℕ := fun k => if hk : 1 ≤ k then Classical.choose (hex k hk) else 0
  have ht_spec : ∀ k : ℕ, 1 ≤ k →
      t k ∈ Icc (9 * k ^ 2) (9 * k ^ 2 + 18 * k - 1) ∧
        realSignChar ω (t k) ≠ realSignChar ω (t k + 1) := by
    intro k hk
    dsimp only [t]
    rw [dif_pos hk]
    exact Classical.choose_spec (hex k hk)
  let cellWitness : ℕ → ℕ := fun k => 2 * t k * (t k + 1)
  have hinj : Set.InjOn cellWitness (Icc 1 K : Set ℕ) := by
    intro k₁ hk₁ k₂ hk₂ heq
    rw [coe_Icc, Set.mem_Icc] at hk₁ hk₂
    have hstrict : ∀ a b : ℕ, 1 ≤ a → a < b → cellWitness a < cellWitness b := by
      intro a b ha hab
      have hta := (mem_Icc.mp (ht_spec a ha).1).2
      have htb := (mem_Icc.mp (ht_spec b (by omega)).1).1
      have ha1_le : (a + 1) ^ 2 ≤ b ^ 2 := Nat.pow_le_pow_left (by omega) 2
      have hlt_t : t a < t b := by
        have hstep : 9 * a ^ 2 + 18 * a - 1 < 9 * (a + 1) ^ 2 := by
          have : 9 * (a + 1) ^ 2 = 9 * a ^ 2 + 18 * a + 9 := by ring
          omega
        have : 9 * (a + 1) ^ 2 ≤ 9 * b ^ 2 := Nat.mul_le_mul_left 9 ha1_le
        omega
      dsimp only [cellWitness]
      nlinarith
    rcases lt_trichotomy k₁ k₂ with hlt | rfl | hgt
    · exact absurd heq (hstrict k₁ k₂ hk₁.1 hlt).ne
    · rfl
    · exact absurd heq.symm (hstrict k₂ k₁ hk₂.1 hgt).ne
  have hsub : (Icc 1 K).image cellWitness ⊆ chargedCells ω X := by
    intro a ha
    obtain ⟨k, hk_mem, rfl⟩ := mem_image.mp ha
    obtain ⟨hk1, hkK⟩ := mem_Icc.mp hk_mem
    obtain ⟨ht_mem, ht_ne⟩ := ht_spec k hk1
    obtain ⟨ht_lo, ht_hi⟩ := mem_Icc.mp ht_mem
    have ht1 : 1 ≤ t k := by nlinarith
    have htk_bound : t k + 1 ≤ 9 * (K + 1) ^ 2 := by
      have hk1_le : (k + 1) ^ 2 ≤ (K + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
      have h1 : 9 * k ^ 2 + 18 * k ≤ 9 * (k + 1) ^ 2 := by
        have : 9 * (k + 1) ^ 2 = 9 * k ^ 2 + 18 * k + 9 := by ring
        omega
      have h2 : 9 * (k + 1) ^ 2 ≤ 9 * (K + 1) ^ 2 := Nat.mul_le_mul_left 9 hk1_le
      omega
    have ha_le : 2 * t k * (t k + 1) ≤ X := by
      have hprod : 2 * t k * (t k + 1) ≤ 162 * (K + 1) ^ 4 := by
        calc 2 * t k * (t k + 1)
            ≤ 2 * (t k + 1) * (t k + 1) := by nlinarith
          _ ≤ 2 * (9 * (K + 1) ^ 2) * (9 * (K + 1) ^ 2) := by nlinarith
          _ = 162 * (K + 1) ^ 4 := by ring
      exact le_trans hprod hX
    exact (two_mul_mul_succ_mem_chargedCells_iff hω h2 ht1 ha_le).mpr ht_ne
  calc K = (Icc 1 K).card := by rw [Nat.card_Icc]; omega
    _ = ((Icc 1 K).image cellWitness).card := (card_image_of_injOn hinj).symm
    _ ≤ (chargedCells ω X).card := card_le_card hsub

/-- **All-`X` Unconditional Fourth-Root Charged-Cell Lower Bound:**
For every real sign gauge `ω` with `realSignChar ω 2 = -1` and **every** `X : ℕ`,
`Nat.sqrt (Nat.sqrt (X / 162)) - 1 ≤ (chargedCells ω X).card`. -/
theorem sqrt_sqrt_div_sub_one_le_card_chargedCells {ω : PrimeGauge} (hω : IsRealSignGauge ω)
    (h2 : realSignChar ω 2 = -1) (X : ℕ) :
    Nat.sqrt (Nat.sqrt (X / 162)) - 1 ≤ (chargedCells ω X).card := by
  set M := Nat.sqrt (Nat.sqrt (X / 162))
  rcases Nat.eq_zero_or_pos M with hM0 | hMpos
  · simp [hM0]
  · have hM2 : M ^ 2 ≤ Nat.sqrt (X / 162) := by
      simpa [sq] using Nat.sqrt_le (Nat.sqrt (X / 162))
    have hM4 : M ^ 4 ≤ X / 162 := by
      calc M ^ 4 = (M ^ 2) ^ 2 := by ring
        _ ≤ (Nat.sqrt (X / 162)) ^ 2 := Nat.pow_le_pow_left hM2 2
        _ ≤ X / 162 := by simpa [sq] using Nat.sqrt_le (X / 162)
    have h162 : 162 * ((M - 1) + 1) ^ 4 ≤ X := by
      rw [Nat.sub_add_cancel hMpos]
      calc 162 * M ^ 4 ≤ 162 * (X / 162) := Nat.mul_le_mul_left 162 hM4
        _ ≤ X := Nat.mul_div_le X 162
    exact card_chargedCells_ge_of_fourth_pow hω h2 h162

/-- **Unconditional `X^{1/4}` Growth of Liouville Agreements Along `(+1, ×2)`:**
For **every** `X : ℕ`, `Nat.sqrt (Nat.sqrt (X / 162)) - 1 ≤ (liouvilleAgreements X).card`,
and whenever `162 * (K + 1) ^ 4 ≤ X`, `K ≤ (liouvilleAgreements X).card`. -/
theorem sqrt_sqrt_div_sub_one_le_card_liouvilleAgreements (X : ℕ) :
    Nat.sqrt (Nat.sqrt (X / 162)) - 1 ≤ (liouvilleAgreements X).card := by
  rw [← chargedCells_liouville]
  exact sqrt_sqrt_div_sub_one_le_card_chargedCells isRealSignGauge_liouville
    (realSignChar_liouville_prime Nat.prime_two) X

theorem card_liouvilleAgreements_ge_of_fourth_pow {K X : ℕ} (hX : 162 * (K + 1) ^ 4 ≤ X) :
    K ≤ (liouvilleAgreements X).card := by
  rw [← chargedCells_liouville]
  exact card_chargedCells_ge_of_fourth_pow isRealSignGauge_liouville
    (realSignChar_liouville_prime Nat.prime_two) hX

/-- **Uniform Polynomial Lower Bound on the Dyadic Cell-Holonomy Defect (`hsDefect`):**
For every real sign gauge `ω` with `realSignChar ω 2 = -1`, every scalar `c : ℝ`, and every
`162 * (K + 1) ^ 4 ≤ X`, `2 * (K : ℝ) ≤ hsDefect ω X c` (and in particular at `liouvilleGauge`). -/
theorem hsDefect_ge_of_fourth_pow {ω : PrimeGauge} (hω : IsRealSignGauge ω)
    (h2 : realSignChar ω 2 = -1) {K X : ℕ} (hX : 162 * (K + 1) ^ 4 ≤ X) (c : ℝ) :
    2 * (K : ℝ) ≤ hsDefect ω X c := by
  have hcard : (K : ℝ) ≤ (chargedCells ω X).card := by
    exact_mod_cast card_chargedCells_ge_of_fourth_pow hω h2 hX
  linarith [hsDefect_ge_charged hω X c]

theorem hsDefect_liouville_ge_of_fourth_pow {K X : ℕ} (hX : 162 * (K + 1) ^ 4 ≤ X) (c : ℝ) :
    2 * (K : ℝ) ≤ hsDefect PrimeGauge.liouvilleGauge X c :=
  hsDefect_ge_of_fourth_pow isRealSignGauge_liouville
    (realSignChar_liouville_prime Nat.prime_two) hX c

/-- For every real sign gauge `ω` with `realSignChar ω 2 = -1`, the minimal real dyadic cell
holonomy defect diverges to `+∞` as `X → ∞`: for every `B : ℝ`, eventually `∀ c : ℝ, B ≤ hsDefect ω X c`. -/
theorem eventually_forall_le_hsDefect_realSign {ω : PrimeGauge} (hω : IsRealSignGauge ω)
    (h2 : realSignChar ω 2 = -1) (B : ℝ) :
    ∀ᶠ X : ℕ in atTop, ∀ c : ℝ, B ≤ hsDefect ω X c := by
  set K : ℕ := ⌈max B 0⌉₊
  filter_upwards [eventually_ge_atTop (162 * (K + 1) ^ 4)] with X hX c
  have hB : B ≤ (K : ℝ) := (le_max_left B 0).trans (Nat.le_ceil _)
  have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  have hdef := hsDefect_ge_of_fourth_pow hω h2 hX c
  linarith

end GaloisForLFunctions.ArithmeticCorrelationGeometry

end
