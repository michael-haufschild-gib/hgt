import GaloisForLFunctions.RHTower.SourceHorizontalWoldPrimeClockProfile
import GaloisForLFunctions.RHTower.EulerHellingerCubicWoldGammaFactorization
import GaloisForLFunctions.HTGeometry.ZetaVerticalAlmostPeriodic

/-!
# Pre-Xi Euler--Gamma cubic negative channel with source renormalization

This module constructs the missing channel before Xi selection.  The literal third logarithmic
Euler jet supplies a negative prime-power current with depth coefficient `k²`; its positive
magnitude is non-summable and has intrinsic cubic coefficient `1/3`.  The depth-one Wold source is
not used to amplify that current.  It is subtracted coefficientwise on the same natural-number
source.  The remaining positive defect is strictly nonzero but `O((log p)³/p²)`, hence summable.

Natural cutoffs use `Finset.range X`, not the ordered-prime clock.  The resulting renormalized
negative current converges unconditionally.  The Euler and reflected-Hellinger third-jet
identities preserve source sign, prime labels, and every prime-power multiplicity before any Xi
divisor is selected.

This closes existence and source-budget parts of the proposed producer.  It does not identify the
new Euler leg with a completed Gamma/Krein selected residue and therefore is not an RH proof.
-/

open Complex Filter Topology
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Positive magnitude of the source-natural negative Euler-log third jet at one prime. -/
def sourceHorizontalEulerGammaCubicAtom (p : Nat.Primes) : ℝ :=
  cubicAnnulusPrimeCurrent (p : ℕ) / 12

/-- Coefficientwise mismatch between the complete Euler--Gamma atom and the depth-one Wold atom. -/
def sourceHorizontalEulerGammaWoldCubicDefect (p : Nat.Primes) : ℝ :=
  sourceHorizontalEulerGammaCubicAtom p -
    woldCoeff 1 p * Real.log (p : ℝ) ^ 2

theorem sourceHorizontalEulerGammaCubicAtom_eq (p : Nat.Primes) :
    sourceHorizontalEulerGammaCubicAtom p =
      Real.log (p : ℝ) ^ 3 *
        ((p : ℝ)⁻¹ * (1 + (p : ℝ)⁻¹) / (1 - (p : ℝ)⁻¹) ^ 3) := by
  rw [sourceHorizontalEulerGammaCubicAtom,
    cubicAnnulusPrimeCurrent_eq p.property]
  ring

theorem woldCubicAtom_eq (p : Nat.Primes) :
    woldCoeff 1 p * Real.log (p : ℝ) ^ 2 =
      Real.log (p : ℝ) ^ 3 * (p : ℝ)⁻¹ * (1 - (p : ℝ)⁻¹) ^ 3 := by
  rw [woldCoeff, pow_one]
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast p.property.ne_zero
  field_simp

theorem sourceHorizontalEulerGammaWoldCubicDefect_eq (p : Nat.Primes) :
    sourceHorizontalEulerGammaWoldCubicDefect p =
      Real.log (p : ℝ) ^ 3 * (p : ℝ)⁻¹ *
        (((1 + (p : ℝ)⁻¹) - (1 - (p : ℝ)⁻¹) ^ 6) /
          (1 - (p : ℝ)⁻¹) ^ 3) := by
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast p.property.two_le
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  have hq : (p : ℝ)⁻¹ < 1 := by
    rw [inv_lt_one₀ hp0]
    exact_mod_cast p.property.one_lt
  have hne : (1 - (p : ℝ)⁻¹) ^ 3 ≠ 0 := by positivity
  rw [sourceHorizontalEulerGammaWoldCubicDefect,
    sourceHorizontalEulerGammaCubicAtom_eq, woldCubicAtom_eq]
  field_simp [hne]

theorem sourceHorizontalEulerGammaWoldCubicDefect_pos (p : Nat.Primes) :
    0 < sourceHorizontalEulerGammaWoldCubicDefect p := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast p.property.pos
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast p.property.one_lt
  have hqpos : 0 < (p : ℝ)⁻¹ := inv_pos.mpr hp0
  have hq1 : (p : ℝ)⁻¹ < 1 := (inv_lt_one₀ hp0).2 hp1
  have hbase0 : 0 ≤ 1 - (p : ℝ)⁻¹ := by linarith
  have hbase1 : 1 - (p : ℝ)⁻¹ < 1 := by linarith
  have hpow : (1 - (p : ℝ)⁻¹) ^ 6 < 1 :=
    pow_lt_one₀ hbase0 hbase1 (by norm_num)
  have hnum : 0 < (1 + (p : ℝ)⁻¹) - (1 - (p : ℝ)⁻¹) ^ 6 := by linarith
  have hlogpos : 0 < Real.log (p : ℝ) := Real.log_pos hp1
  rw [sourceHorizontalEulerGammaWoldCubicDefect_eq]
  positivity

theorem sourceHorizontalEulerGammaWoldCubicDefect_le (p : Nat.Primes) :
    sourceHorizontalEulerGammaWoldCubicDefect p ≤
      56 * Real.log (p : ℝ) ^ 3 / (p : ℝ) ^ 2 := by
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast p.property.two_le
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  let q : ℝ := (p : ℝ)⁻¹
  have hq0 : 0 ≤ q := (inv_pos.mpr hp0).le
  have hq2 : q ≤ 1 / 2 := by
    dsimp only [q]
    simpa only [one_div] using
      (inv_le_inv₀ hp0 (by norm_num : (0 : ℝ) < 2)).2 hp2
  have hqm2 : -2 ≤ -q := by linarith
  have hbern : 1 - 6 * q ≤ (1 - q) ^ 6 := by
    have hb := one_add_mul_le_pow hqm2 6
    norm_num at hb ⊢
    nlinarith
  have hnum : (1 + q) - (1 - q) ^ 6 ≤ 7 * q := by linarith
  have hbase : (1 / 2 : ℝ) ≤ 1 - q := by linarith
  have hden : (1 / 8 : ℝ) ≤ (1 - q) ^ 3 := by
    calc
      (1 / 8 : ℝ) = (1 / 2 : ℝ) ^ 3 := by norm_num
      _ ≤ (1 - q) ^ 3 := pow_le_pow_left₀ (by norm_num) hbase 3
  have hdenpos : 0 < (1 - q) ^ 3 := lt_of_lt_of_le (by norm_num) hden
  have hfrac : ((1 + q) - (1 - q) ^ 6) / (1 - q) ^ 3 ≤ 56 * q := by
    apply (div_le_iff₀ hdenpos).2
    calc
      (1 + q) - (1 - q) ^ 6 ≤ 7 * q := hnum
      _ ≤ (56 * q) * (1 - q) ^ 3 := by nlinarith
  rw [sourceHorizontalEulerGammaWoldCubicDefect_eq]
  dsimp only [q] at hfrac ⊢
  have hlog : 0 ≤ Real.log (p : ℝ) ^ 3 := by positivity
  have hmul := mul_le_mul_of_nonneg_left hfrac
    (mul_nonneg hlog (inv_nonneg.mpr hp0.le))
  calc
    Real.log (p : ℝ) ^ 3 * (p : ℝ)⁻¹ *
        (((1 + (p : ℝ)⁻¹) - (1 - (p : ℝ)⁻¹) ^ 6) /
          (1 - (p : ℝ)⁻¹) ^ 3)
        ≤ Real.log (p : ℝ) ^ 3 * (p : ℝ)⁻¹ * (56 * (p : ℝ)⁻¹) := hmul
    _ = 56 * Real.log (p : ℝ) ^ 3 / (p : ℝ) ^ 2 := by
      field_simp

set_option maxHeartbeats 800000 in
theorem summable_sourceHorizontalEulerGammaWoldCubicDefect :
    Summable sourceHorizontalEulerGammaWoldCubicDefect := by
  have hbase : Summable fun n : ℕ =>
      Real.log (n : ℝ) ^ 3 / (n : ℝ) ^ (2 : ℝ) :=
    HTGeometry.summable_log_pow_div_nat_rpow 3
      (by norm_num : (1 : ℝ) < 2)
  have hnat : Summable fun n : ℕ =>
      56 * Real.log (n : ℝ) ^ 3 / (n : ℝ) ^ (2 : ℝ) :=
    (hbase.mul_left 56).congr fun n => by ring
  have hprime : Summable fun p : Nat.Primes =>
      56 * Real.log (p : ℝ) ^ 3 / (p : ℝ) ^ (2 : ℝ) :=
    hnat.comp_injective Subtype.val_injective
  refine Summable.of_nonneg_of_le
    (fun p => (sourceHorizontalEulerGammaWoldCubicDefect_pos p).le)
    (fun p => ?_) hprime
  simpa only [Real.rpow_two] using sourceHorizontalEulerGammaWoldCubicDefect_le p

/-- The raw complete Euler--Gamma cubic mass through the `N`-th ordered prime. -/
def sourceHorizontalEulerGammaCubicMoment (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (N + 1),
    sourceHorizontalEulerGammaCubicAtom (nthPrimeSubtype n)

/-- Finite source counterterm mismatch through the `N`-th ordered prime. -/
def sourceHorizontalEulerGammaWoldCubicDefectMoment (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (N + 1),
    sourceHorizontalEulerGammaWoldCubicDefect (nthPrimeSubtype n)

/-- Additive coefficientwise split into Wold cubic bulk plus a summable source defect. -/
theorem sourceHorizontalEulerGammaCubicMoment_eq_wold_add_defect (N : ℕ) :
    sourceHorizontalEulerGammaCubicMoment N =
      (∑ n ∈ Finset.range (N + 1),
        woldCoeff 1 (nthPrimeSubtype n) * xiMassNthPrimeLogHeight n ^ 2) +
      sourceHorizontalEulerGammaWoldCubicDefectMoment N := by
  rw [sourceHorizontalEulerGammaCubicMoment,
    sourceHorizontalEulerGammaWoldCubicDefectMoment, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  rw [sourceHorizontalEulerGammaWoldCubicDefect]
  simp only [xiMassNthPrimeLogHeight]
  ring

theorem tendsto_sourceHorizontalEulerGammaWoldCubicDefectMoment :
    Tendsto sourceHorizontalEulerGammaWoldCubicDefectMoment atTop
      (nhds (∑' n : ℕ,
        sourceHorizontalEulerGammaWoldCubicDefect (nthPrimeSubtype n))) := by
  have hsum : Summable fun n : ℕ =>
      sourceHorizontalEulerGammaWoldCubicDefect (nthPrimeSubtype n) :=
    summable_sourceHorizontalEulerGammaWoldCubicDefect.comp_injective
      nthPrimeSubtype_injective
  have h := hsum.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
  change Tendsto (fun N : ℕ => ∑ n ∈ Finset.range (N + 1),
      sourceHorizontalEulerGammaWoldCubicDefect (nthPrimeSubtype n)) atTop _
  exact h

theorem tendsto_xiMassNthPrimeLogHeight_cube_atTop :
    Tendsto (fun N : ℕ => xiMassNthPrimeLogHeight N ^ 3) atTop atTop := by
  apply Filter.tendsto_atTop_mono' atTop _
    tendsto_xiMassNthPrimeLogHeight_atTop
  filter_upwards
    [tendsto_xiMassNthPrimeLogHeight_atTop.eventually_ge_atTop (1 : ℝ)]
    with N hN
  have hnonneg : 0 ≤ xiMassNthPrimeLogHeight N := by linarith
  nlinarith [mul_nonneg
    (mul_nonneg hnonneg (sub_nonneg.mpr hN)) (by linarith :
      0 ≤ xiMassNthPrimeLogHeight N + 1)]

theorem tendsto_sourceHorizontalEulerGammaWoldCubicDefectMoment_normalized_zero :
    Tendsto (fun N : ℕ =>
      sourceHorizontalEulerGammaWoldCubicDefectMoment N /
        xiMassNthPrimeLogHeight N ^ 3) atTop (nhds 0) :=
  tendsto_sourceHorizontalEulerGammaWoldCubicDefectMoment.div_atTop
    tendsto_xiMassNthPrimeLogHeight_cube_atTop

/-- Intrinsic prime-clock normalization of the divergent Euler--Gamma source current. -/
def sourceHorizontalEulerGammaCubicNormalizedMoment (N : ℕ) : ℝ :=
  sourceHorizontalEulerGammaCubicMoment N /
    xiMassNthPrimeLogHeight N ^ 3

theorem sourceHorizontalEulerGammaCubicNormalizedMoment_eq (N : ℕ) :
    sourceHorizontalEulerGammaCubicNormalizedMoment N =
      sourceHorizontalWoldOrderedNormalizedMoment N 2 +
        sourceHorizontalEulerGammaWoldCubicDefectMoment N /
          xiMassNthPrimeLogHeight N ^ 3 := by
  have hheight : xiMassNthPrimeLogHeight N ≠ 0 := by
    exact (xiMassNthPrimeLogHeight_pos N).ne'
  rw [sourceHorizontalEulerGammaCubicNormalizedMoment,
    sourceHorizontalEulerGammaCubicMoment_eq_wold_add_defect,
    sourceHorizontalWoldOrderedNormalizedMoment]
  norm_num
  field_simp [hheight]

/-- The new complete source channel has the exact cubic mass needed by the BV firewall. -/
theorem tendsto_sourceHorizontalEulerGammaCubicNormalizedMoment :
    Tendsto sourceHorizontalEulerGammaCubicNormalizedMoment atTop (nhds (1 / 3 : ℝ)) := by
  have h := (tendsto_sourceHorizontalWoldOrderedNormalizedMoment 2).add
    tendsto_sourceHorizontalEulerGammaWoldCubicDefectMoment_normalized_zero
  convert h using 1
  · funext N
    rw [sourceHorizontalEulerGammaCubicNormalizedMoment_eq]
  · norm_num

/-- Raw complete Euler--Gamma cubic mass diverges; normalization is not amplification of a
convergent current. -/
theorem tendsto_sourceHorizontalEulerGammaCubicMoment_atTop :
    Tendsto sourceHorizontalEulerGammaCubicMoment atTop atTop := by
  have hscaled := tendsto_xiMassNthPrimeLogHeight_cube_atTop.const_mul_atTop
    (by norm_num : (0 : ℝ) < 1 / 6)
  apply Filter.tendsto_atTop_mono' atTop _ hscaled
  filter_upwards
    [(tendsto_sourceHorizontalEulerGammaCubicNormalizedMoment.eventually_const_lt
      (by norm_num : (1 / 6 : ℝ) < 1 / 3))]
    with N hN
  rw [sourceHorizontalEulerGammaCubicNormalizedMoment] at hN
  have hden : 0 < xiMassNthPrimeLogHeight N ^ 3 :=
    pow_pos (xiMassNthPrimeLogHeight_pos N) 3
  exact (lt_div_iff₀ hden).mp hN |>.le

theorem not_summable_sourceHorizontalEulerGammaCubicAtom :
    ¬ Summable sourceHorizontalEulerGammaCubicAtom := by
  intro hsum
  have hnat : Summable fun n : ℕ =>
      sourceHorizontalEulerGammaCubicAtom (nthPrimeSubtype n) :=
    hsum.comp_injective nthPrimeSubtype_injective
  have hfinite := hnat.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
  have hfinite' : Tendsto sourceHorizontalEulerGammaCubicMoment atTop
      (nhds (∑' n : ℕ, sourceHorizontalEulerGammaCubicAtom (nthPrimeSubtype n))) := by
    change Tendsto (fun N : ℕ => ∑ n ∈ Finset.range (N + 1),
      sourceHorizontalEulerGammaCubicAtom (nthPrimeSubtype n)) atTop _
    exact hfinite
  exact not_tendsto_nhds_of_tendsto_atTop
    tendsto_sourceHorizontalEulerGammaCubicMoment_atTop _ hfinite'

/-- Literal additive source renormalization: the negative divergent Euler third jet plus the
positive divergent Wold bulk converges to the finite negative defect. -/
def sourceHorizontalEulerGammaCubicRenormalizedNegativeCurrent (N : ℕ) : ℝ :=
  -sourceHorizontalEulerGammaCubicMoment N +
    ∑ n ∈ Finset.range (N + 1),
      woldCoeff 1 (nthPrimeSubtype n) * xiMassNthPrimeLogHeight n ^ 2

theorem sourceHorizontalEulerGammaCubicRenormalizedNegativeCurrent_eq (N : ℕ) :
    sourceHorizontalEulerGammaCubicRenormalizedNegativeCurrent N =
      -sourceHorizontalEulerGammaWoldCubicDefectMoment N := by
  rw [sourceHorizontalEulerGammaCubicRenormalizedNegativeCurrent,
    sourceHorizontalEulerGammaCubicMoment_eq_wold_add_defect]
  ring

theorem tendsto_sourceHorizontalEulerGammaCubicRenormalizedNegativeCurrent :
    Tendsto sourceHorizontalEulerGammaCubicRenormalizedNegativeCurrent atTop
      (nhds (-(∑' n : ℕ,
        sourceHorizontalEulerGammaWoldCubicDefect (nthPrimeSubtype n)))) := by
  have h := tendsto_sourceHorizontalEulerGammaWoldCubicDefectMoment.neg
  convert h using 1
  funext N
  exact sourceHorizontalEulerGammaCubicRenormalizedNegativeCurrent_eq N

/-- Prime-supported extension of the complete Euler--Gamma cubic atom to the literal natural-number
source.  It vanishes away from primes and contains no clock or Xi selection. -/
def sourceHorizontalEulerGammaCubicNaturalAtom (n : ℕ) : ℝ :=
  if hn : n.Prime then sourceHorizontalEulerGammaCubicAtom ⟨n, hn⟩ else 0

/-- Prime-supported Wold counterterm on the same literal source. -/
def sourceHorizontalEulerGammaWoldCubicNaturalCounterterm (n : ℕ) : ℝ :=
  if hn : n.Prime then woldCoeff 1 ⟨n, hn⟩ * Real.log (n : ℝ) ^ 2 else 0

/-- Prime-supported summable mismatch on the natural-number source. -/
def sourceHorizontalEulerGammaWoldCubicNaturalDefect (n : ℕ) : ℝ :=
  if hn : n.Prime then sourceHorizontalEulerGammaWoldCubicDefect ⟨n, hn⟩ else 0

theorem sourceHorizontalEulerGammaCubicNaturalAtom_sub_counterterm (n : ℕ) :
    -sourceHorizontalEulerGammaCubicNaturalAtom n +
        sourceHorizontalEulerGammaWoldCubicNaturalCounterterm n =
      -sourceHorizontalEulerGammaWoldCubicNaturalDefect n := by
  by_cases hn : n.Prime
  · simp only [sourceHorizontalEulerGammaCubicNaturalAtom,
      sourceHorizontalEulerGammaWoldCubicNaturalCounterterm,
      sourceHorizontalEulerGammaWoldCubicNaturalDefect, dif_pos hn]
    rw [sourceHorizontalEulerGammaWoldCubicDefect]
    ring
  · simp [sourceHorizontalEulerGammaCubicNaturalAtom,
      sourceHorizontalEulerGammaWoldCubicNaturalCounterterm,
      sourceHorizontalEulerGammaWoldCubicNaturalDefect, hn]

theorem summable_sourceHorizontalEulerGammaWoldCubicNaturalDefect :
    Summable sourceHorizontalEulerGammaWoldCubicNaturalDefect := by
  let primeSet : Set ℕ := {n | n.Prime}
  have hcomp : Summable
      (sourceHorizontalEulerGammaWoldCubicNaturalDefect ∘ Subtype.val : primeSet → ℝ) :=
    summable_sourceHorizontalEulerGammaWoldCubicDefect.congr fun p => by
      simp [sourceHorizontalEulerGammaWoldCubicNaturalDefect, primeSet, p.2]
  have hind : Summable
      (primeSet.indicator sourceHorizontalEulerGammaWoldCubicNaturalDefect) :=
    summable_subtype_iff_indicator.mp hcomp
  refine hind.congr fun n => ?_
  by_cases hn : n.Prime
  · simp [primeSet, hn]
  · simp [primeSet, sourceHorizontalEulerGammaWoldCubicNaturalDefect, hn]

theorem not_summable_sourceHorizontalEulerGammaCubicNaturalAtom :
    ¬ Summable sourceHorizontalEulerGammaCubicNaturalAtom := by
  intro hsum
  have hprime : Summable (fun p : Nat.Primes =>
      sourceHorizontalEulerGammaCubicNaturalAtom (p : ℕ)) :=
    hsum.comp_injective Subtype.val_injective
  apply not_summable_sourceHorizontalEulerGammaCubicAtom
  exact hprime.congr fun p => by
    simp [sourceHorizontalEulerGammaCubicNaturalAtom, p.2]

/-- Literal negative Euler third-jet atom plus positive Wold source counterterm below an ordinary
natural cutoff.  Construction precedes every ordered-prime clock and Xi selection. -/
def sourceHorizontalEulerGammaCubicNaturalRenormalizedNegativeCurrent (X : ℕ) : ℝ :=
  ∑ n ∈ Finset.range X,
    (-sourceHorizontalEulerGammaCubicNaturalAtom n +
      sourceHorizontalEulerGammaWoldCubicNaturalCounterterm n)

theorem sourceHorizontalEulerGammaCubicNaturalRenormalizedNegativeCurrent_eq (X : ℕ) :
    sourceHorizontalEulerGammaCubicNaturalRenormalizedNegativeCurrent X =
      ∑ n ∈ Finset.range X,
        -sourceHorizontalEulerGammaWoldCubicNaturalDefect n := by
  apply Finset.sum_congr rfl
  intro n hn
  exact sourceHorizontalEulerGammaCubicNaturalAtom_sub_counterterm n

/-- Natural source cutoffs converge to the finite renormalized negative cubic charge.  This is
coefficientwise cancellation, not clock-dependent amplification of a summable current. -/
theorem tendsto_sourceHorizontalEulerGammaCubicNaturalRenormalizedNegativeCurrent :
    Tendsto sourceHorizontalEulerGammaCubicNaturalRenormalizedNegativeCurrent atTop
      (nhds (-∑' n : ℕ, sourceHorizontalEulerGammaWoldCubicNaturalDefect n)) := by
  have h := summable_sourceHorizontalEulerGammaWoldCubicNaturalDefect.neg.hasSum.tendsto_sum_nat
  rw [show (-∑' n : ℕ, sourceHorizontalEulerGammaWoldCubicNaturalDefect n) =
      ∑' n : ℕ, -sourceHorizontalEulerGammaWoldCubicNaturalDefect n by
        rw [tsum_neg]]
  convert h using 1
  funext X
  exact sourceHorizontalEulerGammaCubicNaturalRenormalizedNegativeCurrent_eq X

/-- The canonical negative current below a natural cutoff, defined before every Xi selection. -/
def sourceHorizontalEulerGammaCubicNegativeCurrentBelow (X : ℕ) : ℝ :=
  -(∑ p ∈ Nat.primesBelow X, cubicAnnulusPrimeCurrent p / 12)

theorem sourceHorizontalEulerGammaCubicNaturalRawNegative_eq_sourceCurrent (X : ℕ) :
    (∑ n ∈ Finset.range X, -sourceHorizontalEulerGammaCubicNaturalAtom n) =
      sourceHorizontalEulerGammaCubicNegativeCurrentBelow X := by
  rw [sourceHorizontalEulerGammaCubicNegativeCurrentBelow, Finset.sum_neg_distrib,
    Nat.primesBelow, Finset.sum_filter]
  congr 1

/-- Euler-log orientation supplies the negative sign itself. -/
theorem sourceHorizontalEulerGammaCubicNegativeCurrentBelow_eq_eulerThirdJet (X : ℕ) :
    sourceHorizontalEulerGammaCubicNegativeCurrentBelow X =
      iteratedDeriv 3 (fun s => primeEulerLogBelow s X) 1 := by
  rw [sourceHorizontalEulerGammaCubicNegativeCurrentBelow,
    iteratedDeriv_three_primeEulerLogBelow, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  rw [cubicAnnulusPrimeCurrent_eq (Nat.prime_of_mem_primesBelow hp)]
  ring

/-- Equivalent reflected-Hellinger presentation with its forced confluence factor `12`. -/
theorem sourceHorizontalEulerGammaCubicNegativeCurrentBelow_eq_reflectedHellingerThirdJet
    (X : ℕ) :
    sourceHorizontalEulerGammaCubicNegativeCurrentBelow X =
      -(1 / 12 : ℝ) *
        iteratedDeriv 3 (fun c => logReflectedSewingBelow c X) 0 := by
  rw [sourceHorizontalEulerGammaCubicNegativeCurrentBelow,
    iteratedDeriv_three_logReflectedSewing_eq_cubicAnnulusCurrent]
  have hdiv : (∑ p ∈ Nat.primesBelow X, cubicAnnulusPrimeCurrent p / 12) =
      (1 / 12 : ℝ) * ∑ p ∈ Nat.primesBelow X, cubicAnnulusPrimeCurrent p := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p hp
    ring
  rw [hdiv]
  ring

/-- All prime-power depths occur with the exact cubic multiplicity `k^2`. -/
theorem sourceHorizontalEulerGammaCubicNegativeAtom_eq_depthSum (p : Nat.Primes) :
    -sourceHorizontalEulerGammaCubicAtom p =
      ∑' k : ℕ, -(Real.log (p : ℝ) ^ 3 * (k : ℝ) ^ 2 * ((p : ℝ)⁻¹) ^ k) := by
  rw [sourceHorizontalEulerGammaCubicAtom, cubicAnnulusPrimeCurrent]
  calc
    -((12 * Real.log (p : ℝ) ^ 3 *
          ∑' k : ℕ, (k : ℝ) ^ 2 * ((p : ℝ)⁻¹) ^ k) / 12) =
        -Real.log (p : ℝ) ^ 3 *
          ∑' k : ℕ, (k : ℝ) ^ 2 * ((p : ℝ)⁻¹) ^ k := by ring
    _ = ∑' k : ℕ,
        (-Real.log (p : ℝ) ^ 3) * ((k : ℝ) ^ 2 * ((p : ℝ)⁻¹) ^ k) := by
          rw [tsum_mul_left]
    _ = ∑' k : ℕ,
        -(Real.log (p : ℝ) ^ 3 * (k : ℝ) ^ 2 * ((p : ℝ)⁻¹) ^ k) := by
          apply tsum_congr
          intro k
          ring

/-- Capstone producer: the pre-Xi Euler third-jet channel is genuinely non-summable with cubic
coefficient `1/3`, while literal coefficientwise Wold renormalization has a summable defect and a
finite natural-cutoff limit. -/
theorem sourceHorizontalEulerGammaCubicNegativeRenormalizedChannel_producer :
    (¬ Summable sourceHorizontalEulerGammaCubicNaturalAtom) ∧
      Tendsto sourceHorizontalEulerGammaCubicNormalizedMoment atTop (nhds (1 / 3 : ℝ)) ∧
      Summable sourceHorizontalEulerGammaWoldCubicNaturalDefect ∧
      Tendsto sourceHorizontalEulerGammaCubicNaturalRenormalizedNegativeCurrent atTop
        (nhds (-∑' n : ℕ, sourceHorizontalEulerGammaWoldCubicNaturalDefect n)) := by
  exact ⟨not_summable_sourceHorizontalEulerGammaCubicNaturalAtom,
    tendsto_sourceHorizontalEulerGammaCubicNormalizedMoment,
    summable_sourceHorizontalEulerGammaWoldCubicNaturalDefect,
    tendsto_sourceHorizontalEulerGammaCubicNaturalRenormalizedNegativeCurrent⟩

end

end RHTower
