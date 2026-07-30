import GaloisForLFunctions.HTGeometry.ExponentZeroEulerGaugeCardinality
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Mathlib.Analysis.Complex.LocallyUniformLimit

/-!
# Exponent-zero Euler-gauge units

An exponent-zero gauge controls the local Euler-ratio perturbation at every positive exponent.
On a compact subset of the positive half-plane, its minimum real part supplies a uniform positive
gap between every denominator and zero.  The resulting summable majorant gives a locally normally
convergent product of the local ratios.

This file constructs that product and proves that it is holomorphic and nowhere zero throughout
the positive half-plane.  It is the analytic bridge from the exponent-zero gauge subgroup to exact
divisor preservation.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex Filter Set

noncomputable section

/-- One local factor of the infinite Euler ratio attached to an exponent-zero gauge. -/
noncomputable def exponentZeroEulerGaugeFactor
    (eta omega : PrimePhase Nat.Primes) (p : Nat.Primes) (s : ℂ) : ℂ :=
  localEulerGaugeRatio (p : ℝ) (eta p : ℂ) (((eta * omega) p : Circle) : ℂ) s

/-- The infinite Euler-ratio unit attached to a base phase and an exponent-zero gauge. -/
noncomputable def exponentZeroEulerGaugeUnit
    (eta omega : PrimePhase Nat.Primes) (s : ℂ) : ℂ :=
  ∏' p : Nat.Primes, exponentZeroEulerGaugeFactor eta omega p s

private theorem natPrime_cast_one_lt (p : Nat.Primes) : (1 : ℝ) < p := by
  exact_mod_cast p.prop.one_lt

private theorem natPrime_cast_two_le (p : Nat.Primes) : (2 : ℝ) ≤ p := by
  exact_mod_cast p.prop.two_le

private theorem circlePhaseProduct_norm (eta omega : PrimePhase Nat.Primes) (p : Nat.Primes) :
    ‖(((eta * omega) p : Circle) : ℂ)‖ = 1 := Circle.norm_coe _

/-- Every local factor is nonzero on the positive half-plane. -/
theorem exponentZeroEulerGaugeFactor_ne_zero
    (eta omega : PrimePhase Nat.Primes) (p : Nat.Primes) {s : ℂ}
    (hs : s ∈ positiveHalfPlane) :
    exponentZeroEulerGaugeFactor eta omega p s ≠ 0 := by
  exact localEulerGaugeRatio_ne_zero (natPrime_cast_one_lt p)
    (Circle.norm_coe _) (circlePhaseProduct_norm eta omega p) hs

/-- Every local factor is holomorphic on the positive half-plane. -/
theorem differentiableOn_exponentZeroEulerGaugeFactor
    (eta omega : PrimePhase Nat.Primes) (p : Nat.Primes) :
    DifferentiableOn ℂ (exponentZeroEulerGaugeFactor eta omega p) positiveHalfPlane := by
  exact differentiableOn_localEulerGaugeRatio_positiveHalfPlane
    (natPrime_cast_one_lt p) (circlePhaseProduct_norm eta omega p)

/-- Exact first-order form of a local Euler-ratio perturbation. -/
theorem exponentZeroEulerGaugeFactor_sub_one
    (eta omega : PrimePhase Nat.Primes) (p : Nat.Primes) {s : ℂ}
    (hs : s ∈ positiveHalfPlane) :
    exponentZeroEulerGaugeFactor eta omega p s - 1 =
      ((eta p : ℂ) * ((omega p : ℂ) - 1) * analyticPrimeDecay (p : ℝ) s) /
        (1 - (((eta * omega) p : Circle) : ℂ) * analyticPrimeDecay (p : ℝ) s) := by
  have hden : 1 - (((eta * omega) p : Circle) : ℂ) *
      analyticPrimeDecay (p : ℝ) s ≠ 0 :=
    one_sub_phase_mul_analyticPrimeDecay_ne_zero (natPrime_cast_one_lt p)
      (circlePhaseProduct_norm eta omega p) hs
  have hphase : (((eta * omega) p : Circle) : ℂ) =
      (eta p : ℂ) * (omega p : ℂ) := by
    rw [Pi.mul_apply, Circle.coe_mul]
  rw [exponentZeroEulerGaugeFactor, localEulerGaugeRatio]
  rw [hphase] at hden ⊢
  rw [div_sub_one hden]
  ring

@[simp]
theorem one_add_exponentZeroEulerGaugeFactor_sub_one
    (eta omega : PrimePhase Nat.Primes) (p : Nat.Primes) (s : ℂ) :
    1 + (exponentZeroEulerGaugeFactor eta omega p s - 1) =
      exponentZeroEulerGaugeFactor eta omega p s := by
  ring

/-- The positive uniform denominator gap obtained from a positive lower real part. -/
noncomputable def exponentZeroDenominatorGap (m : ℝ) : ℝ :=
  1 - Real.exp (-m * Real.log 2)

theorem exponentZeroDenominatorGap_pos {m : ℝ} (hm : 0 < m) :
    0 < exponentZeroDenominatorGap m := by
  rw [exponentZeroDenominatorGap, sub_pos]
  rw [Real.exp_lt_one_iff]
  nlinarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)]

/-- On a half-plane `m ≤ Re(s)`, prime decay is bounded by the exponent-zero weight at `m`. -/
theorem norm_analyticPrimeDecay_le_exponentZeroWeight
    {m : ℝ} (hm : 0 < m) (p : Nat.Primes) {s : ℂ} (hms : m ≤ s.re) :
    ‖analyticPrimeDecay (p : ℝ) s‖ ≤
      exponentZeroWeight natPrimeSize ⟨m, hm⟩ p := by
  rw [norm_analyticPrimeDecay]
  apply Real.exp_le_exp.mpr
  have hlog : 0 ≤ Real.log (p : ℝ) := (Real.log_pos (natPrime_cast_one_lt p)).le
  dsimp [exponentZeroWeight]
  nlinarith

/-- The denominator of every local ratio is uniformly separated from zero on `m ≤ Re(s)`. -/
theorem exponentZeroDenominatorGap_le_norm
    (eta omega : PrimePhase Nat.Primes) {m : ℝ} (hm : 0 < m)
    (p : Nat.Primes) {s : ℂ} (hms : m ≤ s.re) :
    exponentZeroDenominatorGap m ≤
      ‖1 - (((eta * omega) p : Circle) : ℂ) * analyticPrimeDecay (p : ℝ) s‖ := by
  have hdecay : ‖analyticPrimeDecay (p : ℝ) s‖ ≤ Real.exp (-m * Real.log 2) := by
    calc
      ‖analyticPrimeDecay (p : ℝ) s‖
          ≤ Real.exp (-m * Real.log (p : ℝ)) := by
            rw [norm_analyticPrimeDecay]
            apply Real.exp_le_exp.mpr
            have hlog : 0 ≤ Real.log (p : ℝ) :=
              (Real.log_pos (natPrime_cast_one_lt p)).le
            nlinarith
      _ ≤ Real.exp (-m * Real.log 2) := by
        apply Real.exp_le_exp.mpr
        have hlogle : Real.log 2 ≤ Real.log (p : ℝ) :=
          Real.log_le_log (by norm_num) (natPrime_cast_two_le p)
        nlinarith
  have hphase : ‖(((eta * omega) p : Circle) : ℂ) *
      analyticPrimeDecay (p : ℝ) s‖ ≤ Real.exp (-m * Real.log 2) := by
    rw [norm_mul, circlePhaseProduct_norm, one_mul]
    exact hdecay
  calc
    exponentZeroDenominatorGap m = 1 - Real.exp (-m * Real.log 2) := rfl
    _ ≤ 1 - ‖(((eta * omega) p : Circle) : ℂ) *
        analyticPrimeDecay (p : ℝ) s‖ := sub_le_sub_left hphase 1
    _ ≤ ‖1 - (((eta * omega) p : Circle) : ℂ) *
        analyticPrimeDecay (p : ℝ) s‖ := by
      let z : ℂ := (((eta * omega) p : Circle) : ℂ) * analyticPrimeDecay (p : ℝ) s
      change 1 - ‖z‖ ≤ ‖1 - z‖
      have htri := norm_sub_norm_le (1 : ℂ) z
      norm_num at htri
      linarith

/-- Uniform compact-half-plane majorant for one Euler-ratio perturbation. -/
theorem norm_exponentZeroEulerGaugeFactor_sub_one_le
    (eta omega : PrimePhase Nat.Primes) {m : ℝ} (hm : 0 < m)
    (p : Nat.Primes) {s : ℂ} (hs : s ∈ positiveHalfPlane) (hms : m ≤ s.re) :
    ‖exponentZeroEulerGaugeFactor eta omega p s - 1‖ ≤
      (exponentZeroDenominatorGap m)⁻¹ *
        (exponentZeroWeight natPrimeSize ⟨m, hm⟩ p * ‖1 - (omega p : ℂ)‖) := by
  rw [exponentZeroEulerGaugeFactor_sub_one eta omega p hs, norm_div]
  have hgap := exponentZeroDenominatorGap_le_norm eta omega hm p hms
  have hgap_nonneg : 0 ≤ exponentZeroDenominatorGap m :=
    (exponentZeroDenominatorGap_pos hm).le
  have hnum_nonneg :
      0 ≤ ‖(eta p : ℂ) * ((omega p : ℂ) - 1) * analyticPrimeDecay (p : ℝ) s‖ :=
    norm_nonneg _
  calc
    ‖(eta p : ℂ) * ((omega p : ℂ) - 1) * analyticPrimeDecay (p : ℝ) s‖ /
        ‖1 - (((eta * omega) p : Circle) : ℂ) * analyticPrimeDecay (p : ℝ) s‖
      ≤ ‖(eta p : ℂ) * ((omega p : ℂ) - 1) * analyticPrimeDecay (p : ℝ) s‖ /
          exponentZeroDenominatorGap m :=
        div_le_div_of_nonneg_left hnum_nonneg
          (exponentZeroDenominatorGap_pos hm) hgap
    _ = ‖1 - (omega p : ℂ)‖ * ‖analyticPrimeDecay (p : ℝ) s‖ /
          exponentZeroDenominatorGap m := by
        rw [norm_mul, norm_mul, Circle.norm_coe, one_mul, norm_sub_rev]
    _ ≤ ‖1 - (omega p : ℂ)‖ *
          exponentZeroWeight natPrimeSize ⟨m, hm⟩ p /
          exponentZeroDenominatorGap m := by
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left
            (norm_analyticPrimeDecay_le_exponentZeroWeight hm p hms) (norm_nonneg _))
          hgap_nonneg
    _ = (exponentZeroDenominatorGap m)⁻¹ *
          (exponentZeroWeight natPrimeSize ⟨m, hm⟩ p * ‖1 - (omega p : ℂ)‖) := by
        ring

/-- Exponent-zero gauges produce locally normally convergent Euler-ratio products. -/
theorem hasProdLocallyUniformlyOn_exponentZeroEulerGaugeFactor
    (eta omega : PrimePhase Nat.Primes)
    (homega : IsExponentZeroEulerGauge natPrimeSize omega) :
    HasProdLocallyUniformlyOn (exponentZeroEulerGaugeFactor eta omega)
      (exponentZeroEulerGaugeUnit eta omega) positiveHalfPlane := by
  apply hasProdLocallyUniformlyOn_of_forall_compact
    (isOpen_lt continuous_const Complex.continuous_re)
  intro K hKsub hKcompact
  rcases K.eq_empty_or_nonempty with rfl | hKne
  · simpa [hasProdUniformlyOn_iff_tendstoUniformlyOn] using
      (tendstoUniformlyOn_empty : TendstoUniformlyOn
        (fun F : Finset Nat.Primes => fun s : ℂ =>
          ∏ p ∈ F, exponentZeroEulerGaugeFactor eta omega p s)
        (exponentZeroEulerGaugeUnit eta omega) atTop ∅)
  · obtain ⟨smin, hsminK, hsmin⟩ :=
      hKcompact.exists_isMinOn hKne Complex.continuous_re.continuousOn
    have hm : 0 < smin.re := hKsub hsminK
    let u : Nat.Primes → ℝ := fun p =>
      (exponentZeroDenominatorGap smin.re)⁻¹ *
        (exponentZeroWeight natPrimeSize ⟨smin.re, hm⟩ p * ‖1 - (omega p : ℂ)‖)
    have hu : Summable u := by
      exact (homega ⟨smin.re, hm⟩).mul_left (exponentZeroDenominatorGap smin.re)⁻¹
    have hprod := hu.hasProdUniformlyOn_one_add hKcompact
      (Filter.Eventually.of_forall fun p s hs =>
        norm_exponentZeroEulerGaugeFactor_sub_one_le eta omega hm p (hKsub hs)
          ((isMinOn_iff.mp hsmin) s hs))
      (fun p => ((differentiableOn_exponentZeroEulerGaugeFactor eta omega p).continuousOn.mono
        hKsub).sub continuousOn_const)
    simpa only [one_add_exponentZeroEulerGaugeFactor_sub_one,
      exponentZeroEulerGaugeUnit] using! hprod

/-- The infinite Euler-ratio product is holomorphic on the positive half-plane. -/
theorem differentiableOn_exponentZeroEulerGaugeUnit
    (eta omega : PrimePhase Nat.Primes)
    (homega : IsExponentZeroEulerGauge natPrimeSize omega) :
    DifferentiableOn ℂ (exponentZeroEulerGaugeUnit eta omega) positiveHalfPlane := by
  exact (hasProdLocallyUniformlyOn_exponentZeroEulerGaugeFactor eta omega homega).differentiableOn
    (Filter.Eventually.of_forall fun F => by
      simpa [Finset.prod_fn] using DifferentiableOn.finsetProd
        (fun p (_ : p ∈ F) => differentiableOn_exponentZeroEulerGaugeFactor eta omega p))
    (isOpen_lt continuous_const Complex.continuous_re)

/-- At each point of the positive half-plane the local perturbations are absolutely summable. -/
theorem summable_norm_exponentZeroEulerGaugeFactor_sub_one
    (eta omega : PrimePhase Nat.Primes)
    (homega : IsExponentZeroEulerGauge natPrimeSize omega)
    {s : ℂ} (hs : s ∈ positiveHalfPlane) :
    Summable (fun p : Nat.Primes =>
      ‖exponentZeroEulerGaugeFactor eta omega p s - 1‖) := by
  let u : Nat.Primes → ℝ := fun p =>
    (exponentZeroDenominatorGap s.re)⁻¹ *
      (exponentZeroWeight natPrimeSize ⟨s.re, hs⟩ p * ‖1 - (omega p : ℂ)‖)
  have hu : Summable u :=
    (homega ⟨s.re, hs⟩).mul_left (exponentZeroDenominatorGap s.re)⁻¹
  exact hu.of_nonneg_of_le (fun _ => norm_nonneg _) (fun p =>
    norm_exponentZeroEulerGaugeFactor_sub_one_le eta omega hs p hs le_rfl)

/-- The normally convergent Euler-ratio product is nowhere zero on the positive half-plane. -/
theorem exponentZeroEulerGaugeUnit_ne_zero
    (eta omega : PrimePhase Nat.Primes)
    (homega : IsExponentZeroEulerGauge natPrimeSize omega)
    {s : ℂ} (hs : s ∈ positiveHalfPlane) :
    exponentZeroEulerGaugeUnit eta omega s ≠ 0 := by
  rw [exponentZeroEulerGaugeUnit]
  simpa only [one_add_exponentZeroEulerGaugeFactor_sub_one] using
    tprod_one_add_ne_zero_of_summable
      (f := fun p : Nat.Primes => exponentZeroEulerGaugeFactor eta omega p s - 1)
      (fun p => by simpa only [one_add_exponentZeroEulerGaugeFactor_sub_one] using
        exponentZeroEulerGaugeFactor_ne_zero eta omega p hs)
      (summable_norm_exponentZeroEulerGaugeFactor_sub_one eta omega homega hs)

end

end GaloisForLFunctions.HTGeometry
