import GaloisForLFunctions.RHTower.CriticalHalfDensityPrimeTailResolventLaw
import GaloisForLFunctions.RHTower.DeningerCriticalFloquetCrossCurrent
import GaloisForLFunctions.RHTower.XiMassCriticalErrorFlux

/-!
# The Xi-mass cross profile paired with the critical half-density Weil source

The critical half-density prime-tail forcing already present in the corpus has position moment

`Σ Λ(n) n⁻¹ᐟ² δ_(log n)`.

This module proves that the complete Xi-mass cross profile is integrable against that locally
finite measure for every fixed vertical height, identifies the Bochner integral with its exact
von-Mangoldt series, and records the source pairing without a finite cutoff.  The proof uses a
strict interior strip shift `1/2 < d < a`; no RH premise or numerical computation occurs.
-/

open Complex Real MeasureTheory
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-- One atom of the complete critical half-density mass cross current. -/
def xiMassCriticalHalfDensityCrossAtom
    (a sigma u : ℝ) (n : DeningerPrimePowerIndex) : ℂ :=
  (criticalMellinAtomWeight (n : ℕ) : ℂ) *
    xiMassSpectralCrossProfile a sigma u (deningerPrimePowerTime n)

/-- Every fixed-height complete critical cross current is absolutely summable. -/
theorem summable_norm_xiMassCriticalHalfDensityCrossAtom
    {a sigma : ℝ} (ha : 1 / 2 < a) (hsigma : 0 < sigma) (u : ℝ) :
    Summable (fun n : DeningerPrimePowerIndex =>
      ‖xiMassCriticalHalfDensityCrossAtom a sigma u n‖) := by
  let d : ℝ := (a + 1 / 2) / 2
  let p : ℝ := 1 / 2 + d
  let K : ℝ := Real.exp (|u| * d) *
    ∫ x : ℝ, Real.exp (-(sigma * |x|))
  have hd0 : 0 ≤ d := by dsimp only [d]; linarith
  have hdhalf : 1 / 2 < d := by dsimp only [d]; linarith
  have hda : d < a := by dsimp only [d]; linarith
  have hp : 1 < p := by dsimp only [p]; linarith
  have hJ : 0 ≤ ∫ x : ℝ, Real.exp (-(sigma * |x|)) :=
    integral_nonneg fun _ => Real.exp_nonneg _
  have hK : 0 ≤ K := mul_nonneg (Real.exp_nonneg _) hJ
  have hbaseNat : Summable (fun n : ℕ =>
      ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-p)) :=
    summable_vonMangoldt_mul_rpow hp
  have hbase : Summable (fun n : DeningerPrimePowerIndex =>
      K * (ArithmeticFunction.vonMangoldt (n : ℕ) *
        ((n : ℕ) : ℝ) ^ (-p))) :=
    (hbaseNat.subtype {n : ℕ | 2 ≤ n}).mul_left K
  apply Summable.of_nonneg_of_le (f := fun n : DeningerPrimePowerIndex =>
    K * (ArithmeticFunction.vonMangoldt (n : ℕ) *
      ((n : ℕ) : ℝ) ^ (-p))) (fun _ => norm_nonneg _) _ hbase
  intro n
  have hnPos : (0 : ℝ) < (n : ℕ) := by
    exact_mod_cast lt_of_lt_of_le Nat.zero_lt_two n.property
  have hlog : deningerPrimePowerTime n = Real.log (n : ℕ) := rfl
  have hF := norm_stripFourier_xiMass_deepShift_le
    (a := a) (σ := sigma) (d := d) hd0 hda hsigma u
      (deningerPrimePowerTime n)
  have hF' :
      ‖xiMassSpectralCrossProfile a sigma u (deningerPrimePowerTime n)‖ ≤
        Real.exp (|u| * d - deningerPrimePowerTime n * d) *
          ∫ x : ℝ, Real.exp (-(sigma * |x|)) := by
    rw [xiMassSpectralCrossProfile_eq_stripFourier]
    exact hF
  have hexp :
      Real.exp (|u| * d - deningerPrimePowerTime n * d) =
        Real.exp (|u| * d) * ((n : ℕ) : ℝ) ^ (-d) := by
    rw [hlog, Real.rpow_def_of_pos hnPos, ← Real.exp_add]
    apply congrArg Real.exp
    ring_nf
  rw [hexp] at hF'
  have hweight :
      criticalMellinAtomWeight (n : ℕ) =
        ArithmeticFunction.vonMangoldt (n : ℕ) * ((n : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) := by
    rw [criticalMellinAtomWeight]
    ring_nf
  rw [xiMassCriticalHalfDensityCrossAtom, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, hweight,
    abs_of_nonneg (mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
      (Real.rpow_nonneg hnPos.le _))]
  have hpowHalf : 0 ≤ ((n : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) :=
    Real.rpow_nonneg hnPos.le _
  have hLambda : 0 ≤ ArithmeticFunction.vonMangoldt (n : ℕ) :=
    ArithmeticFunction.vonMangoldt_nonneg
  have hmul := mul_le_mul_of_nonneg_left hF'
    (mul_nonneg hLambda hpowHalf)
  calc
    ArithmeticFunction.vonMangoldt (n : ℕ) * ((n : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) *
        ‖xiMassSpectralCrossProfile a sigma u (deningerPrimePowerTime n)‖ ≤
      ArithmeticFunction.vonMangoldt (n : ℕ) * ((n : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) *
        (Real.exp (|u| * d) * ((n : ℕ) : ℝ) ^ (-d) *
          ∫ x : ℝ, Real.exp (-(sigma * |x|))) := hmul
    _ = K * (ArithmeticFunction.vonMangoldt (n : ℕ) *
        ((n : ℕ) : ℝ) ^ (-p)) := by
      calc
        ArithmeticFunction.vonMangoldt (n : ℕ) *
            ((n : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) *
              (Real.exp (|u| * d) * ((n : ℕ) : ℝ) ^ (-d) *
                ∫ x : ℝ, Real.exp (-(sigma * |x|))) =
            K * (ArithmeticFunction.vonMangoldt (n : ℕ) *
              (((n : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) *
                ((n : ℕ) : ℝ) ^ (-d))) := by
          dsimp only [K]
          ring_nf
        _ = K * (ArithmeticFunction.vonMangoldt (n : ℕ) *
            ((n : ℕ) : ℝ) ^ (-(1 / 2 : ℝ) + -d)) := by
          rw [Real.rpow_add hnPos]
        _ = K * (ArithmeticFunction.vonMangoldt (n : ℕ) *
            ((n : ℕ) : ℝ) ^ (-p)) := by
          have he : -(1 / 2 : ℝ) + -d = -p := by
            dsimp only [p]
            ring_nf
          rw [he]

/-- Complete positive-time critical half-density mass cross series. -/
def xiMassCriticalHalfDensityCrossSeries (a sigma u : ℝ) : ℂ :=
  ∑' n : DeningerPrimePowerIndex,
    xiMassCriticalHalfDensityCrossAtom a sigma u n

/-- The mass cross profile is Bochner-integrable against the critical half-density Weil measure. -/
theorem integrable_xiMassSpectralCrossProfile_criticalHalfDensityWeilPrimeMeasure
    {a sigma : ℝ} (ha : 1 / 2 < a) (hsigma : 0 < sigma) (u : ℝ) :
    Integrable (xiMassSpectralCrossProfile a sigma u)
      criticalHalfDensityWeilPrimeMeasure := by
  rw [criticalHalfDensityWeilPrimeMeasure, labelledMeasure]
  apply integrable_sum_measure
  · intro n
    let q : ENNReal := ENNReal.ofReal (criticalMellinAtomWeight (n : ℕ))
    change Integrable (xiMassSpectralCrossProfile a sigma u)
      (q • Measure.dirac (deningerPrimePowerTime n))
    by_cases hq : q = 0
    · rw [hq, zero_smul]
      exact integrable_zero_measure
    · apply (integrable_smul_measure hq ENNReal.ofReal_ne_top).2
      exact integrable_dirac (by simp)
  · have hsum := summable_norm_xiMassCriticalHalfDensityCrossAtom ha hsigma u
    apply hsum.congr
    intro n
    rw [integral_smul_measure, integral_dirac]
    simp only [ENNReal.toReal_ofReal (criticalMellinAtomWeight_nonneg (n : ℕ)),
      xiMassCriticalHalfDensityCrossAtom, norm_mul, Complex.norm_real,
      Real.norm_eq_abs,
      abs_of_nonneg (criticalMellinAtomWeight_nonneg (n : ℕ)), smul_eq_mul]

/-- Bochner pairing of the mass cross profile with the unsquared critical Weil source. -/
def xiMassCriticalHalfDensityWeilPairing (a sigma u : ℝ) : ℂ :=
  ∫ h : ℝ, xiMassSpectralCrossProfile a sigma u h
    ∂criticalHalfDensityWeilPrimeMeasure

/-- **C37 capstone.**  The measure pairing is exactly the absolutely convergent full
half-density von-Mangoldt cross series. -/
theorem xiMassCriticalHalfDensityWeilPairing_eq_crossSeries
    {a sigma : ℝ} (ha : 1 / 2 < a) (hsigma : 0 < sigma) (u : ℝ) :
    xiMassCriticalHalfDensityWeilPairing a sigma u =
      xiMassCriticalHalfDensityCrossSeries a sigma u := by
  rw [xiMassCriticalHalfDensityWeilPairing,
    criticalHalfDensityWeilPrimeMeasure,
    integral_labelledMeasure _ _ _
      (integrable_xiMassSpectralCrossProfile_criticalHalfDensityWeilPrimeMeasure
        ha hsigma u),
    xiMassCriticalHalfDensityCrossSeries]
  apply tsum_congr
  intro n
  rw [ENNReal.toReal_ofReal (criticalMellinAtomWeight_nonneg (n : ℕ))]
  rfl

end

end RHTower
