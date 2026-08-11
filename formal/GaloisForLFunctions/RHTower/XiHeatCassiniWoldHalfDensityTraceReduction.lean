import GaloisForLFunctions.RHTower.XiHeatCassiniHalfDensityWoldCoframe
import GaloisForLFunctions.RHTower.XiMassPrimePowerVerticalIdeal

/-!
# Trace-class reduction of Route T to a pure Wold half-density current

The half-density harmonic coefficient is `log(p)/p`, whereas the depth-one Wold coefficient is
`(1-1/p)^3 log(p)/p`.  Their difference gains one prime power.  After restoring the physical
`sqrt(p)` half-density, the correction is bounded by `3 log(p)/p^(3/2)` and is therefore absolutely
summable against the vertically uniform mass Fourier bound.

Consequently the complete Route-T valuation-one layer is a pure Wold half-density current plus a
uniformly bounded trace-class correction.  Uniform boundedness of the pure current is exactly RH.
-/

open Complex Filter MeasureTheory Set Topology
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Mass Fourier profile at a prime logarithmic frequency. -/
def xiHeatCassiniPrimeMassFourierProfile (a : ℝ) (τ : ℂ)
    (p : Nat.Primes) : ℂ :=
  stripFourier (xiMassAnalyticTest a τ) (Real.log (p : ℝ) : ℂ)

/-- Pure depth-one Wold source atom with the critical half-density restored in the test profile. -/
def xiHeatCassiniPureWoldHalfDensityAtom (a : ℝ) (τ : ℂ)
    (p : Nat.Primes) : ℂ :=
  ((Real.sqrt (p : ℝ) * woldCoeff 1 p : ℝ) : ℂ) *
    xiHeatCassiniPrimeMassFourierProfile a τ p

/-- Raw scalar left after replacing the critical prime coefficient by the restored Wold
half-density coefficient. -/
def xiHeatCassiniWoldHalfDensityTraceCorrectionCoefficient
    (p : Nat.Primes) : ℝ :=
  xiMassValuationOneCriticalCoefficient p -
    Real.sqrt (p : ℝ) * woldCoeff 1 p

/-- Trace correction atom paired with the un-gauged mass Fourier profile. -/
def xiHeatCassiniWoldHalfDensityTraceCorrectionAtom
    (a : ℝ) (τ : ℂ) (p : Nat.Primes) : ℂ :=
  (xiHeatCassiniWoldHalfDensityTraceCorrectionCoefficient p : ℂ) *
    xiHeatCassiniPrimeMassFourierProfile a τ p

/-- Restoring half-density turns the harmonic--Wold trace correction into the raw critical
coefficient correction. -/
theorem xiHeatCassiniWoldHalfDensityTraceCorrectionCoefficient_eq
    (p : Nat.Primes) :
    xiHeatCassiniWoldHalfDensityTraceCorrectionCoefficient p =
      Real.sqrt (p : ℝ) * xiHeatCassiniWoldEulerTraceCorrection p := by
  have hp : 0 < (p : ℝ) := by exact_mod_cast p.2.pos
  have hs : 0 < Real.sqrt (p : ℝ) := Real.sqrt_pos.mpr hp
  have hcritical :
      Real.sqrt (p : ℝ) * xiMassPrimeHarmonicRealCoefficient p =
        xiMassValuationOneCriticalCoefficient p := by
    rw [xiMassPrimeHarmonicRealCoefficient,
      xiMassValuationOneCriticalCoefficient]
    field_simp [hs.ne', hp.ne']
    rw [Real.sq_sqrt hp.le]
    ring
  rw [xiHeatCassiniWoldHalfDensityTraceCorrectionCoefficient,
    xiHeatCassiniWoldEulerTraceCorrection]
  rw [← hcritical]
  ring

/-- Restored trace correction is nonnegative. -/
theorem xiHeatCassiniWoldHalfDensityTraceCorrectionCoefficient_nonneg
    (p : Nat.Primes) :
    0 ≤ xiHeatCassiniWoldHalfDensityTraceCorrectionCoefficient p := by
  rw [xiHeatCassiniWoldHalfDensityTraceCorrectionCoefficient_eq]
  exact mul_nonneg (Real.sqrt_nonneg _)
    (xiHeatCassiniWoldEulerTraceCorrection_nonneg p)

/-- The restored correction is dominated by a prime-square Euler weight at quarter depth. -/
theorem xiHeatCassiniWoldHalfDensityTraceCorrectionCoefficient_le
    (p : Nat.Primes) :
    xiHeatCassiniWoldHalfDensityTraceCorrectionCoefficient p ≤
      3 * xiMassPrimeSquareEulerWeight (1 / 4) p := by
  have hp : 0 < (p : ℝ) := by exact_mod_cast p.2.pos
  have hs : 0 < Real.sqrt (p : ℝ) := Real.sqrt_pos.mpr hp
  rw [xiHeatCassiniWoldHalfDensityTraceCorrectionCoefficient_eq]
  calc
    Real.sqrt (p : ℝ) * xiHeatCassiniWoldEulerTraceCorrection p ≤
        Real.sqrt (p : ℝ) *
          (3 * (Real.log (p : ℝ) / (p : ℝ) ^ 2)) :=
      mul_le_mul_of_nonneg_left
        (xiHeatCassiniWoldEulerTraceCorrection_le p) (Real.sqrt_nonneg _)
    _ = 3 * xiMassPrimeSquareEulerWeight (1 / 4) p := by
      rw [xiMassPrimeSquareEulerWeight_eq]
      norm_num
      have hrpow : (p : ℝ) ^ (-(3 / 2 : ℝ)) =
          1 / ((p : ℝ) * Real.sqrt (p : ℝ)) := by
        rw [Real.rpow_neg hp.le,
          show (3 / 2 : ℝ) = 1 + 1 / 2 by ring,
          Real.rpow_add hp, Real.rpow_one, ← Real.sqrt_eq_rpow]
        simp only [one_div]
      rw [hrpow]
      field_simp [hp.ne', hs.ne']
      rw [Real.sq_sqrt hp.le]
      ring

/-- One actual valuation-one Route-T atom is pure Wold half-density plus trace correction. -/
theorem xiMassCenteredPrimeAtom_eq_pureWoldHalfDensity_add_traceCorrection
    (a : ℝ) (τ : ℂ) (p : Nat.Primes) :
    xiMassCenteredPrimeAtom a τ (p : ℕ) =
      xiHeatCassiniPureWoldHalfDensityAtom a τ p +
        xiHeatCassiniWoldHalfDensityTraceCorrectionAtom a τ p := by
  rw [xiMassCenteredPrimeAtom,
    ← criticalMellinAtomWeight_cast_eq_lSeriesTerm_half p.2.ne_zero,
    criticalMellinAtomWeight_prime_eq_xiMassValuationOneCriticalCoefficient]
  unfold xiHeatCassiniPureWoldHalfDensityAtom
    xiHeatCassiniWoldHalfDensityTraceCorrectionAtom
    xiHeatCassiniWoldHalfDensityTraceCorrectionCoefficient
    xiHeatCassiniPrimeMassFourierProfile
  push_cast
  ring

/-- Vertical mass Fourier profile has a prime-uniform and time-uniform bound. -/
theorem norm_xiHeatCassiniPrimeMassFourierProfile_vertical_le
    {a σ : ℝ} (ha : 0 < a) (hσ : 0 < σ) (u : ℝ) (p : Nat.Primes) :
    ‖xiHeatCassiniPrimeMassFourierProfile a ((σ : ℂ) + u * I) p‖ ≤
      ∫ x : ℝ, Real.exp (-σ * |x|) := by
  simpa only [xiHeatCassiniPrimeMassFourierProfile, neg_mul] using
    norm_stripFourier_xiMassAnalyticTest_vertical_le ha hσ u
      (Real.log (p : ℝ))

/-- Pointwise uniform trace-correction majorant. -/
theorem norm_xiHeatCassiniWoldHalfDensityTraceCorrectionAtom_vertical_le
    {a σ : ℝ} (ha : 0 < a) (hσ : 0 < σ) (u : ℝ) (p : Nat.Primes) :
    ‖xiHeatCassiniWoldHalfDensityTraceCorrectionAtom
        a ((σ : ℂ) + u * I) p‖ ≤
      3 * xiMassPrimeSquareEulerWeight (1 / 4) p *
        (∫ x : ℝ, Real.exp (-σ * |x|)) := by
  let J : ℝ := ∫ x : ℝ, Real.exp (-σ * |x|)
  have hJ : 0 ≤ J := integral_nonneg fun _ => Real.exp_nonneg _
  have hmajorCoefficient :
      0 ≤ 3 * xiMassPrimeSquareEulerWeight (1 / 4) p := by
    rw [xiMassPrimeSquareEulerWeight_eq]
    positivity
  rw [xiHeatCassiniWoldHalfDensityTraceCorrectionAtom, norm_mul,
    Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg
      (xiHeatCassiniWoldHalfDensityTraceCorrectionCoefficient_nonneg p)]
  exact mul_le_mul
    (xiHeatCassiniWoldHalfDensityTraceCorrectionCoefficient_le p)
    (by simpa only [J] using
      norm_xiHeatCassiniPrimeMassFourierProfile_vertical_le ha hσ u p)
    (norm_nonneg _) hmajorCoefficient

/-- Trace correction atoms are absolutely summable. -/
theorem summable_norm_xiHeatCassiniWoldHalfDensityTraceCorrectionAtom
    {a σ : ℝ} (ha : 0 < a) (hσ : 0 < σ) (u : ℝ) :
    Summable (fun p : Nat.Primes =>
      ‖xiHeatCassiniWoldHalfDensityTraceCorrectionAtom
        a ((σ : ℂ) + u * I) p‖) := by
  let J : ℝ := ∫ x : ℝ, Real.exp (-σ * |x|)
  have hmajor : Summable (fun p : Nat.Primes =>
      3 * xiMassPrimeSquareEulerWeight (1 / 4) p * J) :=
    ((summable_xiMassPrimeSquareEulerWeight (by norm_num)).mul_left 3).mul_right J
  exact hmajor.of_nonneg_of_le (fun _ => norm_nonneg _) fun p => by
    simpa only [J] using
      norm_xiHeatCassiniWoldHalfDensityTraceCorrectionAtom_vertical_le ha hσ u p

/-- Complete uniformly bounded trace correction. -/
def xiHeatCassiniWoldHalfDensityTraceCorrectionLayer
    (a : ℝ) (τ : ℂ) : ℂ :=
  ∑' p : Nat.Primes, xiHeatCassiniWoldHalfDensityTraceCorrectionAtom a τ p

/-- Complete pure Wold half-density Route-T current. -/
def xiHeatCassiniPureWoldHalfDensityLayer (a : ℝ) (τ : ℂ) : ℂ :=
  ∑' p : Nat.Primes, xiHeatCassiniPureWoldHalfDensityAtom a τ p

/-- Trace correction has a uniform vertical-line norm bound. -/
theorem norm_xiHeatCassiniWoldHalfDensityTraceCorrectionLayer_vertical_le
    {a σ : ℝ} (ha : 0 < a) (hσ : 0 < σ) (u : ℝ) :
    ‖xiHeatCassiniWoldHalfDensityTraceCorrectionLayer
        a ((σ : ℂ) + u * I)‖ ≤
      3 * (∑' p : Nat.Primes, xiMassPrimeSquareEulerWeight (1 / 4) p) *
        (∫ x : ℝ, Real.exp (-σ * |x|)) := by
  let J : ℝ := ∫ x : ℝ, Real.exp (-σ * |x|)
  let f : Nat.Primes → ℂ := fun p =>
    xiHeatCassiniWoldHalfDensityTraceCorrectionAtom a ((σ : ℂ) + u * I) p
  have hnorm : Summable (fun p => ‖f p‖) := by
    simpa only [f] using
      summable_norm_xiHeatCassiniWoldHalfDensityTraceCorrectionAtom ha hσ u
  have hmajor : Summable (fun p : Nat.Primes =>
      3 * xiMassPrimeSquareEulerWeight (1 / 4) p * J) :=
    ((summable_xiMassPrimeSquareEulerWeight (by norm_num)).mul_left 3).mul_right J
  calc
    ‖xiHeatCassiniWoldHalfDensityTraceCorrectionLayer
        a ((σ : ℂ) + u * I)‖ ≤ ∑' p : Nat.Primes, ‖f p‖ := by
      exact norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' p : Nat.Primes,
        3 * xiMassPrimeSquareEulerWeight (1 / 4) p * J := by
      exact hnorm.tsum_le_tsum (fun p => by
        simpa only [f, J] using
          norm_xiHeatCassiniWoldHalfDensityTraceCorrectionAtom_vertical_le
            ha hσ u p) hmajor
    _ = 3 * (∑' p : Nat.Primes,
        xiMassPrimeSquareEulerWeight (1 / 4) p) *
          (∫ x : ℝ, Real.exp (-σ * |x|)) := by
      rw [← tsum_mul_left, tsum_mul_right]

/-- Pure Wold half-density atoms are summable in every legal Route-T half-plane. -/
theorem summable_xiHeatCassiniPureWoldHalfDensityAtom
    {a d : ℝ} (hhalf : 1 / 2 < d) (hda : d < a)
    {τ : ℂ} (hτ : 0 < τ.re) :
    Summable (xiHeatCassiniPureWoldHalfDensityAtom a τ) := by
  have hsource := summable_xiMassValuationOnePrimeAtom hhalf hda hτ
  have ha : 0 < a := by linarith
  have hcorrection : Summable
      (xiHeatCassiniWoldHalfDensityTraceCorrectionAtom a τ) := by
    let σ : ℝ := τ.re
    let u : ℝ := τ.im
    have hτform : ((σ : ℂ) + u * I) = τ := by
      apply Complex.ext <;> simp [σ, u]
    rw [← hτform]
    exact summable_norm_iff.mp
      (summable_norm_xiHeatCassiniWoldHalfDensityTraceCorrectionAtom
        ha hτ u)
  exact (hsource.sub hcorrection).congr fun p => by
    rw [xiMassCenteredPrimeAtom_eq_pureWoldHalfDensity_add_traceCorrection]
    ring

/-- Exact global source decomposition. -/
theorem xiMassValuationOnePrimeLayer_eq_pureWoldHalfDensity_add_traceCorrection
    {a d : ℝ} (hhalf : 1 / 2 < d) (hda : d < a)
    {τ : ℂ} (hτ : 0 < τ.re) :
    xiMassValuationOnePrimeLayer a τ =
      xiHeatCassiniPureWoldHalfDensityLayer a τ +
        xiHeatCassiniWoldHalfDensityTraceCorrectionLayer a τ := by
  have hpure := summable_xiHeatCassiniPureWoldHalfDensityAtom hhalf hda hτ
  have ha : 0 < a := by linarith
  have hcorrection : Summable
      (xiHeatCassiniWoldHalfDensityTraceCorrectionAtom a τ) := by
    let σ : ℝ := τ.re
    let u : ℝ := τ.im
    have hτform : ((σ : ℂ) + u * I) = τ := by
      apply Complex.ext <;> simp [σ, u]
    rw [← hτform]
    exact summable_norm_iff.mp
      (summable_norm_xiHeatCassiniWoldHalfDensityTraceCorrectionAtom
        ha hτ u)
  rw [xiMassValuationOnePrimeLayer,
    xiHeatCassiniPureWoldHalfDensityLayer,
    xiHeatCassiniWoldHalfDensityTraceCorrectionLayer,
    ← hpure.tsum_add hcorrection]
  exact tsum_congr fun p =>
    xiMassCenteredPrimeAtom_eq_pureWoldHalfDensity_add_traceCorrection a τ p

/-- Uniform line-bound proposition for the reduced pure Wold producer. -/
def XiHeatCassiniPureWoldHalfDensityLineBound (a σ : ℝ) : Prop :=
  ∃ C : ℝ, ∀ u : ℝ,
    ‖xiHeatCassiniPureWoldHalfDensityLayer a ((σ : ℂ) + u * I)‖ ≤ C

/-- Removing the positive trace correction preserves the complete Route-T line-bound problem. -/
theorem xiMassValuationOnePrimeLineBound_iff_pureWoldHalfDensityLineBound
    {a d σ : ℝ} (hhalf : 1 / 2 < d) (hda : d < a) (hσ : 0 < σ) :
    XiMassValuationOnePrimeLineBound a σ ↔
      XiHeatCassiniPureWoldHalfDensityLineBound a σ := by
  let B : ℝ :=
    3 * (∑' p : Nat.Primes, xiMassPrimeSquareEulerWeight (1 / 4) p) *
      (∫ x : ℝ, Real.exp (-σ * |x|))
  have ha : 0 < a := by linarith
  have hB : ∀ u : ℝ,
      ‖xiHeatCassiniWoldHalfDensityTraceCorrectionLayer
        a ((σ : ℂ) + u * I)‖ ≤ B := fun u => by
    simpa only [B] using
      norm_xiHeatCassiniWoldHalfDensityTraceCorrectionLayer_vertical_le
        ha hσ u
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨C + B, fun u => ?_⟩
    have hdecomp :=
      xiMassValuationOnePrimeLayer_eq_pureWoldHalfDensity_add_traceCorrection
        hhalf hda (τ := ((σ : ℂ) + u * I)) (hτ := by simpa using hσ)
    have heq :
        xiHeatCassiniPureWoldHalfDensityLayer a ((σ : ℂ) + u * I) =
          xiMassValuationOnePrimeLayer a ((σ : ℂ) + u * I) -
            xiHeatCassiniWoldHalfDensityTraceCorrectionLayer
              a ((σ : ℂ) + u * I) := by
      rw [hdecomp]
      ring
    rw [heq]
    exact (norm_sub_le _ _).trans (add_le_add (hC u) (hB u))
  · rintro ⟨C, hC⟩
    refine ⟨C + B, fun u => ?_⟩
    rw [xiMassValuationOnePrimeLayer_eq_pureWoldHalfDensity_add_traceCorrection
      hhalf hda (τ := ((σ : ℂ) + u * I)) (hτ := by simpa using hσ)]
    exact (norm_add_le _ _).trans (add_le_add (hC u) (hB u))

/-- **Reduced Route-T producer.**  RH is exactly uniform boundedness of the pure depth-one Wold
coefficient paired with the physical mass half-density profile. -/
theorem riemannHypothesis_iff_xiHeatCassiniPureWoldHalfDensityLineBound
    {a d σ : ℝ} (hhalf : 1 / 2 < d) (hda : d < a) (hσ : 0 < σ) :
    RiemannHypothesis ↔ XiHeatCassiniPureWoldHalfDensityLineBound a σ := by
  exact (riemannHypothesis_iff_xiMassValuationOnePrimeLineBound
    hhalf hda hσ).trans
      (xiMassValuationOnePrimeLineBound_iff_pureWoldHalfDensityLineBound
        hhalf hda hσ)

end

end RHTower
