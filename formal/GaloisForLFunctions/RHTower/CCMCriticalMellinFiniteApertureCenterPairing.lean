import GaloisForLFunctions.RHTower.CCMCriticalMellinGrowingCumulativeBound
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# The coupled finite-aperture Poisson-center pairing

This module applies the elementary Chebyshev mass bound to the actual clipped complex center
pairing.  A radial half-density envelope gives a linear-in-aperture estimate.  The improper tail
is proved genuinely integrable; no convention for nonintegrable Bochner integrals is used.
-/

open Real MeasureTheory Set

noncomputable section

namespace RHTower

/-- The actual complex center pairing with the growing cumulative clipped at height `H`. -/
def criticalMellinFiniteApertureCenterPairing (R : ℝ → ℂ) (H : ℝ) : ℂ :=
  (∫ t in 0..H,
      ((Real.exp (-t / 2) * criticalMellinGrowingCumulativeAtHeight t : ℝ) : ℂ) * R t) +
    (criticalMellinGrowingCumulativeAtHeight H : ℂ) *
      ∫ t in Set.Ioi H, ((Real.exp (-t / 2) : ℝ) : ℂ) * R t

private lemma halfDensity_sq (t : ℝ) :
    Real.exp (-t / 2) * Real.exp (-t / 2) = Real.exp (-t) := by
  rw [← Real.exp_add]
  congr 1
  ring

/-- The active finite interval is bounded by the scalar growing-cumulative mass. -/
theorem norm_criticalMellinCenterActive_le
    {R : ℝ → ℂ} {H B : ℝ} (hH : 0 ≤ H)
    (hR : ∀ t : ℝ, 0 ≤ t → ‖R t‖ ≤ B * Real.exp (-t / 2)) :
    ‖∫ t in 0..H,
        ((Real.exp (-t / 2) * criticalMellinGrowingCumulativeAtHeight t : ℝ) : ℂ) * R t‖ ≤
      B * ∫ t in 0..H,
        Real.exp (-t) * |criticalMellinGrowingCumulativeAtHeight t| := by
  let w : ℝ → ℝ := fun t => Real.exp (-t) *
    |criticalMellinGrowingCumulativeAtHeight t|
  have hwInt : IntervalIntegrable w (volume : Measure ℝ) 0 H := by
    simpa only [w] using
      intervalIntegrable_exp_neg_mul_abs_criticalMellinGrowingCumulativeAtHeight hH
  have hbound := intervalIntegral.norm_integral_le_of_norm_le hH (g := fun t => B * w t)
    (f := fun t => ((Real.exp (-t / 2) *
      criticalMellinGrowingCumulativeAtHeight t : ℝ) : ℂ) * R t) (by
      filter_upwards with t
      intro ht
      have ht0 : 0 ≤ t := ht.1.le
      have hRt := hR t ht0
      have hphase0 : 0 ≤ Real.exp (-t / 2) := (Real.exp_pos _).le
      calc
        ‖((Real.exp (-t / 2) * criticalMellinGrowingCumulativeAtHeight t : ℝ) : ℂ) *
            R t‖ = Real.exp (-t / 2) *
              |criticalMellinGrowingCumulativeAtHeight t| * ‖R t‖ := by
                rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
                  abs_mul, abs_of_nonneg hphase0]
        _ ≤ Real.exp (-t / 2) * |criticalMellinGrowingCumulativeAtHeight t| *
            (B * Real.exp (-t / 2)) := by gcongr
        _ = B * w t := by
          dsimp only [w]
          rw [← halfDensity_sq t]
          ring)
    (hwInt.const_mul B)
  simpa only [intervalIntegral.integral_const_mul, w] using hbound

/-- The center tail is genuinely integrable under the half-density envelope. -/
theorem integrableOn_criticalMellinCenterTail
    {R : ℝ → ℂ} {H B : ℝ} (hH : 0 ≤ H)
    (hRcont : Continuous R)
    (hR : ∀ t : ℝ, 0 ≤ t → ‖R t‖ ≤ B * Real.exp (-t / 2)) :
    IntegrableOn (fun t : ℝ => ((Real.exp (-t / 2) : ℝ) : ℂ) * R t) (Set.Ioi H) := by
  let tailF : ℝ → ℂ := fun t => ((Real.exp (-t / 2) : ℝ) : ℂ) * R t
  have hmajor : IntegrableOn (fun t : ℝ => B * Real.exp (-t)) (Set.Ioi H) :=
    (integrableOn_exp_neg_Ioi H).const_mul B
  have hpoint : ∀ᵐ t ∂volume.restrict (Set.Ioi H), ‖tailF t‖ ≤ B * Real.exp (-t) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 ≤ t := hH.trans ht.le
    have hphase0 : 0 ≤ Real.exp (-t / 2) := (Real.exp_pos _).le
    calc
      ‖tailF t‖ = Real.exp (-t / 2) * ‖R t‖ := by
        change ‖((Real.exp (-t / 2) : ℝ) : ℂ) * R t‖ = _
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hphase0]
      _ ≤ Real.exp (-t / 2) * (B * Real.exp (-t / 2)) := by gcongr
      _ = B * Real.exp (-t) := by rw [← halfDensity_sq t]; ring
  have hphaseCont : Continuous (fun t : ℝ => ((Real.exp (-t / 2) : ℝ) : ℂ)) := by
    fun_prop
  have htailCont : Continuous tailF := by
    change Continuous (fun t : ℝ => ((Real.exp (-t / 2) : ℝ) : ℂ) * R t)
    exact hphaseCont.mul hRcont
  exact hmajor.mono' htailCont.aestronglyMeasurable.restrict hpoint

/-- Exact improper-tail norm bound. -/
theorem norm_integral_criticalMellinCenterTail_le
    {R : ℝ → ℂ} {H B : ℝ} (hH : 0 ≤ H)
    (hRcont : Continuous R)
    (hR : ∀ t : ℝ, 0 ≤ t → ‖R t‖ ≤ B * Real.exp (-t / 2)) :
    ‖∫ t in Set.Ioi H, ((Real.exp (-t / 2) : ℝ) : ℂ) * R t‖ ≤
      B * Real.exp (-H) := by
  let tailF : ℝ → ℂ := fun t => ((Real.exp (-t / 2) : ℝ) : ℂ) * R t
  have htailInt : Integrable tailF (volume.restrict (Set.Ioi H)) :=
    integrableOn_criticalMellinCenterTail hH hRcont hR
  have hmajor : IntegrableOn (fun t : ℝ => B * Real.exp (-t)) (Set.Ioi H) :=
    (integrableOn_exp_neg_Ioi H).const_mul B
  have hpoint : ∀ᵐ t ∂volume.restrict (Set.Ioi H), ‖tailF t‖ ≤ B * Real.exp (-t) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 ≤ t := hH.trans ht.le
    have hphase0 : 0 ≤ Real.exp (-t / 2) := (Real.exp_pos _).le
    calc
      ‖tailF t‖ = Real.exp (-t / 2) * ‖R t‖ := by
        change ‖((Real.exp (-t / 2) : ℝ) : ℂ) * R t‖ = _
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hphase0]
      _ ≤ Real.exp (-t / 2) * (B * Real.exp (-t / 2)) := by gcongr
      _ = B * Real.exp (-t) := by rw [← halfDensity_sq t]; ring
  change ‖∫ t, tailF t ∂volume.restrict (Set.Ioi H)‖ ≤ _
  calc
    ‖∫ t, tailF t ∂volume.restrict (Set.Ioi H)‖ ≤
        ∫ t, ‖tailF t‖ ∂volume.restrict (Set.Ioi H) :=
      MeasureTheory.norm_integral_le_integral_norm tailF
    _ ≤ ∫ t, B * Real.exp (-t) ∂volume.restrict (Set.Ioi H) :=
      MeasureTheory.integral_mono_ae htailInt.norm hmajor hpoint
    _ = B * Real.exp (-H) := by
      rw [MeasureTheory.integral_const_mul, integral_exp_neg_Ioi]

/-- **Coupled finite-aperture center theorem.**  Any continuous radial factor with the natural
half-density envelope pays at most the explicit linear Chebyshev mass. -/
theorem norm_criticalMellinFiniteApertureCenterPairing_le
    {R : ℝ → ℂ} {H B : ℝ} (hH : 0 ≤ H) (hB : 0 ≤ B)
    (hRcont : Continuous R)
    (hR : ∀ t : ℝ, 0 ≤ t → ‖R t‖ ≤ B * Real.exp (-t / 2)) :
    ‖criticalMellinFiniteApertureCenterPairing R H‖ ≤
      B * (Real.log 4 + 7) * (H + 1) := by
  let J : ℝ → ℝ := criticalMellinGrowingCumulativeAtHeight
  have hactive := norm_criticalMellinCenterActive_le hH hR
  have htailIntegral := norm_integral_criticalMellinCenterTail_le hH hRcont hR
  have htail :
      ‖(J H : ℂ) * ∫ t in Set.Ioi H, ((Real.exp (-t / 2) : ℝ) : ℂ) * R t‖ ≤
        B * (Real.exp (-H) * |J H|) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc
      |J H| * ‖∫ t in Set.Ioi H, ((Real.exp (-t / 2) : ℝ) : ℂ) * R t‖ ≤
          |J H| * (B * Real.exp (-H)) :=
        mul_le_mul_of_nonneg_left htailIntegral (abs_nonneg _)
      _ = B * (Real.exp (-H) * |J H|) := by ring
  rw [criticalMellinFiniteApertureCenterPairing]
  change ‖(∫ t in 0..H, ((Real.exp (-t / 2) * J t : ℝ) : ℂ) * R t) +
      (J H : ℂ) * ∫ t in Set.Ioi H, ((Real.exp (-t / 2) : ℝ) : ℂ) * R t‖ ≤ _
  calc
    ‖(∫ t in 0..H, ((Real.exp (-t / 2) * J t : ℝ) : ℂ) * R t) +
        (J H : ℂ) * ∫ t in Set.Ioi H, ((Real.exp (-t / 2) : ℝ) : ℂ) * R t‖ ≤
      ‖∫ t in 0..H, ((Real.exp (-t / 2) * J t : ℝ) : ℂ) * R t‖ +
        ‖(J H : ℂ) * ∫ t in Set.Ioi H, ((Real.exp (-t / 2) : ℝ) : ℂ) * R t‖ :=
      norm_add_le _ _
    _ ≤ B * (∫ t in 0..H, Real.exp (-t) * |J t|) +
        B * (Real.exp (-H) * |J H|) := add_le_add hactive htail
    _ = B * criticalMellinFiniteApertureCenterMass H := by
      rw [criticalMellinFiniteApertureCenterMass]
      dsimp only [J]
      ring
    _ ≤ B * ((Real.log 4 + 7) * (H + 1)) :=
      mul_le_mul_of_nonneg_left (criticalMellinFiniteApertureCenterMass_le hH) hB
    _ = B * (Real.log 4 + 7) * (H + 1) := by ring

end RHTower
