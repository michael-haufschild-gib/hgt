import GaloisForLFunctions.RHTower.XiWardSchwarzCapReflection
import GaloisForLFunctions.RHTower.XiWardSchwarzCapSourcePairing

/-!
# Real signed charge of the canonical Ward cap

The actual completed-source cap density is conjugate-even under height
reversal.  This converts the exact finite cap from a complex contour response
to a real signed charge.  It supplies no size estimate: the real local mass at
the moving Cauchy resonance is precisely the remaining analytic datum.
-/

open Complex MeasureTheory Set

namespace RHTower

noncomputable section

/-- Centered negative conjugation interchanges the two literal lower-cap
points at opposite heights. -/
theorem xiWardLowerCapPoint_neg (s x : ℝ) :
    xiWardLowerCapPoint s (-x) =
      xiCenteredNegConj (xiWardLowerCapPoint s x) := by
  unfold xiWardLowerCapPoint xiCenteredNegConj
  rw [map_sub, Complex.conj_ofReal, map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

/-- The literal reflected source pair is conjugate-even, before applying any
source identity or source-domain admissibility condition. -/
theorem xiWardSchwarzCapSourcePair_neg_height (tau s x : ℝ) :
    xiWardSchwarzCapSourcePair tau s (-x) =
      starRingEnd ℂ (xiWardSchwarzCapSourcePair tau s x) := by
  unfold xiWardSchwarzCapSourcePair
  dsimp
  rw [xiWardLowerCapPoint_neg]
  rw [xiCenteredNegConj_involutive, map_add, map_mul, starRingEnd_self_apply]
  ring

/-- On the conull canonical cap family, the factorized literal completed-source
density is conjugate-even. -/
theorem ae_forall_xiWardSchwarzCapFactorDensity_neg_height :
    ∀ᵐ s : ℝ ∂volume, ∀ tau x : ℝ,
      xiWardSchwarzCapDifference tau s (-x) *
          continuedPrimeArchSourceRelativeTrace (xiWardLowerCapPoint s (-x)) =
        starRingEnd ℂ
          (xiWardSchwarzCapDifference tau s x *
            continuedPrimeArchSourceRelativeTrace (xiWardLowerCapPoint s x)) := by
  filter_upwards [ae_forall_xiWardSchwarzCapSourcePair_eq] with s hs
  intro tau x
  rw [← hs tau (-x), ← hs tau x]
  exact xiWardSchwarzCapSourcePair_neg_height tau s x

/-- A conjugate-even complex density on a symmetric interval is twice the real
half-cap integral. -/
private theorem symmetric_intervalIntegral_eq_two_re
    (f : ℝ → ℂ) (H : ℝ)
    (hneg : IntervalIntegrable f volume (-H) 0)
    (hpos : IntervalIntegrable f volume 0 H)
    (hsym : ∀ x : ℝ, f (-x) = starRingEnd ℂ (f x)) :
    (∫ x in (-H)..H, f x) =
      (2 * (∫ x in 0..H, (f x).re) : ℝ) := by
  have hreflect : (∫ x in (-H)..0, f x) =
      starRingEnd ℂ (∫ x in 0..H, f x) := by
    calc
      (∫ x in (-H)..0, f x) = ∫ x in 0..H, f (-x) := by
        simpa only [neg_zero] using
          (intervalIntegral.integral_comp_neg f (a := 0) (b := H)).symm
      _ = ∫ x in 0..H, starRingEnd ℂ (f x) := by
        apply intervalIntegral.integral_congr
        intro x _
        exact hsym x
      _ = starRingEnd ℂ (∫ x in 0..H, f x) := by
        exact intervalIntegral.intervalIntegral_conj
  rw [← intervalIntegral.integral_add_adjacent_intervals hneg hpos, hreflect]
  apply Complex.ext
  · have hre := intervalIntegral.intervalIntegral_re hpos
    simpa [Complex.add_re, Complex.conj_re, two_mul] using
      congrArg (fun u : ℝ => 2 * u) hre.symm
  · simp [Complex.add_im, Complex.conj_im]

/-- On the conull canonical-cap family, each literal symmetric completed-source
cap is exactly twice the real signed charge on its positive half.  This is a
reduction of the all-height cancellation problem, not a uniform bound. -/
theorem ae_forall_xiWardSchwarzCapFactorIntegral_eq_two_re_half :
    ∀ᵐ s : ℝ ∂volume, ∀ tau H : ℝ,
      xiWardSchwarzCapFactorIntegral tau s H =
        (2 * (∫ x in 0..H,
          (xiWardSchwarzCapDifference tau s x *
            continuedPrimeArchSourceRelativeTrace (xiWardLowerCapPoint s x)).re) : ℝ) := by
  filter_upwards [ae_forall_intervalIntegrable_xiWardSchwarzCapFactor,
    ae_forall_xiWardSchwarzCapFactorDensity_neg_height] with s hint hsym
  intro tau H
  let f : ℝ → ℂ := fun x =>
    xiWardSchwarzCapDifference tau s x *
      continuedPrimeArchSourceRelativeTrace (xiWardLowerCapPoint s x)
  have hfull : IntervalIntegrable f volume (-H) H := hint tau H
  have hzero : (0 : ℝ) ∈ Set.uIcc (-H) H := by
    rcases le_total 0 H with hH | hH
    · exact Set.mem_uIcc_of_le (by linarith) hH
    · exact Set.mem_uIcc_of_ge hH (by linarith)
  have hneg : IntervalIntegrable f volume (-H) 0 := by
    apply hfull.mono_set
    exact Set.uIcc_subset_uIcc_left hzero
  have hpos : IntervalIntegrable f volume 0 H := by
    apply hfull.mono_set
    exact Set.uIcc_subset_uIcc_right hzero
  change (∫ x in (-H)..H, f x) = _
  apply symmetric_intervalIntegral_eq_two_re f H hneg hpos
  intro x
  exact hsym tau x

end

end RHTower
