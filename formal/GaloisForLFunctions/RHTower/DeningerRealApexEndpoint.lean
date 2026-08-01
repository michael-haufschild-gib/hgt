import GaloisForLFunctions.RHTower.DeningerRadialKahlerTrace
import GaloisForLFunctions.RHTower.DeningerStationaryKahlerGerm
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket

/-!
# The real orientation-twisted Hodge apex and its relative endpoint

The real-place leaf germ is the quotient of the complex leaf by complex conjugation.  The closed
upper half plane is a fundamental domain of that involution, so integration over the quotient is
integration over the half plane, and for a conjugation-invariant integrable function this is
exactly half the integral over the oriented double cover.  Applied to the radial lift of an even
Schwartz function, the leafwise Kähler trace of the quotient is `π/2` times the ray integral, hence
`π/4` times the Fourier transform at the origin; the nonzero scalar does not change the kernel, so
the two relative endpoint conditions downstairs are again apex restriction and vanishing trace.

Conjugation reverses leaf orientation, so the Hodge star cannot descend to the quotient as an
untwisted endomorphism: an invariant one-form whose star is again invariant is zero.  The star does
descend through the orientation sign local system, where it produces the odd operator `J = ⋆c` of
square `-1` with strictly positive Hodge density, and the half-density flow, acting by a real
scalar, commutes with `J`.

* `deningerRealChart_half` : the quotient integral is half the cover integral.
* `deningerRealApex_trace`, `deningerRealApex_trace_fourier` : the relative endpoint.
* `deningerRadialLift_integrable` : the radial lift of a Schwartz function is integrable.
* `deningerRealApexEndpoint_schwartz` : the two relative conditions on the quotient.
* `deningerRealTwist_forced` : the Hodge star does not descend untwisted.
* `deningerGermJ_flow_comm` : the half-density flow commutes with the odd Hodge operator.
-/

namespace RHTower

open MeasureTheory Set Real Module

section RealQuotient

/-- The closed upper half plane: a fundamental domain of the real involution of the leaf. -/
def deningerRealChart : Set ℂ := {z : ℂ | 0 ≤ z.im}

theorem deningerRealChart_measurableSet : MeasurableSet deningerRealChart :=
  measurableSet_le measurable_const Complex.measurable_im

/-- The real involution of the leaf is measure preserving, being a linear isometry. -/
theorem deningerConj_measurePreserving :
    MeasurePreserving (fun z : ℂ => (starRingEnd ℂ) z) volume volume :=
  Complex.conjLIE.measurePreserving

theorem deningerConj_measurableEmbedding :
    MeasurableEmbedding (fun z : ℂ => (starRingEnd ℂ) z) :=
  Complex.conjLIE.toHomeomorph.measurableEmbedding

/-- **The fixed axis of the involution is null.**  It is a proper real subspace of the leaf. -/
theorem deningerRealAxis_volume_zero : volume {z : ℂ | z.im = 0} = 0 := by
  have h : {z : ℂ | z.im = 0} = (LinearMap.ker Complex.imLm : Submodule ℝ ℂ) := rfl
  rw [h]
  refine Measure.addHaar_submodule _ _ ?_
  intro hcon
  have hI : Complex.I ∈ (LinearMap.ker Complex.imLm : Submodule ℝ ℂ) := by
    rw [hcon]
    trivial
  simp [LinearMap.mem_ker, Complex.imLm] at hI

/-- The closed and the open half plane agree up to the null fixed axis. -/
theorem deningerRealChart_ae_eq :
    deningerRealChart =ᵐ[volume] {z : ℂ | 0 < z.im} := by
  refine Filter.eventuallyEq_set.mpr ?_
  refine MeasureTheory.ae_iff.mpr ?_
  refine measure_mono_null (fun z hz => ?_) deningerRealAxis_volume_zero
  show z.im = 0
  by_contra him
  refine hz ?_
  show (0 : ℝ) ≤ z.im ↔ (0 : ℝ) < z.im
  rcases lt_or_gt_of_ne him with h | h
  · exact ⟨fun hle => absurd hle (not_le.mpr h), fun hlt => absurd hlt (not_lt.mpr h.le)⟩
  · exact ⟨fun _ => h, fun _ => h.le⟩

/-- The complement of the closed upper half plane is the open lower half plane. -/
theorem deningerRealChart_compl : deningerRealChartᶜ = {z : ℂ | z.im < 0} := by
  ext z
  simp only [deningerRealChart, Set.mem_compl_iff, Set.mem_setOf_eq, not_le]

/-- **The two half planes carry the same integral** for a conjugation-invariant integrand, because
the involution exchanges them and preserves the measure. -/
theorem deningerConj_setIntegral (F : ℂ → ℂ) (hconj : ∀ z : ℂ, F ((starRingEnd ℂ) z) = F z) :
    (∫ z in {z : ℂ | z.im < 0}, F z) = ∫ z in {z : ℂ | 0 < z.im}, F z := by
  have h := deningerConj_measurePreserving.setIntegral_preimage_emb
    deningerConj_measurableEmbedding F {z : ℂ | z.im < 0}
  have hpre : (fun z : ℂ => (starRingEnd ℂ) z) ⁻¹' {z : ℂ | z.im < 0} = {z : ℂ | 0 < z.im} := by
    ext z
    simp only [Set.mem_preimage, Set.mem_setOf_eq, Complex.conj_im, neg_lt_zero]
  rw [hpre] at h
  rw [← h]
  exact setIntegral_congr_fun (measurableSet_lt measurable_const Complex.measurable_im)
    fun z _ => hconj z

/-- **Integration over the real quotient is half the integral over the oriented double cover.** -/
theorem deningerRealChart_half (F : ℂ → ℂ) (hconj : ∀ z : ℂ, F ((starRingEnd ℂ) z) = F z)
    (hint : Integrable F) :
    (∫ z in deningerRealChart, F z) = (1 / 2 : ℂ) * ∫ z : ℂ, F z := by
  have hsplit := integral_add_compl deningerRealChart_measurableSet hint
  rw [deningerRealChart_compl, deningerConj_setIntegral F hconj,
    setIntegral_congr_set deningerRealChart_ae_eq] at hsplit
  rw [setIntegral_congr_set deningerRealChart_ae_eq, ← hsplit]
  ring

end RealQuotient

section RelativeEndpoint

/-- The radial lift is invariant under the real involution. -/
theorem deningerRadialLift_conj (f : ℝ → ℂ) (z : ℂ) :
    deningerRadialLift f ((starRingEnd ℂ) z) = deningerRadialLift f z := by
  rw [deningerRadialLift, deningerRadialLift, RCLike.norm_conj]

/-- **The relative Kähler trace of the real quotient.**  It is half the trace of the oriented
double cover, hence `π/2` times the ray integral. -/
theorem deningerRealApex_trace (f : ℝ → ℂ) (hint : Integrable (deningerRadialLift f)) :
    (∫ z in deningerRealChart, deningerRadialLift f z)
      = ((π : ℂ) / 2) * ∫ x in Ioi (0 : ℝ), f x := by
  rw [deningerRealChart_half _ (deningerRadialLift_conj f) hint, deningerRadialKahler_trace]
  ring

/-- **The relative endpoint.**  For an even integrable function the relative Kähler trace of the
quotient is `π/4` times the Fourier transform at the origin. -/
theorem deningerRealApex_trace_fourier (f : ℝ → ℂ) (heven : ∀ x, f (-x) = f x)
    (hf : Integrable f) (hint : Integrable (deningerRadialLift f)) :
    (∫ z in deningerRealChart, deningerRadialLift f z)
      = ((π : ℂ) / 4) * deningerMeyerFourier f 0 := by
  rw [deningerRealApex_trace f hint, deningerMeyerFourier_zero, deningerEven_integral f heven hf]
  ring

/-- **The apex restriction.**  The radial lift restricted to the fixed apex of the quotient is the
value at the origin. -/
theorem deningerRealApex_restriction (f : ℝ → ℂ) : deningerRadialLift f 0 = f 0 :=
  deningerRadialLift_zero f

/-- **The two relative conditions on the quotient.**  The nonzero normalization scalar does not
change the kernel, so vanishing at the real apex together with vanishing of the orientation-twisted
leaf trace is exactly Meyer's pair of conditions. -/
theorem deningerRealApexEndpoint_iff (f : ℝ → ℂ) (heven : ∀ x, f (-x) = f x)
    (hf : Integrable f) (hint : Integrable (deningerRadialLift f)) :
    (f 0 = 0 ∧ deningerMeyerFourier f 0 = 0)
      ↔ (deningerRadialLift f 0 = 0
          ∧ (∫ z in deningerRealChart, deningerRadialLift f z) = 0) := by
  rw [deningerRadialLift_zero, deningerRealApex_trace_fourier f heven hf hint]
  constructor
  · rintro ⟨h0, hF⟩
    exact ⟨h0, by rw [hF, mul_zero]⟩
  · rintro ⟨h0, hT⟩
    refine ⟨h0, ?_⟩
    have hpi : ((π : ℂ) / 4) ≠ 0 := by
      have hne : (π : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt Real.pi_pos
      exact div_ne_zero hne (by norm_num)
    rcases mul_eq_zero.mp hT with h | h
    · exact absurd h hpi
    · exact h

end RelativeEndpoint

section SchwartzIntegrability

/-- **The radial lift of a Schwartz function is integrable on the leaf.**  The zeroth and second
decay estimates give the bound `(1 + ‖z‖)^{-3}`, which is integrable on a real plane. -/
theorem deningerRadialLift_integrable (f : SchwartzMap ℝ ℂ) :
    Integrable (deningerRadialLift (f : ℝ → ℂ)) := by
  obtain ⟨C0, hC0pos, hC0⟩ := f.decay 0 0
  obtain ⟨C2, hC2pos, hC2⟩ := f.decay 2 0
  have hnorm : ∀ x : ℝ, ‖(f : ℝ → ℂ) x‖ = ‖iteratedFDeriv ℝ 0 (f : ℝ → ℂ) x‖ := by
    intro x
    rw [norm_iteratedFDeriv_zero]
  have hbound0 : ∀ x : ℝ, ‖(f : ℝ → ℂ) x‖ ≤ C0 := by
    intro x
    have := hC0 x
    rw [pow_zero, one_mul, ← hnorm x] at this
    exact this
  have hbound2 : ∀ x : ℝ, ‖x‖ ^ 2 * ‖(f : ℝ → ℂ) x‖ ≤ C2 := by
    intro x
    have := hC2 x
    rw [← hnorm x] at this
    exact this
  have hmeas : AEStronglyMeasurable (deningerRadialLift (f : ℝ → ℂ)) volume := by
    have hcont : Continuous (deningerRadialLift (f : ℝ → ℂ)) := by
      have : Continuous fun z : ℂ => ‖z‖ ^ 2 := (continuous_norm.pow 2)
      exact f.continuous.comp this
    exact hcont.aestronglyMeasurable
  have hint : Integrable fun z : ℂ => (8 * (C0 + C2)) * (1 + ‖z‖) ^ (-(3 : ℝ)) := by
    refine Integrable.const_mul ?_ _
    refine integrable_one_add_norm ?_
    rw [Complex.finrank_real_complex]
    norm_num
  refine Integrable.mono' hint hmeas ?_
  refine Filter.Eventually.of_forall fun z => ?_
  have ht0 : (0 : ℝ) ≤ ‖z‖ := norm_nonneg z
  have hpos : (0 : ℝ) < 1 + ‖z‖ := by linarith
  have hlift : deningerRadialLift (f : ℝ → ℂ) z = (f : ℝ → ℂ) (‖z‖ ^ 2) := rfl
  have hFnn : 0 ≤ ‖(f : ℝ → ℂ) (‖z‖ ^ 2)‖ := norm_nonneg _
  have hF0 : ‖(f : ℝ → ℂ) (‖z‖ ^ 2)‖ ≤ C0 := hbound0 _
  have hF4 : ‖z‖ ^ 4 * ‖(f : ℝ → ℂ) (‖z‖ ^ 2)‖ ≤ C2 := by
    have h := hbound2 (‖z‖ ^ 2)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖z‖ ^ 2)] at h
    calc ‖z‖ ^ 4 * ‖(f : ℝ → ℂ) (‖z‖ ^ 2)‖
        = (‖z‖ ^ 2) ^ 2 * ‖(f : ℝ → ℂ) (‖z‖ ^ 2)‖ := by ring
      _ ≤ C2 := h
  have hkey : ‖(f : ℝ → ℂ) (‖z‖ ^ 2)‖ * (1 + ‖z‖) ^ 3 ≤ 8 * (C0 + C2) := by
    rcases le_or_gt ‖z‖ 1 with hle | hgt
    · have h2 : (1 : ℝ) + ‖z‖ ≤ 2 := by linarith
      have hcube : (1 + ‖z‖) ^ 3 ≤ 8 := by
        calc (1 + ‖z‖) ^ 3 ≤ 2 ^ 3 := by gcongr
          _ = 8 := by norm_num
      have hstep := mul_le_mul_of_nonneg_left hcube hFnn
      linarith [hC2pos.le]
    · have h1t : (1 : ℝ) + ‖z‖ ≤ 2 * ‖z‖ := by linarith
      have hcube : (1 + ‖z‖) ^ 3 ≤ 8 * ‖z‖ ^ 4 := by
        have hc : (1 + ‖z‖) ^ 3 ≤ (2 * ‖z‖) ^ 3 := by gcongr
        have ht3 : ‖z‖ ^ 3 ≤ ‖z‖ ^ 4 := by nlinarith
        nlinarith
      have hstep := mul_le_mul_of_nonneg_left hcube hFnn
      have hstep2 : ‖(f : ℝ → ℂ) (‖z‖ ^ 2)‖ * (8 * ‖z‖ ^ 4)
          = 8 * (‖z‖ ^ 4 * ‖(f : ℝ → ℂ) (‖z‖ ^ 2)‖) := by ring
      rw [hstep2] at hstep
      linarith [hC0pos.le]
  rw [hlift]
  have hrw : (1 + ‖z‖) ^ (-(3 : ℝ)) = ((1 + ‖z‖) ^ (3 : ℕ))⁻¹ := by
    rw [Real.rpow_neg hpos.le, show ((3 : ℝ)) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [hrw, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  exact hkey

/-- **Meyer's relative domain on the real quotient.**  For an even Schwartz function the two
conditions of the real apex chart are exactly apex vanishing and vanishing Fourier transform at the
origin. -/
theorem deningerRealApexEndpoint_schwartz (f : SchwartzMap ℝ ℂ) (heven : ∀ x, f (-x) = f x) :
    ((f : ℝ → ℂ) 0 = 0 ∧ deningerMeyerFourier (f : ℝ → ℂ) 0 = 0)
      ↔ (deningerRadialLift (f : ℝ → ℂ) 0 = 0
          ∧ (∫ z in deningerRealChart, deningerRadialLift (f : ℝ → ℂ) z) = 0) :=
  deningerRealApexEndpoint_iff (f : ℝ → ℂ) heven (SchwartzMap.integrable f)
    (deningerRadialLift_integrable f)

end SchwartzIntegrability

section ForcedTwist

/-- **The twist is forced.**  A one-form invariant under the real involution whose Hodge star is
again invariant vanishes: the star does not descend to the quotient as an untwisted
endomorphism. -/
theorem deningerRealTwist_forced {a : ℝ × ℝ} (ha : deningerGermSigmaOne a = a)
    (hstar : deningerGermSigmaOne (deningerLeafStar a) = deningerLeafStar a) : a = 0 := by
  have h2 : (-a.2 : ℝ) = a.2 := congrArg Prod.snd ha
  have h1 : (-a.1 : ℝ) = a.1 := congrArg Prod.snd hstar
  refine Prod.ext ?_ ?_
  · show a.1 = 0
    linarith
  · show a.2 = 0
    linarith

/-- **The half-density flow commutes with the odd Hodge operator**, because it acts on one-forms by
a real scalar. -/
theorem deningerGermJ_smul (c : ℝ) (a : (ℝ × ℝ) × (ℝ × ℝ)) :
    deningerGermJ (c • a) = c • deningerGermJ a := by
  refine Prod.ext ?_ ?_
  · show deningerLeafStar (c • a.1) = c • deningerLeafStar a.1
    rcases a.1 with ⟨x, y⟩
    simp only [deningerLeafStar, Prod.smul_mk, smul_eq_mul, mul_neg]
  · show -deningerLeafStar (c • a.2) = c • -deningerLeafStar a.2
    rcases a.2 with ⟨x, y⟩
    simp only [deningerLeafStar, Prod.smul_mk, Prod.neg_mk, smul_eq_mul, mul_neg, neg_neg]

theorem deningerGermJ_flow_comm (t : ℝ) (a : (ℝ × ℝ) × (ℝ × ℝ)) :
    deningerGermJ (deningerGermLeafWeight t • a) = deningerGermLeafWeight t • deningerGermJ a :=
  deningerGermJ_smul _ a

end ForcedTwist

end RHTower
