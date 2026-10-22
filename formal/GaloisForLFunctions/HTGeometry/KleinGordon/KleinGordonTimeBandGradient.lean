import GaloisForLFunctions.HTGeometry.KleinGordon.KleinGordonTimeBandStrong

/-!
# The gradient on a band, in a moving background

Statement 231 identifies the abstract gradient of the energy thread with `⟨D⟩_R u`, the
band-restricted frequency applied to the solution, for a fixed perturbation. Nothing in that
identification uses autonomy: the frequency passes through the Duhamel formula term by term, and each
term carries the perturbation only inside the source.

The file also records that band compression commutes with switching a fixed perturbation on and off:
compressing `φ(t)W₀` is the same as switching the compression `P_RW₀P_R`, because compression is
linear in the operator. That turns every statement of the adiabatic layer into a statement about a
band by a change of the fixed operator alone.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-! ## Compression is linear in the operator -/

/-- The band compression of a scalar multiple is the multiple of the compression. -/
theorem kgBandOp_smul (c : ℂ) (W₀ : Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E))
    (R : ℝ) : kgBandOp (c • W₀) R = c • kgBandOp W₀ R := by
  refine ContinuousLinearMap.ext fun x => ?_
  rw [kgBandOp_apply, smul_apply, smul_apply, kgBandOp_apply, map_smul]

/-- **Compressing a switched perturbation is switching the compressed one.** -/
theorem kgBandOpT_kgScaledPotential
    (W₀ : Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E)) (φ : ℝ → ℝ) (R : ℝ) :
    kgBandOpT (kgScaledPotential W₀ φ) R = kgScaledPotential (kgBandOp W₀ R) φ := by
  funext t
  exact kgBandOp_smul _ W₀ R

/-! ## The gradient on a band -/

section BandGradientT

variable {W : ℝ → (Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E))} {b : ℝ}

/-- **On a band the abstract gradient is the band-restricted frequency of the solution**, in a
moving background. -/
theorem kgFieldGradT_band (hb0 : 0 ≤ b) (hWb : ∀ r : ℝ, ‖W r‖ ≤ b)
    (hWs : ∀ z : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r z) (R : ℝ)
    (x y : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    kgFieldGradT (kgBandOpT W R) (kgFreqLowOp R x) (kgLowPassOp R y) t
      = kgFreqLowOp R (kgFieldMildT (kgBandOpT W R) (kgFreqInvOp (kgFreqLowOp R x))
          (kgLowPassOp R y) t) := by
  have hRb : ∀ r : ℝ, ‖kgBandOpT W R r‖ ≤ b := norm_kgBandOpT_le hb0 hWb R
  have hRs : ∀ z : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => kgBandOpT W R r z :=
    continuous_kgBandOpT_apply hWs R
  have hcu : Continuous (kgFieldMildT (kgBandOpT W R) (kgFreqInvOp (kgFreqLowOp R x))
      (kgLowPassOp R y)) := continuous_kgFieldMildT hb0 hRb hRs _ _
  have hcurve : Continuous fun s : ℝ => kgBandOpT W R s
      (kgFieldMildT (kgBandOpT W R) (kgFreqInvOp (kgFreqLowOp R x)) (kgLowPassOp R y) s) :=
    continuous_of_strong_comp hRb hRs continuous_id hcu
  have hsrc : Continuous fun s : ℝ => kgSinFreqOp (t - s) (kgBandOpT W R s
      (kgFieldMildT (kgBandOpT W R) (kgFreqInvOp (kgFreqLowOp R x)) (kgLowPassOp R y) s)) :=
    continuous_kgSinFreqOp_comp (continuous_const.sub continuous_id) hcurve
  have hI := hsrc.intervalIntegrable (μ := volume) 0 t
  have hker : (∫ s in (0 : ℝ)..t, kgFieldKernelT (kgBandOpT W R) t s
        (kgFieldMildT (kgBandOpT W R) (kgFreqInvOp (kgFreqLowOp R x)) (kgLowPassOp R y) s))
      = ∫ s in (0 : ℝ)..t, kgSinFreqOp (t - s) (kgBandOpT W R s
          (kgFieldMildT (kgBandOpT W R) (kgFreqInvOp (kgFreqLowOp R x))
            (kgLowPassOp R y) s)) :=
    intervalIntegral.integral_congr fun s _ => kgFieldKernelT_apply (kgBandOpT W R) t s _
  have hfree : kgFreqLowOp R (kgCosOp t (kgFreqInvOp (kgFreqLowOp (E := E) R x)))
      = kgCosOp t (kgFreqLowOp R x) := by
    rw [kgFreqInvOp_kgFreqLowOp, ← kgCosOp_kgFreqLowOp, kgFreqLowOp_kgLowPassOp]
  have hvel : kgFreqLowOp R (kgSinFreqOp t (kgLowPassOp (E := E) R y))
      = kgSinOp t (kgLowPassOp R y) := by
    rw [kgFreqLowOp_kgSinFreqOp, kgLowPassOp_idem]
  have hpt : ∀ s ∈ Set.uIcc (0 : ℝ) t,
      kgFreqLowOp R (kgSinFreqOp (t - s) (kgBandOpT W R s
          (kgFieldMildT (kgBandOpT W R) (kgFreqInvOp (kgFreqLowOp R x))
            (kgLowPassOp R y) s)))
        = kgSinOp (t - s) (kgBandOpT W R s
            (kgFieldMildT (kgBandOpT W R) (kgFreqInvOp (kgFreqLowOp R x))
              (kgLowPassOp R y) s)) := by
    intro s _
    rw [kgFreqLowOp_kgSinFreqOp]
    exact congrArg (kgSinOp (t - s)) (kgBandOp_ran (W s) R _)
  rw [kgFieldMildT_eq hb0 hRb hRs _ _ t, hker, map_add, kgFieldFree, map_add, hfree, hvel,
    ← ContinuousLinearMap.intervalIntegral_comp_comm _ hI,
    intervalIntegral.integral_congr hpt, kgFieldGradT]

end BandGradientT

end GaloisForLFunctions.HTGeometry
