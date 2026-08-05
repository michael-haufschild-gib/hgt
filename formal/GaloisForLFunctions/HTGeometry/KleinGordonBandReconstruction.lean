import GaloisForLFunctions.HTGeometry.KleinGordonPeriodicReconstruction

/-!
# The reconstruction class is inhabited by the band models

The reconstruction theorems of statements 371 and 374 carry two band hypotheses on the difference of
the backgrounds — that it neither sees nor produces frequencies above the cut-off. A criterion decides
nothing until something satisfies it, and the band compressions do: statement 210 records exactly
those two identities for `P_RW₁P_R − P_RW₂P_R`.

The only thing to check is that compression does not spoil the Lipschitz hypothesis, and it cannot:
compression is linear in the operator and contracts, so the difference of differences is compressed
into itself with no growth. Hence

**two moving backgrounds compressed to the same band, observed exactly on short times, have equal
compressions** — the reconstruction theory applies to the very models on which the rest of the card
computes.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- **Compression contracts the difference of differences.** -/
theorem norm_kgBandOp_sub_sub_le
    (A₁ A₂ B₁ B₂ : Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E)) (R : ℝ) :
    ‖(kgBandOp A₁ R - kgBandOp A₂ R) - (kgBandOp B₁ R - kgBandOp B₂ R)‖
      ≤ ‖(A₁ - A₂) - (B₁ - B₂)‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun x => ?_
  have hval : ((kgBandOp A₁ R - kgBandOp A₂ R) - (kgBandOp B₁ R - kgBandOp B₂ R)) x
      = kgLowPassOp R (((A₁ - A₂) - (B₁ - B₂)) (kgLowPassOp R x)) := by
    rw [sub_apply, kgBandOp_sub, kgBandOp_sub, ← map_sub, ← sub_apply]
  rw [hval]
  calc ‖kgLowPassOp R (((A₁ - A₂) - (B₁ - B₂)) (kgLowPassOp R x))‖
      ≤ ‖((A₁ - A₂) - (B₁ - B₂)) (kgLowPassOp R x)‖ := norm_kgLowPassOp_apply_le R _
    _ ≤ ‖(A₁ - A₂) - (B₁ - B₂)‖ * ‖kgLowPassOp R x‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ ‖(A₁ - A₂) - (B₁ - B₂)‖ * ‖x‖ :=
        mul_le_mul_of_nonneg_left (norm_kgLowPassOp_apply_le R x) (norm_nonneg _)

section BandReconstruction

variable {W₁ W₂ : ℝ → (Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E))} {b L : ℝ}

set_option maxHeartbeats 1000000 in
/-- **The reconstruction theorem on the band models.** Two moving backgrounds compressed to the same
band and observed exactly on short times have equal compressions. -/
theorem eq_of_exact_observation_band (hb0 : 0 ≤ b) (hW₁b : ∀ r : ℝ, ‖W₁ r‖ ≤ b)
    (hW₁s : ∀ y : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W₁ r y)
    (hW₂b : ∀ r : ℝ, ‖W₂ r‖ ≤ b)
    (hW₂s : ∀ y : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W₂ r y) (R : ℝ)
    (hL0 : 0 ≤ L)
    (hLip : ∀ σ τ : ℝ, ‖(W₁ σ - W₂ σ) - (W₁ τ - W₂ τ)‖ ≤ L * |σ - τ|)
    {T : ℝ} (hT0 : 0 < T)
    (hobs : ∀ (s : ℝ) (g k : Lp ℂ 2 (volume : Measure E)) (t : ℝ), |t| ≤ T →
      kgFieldMildT (fun r : ℝ => kgBandOpT W₁ R (r + s)) g k t
        = kgFieldMildT (fun r : ℝ => kgBandOpT W₂ R (r + s)) g k t) :
    kgBandOpT W₁ R = kgBandOpT W₂ R := by
  have hLip' : ∀ σ τ : ℝ,
      ‖(kgBandOpT W₁ R σ - kgBandOpT W₂ R σ) - (kgBandOpT W₁ R τ - kgBandOpT W₂ R τ)‖
        ≤ L * |σ - τ| := fun σ τ =>
    (norm_kgBandOp_sub_sub_le (W₁ σ) (W₂ σ) (W₁ τ) (W₂ τ) R).trans (hLip σ τ)
  have hAdom : ∀ (r : ℝ) (v : Lp ℂ 2 (volume : Measure E)),
      (kgBandOpT W₁ R r - kgBandOpT W₂ R r) (kgLowPassOp R v)
        = (kgBandOpT W₁ R r - kgBandOpT W₂ R r) v := fun r v =>
    kgBandOp_lowPass_dom (W₁ r) (W₂ r) R v
  have hAran : ∀ (r : ℝ) (v : Lp ℂ 2 (volume : Measure E)),
      kgLowPassOp R ((kgBandOpT W₁ R r - kgBandOpT W₂ R r) v)
        = (kgBandOpT W₁ R r - kgBandOpT W₂ R r) v := fun r v =>
    kgBandOp_lowPass_ran (W₁ r) (W₂ r) R v
  exact eq_of_exact_observation_everywhere hb0 (norm_kgBandOpT_le hb0 hW₁b R)
    (continuous_kgBandOpT_apply hW₁s R) (norm_kgBandOpT_le hb0 hW₂b R)
    (continuous_kgBandOpT_apply hW₂s R) hL0 hLip' hAdom hAran hT0 hobs

end BandReconstruction

end GaloisForLFunctions.HTGeometry
