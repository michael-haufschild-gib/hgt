import GaloisForLFunctions.HTGeometry.KleinGordon.KleinGordonBandFrequency

/-!
# The strong solution on a band, with no smoothing hypothesis

The perturbed equation was solved strongly only under a smoothing hypothesis on the perturbation
(statements 103–109), because `⟨D⟩sin(τ⟨D⟩)` is unbounded and appears when the velocity is
differentiated a second time. On a band it does not appear: the sine propagator factors through the
half-order one (statement 223), which is differentiable on every vector, and the leftover frequency is
the bounded `⟨D⟩_R`.

So for band-limited data and a band-compressed perturbation the mild solution is a **strong** solution:
it is twice differentiable and satisfies

`∂ₜ²u = −⟨D⟩²_R u + Wu`

as an identity in `L²`, with no hypothesis on the perturbation beyond boundedness. Every input is
already in the corpus — the two propagator derivatives of statement 65, the Duhamel second derivative
of statement 102, and the symbol calculus of statements 221–224; what this file does is check that
they fit together, which is the identity `⟨D⟩²_R u = cos(t⟨D⟩)⟨D⟩²_R x + sin(t⟨D⟩)⟨D⟩_R y + ∫ …`
obtained by pushing `⟨D⟩²_R` through the Duhamel formula.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

section BandStrong

variable {W₀ : Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E)} {b : ℝ}

/-- **The band-restricted `⟨D⟩²` of the solution, in closed form.** -/
theorem kgFreqSqLowOp_kgFieldMild (hb0 : 0 ≤ b) (hW : ‖W₀‖ ≤ b) (R : ℝ)
    (x y : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    kgFreqSqLowOp R (kgFieldMild (kgBandOp W₀ R) (kgFreqInvOp (kgFreqLowOp R x))
        (kgLowPassOp R y) t)
      = kgCosOp t (kgFreqSqLowOp R x) + kgSinOp t (kgFreqLowOp R y)
        + ∫ s in (0 : ℝ)..t, kgSinOp (t - s) (kgFreqLowOp R (kgBandOp W₀ R
            (kgFieldMild (kgBandOp W₀ R) (kgFreqInvOp (kgFreqLowOp R x))
              (kgLowPassOp R y) s))) := by
  have hWb : ‖kgBandOp W₀ R‖ ≤ b := norm_kgBandOp_le hb0 hW R
  have hcu : Continuous (kgFieldMild (kgBandOp W₀ R) (kgFreqInvOp (kgFreqLowOp R x))
      (kgLowPassOp R y)) := continuous_kgFieldMild hb0 hWb _ _
  have hsrc : Continuous fun s : ℝ => kgSinFreqOp (t - s) (kgBandOp W₀ R
      (kgFieldMild (kgBandOp W₀ R) (kgFreqInvOp (kgFreqLowOp R x)) (kgLowPassOp R y) s)) :=
    continuous_kgSinFreqOp_comp (continuous_const.sub continuous_id)
      ((kgBandOp W₀ R).continuous.comp hcu)
  have hI := hsrc.intervalIntegrable (μ := volume) 0 t
  have hker : (∫ s in (0 : ℝ)..t, kgFieldKernel (kgBandOp W₀ R) t s
        (kgFieldMild (kgBandOp W₀ R) (kgFreqInvOp (kgFreqLowOp R x)) (kgLowPassOp R y) s))
      = ∫ s in (0 : ℝ)..t, kgSinFreqOp (t - s) (kgBandOp W₀ R
          (kgFieldMild (kgBandOp W₀ R) (kgFreqInvOp (kgFreqLowOp R x)) (kgLowPassOp R y) s)) :=
    intervalIntegral.integral_congr fun s _ => kgFieldKernel_apply (kgBandOp W₀ R) t s _
  have hfree : kgFreqSqLowOp R (kgCosOp t (kgFreqInvOp (kgFreqLowOp (E := E) R x)))
      = kgCosOp t (kgFreqSqLowOp R x) := by
    rw [kgFreqSqLowOp_kgCosOp, kgFreqInvOp_kgFreqLowOp, ← kgFreqLowOp_kgFreqLowOp,
      kgFreqLowOp_kgLowPassOp, kgFreqLowOp_kgFreqLowOp]
  have hvel : kgFreqSqLowOp R (kgSinFreqOp t (kgLowPassOp (E := E) R y))
      = kgSinOp t (kgFreqLowOp R y) := by
    rw [kgFreqSqLowOp_kgSinFreqOp, kgFreqLowOp_kgLowPassOp]
  have hpt : ∀ s ∈ Set.uIcc (0 : ℝ) t,
      kgFreqSqLowOp R (kgSinFreqOp (t - s) (kgBandOp W₀ R
          (kgFieldMild (kgBandOp W₀ R) (kgFreqInvOp (kgFreqLowOp R x)) (kgLowPassOp R y) s)))
        = kgSinOp (t - s) (kgFreqLowOp R (kgBandOp W₀ R
            (kgFieldMild (kgBandOp W₀ R) (kgFreqInvOp (kgFreqLowOp R x))
              (kgLowPassOp R y) s))) := by
    intro s _
    rw [kgFreqSqLowOp_kgSinFreqOp]
  rw [kgFieldMild_eq hb0 hWb _ _ t, hker, map_add, kgFieldFree, map_add, hfree, hvel,
    ← ContinuousLinearMap.intervalIntegral_comp_comm _ hI,
    intervalIntegral.integral_congr hpt]

/-- **The mild solution on a band is a strong solution.** No smoothing hypothesis: the perturbation
is any bounded operator, compressed to the band. -/
theorem hasDerivAt_kgFieldVel_band (hb0 : 0 ≤ b) (hW : ‖W₀‖ ≤ b) (R : ℝ)
    (x y : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    HasDerivAt (kgFieldVel (kgBandOp W₀ R) (kgFreqLowOp R x) (kgLowPassOp R y))
      (-(kgFreqSqLowOp R (kgFieldMild (kgBandOp W₀ R) (kgFreqInvOp (kgFreqLowOp R x))
            (kgLowPassOp R y) t))
        + kgBandOp W₀ R (kgFieldMild (kgBandOp W₀ R) (kgFreqInvOp (kgFreqLowOp R x))
            (kgLowPassOp R y) t)) t := by
  have hWb : ‖kgBandOp W₀ R‖ ≤ b := norm_kgBandOp_le hb0 hW R
  have hcu : Continuous (kgFieldMild (kgBandOp W₀ R) (kgFreqInvOp (kgFreqLowOp R x))
      (kgLowPassOp R y)) := continuous_kgFieldMild hb0 hWb _ _
  -- the first term: the sine propagator factors through the half-order one
  have hsin : ∀ s : ℝ, kgSinOp s (kgFreqLowOp (E := E) R x)
      = kgSinFreqOp s (kgFreqSqLowOp R x) := by
    intro s
    rw [← kgLowPassOp_kgFreqLowOp R x, kgSinOp_kgLowPassOp, kgFreqLowOp_kgFreqLowOp]
  have hA : HasDerivAt (fun s : ℝ => -(kgSinOp s (kgFreqLowOp (E := E) R x)))
      (-(kgCosOp t (kgFreqSqLowOp R x))) t := by
    have hd := (hasDerivAt_kgSinFreqOp (E := E) t (kgFreqSqLowOp R x)).neg
    refine hd.congr_of_eventuallyEq ?_
    refine Filter.Eventually.of_forall fun s => ?_
    simp only [Pi.neg_apply]
    rw [hsin s]
  -- the second term: the velocity datum carries a power of the inverse frequency
  have hB : HasDerivAt (fun s : ℝ => kgCosOp s (kgLowPassOp (E := E) R y))
      (-(kgSinOp t (kgFreqLowOp R y))) t := by
    have hd := hasDerivAt_kgCosOp_freqInv (E := E) t (kgFreqLowOp R y)
    refine hd.congr_of_eventuallyEq ?_
    exact Filter.Eventually.of_forall fun s => by rw [kgFreqInvOp_kgFreqLowOp]
  -- the Duhamel term: the source is band-limited, hence regular
  have hk : Continuous fun s : ℝ => kgFreqLowOp R (kgBandOp W₀ R
      (kgFieldMild (kgBandOp W₀ R) (kgFreqInvOp (kgFreqLowOp R x)) (kgLowPassOp R y) s)) :=
    (kgFreqLowOp (E := E) R).continuous.comp ((kgBandOp W₀ R).continuous.comp hcu)
  have hreg : ∀ s : ℝ, kgFreqInvOp (kgFreqLowOp R (kgBandOp W₀ R
        (kgFieldMild (kgBandOp W₀ R) (kgFreqInvOp (kgFreqLowOp R x)) (kgLowPassOp R y) s)))
      = kgBandOp W₀ R (kgFieldMild (kgBandOp W₀ R) (kgFreqInvOp (kgFreqLowOp R x))
          (kgLowPassOp R y) s) := by
    intro s
    rw [kgFreqInvOp_kgFreqLowOp, kgBandOp_ran]
  have hC : HasDerivAt (fun r : ℝ => ∫ s in (0 : ℝ)..r, kgCosOp (r - s) (kgBandOp W₀ R
        (kgFieldMild (kgBandOp W₀ R) (kgFreqInvOp (kgFreqLowOp R x)) (kgLowPassOp R y) s)))
      (kgBandOp W₀ R (kgFieldMild (kgBandOp W₀ R) (kgFreqInvOp (kgFreqLowOp R x))
          (kgLowPassOp R y) t)
        - ∫ s in (0 : ℝ)..t, kgSinOp (t - s) (kgFreqLowOp R (kgBandOp W₀ R
            (kgFieldMild (kgBandOp W₀ R) (kgFreqInvOp (kgFreqLowOp R x))
              (kgLowPassOp R y) s)))) t := by
    have hd := hasDerivAt_kgCosDuhamel hk t
    rw [hreg t] at hd
    refine hd.congr_of_eventuallyEq ?_
    refine Filter.Eventually.of_forall fun r => ?_
    exact intervalIntegral.integral_congr fun s _ => by rw [hreg s]
  have hsum := (hA.add hB).add hC
  have hval : -(kgCosOp t (kgFreqSqLowOp (E := E) R x)) + -(kgSinOp t (kgFreqLowOp R y))
      + (kgBandOp W₀ R (kgFieldMild (kgBandOp W₀ R) (kgFreqInvOp (kgFreqLowOp R x))
            (kgLowPassOp R y) t)
        - ∫ s in (0 : ℝ)..t, kgSinOp (t - s) (kgFreqLowOp R (kgBandOp W₀ R
            (kgFieldMild (kgBandOp W₀ R) (kgFreqInvOp (kgFreqLowOp R x))
              (kgLowPassOp R y) s))))
      = -(kgFreqSqLowOp R (kgFieldMild (kgBandOp W₀ R) (kgFreqInvOp (kgFreqLowOp R x))
            (kgLowPassOp R y) t))
        + kgBandOp W₀ R (kgFieldMild (kgBandOp W₀ R) (kgFreqInvOp (kgFreqLowOp R x))
            (kgLowPassOp R y) t) := by
    rw [kgFreqSqLowOp_kgFieldMild hb0 hW R x y t]
    abel
  rw [hval] at hsum
  refine hsum.congr_of_eventuallyEq ?_
  refine Filter.Eventually.of_forall fun r => ?_
  simp only [Pi.add_apply, kgFieldVel]

end BandStrong

end GaloisForLFunctions.HTGeometry
