import GaloisForLFunctions.HTGeometry.KleinGordon.KleinGordonTimeStrongSolution

/-!
# The strong Cauchy problem on a band, in a moving background

The band removes the obstruction that forced a smoothing hypothesis on the perturbation: the sine
propagator factors through the half-order one and the leftover frequency is the bounded `⟨D⟩_R`. None
of that involves the perturbation, so it works just as well when the perturbation moves.

This file carries statements 225–229 to a moving background. For band-limited data and a moving
background compressed to the band, the mild solution is twice differentiable and satisfies

`∂ₜ²u = −⟨D⟩²_R u + W(t)u`,

hence is a strong solution in the sense of the previous file, and the energy method there makes it the
only one. The strong Cauchy problem in a moving background is well posed on a band, for any uniformly
bounded strongly continuous background.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

section BandInvarianceT

variable {W : ℝ → (Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E))} {b : ℝ}

/-- **The band is invariant under a moving evolution that preserves it.** -/
theorem kgLowPassOp_kgFieldMildT (hb0 : 0 ≤ b) (hWb : ∀ r : ℝ, ‖W r‖ ≤ b)
    (hWs : ∀ z : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r z) {R : ℝ}
    (hdom : ∀ (r : ℝ) (v : Lp ℂ 2 (volume : Measure E)), W r (kgLowPassOp R v) = W r v)
    (hran : ∀ (r : ℝ) (v : Lp ℂ 2 (volume : Measure E)), kgLowPassOp R (W r v) = W r v)
    (f h : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    kgLowPassOp R (kgFieldMildT W f h t)
      = kgFieldMildT W (kgLowPassOp R f) (kgLowPassOp R h) t := by
  have hcu : Continuous (kgFieldMildT W f h) := continuous_kgFieldMildT hb0 hWb hWs f h
  have hproj : Continuous fun τ : ℝ => kgLowPassOp R (kgFieldMildT W f h τ) :=
    (kgLowPassOp (E := E) R).continuous.comp hcu
  have hduh : ∀ τ : ℝ, kgLowPassOp R (kgFieldMildT W f h τ)
      = kgFieldFree (kgLowPassOp R f) (kgLowPassOp R h) τ
        + ∫ s in (0 : ℝ)..τ, kgFieldKernelT W τ s (kgLowPassOp R (kgFieldMildT W f h s)) := by
    intro τ
    have hI := intervalIntegrable_kgFieldKernelT hWb hWs hcu τ
    have hpt : ∀ s ∈ Set.uIcc (0 : ℝ) τ,
        kgLowPassOp R (kgFieldKernelT W τ s (kgFieldMildT W f h s))
          = kgFieldKernelT W τ s (kgLowPassOp R (kgFieldMildT W f h s)) := by
      intro s _
      rw [kgFieldKernelT_apply, kgFieldKernelT_apply, hdom, ← kgSinFreqOp_kgLowPassOp, hran]
    rw [kgFieldMildT_eq hb0 hWb hWs f h τ, map_add, kgLowPassOp_kgFieldFree,
      ← ContinuousLinearMap.intervalIntegral_comp_comm _ hI,
      intervalIntegral.integral_congr hpt]
  have hfin := eq_kgFieldMildT_of_duhamel hb0 hWb hWs (kgLowPassOp R f) (kgLowPassOp R h)
    hproj hduh
  exact congrFun hfin t

/-- **The band is invariant under the moving evolution**: band-limited data stay band-limited. -/
theorem kgFieldMildT_lowPass_invariant (hb0 : 0 ≤ b) (hWb : ∀ r : ℝ, ‖W r‖ ≤ b)
    (hWs : ∀ z : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r z) {R : ℝ}
    (hdom : ∀ (r : ℝ) (v : Lp ℂ 2 (volume : Measure E)), W r (kgLowPassOp R v) = W r v)
    (hran : ∀ (r : ℝ) (v : Lp ℂ 2 (volume : Measure E)), kgLowPassOp R (W r v) = W r v)
    (f h : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    kgLowPassOp R (kgFieldMildT W (kgLowPassOp R f) (kgLowPassOp R h) t)
      = kgFieldMildT W (kgLowPassOp R f) (kgLowPassOp R h) t := by
  rw [kgLowPassOp_kgFieldMildT hb0 hWb hWs hdom hran, kgLowPassOp_idem, kgLowPassOp_idem]

/-- **Band-limited data evolve into band-limited fields**, in a moving background. -/
theorem kgBandOpT_lowPass_invariant (hb0 : 0 ≤ b) (hWb : ∀ r : ℝ, ‖W r‖ ≤ b)
    (hWs : ∀ z : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r z) (R : ℝ)
    (f h : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    kgLowPassOp R (kgFieldMildT (kgBandOpT W R) (kgLowPassOp R f) (kgLowPassOp R h) t)
      = kgFieldMildT (kgBandOpT W R) (kgLowPassOp R f) (kgLowPassOp R h) t :=
  kgFieldMildT_lowPass_invariant hb0 (norm_kgBandOpT_le hb0 hWb R)
    (continuous_kgBandOpT_apply hWs R) (fun r v => kgBandOp_dom (W r) R v)
    (fun r v => kgBandOp_ran (W r) R v) f h t

end BandInvarianceT

section BandStrongT

variable {W : ℝ → (Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E))} {b : ℝ}

/-- **The band-restricted `⟨D⟩²` of the moving solution, in closed form.** -/
theorem kgFreqSqLowOp_kgFieldMildT (hb0 : 0 ≤ b) (hWb : ∀ r : ℝ, ‖W r‖ ≤ b)
    (hWs : ∀ z : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r z) (R : ℝ)
    (x y : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    kgFreqSqLowOp R (kgFieldMildT (kgBandOpT W R) (kgFreqInvOp (kgFreqLowOp R x))
        (kgLowPassOp R y) t)
      = kgCosOp t (kgFreqSqLowOp R x) + kgSinOp t (kgFreqLowOp R y)
        + ∫ s in (0 : ℝ)..t, kgSinOp (t - s) (kgFreqLowOp R (kgBandOpT W R s
            (kgFieldMildT (kgBandOpT W R) (kgFreqInvOp (kgFreqLowOp R x))
              (kgLowPassOp R y) s))) := by
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
  have hfree : kgFreqSqLowOp R (kgCosOp t (kgFreqInvOp (kgFreqLowOp (E := E) R x)))
      = kgCosOp t (kgFreqSqLowOp R x) := by
    rw [kgFreqSqLowOp_kgCosOp, kgFreqInvOp_kgFreqLowOp, ← kgFreqLowOp_kgFreqLowOp,
      kgFreqLowOp_kgLowPassOp, kgFreqLowOp_kgFreqLowOp]
  have hvel : kgFreqSqLowOp R (kgSinFreqOp t (kgLowPassOp (E := E) R y))
      = kgSinOp t (kgFreqLowOp R y) := by
    rw [kgFreqSqLowOp_kgSinFreqOp, kgFreqLowOp_kgLowPassOp]
  have hpt : ∀ s ∈ Set.uIcc (0 : ℝ) t,
      kgFreqSqLowOp R (kgSinFreqOp (t - s) (kgBandOpT W R s
          (kgFieldMildT (kgBandOpT W R) (kgFreqInvOp (kgFreqLowOp R x))
            (kgLowPassOp R y) s)))
        = kgSinOp (t - s) (kgFreqLowOp R (kgBandOpT W R s
            (kgFieldMildT (kgBandOpT W R) (kgFreqInvOp (kgFreqLowOp R x))
              (kgLowPassOp R y) s))) := by
    intro s _
    rw [kgFreqSqLowOp_kgSinFreqOp]
  rw [kgFieldMildT_eq hb0 hRb hRs _ _ t, hker, map_add, kgFieldFree, map_add, hfree, hvel,
    ← ContinuousLinearMap.intervalIntegral_comp_comm _ hI,
    intervalIntegral.integral_congr hpt]

/-- **The mild solution on a band is a strong solution**, in a moving background. -/
theorem hasDerivAt_kgFieldVelT_band (hb0 : 0 ≤ b) (hWb : ∀ r : ℝ, ‖W r‖ ≤ b)
    (hWs : ∀ z : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r z) (R : ℝ)
    (x y : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    HasDerivAt (kgFieldVelT (kgBandOpT W R) (kgFreqLowOp R x) (kgLowPassOp R y))
      (-(kgFreqSqLowOp R (kgFieldMildT (kgBandOpT W R) (kgFreqInvOp (kgFreqLowOp R x))
            (kgLowPassOp R y) t))
        + kgBandOpT W R t (kgFieldMildT (kgBandOpT W R) (kgFreqInvOp (kgFreqLowOp R x))
            (kgLowPassOp R y) t)) t := by
  have hRb : ∀ r : ℝ, ‖kgBandOpT W R r‖ ≤ b := norm_kgBandOpT_le hb0 hWb R
  have hRs : ∀ z : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => kgBandOpT W R r z :=
    continuous_kgBandOpT_apply hWs R
  have hcu : Continuous (kgFieldMildT (kgBandOpT W R) (kgFreqInvOp (kgFreqLowOp R x))
      (kgLowPassOp R y)) := continuous_kgFieldMildT hb0 hRb hRs _ _
  have hcurve : Continuous fun s : ℝ => kgBandOpT W R s
      (kgFieldMildT (kgBandOpT W R) (kgFreqInvOp (kgFreqLowOp R x)) (kgLowPassOp R y) s) :=
    continuous_of_strong_comp hRb hRs continuous_id hcu
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
  have hB : HasDerivAt (fun s : ℝ => kgCosOp s (kgLowPassOp (E := E) R y))
      (-(kgSinOp t (kgFreqLowOp R y))) t := by
    have hd := hasDerivAt_kgCosOp_freqInv (E := E) t (kgFreqLowOp R y)
    refine hd.congr_of_eventuallyEq ?_
    exact Filter.Eventually.of_forall fun s => by rw [kgFreqInvOp_kgFreqLowOp]
  have hk : Continuous fun s : ℝ => kgFreqLowOp R (kgBandOpT W R s
      (kgFieldMildT (kgBandOpT W R) (kgFreqInvOp (kgFreqLowOp R x)) (kgLowPassOp R y) s)) :=
    (kgFreqLowOp (E := E) R).continuous.comp hcurve
  have hreg : ∀ s : ℝ, kgFreqInvOp (kgFreqLowOp R (kgBandOpT W R s
        (kgFieldMildT (kgBandOpT W R) (kgFreqInvOp (kgFreqLowOp R x)) (kgLowPassOp R y) s)))
      = kgBandOpT W R s (kgFieldMildT (kgBandOpT W R) (kgFreqInvOp (kgFreqLowOp R x))
          (kgLowPassOp R y) s) := by
    intro s
    rw [kgFreqInvOp_kgFreqLowOp]
    exact kgBandOp_ran (W s) R _
  have hC : HasDerivAt (fun r : ℝ => ∫ s in (0 : ℝ)..r, kgCosOp (r - s) (kgBandOpT W R s
        (kgFieldMildT (kgBandOpT W R) (kgFreqInvOp (kgFreqLowOp R x)) (kgLowPassOp R y) s)))
      (kgBandOpT W R t (kgFieldMildT (kgBandOpT W R) (kgFreqInvOp (kgFreqLowOp R x))
          (kgLowPassOp R y) t)
        - ∫ s in (0 : ℝ)..t, kgSinOp (t - s) (kgFreqLowOp R (kgBandOpT W R s
            (kgFieldMildT (kgBandOpT W R) (kgFreqInvOp (kgFreqLowOp R x))
              (kgLowPassOp R y) s)))) t := by
    have hd := hasDerivAt_kgCosDuhamel hk t
    rw [hreg t] at hd
    refine hd.congr_of_eventuallyEq ?_
    refine Filter.Eventually.of_forall fun r => ?_
    exact intervalIntegral.integral_congr fun s _ => by rw [hreg s]
  have hsum := (hA.add hB).add hC
  have hval : -(kgCosOp t (kgFreqSqLowOp (E := E) R x)) + -(kgSinOp t (kgFreqLowOp R y))
      + (kgBandOpT W R t (kgFieldMildT (kgBandOpT W R) (kgFreqInvOp (kgFreqLowOp R x))
            (kgLowPassOp R y) t)
        - ∫ s in (0 : ℝ)..t, kgSinOp (t - s) (kgFreqLowOp R (kgBandOpT W R s
            (kgFieldMildT (kgBandOpT W R) (kgFreqInvOp (kgFreqLowOp R x))
              (kgLowPassOp R y) s))))
      = -(kgFreqSqLowOp R (kgFieldMildT (kgBandOpT W R) (kgFreqInvOp (kgFreqLowOp R x))
            (kgLowPassOp R y) t))
        + kgBandOpT W R t (kgFieldMildT (kgBandOpT W R) (kgFreqInvOp (kgFreqLowOp R x))
            (kgLowPassOp R y) t) := by
    rw [kgFreqSqLowOp_kgFieldMildT hb0 hWb hWs R x y t]
    abel
  rw [hval] at hsum
  refine hsum.congr_of_eventuallyEq ?_
  refine Filter.Eventually.of_forall fun r => ?_
  simp only [Pi.add_apply, kgFieldVelT]

/-- **The band solution is a strong solution** in a moving background. -/
theorem solvesKGSourceT_band (hb0 : 0 ≤ b) (hWb : ∀ r : ℝ, ‖W r‖ ≤ b)
    (hWs : ∀ z : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r z) (R : ℝ)
    (x y : Lp ℂ 2 (volume : Measure E)) :
    SolvesKGSourceT (kgBandOpT W R)
      (kgFieldMildT (kgBandOpT W R) (kgFreqInvOp (kgFreqLowOp R x)) (kgLowPassOp R y))
      (kgFieldVelT (kgBandOpT W R) (kgFreqLowOp R x) (kgLowPassOp R y))
      (fun t => -(kgFreqSqLowOp R (kgFieldMildT (kgBandOpT W R)
            (kgFreqInvOp (kgFreqLowOp R x)) (kgLowPassOp R y) t))
        + kgBandOpT W R t (kgFieldMildT (kgBandOpT W R)
            (kgFreqInvOp (kgFreqLowOp R x)) (kgLowPassOp R y) t)) := by
  have hRb : ∀ r : ℝ, ‖kgBandOpT W R r‖ ≤ b := norm_kgBandOpT_le hb0 hWb R
  have hRs : ∀ z : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => kgBandOpT W R r z :=
    continuous_kgBandOpT_apply hWs R
  refine ⟨fun t => hasDerivAt_kgFieldMildT hb0 hRb hRs (kgFreqLowOp R x) (kgLowPassOp R y) t,
    fun t => hasDerivAt_kgFieldVelT_band hb0 hWb hWs R x y t, fun t => ?_⟩
  have hband : kgLowPassOp R (kgFieldMildT (kgBandOpT W R) (kgFreqInvOp (kgFreqLowOp R x))
      (kgLowPassOp R y) t)
      = kgFieldMildT (kgBandOpT W R) (kgFreqInvOp (kgFreqLowOp R x)) (kgLowPassOp R y) t := by
    rw [kgFreqInvOp_kgFreqLowOp]
    exact kgBandOpT_lowPass_invariant hb0 hWb hWs R x y t
  rw [map_add, map_add, map_neg, map_neg, kgFreqInvOp_sq_kgFreqSqLowOp, hband]

/-- **Uniqueness of the strong solution on a band**, in a moving background. -/
theorem eq_of_solvesKGSourceT_band (hb0 : 0 ≤ b) (hWb : ∀ r : ℝ, ‖W r‖ ≤ b) (R : ℝ)
    {u₁ v₁ a₁ u₂ v₂ a₂ : ℝ → Lp ℂ 2 (volume : Measure E)}
    (h₁ : SolvesKGSourceT (kgBandOpT W R) u₁ v₁ a₁)
    (h₂ : SolvesKGSourceT (kgBandOpT W R) u₂ v₂ a₂)
    (hu0 : u₁ 0 = u₂ 0) (hv0 : v₁ 0 = v₂ 0) (t : ℝ) : u₁ t = u₂ t :=
  eq_of_solvesKGSourceT hb0 (norm_kgBandOpT_le hb0 hWb R) h₁ h₂ hu0 hv0 t

/-- **The strong Cauchy problem on a band is well posed in a moving background.** For band-limited
data and any uniformly bounded strongly continuous background compressed to the band there is a strong
solution with those data, and it is the only one. -/
theorem exists_unique_solvesKGSourceT_band (hb0 : 0 ≤ b) (hWb : ∀ r : ℝ, ‖W r‖ ≤ b)
    (hWs : ∀ z : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r z) (R : ℝ)
    (x y : Lp ℂ 2 (volume : Measure E)) :
    ∃ u v a : ℝ → Lp ℂ 2 (volume : Measure E),
      SolvesKGSourceT (kgBandOpT W R) u v a ∧ u 0 = kgLowPassOp R x ∧ v 0 = kgLowPassOp R y ∧
        ∀ u' v' a' : ℝ → Lp ℂ 2 (volume : Measure E),
          SolvesKGSourceT (kgBandOpT W R) u' v' a' → u' 0 = kgLowPassOp R x →
            v' 0 = kgLowPassOp R y → ∀ t : ℝ, u' t = u t := by
  have hRb : ∀ r : ℝ, ‖kgBandOpT W R r‖ ≤ b := norm_kgBandOpT_le hb0 hWb R
  have hRs : ∀ z : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => kgBandOpT W R r z :=
    continuous_kgBandOpT_apply hWs R
  refine ⟨_, _, _, solvesKGSourceT_band hb0 hWb hWs R x y, ?_, ?_, ?_⟩
  · rw [kgFieldMildT_zero hb0 hRb hRs, kgFreqInvOp_kgFreqLowOp]
  · rw [kgFieldVelT, intervalIntegral.integral_same, kgSinOp_zero, kgCosOp_zero]
    simp
  · intro u' v' a' h' hu0 hv0 t
    refine eq_of_solvesKGSourceT_band hb0 hWb R h' (solvesKGSourceT_band hb0 hWb hWs R x y)
      ?_ ?_ t
    · rw [hu0, kgFieldMildT_zero hb0 hRb hRs, kgFreqInvOp_kgFreqLowOp]
    · rw [hv0, kgFieldVelT, intervalIntegral.integral_same, kgSinOp_zero, kgCosOp_zero]
      simp

end BandStrongT

end GaloisForLFunctions.HTGeometry
