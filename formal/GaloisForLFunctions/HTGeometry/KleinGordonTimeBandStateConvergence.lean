import GaloisForLFunctions.HTGeometry.KleinGordonTimeBandApproximation
import GaloisForLFunctions.HTGeometry.KleinGordonTimeFieldEnergy

/-!
# The state and the energy converge in a moving background

Statement 252 approximates the field of a clock in a moving background; the clock reads the state, so
what has to converge is the pair `(⟨D⟩u, ∂ₜu)` and with it the energy. The two components are the same
Duhamel formula with the sine and the cosine propagator, and both have the same integrand, so the work
is done once: the perturbed source `W_R(s)u_R(s)` converges to `W(s)u(s)`, by the splitting

`W_R(s)u_R(s) − W(s)u(s) = W_R(s)(u_R(s) − u(s)) + (W_R(s) − W(s))u(s)`,

whose first term is damped by the uniform bound and killed by statement 252 and whose second vanishes
by statement 247. The integrands are bounded by a constant on the interval, so dominated convergence
gives both propagator terms, and hence

`‖⟨D⟩u_R(t)‖² + ‖∂ₜu_R(t)‖² → ‖⟨D⟩u(t)‖² + ‖∂ₜu(t)‖²`.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

section StateT

variable {W : ℝ → (Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E))} {b : ℝ}

/-- **The perturbed sources converge**, in a moving background. -/
theorem tendsto_kgBandOpT_source (hb0 : 0 ≤ b) (hWb : ∀ r : ℝ, ‖W r‖ ≤ b)
    (hWs : ∀ z : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r z)
    (x y : Lp ℂ 2 (volume : Measure E)) (s : ℝ) :
    Tendsto (fun R : ℝ => kgBandOpT W R s
        (kgFieldMildT (kgBandOpT W R) (kgLowPassOp R x) (kgLowPassOp R y) s)) atTop
      (𝓝 (W s (kgFieldMildT W x y s))) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hsol := (tendsto_iff_norm_sub_tendsto_zero).mp
    (tendsto_kgFieldMildT_band hb0 hWb hWs x y s)
  have hop := (tendsto_iff_norm_sub_tendsto_zero).mp
    (tendsto_kgBandOpT_apply W s (kgFieldMildT W x y s))
  have hle : ∀ R : ℝ, ‖kgBandOpT W R s
        (kgFieldMildT (kgBandOpT W R) (kgLowPassOp R x) (kgLowPassOp R y) s)
          - W s (kgFieldMildT W x y s)‖
      ≤ b * ‖kgFieldMildT (kgBandOpT W R) (kgLowPassOp R x) (kgLowPassOp R y) s
            - kgFieldMildT W x y s‖
        + ‖kgBandOpT W R s (kgFieldMildT W x y s) - W s (kgFieldMildT W x y s)‖ := by
    intro R
    have hsplit : kgBandOpT W R s
          (kgFieldMildT (kgBandOpT W R) (kgLowPassOp R x) (kgLowPassOp R y) s)
            - W s (kgFieldMildT W x y s)
        = kgBandOpT W R s (kgFieldMildT (kgBandOpT W R) (kgLowPassOp R x)
            (kgLowPassOp R y) s - kgFieldMildT W x y s)
          + (kgBandOpT W R s (kgFieldMildT W x y s) - W s (kgFieldMildT W x y s)) := by
      rw [map_sub]
      abel
    rw [hsplit]
    refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
    exact (kgBandOpT W R s).le_of_opNorm_le (norm_kgBandOpT_le hb0 hWb R s) _
  have hsum : Tendsto (fun R : ℝ => b * ‖kgFieldMildT (kgBandOpT W R) (kgLowPassOp R x)
        (kgLowPassOp R y) s - kgFieldMildT W x y s‖
      + ‖kgBandOpT W R s (kgFieldMildT W x y s) - W s (kgFieldMildT W x y s)‖) atTop (𝓝 0) := by
    simpa using (hsol.const_mul b).add hop
  exact squeeze_zero (fun _ => norm_nonneg _) hle hsum

set_option maxHeartbeats 1000000 in
/-- **The Duhamel terms of the velocity converge**, in a moving background. -/
theorem tendsto_integral_kgCosT_band (hb0 : 0 ≤ b) (hWb : ∀ r : ℝ, ‖W r‖ ≤ b)
    (hWs : ∀ z : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r z)
    (x y : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    Tendsto (fun R : ℝ => ∫ s in (0 : ℝ)..t, kgCosOp (t - s) (kgBandOpT W R s
        (kgFieldMildT (kgBandOpT W R) (kgLowPassOp R x) (kgLowPassOp R y) s))) atTop
      (𝓝 (∫ s in (0 : ℝ)..t, kgCosOp (t - s) (W s (kgFieldMildT W x y s)))) := by
  set K : ℝ := b * ((‖x‖ + ‖y‖) * Real.exp (b * |t|)) with hK
  have hK0 : (0 : ℝ) ≤ K := by rw [hK]; positivity
  have hbound : IntervalIntegrable (fun _ : ℝ => K) volume 0 t := intervalIntegrable_const
  have hsrc : ∀ R : ℝ, Continuous fun s : ℝ => kgBandOpT W R s
      (kgFieldMildT (kgBandOpT W R) (kgLowPassOp R x) (kgLowPassOp R y) s) := fun R =>
    continuous_of_strong_comp (norm_kgBandOpT_le hb0 hWb R) (continuous_kgBandOpT_apply hWs R)
      continuous_id (continuous_kgFieldMildT hb0 (norm_kgBandOpT_le hb0 hWb R)
        (continuous_kgBandOpT_apply hWs R) _ _)
  have hmeas : ∀ R : ℝ, AEStronglyMeasurable
      (fun s : ℝ => kgCosOp (t - s) (kgBandOpT W R s
        (kgFieldMildT (kgBandOpT W R) (kgLowPassOp R x) (kgLowPassOp R y) s)))
      (volume.restrict (Set.uIoc 0 t)) := fun R =>
    (continuous_kgCosOp_comp (continuous_const.sub continuous_id) (hsrc R)).aestronglyMeasurable
  have hdom : ∀ R : ℝ, ∀ᵐ s : ℝ, s ∈ Set.uIoc 0 t →
      ‖kgCosOp (t - s) (kgBandOpT W R s
        (kgFieldMildT (kgBandOpT W R) (kgLowPassOp R x) (kgLowPassOp R y) s))‖ ≤ K := by
    intro R
    filter_upwards with s hs
    have habs : |s| ≤ |t| := abs_le_abs_of_mem_uIoc_zero hs
    have h1 := norm_kgCosOp_apply_le (E := E) (t - s) (kgBandOpT W R s
      (kgFieldMildT (kgBandOpT W R) (kgLowPassOp R x) (kgLowPassOp R y) s))
    have h2 : ‖kgBandOpT W R s
        (kgFieldMildT (kgBandOpT W R) (kgLowPassOp R x) (kgLowPassOp R y) s)‖
        ≤ b * ‖kgFieldMildT (kgBandOpT W R) (kgLowPassOp R x) (kgLowPassOp R y) s‖ :=
      (kgBandOpT W R s).le_of_opNorm_le (norm_kgBandOpT_le hb0 hWb R s) _
    have h3 : ‖kgFieldMildT (kgBandOpT W R) (kgLowPassOp R x) (kgLowPassOp R y) s‖
        ≤ (‖kgLowPassOp (E := E) R x‖ + ‖kgLowPassOp (E := E) R y‖) * Real.exp (b * |s|) :=
      norm_kgFieldMildT_le hb0 (norm_kgBandOpT_le hb0 hWb R)
        (continuous_kgBandOpT_apply hWs R) _ _ s
    have h4 : ‖kgLowPassOp (E := E) R x‖ ≤ ‖x‖ := norm_kgLowPassOp_apply_le R x
    have h5 : ‖kgLowPassOp (E := E) R y‖ ≤ ‖y‖ := norm_kgLowPassOp_apply_le R y
    have h6 : Real.exp (b * |s|) ≤ Real.exp (b * |t|) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left habs hb0)
    have h7 : ‖kgFieldMildT (kgBandOpT W R) (kgLowPassOp R x) (kgLowPassOp R y) s‖
        ≤ (‖x‖ + ‖y‖) * Real.exp (b * |t|) := by
      refine h3.trans ?_
      exact mul_le_mul (by linarith) h6 (Real.exp_pos _).le (by positivity)
    have h8 : b * ‖kgFieldMildT (kgBandOpT W R) (kgLowPassOp R x) (kgLowPassOp R y) s‖ ≤ K :=
      by rw [hK]; exact mul_le_mul_of_nonneg_left h7 hb0
    linarith
  have hlim : ∀ᵐ s : ℝ, s ∈ Set.uIoc 0 t →
      Tendsto (fun R : ℝ => kgCosOp (t - s) (kgBandOpT W R s
          (kgFieldMildT (kgBandOpT W R) (kgLowPassOp R x) (kgLowPassOp R y) s))) atTop
        (𝓝 (kgCosOp (t - s) (W s (kgFieldMildT W x y s)))) := by
    filter_upwards with s _
    exact ((kgCosOp (E := E) (t - s)).continuous.tendsto _).comp
      (tendsto_kgBandOpT_source hb0 hWb hWs x y s)
  exact intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (bound := fun _ : ℝ => K) (l := (atTop : Filter ℝ))
    (Eventually.of_forall hmeas) (Eventually.of_forall hdom) hbound hlim

set_option maxHeartbeats 1000000 in
/-- **The Duhamel terms of the gradient converge**, in a moving background. -/
theorem tendsto_integral_kgSinT_band (hb0 : 0 ≤ b) (hWb : ∀ r : ℝ, ‖W r‖ ≤ b)
    (hWs : ∀ z : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r z)
    (x y : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    Tendsto (fun R : ℝ => ∫ s in (0 : ℝ)..t, kgSinOp (t - s) (kgBandOpT W R s
        (kgFieldMildT (kgBandOpT W R) (kgLowPassOp R x) (kgLowPassOp R y) s))) atTop
      (𝓝 (∫ s in (0 : ℝ)..t, kgSinOp (t - s) (W s (kgFieldMildT W x y s)))) := by
  set K : ℝ := b * ((‖x‖ + ‖y‖) * Real.exp (b * |t|)) with hK
  have hK0 : (0 : ℝ) ≤ K := by rw [hK]; positivity
  have hbound : IntervalIntegrable (fun _ : ℝ => K) volume 0 t := intervalIntegrable_const
  have hsrc : ∀ R : ℝ, Continuous fun s : ℝ => kgBandOpT W R s
      (kgFieldMildT (kgBandOpT W R) (kgLowPassOp R x) (kgLowPassOp R y) s) := fun R =>
    continuous_of_strong_comp (norm_kgBandOpT_le hb0 hWb R) (continuous_kgBandOpT_apply hWs R)
      continuous_id (continuous_kgFieldMildT hb0 (norm_kgBandOpT_le hb0 hWb R)
        (continuous_kgBandOpT_apply hWs R) _ _)
  have hmeas : ∀ R : ℝ, AEStronglyMeasurable
      (fun s : ℝ => kgSinOp (t - s) (kgBandOpT W R s
        (kgFieldMildT (kgBandOpT W R) (kgLowPassOp R x) (kgLowPassOp R y) s)))
      (volume.restrict (Set.uIoc 0 t)) := fun R =>
    (continuous_of_strong_comp norm_kgSinOp_le continuous_kgSinOp_apply
      (continuous_const.sub continuous_id) (hsrc R)).aestronglyMeasurable
  have hdom : ∀ R : ℝ, ∀ᵐ s : ℝ, s ∈ Set.uIoc 0 t →
      ‖kgSinOp (t - s) (kgBandOpT W R s
        (kgFieldMildT (kgBandOpT W R) (kgLowPassOp R x) (kgLowPassOp R y) s))‖ ≤ K := by
    intro R
    filter_upwards with s hs
    have habs : |s| ≤ |t| := abs_le_abs_of_mem_uIoc_zero hs
    have h1 := norm_kgSinOp_apply_le (E := E) (t - s) (kgBandOpT W R s
      (kgFieldMildT (kgBandOpT W R) (kgLowPassOp R x) (kgLowPassOp R y) s))
    have h2 : ‖kgBandOpT W R s
        (kgFieldMildT (kgBandOpT W R) (kgLowPassOp R x) (kgLowPassOp R y) s)‖
        ≤ b * ‖kgFieldMildT (kgBandOpT W R) (kgLowPassOp R x) (kgLowPassOp R y) s‖ :=
      (kgBandOpT W R s).le_of_opNorm_le (norm_kgBandOpT_le hb0 hWb R s) _
    have h3 : ‖kgFieldMildT (kgBandOpT W R) (kgLowPassOp R x) (kgLowPassOp R y) s‖
        ≤ (‖kgLowPassOp (E := E) R x‖ + ‖kgLowPassOp (E := E) R y‖) * Real.exp (b * |s|) :=
      norm_kgFieldMildT_le hb0 (norm_kgBandOpT_le hb0 hWb R)
        (continuous_kgBandOpT_apply hWs R) _ _ s
    have h4 : ‖kgLowPassOp (E := E) R x‖ ≤ ‖x‖ := norm_kgLowPassOp_apply_le R x
    have h5 : ‖kgLowPassOp (E := E) R y‖ ≤ ‖y‖ := norm_kgLowPassOp_apply_le R y
    have h6 : Real.exp (b * |s|) ≤ Real.exp (b * |t|) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left habs hb0)
    have h7 : ‖kgFieldMildT (kgBandOpT W R) (kgLowPassOp R x) (kgLowPassOp R y) s‖
        ≤ (‖x‖ + ‖y‖) * Real.exp (b * |t|) := by
      refine h3.trans ?_
      exact mul_le_mul (by linarith) h6 (Real.exp_pos _).le (by positivity)
    have h8 : b * ‖kgFieldMildT (kgBandOpT W R) (kgLowPassOp R x) (kgLowPassOp R y) s‖ ≤ K :=
      by rw [hK]; exact mul_le_mul_of_nonneg_left h7 hb0
    linarith
  have hlim : ∀ᵐ s : ℝ, s ∈ Set.uIoc 0 t →
      Tendsto (fun R : ℝ => kgSinOp (t - s) (kgBandOpT W R s
          (kgFieldMildT (kgBandOpT W R) (kgLowPassOp R x) (kgLowPassOp R y) s))) atTop
        (𝓝 (kgSinOp (t - s) (W s (kgFieldMildT W x y s)))) := by
    filter_upwards with s _
    exact ((kgSinOp (E := E) (t - s)).continuous.tendsto _).comp
      (tendsto_kgBandOpT_source hb0 hWb hWs x y s)
  exact intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (bound := fun _ : ℝ => K) (l := (atTop : Filter ℝ))
    (Eventually.of_forall hmeas) (Eventually.of_forall hdom) hbound hlim

/-- **The velocity converges**, in a moving background. -/
theorem tendsto_kgFieldVelT_band (hb0 : 0 ≤ b) (hWb : ∀ r : ℝ, ‖W r‖ ≤ b)
    (hWs : ∀ z : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r z)
    (g y : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    Tendsto (fun R : ℝ => kgFieldVelT (kgBandOpT W R) (kgLowPassOp R g) (kgLowPassOp R y) t)
      atTop (𝓝 (kgFieldVelT W g y t)) := by
  have halign : ∀ R : ℝ,
      kgFieldVelT (kgBandOpT W R) (kgLowPassOp R g) (kgLowPassOp R y) t
        = -(kgSinOp t (kgLowPassOp R g)) + kgCosOp t (kgLowPassOp R y)
          + ∫ s in (0 : ℝ)..t, kgCosOp (t - s) (kgBandOpT W R s
              (kgFieldMildT (kgBandOpT W R) (kgLowPassOp R (kgFreqInvOp g))
                (kgLowPassOp R y) s)) := by
    intro R
    rw [kgFieldVelT, kgLowPassOp_kgFreqInvOp]
  have hA : Tendsto (fun R : ℝ => -(kgSinOp t (kgLowPassOp (E := E) R g))) atTop
      (𝓝 (-(kgSinOp t g))) :=
    (((kgSinOp (E := E) t).continuous.tendsto g).comp (tendsto_kgLowPassOp_apply g)).neg
  have hB : Tendsto (fun R : ℝ => kgCosOp t (kgLowPassOp (E := E) R y)) atTop
      (𝓝 (kgCosOp t y)) :=
    ((kgCosOp (E := E) t).continuous.tendsto y).comp (tendsto_kgLowPassOp_apply y)
  have hC := tendsto_integral_kgCosT_band hb0 hWb hWs (kgFreqInvOp g) y t
  have hsum := (hA.add hB).add hC
  have hlimval : kgFieldVelT W g y t
      = -(kgSinOp t g) + kgCosOp t y
        + ∫ s in (0 : ℝ)..t, kgCosOp (t - s) (W s (kgFieldMildT W (kgFreqInvOp g) y s)) := rfl
  rw [hlimval]
  exact hsum.congr fun R => (halign R).symm

/-- **The gradient converges**, in a moving background. -/
theorem tendsto_kgFieldGradT_band (hb0 : 0 ≤ b) (hWb : ∀ r : ℝ, ‖W r‖ ≤ b)
    (hWs : ∀ z : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r z)
    (g y : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    Tendsto (fun R : ℝ => kgFieldGradT (kgBandOpT W R) (kgLowPassOp R g) (kgLowPassOp R y) t)
      atTop (𝓝 (kgFieldGradT W g y t)) := by
  have halign : ∀ R : ℝ,
      kgFieldGradT (kgBandOpT W R) (kgLowPassOp R g) (kgLowPassOp R y) t
        = kgCosOp t (kgLowPassOp R g) + kgSinOp t (kgLowPassOp R y)
          + ∫ s in (0 : ℝ)..t, kgSinOp (t - s) (kgBandOpT W R s
              (kgFieldMildT (kgBandOpT W R) (kgLowPassOp R (kgFreqInvOp g))
                (kgLowPassOp R y) s)) := by
    intro R
    rw [kgFieldGradT, kgLowPassOp_kgFreqInvOp]
  have hA : Tendsto (fun R : ℝ => kgCosOp t (kgLowPassOp (E := E) R g)) atTop
      (𝓝 (kgCosOp t g)) :=
    ((kgCosOp (E := E) t).continuous.tendsto g).comp (tendsto_kgLowPassOp_apply g)
  have hB : Tendsto (fun R : ℝ => kgSinOp t (kgLowPassOp (E := E) R y)) atTop
      (𝓝 (kgSinOp t y)) :=
    ((kgSinOp (E := E) t).continuous.tendsto y).comp (tendsto_kgLowPassOp_apply y)
  have hC := tendsto_integral_kgSinT_band hb0 hWb hWs (kgFreqInvOp g) y t
  have hsum := (hA.add hB).add hC
  have hlimval : kgFieldGradT W g y t
      = kgCosOp t g + kgSinOp t y
        + ∫ s in (0 : ℝ)..t, kgSinOp (t - s) (W s (kgFieldMildT W (kgFreqInvOp g) y s)) := rfl
  rw [hlimval]
  exact hsum.congr fun R => (halign R).symm

/-- **The state converges in the energy space**, in a moving background. -/
theorem tendsto_kgFieldStateT_band (hb0 : 0 ≤ b) (hWb : ∀ r : ℝ, ‖W r‖ ≤ b)
    (hWs : ∀ z : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r z)
    (g y : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    Tendsto (fun R : ℝ => kgFieldStateT (kgBandOpT W R) (kgLowPassOp R g) (kgLowPassOp R y) t)
      atTop (𝓝 (kgFieldStateT W g y t)) :=
  ((kgPair E).continuous.tendsto (kgFieldGradT W g y t, kgFieldVelT W g y t)).comp
    ((tendsto_kgFieldGradT_band hb0 hWb hWs g y t).prodMk_nhds
      (tendsto_kgFieldVelT_band hb0 hWb hWs g y t))

/-- **The energy converges**, in a moving background: the estimate of statement 186 is a statement
about the original equation, not only about the compressed one. -/
theorem tendsto_kgFieldEnergyT_band (hb0 : 0 ≤ b) (hWb : ∀ r : ℝ, ‖W r‖ ≤ b)
    (hWs : ∀ z : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r z)
    (g y : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    Tendsto (fun R : ℝ =>
        ‖kgFieldGradT (kgBandOpT W R) (kgLowPassOp R g) (kgLowPassOp R y) t‖ ^ (2 : ℕ)
          + ‖kgFieldVelT (kgBandOpT W R) (kgLowPassOp R g) (kgLowPassOp R y) t‖ ^ (2 : ℕ)) atTop
      (𝓝 (‖kgFieldGradT W g y t‖ ^ (2 : ℕ) + ‖kgFieldVelT W g y t‖ ^ (2 : ℕ))) :=
  (((tendsto_kgFieldGradT_band hb0 hWb hWs g y t).norm).pow 2).add
    (((tendsto_kgFieldVelT_band hb0 hWb hWs g y t).norm).pow 2)

end StateT

end GaloisForLFunctions.HTGeometry
