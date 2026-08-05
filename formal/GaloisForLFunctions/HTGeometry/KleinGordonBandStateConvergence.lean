import GaloisForLFunctions.HTGeometry.KleinGordonBandStateApprox

/-!
# The energy of the band solution converges

The state carried by the energy estimate is the pair `(⟨D⟩u, ∂ₜu)`, and its norm squared is the
energy. The velocity converges by statement 240; the gradient is the same Duhamel formula with the
sine propagator in place of the cosine, so it converges for the same reason. The two together give
convergence of the state in the energy space, and hence of the energy itself:

`‖⟨D⟩u_R(t)‖² + ‖∂ₜu_R(t)‖² → ‖⟨D⟩u(t)‖² + ‖∂ₜu(t)‖²`.

The sharp estimate of statement 182 therefore passes to the limit: what the band theory says about
the energy is what holds for the original equation.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

section StateConvergence

variable {W₀ : Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E)} {b : ℝ}

set_option maxHeartbeats 1000000 in
/-- **The Duhamel terms of the gradient converge.** -/
theorem tendsto_integral_kgSin_band (hb0 : 0 ≤ b) (hW : ‖W₀‖ ≤ b)
    (x y : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    Tendsto (fun R : ℝ => ∫ s in (0 : ℝ)..t, kgSinOp (t - s) (kgBandOp W₀ R
        (kgFieldMild (kgBandOp W₀ R) (kgLowPassOp R x) (kgLowPassOp R y) s))) atTop
      (𝓝 (∫ s in (0 : ℝ)..t, kgSinOp (t - s) (W₀ (kgFieldMild W₀ x y s)))) := by
  set K : ℝ := b * ((‖x‖ + ‖y‖) * Real.exp (b * |t|)) with hK
  have hK0 : (0 : ℝ) ≤ K := by rw [hK]; positivity
  have hbound : IntervalIntegrable (fun _ : ℝ => K) volume 0 t := intervalIntegrable_const
  have hmeas : ∀ R : ℝ, AEStronglyMeasurable
      (fun s : ℝ => kgSinOp (t - s) (kgBandOp W₀ R
        (kgFieldMild (kgBandOp W₀ R) (kgLowPassOp R x) (kgLowPassOp R y) s)))
      (volume.restrict (Set.uIoc 0 t)) := by
    intro R
    exact (continuous_of_strong_comp norm_kgSinOp_le continuous_kgSinOp_apply
      (continuous_const.sub continuous_id)
      ((kgBandOp W₀ R).continuous.comp (continuous_kgFieldMild hb0
        (norm_kgBandOp_le hb0 hW R) _ _))).aestronglyMeasurable
  have hdom : ∀ R : ℝ, ∀ᵐ s : ℝ, s ∈ Set.uIoc 0 t →
      ‖kgSinOp (t - s) (kgBandOp W₀ R
        (kgFieldMild (kgBandOp W₀ R) (kgLowPassOp R x) (kgLowPassOp R y) s))‖ ≤ K := by
    intro R
    filter_upwards with s hs
    have habs : |s| ≤ |t| := abs_le_abs_of_mem_uIoc_zero hs
    have h1 := norm_kgSinOp_apply_le (E := E) (t - s) (kgBandOp W₀ R
      (kgFieldMild (kgBandOp W₀ R) (kgLowPassOp R x) (kgLowPassOp R y) s))
    have h2 : ‖kgBandOp W₀ R (kgFieldMild (kgBandOp W₀ R) (kgLowPassOp R x)
        (kgLowPassOp R y) s)‖
        ≤ b * ‖kgFieldMild (kgBandOp W₀ R) (kgLowPassOp R x) (kgLowPassOp R y) s‖ :=
      (kgBandOp W₀ R).le_of_opNorm_le (norm_kgBandOp_le hb0 hW R) _
    have h3 : ‖kgFieldMild (kgBandOp W₀ R) (kgLowPassOp R x) (kgLowPassOp R y) s‖
        ≤ (‖kgLowPassOp (E := E) R x‖ + ‖kgLowPassOp (E := E) R y‖) * Real.exp (b * |s|) :=
      norm_kgFieldMild_le hb0 (norm_kgBandOp_le hb0 hW R) _ _ s
    have h4 : ‖kgLowPassOp (E := E) R x‖ ≤ ‖x‖ := norm_kgLowPassOp_apply_le R x
    have h5 : ‖kgLowPassOp (E := E) R y‖ ≤ ‖y‖ := norm_kgLowPassOp_apply_le R y
    have h6 : Real.exp (b * |s|) ≤ Real.exp (b * |t|) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left habs hb0)
    have h7 : ‖kgFieldMild (kgBandOp W₀ R) (kgLowPassOp R x) (kgLowPassOp R y) s‖
        ≤ (‖x‖ + ‖y‖) * Real.exp (b * |t|) := by
      refine h3.trans ?_
      exact mul_le_mul (by linarith) h6 (Real.exp_pos _).le (by positivity)
    have h8 : b * ‖kgFieldMild (kgBandOp W₀ R) (kgLowPassOp R x) (kgLowPassOp R y) s‖ ≤ K :=
      by rw [hK]; exact mul_le_mul_of_nonneg_left h7 hb0
    linarith
  have hlim : ∀ᵐ s : ℝ, s ∈ Set.uIoc 0 t →
      Tendsto (fun R : ℝ => kgSinOp (t - s) (kgBandOp W₀ R
          (kgFieldMild (kgBandOp W₀ R) (kgLowPassOp R x) (kgLowPassOp R y) s))) atTop
        (𝓝 (kgSinOp (t - s) (W₀ (kgFieldMild W₀ x y s)))) := by
    filter_upwards with s _
    exact ((kgSinOp (E := E) (t - s)).continuous.tendsto _).comp
      (tendsto_kgBandOp_source hb0 hW x y s)
  exact intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (bound := fun _ : ℝ => K) (l := (atTop : Filter ℝ))
    (Eventually.of_forall hmeas) (Eventually.of_forall hdom) hbound hlim

/-- **The gradient of the band solution converges.** -/
theorem tendsto_kgFieldGrad_band (hb0 : 0 ≤ b) (hW : ‖W₀‖ ≤ b)
    (g y : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    Tendsto (fun R : ℝ => kgFieldGrad (kgBandOp W₀ R) (kgLowPassOp R g) (kgLowPassOp R y) t)
      atTop (𝓝 (kgFieldGrad W₀ g y t)) := by
  have halign : ∀ R : ℝ,
      kgFieldGrad (kgBandOp W₀ R) (kgLowPassOp R g) (kgLowPassOp R y) t
        = kgCosOp t (kgLowPassOp R g) + kgSinOp t (kgLowPassOp R y)
          + ∫ s in (0 : ℝ)..t, kgSinOp (t - s) (kgBandOp W₀ R
              (kgFieldMild (kgBandOp W₀ R) (kgLowPassOp R (kgFreqInvOp g))
                (kgLowPassOp R y) s)) := by
    intro R
    rw [kgFieldGrad, kgLowPassOp_kgFreqInvOp]
  have hA : Tendsto (fun R : ℝ => kgCosOp t (kgLowPassOp (E := E) R g)) atTop
      (𝓝 (kgCosOp t g)) :=
    ((kgCosOp (E := E) t).continuous.tendsto g).comp (tendsto_kgLowPassOp_apply g)
  have hB : Tendsto (fun R : ℝ => kgSinOp t (kgLowPassOp (E := E) R y)) atTop
      (𝓝 (kgSinOp t y)) :=
    ((kgSinOp (E := E) t).continuous.tendsto y).comp (tendsto_kgLowPassOp_apply y)
  have hC := tendsto_integral_kgSin_band hb0 hW (kgFreqInvOp g) y t
  have hsum := (hA.add hB).add hC
  have hlimval : kgFieldGrad W₀ g y t
      = kgCosOp t g + kgSinOp t y
        + ∫ s in (0 : ℝ)..t, kgSinOp (t - s) (W₀ (kgFieldMild W₀ (kgFreqInvOp g) y s)) := rfl
  rw [hlimval]
  exact hsum.congr fun R => (halign R).symm

/-- **The state of the band solution converges in the energy space.** -/
theorem tendsto_kgFieldState_band (hb0 : 0 ≤ b) (hW : ‖W₀‖ ≤ b)
    (g y : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    Tendsto (fun R : ℝ => kgFieldState (kgBandOp W₀ R) (kgLowPassOp R g) (kgLowPassOp R y) t)
      atTop (𝓝 (kgFieldState W₀ g y t)) :=
  ((kgPair E).continuous.tendsto (kgFieldGrad W₀ g y t, kgFieldVel W₀ g y t)).comp
    ((tendsto_kgFieldGrad_band hb0 hW g y t).prodMk_nhds
      (tendsto_kgFieldVel_band hb0 hW g y t))

/-- **The energy of the band solution converges to the energy of the true solution.** The sharp
estimate of statement 182 therefore passes to the limit: it is a statement about the original
equation, not only about the compressed one. -/
theorem tendsto_kgFieldEnergy_band (hb0 : 0 ≤ b) (hW : ‖W₀‖ ≤ b)
    (g y : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    Tendsto (fun R : ℝ =>
        ‖kgFieldGrad (kgBandOp W₀ R) (kgLowPassOp R g) (kgLowPassOp R y) t‖ ^ 2
          + ‖kgFieldVel (kgBandOp W₀ R) (kgLowPassOp R g) (kgLowPassOp R y) t‖ ^ 2) atTop
      (𝓝 (‖kgFieldGrad W₀ g y t‖ ^ 2 + ‖kgFieldVel W₀ g y t‖ ^ 2)) :=
  (((tendsto_kgFieldGrad_band hb0 hW g y t).norm).pow 2).add
    (((tendsto_kgFieldVel_band hb0 hW g y t).norm).pow 2)

end StateConvergence

end GaloisForLFunctions.HTGeometry
