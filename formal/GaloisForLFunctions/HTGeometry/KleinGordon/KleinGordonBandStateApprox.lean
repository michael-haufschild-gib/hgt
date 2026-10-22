import GaloisForLFunctions.HTGeometry.KleinGordon.KleinGordonBandApproximation

/-!
# The whole state converges, not only the field

Statement 236 says the band solutions converge to the true solution. A clock reads the state — the
field *and* its velocity — so the approximation is only as good as the convergence of both.

The velocity is the sum of two propagator terms in the data and one Duhamel integral. The first two
converge because the data do and the propagators are contractions. For the third, the integrand
`cos((t−s)⟨D⟩)W_R u_R(s)` converges pointwise, because

`W_R u_R(s) − W u(s) = (W_R − W)u(s) + W_R(u_R(s) − u(s))`

and both terms vanish — the first by the strong convergence of the band compressions, the second by
statement 236 — while the whole integrand is bounded by a constant on the interval. Dominated
convergence does the rest.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

private theorem fourierMul_comp_apply'' {φ ψ χ : E → ℂ} (hφ : Measurable φ) (hψ : Measurable ψ)
    (hχ : Measurable χ) {C D B : ℝ} (hC0 : 0 ≤ C) (hC : ∀ ξ, ‖φ ξ‖ ≤ C) (hD0 : 0 ≤ D)
    (hD : ∀ ξ, ‖ψ ξ‖ ≤ D) (hB0 : 0 ≤ B) (hB : ∀ ξ, ‖χ ξ‖ ≤ B)
    (hae : ∀ ξ, χ ξ = φ ξ * ψ ξ) (x : Lp ℂ 2 (volume : Measure E)) :
    fourierMulCLM hφ hC0 hC (fourierMulCLM hψ hD0 hD x) = fourierMulCLM hχ hB0 hB x :=
  congrArg (fun T : Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E) => T x)
    (fourierMulCLM_comp hφ hψ hχ hC0 hC hD0 hD hB0 hB (Filter.Eventually.of_forall hae))

/-- The projection commutes with the inverse frequency. -/
theorem kgLowPassOp_kgFreqInvOp (R : ℝ) (z : Lp ℂ 2 (volume : Measure E)) :
    kgLowPassOp R (kgFreqInvOp z) = kgFreqInvOp (kgLowPassOp R z) := by
  have hmeas : Measurable fun ξ : E => kgLowPass R ξ * kgFreqInv ξ :=
    (measurable_kgLowPass R).mul (measurable_kgFreqInv (E := E))
  have hbd : ∀ ξ : E, ‖kgLowPass R ξ * kgFreqInv ξ‖ ≤ 1 := by
    intro ξ
    rw [norm_mul]
    have h1 := norm_kgLowPass_le R ξ
    have h2 := norm_kgFreqInv_le (E := E) ξ
    nlinarith [norm_nonneg (kgLowPass R ξ), norm_nonneg (kgFreqInv (E := E) ξ)]
  have hL : kgLowPassOp (E := E) R (kgFreqInvOp z) = fourierMulCLM hmeas zero_le_one hbd z := by
    rw [kgLowPassOp_eq, kgFreqInvOp_eq]
    exact fourierMul_comp_apply'' _ _ hmeas _ _ _ _ zero_le_one hbd (fun _ => rfl) z
  have hRgt : kgFreqInvOp (E := E) (kgLowPassOp R z) = fourierMulCLM hmeas zero_le_one hbd z := by
    rw [kgLowPassOp_eq, kgFreqInvOp_eq]
    exact fourierMul_comp_apply'' _ _ hmeas _ _ _ _ zero_le_one hbd (fun ξ => mul_comm _ _) z
  rw [hL, hRgt]

section StateApprox

variable {W₀ : Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E)} {b : ℝ}

/-- **The perturbed sources converge.** -/
theorem tendsto_kgBandOp_source (hb0 : 0 ≤ b) (hW : ‖W₀‖ ≤ b)
    (x y : Lp ℂ 2 (volume : Measure E)) (s : ℝ) :
    Tendsto (fun R : ℝ => kgBandOp W₀ R
        (kgFieldMild (kgBandOp W₀ R) (kgLowPassOp R x) (kgLowPassOp R y) s)) atTop
      (𝓝 (W₀ (kgFieldMild W₀ x y s))) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hsol := (tendsto_iff_norm_sub_tendsto_zero).mp
    (tendsto_kgFieldMild_band hb0 hW x y s)
  have hop := (tendsto_iff_norm_sub_tendsto_zero).mp
    (tendsto_kgBandOp_apply (W₀ := W₀) (kgFieldMild W₀ x y s))
  have hle : ∀ R : ℝ, ‖kgBandOp W₀ R
        (kgFieldMild (kgBandOp W₀ R) (kgLowPassOp R x) (kgLowPassOp R y) s)
          - W₀ (kgFieldMild W₀ x y s)‖
      ≤ b * ‖kgFieldMild (kgBandOp W₀ R) (kgLowPassOp R x) (kgLowPassOp R y) s
            - kgFieldMild W₀ x y s‖
        + ‖kgBandOp W₀ R (kgFieldMild W₀ x y s) - W₀ (kgFieldMild W₀ x y s)‖ := by
    intro R
    have hsplit : kgBandOp W₀ R
          (kgFieldMild (kgBandOp W₀ R) (kgLowPassOp R x) (kgLowPassOp R y) s)
            - W₀ (kgFieldMild W₀ x y s)
        = kgBandOp W₀ R (kgFieldMild (kgBandOp W₀ R) (kgLowPassOp R x) (kgLowPassOp R y) s
            - kgFieldMild W₀ x y s)
          + (kgBandOp W₀ R (kgFieldMild W₀ x y s) - W₀ (kgFieldMild W₀ x y s)) := by
      rw [map_sub]
      abel
    rw [hsplit]
    refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
    exact (kgBandOp W₀ R).le_of_opNorm_le (norm_kgBandOp_le hb0 hW R) _
  have hsum : Tendsto (fun R : ℝ => b * ‖kgFieldMild (kgBandOp W₀ R) (kgLowPassOp R x)
        (kgLowPassOp R y) s - kgFieldMild W₀ x y s‖
      + ‖kgBandOp W₀ R (kgFieldMild W₀ x y s) - W₀ (kgFieldMild W₀ x y s)‖) atTop (𝓝 0) := by
    simpa using (hsol.const_mul b).add hop
  exact squeeze_zero (fun _ => norm_nonneg _) hle hsum

/-- **The Duhamel terms converge.** -/
theorem tendsto_integral_kgCos_band (hb0 : 0 ≤ b) (hW : ‖W₀‖ ≤ b)
    (x y : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    Tendsto (fun R : ℝ => ∫ s in (0 : ℝ)..t, kgCosOp (t - s) (kgBandOp W₀ R
        (kgFieldMild (kgBandOp W₀ R) (kgLowPassOp R x) (kgLowPassOp R y) s))) atTop
      (𝓝 (∫ s in (0 : ℝ)..t, kgCosOp (t - s) (W₀ (kgFieldMild W₀ x y s)))) := by
  set K : ℝ := b * ((‖x‖ + ‖y‖) * Real.exp (b * |t|)) with hK
  have hK0 : (0 : ℝ) ≤ K := by rw [hK]; positivity
  have hbound : IntervalIntegrable (fun _ : ℝ => K) volume 0 t := intervalIntegrable_const
  have hmeas : ∀ R : ℝ, AEStronglyMeasurable
      (fun s : ℝ => kgCosOp (t - s) (kgBandOp W₀ R
        (kgFieldMild (kgBandOp W₀ R) (kgLowPassOp R x) (kgLowPassOp R y) s)))
      (volume.restrict (Set.uIoc 0 t)) := by
    intro R
    refine (continuous_kgCosOp_comp (continuous_const.sub continuous_id)
      ((kgBandOp W₀ R).continuous.comp (continuous_kgFieldMild hb0
        (norm_kgBandOp_le hb0 hW R) _ _))).aestronglyMeasurable
  have hdom : ∀ R : ℝ, ∀ᵐ s : ℝ, s ∈ Set.uIoc 0 t →
      ‖kgCosOp (t - s) (kgBandOp W₀ R
        (kgFieldMild (kgBandOp W₀ R) (kgLowPassOp R x) (kgLowPassOp R y) s))‖ ≤ K := by
    intro R
    filter_upwards with s hs
    have habs : |s| ≤ |t| := abs_le_abs_of_mem_uIoc_zero hs
    have h1 := norm_kgCosOp_apply_le (E := E) (t - s) (kgBandOp W₀ R
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
      Tendsto (fun R : ℝ => kgCosOp (t - s) (kgBandOp W₀ R
          (kgFieldMild (kgBandOp W₀ R) (kgLowPassOp R x) (kgLowPassOp R y) s))) atTop
        (𝓝 (kgCosOp (t - s) (W₀ (kgFieldMild W₀ x y s)))) := by
    filter_upwards with s _
    exact ((kgCosOp (E := E) (t - s)).continuous.tendsto _).comp
      (tendsto_kgBandOp_source hb0 hW x y s)
  exact intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (bound := fun _ : ℝ => K) (l := (atTop : Filter ℝ))
    (Eventually.of_forall hmeas) (Eventually.of_forall hdom) hbound hlim

/-- **The whole state converges.** The velocity of the band solution converges to the velocity of the
true one, so the band approximation is faithful on the state a clock reads. -/
theorem tendsto_kgFieldVel_band (hb0 : 0 ≤ b) (hW : ‖W₀‖ ≤ b)
    (g y : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    Tendsto (fun R : ℝ => kgFieldVel (kgBandOp W₀ R) (kgLowPassOp R g) (kgLowPassOp R y) t)
      atTop (𝓝 (kgFieldVel W₀ g y t)) := by
  have halign : ∀ R : ℝ,
      kgFieldVel (kgBandOp W₀ R) (kgLowPassOp R g) (kgLowPassOp R y) t
        = -(kgSinOp t (kgLowPassOp R g)) + kgCosOp t (kgLowPassOp R y)
          + ∫ s in (0 : ℝ)..t, kgCosOp (t - s) (kgBandOp W₀ R
              (kgFieldMild (kgBandOp W₀ R) (kgLowPassOp R (kgFreqInvOp g))
                (kgLowPassOp R y) s)) := by
    intro R
    rw [kgFieldVel, kgLowPassOp_kgFreqInvOp]
  have hA : Tendsto (fun R : ℝ => -(kgSinOp t (kgLowPassOp (E := E) R g))) atTop
      (𝓝 (-(kgSinOp t g))) :=
    (((kgSinOp (E := E) t).continuous.tendsto g).comp (tendsto_kgLowPassOp_apply g)).neg
  have hB : Tendsto (fun R : ℝ => kgCosOp t (kgLowPassOp (E := E) R y)) atTop
      (𝓝 (kgCosOp t y)) :=
    ((kgCosOp (E := E) t).continuous.tendsto y).comp (tendsto_kgLowPassOp_apply y)
  have hC := tendsto_integral_kgCos_band hb0 hW (kgFreqInvOp g) y t
  have hsum := (hA.add hB).add hC
  have hlimval : kgFieldVel W₀ g y t
      = -(kgSinOp t g) + kgCosOp t y
        + ∫ s in (0 : ℝ)..t, kgCosOp (t - s) (W₀ (kgFieldMild W₀ (kgFreqInvOp g) y s)) := rfl
  rw [hlimval]
  exact hsum.congr fun R => (halign R).symm

end StateApprox

end GaloisForLFunctions.HTGeometry
