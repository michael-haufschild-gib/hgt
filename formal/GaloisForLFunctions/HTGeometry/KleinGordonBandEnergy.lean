import GaloisForLFunctions.HTGeometry.KleinGordonBandWellPosed

/-!
# The conserved energy on a band, in concrete terms

The energy thread carries the gradient of the solution as an abstract closed-form expression
`kgFieldGrad`, defined so that dividing it by the frequency returns the solution. On a band it is
literally `⟨D⟩_R u`, the band-restricted frequency applied to the solution — a bounded operator
applied to the state, with nothing abstract left.

With that identification the conservation law of statement 189 reads, for a real potential compressed
to the band,

`‖⟨D⟩_R u(t)‖² + ‖∂ₜu(t)‖² − ∫V|u(t)|² = ‖⟨D⟩_R u(0)‖² + ‖∂ₜu(0)‖² − ∫V|u(0)|²`,

which is the classical conserved energy of the Klein–Gordon field in a potential, with every term a
quantity of the solution itself.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

set_option maxHeartbeats 1000000 in
private theorem fourierMul_comp_apply' {φ ψ χ : E → ℂ} (hφ : Measurable φ) (hψ : Measurable ψ)
    (hχ : Measurable χ) {C D B : ℝ} (hC0 : 0 ≤ C) (hC : ∀ ξ, ‖φ ξ‖ ≤ C) (hD0 : 0 ≤ D)
    (hD : ∀ ξ, ‖ψ ξ‖ ≤ D) (hB0 : 0 ≤ B) (hB : ∀ ξ, ‖χ ξ‖ ≤ B)
    (hae : ∀ ξ, χ ξ = φ ξ * ψ ξ) (x : Lp ℂ 2 (volume : Measure E)) :
    fourierMulCLM hφ hC0 hC (fourierMulCLM hψ hD0 hD x) = fourierMulCLM hχ hB0 hB x :=
  congrArg (fun T : Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E) => T x)
    (fourierMulCLM_comp hφ hψ hχ hC0 hC hD0 hD hB0 hB (Filter.Eventually.of_forall hae))

/-- **The band-restricted frequency turns the half-order propagator into the sine one.** -/
theorem kgFreqLowOp_kgSinFreqOp (t R : ℝ) (x : Lp ℂ 2 (volume : Measure E)) :
    kgFreqLowOp R (kgSinFreqOp t x) = kgSinOp t (kgLowPassOp R x) := by
  have hmeas : Measurable fun ξ : E => kgSinPhase t ξ * kgLowPass R ξ :=
    (measurable_kgSinPhase t).mul (measurable_kgLowPass R)
  have hbd : ∀ ξ : E, ‖kgSinPhase t ξ * kgLowPass R ξ‖ ≤ 1 := by
    intro ξ
    rw [norm_mul]
    have h1 := norm_kgSinPhase_le t ξ
    have h2 := norm_kgLowPass_le R ξ
    nlinarith [norm_nonneg (kgSinPhase t ξ), norm_nonneg (kgLowPass R ξ)]
  have hL : kgFreqLowOp (E := E) R (kgSinFreqOp t x)
      = fourierMulCLM hmeas zero_le_one hbd x := by
    rw [kgSinFreqOp_eq, kgFreqLowOp]
    refine fourierMul_comp_apply' _ _ hmeas _ _ _ _ zero_le_one hbd (fun ξ => ?_) x
    have hpos := kgFreq_pos ξ
    have hne : ((kgFreq ξ : ℝ) : ℂ) ≠ 0 := by simpa using hpos.ne'
    rw [kgSinPhase, kgFreqLow, kgSinOverFreq]
    by_cases hξ : ‖ξ‖ ≤ R
    · rw [kgLowPass, if_pos hξ]
      push_cast
      field_simp
    · rw [kgLowPass, if_neg hξ]
      simp
  have hRgt : kgSinOp (E := E) t (kgLowPassOp R x) = fourierMulCLM hmeas zero_le_one hbd x := by
    rw [kgSinOp_eq, kgLowPassOp_eq]
    exact fourierMul_comp_apply' _ _ hmeas _ _ _ _ zero_le_one hbd (fun _ => rfl) x
  rw [hL, hRgt]

section BandGradient

variable {W₀ : Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E)} {b : ℝ}

set_option maxHeartbeats 1000000 in
/-- **On a band the abstract gradient is the band-restricted frequency of the solution.** -/
theorem kgFieldGrad_band (hb0 : 0 ≤ b) (hW : ‖W₀‖ ≤ b) (R : ℝ)
    (x y : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    kgFieldGrad (kgBandOp W₀ R) (kgFreqLowOp R x) (kgLowPassOp R y) t
      = kgFreqLowOp R (kgFieldMild (kgBandOp W₀ R) (kgFreqInvOp (kgFreqLowOp R x))
          (kgLowPassOp R y) t) := by
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
  have hfree : kgFreqLowOp R (kgCosOp t (kgFreqInvOp (kgFreqLowOp (E := E) R x)))
      = kgCosOp t (kgFreqLowOp R x) := by
    rw [kgFreqInvOp_kgFreqLowOp, ← kgCosOp_kgFreqLowOp, kgFreqLowOp_kgLowPassOp]
  have hvel : kgFreqLowOp R (kgSinFreqOp t (kgLowPassOp (E := E) R y))
      = kgSinOp t (kgLowPassOp R y) := by
    rw [kgFreqLowOp_kgSinFreqOp, kgLowPassOp_idem]
  have hpt : ∀ s ∈ Set.uIcc (0 : ℝ) t,
      kgFreqLowOp R (kgSinFreqOp (t - s) (kgBandOp W₀ R
          (kgFieldMild (kgBandOp W₀ R) (kgFreqInvOp (kgFreqLowOp R x)) (kgLowPassOp R y) s)))
        = kgSinOp (t - s) (kgBandOp W₀ R
            (kgFieldMild (kgBandOp W₀ R) (kgFreqInvOp (kgFreqLowOp R x))
              (kgLowPassOp R y) s)) := by
    intro s _
    rw [kgFreqLowOp_kgSinFreqOp, kgBandOp_ran]
  rw [kgFieldMild_eq hb0 hWb _ _ t, hker, map_add, kgFieldFree, map_add, hfree, hvel,
    ← ContinuousLinearMap.intervalIntegral_comp_comm _ hI,
    intervalIntegral.integral_congr hpt, kgFieldGrad]

end BandGradient

/-! ## The classical conserved energy -/

section BandReal

variable {V : E → ℝ} {bV : ℝ}

/-- **The conserved energy of the band solution, in concrete terms.** Every term is a quantity of the
solution itself: the band-restricted gradient, the velocity, and the potential energy. -/
theorem kgBandReal_energy_conserved (hV : Measurable V) (hbV0 : 0 ≤ bV)
    (hbV : ∀ a : E, |V a| ≤ bV) (R : ℝ) (x y : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    ‖kgFreqLowOp R (kgFieldMild (kgBandOp (kgMulOp hV hbV0 hbV) R)
          (kgFreqInvOp (kgFreqLowOp R x)) (kgLowPassOp R y) t)‖ ^ (2 : ℕ)
        + ‖kgFieldVel (kgBandOp (kgMulOp hV hbV0 hbV) R) (kgFreqLowOp R x)
            (kgLowPassOp R y) t‖ ^ (2 : ℕ)
        - RCLike.re (inner ℂ (kgBandOp (kgMulOp hV hbV0 hbV) R
            (kgFieldMild (kgBandOp (kgMulOp hV hbV0 hbV) R) (kgFreqInvOp (kgFreqLowOp R x))
              (kgLowPassOp R y) t))
          (kgFieldMild (kgBandOp (kgMulOp hV hbV0 hbV) R) (kgFreqInvOp (kgFreqLowOp R x))
            (kgLowPassOp R y) t))
      = ‖kgFreqLowOp R x‖ ^ (2 : ℕ) + ‖kgLowPassOp R y‖ ^ (2 : ℕ)
        - RCLike.re (inner ℂ (kgBandOp (kgMulOp hV hbV0 hbV) R
            (kgFreqInvOp (kgFreqLowOp R x))) (kgFreqInvOp (kgFreqLowOp R x))) := by
  have hgrad := kgFieldGrad_band hbV0 (norm_kgMulOp_le hV hbV0 hbV) R x y t
  rw [← hgrad]
  exact kgBandOp_real_energy_conserved hV hbV0 hbV R (kgFreqLowOp R x) (kgLowPassOp R y) t

end BandReal

end GaloisForLFunctions.HTGeometry
