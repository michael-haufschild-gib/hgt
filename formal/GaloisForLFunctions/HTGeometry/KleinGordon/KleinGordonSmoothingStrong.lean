import GaloisForLFunctions.HTGeometry.KleinGordon.KleinGordonDuhamelSecondDerivative

/-!
# A smoothing perturbation makes the mild solution strong

The card records the obstruction: a mild solution with a merely bounded potential need not be a
strong one, because the second differentiation of the Duhamel term produces `⟨D⟩ sin((t-s)⟨D⟩)Wu(s)`
and nothing absorbs the `⟨D⟩`. Statement 102 shows what does absorb it — a factor `⟨D⟩⁻¹` in the
perturbation itself.

For `W = ⟨D⟩⁻¹W₀` with `W₀` bounded, and Cauchy data `⟨D⟩⁻²g₀`, `⟨D⟩⁻¹h₀`, the field-level mild
solution is twice differentiable and satisfies the equation in the strong sense:

`⟨D⟩⁻²(∂ₜ²u) = -u + ⟨D⟩⁻²(Wu)`.

So the estimate, uniqueness and stability of statements 74–80 apply to a solution that is
*constructed*, not merely assumed — the two halves of the perturbed theory meet.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-! ## The smoothing perturbation -/

/-- A **smoothing perturbation**: a bounded operator composed with `⟨D⟩⁻¹`. -/
def kgSmoothingOp (W₀ : Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E)) :
    Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E) :=
  (kgFreqInvOp).comp W₀

theorem kgSmoothingOp_apply (W₀ : Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E))
    (x : Lp ℂ 2 (volume : Measure E)) : kgSmoothingOp W₀ x = kgFreqInvOp (W₀ x) := rfl

theorem norm_kgSmoothingOp_le {W₀ : Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E)}
    {b : ℝ} (hW : ‖W₀‖ ≤ b) : ‖kgSmoothingOp W₀‖ ≤ b := by
  rw [kgSmoothingOp]
  refine le_trans (ContinuousLinearMap.opNorm_comp_le _ _) ?_
  have h := mul_le_mul (norm_kgFreqInvOp_le (E := E)) hW (norm_nonneg _) zero_le_one
  rwa [one_mul] at h

/-- The half-order propagator on a regular vector gains two powers of `⟨D⟩⁻¹`. -/
theorem kgSinFreqOp_freqInv (t : ℝ) (x : Lp ℂ 2 (volume : Measure E)) :
    kgSinFreqOp t (kgFreqInvOp x) = kgFreqInvOp (kgFreqInvOp (kgSinOp t x)) := by
  rw [kgSinFreqOp_apply_freqInv, ← kgFreqInvOp_kgSinOp]

/-! ## The solution and its two derivatives -/

section Solution

variable {W₀ : Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E)} {b : ℝ}

/-- The mild solution driven by a smoothing perturbation, with doubly regular position datum. -/
def kgSmoothMild (W₀ : Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E))
    (g₀ h₀ : Lp ℂ 2 (volume : Measure E)) : ℝ → Lp ℂ 2 (volume : Measure E) :=
  kgFieldMild (kgSmoothingOp W₀) (kgFreqInvOp (kgFreqInvOp g₀)) (kgFreqInvOp h₀)

/-- Its velocity. -/
def kgSmoothVel (W₀ : Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E))
    (g₀ h₀ : Lp ℂ 2 (volume : Measure E)) (t : ℝ) : Lp ℂ 2 (volume : Measure E) :=
  -(kgSinOp t (kgFreqInvOp g₀)) + kgCosOp t (kgFreqInvOp h₀)
    + ∫ s in (0 : ℝ)..t, kgCosOp (t - s) (kgFreqInvOp (W₀ (kgSmoothMild W₀ g₀ h₀ s)))

/-- Its acceleration. -/
def kgSmoothAcc (W₀ : Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E))
    (g₀ h₀ : Lp ℂ 2 (volume : Measure E)) (t : ℝ) : Lp ℂ 2 (volume : Measure E) :=
  -(kgCosOp t g₀) + -(kgSinOp t h₀)
    + (kgFreqInvOp (W₀ (kgSmoothMild W₀ g₀ h₀ t))
      - ∫ s in (0 : ℝ)..t, kgSinOp (t - s) (W₀ (kgSmoothMild W₀ g₀ h₀ s)))

theorem continuous_kgSmoothMild (hb0 : 0 ≤ b) (hW : ‖W₀‖ ≤ b)
    (g₀ h₀ : Lp ℂ 2 (volume : Measure E)) : Continuous (kgSmoothMild W₀ g₀ h₀) :=
  continuous_kgFieldMild hb0 (norm_kgSmoothingOp_le hW) _ _

theorem continuous_kgSmoothSource (hb0 : 0 ≤ b) (hW : ‖W₀‖ ≤ b)
    (g₀ h₀ : Lp ℂ 2 (volume : Measure E)) :
    Continuous fun s : ℝ => W₀ (kgSmoothMild W₀ g₀ h₀ s) :=
  W₀.continuous.comp (continuous_kgSmoothMild hb0 hW g₀ h₀)

/-- **The solution is differentiable, with the stated velocity.** -/
theorem hasDerivAt_kgSmoothMild (hb0 : 0 ≤ b) (hW : ‖W₀‖ ≤ b)
    (g₀ h₀ : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    HasDerivAt (kgSmoothMild W₀ g₀ h₀) (kgSmoothVel W₀ g₀ h₀ t) t :=
  hasDerivAt_kgFieldMild (W := kgSmoothingOp W₀) hb0 (norm_kgSmoothingOp_le hW)
    (kgFreqInvOp g₀) (kgFreqInvOp h₀) t

/-- **The velocity is differentiable, with the stated acceleration.** This is the step the smoothing
hypothesis buys. -/
theorem hasDerivAt_kgSmoothVel (hb0 : 0 ≤ b) (hW : ‖W₀‖ ≤ b)
    (g₀ h₀ : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    HasDerivAt (kgSmoothVel W₀ g₀ h₀) (kgSmoothAcc W₀ g₀ h₀ t) t := by
  have hk := continuous_kgSmoothSource hb0 hW g₀ h₀
  have h1 : HasDerivAt (fun r : ℝ => -(kgSinOp r (kgFreqInvOp g₀)) + kgCosOp r (kgFreqInvOp h₀))
      (-(kgCosOp t g₀) + -(kgSinOp t h₀)) t :=
    ((hasDerivAt_kgSinOp_freqInv t g₀).neg).add (hasDerivAt_kgCosOp_freqInv t h₀)
  exact h1.add (hasDerivAt_kgCosDuhamel hk t)

end Solution

/-! ## The equation -/

section Equation

variable {W₀ : Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E)} {b : ℝ}

/-- The solution is doubly regular, and its regularising vector is explicit. -/
theorem kgSmoothMild_eq (hb0 : 0 ≤ b) (hW : ‖W₀‖ ≤ b) (g₀ h₀ : Lp ℂ 2 (volume : Measure E))
    (t : ℝ) :
    kgSmoothMild W₀ g₀ h₀ t
      = kgFreqInvOp (kgFreqInvOp (kgCosOp t g₀ + kgSinOp t h₀
        + ∫ s in (0 : ℝ)..t, kgSinOp (t - s) (W₀ (kgSmoothMild W₀ g₀ h₀ s)))) := by
  have hk := continuous_kgSmoothSource hb0 hW g₀ h₀
  have hu := continuous_kgSmoothMild hb0 hW g₀ h₀
  have hsin : Continuous fun s : ℝ =>
      kgSinOp (t - s) (W₀ (kgSmoothMild W₀ g₀ h₀ s)) :=
    continuous_of_strong_comp norm_kgSinOp_le continuous_kgSinOp_apply
      (continuous_const.sub continuous_id) hk
  have hI := hsin.intervalIntegrable (μ := volume) 0 t
  have hpoint : ∀ s ∈ Set.uIcc (0 : ℝ) t,
      kgFieldKernel (kgSmoothingOp W₀) t s (kgSmoothMild W₀ g₀ h₀ s)
        = kgFreqInvOp (kgFreqInvOp (kgSinOp (t - s)
            (W₀ (kgSmoothMild W₀ g₀ h₀ s)))) := by
    intro s _
    rw [kgFieldKernel_apply, kgSmoothingOp_apply, kgSinFreqOp_freqInv]
  have hfree : kgFieldFree (kgFreqInvOp (kgFreqInvOp g₀)) (kgFreqInvOp h₀) t
      = kgFreqInvOp (kgFreqInvOp (kgCosOp t g₀ + kgSinOp t h₀)) := by
    rw [kgFieldFree, kgSinFreqOp_freqInv, map_add, map_add, ← kgFreqInvOp_kgCosOp,
      ← kgFreqInvOp_kgCosOp]
  have hstart : kgSmoothMild W₀ g₀ h₀ t
      = kgFieldFree (kgFreqInvOp (kgFreqInvOp g₀)) (kgFreqInvOp h₀) t
        + ∫ s in (0 : ℝ)..t,
            kgFieldKernel (kgSmoothingOp W₀) t s (kgSmoothMild W₀ g₀ h₀ s) :=
    kgFieldMild_eq hb0 (norm_kgSmoothingOp_le hW) _ _ t
  have hI2 : IntervalIntegrable
      (fun s : ℝ => kgFreqInvOp (kgSinOp (t - s) (W₀ (kgSmoothMild W₀ g₀ h₀ s))))
      volume 0 t :=
    ((kgFreqInvOp (E := E)).continuous.comp hsin).intervalIntegrable (μ := volume) 0 t
  rw [hstart, intervalIntegral.integral_congr hpoint,
    ContinuousLinearMap.intervalIntegral_comp_comm _ hI2,
    ContinuousLinearMap.intervalIntegral_comp_comm _ hI, hfree, ← map_add, ← map_add]


/-- **A smoothing perturbation makes the mild solution strong.** For `W = ⟨D⟩⁻¹W₀` and Cauchy data
`⟨D⟩⁻²g₀`, `⟨D⟩⁻¹h₀`, the field-level mild solution is twice differentiable and satisfies
`⟨D⟩⁻²(∂ₜ²u) = -u + ⟨D⟩⁻²(Wu)`. So the estimate, uniqueness and stability of the perturbed strong
theory apply to a solution the corpus constructs. -/
theorem solvesKGSource_kgSmoothMild (hb0 : 0 ≤ b) (hW : ‖W₀‖ ≤ b)
    (g₀ h₀ : Lp ℂ 2 (volume : Measure E)) :
    SolvesKGSource (kgSmoothingOp W₀) (kgSmoothMild W₀ g₀ h₀) (kgSmoothVel W₀ g₀ h₀)
      (kgSmoothAcc W₀ g₀ h₀) := by
  refine ⟨hasDerivAt_kgSmoothMild hb0 hW g₀ h₀, hasDerivAt_kgSmoothVel hb0 hW g₀ h₀, fun t => ?_⟩
  have key : ∀ A B C D : Lp ℂ 2 (volume : Measure E),
      kgFreqInvOp (kgFreqInvOp (-A + -B + (D - C)))
        = -(kgFreqInvOp (kgFreqInvOp (A + B + C))) + kgFreqInvOp (kgFreqInvOp D) := by
    intro A B C D
    simp only [map_add, map_neg, map_sub]
    abel
  rw [kgSmoothAcc, key, ← kgSmoothMild_eq hb0 hW g₀ h₀ t,
    ← kgSmoothingOp_apply W₀ (kgSmoothMild W₀ g₀ h₀ t)]

/-- **The perturbed energy estimate for the constructed solution.** -/
theorem kgStrongEnergy_kgSmoothMild_le (hb0 : 0 ≤ b) (hW : ‖W₀‖ ≤ b)
    (g₀ h₀ : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    kgStrongEnergy (kgSmoothMild W₀ g₀ h₀) (kgSmoothVel W₀ g₀ h₀) t
      ≤ kgStrongEnergy (kgSmoothMild W₀ g₀ h₀) (kgSmoothVel W₀ g₀ h₀) 0
        * Real.exp (b * |t|) :=
  kgStrongEnergy_le_exp_abs hb0 (norm_kgSmoothingOp_le hW)
    (solvesKGSource_kgSmoothMild hb0 hW g₀ h₀) t

end Equation

end GaloisForLFunctions.HTGeometry
