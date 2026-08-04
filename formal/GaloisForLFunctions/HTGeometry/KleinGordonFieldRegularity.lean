import GaloisForLFunctions.HTGeometry.KleinGordonFieldMild

/-!
# Regularity and linearity of the field-level solution

Two independent refinements of the field-level theory.

First, the velocity datum needs **no** regularity. Differentiating `sin(t⟨ξ⟩)/⟨ξ⟩` gives `cos(t⟨ξ⟩)`,
which is bounded, so `t ↦ (sin(t⟨D⟩)/⟨D⟩)h` is differentiable for every `h ∈ L²`; only the position
datum has to be regularised, and only by one power of `⟨D⟩⁻¹`. That is strictly weaker than the
hypothesis the second derivative needs.

Second, the field-level Duhamel formula is linear in its data, so uniqueness turns the difference of
two solutions into the solution of the difference of the data, and the exponential bound becomes
**continuous dependence** at the level of the field.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Filter

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-! ## The velocity datum needs no regularity -/

theorem kgSinFreqOp_apply (t : ℝ) (x : Lp ℂ 2 (volume : Measure E)) :
    kgSinFreqOp t x = kgSinOp t (kgFreqInvOp x) := by
  rw [kgSinFreqOp_eq_comp]
  rfl

/-- **The half-order propagator is differentiable on every datum**, with derivative the cosine
propagator. The factor `⟨ξ⟩⁻¹` in the symbol absorbs the `⟨ξ⟩` the chain rule produces, so no
regularity is needed. -/
theorem hasDerivAt_kgSinFreqOp (t : ℝ) (x : Lp ℂ 2 (volume : Measure E)) :
    HasDerivAt (fun s : ℝ => kgSinFreqOp s x) (kgCosOp t x) t := by
  have h := hasDerivAt_kgSinOp_freqInv (E := E) t x
  refine h.congr_of_eventuallyEq ?_
  exact Filter.Eventually.of_forall fun s => kgSinFreqOp_apply s x

/-- **The free field is differentiable once the position datum carries one power of `⟨D⟩⁻¹`.** -/
theorem hasDerivAt_kgFieldFree (g h : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    HasDerivAt (kgFieldFree (kgFreqInvOp g) h) (-(kgSinOp t g) + kgCosOp t h) t :=
  (hasDerivAt_kgCosOp_freqInv t g).add (hasDerivAt_kgSinFreqOp t h)

/-- The free field starts at the position datum with velocity the velocity datum. -/
theorem deriv_kgFieldFree_zero (g h : Lp ℂ 2 (volume : Measure E)) :
    deriv (kgFieldFree (kgFreqInvOp g) h) 0 = h := by
  rw [(hasDerivAt_kgFieldFree g h 0).deriv, kgCosOp_zero, kgSinOp_zero]
  simp

/-! ## Linearity of the field-level solution -/

section Linear

variable {W : Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E)} {b : ℝ}

theorem kgFieldFree_sub (f₁ h₁ f₂ h₂ : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    kgFieldFree f₁ h₁ t - kgFieldFree f₂ h₂ t = kgFieldFree (f₁ - f₂) (h₁ - h₂) t := by
  rw [kgFieldFree, kgFieldFree, kgFieldFree, map_sub, map_sub]
  abel

theorem intervalIntegrable_kgFieldKernel {u : ℝ → Lp ℂ 2 (volume : Measure E)}
    (hu : Continuous u) (W : Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E))
    (t : ℝ) : IntervalIntegrable (fun s => kgFieldKernel W t s (u s)) volume 0 t := by
  have hpair : Continuous fun s : ℝ => ((t, s) : ℝ × ℝ) :=
    continuous_const.prodMk continuous_id
  have hcomp : Continuous
      ((fun p : ℝ × ℝ => kgFieldKernel W p.1 p.2 (u p.2)) ∘ fun s : ℝ => ((t, s) : ℝ × ℝ)) :=
    (strongKernel_kgFieldKernel W u hu).comp hpair
  have hcont : Continuous fun s : ℝ => kgFieldKernel W t s (u s) :=
    hcomp.congr fun s => rfl
  exact hcont.intervalIntegrable 0 t

/-- **The field-level solution is linear in its Cauchy data.** -/
theorem kgFieldMild_sub (hb0 : 0 ≤ b) (hW : ‖W‖ ≤ b)
    (f₁ h₁ f₂ h₂ : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    kgFieldMild W f₁ h₁ t - kgFieldMild W f₂ h₂ t
      = kgFieldMild W (f₁ - f₂) (h₁ - h₂) t := by
  have hdiff : (fun s => kgFieldMild W f₁ h₁ s - kgFieldMild W f₂ h₂ s)
      = kgFieldMild W (f₁ - f₂) (h₁ - h₂) := by
    refine eq_kgFieldMild_of_duhamel hb0 hW (f₁ - f₂) (h₁ - h₂)
      ((continuous_kgFieldMild hb0 hW f₁ h₁).sub (continuous_kgFieldMild hb0 hW f₂ h₂))
      (fun r => ?_)
    have hI₁ := intervalIntegrable_kgFieldKernel (continuous_kgFieldMild hb0 hW f₁ h₁) W r
    have hI₂ := intervalIntegrable_kgFieldKernel (continuous_kgFieldMild hb0 hW f₂ h₂) W r
    have hint : (∫ s in (0 : ℝ)..r, kgFieldKernel W r s (kgFieldMild W f₁ h₁ s))
        - ∫ s in (0 : ℝ)..r, kgFieldKernel W r s (kgFieldMild W f₂ h₂ s)
        = ∫ s in (0 : ℝ)..r,
            kgFieldKernel W r s (kgFieldMild W f₁ h₁ s - kgFieldMild W f₂ h₂ s) := by
      rw [← intervalIntegral.integral_sub hI₁ hI₂]
      refine intervalIntegral.integral_congr fun s _ => ?_
      rw [map_sub]
    rw [← kgFieldFree_sub, ← hint, kgFieldMild_eq hb0 hW f₁ h₁ r, kgFieldMild_eq hb0 hW f₂ h₂ r]
    abel
  exact congrFun hdiff t

/-- **Continuous dependence on the Cauchy data, at the level of the field.** -/
theorem norm_kgFieldMild_sub_le (hb0 : 0 ≤ b) (hW : ‖W‖ ≤ b)
    (f₁ h₁ f₂ h₂ : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    ‖kgFieldMild W f₁ h₁ t - kgFieldMild W f₂ h₂ t‖
      ≤ (‖f₁ - f₂‖ + ‖h₁ - h₂‖) * Real.exp (b * |t|) := by
  rw [kgFieldMild_sub hb0 hW]
  exact norm_kgFieldMild_le hb0 hW (f₁ - f₂) (h₁ - h₂) t

end Linear

end GaloisForLFunctions.HTGeometry
