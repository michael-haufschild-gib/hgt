import GaloisForLFunctions.HTGeometry.KleinGordon.KleinGordonSmoothingStrong

/-!
# Well-posedness of the strong problem with a smoothing perturbation

The constructed strong solution starts at the prescribed Cauchy data, and by the uniqueness of the
perturbed strong theory it is the *only* strong solution with those data. So for a smoothing
perturbation the second-order equation is well posed in the strong sense: existence, the exponential
energy estimate and uniqueness hold together, about the same object.

The last statement instantiates this at a bounded measurable potential smoothed by one power of
`⟨D⟩⁻¹`, which is the clock equation with the roughest coefficient the strong theory admits.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

section WellPosed

variable {W₀ : Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E)} {b : ℝ}

/-- The constructed solution starts at the position datum. -/
theorem kgSmoothMild_at_zero (hb0 : 0 ≤ b) (hW : ‖W₀‖ ≤ b)
    (g₀ h₀ : Lp ℂ 2 (volume : Measure E)) :
    kgSmoothMild W₀ g₀ h₀ 0 = kgFreqInvOp (kgFreqInvOp g₀) :=
  kgFieldMild_zero hb0 (norm_kgSmoothingOp_le hW) _ _

/-- The constructed solution starts with the velocity datum. -/
theorem kgSmoothVel_at_zero (g₀ h₀ : Lp ℂ 2 (volume : Measure E)) :
    kgSmoothVel W₀ g₀ h₀ 0 = kgFreqInvOp h₀ := by
  rw [kgSmoothVel, intervalIntegral.integral_same, kgCosOp_zero, kgSinOp_zero]
  simp

/-- **Uniqueness against the constructed solution.** Every strong solution of the smoothed equation
with the prescribed Cauchy data is the constructed one. -/
theorem eq_kgSmoothMild_of_solvesKGSource (hb0 : 0 ≤ b) (hW : ‖W₀‖ ≤ b)
    (g₀ h₀ : Lp ℂ 2 (volume : Measure E)) {u v a : ℝ → Lp ℂ 2 (volume : Measure E)}
    (h : SolvesKGSource (kgSmoothingOp W₀) u v a)
    (hu0 : u 0 = kgFreqInvOp (kgFreqInvOp g₀)) (hv0 : v 0 = kgFreqInvOp h₀) (t : ℝ) :
    u t = kgSmoothMild W₀ g₀ h₀ t :=
  eq_of_solvesKGSource hb0 (norm_kgSmoothingOp_le hW) h
    (solvesKGSource_kgSmoothMild hb0 hW g₀ h₀)
    (by rw [hu0, kgSmoothMild_at_zero hb0 hW]) (by rw [hv0, kgSmoothVel_at_zero]) t

/-- **The strong Cauchy problem with a smoothing perturbation is well posed.** There is a strong
solution with the prescribed data, it obeys the exponential energy estimate, and every strong
solution with those data equals it. -/
theorem wellPosed_solvesKGSource_smoothing (hb0 : 0 ≤ b) (hW : ‖W₀‖ ≤ b)
    (g₀ h₀ : Lp ℂ 2 (volume : Measure E)) :
    ∃ u v a : ℝ → Lp ℂ 2 (volume : Measure E),
      SolvesKGSource (kgSmoothingOp W₀) u v a ∧
      u 0 = kgFreqInvOp (kgFreqInvOp g₀) ∧ v 0 = kgFreqInvOp h₀ ∧
      (∀ t : ℝ, kgStrongEnergy u v t ≤ kgStrongEnergy u v 0 * Real.exp (b * |t|)) ∧
      ∀ u' v' a' : ℝ → Lp ℂ 2 (volume : Measure E),
        SolvesKGSource (kgSmoothingOp W₀) u' v' a' →
        u' 0 = kgFreqInvOp (kgFreqInvOp g₀) → v' 0 = kgFreqInvOp h₀ →
        ∀ t : ℝ, u' t = u t := by
  refine ⟨kgSmoothMild W₀ g₀ h₀, kgSmoothVel W₀ g₀ h₀, kgSmoothAcc W₀ g₀ h₀,
    solvesKGSource_kgSmoothMild hb0 hW g₀ h₀, kgSmoothMild_at_zero hb0 hW g₀ h₀,
    kgSmoothVel_at_zero g₀ h₀, kgStrongEnergy_kgSmoothMild_le hb0 hW g₀ h₀, ?_⟩
  intro u' v' a' h' hu0 hv0 t
  exact eq_kgSmoothMild_of_solvesKGSource hb0 hW g₀ h₀ h' hu0 hv0 t

end WellPosed

/-! ## The smoothed potential -/

/-- **The clock equation with a smoothed bounded measurable potential is strongly well posed.** The
perturbation is multiplication by `V` followed by one power of `⟨D⟩⁻¹`; no continuity, decay or
smoothness of `V` is used. -/
theorem solvesKGSource_kgSmoothMild_potential {V : E → ℂ} (hV : Measurable V) {b : ℝ}
    (hb0 : 0 ≤ b) (hb : ∀ ξ, ‖V ξ‖ ≤ b) (g₀ h₀ : Lp ℂ 2 (volume : Measure E)) :
    SolvesKGSource
      (kgSmoothingOp (lpBoundedMulCLM (p := 2) (μ := (volume : Measure E)) hV hb0 hb))
      (kgSmoothMild (lpBoundedMulCLM (p := 2) (μ := (volume : Measure E)) hV hb0 hb) g₀ h₀)
      (kgSmoothVel (lpBoundedMulCLM (p := 2) (μ := (volume : Measure E)) hV hb0 hb) g₀ h₀)
      (kgSmoothAcc (lpBoundedMulCLM (p := 2) (μ := (volume : Measure E)) hV hb0 hb) g₀ h₀) :=
  solvesKGSource_kgSmoothMild hb0
    (norm_lpBoundedMulCLM_le (p := 2) (μ := (volume : Measure E)) hV hb0 hb) g₀ h₀

/-- The energy estimate for the smoothed-potential solution. -/
theorem kgStrongEnergy_kgSmoothMild_potential_le {V : E → ℂ} (hV : Measurable V) {b : ℝ}
    (hb0 : 0 ≤ b) (hb : ∀ ξ, ‖V ξ‖ ≤ b) (g₀ h₀ : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    kgStrongEnergy
        (kgSmoothMild (lpBoundedMulCLM (p := 2) (μ := (volume : Measure E)) hV hb0 hb) g₀ h₀)
        (kgSmoothVel (lpBoundedMulCLM (p := 2) (μ := (volume : Measure E)) hV hb0 hb) g₀ h₀) t
      ≤ kgStrongEnergy
          (kgSmoothMild (lpBoundedMulCLM (p := 2) (μ := (volume : Measure E)) hV hb0 hb) g₀ h₀)
          (kgSmoothVel (lpBoundedMulCLM (p := 2) (μ := (volume : Measure E)) hV hb0 hb) g₀ h₀) 0
        * Real.exp (b * |t|) :=
  kgStrongEnergy_kgSmoothMild_le hb0
    (norm_lpBoundedMulCLM_le (p := 2) (μ := (volume : Measure E)) hV hb0 hb) g₀ h₀ t

end GaloisForLFunctions.HTGeometry
