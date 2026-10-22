import GaloisForLFunctions.HTGeometry.KleinGordon.KleinGordonPotentialInjective

/-!
# A moving real potential is reconstructed at every instant

Statement 382 recovers a static potential. The clock programme's backgrounds move, and the
reconstruction machinery is built for moving ones — what is needed is the translation of its two
analytic hypotheses into statements about the potential.

The uniform bound is immediate: a multiplication operator obeys every bound its symbol obeys. The
Lipschitz hypothesis is the same fact applied to the four-term combination
`(V₁(σ)−V₂(σ)) − (V₁(τ)−V₂(τ))`, which is again a multiplication operator, by the additivity of the
symbol calculus. The strong continuity in time is genuinely a hypothesis on the family — it is what
the moving theory of statements 144–147 assumes, and the switched potentials of 206 satisfy it.

With those, statement 378 applies and injectivity of the symbol (381) turns its conclusion into

**a moving bounded real potential, Lipschitz in time, is determined almost everywhere at every instant
by short-time clock observations at every cut-off.**
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

section MulOpLipschitz

variable {A₁ A₂ B₁ B₂ : E → ℝ} {b : ℝ}

/-- **The four-term combination of multiplication operators is the multiplication operator of the
combined potential**, so it obeys every bound the combined potential obeys. -/
theorem norm_kgMulOp_sub_sub_le (hA₁ : Measurable A₁) (hA₂ : Measurable A₂)
    (hB₁ : Measurable B₁) (hB₂ : Measurable B₂) (hb0 : 0 ≤ b)
    (hbA₁ : ∀ a : E, |A₁ a| ≤ b) (hbA₂ : ∀ a : E, |A₂ a| ≤ b)
    (hbB₁ : ∀ a : E, |B₁ a| ≤ b) (hbB₂ : ∀ a : E, |B₂ a| ≤ b)
    {D : ℝ} (hD0 : 0 ≤ D) (hD : ∀ a : E, |(A₁ a - A₂ a) - (B₁ a - B₂ a)| ≤ D) :
    ‖(kgMulOp hA₁ hb0 hbA₁ - kgMulOp hA₂ hb0 hbA₂)
        - (kgMulOp hB₁ hb0 hbB₁ - kgMulOp hB₂ hb0 hbB₂)‖ ≤ D := by
  have hb2 : (0 : ℝ) ≤ b + b := by linarith
  have hmA : Measurable fun a : E => ((A₁ a - A₂ a : ℝ) : ℂ) :=
    Complex.continuous_ofReal.measurable.comp (hA₁.sub hA₂)
  have hmB : Measurable fun a : E => ((B₁ a - B₂ a : ℝ) : ℂ) :=
    Complex.continuous_ofReal.measurable.comp (hB₁.sub hB₂)
  have hbdA : ∀ a : E, ‖((A₁ a - A₂ a : ℝ) : ℂ)‖ ≤ b + b := by
    intro a
    rw [Complex.norm_real, Real.norm_eq_abs]
    have h1 := hbA₁ a
    have h2 := hbA₂ a
    calc |A₁ a - A₂ a| ≤ |A₁ a| + |A₂ a| := abs_sub _ _
      _ ≤ b + b := by linarith
  have hbdB : ∀ a : E, ‖((B₁ a - B₂ a : ℝ) : ℂ)‖ ≤ b + b := by
    intro a
    rw [Complex.norm_real, Real.norm_eq_abs]
    have h1 := hbB₁ a
    have h2 := hbB₂ a
    calc |B₁ a - B₂ a| ≤ |B₁ a| + |B₂ a| := abs_sub _ _
      _ ≤ b + b := by linarith
  have hmC : Measurable fun a : E => (((A₁ a - A₂ a) - (B₁ a - B₂ a) : ℝ) : ℂ) :=
    Complex.continuous_ofReal.measurable.comp ((hA₁.sub hA₂).sub (hB₁.sub hB₂))
  have hbdC : ∀ a : E, ‖(((A₁ a - A₂ a) - (B₁ a - B₂ a) : ℝ) : ℂ)‖ ≤ D := by
    intro a
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact hD a
  have hA : lpBoundedMulCLM (p := 2) (μ := (volume : Measure E)) hmA hb2 hbdA
      = kgMulOp hA₁ hb0 hbA₁ - kgMulOp hA₂ hb0 hbA₂ := by
    rw [kgMulOp, kgMulOp]
    refine lpBoundedMulCLM_sub (measurable_ofReal_potential hA₁)
      (measurable_ofReal_potential hA₂) hmA hb0 (norm_ofReal_potential_le hbA₁) hb0
      (norm_ofReal_potential_le hbA₂) hb2 hbdA ?_
    refine Filter.Eventually.of_forall fun a => ?_
    push_cast
    ring
  have hB : lpBoundedMulCLM (p := 2) (μ := (volume : Measure E)) hmB hb2 hbdB
      = kgMulOp hB₁ hb0 hbB₁ - kgMulOp hB₂ hb0 hbB₂ := by
    rw [kgMulOp, kgMulOp]
    refine lpBoundedMulCLM_sub (measurable_ofReal_potential hB₁)
      (measurable_ofReal_potential hB₂) hmB hb0 (norm_ofReal_potential_le hbB₁) hb0
      (norm_ofReal_potential_le hbB₂) hb2 hbdB ?_
    refine Filter.Eventually.of_forall fun a => ?_
    push_cast
    ring
  have hC : lpBoundedMulCLM (p := 2) (μ := (volume : Measure E)) hmC hD0 hbdC
      = lpBoundedMulCLM (p := 2) (μ := (volume : Measure E)) hmA hb2 hbdA
        - lpBoundedMulCLM (p := 2) (μ := (volume : Measure E)) hmB hb2 hbdB := by
    refine lpBoundedMulCLM_sub hmA hmB hmC hb2 hbdA hb2 hbdB hD0 hbdC ?_
    refine Filter.Eventually.of_forall fun a => ?_
    push_cast
    ring
  rw [← hA, ← hB, ← hC]
  exact norm_lpBoundedMulCLM_le _ _ _

end MulOpLipschitz

section MovingPotential

variable {V₁ V₂ : ℝ → E → ℝ} {b L : ℝ}

/-- **A moving bounded real potential is determined almost everywhere at every instant** by
short-time clock observations at every cut-off. -/
theorem potentialT_ae_eq_of_exact_observation
    (hV₁ : ∀ r : ℝ, Measurable (V₁ r)) (hV₂ : ∀ r : ℝ, Measurable (V₂ r)) (hb0 : 0 ≤ b)
    (hb₁ : ∀ (r : ℝ) (a : E), |V₁ r a| ≤ b) (hb₂ : ∀ (r : ℝ) (a : E), |V₂ r a| ≤ b)
    (hs₁ : ∀ y : Lp ℂ 2 (volume : Measure E),
      Continuous fun r : ℝ => kgMulOp (hV₁ r) hb0 (hb₁ r) y)
    (hs₂ : ∀ y : Lp ℂ 2 (volume : Measure E),
      Continuous fun r : ℝ => kgMulOp (hV₂ r) hb0 (hb₂ r) y)
    (hL0 : 0 ≤ L)
    (hLip : ∀ (σ τ : ℝ) (a : E),
      |(V₁ σ a - V₂ σ a) - (V₁ τ a - V₂ τ a)| ≤ L * |σ - τ|)
    {T : ℝ} (hT0 : 0 < T)
    (hobs : ∀ (R s : ℝ) (g k : Lp ℂ 2 (volume : Measure E)) (t : ℝ), |t| ≤ T →
      kgFieldMildT (fun r : ℝ =>
          kgBandOpT (fun ρ : ℝ => kgMulOp (hV₁ ρ) hb0 (hb₁ ρ)) R (r + s)) g k t
        = kgFieldMildT (fun r : ℝ =>
            kgBandOpT (fun ρ : ℝ => kgMulOp (hV₂ ρ) hb0 (hb₂ ρ)) R (r + s)) g k t)
    (t : ℝ) : V₁ t =ᵐ[(volume : Measure E)] V₂ t := by
  have hWb₁ : ∀ r : ℝ, ‖kgMulOp (hV₁ r) hb0 (hb₁ r)‖ ≤ b := fun r =>
    norm_kgMulOp_le (hV₁ r) hb0 (hb₁ r)
  have hWb₂ : ∀ r : ℝ, ‖kgMulOp (hV₂ r) hb0 (hb₂ r)‖ ≤ b := fun r =>
    norm_kgMulOp_le (hV₂ r) hb0 (hb₂ r)
  have hLip' : ∀ σ τ : ℝ,
      ‖(kgMulOp (hV₁ σ) hb0 (hb₁ σ) - kgMulOp (hV₂ σ) hb0 (hb₂ σ))
          - (kgMulOp (hV₁ τ) hb0 (hb₁ τ) - kgMulOp (hV₂ τ) hb0 (hb₂ τ))‖ ≤ L * |σ - τ| := by
    intro σ τ
    have hD0 : (0 : ℝ) ≤ L * |σ - τ| := by positivity
    exact norm_kgMulOp_sub_sub_le (hV₁ σ) (hV₂ σ) (hV₁ τ) (hV₂ τ) hb0 (hb₁ σ) (hb₂ σ)
      (hb₁ τ) (hb₂ τ) hD0 (hLip σ τ)
  have hfun := eq_of_exact_observation_all_bands hb0 hWb₁ hs₁ hWb₂ hs₂ hL0 hLip' hT0 hobs
  exact kgMulOp_injective (hV₁ t) (hV₂ t) hb0 (hb₁ t) (hb₂ t) (congrFun hfun t)

end MovingPotential

end GaloisForLFunctions.HTGeometry
