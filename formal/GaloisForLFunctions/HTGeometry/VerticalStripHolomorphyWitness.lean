import GaloisForLFunctions.HTGeometry.VerticalStripBohrHull

/-!
# Holomorphy on a vertical strip: producers and the pointwise criterion

Holomorphy on an open vertical strip is the standing hypothesis of the strip-collapse and
valuation-boundary theorems, consumed at many sites and produced at none.  It is implied by
entirety, it is a pointwise condition because the strip is open, and it is strictly weaker than
entirety: a simple pole outside the strip is invisible to it.

The last point is what makes the hypothesis the right one — the theorems apply to functions with
poles off the strip, not only to entire functions.
-/

open Complex

namespace GaloisForLFunctions.HTGeometry

/-- Every entire function is holomorphic on every vertical strip. -/
theorem differentiableOn_openVerticalStrip_of_differentiable {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (σ η : ℝ) :
    DifferentiableOn ℂ f (openVerticalStrip σ η) :=
  hf.differentiableOn

/-- **Pointwise criterion.**  The strip is open, so holomorphy on it is differentiability at each
of its points. -/
theorem differentiableOn_openVerticalStrip_iff {f : ℂ → ℂ} (σ η : ℝ) :
    DifferentiableOn ℂ f (openVerticalStrip σ η) ↔
      ∀ z ∈ openVerticalStrip σ η, DifferentiableAt ℂ f z := by
  constructor
  · intro hf z hz
    exact hf.differentiableAt ((isOpen_openVerticalStrip σ η).mem_nhds hz)
  · intro h
    exact fun z hz => (h z hz).differentiableWithinAt

/-- Constants are holomorphic on every strip. -/
theorem differentiableOn_openVerticalStrip_const (c : ℂ) (σ η : ℝ) :
    DifferentiableOn ℂ (fun _ => c) (openVerticalStrip σ η) :=
  differentiableOn_openVerticalStrip_of_differentiable (differentiable_const c) σ η

/-- The exponential is holomorphic on every strip. -/
theorem differentiableOn_openVerticalStrip_exp (σ η : ℝ) :
    DifferentiableOn ℂ Complex.exp (openVerticalStrip σ η) :=
  differentiableOn_openVerticalStrip_of_differentiable Complex.differentiable_exp σ η

/-- **A witness that is not entire.**  A simple pole placed outside the strip leaves a function
holomorphic on it, so the hypothesis is strictly weaker than entirety. -/
theorem differentiableOn_openVerticalStrip_inv_sub {c : ℂ} {σ η : ℝ}
    (hc : c ∉ openVerticalStrip σ η) :
    DifferentiableOn ℂ (fun z => (z - c)⁻¹) (openVerticalStrip σ η) := by
  rw [differentiableOn_openVerticalStrip_iff]
  intro z hz
  have hne : z - c ≠ 0 := by
    intro h
    exact hc (by rwa [sub_eq_zero.mp h] at hz)
  exact (differentiableAt_id.sub_const c).inv hne

/-- The pole of the witness lies off the strip when placed at the boundary abscissa. -/
theorem boundaryAbscissa_not_mem_openVerticalStrip (σ : ℝ) {η : ℝ} (hη : 0 < η) :
    ((σ + η : ℝ) : ℂ) ∉ openVerticalStrip σ η := by
  rw [mem_openVerticalStrip]
  simp only [Complex.ofReal_re]
  rw [show σ + η - σ = η by ring, abs_of_pos hη]
  exact lt_irrefl η

/-- Hence every strip of positive width carries a function holomorphic on it whose pole sits off
it: the hypothesis is genuinely weaker than entirety. -/
theorem exists_differentiableOn_openVerticalStrip_with_pole (σ : ℝ) {η : ℝ} (hη : 0 < η) :
    ∃ c : ℂ, c ∉ openVerticalStrip σ η ∧
      DifferentiableOn ℂ (fun z => (z - c)⁻¹) (openVerticalStrip σ η) :=
  ⟨((σ + η : ℝ) : ℂ), boundaryAbscissa_not_mem_openVerticalStrip σ hη,
    differentiableOn_openVerticalStrip_inv_sub
      (boundaryAbscissa_not_mem_openVerticalStrip σ hη)⟩

end GaloisForLFunctions.HTGeometry
