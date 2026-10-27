import GaloisForLFunctions.BiarithmeticGaugeGeometry.TheLandauWronskianDeformationPrinciple

/-!
# Positivity is irreversible

A *positive deformation* of an entire function `Λ₀` is a function `Λ` whose logarithmic derivative
differs from that of `Λ₀`, on a real ray, by the Laplace transform of a measure on `(0, ∞)` with
finite Laplace mass:

`Λ₀′/Λ₀ (σ) − Λ′/Λ (σ) = ∫_{(0,∞)} e^{−σu} dν(u)`.

This is the form of every deformation in the Bochner–Hadamard calculus of BGG (outward critical
splitting, positive prime-mass excess, rational deformations).

* **Composition** (`PositiveDeformation.trans`): positive deformations compose; the measures add.
* **Trivial units** (`PositiveDeformation.antisymm`): if `Λ` is a positive deformation of `Λ₀` and
  `Λ₀` one of `Λ`, the two logarithmic derivatives agree on a ray and both measures vanish on
  `(0, ∞)`, because two nonnegative transforms sum to zero.
* **Irreversibility** (`not_positiveDeformation_of_ne`): a deformation that changes the logarithmic
  derivative somewhere on its ray cannot be undone by a positive one.

So positive deformations form a monoid without nontrivial invertible elements: positivity orders
deformations and never acts by a group. Together with the Landau–Wronskian principle (a positive
deformation can only lower the order at its abscissa) this is the chirality of RBG: outward
splitting is positive, its inverse is not.
-/

open Complex Filter Topology Set MeasureTheory
open scoped ENNReal

noncomputable section

namespace GaloisForLFunctions.RenormalizedBiarithmeticGeometry

open GaloisForLFunctions.RHTower (laplaceReal laplaceMass)

/-- `Λ` is a **positive deformation** of `Λ₀`: on the ray `σ > σ₁` both are nonzero and
`Λ₀′/Λ₀ − Λ′/Λ` is the Laplace transform of a measure `ν` with finite Laplace mass at `σ₁`. -/
def PositiveDeformation (Λ₀ Λ : ℂ → ℂ) : Prop :=
  ∃ (ν : Measure ℝ) (σ₁ : ℝ), laplaceMass ν σ₁ ≠ ⊤ ∧ ∀ σ : ℝ, σ₁ < σ →
    Λ σ ≠ 0 ∧ Λ₀ σ ≠ 0 ∧ logDeriv Λ₀ (σ : ℂ) - logDeriv Λ (σ : ℂ) = ((laplaceReal ν σ : ℝ) : ℂ)

/-- The Laplace mass decreases along the ray. -/
theorem laplaceMass_le_of_le (ν : Measure ℝ) {σ₁ σ : ℝ} (h : σ₁ ≤ σ) :
    laplaceMass ν σ ≤ laplaceMass ν σ₁ := by
  unfold laplaceMass
  refine setLIntegral_mono' measurableSet_Ioi fun u hu => ENNReal.ofReal_le_ofReal ?_
  exact Real.exp_le_exp.mpr (by nlinarith [mem_Ioi.mp hu])

/-- Finite Laplace mass makes `e^{−σu}` integrable on `(0, ∞)`. -/
theorem integrableOn_exp_of_laplaceMass_ne_top {ν : Measure ℝ} {σ : ℝ}
    (h : laplaceMass ν σ ≠ ⊤) :
    IntegrableOn (fun u : ℝ => Real.exp (-σ * u)) (Ioi 0) ν := by
  refine ⟨(Real.continuous_exp.comp (continuous_const.mul continuous_id)).aestronglyMeasurable,
    ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ fun u => (Real.exp_pos _).le)]
  exact lt_top_iff_ne_top.mpr h

/-- The Laplace transform of a measure is nonnegative. -/
theorem laplaceReal_nonneg (ν : Measure ℝ) (σ : ℝ) : 0 ≤ laplaceReal ν σ :=
  setIntegral_nonneg measurableSet_Ioi fun _ _ => (Real.exp_pos _).le

/-- Laplace transforms of a sum of measures add. -/
theorem laplaceReal_add {ν ν' : Measure ℝ} {σ : ℝ} (h : laplaceMass ν σ ≠ ⊤)
    (h' : laplaceMass ν' σ ≠ ⊤) : laplaceReal (ν + ν') σ = laplaceReal ν σ + laplaceReal ν' σ := by
  unfold laplaceReal
  rw [Measure.restrict_add]
  exact integral_add_measure (integrableOn_exp_of_laplaceMass_ne_top h)
    (integrableOn_exp_of_laplaceMass_ne_top h')

theorem laplaceMass_add (ν ν' : Measure ℝ) (σ : ℝ) :
    laplaceMass (ν + ν') σ = laplaceMass ν σ + laplaceMass ν' σ := by
  unfold laplaceMass
  rw [Measure.restrict_add, lintegral_add_measure]

/-- **Positive deformations compose**, with added measures. -/
theorem PositiveDeformation.trans {Λ₀ Λ₁ Λ₂ : ℂ → ℂ} (h₁ : PositiveDeformation Λ₀ Λ₁)
    (h₂ : PositiveDeformation Λ₁ Λ₂) : PositiveDeformation Λ₀ Λ₂ := by
  obtain ⟨ν, σ, hν, hd⟩ := h₁
  obtain ⟨ν', σ', hν', hd'⟩ := h₂
  refine ⟨ν + ν', max σ σ', ?_, fun s hs => ?_⟩
  · rw [laplaceMass_add]
    exact ENNReal.add_ne_top.mpr
      ⟨ne_top_of_le_ne_top hν (laplaceMass_le_of_le ν (le_max_left _ _)),
        ne_top_of_le_ne_top hν' (laplaceMass_le_of_le ν' (le_max_right _ _))⟩
  · have hs1 : σ < s := lt_of_le_of_lt (le_max_left _ _) hs
    have hs2 : σ' < s := lt_of_le_of_lt (le_max_right _ _) hs
    obtain ⟨-, h0, e1⟩ := hd s hs1
    obtain ⟨h2, -, e2⟩ := hd' s hs2
    refine ⟨h2, h0, ?_⟩
    rw [laplaceReal_add (ne_top_of_le_ne_top hν (laplaceMass_le_of_le ν hs1.le))
      (ne_top_of_le_ne_top hν' (laplaceMass_le_of_le ν' hs2.le))]
    push_cast
    linear_combination e1 + e2

/-- **Trivial units.** If each of `Λ₀, Λ` is a positive deformation of the other, their logarithmic
derivatives agree on a ray. -/
theorem PositiveDeformation.antisymm {Λ₀ Λ : ℂ → ℂ} (h : PositiveDeformation Λ₀ Λ)
    (h' : PositiveDeformation Λ Λ₀) :
    ∃ σ₂ : ℝ, ∀ σ : ℝ, σ₂ < σ → logDeriv Λ₀ (σ : ℂ) = logDeriv Λ (σ : ℂ) := by
  obtain ⟨ν, σ₁, -, hd⟩ := h
  obtain ⟨ν', σ₁', -, hd'⟩ := h'
  refine ⟨max σ₁ σ₁', fun σ hσ => ?_⟩
  obtain ⟨-, -, e⟩ := hd σ (lt_of_le_of_lt (le_max_left _ _) hσ)
  obtain ⟨-, -, e'⟩ := hd' σ (lt_of_le_of_lt (le_max_right _ _) hσ)
  -- Two nonnegative transforms with zero sum both vanish.
  have hsum : ((laplaceReal ν σ + laplaceReal ν' σ : ℝ) : ℂ) = 0 := by
    push_cast; linear_combination -e - e'
  have hsum' : laplaceReal ν σ + laplaceReal ν' σ = 0 := by exact_mod_cast hsum
  have h0 : laplaceReal ν σ = 0 := by
    linarith [laplaceReal_nonneg ν σ, laplaceReal_nonneg ν' σ]
  rw [h0, Complex.ofReal_zero, sub_eq_zero] at e
  exact e

/-- **Positivity is irreversible.** A positive deformation that changes the logarithmic derivative
at points of its ray arbitrarily far right cannot be undone by a positive deformation. -/
theorem not_positiveDeformation_of_ne {Λ₀ Λ : ℂ → ℂ} (h : PositiveDeformation Λ₀ Λ)
    (hne : ∀ σ₂ : ℝ, ∃ σ : ℝ, σ₂ < σ ∧ logDeriv Λ₀ (σ : ℂ) ≠ logDeriv Λ (σ : ℂ)) :
    ¬ PositiveDeformation Λ Λ₀ := by
  intro h'
  obtain ⟨σ₂, hσ₂⟩ := h.antisymm h'
  obtain ⟨σ, hσ, hne'⟩ := hne σ₂
  exact hne' (hσ₂ σ hσ)

end GaloisForLFunctions.RenormalizedBiarithmeticGeometry
