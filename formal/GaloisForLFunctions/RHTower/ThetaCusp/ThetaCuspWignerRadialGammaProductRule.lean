import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspWignerPairLogSpectrum

/-!
# The Gamma product rule behind the log-scale radial weight

Writing every Gamma value and Gamma derivative at `σ+3` and `σ+4` through the recurrence
`Γ(x+1) = x Γ(x)`, `Γ'(x+1) = x Γ'(x) + Γ(x)`, the log-scale radial weight collapses to the exact
product rule for `Γ(σ+2) C^(-(σ+2)) Q σ C` in the order variable:

```text
LogWeight σ C = (Γ'(σ+2) - Γ(σ+2) log C) Q σ C + Γ(σ+2) ∂_σ Q σ C .
```

At zero hyperbolic separation this reads `Γ'(σ+2)(σ² - σ + 3) + Γ(σ+2)(2σ - 1)`: the second term
carries the factor `2σ - 1`, which changes sign exactly at the critical abscissa and is therefore
the antisymmetric part of the centre weight under `σ ↔ 1 - σ`.
-/

open Real MeasureTheory Set

namespace RHTower

noncomputable section

theorem deriv_Gamma_add_one {x : ℝ} (hx : 0 < x) :
    deriv Real.Gamma (x + 1) = x * deriv Real.Gamma x + Real.Gamma x := by
  have hne : ∀ m : ℕ, x ≠ -(m : ℝ) := by
    intro m hm
    have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith [hm ▸ hx]
  have hne1 : ∀ m : ℕ, x + 1 ≠ -(m : ℝ) := by
    intro m hm
    have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith [hm ▸ (by linarith : (0 : ℝ) < x + 1)]
  have hd : DifferentiableAt ℝ Real.Gamma x := Real.differentiableAt_Gamma hne
  have hd1 : DifferentiableAt ℝ Real.Gamma (x + 1) := Real.differentiableAt_Gamma hne1
  have hshift : HasDerivAt (fun y : ℝ => Real.Gamma (y + 1)) (deriv Real.Gamma (x + 1)) x := by
    have hinner : HasDerivAt (fun y : ℝ => y + 1) 1 x := (hasDerivAt_id x).add_const 1
    simpa [Function.comp_def] using hd1.hasDerivAt.comp x hinner
  have hprod : HasDerivAt (fun y : ℝ => y * Real.Gamma y)
      (1 * Real.Gamma x + x * deriv Real.Gamma x) x :=
    (hasDerivAt_id x).mul hd.hasDerivAt
  have heq : HasDerivAt (fun y : ℝ => Real.Gamma (y + 1))
      (1 * Real.Gamma x + x * deriv Real.Gamma x) x := by
    refine hprod.congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds hx] with y hy
    exact Real.Gamma_add_one (ne_of_gt hy)
  have := hshift.unique heq
  rw [this]
  ring

/-- The `σ`-derivative of the rational radial weight. -/
def thetaCuspWignerRadialQDeriv (σ C : ℝ) : ℝ := (2 * σ + 5) / C ^ 2 - 6

/-- **The log-scale radial weight is the product-rule derivative of the rational one.**  The
Gamma-derivative combination collapses onto `Q` itself, the `log C` term is the derivative of the
power, and the remainder is `∂_σ Q`. -/
theorem thetaCuspWignerRadialLogWeight_eq_product_rule {σ : ℝ} (hσ : 0 < σ) {C : ℝ} (hC : 0 < C) :
    thetaCuspWignerRadialLogWeight σ C =
      (deriv Real.Gamma (σ + 2) - Real.Gamma (σ + 2) * Real.log C) *
          thetaCuspWignerRadialQ σ C +
        Real.Gamma (σ + 2) * thetaCuspWignerRadialQDeriv σ C := by
  have h2 : (0 : ℝ) < σ + 2 := by linarith
  have h3 : (0 : ℝ) < σ + 3 := by linarith
  have g3 : Real.Gamma (σ + 3) = (σ + 2) * Real.Gamma (σ + 2) := by
    rw [show σ + 3 = (σ + 2) + 1 by ring, Real.Gamma_add_one (ne_of_gt h2)]
  have d3 : deriv Real.Gamma (σ + 3) =
      (σ + 2) * deriv Real.Gamma (σ + 2) + Real.Gamma (σ + 2) := by
    rw [show σ + 3 = (σ + 2) + 1 by ring, deriv_Gamma_add_one h2]
  have g4 : Real.Gamma (σ + 4) = (σ + 3) * ((σ + 2) * Real.Gamma (σ + 2)) := by
    rw [show σ + 4 = (σ + 3) + 1 by ring, Real.Gamma_add_one (ne_of_gt h3), g3]
  have d4 : deriv Real.Gamma (σ + 4) =
      (σ + 3) * ((σ + 2) * deriv Real.Gamma (σ + 2) + Real.Gamma (σ + 2)) +
        (σ + 2) * Real.Gamma (σ + 2) := by
    rw [show σ + 4 = (σ + 3) + 1 by ring, deriv_Gamma_add_one h3, d3, g3]
  rw [thetaCuspWignerRadialLogWeight, thetaCuspWignerRadialQ, thetaCuspWignerRadialQDeriv,
    d4, d3, g4, g3]
  field_simp
  ring

/-- At zero hyperbolic separation the log-scale weight carries the antisymmetric factor `2σ - 1`,
which changes sign exactly at the critical abscissa. -/
theorem thetaCuspWignerRadialLogWeight_one {σ : ℝ} (hσ : 0 < σ) :
    thetaCuspWignerRadialLogWeight σ 1 =
      deriv Real.Gamma (σ + 2) * (σ ^ 2 - σ + 3) + Real.Gamma (σ + 2) * (2 * σ - 1) := by
  rw [thetaCuspWignerRadialLogWeight_eq_product_rule hσ one_pos,
    thetaCuspWignerRadialQ, thetaCuspWignerRadialQDeriv]
  norm_num
  ring

end

end RHTower
