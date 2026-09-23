import GaloisForLFunctions.HTGeometry.AnalyticEquilibriumUniqueness
import GaloisForLFunctions.HTGeometry.BriotBouquetLinear

/-!
# The quadratic autonomous equation has no nonconstant entire solution

With two distinct roots the equation `F' = γ(F − a₁)(F − a₂)` linearises: a nonconstant solution
omits `a₁`, so `V = (F − a₁)⁻¹` is entire, and

```text
V' = −γ (F − a₂)/(F − a₁) = −γ − γ(a₁ − a₂) V.
```

The affine classification makes `V = −b/α + κ·exp(α z)` with `α = −γ(a₁ − a₂) ≠ 0`.  If `κ ≠ 0` then
`exp(α z)` attains the nonzero value `(b/α)/κ`, so `V` has a zero — impossible.  Hence `κ = 0`, `V`
is constant, and so is `F`.

Together with the pure-power case this closes every quadratic `c`: the two roots are either distinct
or equal.
-/

namespace GaloisForLFunctions.HTGeometry

/-- Every nonzero complex number is an exponential. -/
theorem exists_exp_eq {w : ℂ} (hw : w ≠ 0) : ∃ z : ℂ, Complex.exp z = w := by
  have hmem : w ∈ Set.range Complex.exp := by
    rw [Complex.range_exp]
    simpa using hw
  exact hmem

/-- **No nonconstant entire solution of a quadratic autonomous equation with distinct roots.**
Inverting `F − a₁` turns `F' = γ(F − a₁)(F − a₂)` into the affine equation
`V' = −γ − γ(a₁ − a₂) V`, whose solutions are `−b/α + κ·exp(α z)`; a nonzero `κ` would make `V`
vanish somewhere, and `κ = 0` makes `F` constant. -/
theorem eq_const_of_deriv_eq_quadratic {gam a₁ a₂ : ℂ} (hgam : gam ≠ 0) (hne : a₁ ≠ a₂)
    {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    (heq : ∀ z, deriv F z = gam * (F z - a₁) * (F z - a₂)) :
    ∃ b : ℂ, F = fun _ => b := by
  classical
  set c : Polynomial ℂ :=
    Polynomial.C gam * (Polynomial.X - Polynomial.C a₁) * (Polynomial.X - Polynomial.C a₂) with hc
  have hceval : ∀ y : ℂ, c.eval y = gam * (y - a₁) * (y - a₂) := by
    intro y
    rw [hc]
    simp
  have heq' : ∀ z, deriv F z = c.eval (F z) := by
    intro z
    rw [hceval, heq z]
  by_cases hconst : ∃ b : ℂ, F = fun _ => b
  · exact hconst
  -- `F` omits `a₁`
  have homit : ∀ z, F z ≠ a₁ := by
    intro z hz
    exact hconst ⟨a₁, eq_const_of_root_of_deriv_eq_comp (by rw [hceval]; ring) hF heq' hz⟩
  have hsub : ∀ z, F z - a₁ ≠ 0 := fun z h => homit z (by linear_combination h)
  set V : ℂ → ℂ := fun z => (F z - a₁)⁻¹ with hV
  have hVdiff : Differentiable ℂ V := fun z => ((hF z).sub_const a₁).inv (hsub z)
  set alpha : ℂ := -(gam * (a₁ - a₂)) with halpha
  have halpha0 : alpha ≠ 0 := by
    rw [halpha]
    simp only [neg_ne_zero]
    exact mul_ne_zero hgam (sub_ne_zero.mpr hne)
  have hVderiv : ∀ z, deriv V z = alpha * V z + -gam := by
    intro z
    have h1 : HasDerivAt (fun w => F w - a₁) (gam * (F z - a₁) * (F z - a₂)) z := by
      have := (hF z).hasDerivAt
      rw [heq z] at this
      simpa using this.sub_const a₁
    have h2 := h1.inv (hsub z)
    have hne2 : (F z - a₁) ≠ 0 := hsub z
    have h3 : -(gam * (F z - a₁) * (F z - a₂)) / (F z - a₁) ^ (2 : ℕ)
        = alpha * (F z - a₁)⁻¹ + -gam := by
      rw [halpha, div_eq_iff (pow_ne_zero 2 hne2)]
      field_simp
      ring
    rw [h3] at h2
    exact h2.deriv
  obtain ⟨kappa, hkappa⟩ : ∃ k : ℂ, ∀ z, V z = -(-gam / alpha) + k * Complex.exp (alpha * z) := by
    refine ⟨V 0 + -gam / alpha, fun z => ?_⟩
    have := congrFun (eq_briotBouquetMap_of_deriv_eq_affine halpha0 hVdiff hVderiv) z
    rw [briotBouquetMap] at this
    simpa using this
  have hVne : ∀ z, V z ≠ 0 := fun z => inv_ne_zero (hsub z)
  have hquot : -gam / alpha ≠ 0 := div_ne_zero (neg_ne_zero.mpr hgam) halpha0
  have hkappa0 : kappa = 0 := by
    by_contra hk
    obtain ⟨u, hu⟩ := exists_exp_eq (w := (-gam / alpha) / kappa) (div_ne_zero hquot hk)
    have hz := hkappa (u / alpha)
    rw [show alpha * (u / alpha) = u by field_simp, hu] at hz
    have hz2 : V (u / alpha) = 0 := by
      rw [hz]
      field_simp
      ring
    exact hVne (u / alpha) hz2
  -- `V` is constant, hence so is `F`
  refine absurd ?_ hconst
  refine ⟨a₁ + (-(-gam / alpha))⁻¹, ?_⟩
  funext z
  have hVz : V z = -(-gam / alpha) := by rw [hkappa z, hkappa0]; ring
  have : (F z - a₁)⁻¹ = -(-gam / alpha) := hVz
  have hFz : F z - a₁ = (-(-gam / alpha))⁻¹ := by
    rw [← this, inv_inv]
  linear_combination hFz

end GaloisForLFunctions.HTGeometry
