import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# The radius moment cone of a decreasing half-line density

A decreasing density is a positive mixture of flat intervals.  The polynomial
`x^3 * (x^4 + α*x^2 + β)^2` is nonnegative, and integration by parts makes
its derivative a positive source functional.  This is the shifted Gram form
for the radius mixing law, without constructing that law as a measure.
-/

open MeasureTheory Set
namespace GaloisForLFunctions.HTGeometry
noncomputable section

def radiusQuadraticPrimitive (α β x : ℝ) : ℝ :=
  x ^ (11 : ℕ) + (2 * α) * x ^ (9 : ℕ) +
    (α ^ (2 : ℕ) + 2 * β) * x ^ (7 : ℕ) +
    (2 * α * β) * x ^ (5 : ℕ) + β ^ (2 : ℕ) * x ^ (3 : ℕ)

def radiusQuadraticDerivative (α β x : ℝ) : ℝ :=
  11 * x ^ (10 : ℕ) + (18 * α) * x ^ (8 : ℕ) +
    (7 * α ^ (2 : ℕ) + 14 * β) * x ^ (6 : ℕ) +
    (10 * α * β) * x ^ (4 : ℕ) + (3 * β ^ (2 : ℕ)) * x ^ (2 : ℕ)

private theorem radiusQuadraticPrimitive_nonneg (α β x : ℝ) (hx : 0 ≤ x) :
    0 ≤ radiusQuadraticPrimitive α β x := by
  have heq : radiusQuadraticPrimitive α β x =
      x ^ (3 : ℕ) * (x ^ (4 : ℕ) + α * x ^ (2 : ℕ) + β) ^ (2 : ℕ) := by
    dsimp [radiusQuadraticPrimitive]
    ring
  rw [heq]
  positivity

private theorem hasDerivAt_radiusQuadraticPrimitive (α β x : ℝ) :
    HasDerivAt (radiusQuadraticPrimitive α β)
      (radiusQuadraticDerivative α β x) x := by
  have h := ((((hasDerivAt_pow 11 x).add
      ((hasDerivAt_pow 9 x).const_mul (2 * α))).add
      ((hasDerivAt_pow 7 x).const_mul (α ^ (2 : ℕ) + 2 * β))).add
      ((hasDerivAt_pow 5 x).const_mul (2 * α * β))).add
      ((hasDerivAt_pow 3 x).const_mul (β ^ (2 : ℕ)))
  have hf : radiusQuadraticPrimitive α β =
      ((((fun t : ℝ => t ^ (11 : ℕ)) +
        (fun t => (2 * α) * t ^ (9 : ℕ))) +
        (fun t => (α ^ (2 : ℕ) + 2 * β) * t ^ (7 : ℕ))) +
        (fun t => (2 * α * β) * t ^ (5 : ℕ))) +
        (fun t => β ^ (2 : ℕ) * t ^ (3 : ℕ)) := by
    funext t
    simp [radiusQuadraticPrimitive, Pi.add_apply]
  rw [← hf] at h
  refine h.congr_deriv ?_
  dsimp [radiusQuadraticDerivative]
  ring

/-- The radius shifted-Gram polynomial has nonnegative density-weighted
derivative on every finite interval. -/
theorem antitone_density_radiusQuadratic_interval
    (ρ : ℝ → ℝ) (hρ : Differentiable ℝ ρ)
    (hρ' : Continuous (deriv ρ))
    (R α β : ℝ) (hR : 0 ≤ R) (hρR : 0 ≤ ρ R)
    (hder : ∀ x ∈ Ioc (0 : ℝ) R, deriv ρ x ≤ 0) :
    0 ≤ ∫ x : ℝ in 0..R,
      ρ x * radiusQuadraticDerivative α β x := by
  let F : ℝ → ℝ := radiusQuadraticPrimitive α β
  let g : ℝ → ℝ := radiusQuadraticDerivative α β
  have hFder (x : ℝ) : HasDerivAt F (g x) x :=
    hasDerivAt_radiusQuadraticPrimitive α β x
  have hgcont : Continuous g := by
    unfold g radiusQuadraticDerivative
    fun_prop
  have hρint : IntervalIntegrable (deriv ρ) volume 0 R :=
    hρ'.intervalIntegrable _ _
  have hgint : IntervalIntegrable g volume 0 R :=
    hgcont.intervalIntegrable _ _
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := ρ) (u' := deriv ρ) (v := F) (v' := g)
    (fun x _ => (hρ x).hasDerivAt) (fun x _ => hFder x)
    hρint hgint
  have hFzero : F 0 = 0 := by norm_num [F, radiusQuadraticPrimitive]
  have hend : 0 ≤ ρ R * F R :=
    mul_nonneg hρR (radiusQuadraticPrimitive_nonneg α β R hR)
  have hneg : ∫ x : ℝ in 0..R, deriv ρ x * F x ≤ 0 := by
    have hnonneg : 0 ≤ ∫ x : ℝ in 0..R, -(deriv ρ x * F x) := by
      apply intervalIntegral.integral_nonneg hR
      intro x hx
      by_cases hx0 : x = 0
      · subst x
        simp [F, radiusQuadraticPrimitive]
      have hxpos : 0 < x := lt_of_le_of_ne hx.1 (Ne.symm hx0)
      exact neg_nonneg.mpr
        (mul_nonpos_of_nonpos_of_nonneg
          (hder x ⟨hxpos, hx.2⟩)
          (radiusQuadraticPrimitive_nonneg α β x hx.1))
    rw [intervalIntegral.integral_neg] at hnonneg
    linarith
  change 0 ≤ ∫ x : ℝ in 0..R, ρ x * g x
  rw [hibp, hFzero, mul_zero, sub_zero]
  linarith

/-- The positive radius shifted-Gram functional on the half-line. -/
theorem antitone_density_radiusQuadratic_Ioi
    (ρ : ℝ → ℝ) (hρ : Differentiable ℝ ρ)
    (hρ' : Continuous (deriv ρ))
    (hρnonneg : ∀ x : ℝ, 0 ≤ x → 0 ≤ ρ x)
    (hder : ∀ x : ℝ, 0 < x → deriv ρ x ≤ 0)
    (α β : ℝ)
    (hint : IntegrableOn
      (fun x : ℝ => ρ x * radiusQuadraticDerivative α β x) (Ioi 0)) :
    0 ≤ ∫ x : ℝ in Ioi 0,
      ρ x * radiusQuadraticDerivative α β x := by
  have hright := intervalIntegral_tendsto_integral_Ioi 0 hint Filter.tendsto_id
  apply le_of_tendsto_of_tendsto tendsto_const_nhds hright
  filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with R hR
  exact antitone_density_radiusQuadratic_interval ρ hρ hρ' R α β hR
    (hρnonneg R hR) (fun x hx => hder x hx.1)

end
end GaloisForLFunctions.HTGeometry
