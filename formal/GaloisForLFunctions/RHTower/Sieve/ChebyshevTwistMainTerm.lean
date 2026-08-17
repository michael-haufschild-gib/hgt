import GaloisForLFunctions.RHTower.Sieve.VerticalPoleIntegral
import GaloisForLFunctions.RHTower.Sieve.ChebyshevTwistPerronIdentity

/-!
# The twisted main term

The pole of the twisted Chebyshev integrand sits at ordinate `-τ`, so truncating the Perron line
symmetrically no longer truncates symmetrically *about the pole*.  The closed form therefore has two
pieces rather than one: over an arbitrary interval the pole kernel integrates to

```text
∫_a^b (α + iu)⁻¹ du  =  (arctan(b/α) - arctan(a/α))  -  (i/2)·(log(α²+b²) - log(α²+a²)) ,
```

the first summand coming from the even real part and the second from the odd imaginary part, which
no longer cancels.  At `τ = 0` the logarithms agree and the arctan difference is `2 arctan(T/α)`,
recovering the untwisted main term.

Substituting `α = d - 1` and the shift `u = y + τ` gives the twisted main term of the truncated
Chebyshev identity, with coefficient the cutoff's transform at the twist pole `1 - iτ`.
-/

namespace RHTower.Sieve

open Complex MeasureTheory

/-- The real part of the pole kernel, integrated over an arbitrary interval. -/
theorem integral_re_pole_interval {α a b : ℝ} (hα : α ≠ 0) :
    (∫ u : ℝ in a..b, α / (α ^ 2 + u ^ 2))
      = Real.arctan (b / α) - Real.arctan (a / α) := by
  have hpt : ∀ u : ℝ, α / (α ^ 2 + u ^ 2) = α⁻¹ * (1 + (u / α) ^ 2)⁻¹ := by
    intro u
    have hsq : (0 : ℝ) < α ^ 2 + u ^ 2 := by positivity
    field_simp
  rw [intervalIntegral.integral_congr (g := fun u => α⁻¹ * (1 + (u / α) ^ 2)⁻¹)
    (fun u _ => hpt u)]
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_div (fun x : ℝ => (1 + x ^ 2)⁻¹) hα,
    integral_inv_one_add_sq, smul_eq_mul]
  field_simp

/-- The imaginary part of the pole kernel, integrated over an arbitrary interval. -/
theorem integral_im_pole_interval {α a b : ℝ} (hα : α ≠ 0) :
    (∫ u : ℝ in a..b, u / (α ^ 2 + u ^ 2))
      = (Real.log (α ^ 2 + b ^ 2) - Real.log (α ^ 2 + a ^ 2)) / 2 := by
  have hpos : ∀ u : ℝ, (0 : ℝ) < α ^ 2 + u ^ 2 := fun u => by positivity
  have hderiv : ∀ u ∈ Set.uIcc a b,
      HasDerivAt (fun u : ℝ => Real.log (α ^ 2 + u ^ 2) / 2) (u / (α ^ 2 + u ^ 2)) u := by
    intro u _
    have h1 : HasDerivAt (fun u : ℝ => α ^ 2 + u ^ 2) (2 * u) u := by
      simpa using (hasDerivAt_pow 2 u).const_add (α ^ 2)
    have h2 := (h1.log (ne_of_gt (hpos u))).div_const 2
    have hval : 2 * u / (α ^ 2 + u ^ 2) / 2 = u / (α ^ 2 + u ^ 2) := by
      field_simp
    rw [hval] at h2
    exact h2
  have hcont : Continuous fun u : ℝ => u / (α ^ 2 + u ^ 2) :=
    continuous_id.div (by fun_prop) (fun u => ne_of_gt (hpos u))
  have hint : IntervalIntegrable (fun u : ℝ => u / (α ^ 2 + u ^ 2)) volume a b :=
    hcont.intervalIntegrable a b
  have := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  rw [this]
  ring

/-- **The vertical pole integral over a shifted symmetric interval.**  The pole sits at ordinate
`-τ`, so the truncated integral is no longer symmetric about it: the arctan difference is the real
part, and the logarithm the imaginary one. -/
theorem integral_vertical_pole_shift {α T τ : ℝ} (hα : α ≠ 0) :
    (∫ y : ℝ in (-T)..T, ((α : ℂ) + ((y + τ : ℝ)) * Complex.I)⁻¹)
      = ((Real.arctan ((T + τ) / α) - Real.arctan ((-T + τ) / α) : ℝ) : ℂ)
        - (((Real.log (α ^ 2 + (T + τ) ^ 2)
              - Real.log (α ^ 2 + (-T + τ) ^ 2)) / 2 : ℝ) : ℂ) * Complex.I := by
  have hsplit : ∀ y : ℝ, ((α : ℂ) + ((y + τ : ℝ)) * Complex.I)⁻¹
      = ((α / (α ^ 2 + (y + τ) ^ 2) : ℝ) : ℂ)
        - (((y + τ) / (α ^ 2 + (y + τ) ^ 2) : ℝ) : ℂ) * Complex.I := fun y =>
    inv_add_mul_I_eq hα
  rw [intervalIntegral.integral_congr
    (g := fun y : ℝ => ((α / (α ^ 2 + (y + τ) ^ 2) : ℝ) : ℂ)
      - (((y + τ) / (α ^ 2 + (y + τ) ^ 2) : ℝ) : ℂ) * Complex.I) (fun y _ => hsplit y)]
  have hreR : Continuous fun y : ℝ => (α / (α ^ 2 + (y + τ) ^ 2) : ℝ) := by
    refine Continuous.div continuous_const (by fun_prop) ?_
    intro y; positivity
  have hre : Continuous fun y : ℝ => ((α / (α ^ 2 + (y + τ) ^ 2) : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp hreR
  have himR : Continuous fun y : ℝ => ((y + τ) / (α ^ 2 + (y + τ) ^ 2) : ℝ) := by
    refine Continuous.div (by fun_prop) (by fun_prop) ?_
    intro y; positivity
  have him : Continuous fun y : ℝ =>
      (((y + τ) / (α ^ 2 + (y + τ) ^ 2) : ℝ) : ℂ) * Complex.I :=
    (Complex.continuous_ofReal.comp himR).mul continuous_const
  rw [intervalIntegral.integral_sub (hre.intervalIntegrable _ _) (him.intervalIntegrable _ _)]
  congr 1
  · rw [intervalIntegral.integral_ofReal]
    congr 1
    rw [intervalIntegral.integral_comp_add_right (fun u : ℝ => α / (α ^ 2 + u ^ 2)) τ,
      integral_re_pole_interval hα]
  · rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_ofReal]
    congr 2
    rw [intervalIntegral.integral_comp_add_right (fun u : ℝ => u / (α ^ 2 + u ^ 2)) τ,
      integral_im_pole_interval hα]

/-- **The twisted pole term on the truncated Perron line.**  The main term of the twisted Chebyshev
sum, in closed form: the arctan difference is its real part and the logarithm its imaginary one. -/
theorem integral_twist_pole_term_line {N H : ℝ} {d T τ : ℝ} (hd : 1 < d) :
    (∫ y : ℝ in (-T)..T,
        mellin (fun x : ℝ => ((GaloisForLFunctions.HTGeometry.smoothWeight N H x : ℝ) : ℂ))
            (twistPole τ)
          * ((d : ℂ) + (y : ℝ) * Complex.I + (τ : ℂ) * Complex.I - 1)⁻¹)
      = mellin (fun x : ℝ => ((GaloisForLFunctions.HTGeometry.smoothWeight N H x : ℝ) : ℂ))
            (twistPole τ)
          * ((((Real.arctan ((T + τ) / (d - 1))
                - Real.arctan ((-T + τ) / (d - 1)) : ℝ)) : ℂ)
            - ((((Real.log ((d - 1) ^ 2 + (T + τ) ^ 2)
                  - Real.log ((d - 1) ^ 2 + (-T + τ) ^ 2)) / 2 : ℝ)) : ℂ) * Complex.I) := by
  have hα : (d - 1 : ℝ) ≠ 0 := by
    intro h
    have : d = 1 := by linarith
    exact absurd this (by linarith)
  have hrw : ∀ y : ℝ, (d : ℂ) + (y : ℝ) * Complex.I + (τ : ℂ) * Complex.I - 1
      = (((d - 1 : ℝ)) : ℂ) + ((y + τ : ℝ)) * Complex.I := by
    intro y
    push_cast
    ring
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_congr
      (g := fun y : ℝ => ((((d - 1 : ℝ)) : ℂ) + ((y + τ : ℝ)) * Complex.I)⁻¹)
      (fun y _ => by rw [hrw y]),
    integral_vertical_pole_shift hα]

end RHTower.Sieve
