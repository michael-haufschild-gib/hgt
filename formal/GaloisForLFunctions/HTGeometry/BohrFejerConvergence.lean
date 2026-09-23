import GaloisForLFunctions.HTGeometry.BohrFejerPointwise
import GaloisForLFunctions.HTGeometry.BohrMeanMonotone
import GaloisForLFunctions.HTGeometry.BohrParseval

/-!
# Fejér convergence along a single frequency progression

Averaging the pointwise Fejér estimate.  The kernel is a nonnegative trigonometric polynomial of
mean one, so the mean of `K_N(u) f(t+u)` differs from `f t` by at most the mean of
`K_N(u) ‖f(t+u) - f t‖`; the pointwise bound turns that into the almost-period error, the modulus of
continuity on the concentration scale, and a tail term that vanishes as `N → ∞`.
-/

open Filter Topology

open scoped BoundedContinuousFunction Real

namespace GaloisForLFunctions

open _root_.HTGeometry

variable {f : ℝ →ᵇ ℂ}

/-- The Fejér kernel is almost periodic: it is a trigonometric polynomial. -/
theorem isBohrAlmostPeriodic_fejerKernel (β : ℝ) (N : ℕ) :
    HTGeometry.IsBohrAlmostPeriodic (fejerKernel β N) := by
  classical
  have h : fejerKernel β N = fun u => ∑ p ∈ Finset.range (N + 1) ×ˢ Finset.range (N + 1),
      ((N : ℂ) + 1)⁻¹ * expChar (((p.1 : ℝ) - (p.2 : ℝ)) * β) u :=
    funext fun u => fejerKernel_eq_sum β N u
  rw [h]
  exact isBohrAlmostPeriodic_sum _
    (fun p _ => continuous_const.mul (continuous_expChar _))
    (fun p _ => isBohrAlmostPeriodic_const_mul _ (isBohrAlmostPeriodic_expChar _))

/-- The real form of the Fejér kernel is continuous. -/
theorem continuous_fejerKernelReal (β : ℝ) (N : ℕ) :
    Continuous fun u => ‖fejerSum β N u‖ ^ (2 : ℕ) / ((N : ℝ) + 1) := by
  have hre : (fun u => ‖fejerSum β N u‖ ^ (2 : ℕ) / ((N : ℝ) + 1))
      = fun u => (fejerKernel β N u).re := by
    funext u
    rw [fejerKernel_eq_ofReal β N u, Complex.ofReal_re]
  rw [hre]
  exact Complex.continuous_re.comp (continuous_fejerKernel β N)

/-- The real form of the Fejér kernel is almost periodic. -/
theorem isBohrAlmostPeriodic_fejerKernelReal (β : ℝ) (N : ℕ) :
    HTGeometry.IsBohrAlmostPeriodic fun u => ‖fejerSum β N u‖ ^ (2 : ℕ) / ((N : ℝ) + 1) := by
  intro ε hε
  obtain ⟨L, hL, hdense⟩ := isBohrAlmostPeriodic_fejerKernel β N ε hε
  refine ⟨L, hL, fun a => ?_⟩
  obtain ⟨τ, hτmem, hτ⟩ := hdense a
  refine ⟨τ, hτmem, fun x => ?_⟩
  have hx := hτ x
  rw [fejerKernel_eq_ofReal β N (x + τ), fejerKernel_eq_ofReal β N x, ← Complex.ofReal_sub,
    Complex.norm_real] at hx
  exact hx

/-- The real form of the Fejér kernel has mean one. -/
theorem bohrMean_fejerKernelReal {β : ℝ} (hβ : β ≠ 0) (N : ℕ) :
    bohrMean (fun u => ‖fejerSum β N u‖ ^ (2 : ℕ) / ((N : ℝ) + 1)) = 1 := by
  have h := bohrMean_fejerKernel hβ N
  have hcast : bohrMean (fun u => ((‖fejerSum β N u‖ ^ (2 : ℕ) / ((N : ℝ) + 1) : ℝ) : ℂ))
      = ((bohrMean (fun u => ‖fejerSum β N u‖ ^ (2 : ℕ) / ((N : ℝ) + 1)) : ℝ) : ℂ) :=
    bohrMean_ofReal (continuous_fejerKernelReal β N) (isBohrAlmostPeriodic_fejerKernelReal β N)
  rw [funext fun u => fejerKernel_eq_ofReal β N u, hcast] at h
  exact_mod_cast h

/-- **Fejér convergence, quantitatively.**  For a bounded uniformly continuous function with a
relatively compact orbit whose hull frequencies all lie in `βℤ`, the Fejér mean of order `N`
approximates the function pointwise up to the almost-period error `2ε`, the modulus of continuity
`ω` on the scale `ρ`, and a tail term of size `4‖f‖/((N+1)c)`. -/
theorem norm_bohrMean_fejer_sub_le {β : ℝ} (hβ : β ≠ 0)
    (hf : UniformContinuous fun x => f x) (htb : HasTotallyBoundedOrbit fun x => f x)
    (hfreq : ∀ μ : ℝ, IsBohrHullFrequency f μ → ∃ k : ℤ, μ = k * β)
    {ε ρ ω c : ℝ} (hε : 0 < ε) (hρ : 0 < ρ)
    (hmod : ∀ x y : ℝ, |x - y| ≤ ρ → ‖f x - f y‖ ≤ ω)
    (hc : 0 < c) (hcρ : Real.pi * Real.sqrt (c / 2) ≤ |β| * ρ) (N : ℕ) (t : ℝ) :
    ‖bohrMean (fun u => fejerKernel β N u * f (t + u)) - f t‖
      ≤ 2 * ε + ω + 2 * ‖f‖ * (2 / (((N : ℝ) + 1) * c)) := by
  classical
  set C : ℝ := 2 * ‖f‖ * (2 / (((N : ℝ) + 1) * c)) with hC
  set Kr : ℝ → ℝ := fun u => ‖fejerSum β N u‖ ^ (2 : ℕ) / ((N : ℝ) + 1) with hKrdef
  have hKcont : Continuous (fejerKernel β N) := continuous_fejerKernel β N
  have hKap : HTGeometry.IsBohrAlmostPeriodic (fejerKernel β N) :=
    isBohrAlmostPeriodic_fejerKernel β N
  have hKreal : ∀ u, fejerKernel β N u = ((Kr u : ℝ) : ℂ) := fun u => fejerKernel_eq_ofReal β N u
  have hKrcont : Continuous Kr := continuous_fejerKernelReal β N
  have hKrap : HTGeometry.IsBohrAlmostPeriodic Kr := isBohrAlmostPeriodic_fejerKernelReal β N
  -- the translate of `f`
  have hfcont : Continuous fun u : ℝ => f (t + u) :=
    f.continuous.comp (continuous_const.add continuous_id)
  have hfap : HTGeometry.IsBohrAlmostPeriodic fun u : ℝ => f (t + u) := by
    have hbase : HTGeometry.IsBohrAlmostPeriodic (fun x => f x) :=
      isBohrAlmostPeriodic_of_hasTotallyBoundedOrbit htb
    have h := isBohrAlmostPeriodic_comp_add_const hbase t
    have hcomm : (fun u : ℝ => f (t + u)) = fun u : ℝ => f (u + t) := by
      funext u; rw [add_comm]
    rw [hcomm]
    exact h
  -- the difference is a single mean
  have hprodc : Continuous fun u : ℝ => fejerKernel β N u * f (t + u) := hKcont.mul hfcont
  have hproda : HTGeometry.IsBohrAlmostPeriodic fun u : ℝ => fejerKernel β N u * f (t + u) :=
    isBohrAlmostPeriodic_mul hKcont hKap hfcont hfap
  have hconstc : Continuous fun u : ℝ => f t * fejerKernel β N u := continuous_const.mul hKcont
  have hconsta : HTGeometry.IsBohrAlmostPeriodic fun u : ℝ => f t * fejerKernel β N u :=
    isBohrAlmostPeriodic_const_mul _ hKap
  have hmeanconst : bohrMean (fun u : ℝ => f t * fejerKernel β N u) = f t := by
    rw [bohrMean_const_mul _ hKcont hKap, bohrMean_fejerKernel hβ N, mul_one]
  have hsub : bohrMean (fun u : ℝ => fejerKernel β N u * f (t + u)) - f t
      = bohrMean (fun u : ℝ => fejerKernel β N u * f (t + u) - f t * fejerKernel β N u) := by
    rw [bohrMean_sub hprodc hproda hconstc hconsta, hmeanconst]
  have hgc : Continuous fun u : ℝ => fejerKernel β N u * f (t + u) - f t * fejerKernel β N u :=
    hprodc.sub hconstc
  have hga : HTGeometry.IsBohrAlmostPeriodic fun u : ℝ =>
      fejerKernel β N u * f (t + u) - f t * fejerKernel β N u :=
    isBohrAlmostPeriodic_sub hprodc hproda hconstc hconsta
  rw [hsub]
  refine le_trans (norm_bohrMean_le_bohrMean_norm hgc hga) ?_
  -- the integrand's norm, and the bound supplied by the pointwise estimate
  have hnormeq : ∀ u : ℝ,
      ‖fejerKernel β N u * f (t + u) - f t * fejerKernel β N u‖ = Kr u * ‖f (t + u) - f t‖ := by
    intro u
    have hfac : fejerKernel β N u * f (t + u) - f t * fejerKernel β N u
        = fejerKernel β N u * (f (t + u) - f t) := by ring
    rw [hfac, norm_mul, hKreal u, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (fejerKernel_nonneg β N u)]
  have hnormc : Continuous fun u : ℝ =>
      ‖fejerKernel β N u * f (t + u) - f t * fejerKernel β N u‖ := hgc.norm
  have hnorma : HTGeometry.IsBohrAlmostPeriodic fun u : ℝ =>
      ‖fejerKernel β N u * f (t + u) - f t * fejerKernel β N u‖ := isBohrAlmostPeriodic_norm_real hga
  have hboundc : Continuous fun u : ℝ => (2 * ε + ω) * Kr u + C :=
    (continuous_const.mul hKrcont).add continuous_const
  have hbounda : HTGeometry.IsBohrAlmostPeriodic fun u : ℝ => (2 * ε + ω) * Kr u + C :=
    isBohrAlmostPeriodic_add_const_real (isBohrAlmostPeriodic_const_mul_real (2 * ε + ω) hKrap) C
  refine le_trans (bohrMean_le_bohrMean hnormc hnorma hboundc hbounda ?_) ?_
  · intro u
    have hpt := fejer_pointwise_bound hβ hf htb hfreq hε hρ hmod hc hcρ N t u
    rw [hnormeq u]
    calc Kr u * ‖f (t + u) - f t‖ ≤ Kr u * (2 * ε + ω) + C := hpt
      _ = (2 * ε + ω) * Kr u + C := by ring
  · have hmulc : Continuous fun u : ℝ => (2 * ε + ω) * Kr u := continuous_const.mul hKrcont
    have hmula : HTGeometry.IsBohrAlmostPeriodic fun u : ℝ => (2 * ε + ω) * Kr u :=
      isBohrAlmostPeriodic_const_mul_real (2 * ε + ω) hKrap
    have hmeanKr : bohrMean Kr = 1 := by
      rw [hKrdef]
      exact bohrMean_fejerKernelReal hβ N
    rw [bohrMean_add_const_real hmulc hmula C,
      bohrMean_const_mul_real (2 * ε + ω) hKrcont hKrap, hmeanKr]
    have hcalc : (2 * ε + ω) * 1 + C = 2 * ε + ω + C := by ring
    rw [hcalc]

end GaloisForLFunctions
