import GaloisForLFunctions.HTGeometry.DifferentialAlgebraicAntiderivative
import GaloisForLFunctions.HTGeometry.HypertranscendencePolynomial

/-!
# No analytic reparametrisation of two independent clocks into difference form

Suppose two scalar observables of a two-parameter system,

```text
u - v      = a (ρ u - ρ v),
H u - H v  = b (ρ u - ρ v),
```

are both functions of one common spectral coordinate difference.  Differentiating the first
identity separately in each argument shows that `deriv ρ` takes the same value at every pair of
points, and the second identity then transports that rigidity to `H`: its derivative is constant.

Consequently a hypertranscendental clock `H` admits no analytic reparametrisation making the pair
`(u - v, H u - H v)` a difference family: the derivative of an affine function is constant, and an
affine function is differentially algebraic.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

/-- Both identities of a difference reparametrisation force `deriv H` to be constant on the open
set where they hold.  No differentiability of `H` is assumed: the second identity supplies it. -/
theorem deriv_eq_of_difference_reparametrisation
    {s : Set ℂ} (hs : IsOpen s) {H ρ a b : ℂ → ℂ}
    (hρ : ∀ z ∈ s, DifferentiableAt ℂ ρ z)
    (ha : ∀ w : ℂ, DifferentiableAt ℂ a w)
    (hb : ∀ w : ℂ, DifferentiableAt ℂ b w)
    (h1 : ∀ u ∈ s, ∀ v ∈ s, u - v = a (ρ u - ρ v))
    (h2 : ∀ u ∈ s, ∀ v ∈ s, H u - H v = b (ρ u - ρ v))
    {u v : ℂ} (hu : u ∈ s) (hv : v ∈ s) :
    deriv H u = deriv H v := by
  -- the first identity, differentiated in the first argument at `u`
  have hchainA₁ : HasDerivAt (fun z => a (ρ z - ρ v))
      (deriv a (ρ u - ρ v) * deriv ρ u) u :=
    HasDerivAt.comp u (ha (ρ u - ρ v)).hasDerivAt
      (((hρ u hu).hasDerivAt).sub_const (ρ v))
  have hevA₁ : (fun z => z - v) =ᶠ[nhds u] fun z => a (ρ z - ρ v) :=
    Filter.eventuallyEq_of_mem (hs.mem_nhds hu) fun z hz => h1 z hz v hv
  have hA₁ : (1 : ℂ) = deriv a (ρ u - ρ v) * deriv ρ u :=
    (((hasDerivAt_id u).sub_const v).congr_of_eventuallyEq hevA₁.symm).unique hchainA₁
  -- the first identity, differentiated in the second argument at `v`
  have hchainA₂ : HasDerivAt (fun z => a (ρ u - ρ z))
      (deriv a (ρ u - ρ v) * -deriv ρ v) v :=
    HasDerivAt.comp v (ha (ρ u - ρ v)).hasDerivAt
      (((hρ v hv).hasDerivAt).const_sub (ρ u))
  have hevA₂ : (fun z => u - z) =ᶠ[nhds v] fun z => a (ρ u - ρ z) :=
    Filter.eventuallyEq_of_mem (hs.mem_nhds hv) fun z hz => h1 u hu z hz
  have hA₂ : (-1 : ℂ) = deriv a (ρ u - ρ v) * -deriv ρ v :=
    (((hasDerivAt_id v).const_sub u).congr_of_eventuallyEq hevA₂.symm).unique hchainA₂
  have hane : deriv a (ρ u - ρ v) ≠ 0 := by
    intro h
    rw [h, zero_mul] at hA₁
    exact one_ne_zero hA₁
  have hρeq : deriv ρ u = deriv ρ v := by
    have h₂ : (1 : ℂ) = deriv a (ρ u - ρ v) * deriv ρ v := by
      have := hA₂
      field_simp at this
      linear_combination -this
    exact mul_left_cancel₀ hane (hA₁.symm.trans h₂)
  -- the second identity, differentiated in the first argument at `u`
  have hchainB₁ : HasDerivAt (fun z => H v + b (ρ z - ρ v))
      (deriv b (ρ u - ρ v) * deriv ρ u) u := by
    simpa using
      (HasDerivAt.comp u (hb (ρ u - ρ v)).hasDerivAt
        (((hρ u hu).hasDerivAt).sub_const (ρ v))).const_add (H v)
  have hevB₁ : H =ᶠ[nhds u] fun z => H v + b (ρ z - ρ v) :=
    Filter.eventuallyEq_of_mem (hs.mem_nhds hu) fun z hz => by
      have h := h2 z hz v hv
      linear_combination h
  have hB₁ : HasDerivAt H (deriv b (ρ u - ρ v) * deriv ρ u) u :=
    hchainB₁.congr_of_eventuallyEq hevB₁
  -- the second identity, differentiated in the second argument at `v`
  have hchainB₂ : HasDerivAt (fun z => H u - b (ρ u - ρ z))
      (deriv b (ρ u - ρ v) * deriv ρ v) v := by
    have h := (HasDerivAt.comp v (hb (ρ u - ρ v)).hasDerivAt
      (((hρ v hv).hasDerivAt).const_sub (ρ u))).const_sub (H u)
    simpa using h
  have hevB₂ : H =ᶠ[nhds v] fun z => H u - b (ρ u - ρ z) :=
    Filter.eventuallyEq_of_mem (hs.mem_nhds hv) fun z hz => by
      have h := h2 u hu z hz
      linear_combination -h
  have hB₂ : HasDerivAt H (deriv b (ρ u - ρ v) * deriv ρ v) v :=
    hchainB₂.congr_of_eventuallyEq hevB₂
  rw [hB₁.deriv, hB₂.deriv, hρeq]

/-- **A hypertranscendental clock has no difference form.**  There is no analytic spectral
coordinate `ρ` and no pair of analytic functions `a, b` turning the two independent clocks
`u - v` and `H u - H v` into functions of a single difference. -/
theorem not_exists_difference_reparametrisation_of_hypertranscendental
    {H : ℂ → ℂ} (hH : Hypertranscendental H) :
    ¬ ∃ ρ a b : ℂ → ℂ,
      (∀ z : ℂ, DifferentiableAt ℂ ρ z) ∧ (∀ w : ℂ, DifferentiableAt ℂ a w) ∧
        (∀ w : ℂ, DifferentiableAt ℂ b w) ∧
        (∀ u v : ℂ, u - v = a (ρ u - ρ v)) ∧
        (∀ u v : ℂ, H u - H v = b (ρ u - ρ v)) := by
  rintro ⟨ρ, a, b, hρ, ha, hb, h1, h2⟩
  have hconst : ∀ z : ℂ, deriv H z = deriv H 0 :=
    fun z => deriv_eq_of_difference_reparametrisation isOpen_univ
      (fun w _ => hρ w) ha hb (fun u _ v _ => h1 u v) (fun u _ v _ => h2 u v)
      (Set.mem_univ z) (Set.mem_univ 0)
  have hderiv : deriv H = fun _ => deriv H 0 := funext hconst
  exact hH (differentiallyAlgebraic_of_deriv
    (by rw [hderiv]; exact differentiallyAlgebraic_const (deriv H 0)))

end GaloisForLFunctions.HTGeometry
