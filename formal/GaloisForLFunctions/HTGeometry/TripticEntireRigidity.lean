import GaloisForLFunctions.HTGeometry.EllipticLiouvilleFacetCodimension
import GaloisForLFunctions.HTGeometry.BoundaryWedgePeriodRankObstruction

/-!
# Entire members of the mixed-constraint class are constant

A meromorphic function that is `ω₁`-periodic and whose mixed second difference along two further
steps vanishes has, in the pole-free case, no freedom at all.

The mechanism is two applications of Liouville.  If `f` is entire and both of its difference
operators produce constants, then `deriv f` is invariant under a full lattice, hence constant, so
`f` is affine; and an affine function with a genuine period is constant.  Feeding this back, a
vanishing mixed difference makes the single difference `Δ_σ f` entire and lattice-periodic, hence
constant, and the previous step applies.

* `deriv_periodic_of_shift_add_const` — a shift that changes a function by a constant is a period
  of its derivative;
* `exists_affine_of_entire_of_shift_const` — two independent such shifts force an affine function;
* `const_of_entire_periodic_of_shift_const` — one of them being a genuine period forces a constant,
  and the other constant is then `0`;
* `const_of_entire_of_periodic_of_mixed_const_zero` — the form the mixed-constraint class uses.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex

/-- A step along which a function changes by a constant is a period of its derivative. -/
theorem deriv_periodic_of_shift_add_const {f : ℂ → ℂ} (hf : Differentiable ℂ f) {ω c : ℂ}
    (h : ∀ z, f (z + ω) = f z + c) : Function.Periodic (deriv f) ω := by
  intro z
  have hcomp : HasDerivAt (fun w => f (w + ω)) (deriv f (z + ω)) z := by
    have hinner : HasDerivAt (fun w : ℂ => w + ω) 1 z := (hasDerivAt_id z).add_const ω
    have hc := (hf (z + ω)).hasDerivAt.comp z hinner
    rw [mul_one] at hc
    exact hc
  have hfun : (fun w => f (w + ω)) = fun w => f w + c := funext h
  rw [hfun] at hcomp
  exact hcomp.unique ((hf z).hasDerivAt.add_const c)

/-- **Two independent constant-change steps force an affine function.**  The derivative is entire
and invariant under the full lattice they generate, hence constant. -/
theorem exists_affine_of_entire_of_shift_const {ω₁ ω₂ : ℂ}
    (hindep : LinearIndependent ℝ ![ω₁, ω₂]) {f : ℂ → ℂ} (hf : Differentiable ℂ f) {c₁ c₂ : ℂ}
    (h₁ : ∀ z, f (z + ω₁) = f z + c₁) (h₂ : ∀ z, f (z + ω₂) = f z + c₂) :
    ∃ k b : ℂ, ∀ z, f z = k * z + b := by
  have hfan : AnalyticOnNhd ℂ f Set.univ := hf.differentiableOn.analyticOnNhd isOpen_univ
  have hdan : AnalyticOnNhd ℂ (deriv f) Set.univ := hfan.deriv
  have hdiff : Differentiable ℂ (deriv f) := fun z => (hdan z (Set.mem_univ z)).differentiableAt
  have hlat : ∀ p ∈ (⟨ω₁, ω₂, hindep⟩ : PeriodPair).lattice, Function.Periodic (deriv f) p := by
    intro p hp
    refine periodic_of_mem_span_range ![ω₁, ω₂] (fun i => ?_) p ?_
    · fin_cases i
      · exact deriv_periodic_of_shift_add_const hf h₁
      · exact deriv_periodic_of_shift_add_const hf h₂
    · rw [range_cons_two]
      exact hp
  have hconst := const_of_lattice_periodic_differentiable ⟨ω₁, ω₂, hindep⟩ hdiff hlat
  set k : ℂ := deriv f 0 with hk
  have hderiv : ∀ z, deriv f z = k := fun z => hconst z 0
  refine ⟨k, f 0, ?_⟩
  have haux : ∀ x y : ℂ, f x - k * x = f y - k * y := by
    refine is_const_of_deriv_eq_zero (f := fun z => f z - k * z) ?_ ?_
    · exact hf.sub ((differentiable_id).const_mul k)
    · intro z
      have hlin : HasDerivAt (fun w : ℂ => k * w) k z := by
        have hi := (hasDerivAt_id z).const_mul k
        rw [mul_one] at hi
        exact hi
      have hd : HasDerivAt (fun w : ℂ => f w - k * w) (deriv f z - k) z :=
        (hf z).hasDerivAt.sub hlin
      rw [hd.deriv, hderiv z, sub_self]
  intro z
  have := haux z 0
  simp only [mul_zero, sub_zero] at this
  linear_combination this

/-- **An entire function with a genuine period and one constant-change step is constant**, and the
constant change is then `0`. -/
theorem const_of_entire_periodic_of_shift_const {ω₁ ω₂ : ℂ}
    (hindep : LinearIndependent ℝ ![ω₁, ω₂]) {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (h₁ : Function.Periodic f ω₁) {c : ℂ} (h₂ : ∀ z, f (z + ω₂) = f z + c) :
    (∀ x y, f x = f y) ∧ c = 0 := by
  have hω₁ : ω₁ ≠ 0 := by
    intro h
    have := hindep.ne_zero 0
    simp [h] at this
  obtain ⟨k, b, hkb⟩ :=
    exists_affine_of_entire_of_shift_const hindep hf (c₁ := 0) (fun z => by
      rw [h₁ z, add_zero]) h₂
  have hk0 : k = 0 := by
    have h0 := h₁ 0
    rw [hkb (0 + ω₁), hkb 0] at h0
    have : k * ω₁ = 0 := by
      rw [zero_add] at h0
      linear_combination h0
    rcases mul_eq_zero.mp this with hk | hω
    · exact hk
    · exact absurd hω hω₁
  have hconst : ∀ x y : ℂ, f x = f y := by
    intro x y
    rw [hkb x, hkb y, hk0]
    ring
  refine ⟨hconst, ?_⟩
  have := h₂ 0
  rw [hconst (0 + ω₂) 0] at this
  linear_combination -this

/-- **The mixed-constraint form.**  An entire function with a genuine period `ω₁` whose mixed second
difference along `τ` and `σ` vanishes is constant.  The single difference `Δ_σ f` is entire and
invariant under the lattice generated by `ω₁` and `τ`, hence constant; the rigidity theorem then
applies along `σ`. -/
theorem const_of_entire_of_periodic_of_mixed_const_zero {ω₁ τ σ : ℂ}
    (hindepτ : LinearIndependent ℝ ![ω₁, τ]) (hindepσ : LinearIndependent ℝ ![ω₁, σ])
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) (h₁ : Function.Periodic f ω₁)
    (hmix : ∀ z, f (z + τ + σ) - f (z + τ) - (f (z + σ) - f z) = 0) :
    ∀ x y, f x = f y := by
  set U : ℂ → ℂ := fun z => f (z + σ) - f z with hU
  have hUdiff : Differentiable ℂ U := by
    refine Differentiable.sub ?_ hf
    exact hf.comp (differentiable_id.add_const σ)
  have hUω₁ : Function.Periodic U ω₁ := by
    intro z
    simp only [hU]
    rw [show z + ω₁ + σ = z + σ + ω₁ by ring, h₁ (z + σ), h₁ z]
  have hUτ : Function.Periodic U τ := by
    intro z
    simp only [hU]
    have := hmix z
    rw [show z + τ + σ = z + τ + σ from rfl]
    linear_combination this
  have hlat : ∀ p ∈ (⟨ω₁, τ, hindepτ⟩ : PeriodPair).lattice, Function.Periodic U p := by
    intro p hp
    refine periodic_of_mem_span_range ![ω₁, τ] (fun i => ?_) p ?_
    · fin_cases i
      · exact hUω₁
      · exact hUτ
    · rw [range_cons_two]
      exact hp
  have hUconst := const_of_lattice_periodic_differentiable ⟨ω₁, τ, hindepτ⟩ hUdiff hlat
  have hshift : ∀ z, f (z + σ) = f z + U 0 := by
    intro z
    have := hUconst z 0
    simp only [hU] at this
    linear_combination this
  exact (const_of_entire_periodic_of_shift_const hindepσ hf h₁ hshift).1

/-- **The mixed constant is forced to vanish.**  An entire function with a genuine period `ω₁` whose
mixed second difference along `τ` and `σ` is the constant `C` is itself constant, and `C = 0`.  The
single difference `Δ_σ f` is entire, `ω₁`-periodic and changes by `C` under `τ`, so the rigidity
theorem applies to it first and returns `C = 0`, and then to `f`. -/
theorem const_of_entire_of_periodic_of_mixed_const {ω₁ τ σ : ℂ}
    (hindepτ : LinearIndependent ℝ ![ω₁, τ]) (hindepσ : LinearIndependent ℝ ![ω₁, σ])
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) (h₁ : Function.Periodic f ω₁) {C : ℂ}
    (hmix : ∀ z, f (z + τ + σ) - f (z + τ) - (f (z + σ) - f z) = C) :
    (∀ x y, f x = f y) ∧ C = 0 := by
  set U : ℂ → ℂ := fun z => f (z + σ) - f z with hU
  have hUdiff : Differentiable ℂ U := by
    refine Differentiable.sub ?_ hf
    exact hf.comp (differentiable_id.add_const σ)
  have hUω₁ : Function.Periodic U ω₁ := by
    intro z
    simp only [hU]
    rw [show z + ω₁ + σ = z + σ + ω₁ by ring, h₁ (z + σ), h₁ z]
  have hUshift : ∀ z, U (z + τ) = U z + C := by
    intro z
    simp only [hU]
    have := hmix z
    linear_combination this
  obtain ⟨hUconst, hC⟩ := const_of_entire_periodic_of_shift_const hindepτ hUdiff hUω₁ hUshift
  refine ⟨?_, hC⟩
  have hshift : ∀ z, f (z + σ) = f z + U 0 := by
    intro z
    have := hUconst z 0
    simp only [hU] at this
    linear_combination this
  exact (const_of_entire_periodic_of_shift_const hindepσ hf h₁ hshift).1

/-- The entire members of the mixed-constraint class are differentially algebraic, being constant. -/
theorem differentiallyAlgebraic_of_entire_of_periodic_of_mixed_const_zero {ω₁ τ σ : ℂ}
    (hindepτ : LinearIndependent ℝ ![ω₁, τ]) (hindepσ : LinearIndependent ℝ ![ω₁, σ])
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) (h₁ : Function.Periodic f ω₁)
    (hmix : ∀ z, f (z + τ + σ) - f (z + τ) - (f (z + σ) - f z) = 0) :
    DifferentiallyAlgebraic f :=
  differentiallyAlgebraic_of_const
    (const_of_entire_of_periodic_of_mixed_const_zero hindepτ hindepσ hf h₁ hmix)

end GaloisForLFunctions.HTGeometry
