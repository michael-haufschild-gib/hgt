import GaloisForLFunctions.HTGeometry.LiouvilleGreenErrorBound
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# A perturbed oscillator satisfies its variation-of-constants equation

The error bound of the previous file is stated for a function obeying the Volterra equation.  This
file shows that a genuine solution of

```text
W'' + (u² + ψ) W = 0 ,   W(a) = 1 ,  W'(a) = 0
```

obeys it.  The only device needed is the addition formula: writing
`sin(u(ξ − t)) = sin(uξ) cos(ut) − cos(uξ) sin(ut)` separates the two variables, so the kernel
integral becomes a combination of *ordinary* primitives and elementary functions, and the two
differentiations are the product rule and the fundamental theorem — the terms produced by
differentiating the upper limit cancel at the first step.

Uniqueness comes from the energy `y'² + u² y²`, which is constant along the unperturbed equation.
-/

open Set MeasureTheory intervalIntegral

namespace GaloisForLFunctions.HTGeometry

/-! ### Uniqueness for the unperturbed oscillator -/

theorem eq_zero_of_harmonic {u a : ℝ} (hu : u ≠ 0) {y y' : ℝ → ℝ}
    (hy : ∀ x, HasDerivAt y (y' x) x)
    (hy' : ∀ x, HasDerivAt y' (-(u ^ (2 : ℕ)) * y x) x)
    (ha : y a = 0) (ha' : y' a = 0) : ∀ x, y x = 0 := by
  set E : ℝ → ℝ := fun x => (y' x) ^ (2 : ℕ) + u ^ (2 : ℕ) * (y x) ^ (2 : ℕ) with hE
  have hEd : ∀ x, HasDerivAt E 0 x := by
    intro x
    have hA : HasDerivAt y' (-(u ^ (2 : ℕ)) * y x) x := hy' x
    have hB : HasDerivAt y (y' x) x := hy x
    have h1 : HasDerivAt (fun t => (y' t) ^ (2 : ℕ)) (2 * y' x * (-(u ^ (2 : ℕ)) * y x)) x := by
      have hp := HasDerivAt.pow hA 2
      have hval : ((2 : ℕ) : ℝ) * y' x ^ (2 - 1) * (-(u ^ (2 : ℕ)) * y x)
          = 2 * y' x * (-(u ^ (2 : ℕ)) * y x) := by norm_num
      rwa [hval] at hp
    have h2 : HasDerivAt (fun t => u ^ (2 : ℕ) * (y t) ^ (2 : ℕ)) (u ^ (2 : ℕ) * (2 * y x * y' x)) x := by
      have hp := HasDerivAt.pow hB 2
      have hval : ((2 : ℕ) : ℝ) * y x ^ (2 - 1) * y' x = 2 * y x * y' x := by norm_num
      rw [hval] at hp
      exact HasDerivAt.const_mul (u ^ (2 : ℕ)) hp
    have h3 := h1.add h2
    have hzero : 2 * y' x * (-(u ^ (2 : ℕ)) * y x) + u ^ (2 : ℕ) * (2 * y x * y' x) = 0 := by ring
    rwa [hzero] at h3
  have hdiff : Differentiable ℝ E := fun x => (hEd x).differentiableAt
  have hderiv : ∀ x, deriv E x = 0 := fun x => (hEd x).deriv
  have hconst : ∀ x, E x = E a := fun x => is_const_of_deriv_eq_zero hdiff hderiv x a
  have hEa : E a = 0 := by
    rw [hE]
    simp [ha, ha']
  intro x
  have hx : (y' x) ^ (2 : ℕ) + u ^ (2 : ℕ) * (y x) ^ (2 : ℕ) = 0 := by
    have h := hconst x
    rw [hEa] at h
    exact h
  have h1 : (0 : ℝ) ≤ (y' x) ^ (2 : ℕ) := sq_nonneg _
  have h2 : (0 : ℝ) ≤ u ^ (2 : ℕ) * (y x) ^ (2 : ℕ) := mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have h3 : u ^ (2 : ℕ) * (y x) ^ (2 : ℕ) = 0 := by linarith
  have h4 : (y x) ^ (2 : ℕ) = 0 := by
    rcases mul_eq_zero.mp h3 with h | h
    · exact absurd (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h) hu
    · exact h
  exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h4

/-! ### The kernel integral -/

variable {a u : ℝ} {ψ W W' : ℝ → ℝ}

/-- The kernel integral, with the two variables separated by the addition formula. -/
noncomputable def sinKernelIntegral (a u : ℝ) (F : ℝ → ℝ) (ξ : ℝ) : ℝ :=
  Real.sin (u * ξ) * (∫ t in a..ξ, Real.cos (u * t) * F t)
    - Real.cos (u * ξ) * (∫ t in a..ξ, Real.sin (u * t) * F t)

theorem hasDerivAt_linear (u x : ℝ) : HasDerivAt (fun y : ℝ => u * y) u x := by
  simpa using (hasDerivAt_id x).const_mul u

theorem sinKernelIntegral_eq (a u : ℝ) {F : ℝ → ℝ} (hF : Continuous F) (ξ : ℝ) :
    sinKernelIntegral a u F ξ = ∫ t in a..ξ, Real.sin (u * (ξ - t)) * F t := by
  have hint1 : IntervalIntegrable
      (fun t : ℝ => Real.sin (u * ξ) * (Real.cos (u * t) * F t)) volume a ξ := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hint2 : IntervalIntegrable
      (fun t : ℝ => Real.cos (u * ξ) * (Real.sin (u * t) * F t)) volume a ξ := by
    apply Continuous.intervalIntegrable
    fun_prop
  rw [sinKernelIntegral, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub hint1 hint2]
  refine intervalIntegral.integral_congr fun t _ => ?_
  show Real.sin (u * ξ) * (Real.cos (u * t) * F t) - Real.cos (u * ξ) * (Real.sin (u * t) * F t)
    = Real.sin (u * (ξ - t)) * F t
  rw [show u * (ξ - t) = u * ξ - u * t from by ring, Real.sin_sub]
  ring

/-- The first derivative: the boundary terms cancel. -/
theorem hasDerivAt_sinKernelIntegral (a u : ℝ) {F : ℝ → ℝ} (hF : Continuous F) (ξ : ℝ) :
    HasDerivAt (sinKernelIntegral a u F)
      (u * (Real.cos (u * ξ) * (∫ t in a..ξ, Real.cos (u * t) * F t)
        + Real.sin (u * ξ) * (∫ t in a..ξ, Real.sin (u * t) * F t))) ξ := by
  have hc : Continuous fun t : ℝ => Real.cos (u * t) * F t := by fun_prop
  have hs : Continuous fun t : ℝ => Real.sin (u * t) * F t := by fun_prop
  have hP : HasDerivAt (fun y => ∫ t in a..y, Real.cos (u * t) * F t)
      (Real.cos (u * ξ) * F ξ) ξ :=
    intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable a ξ)
      (hc.stronglyMeasurableAtFilter _ _) hc.continuousAt
  have hQ : HasDerivAt (fun y => ∫ t in a..y, Real.sin (u * t) * F t)
      (Real.sin (u * ξ) * F ξ) ξ :=
    intervalIntegral.integral_hasDerivAt_right (hs.intervalIntegrable a ξ)
      (hs.stronglyMeasurableAtFilter _ _) hs.continuousAt
  have hlin : HasDerivAt (fun y : ℝ => u * y) u ξ := hasDerivAt_linear u ξ
  have hsin : HasDerivAt (fun y : ℝ => Real.sin (u * y)) (Real.cos (u * ξ) * u) ξ := HasDerivAt.sin hlin
  have hcos : HasDerivAt (fun y : ℝ => Real.cos (u * y)) (-Real.sin (u * ξ) * u) ξ := HasDerivAt.cos hlin
  have h := (hsin.mul hP).sub (hcos.mul hQ)
  have hval : Real.cos (u * ξ) * u * (∫ t in a..ξ, Real.cos (u * t) * F t)
      + Real.sin (u * ξ) * (Real.cos (u * ξ) * F ξ)
      - (-Real.sin (u * ξ) * u * (∫ t in a..ξ, Real.sin (u * t) * F t)
        + Real.cos (u * ξ) * (Real.sin (u * ξ) * F ξ))
      = u * (Real.cos (u * ξ) * (∫ t in a..ξ, Real.cos (u * t) * F t)
        + Real.sin (u * ξ) * (∫ t in a..ξ, Real.sin (u * t) * F t)) := by ring
  rwa [hval] at h

/-- The second derivative reproduces the oscillator with a source. -/
theorem hasDerivAt_sinKernelIntegral_deriv (a u : ℝ) {F : ℝ → ℝ} (hF : Continuous F) (ξ : ℝ) :
    HasDerivAt (fun y => u * (Real.cos (u * y) * (∫ t in a..y, Real.cos (u * t) * F t)
        + Real.sin (u * y) * (∫ t in a..y, Real.sin (u * t) * F t)))
      (u * F ξ - u ^ (2 : ℕ) * sinKernelIntegral a u F ξ) ξ := by
  have hc : Continuous fun t : ℝ => Real.cos (u * t) * F t := by fun_prop
  have hs : Continuous fun t : ℝ => Real.sin (u * t) * F t := by fun_prop
  have hP : HasDerivAt (fun y => ∫ t in a..y, Real.cos (u * t) * F t)
      (Real.cos (u * ξ) * F ξ) ξ :=
    intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable a ξ)
      (hc.stronglyMeasurableAtFilter _ _) hc.continuousAt
  have hQ : HasDerivAt (fun y => ∫ t in a..y, Real.sin (u * t) * F t)
      (Real.sin (u * ξ) * F ξ) ξ :=
    intervalIntegral.integral_hasDerivAt_right (hs.intervalIntegrable a ξ)
      (hs.stronglyMeasurableAtFilter _ _) hs.continuousAt
  have hlin : HasDerivAt (fun y : ℝ => u * y) u ξ := hasDerivAt_linear u ξ
  have hsin : HasDerivAt (fun y : ℝ => Real.sin (u * y)) (Real.cos (u * ξ) * u) ξ := HasDerivAt.sin hlin
  have hcos : HasDerivAt (fun y : ℝ => Real.cos (u * y)) (-Real.sin (u * ξ) * u) ξ := HasDerivAt.cos hlin
  have h := ((hcos.mul hP).add (hsin.mul hQ)).const_mul u
  have hpy : Real.sin (u * ξ) ^ (2 : ℕ) + Real.cos (u * ξ) ^ (2 : ℕ) = 1 := Real.sin_sq_add_cos_sq _
  have hval : u * (-Real.sin (u * ξ) * u * (∫ t in a..ξ, Real.cos (u * t) * F t)
        + Real.cos (u * ξ) * (Real.cos (u * ξ) * F ξ)
      + (Real.cos (u * ξ) * u * (∫ t in a..ξ, Real.sin (u * t) * F t)
        + Real.sin (u * ξ) * (Real.sin (u * ξ) * F ξ)))
      = u * F ξ - u ^ (2 : ℕ) * sinKernelIntegral a u F ξ := by
    rw [sinKernelIntegral]
    linear_combination (u * F ξ) * hpy
  rwa [hval] at h

/-! ### The transfer -/

/-- **A solution of the perturbed oscillator obeys the Volterra equation.** -/
theorem isOscillatoryLGSolution_of_ode {b : ℝ} (hu : u ≠ 0)
    (hψ : Continuous ψ) (hWc : Continuous W)
    (hW : ∀ x, HasDerivAt W (W' x) x)
    (hW' : ∀ x, HasDerivAt W' (-(u ^ (2 : ℕ) + ψ x) * W x) x)
    (hWa : W a = 1) (hW'a : W' a = 0) :
    IsOscillatoryLGSolution a u ψ W b := by
  set F : ℝ → ℝ := fun t => ψ t * W t with hFdef
  have hF : Continuous F := hψ.mul hWc
  set R : ℝ → ℝ := fun ξ => Real.cos (u * (ξ - a)) - (1 / u) * sinKernelIntegral a u F ξ with hRdef
  set R' : ℝ → ℝ := fun ξ => -Real.sin (u * (ξ - a)) * u
      - (1 / u) * (u * (Real.cos (u * ξ) * (∫ t in a..ξ, Real.cos (u * t) * F t)
        + Real.sin (u * ξ) * (∫ t in a..ξ, Real.sin (u * t) * F t))) with hR'def
  have hshift : ∀ x : ℝ, HasDerivAt (fun y : ℝ => u * (y - a)) u x := by
    intro x
    simpa using ((hasDerivAt_id x).sub_const a).const_mul u
  have hRd : ∀ x, HasDerivAt R (R' x) x := by
    intro x
    have hc : HasDerivAt (fun y : ℝ => Real.cos (u * (y - a))) (-Real.sin (u * (x - a)) * u) x :=
      HasDerivAt.cos (hshift x)
    exact hc.sub ((hasDerivAt_sinKernelIntegral a u hF x).const_mul (1 / u))
  have hR'd : ∀ x, HasDerivAt R' (-(u ^ (2 : ℕ)) * R x - F x) x := by
    intro x
    have h2 : HasDerivAt (fun y : ℝ => Real.sin (u * (y - a))) (Real.cos (u * (x - a)) * u) x :=
      HasDerivAt.sin (hshift x)
    have h3 := (h2.neg).mul_const u
    have hcval : -(Real.cos (u * (x - a)) * u) * u = -(u ^ (2 : ℕ)) * Real.cos (u * (x - a)) := by ring
    rw [hcval] at h3
    have hd := (hasDerivAt_sinKernelIntegral_deriv a u hF x).const_mul (1 / u)
    have h := h3.sub hd
    have hval : -(u ^ (2 : ℕ)) * Real.cos (u * (x - a))
        - 1 / u * (u * F x - u ^ (2 : ℕ) * sinKernelIntegral a u F x)
        = -(u ^ (2 : ℕ)) * R x - F x := by
      rw [hRdef]
      field_simp
      ring
    rwa [hval] at h
  have hRa : R a = 1 := by
    show Real.cos (u * (a - a)) - 1 / u * sinKernelIntegral a u F a = 1
    simp [sinKernelIntegral, intervalIntegral.integral_same]
  have hR'a : R' a = 0 := by
    show -Real.sin (u * (a - a)) * u
      - 1 / u * (u * (Real.cos (u * a) * (∫ t in a..a, Real.cos (u * t) * F t)
        + Real.sin (u * a) * (∫ t in a..a, Real.sin (u * t) * F t))) = 0
    simp [intervalIntegral.integral_same]
  have hdiff : ∀ x, HasDerivAt (fun y => W y - R y) (W' x - R' x) x := fun x => (hW x).sub (hRd x)
  have hdiff2 : ∀ x, HasDerivAt (fun y => W' y - R' y) (-(u ^ (2 : ℕ)) * (W x - R x)) x := by
    intro x
    have h := (hW' x).sub (hR'd x)
    have hval : -(u ^ (2 : ℕ) + ψ x) * W x - (-(u ^ (2 : ℕ)) * R x - F x) = -(u ^ (2 : ℕ)) * (W x - R x) := by
      rw [hFdef]
      ring
    rwa [hval] at h
  have hzero := eq_zero_of_harmonic hu hdiff hdiff2 (by rw [hWa, hRa]; ring)
    (by rw [hW'a, hR'a]; ring)
  intro ξ _
  have h := hzero ξ
  have hWR : W ξ = R ξ := by
    have : W ξ - R ξ = 0 := h
    linarith
  rw [hWR]
  show Real.cos (u * (ξ - a)) - 1 / u * sinKernelIntegral a u F ξ
    = Real.cos (u * (ξ - a)) - 1 / u * ∫ t in a..ξ, Real.sin (u * (ξ - t)) * ψ t * W t
  rw [sinKernelIntegral_eq a u hF ξ]
  have hFI : (∫ t in a..ξ, Real.sin (u * (ξ - t)) * F t)
      = ∫ t in a..ξ, Real.sin (u * (ξ - t)) * ψ t * W t := by
    refine intervalIntegral.integral_congr fun t _ => ?_
    show Real.sin (u * (ξ - t)) * F t = Real.sin (u * (ξ - t)) * ψ t * W t
    rw [hFdef]
    ring
  rw [hFI]

end GaloisForLFunctions.HTGeometry
