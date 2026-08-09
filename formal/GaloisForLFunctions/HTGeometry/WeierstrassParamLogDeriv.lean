import GaloisForLFunctions.HTGeometry.CircleIntegralParamOpen

/-!
# Moments of a logarithmic derivative, holomorphic in the parameters

The distinguished-variable moments

`y ↦ ∮_{|ζ|=t} ζ^p (∂₀f/f)(ζ, y) dζ`

of a function of several complex variables are holomorphic wherever the circle avoids the zero set
of `f`.  These are the power sums of the roots of the slice `f(·, y)` inside the circle, so their
holomorphy is what makes the elementary symmetric functions of those roots holomorphic — the
analytic content of Weierstrass' preparation theorem.

The integrand is holomorphic on the open set `U ∩ {f ≠ 0}`, which is not a product, so the
parameter holomorphy is taken in the form valid over an arbitrary open set.

* `HTGeometry.partialFirst` — the derivative in the distinguished variable;
* `HTGeometry.deriv_cons_slice` — it computes the derivative of a slice;
* `HTGeometry.analyticOnNhd_partialFirst` — it is again holomorphic;
* `HTGeometry.differentiableAt_logDerivMoment` — the moments are holomorphic in the parameters.
-/

namespace HTGeometry

open Complex MeasureTheory GaloisForLFunctions.HTGeometry
open scoped Real

variable {n : ℕ}

/-- The derivative in the distinguished (first) variable. -/
noncomputable def partialFirst (f : (Fin (n + 1) → ℂ) → ℂ) (z : Fin (n + 1) → ℂ) : ℂ :=
  fderiv ℂ f z (Pi.single 0 1)

/-- Consing a first coordinate is an affine map of that coordinate. -/
theorem cons_eq_single_add (s : ℂ) (y : Fin n → ℂ) :
    (Fin.cons s y : Fin (n + 1) → ℂ) = Pi.single 0 s + Fin.cons 0 y := by
  funext i
  induction i using Fin.cases <;> simp

/-- The derivative of consing a first coordinate. -/
theorem hasFDerivAt_consFirst (y : Fin n → ℂ) (s : ℂ) :
    HasFDerivAt (fun u : ℂ => (Fin.cons u y : Fin (n + 1) → ℂ))
      (ContinuousLinearMap.single ℂ (fun _ : Fin (n + 1) => ℂ) 0) s := by
  have h : (fun u : ℂ => (Fin.cons u y : Fin (n + 1) → ℂ))
      = fun u : ℂ => (ContinuousLinearMap.single ℂ (fun _ : Fin (n + 1) => ℂ) 0) u
          + Fin.cons 0 y := by
    funext u
    rw [cons_eq_single_add]
    rfl
  rw [h]
  exact (ContinuousLinearMap.single ℂ (fun _ : Fin (n + 1) => ℂ) 0).hasFDerivAt.add_const _

/-- **The first partial derivative computes the derivative of a slice.** -/
theorem deriv_cons_slice {f : (Fin (n + 1) → ℂ) → ℂ} {U : Set (Fin (n + 1) → ℂ)} (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f U) {y : Fin n → ℂ} {s : ℂ}
    (hmem : (Fin.cons s y : Fin (n + 1) → ℂ) ∈ U) :
    deriv (fun u : ℂ => f (Fin.cons u y)) s = partialFirst f (Fin.cons s y) := by
  have hd : DifferentiableAt ℂ f (Fin.cons s y) := hf.differentiableAt (hU.mem_nhds hmem)
  have hfd : HasFDerivAt (fun u : ℂ => f (Fin.cons u y))
      ((fderiv ℂ f (Fin.cons s y)).comp
        (ContinuousLinearMap.single ℂ (fun _ : Fin (n + 1) => ℂ) 0)) s :=
    hd.hasFDerivAt.comp s (hasFDerivAt_consFirst y s)
  rw [← fderiv_apply_one_eq_deriv, hfd.fderiv]
  simp [partialFirst]

/-- **The first partial derivative of a holomorphic function is holomorphic.** -/
theorem analyticOnNhd_partialFirst {f : (Fin (n + 1) → ℂ) → ℂ} {U : Set (Fin (n + 1) → ℂ)}
    (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) : AnalyticOnNhd ℂ (partialFirst f) U := by
  have hA : AnalyticOnNhd ℂ f U := fun z hz => analyticAt_of_differentiableOn hU hf hz
  have hfd : AnalyticOnNhd ℂ (fderiv ℂ f) U := hA.fderiv
  have hcomp := (ContinuousLinearMap.apply ℂ ℂ
    (Pi.single (0 : Fin (n + 1)) (1 : ℂ) : Fin (n + 1) → ℂ)).comp_analyticOnNhd hfd
  exact hcomp

/-- **The moments of the logarithmic derivative along a circle are holomorphic in the remaining
variables.**  The integrand is holomorphic on the open set where `f` does not vanish, and the
circle stays inside it for every nearby parameter. -/
theorem differentiableAt_logDerivMoment
    {f : (Fin (n + 1) → ℂ) → ℂ} {U : Set (Fin (n + 1) → ℂ)} {V : Set (Fin n → ℂ)}
    (hU : IsOpen U) (hV : IsOpen V) (hf : DifferentiableOn ℂ f U) {t : ℝ} (ht : 0 < t)
    (hmemU : ∀ (θ : ℝ) (y : Fin n → ℂ), y ∈ V →
      (Fin.cons (circleMap 0 t θ) y : Fin (n + 1) → ℂ) ∈ U)
    (hne : ∀ (θ : ℝ) (y : Fin n → ℂ), y ∈ V → f (Fin.cons (circleMap 0 t θ) y) ≠ 0)
    (p : ℕ) {y₀ : Fin n → ℂ} (hy₀ : y₀ ∈ V) :
    DifferentiableAt ℂ (fun y : Fin n → ℂ =>
      ∮ ζ in C(0, t), ζ ^ p • (partialFirst f (Fin.cons ζ y) / f (Fin.cons ζ y))) y₀ := by
  classical
  set U' : Set (Fin (n + 1) → ℂ) := U ∩ f ⁻¹' {(0 : ℂ)}ᶜ with hU'
  have hU'open : IsOpen U' :=
    hf.continuousOn.isOpen_inter_preimage hU isOpen_compl_singleton
  have hquot : DifferentiableOn ℂ (fun z => partialFirst f z / f z) U' := by
    intro z hz
    have h1 : DifferentiableAt ℂ (partialFirst f) z :=
      (analyticOnNhd_partialFirst hU hf z hz.1).differentiableAt
    have h2 : DifferentiableAt ℂ f z := hf.differentiableAt (hU.mem_nhds hz.1)
    have h3 : f z ≠ 0 := hz.2
    have hmul : DifferentiableAt ℂ (fun z => partialFirst f z * (f z)⁻¹) z :=
      h1.mul (h2.inv h3)
    exact (hmul.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun w => (div_eq_mul_inv _ _).symm)).differentiableWithinAt
  refine differentiableAt_circleIntegral_slice_open hU'open hV hquot ht (fun ζ => ζ ^ p)
    ((continuous_circleMap 0 t).pow p) ?_ hy₀
  intro θ y hy
  exact ⟨hmemU θ y hy, hne θ y hy⟩

end HTGeometry
