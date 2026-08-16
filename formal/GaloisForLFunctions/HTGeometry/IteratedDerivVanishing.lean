import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Vanishing jets of a product

If the first `m` derivatives of `f` vanish at a point, so does the `m`-th derivative of `f · g`:
the Leibniz expansion has `f`-derivatives of order at most `m` in every term.  The proof is the
induction that differentiates the product once and reuses the statement for `f'` and for `f`.

This is the step that converts a contact order into the vanishing of a jet of any quantity
proportional to the contacting function.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

/-- **A product with a flat factor is flat.** -/
theorem iteratedDeriv_mul_eq_zero_of_vanishing :
    ∀ (m : ℕ) {f g : ℝ → ℝ} {y : ℝ},
      (∀ k : ℕ, ContDiffAt ℝ k f y) → (∀ k : ℕ, ContDiffAt ℝ k g y) →
      (∀ j ≤ m, iteratedDeriv j f y = 0) →
      iteratedDeriv m (fun t => f t * g t) y = 0 := by
  intro m
  induction m with
  | zero =>
      intro f g y _ _ hvan
      have h0 : f y = 0 := by simpa [iteratedDeriv_zero] using hvan 0 (le_refl 0)
      simp [iteratedDeriv_zero, h0]
  | succ m ih =>
      intro f g y hf hg hvan
      have hfd : ∀ᶠ z in 𝓝 y, DifferentiableAt ℝ f z := by
        have h := (hf 1).eventually (by simp)
        filter_upwards [h] with z hz
        exact hz.differentiableAt (by simp)
      have hgd : ∀ᶠ z in 𝓝 y, DifferentiableAt ℝ g z := by
        have h := (hg 1).eventually (by simp)
        filter_upwards [h] with z hz
        exact hz.differentiableAt (by simp)
      have hderivEq : deriv (fun t => f t * g t)
          =ᶠ[𝓝 y] fun t => deriv f t * g t + f t * deriv g t := by
        filter_upwards [hfd, hgd] with z hz hz'
        exact deriv_mul hz hz'
      have hfderiv : ∀ k : ℕ, ContDiffAt ℝ k (deriv f) y := by
        intro k
        exact (hf (k + 1)).derivWithin (by norm_cast)
      have hgderiv : ∀ k : ℕ, ContDiffAt ℝ k (deriv g) y := by
        intro k
        exact (hg (k + 1)).derivWithin (by norm_cast)
      have hvanDeriv : ∀ j ≤ m, iteratedDeriv j (deriv f) y = 0 := by
        intro j hj
        rw [← iteratedDeriv_succ']
        exact hvan (j + 1) (by omega)
      have hvanF : ∀ j ≤ m, iteratedDeriv j f y = 0 := fun j hj => hvan j (by omega)
      have h1 : iteratedDeriv m (fun t => deriv f t * g t) y = 0 :=
        ih hfderiv hg hvanDeriv
      have h2 : iteratedDeriv m (fun t => f t * deriv g t) y = 0 :=
        ih hf hgderiv hvanF
      have hsumCD1 : ∀ k : ℕ, ContDiffAt ℝ k (fun t => deriv f t * g t) y :=
        fun k => (hfderiv k).mul (hg k)
      have hsumCD2 : ∀ k : ℕ, ContDiffAt ℝ k (fun t => f t * deriv g t) y :=
        fun k => (hf k).mul (hgderiv k)
      have hpi : (fun t => deriv f t * g t + f t * deriv g t)
          = (fun t => deriv f t * g t) + fun t => f t * deriv g t := rfl
      rw [iteratedDeriv_succ', Filter.EventuallyEq.iteratedDeriv_eq m hderivEq, hpi,
        iteratedDeriv_add (hsumCD1 m) (hsumCD2 m), h1, h2, add_zero]

/-- **The surviving Leibniz term.**  If the derivatives of `f` below order `m` vanish, the `m`-th
derivative of `f · g` is `f^{(m)} · g`. -/
theorem iteratedDeriv_mul_of_vanishing_below :
    ∀ (m : ℕ) {f g : ℝ → ℝ} {y : ℝ},
      (∀ k : ℕ, ContDiffAt ℝ k f y) → (∀ k : ℕ, ContDiffAt ℝ k g y) →
      (∀ j < m, iteratedDeriv j f y = 0) →
      iteratedDeriv m (fun t => f t * g t) y = iteratedDeriv m f y * g y := by
  intro m
  induction m with
  | zero =>
      intro f g y _ _ _
      simp [iteratedDeriv_zero]
  | succ m ih =>
      intro f g y hf hg hvan
      have hfd : ∀ᶠ z in 𝓝 y, DifferentiableAt ℝ f z := by
        have h := (hf 1).eventually (by simp)
        filter_upwards [h] with z hz
        exact hz.differentiableAt (by simp)
      have hgd : ∀ᶠ z in 𝓝 y, DifferentiableAt ℝ g z := by
        have h := (hg 1).eventually (by simp)
        filter_upwards [h] with z hz
        exact hz.differentiableAt (by simp)
      have hderivEq : deriv (fun t => f t * g t)
          =ᶠ[𝓝 y] fun t => deriv f t * g t + f t * deriv g t := by
        filter_upwards [hfd, hgd] with z hz hz'
        exact deriv_mul hz hz'
      have hfderiv : ∀ k : ℕ, ContDiffAt ℝ k (deriv f) y := fun k =>
        (hf (k + 1)).derivWithin (by norm_cast)
      have hgderiv : ∀ k : ℕ, ContDiffAt ℝ k (deriv g) y := fun k =>
        (hg (k + 1)).derivWithin (by norm_cast)
      have hvanDeriv : ∀ j < m, iteratedDeriv j (deriv f) y = 0 := by
        intro j hj
        rw [← iteratedDeriv_succ']
        exact hvan (j + 1) (by omega)
      have hvanAll : ∀ j ≤ m, iteratedDeriv j f y = 0 := fun j hj => hvan j (by omega)
      have h1 : iteratedDeriv m (fun t => deriv f t * g t) y
          = iteratedDeriv m (deriv f) y * g y := ih hfderiv hg hvanDeriv
      have h2 : iteratedDeriv m (fun t => f t * deriv g t) y = 0 :=
        iteratedDeriv_mul_eq_zero_of_vanishing m hf hgderiv hvanAll
      have hsumCD1 : ∀ k : ℕ, ContDiffAt ℝ k (fun t => deriv f t * g t) y :=
        fun k => (hfderiv k).mul (hg k)
      have hsumCD2 : ∀ k : ℕ, ContDiffAt ℝ k (fun t => f t * deriv g t) y :=
        fun k => (hf k).mul (hgderiv k)
      have hpi : (fun t => deriv f t * g t + f t * deriv g t)
          = (fun t => deriv f t * g t) + fun t => f t * deriv g t := rfl
      rw [iteratedDeriv_succ', Filter.EventuallyEq.iteratedDeriv_eq m hderivEq, hpi,
        iteratedDeriv_add (hsumCD1 m) (hsumCD2 m), h1, h2, add_zero, iteratedDeriv_succ']

/-- **(GJRS.19) The flat-contact jet.**  If the velocity of `u` is a multiple of a function whose
first `d-1` derivatives vanish, then the first `d` derivatives of `u` vanish. -/
theorem iteratedDeriv_eq_zero_of_velocity_flat {D G u : ℝ → ℝ} {y₀ : ℝ} {d : ℕ}
    (hD : ∀ k : ℕ, ContDiffAt ℝ k D y₀) (hG : ∀ k : ℕ, ContDiffAt ℝ k G y₀)
    (hderiv : deriv u =ᶠ[𝓝 y₀] fun t => D t * G t)
    (hvan : ∀ j ≤ d - 1, iteratedDeriv j D y₀ = 0)
    {r : ℕ} (hr1 : 1 ≤ r) (hrd : r ≤ d) :
    iteratedDeriv r u y₀ = 0 := by
  obtain ⟨q, hq⟩ : ∃ q : ℕ, r = q + 1 := ⟨r - 1, by omega⟩
  rw [hq, iteratedDeriv_succ', Filter.EventuallyEq.iteratedDeriv_eq q hderiv]
  refine iteratedDeriv_mul_eq_zero_of_vanishing q hD hG fun j hj => ?_
  exact hvan j (by omega)

/-- **(GJRS.20) The first surviving jet.**  At contact order `d` the `(d+1)`-st derivative of `u`
is `D^{(d)}(y₀)·G(y₀)`. -/
theorem iteratedDeriv_velocity_flat_top {D G u : ℝ → ℝ} {y₀ : ℝ} {d : ℕ}
    (hD : ∀ k : ℕ, ContDiffAt ℝ k D y₀) (hG : ∀ k : ℕ, ContDiffAt ℝ k G y₀)
    (hderiv : deriv u =ᶠ[𝓝 y₀] fun t => D t * G t)
    (hvan : ∀ j < d, iteratedDeriv j D y₀ = 0) :
    iteratedDeriv (d + 1) u y₀ = iteratedDeriv d D y₀ * G y₀ := by
  rw [iteratedDeriv_succ', Filter.EventuallyEq.iteratedDeriv_eq d hderiv]
  exact iteratedDeriv_mul_of_vanishing_below d hD hG hvan

end GaloisForLFunctions.HTGeometry
