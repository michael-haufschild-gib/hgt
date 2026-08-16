import Mathlib

/-!
# The virial identity and the Sturm energy of a self-adjoint equation

For a solution of the self-adjoint equation

```text
(p R')' + Q R = 0
```

two exact identities hold, both by one product rule and no estimate:

```text
(p R R')' = p R'² − Q R² ,                      the virial identity
((p R')² + p Q R²)' = (p Q)' R² ,               the Sturm energy
```

The first turns the total kinetic integral into the potential integral plus boundary terms; the
second says the Sturm energy is monotone whenever `p Q` is.  Together they convert an energy bound
into an `L²` mass bound without any information about the oscillation — no phase, no speed floor, no
stationary-phase estimate.  That matters because the oscillating factor vanishes at its zeros, so no
pointwise envelope can do it.

Nothing here assumes `p` or `Q` positive; positivity enters only when the identities are used.
-/

noncomputable section

open Set

namespace GaloisForLFunctions.HTGeometry

variable {p Q R DR DpQ : ℝ → ℝ} {α β : ℝ}

/-- The Sturm energy of a solution of `(p R')' + Q R = 0`. -/
def slEnergy (p Q R DR : ℝ → ℝ) (x : ℝ) : ℝ := (p x * DR x) ^ 2 + p x * Q x * R x ^ 2

theorem slEnergy_nonneg (hp : 0 ≤ p x) (hQ : 0 ≤ Q x) : 0 ≤ slEnergy p Q R DR x := by
  rw [slEnergy]
  have : 0 ≤ p x * Q x := mul_nonneg hp hQ
  positivity

/-- **The virial identity.**  `(p R R')' = p R'² − Q R²`. -/
theorem hasDerivAt_virial {x : ℝ} (hR : HasDerivAt R (DR x) x)
    (hpR : HasDerivAt (fun t => p t * DR t) (-(Q x * R x)) x) :
    HasDerivAt (fun t => R t * (p t * DR t)) (p x * DR x ^ 2 - Q x * R x ^ 2) x := by
  refine (hR.mul hpR).congr_deriv ?_
  ring

/-- **The Sturm energy has derivative `(p Q)' R²`.** -/
theorem hasDerivAt_slEnergy {x : ℝ} (hR : HasDerivAt R (DR x) x)
    (hpR : HasDerivAt (fun t => p t * DR t) (-(Q x * R x)) x)
    (hpQ : HasDerivAt (fun t => p t * Q t) (DpQ x) x) :
    HasDerivAt (slEnergy p Q R DR) (DpQ x * R x ^ 2) x := by
  have h1 : HasDerivAt (fun t => (p t * DR t) ^ 2)
      (2 * (p x * DR x) ^ 1 * -(Q x * R x)) x := hpR.pow 2
  have h2 : HasDerivAt (fun t => p t * Q t * R t ^ 2)
      (DpQ x * R x ^ 2 + p x * Q x * (2 * R x ^ 1 * DR x)) x := hpQ.mul (hR.pow 2)
  have h := h1.add h2
  have hfun : slEnergy p Q R DR
      = fun t => (p t * DR t) ^ 2 + p t * Q t * R t ^ 2 := by
    funext t
    rw [slEnergy]
  rw [hfun]
  refine h.congr_deriv ?_
  ring

/-- **The Sturm energy is nondecreasing** where `p Q` is. -/
theorem slEnergy_le_of_monotone
    (hR : ∀ x ∈ Icc α β, HasDerivAt R (DR x) x)
    (hpR : ∀ x ∈ Icc α β, HasDerivAt (fun t => p t * DR t) (-(Q x * R x)) x)
    (hpQ : ∀ x ∈ Icc α β, HasDerivAt (fun t => p t * Q t) (DpQ x) x)
    (hnn : ∀ x ∈ Icc α β, 0 ≤ DpQ x) {x : ℝ} (hx : x ∈ Icc α β) :
    slEnergy p Q R DR α ≤ slEnergy p Q R DR x := by
  have hd : ∀ y ∈ Icc α β, HasDerivAt (slEnergy p Q R DR) (DpQ y * R y ^ 2) y :=
    fun y hy => hasDerivAt_slEnergy (hR y hy) (hpR y hy) (hpQ y hy)
  have hsub : Icc α x ⊆ Icc α β := Icc_subset_Icc le_rfl hx.2
  have hcont : ContinuousOn (slEnergy p Q R DR) (Icc α x) := fun y hy =>
    ((hd y (hsub hy)).continuousAt).continuousWithinAt
  have hdiff : DifferentiableOn ℝ (slEnergy p Q R DR) (interior (Icc α x)) := by
    rw [interior_Icc]
    exact fun y hy => ((hd y (hsub ⟨hy.1.le, hy.2.le⟩)).differentiableAt).differentiableWithinAt
  have hderiv : ∀ y ∈ interior (Icc α x), 0 ≤ deriv (slEnergy p Q R DR) y := by
    rw [interior_Icc]
    intro y hy
    have hymem : y ∈ Icc α β := hsub ⟨hy.1.le, hy.2.le⟩
    rw [(hd y hymem).deriv]
    exact mul_nonneg (hnn y hymem) (sq_nonneg _)
  exact monotoneOn_of_deriv_nonneg (convex_Icc α x) hcont hdiff hderiv
    (left_mem_Icc.2 hx.1) (right_mem_Icc.2 hx.1) hx.1

/-- **The integrated virial identity.** -/
theorem integral_virial
    (hR : ∀ x ∈ uIcc α β, HasDerivAt R (DR x) x)
    (hpR : ∀ x ∈ uIcc α β, HasDerivAt (fun t => p t * DR t) (-(Q x * R x)) x)
    (hint : IntervalIntegrable (fun x => p x * DR x ^ 2 - Q x * R x ^ 2)
      MeasureTheory.volume α β) :
    (∫ x in α..β, (p x * DR x ^ 2 - Q x * R x ^ 2))
      = R β * (p β * DR β) - R α * (p α * DR α) :=
  intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x hx => hasDerivAt_virial (hR x hx) (hpR x hx)) hint

/-- **Mass from Sturm energy.**  The energy divided by `p` integrates to twice the potential mass
plus boundary terms, so a lower bound on the energy forces `L²` mass.  No property of the
oscillation is used. -/
theorem integral_slEnergy_div_eq
    (hR : ∀ x ∈ uIcc α β, HasDerivAt R (DR x) x)
    (hpR : ∀ x ∈ uIcc α β, HasDerivAt (fun t => p t * DR t) (-(Q x * R x)) x)
    (hp0 : ∀ x ∈ uIcc α β, p x ≠ 0)
    (hint : IntervalIntegrable (fun x => p x * DR x ^ 2 - Q x * R x ^ 2)
      MeasureTheory.volume α β)
    (hQR : IntervalIntegrable (fun x => Q x * R x ^ 2) MeasureTheory.volume α β) :
    (∫ x in α..β, slEnergy p Q R DR x / p x)
      = 2 * (∫ x in α..β, Q x * R x ^ 2) + (R β * (p β * DR β) - R α * (p α * DR α)) := by
  have hvir := integral_virial hR hpR hint
  have hsplit : (∫ x in α..β, (p x * DR x ^ 2 - Q x * R x ^ 2))
      = (∫ x in α..β, p x * DR x ^ 2) - ∫ x in α..β, Q x * R x ^ 2 := by
    have hpd : IntervalIntegrable (fun x => p x * DR x ^ 2) MeasureTheory.volume α β := by
      have := hint.add hQR
      exact this.congr fun x _ => by ring
    rw [intervalIntegral.integral_sub hpd hQR]
  have hEeq : (∫ x in α..β, slEnergy p Q R DR x / p x)
      = (∫ x in α..β, p x * DR x ^ 2) + ∫ x in α..β, Q x * R x ^ 2 := by
    have hpd : IntervalIntegrable (fun x => p x * DR x ^ 2) MeasureTheory.volume α β := by
      have := hint.add hQR
      exact this.congr fun x _ => by ring
    have hcongr : (∫ x in α..β, slEnergy p Q R DR x / p x)
        = ∫ x in α..β, (p x * DR x ^ 2 + Q x * R x ^ 2) := by
      refine intervalIntegral.integral_congr fun x hx => ?_
      have hpx : p x ≠ 0 := hp0 x hx
      rw [slEnergy]
      field_simp
    rw [hcongr, intervalIntegral.integral_add hpd hQR]
  rw [hEeq]
  linarith [hvir, hsplit]

end GaloisForLFunctions.HTGeometry

end
