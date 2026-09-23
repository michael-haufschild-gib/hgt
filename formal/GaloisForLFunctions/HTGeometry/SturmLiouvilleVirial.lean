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
def slEnergy (p Q R DR : ℝ → ℝ) (x : ℝ) : ℝ := (p x * DR x) ^ (2 : ℕ) + p x * Q x * R x ^ (2 : ℕ)

theorem slEnergy_nonneg (hp : 0 ≤ p x) (hQ : 0 ≤ Q x) : 0 ≤ slEnergy p Q R DR x := by
  rw [slEnergy]
  have : 0 ≤ p x * Q x := mul_nonneg hp hQ
  positivity

/-- **The virial identity.**  `(p R R')' = p R'² − Q R²`. -/
theorem hasDerivAt_virial {x : ℝ} (hR : HasDerivAt R (DR x) x)
    (hpR : HasDerivAt (fun t => p t * DR t) (-(Q x * R x)) x) :
    HasDerivAt (fun t => R t * (p t * DR t)) (p x * DR x ^ (2 : ℕ) - Q x * R x ^ (2 : ℕ)) x := by
  refine (hR.mul hpR).congr_deriv ?_
  ring

/-- **The Sturm energy has derivative `(p Q)' R²`.** -/
theorem hasDerivAt_slEnergy {x : ℝ} (hR : HasDerivAt R (DR x) x)
    (hpR : HasDerivAt (fun t => p t * DR t) (-(Q x * R x)) x)
    (hpQ : HasDerivAt (fun t => p t * Q t) (DpQ x) x) :
    HasDerivAt (slEnergy p Q R DR) (DpQ x * R x ^ (2 : ℕ)) x := by
  have h1 : HasDerivAt (fun t => (p t * DR t) ^ (2 : ℕ))
      (2 * (p x * DR x) ^ (1 : ℕ) * -(Q x * R x)) x := hpR.pow 2
  have h2 : HasDerivAt (fun t => p t * Q t * R t ^ (2 : ℕ))
      (DpQ x * R x ^ (2 : ℕ) + p x * Q x * (2 * R x ^ (1 : ℕ) * DR x)) x := hpQ.mul (hR.pow 2)
  have h := h1.add h2
  have hfun : slEnergy p Q R DR
      = fun t => (p t * DR t) ^ (2 : ℕ) + p t * Q t * R t ^ (2 : ℕ) := by
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
  have hd : ∀ y ∈ Icc α β, HasDerivAt (slEnergy p Q R DR) (DpQ y * R y ^ (2 : ℕ)) y :=
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
    (hint : IntervalIntegrable (fun x => p x * DR x ^ (2 : ℕ) - Q x * R x ^ (2 : ℕ))
      MeasureTheory.volume α β) :
    (∫ x in α..β, (p x * DR x ^ (2 : ℕ) - Q x * R x ^ (2 : ℕ)))
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
    (hint : IntervalIntegrable (fun x => p x * DR x ^ (2 : ℕ) - Q x * R x ^ (2 : ℕ))
      MeasureTheory.volume α β)
    (hQR : IntervalIntegrable (fun x => Q x * R x ^ (2 : ℕ)) MeasureTheory.volume α β) :
    (∫ x in α..β, slEnergy p Q R DR x / p x)
      = 2 * (∫ x in α..β, Q x * R x ^ (2 : ℕ)) + (R β * (p β * DR β) - R α * (p α * DR α)) := by
  have hvir := integral_virial hR hpR hint
  have hsplit : (∫ x in α..β, (p x * DR x ^ (2 : ℕ) - Q x * R x ^ (2 : ℕ)))
      = (∫ x in α..β, p x * DR x ^ (2 : ℕ)) - ∫ x in α..β, Q x * R x ^ (2 : ℕ) := by
    have hpd : IntervalIntegrable (fun x => p x * DR x ^ (2 : ℕ)) MeasureTheory.volume α β := by
      have := hint.add hQR
      exact this.congr fun x _ => by ring
    rw [intervalIntegral.integral_sub hpd hQR]
  have hEeq : (∫ x in α..β, slEnergy p Q R DR x / p x)
      = (∫ x in α..β, p x * DR x ^ (2 : ℕ)) + ∫ x in α..β, Q x * R x ^ (2 : ℕ) := by
    have hpd : IntervalIntegrable (fun x => p x * DR x ^ (2 : ℕ)) MeasureTheory.volume α β := by
      have := hint.add hQR
      exact this.congr fun x _ => by ring
    have hcongr : (∫ x in α..β, slEnergy p Q R DR x / p x)
        = ∫ x in α..β, (p x * DR x ^ (2 : ℕ) + Q x * R x ^ (2 : ℕ)) := by
      refine intervalIntegral.integral_congr fun x hx => ?_
      have hpx : p x ≠ 0 := hp0 x hx
      rw [slEnergy]
      field_simp
    rw [hcongr, intervalIntegral.integral_add hpd hQR]
  rw [hEeq]
  linarith [hvir, hsplit]

/-- **`L²` mass from a Sturm energy floor.**  An interval on which `∫ dx/p` exceeds the boundary
budget must carry mass proportional to the energy floor.  Nothing about the oscillation enters. -/
theorem mass_lower_of_slEnergy {F₀ Ip B Qβ : ℝ} (hαβ : α ≤ β)
    (hR : ∀ x ∈ uIcc α β, HasDerivAt R (DR x) x)
    (hpR : ∀ x ∈ uIcc α β, HasDerivAt (fun t => p t * DR t) (-(Q x * R x)) x)
    (hint : IntervalIntegrable (fun x => p x * DR x ^ (2 : ℕ) - Q x * R x ^ (2 : ℕ))
      MeasureTheory.volume α β)
    (hQR : IntervalIntegrable (fun x => Q x * R x ^ (2 : ℕ)) MeasureTheory.volume α β)
    (hEint : IntervalIntegrable (fun x => slEnergy p Q R DR x / p x) MeasureTheory.volume α β)
    (hpinv : IntervalIntegrable (fun x => 1 / p x) MeasureTheory.volume α β)
    (hR2 : IntervalIntegrable (fun x => R x ^ (2 : ℕ)) MeasureTheory.volume α β)
    (hppos : ∀ x ∈ Icc α β, 0 < p x)
    (hF₀ : ∀ x ∈ Icc α β, F₀ ≤ slEnergy p Q R DR x) (hF₀0 : 0 ≤ F₀)
    (hIp : Ip ≤ ∫ x in α..β, 1 / p x)
    (hbd : R β * (p β * DR β) - R α * (p α * DR α) ≤ B)
    (hQ : ∀ x ∈ Icc α β, Q x ≤ Qβ) (hQβ : 0 < Qβ) :
    (F₀ * Ip - B) / (2 * Qβ) ≤ ∫ x in α..β, R x ^ (2 : ℕ) := by
  have huIcc : uIcc α β = Icc α β := uIcc_of_le hαβ
  have hp0 : ∀ x ∈ uIcc α β, p x ≠ 0 := by
    rw [huIcc]
    exact fun x hx => (hppos x hx).ne'
  have hid := integral_slEnergy_div_eq hR hpR hp0 hint hQR
  -- the energy floor
  have hfloor : F₀ * Ip ≤ ∫ x in α..β, slEnergy p Q R DR x / p x := by
    have hmono : (∫ x in α..β, F₀ * (1 / p x)) ≤ ∫ x in α..β, slEnergy p Q R DR x / p x := by
      refine intervalIntegral.integral_mono_on hαβ (hpinv.const_mul F₀) hEint fun x hx => ?_
      have hpx : 0 < p x := hppos x hx
      have hFx : F₀ ≤ slEnergy p Q R DR x := hF₀ x hx
      rw [mul_one_div, div_le_div_iff₀ hpx hpx]
      nlinarith [hFx, hpx]
    have hconst : (∫ x in α..β, F₀ * (1 / p x)) = F₀ * ∫ x in α..β, 1 / p x :=
      intervalIntegral.integral_const_mul _ _
    have hIp' : F₀ * Ip ≤ F₀ * ∫ x in α..β, 1 / p x :=
      mul_le_mul_of_nonneg_left hIp hF₀0
    rw [hconst] at hmono
    linarith [hmono, hIp']
  -- the potential mass from above
  have hpot : (∫ x in α..β, Q x * R x ^ (2 : ℕ)) ≤ Qβ * ∫ x in α..β, R x ^ (2 : ℕ) := by
    have hmono : (∫ x in α..β, Q x * R x ^ (2 : ℕ)) ≤ ∫ x in α..β, Qβ * R x ^ (2 : ℕ) := by
      refine intervalIntegral.integral_mono_on hαβ hQR (hR2.const_mul Qβ) fun x hx => ?_
      nlinarith [hQ x hx, sq_nonneg (R x)]
    rwa [intervalIntegral.integral_const_mul] at hmono
  rw [div_le_iff₀ (by positivity)]
  linarith [hid, hfloor, hpot, hbd]

/-! ## A nonzero Wronskian floors the Sturm energy

For two solutions of `(p R')' + Q R = 0` the combination `R₁·(p R₂') − (p R₁')·R₂` is constant.
Weighted Cauchy–Schwarz against the Sturm energies gives

```text
p Q · W²  ≤  slEnergy₁ · slEnergy₂ ,
```

the weight `p Q` appearing because the energy weights `(p R')²` and `p Q R²` differently.  The
identity behind it is exact:

```text
(A² + μB²)(C² + μD²) − μ(BC − AD)²  =  (AC + μBD)² .
```

This is where a factor of the aperture comes from in the radial application: `p Q = c²(x²−1)(x²−s)`
carries `c²`, so a companion solution with energy `O(c)` forces the solution's own energy to be
`Ω(c)`.  No evaluation of either solution is involved. -/

/-- **The weighted Lagrange identity.** -/
theorem sq_wronskian_mul_le_slEnergy_mul (p Q R₁ DR₁ R₂ DR₂ : ℝ → ℝ) (x : ℝ) :
    p x * Q x * (R₁ x * (p x * DR₂ x) - (p x * DR₁ x) * R₂ x) ^ (2 : ℕ)
      ≤ slEnergy p Q R₁ DR₁ x * slEnergy p Q R₂ DR₂ x := by
  rw [slEnergy, slEnergy]
  nlinarith [sq_nonneg ((p x * DR₁ x) * (p x * DR₂ x) + (p x * Q x) * (R₁ x * R₂ x))]

/-- **A nonzero Wronskian floors the Sturm energy.** -/
theorem slEnergy_lower_of_wronskian {p Q R₁ DR₁ R₂ DR₂ : ℝ → ℝ} {x W C : ℝ}
    (hWval : R₁ x * (p x * DR₂ x) - (p x * DR₁ x) * R₂ x = W)
    (hpQ : 0 ≤ p x * Q x)
    (hE₂ : slEnergy p Q R₂ DR₂ x ≤ C) (hC : 0 < C) :
    p x * Q x * W ^ (2 : ℕ) / C ≤ slEnergy p Q R₁ DR₁ x := by
  have hCS := sq_wronskian_mul_le_slEnergy_mul p Q R₁ DR₁ R₂ DR₂ x
  rw [hWval] at hCS
  have hE1 : 0 ≤ slEnergy p Q R₁ DR₁ x := by
    rw [slEnergy]
    nlinarith [sq_nonneg (p x * DR₁ x), sq_nonneg (R₁ x), hpQ]
  rw [div_le_iff₀ hC]
  nlinarith [hCS, hE1, hE₂, sq_nonneg W, hpQ]

/-! ## The Wronskian is constant -/

/-- The self-adjoint Wronskian of two solutions. -/
def slWronskian (p R₁ DR₁ R₂ DR₂ : ℝ → ℝ) (x : ℝ) : ℝ :=
  R₁ x * (p x * DR₂ x) - (p x * DR₁ x) * R₂ x

/-- **Abel's identity in self-adjoint form.**  The Wronskian of two solutions has zero
derivative. -/
theorem hasDerivAt_slWronskian {R₁ DR₁ R₂ DR₂ : ℝ → ℝ} {x : ℝ}
    (hR₁ : HasDerivAt R₁ (DR₁ x) x)
    (hpR₁ : HasDerivAt (fun t => p t * DR₁ t) (-(Q x * R₁ x)) x)
    (hR₂ : HasDerivAt R₂ (DR₂ x) x)
    (hpR₂ : HasDerivAt (fun t => p t * DR₂ t) (-(Q x * R₂ x)) x) :
    HasDerivAt (slWronskian p R₁ DR₁ R₂ DR₂) 0 x := by
  have h := (hR₁.mul hpR₂).sub (hpR₁.mul hR₂)
  have hfun : slWronskian p R₁ DR₁ R₂ DR₂
      = fun t => R₁ t * (p t * DR₂ t) - (p t * DR₁ t) * R₂ t := by
    funext t
    rw [slWronskian]
  rw [hfun]
  refine h.congr_deriv ?_
  ring

/-- **The Wronskian is constant on an interval of solutions.** -/
theorem slWronskian_eq {R₁ DR₁ R₂ DR₂ : ℝ → ℝ}
    (hR₁ : ∀ x ∈ Icc α β, HasDerivAt R₁ (DR₁ x) x)
    (hpR₁ : ∀ x ∈ Icc α β, HasDerivAt (fun t => p t * DR₁ t) (-(Q x * R₁ x)) x)
    (hR₂ : ∀ x ∈ Icc α β, HasDerivAt R₂ (DR₂ x) x)
    (hpR₂ : ∀ x ∈ Icc α β, HasDerivAt (fun t => p t * DR₂ t) (-(Q x * R₂ x)) x)
    {x : ℝ} (hx : x ∈ Icc α β) :
    slWronskian p R₁ DR₁ R₂ DR₂ x = slWronskian p R₁ DR₁ R₂ DR₂ α := by
  have hd : ∀ y ∈ Icc α β, HasDerivAt (slWronskian p R₁ DR₁ R₂ DR₂) 0 y := fun y hy =>
    hasDerivAt_slWronskian (Q := Q) (hR₁ y hy) (hpR₁ y hy) (hR₂ y hy) (hpR₂ y hy)
  have hsub : Icc α x ⊆ Icc α β := Icc_subset_Icc le_rfl hx.2
  have hcont : ContinuousOn (slWronskian p R₁ DR₁ R₂ DR₂) (Icc α x) := fun y hy =>
    ((hd y (hsub hy)).continuousAt).continuousWithinAt
  have hdiff : DifferentiableOn ℝ (slWronskian p R₁ DR₁ R₂ DR₂) (interior (Icc α x)) := by
    rw [interior_Icc]
    exact fun y hy => ((hd y (hsub ⟨hy.1.le, hy.2.le⟩)).differentiableAt).differentiableWithinAt
  have hmono : MonotoneOn (slWronskian p R₁ DR₁ R₂ DR₂) (Icc α x) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc α x) hcont hdiff ?_
    rw [interior_Icc]
    intro y hy
    rw [(hd y (hsub ⟨hy.1.le, hy.2.le⟩)).deriv]
  have hanti : AntitoneOn (slWronskian p R₁ DR₁ R₂ DR₂) (Icc α x) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc α x) hcont hdiff ?_
    rw [interior_Icc]
    intro y hy
    rw [(hd y (hsub ⟨hy.1.le, hy.2.le⟩)).deriv]
  have h1 := hmono (left_mem_Icc.2 hx.1) (right_mem_Icc.2 hx.1) hx.1
  have h2 := hanti (left_mem_Icc.2 hx.1) (right_mem_Icc.2 hx.1) hx.1
  linarith

end GaloisForLFunctions.HTGeometry
