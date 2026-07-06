/-
# The second-order Euler–Maclaurin sandwich of the pole-excess field

The pole-excess field `poleExcess u = 1/(eᵘ − 1)` carries the exact Euler–Maclaurin expansion
`1/(eᵘ−1) = 1/u − 1/2 + u/12 − …`, whose coefficients are the Bernoulli numbers
`B₁ = −1/2`, `B₂ = 1/6` (giving `u/12`). This file pins the first two correction terms as a
Padé-tight two-sided bound, valid for every `u > 0`:

> `poleExcess_em_lower` : `1/u − 1/2 ≤ poleExcess u`,
> `poleExcess_em_upper` : `poleExcess u ≤ 1/u − 1/2 + u/12`.

The lower bound is the `[1/1]` Padé inequality `(2−u)eᵘ ≤ 2+u` (equivalently `coth(u/2) ≥ 2/u`); the
upper bound is the `[2/2]` Padé inequality `(u²+6u+12) ≤ (u²−6u+12)eᵘ`. Both are proved by
iterated monotonicity from `0`: the defining function vanishes at `0` and its derivative — after one,
two, or three differentiations reaching the manifestly nonnegative `u²eᵘ` — is nonnegative on `[0,∞)`.

These are the exact boundary-layer coefficients of the pole-excess field: on the near-gap distances
`aₖ, bₖ ≈ (2k+1)/i` the `−1/2` term cancels between the ahead and behind trains over the matched
range and the reciprocal `1/u` and correction `u/12` terms carry the finite-size deviation of
`poleModelDiff(2,·)` from its continuum residue `Φ(2) = 1`.
-/
import GaloisForLFunctions.RHTower.LegStripThreshold
open Real Set
noncomputable section
namespace RHTower

/-- If `g 0 = 0` and `g` has a derivative `g'` that is nonnegative on `[0,∞)`, then `g ≥ 0` on
`[0,∞)`. The workhorse for the iterated-monotonicity Padé bounds. -/
theorem nonneg_of_deriv {g g' : ℝ → ℝ} (hg0 : g 0 = 0)
    (hd : ∀ x, HasDerivAt g (g' x) x) (hpos : ∀ x, 0 ≤ x → 0 ≤ g' x) :
    ∀ {u : ℝ}, 0 ≤ u → 0 ≤ g u := by
  intro u hu
  have hmono : MonotoneOn g (Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
      (fun x _ => (hd x).continuousAt.continuousWithinAt)
      (fun x _ => (hd x).differentiableAt.differentiableWithinAt)
    intro x hx; rw [interior_Ici] at hx
    rw [(hd x).deriv]; exact hpos x (le_of_lt hx)
  have := hmono self_mem_Ici (mem_Ici.mpr hu) hu
  rwa [hg0] at this

/-- Derivative of the quadratic-times-exponential `(v²+av+b)·eᵛ`, as a clean lambda. -/
theorem hasDerivAt_quad_exp (a b x : ℝ) :
    HasDerivAt (fun v => (v^2 + a*v + b) * Real.exp v)
      (((2*x + a) + (x^2 + a*x + b)) * Real.exp x) x := by
  have hp : HasDerivAt (fun v : ℝ => v^2 + a*v + b) (2*x + a) x := by
    have := (((hasDerivAt_pow 2 x).add ((hasDerivAt_id x).const_mul a)).add_const b)
    convert this using 1; norm_num
  have := hp.mul (Real.hasDerivAt_exp x)
  convert this using 1; ring

/-- `[1/1]` Padé inequality `(2−u)eᵘ ≤ 2+u` for `u ≥ 0`: with `h(u) = 2+u−(2−u)eᵘ`, `h(0)=0`,
`h'(u) = 1−(1−u)eᵘ`, and `h''(u) = ueᵘ ≥ 0`. -/
theorem pade_one {u : ℝ} (hu : 0 ≤ u) : (2 - u) * Real.exp u ≤ 2 + u := by
  have hA : ∀ {v : ℝ}, 0 ≤ v → (1 - v) * Real.exp v ≤ 1 := by
    intro v hv
    have hmono : MonotoneOn (fun w => 1 - (1 - w) * Real.exp w) (Ici 0) := by
      apply monotoneOn_of_deriv_nonneg (convex_Ici 0) (by fun_prop)
        (fun w _ => (by fun_prop : DifferentiableAt ℝ _ w).differentiableWithinAt)
      intro w hw; rw [interior_Ici] at hw
      have hd : deriv (fun w => 1 - (1 - w) * Real.exp w) w = w * Real.exp w := by
        have h1 : HasDerivAt (fun w : ℝ => (1 - w) * Real.exp w)
            ((-1) * Real.exp w + (1 - w) * Real.exp w) w :=
          (((hasDerivAt_id w).const_sub 1).mul (Real.hasDerivAt_exp w))
        rw [(by convert h1.const_sub 1 using 1; ring : HasDerivAt
          (fun w : ℝ => 1 - (1 - w) * Real.exp w) (w * Real.exp w) w).deriv]
      rw [hd]; exact mul_nonneg (le_of_lt hw) (Real.exp_pos w).le
    have := hmono self_mem_Ici (mem_Ici.mpr hv) hv; simp at this; linarith
  have hmono : MonotoneOn (fun w => 2 + w - (2 - w) * Real.exp w) (Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0) (by fun_prop)
      (fun w _ => (by fun_prop : DifferentiableAt ℝ _ w).differentiableWithinAt)
    intro w hw; rw [interior_Ici] at hw
    have hd : deriv (fun w => 2 + w - (2 - w) * Real.exp w) w = 1 - (1 - w) * Real.exp w := by
      have h1 : HasDerivAt (fun w : ℝ => (2 - w) * Real.exp w)
          ((-1) * Real.exp w + (2 - w) * Real.exp w) w :=
        (((hasDerivAt_id w).const_sub 2).mul (Real.hasDerivAt_exp w))
      have h0 : HasDerivAt (fun w : ℝ => 2 + w) 1 w := by simpa using (hasDerivAt_id w).const_add 2
      rw [((by convert h0.sub h1 using 1; ring : HasDerivAt
        (fun w : ℝ => 2 + w - (2 - w) * Real.exp w) (1 - (1 - w) * Real.exp w) w)).deriv]
    rw [hd]; linarith [hA (le_of_lt hw)]
  have := hmono self_mem_Ici (mem_Ici.mpr hu) hu; simp at this; linarith

/-- `[2/2]` Padé inequality `(u²+6u+12) ≤ (u²−6u+12)eᵘ` for `u ≥ 0`: with
`m(u) = (u²−6u+12)eᵘ−(u²+6u+12)`, all of `m, m', m''` vanish at `0` and `m'''(u) = u²eᵘ ≥ 0`. -/
theorem pade_two {u : ℝ} (hu : 0 ≤ u) :
    (u^2 + 6*u + 12) ≤ (u^2 - 6*u + 12) * Real.exp u := by
  have hm2 : ∀ {v : ℝ}, 0 ≤ v → 0 ≤ (v^2 + (-2)*v + 2) * Real.exp v - 2 := by
    apply nonneg_of_deriv (g' := fun v => v^2 * Real.exp v) (by norm_num)
    · intro x; have h := (hasDerivAt_quad_exp (-2) 2 x).sub_const 2
      convert h using 1; ring
    · intro x _; positivity
  have hm1 : ∀ {v : ℝ}, 0 ≤ v → 0 ≤ (v^2 + (-4)*v + 6) * Real.exp v - (2*v + 6) := by
    apply nonneg_of_deriv (g' := fun v => (v^2 + (-2)*v + 2) * Real.exp v - 2) (by norm_num)
    · intro x
      have hlin : HasDerivAt (fun v : ℝ => 2*v + 6) 2 x := by
        have := ((hasDerivAt_id x).const_mul 2).add_const 6; convert this using 1; norm_num
      have h := (hasDerivAt_quad_exp (-4) 6 x).sub hlin
      convert h using 1; ring
    · intro x hx; have := hm2 hx; linarith
  have hm : ∀ {v : ℝ}, 0 ≤ v → 0 ≤ (v^2 + (-6)*v + 12) * Real.exp v - (v^2 + 6*v + 12) := by
    apply nonneg_of_deriv (g' := fun v => (v^2 + (-4)*v + 6) * Real.exp v - (2*v + 6)) (by norm_num)
    · intro x
      have hquad : HasDerivAt (fun v : ℝ => v^2 + 6*v + 12) (2*x + 6) x := by
        have := (((hasDerivAt_pow 2 x).add ((hasDerivAt_id x).const_mul 6)).add_const 12)
        convert this using 1; norm_num
      have h := (hasDerivAt_quad_exp (-6) 12 x).sub hquad
      convert h using 1; ring
    · intro x hx; have := hm1 hx; linarith
  have h := hm hu
  have heq : (u^2 + (-6)*u + 12) * Real.exp u = (u^2 - 6*u + 12) * Real.exp u := by ring
  linarith [h, heq]

/-- **Lower Euler–Maclaurin bound of the pole-excess field.** `1/u − 1/2 ≤ poleExcess u` for
`u > 0` — equivalently `coth(u/2) ≥ 2/u`. The `−1/2` is the `B₁` term. -/
theorem poleExcess_em_lower {u : ℝ} (hu : 0 < u) : 1/u - 1/2 ≤ poleExcess u := by
  have h1 : 0 < Real.exp u - 1 := by have := Real.one_lt_exp_iff.mpr hu; linarith
  have hP := pade_one hu.le
  rw [poleExcess]
  have e1 : 1/u - 1/2 = (2 - u)/(2*u) := by field_simp
  rw [e1, div_le_div_iff₀ (by positivity) h1]
  nlinarith [hP, Real.exp_pos u]

/-- **Upper Euler–Maclaurin bound of the pole-excess field.** `poleExcess u ≤ 1/u − 1/2 + u/12`
for `u > 0`. The `u/12` is the `B₂` term; together with `poleExcess_em_lower` this pins the field
to its second-order Euler–Maclaurin expansion. -/
theorem poleExcess_em_upper {u : ℝ} (hu : 0 < u) : poleExcess u ≤ 1/u - 1/2 + u/12 := by
  have h1 : 0 < Real.exp u - 1 := by have := Real.one_lt_exp_iff.mpr hu; linarith
  have hP := pade_two hu.le
  rw [poleExcess]
  have e1 : 1/u - 1/2 + u/12 = (u^2 - 6*u + 12)/(12*u) := by field_simp; ring
  rw [e1, div_le_div_iff₀ h1 (by positivity)]
  nlinarith [hP]

/-- The Euler–Maclaurin remainder `poleExcess u − (1/u − 1/2)` is trapped in `[0, u/12]`. -/
theorem poleExcess_em_remainder {u : ℝ} (hu : 0 < u) :
    poleExcess u - (1/u - 1/2) ∈ Set.Icc (0:ℝ) (u/12) := by
  constructor
  · linarith [poleExcess_em_lower hu]
  · linarith [poleExcess_em_upper hu]

end RHTower
end
