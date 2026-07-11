import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.LinearCombination
import GaloisForLFunctions.RHTower.FuchsProlateScale

/-!
# Slepian commutation of the sinc kernel with the prolate operator

The time–band concentration kernel `K_c(x,y) = sin(c(x−y))/(π(x−y))` satisfies the same prolate
Sturm–Liouville action in each variable off the diagonal:
`P_x K = P_y K` where `P` is `(1−t²)∂² − 2t∂ − c²t²` (`prolateSLAction_sincKernel`).  This is the
identity behind Slepian's commuting-operator phenomenon: it forces the time–band integral
operator to commute with the prolate differential operator, so the eigenfunctions of the
concentration problem are the eigenfunctions of the prolate ODE — the door through which the
fixed-index eigenvalue asymptotics of the concentration problem are computed.

The proof reduces along the difference variable `u = x−y`.  The kernel is a function
`g(u) = sin(cu)/(πu)` of `u` alone, so both partials are `±g'`, `g''` at `u`, and the two-variable
commutation collapses to the radial (spherical Bessel) identity
`u·g'' + 2·g' + c²·u·g = 0` (`sincScalar_bessel`), which holds because `u·g = sin(cu)/π`
satisfies the harmonic equation `(u·g)'' = −c²·(u·g)`.
-/

open Filter Real

namespace RHTower

/-- The sinc profile `g(u) = sin(cu)/(πu)` of the time–band kernel. -/
noncomputable def sincScalar (c u : ℝ) : ℝ := Real.sin (c * u) / (Real.pi * u)

/-- Off the origin, `g'(u) = (cu·cos(cu) − sin(cu))/(πu²)`. -/
noncomputable def sincScalarD (c u : ℝ) : ℝ :=
  (c * u * Real.cos (c * u) - Real.sin (c * u)) / (Real.pi * u ^ 2)

theorem hasDerivAt_sincScalar {c u : ℝ} (h : u ≠ 0) :
    HasDerivAt (sincScalar c) (sincScalarD c u) u := by
  have hcu : HasDerivAt (fun v : ℝ => c * v) c u := by
    simpa using (hasDerivAt_id u).const_mul c
  have hnum : HasDerivAt (fun v : ℝ => Real.sin (c * v)) (Real.cos (c * u) * c) u := hcu.sin
  have hden : HasDerivAt (fun v : ℝ => Real.pi * v) Real.pi u := by
    simpa using (hasDerivAt_id u).const_mul Real.pi
  have hden0 : Real.pi * u ≠ 0 := mul_ne_zero Real.pi_ne_zero h
  have hdiv := hnum.div hden hden0
  have hval : (Real.cos (c * u) * c * (Real.pi * u) - Real.sin (c * u) * Real.pi)
        / (Real.pi * u) ^ 2 = sincScalarD c u := by
    unfold sincScalarD
    field_simp
  rw [hval] at hdiv
  exact hdiv

theorem deriv_sincScalar {c u : ℝ} (h : u ≠ 0) :
    deriv (sincScalar c) u = sincScalarD c u :=
  (hasDerivAt_sincScalar h).deriv

/-- **Radial (spherical Bessel) identity of the sinc profile**:
`u·g'' + 2·g' + c²·u·g = 0` away from the origin, because `u·g = sin(cu)/π` solves the
harmonic equation `(u·g)'' = −c²·(u·g)`. -/
theorem sincScalar_bessel {c u : ℝ} (h : u ≠ 0) :
    u * deriv (deriv (sincScalar c)) u + 2 * deriv (sincScalar c) u
      + c ^ 2 * u * sincScalar c u = 0 := by
  have hev : deriv (sincScalar c) =ᶠ[nhds u] fun v => sincScalarD c v := by
    filter_upwards [isOpen_compl_singleton.mem_nhds
      (by simpa using h : u ∈ ({0}ᶜ : Set ℝ))] with v hv
    exact deriv_sincScalar (by simpa using hv)
  have hcu : HasDerivAt (fun v : ℝ => c * v) c u := by
    simpa using (hasDerivAt_id u).const_mul c
  have hcv : HasDerivAt (fun v : ℝ => c * v * Real.cos (c * v))
      (c * Real.cos (c * u) + c * u * (-Real.sin (c * u) * c)) u := hcu.mul hcu.cos
  have hnum : HasDerivAt (fun v : ℝ => c * v * Real.cos (c * v) - Real.sin (c * v))
      (c * Real.cos (c * u) + c * u * (-Real.sin (c * u) * c) - Real.cos (c * u) * c) u :=
    hcv.sub hcu.sin
  have hden : HasDerivAt (fun v : ℝ => Real.pi * v ^ 2) (Real.pi * (2 * u)) u := by
    have h2 : HasDerivAt (fun v : ℝ => v ^ 2) (2 * u) u := by
      simpa using hasDerivAt_pow 2 u
    simpa using h2.const_mul Real.pi
  have hden0 : Real.pi * u ^ 2 ≠ 0 := mul_ne_zero Real.pi_ne_zero (pow_ne_zero 2 h)
  have hdiv := hnum.div hden hden0
  have hD2 : deriv (deriv (sincScalar c)) u
      = ((c * Real.cos (c * u) + c * u * (-Real.sin (c * u) * c) - Real.cos (c * u) * c)
            * (Real.pi * u ^ 2)
          - (c * u * Real.cos (c * u) - Real.sin (c * u)) * (Real.pi * (2 * u)))
        / (Real.pi * u ^ 2) ^ 2 := by
    rw [hev.deriv_eq]
    exact hdiv.deriv
  rw [hD2, deriv_sincScalar h]
  unfold sincScalarD sincScalar
  field_simp
  ring

/-- The time–band concentration kernel `K_c(x,y) = sin(c(x−y))/(π(x−y))`. -/
noncomputable def sincKernel (c x y : ℝ) : ℝ := sincScalar c (x - y)

theorem sincKernel_symm (c x y : ℝ) : sincKernel c x y = sincKernel c y x := by
  unfold sincKernel sincScalar
  rw [show c * (y - x) = -(c * (x - y)) by ring, Real.sin_neg,
    show Real.pi * (y - x) = -(Real.pi * (x - y)) by ring, neg_div_neg_eq]

/-- **Slepian commutation identity.**  Off the diagonal, the sinc kernel satisfies the same
prolate Sturm–Liouville action in each of its two variables:
`P_x K_c(x,y) = P_y K_c(x,y)`.  Both partial actions reduce to the profile `g` at `u = x−y`
(`∂_x ↦ g'`, `∂_y ↦ −g'`, second partials `↦ g''`), and the difference is
`−(x+y)·(u·g'' + 2·g' + c²·u·g)`, which vanishes by the radial identity. -/
theorem prolateSLAction_sincKernel {c x y : ℝ} (h : x ≠ y) :
    prolateSLAction c (fun t => sincKernel c t y) x
      = prolateSLAction c (fun s => sincKernel c x s) y := by
  have hu : x - y ≠ 0 := sub_ne_zero.mpr h
  have hx1 : deriv (fun t => sincKernel c t y) x = deriv (sincScalar c) (x - y) :=
    deriv_comp_sub_const (sincScalar c) y x
  have hx2 : deriv (deriv (fun t => sincKernel c t y)) x
      = deriv (deriv (sincScalar c)) (x - y) := by
    have hfun : deriv (fun t => sincKernel c t y) = fun t => deriv (sincScalar c) (t - y) :=
      funext fun t => deriv_comp_sub_const (sincScalar c) y t
    rw [hfun]
    exact deriv_comp_sub_const (deriv (sincScalar c)) y x
  have hy1 : deriv (fun s => sincKernel c x s) y = -deriv (sincScalar c) (x - y) :=
    deriv_comp_const_sub (sincScalar c) x y
  have hy2 : deriv (deriv (fun s => sincKernel c x s)) y
      = deriv (deriv (sincScalar c)) (x - y) := by
    have hfun : deriv (fun s => sincKernel c x s) = fun s => -deriv (sincScalar c) (x - s) :=
      funext fun s => deriv_comp_const_sub (sincScalar c) x s
    rw [hfun]
    have hneg : deriv (fun s : ℝ => -deriv (sincScalar c) (x - s)) y
        = -deriv (fun s : ℝ => deriv (sincScalar c) (x - s)) y := deriv.neg
    rw [hneg, deriv_comp_const_sub (deriv (sincScalar c)) x y, neg_neg]
  have hb := sincScalar_bessel (c := c) hu
  unfold prolateSLAction
  rw [hx1, hx2, hy1, hy2]
  simp only [sincKernel]
  linear_combination (-(x + y)) * hb

end RHTower
