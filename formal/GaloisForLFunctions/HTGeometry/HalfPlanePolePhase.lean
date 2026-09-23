import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# The boundary phase of a half-plane Blaschke factor

For a pole `u + iv` in the open upper half plane the factor `(z - (u+iv))/(z - (u-iv))` is
unimodular on the real axis, and its *globally continuous* phase is

`2 arctan((x - u)/v) + π`,

an increasing bijection of `ℝ` onto `(0, 2π)` with derivative the half-plane Poisson kernel
`2v/((x-u)² + v²)`.  A deep pole therefore spends almost a full turn on any interval containing its
foot: the phase gained over `[α, β]` with `α < u < β` is at least

`2π - 2v(1/(β-u) + 1/(u-α))`,

so the deficit from a full turn is proportional to the depth alone.  Iterating a pole `N` times
multiplies both the gain and the deficit by `N`.

This makes a boundary crossing count explicit: no winding number, no boundary integral, only the
addition formula for the arctangent.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open Complex Real Filter Topology

/-! ## Arctangent estimates -/

/-- The arctangent is strictly below the identity on the positive axis. -/
theorem arctan_lt_self {s : ℝ} (hs : 0 < s) : Real.arctan s < s := by
  have h1 : 0 < Real.arctan s := Real.arctan_pos.mpr hs
  have h2 : Real.arctan s < π / 2 := Real.arctan_lt_pi_div_two s
  have h3 := Real.lt_tan h1 h2
  rwa [Real.tan_arctan] at h3

/-- A tail estimate for the arctangent: it approaches the quarter turn at rate `1/T`. -/
theorem pi_div_two_sub_inv_le_arctan {T : ℝ} (hT : 0 < T) :
    π / 2 - 1 / T ≤ Real.arctan T := by
  have hinv : Real.arctan T⁻¹ = π / 2 - Real.arctan T := Real.arctan_inv_of_pos hT
  have hlt : Real.arctan T⁻¹ < T⁻¹ := arctan_lt_self (by positivity)
  rw [hinv] at hlt
  rw [one_div]
  linarith

/-! ## Trigonometric values along a ray -/

/-- The normalising radius attached to a ratio. -/
theorem sqrt_one_add_div_sq {c x : ℝ} (hx : 0 < x) :
    Real.sqrt (1 + (c / x) ^ (2 : ℕ)) = Real.sqrt (x ^ (2 : ℕ) + c ^ (2 : ℕ)) / x := by
  have hrhs : 0 ≤ Real.sqrt (x ^ (2 : ℕ) + c ^ (2 : ℕ)) / x := by positivity
  have hsq : (Real.sqrt (x ^ (2 : ℕ) + c ^ (2 : ℕ)) / x) ^ (2 : ℕ) = 1 + (c / x) ^ (2 : ℕ) := by
    rw [div_pow, Real.sq_sqrt (by positivity)]
    field_simp
  rw [← hsq, Real.sqrt_sq hrhs]

theorem cos_arctan_div {c x : ℝ} (hx : 0 < x) :
    Real.cos (Real.arctan (c / x)) = x / Real.sqrt (x ^ (2 : ℕ) + c ^ (2 : ℕ)) := by
  rw [Real.cos_arctan, sqrt_one_add_div_sq hx, one_div_div]

theorem sin_arctan_div {c x : ℝ} (hx : 0 < x) :
    Real.sin (Real.arctan (c / x)) = c / Real.sqrt (x ^ (2 : ℕ) + c ^ (2 : ℕ)) := by
  have hr : 0 < Real.sqrt (x ^ (2 : ℕ) + c ^ (2 : ℕ)) := Real.sqrt_pos.mpr (by positivity)
  rw [Real.sin_arctan, sqrt_one_add_div_sq hx]
  field_simp

/-! ## The pole phase -/

/-- The continuous boundary phase of the half-plane factor with pole `u + iv`. -/
def polePhase (u v x : ℝ) : ℝ := 2 * Real.arctan ((x - u) / v) + π

/-- The factor is unimodular on the real axis with the stated phase. -/
theorem polePhase_eq_exp {u v x : ℝ} (hv : 0 < v) :
    ((x : ℂ) - ((u : ℂ) + (v : ℂ) * I)) / ((x : ℂ) - ((u : ℂ) - (v : ℂ) * I))
      = Complex.exp ((polePhase u v x : ℂ) * I) := by
  set s : ℝ := x - u with hs
  have hr : 0 < Real.sqrt (v ^ (2 : ℕ) + s ^ (2 : ℕ)) := Real.sqrt_pos.mpr (by positivity)
  have hrC : ((Real.sqrt (v ^ (2 : ℕ) + s ^ (2 : ℕ)) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hr
  have hexp : Complex.exp ((Real.arctan (s / v) : ℂ) * I)
      = ((v : ℂ) + (s : ℂ) * I) / ((Real.sqrt (v ^ (2 : ℕ) + s ^ (2 : ℕ)) : ℝ) : ℂ) := by
    rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
      cos_arctan_div hv, sin_arctan_div hv]
    push_cast
    field_simp
  have hsq : Complex.exp ((polePhase u v x : ℂ) * I)
      = -(Complex.exp ((Real.arctan (s / v) : ℂ) * I)) ^ (2 : ℕ) := by
    have hsplit : ((polePhase u v x : ℝ) : ℂ) * I
        = ((Real.arctan (s / v) : ℂ) * I + (Real.arctan (s / v) : ℂ) * I) + (π : ℂ) * I := by
      rw [polePhase]
      push_cast
      ring
    rw [hsplit, Complex.exp_add, Complex.exp_add, Complex.exp_pi_mul_I]
    ring
  have hden : (s : ℂ) + (v : ℂ) * I ≠ 0 := by
    intro hzero
    have hre := congrArg Complex.im hzero
    simp at hre
    exact absurd hre (ne_of_gt hv)
  have hnum : (x : ℂ) - ((u : ℂ) + (v : ℂ) * I) = (s : ℂ) - (v : ℂ) * I := by
    rw [hs]; push_cast; ring
  have hnum' : (x : ℂ) - ((u : ℂ) - (v : ℂ) * I) = (s : ℂ) + (v : ℂ) * I := by
    rw [hs]; push_cast; ring
  have hrsq : (((Real.sqrt (v ^ (2 : ℕ) + s ^ (2 : ℕ)) : ℝ) : ℂ)) ^ (2 : ℕ) = ((v : ℂ) ^ (2 : ℕ) + (s : ℂ) ^ (2 : ℕ)) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by positivity)]
    push_cast
    ring
  have hvs : ((v : ℂ) ^ (2 : ℕ) + (s : ℂ) ^ (2 : ℕ)) ≠ 0 := by
    rw [← hrsq]
    exact pow_ne_zero 2 hrC
  have hI3 : (I : ℂ) ^ (3 : ℕ) = -I := by
    rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ, Complex.I_sq, neg_one_mul]
  rw [hsq, hexp, hnum, hnum', div_pow, hrsq]
  field_simp
  ring_nf
  simp only [Complex.I_sq, hI3]
  ring

/-- The phase rate is the half-plane Poisson kernel. -/
theorem hasDerivAt_polePhase (u : ℝ) {v : ℝ} (hv : 0 < v) (x : ℝ) :
    HasDerivAt (polePhase u v) (2 * v / ((x - u) ^ (2 : ℕ) + v ^ (2 : ℕ))) x := by
  have hinner : HasDerivAt (fun y : ℝ => (y - u) / v) (1 / v) x := by
    simpa using ((hasDerivAt_id x).sub_const u).div_const v
  have harc : HasDerivAt Real.arctan (1 / (1 + ((x - u) / v) ^ (2 : ℕ))) ((x - u) / v) :=
    Real.hasDerivAt_arctan _
  have hcomp := harc.comp x hinner
  simp only [Function.comp_def] at hcomp
  have hres : HasDerivAt (polePhase u v)
      (2 * ((1 / (1 + ((x - u) / v) ^ (2 : ℕ))) * (1 / v))) x := by
    have hfun : polePhase u v = fun y : ℝ => 2 * Real.arctan ((y - u) / v) + π := rfl
    rw [hfun]
    exact (hcomp.const_mul 2).add_const π
  convert hres using 1
  have hvne : v ≠ 0 := ne_of_gt hv
  have hsum : (1 : ℝ) + ((x - u) / v) ^ (2 : ℕ) ≠ 0 := by positivity
  field_simp
  ring

theorem continuous_polePhase (u : ℝ) {v : ℝ} (hv : 0 < v) : Continuous (polePhase u v) := by
  refine continuous_iff_continuousAt.mpr fun x => ?_
  exact (hasDerivAt_polePhase u hv x).differentiableAt.continuousAt

theorem strictMono_polePhase (u : ℝ) {v : ℝ} (hv : 0 < v) : StrictMono (polePhase u v) := by
  refine strictMono_of_deriv_pos fun x => ?_
  rw [(hasDerivAt_polePhase u hv x).deriv]
  positivity

/-! ## The full turn of a deep pole -/

/-- The phase gain over an interval is twice a sum of two arctangents. -/
theorem polePhase_gain (u v α β : ℝ) :
    polePhase u v β - polePhase u v α
      = 2 * (Real.arctan ((β - u) / v) + Real.arctan ((u - α) / v)) := by
  have hneg : (α - u) / v = -((u - α) / v) := by ring_nf
  rw [polePhase, polePhase, hneg, Real.arctan_neg]
  ring

/-- **A deep pole spends almost a full turn on any interval around its foot.**  The deficit is
proportional to the depth. -/
theorem polePhase_gain_ge {u v α β : ℝ} (hv : 0 < v) (hα : α < u) (hβ : u < β) :
    2 * π - 2 * v * (1 / (β - u) + 1 / (u - α)) ≤ polePhase u v β - polePhase u v α := by
  have hA : 0 < (β - u) / v := by
    apply div_pos (by linarith) hv
  have hB : 0 < (u - α) / v := by
    apply div_pos (by linarith) hv
  have h1 := pi_div_two_sub_inv_le_arctan hA
  have h2 := pi_div_two_sub_inv_le_arctan hB
  rw [polePhase_gain u v α β]
  have hinvA : 1 / ((β - u) / v) = v / (β - u) := by
    rw [one_div_div]
  have hinvB : 1 / ((u - α) / v) = v / (u - α) := by
    rw [one_div_div]
  rw [hinvA] at h1
  rw [hinvB] at h2
  have hexpand : 2 * v * (1 / (β - u) + 1 / (u - α)) = 2 * (v / (β - u) + v / (u - α)) := by
    field_simp
  rw [hexpand]
  linarith

/-- The gain never exceeds a full turn. -/
theorem polePhase_gain_lt (u v α β : ℝ) : polePhase u v β - polePhase u v α < 2 * π := by
  have h1 : Real.arctan ((β - u) / v) < π / 2 := Real.arctan_lt_pi_div_two _
  have h2 : -(π / 2) < Real.arctan ((α - u) / v) := Real.neg_pi_div_two_lt_arctan _
  rw [polePhase, polePhase]
  linarith

/-- Iterating a pole `N` times multiplies both the full turn and the deficit. -/
theorem polePhase_nsmul_gain_ge {u v α β : ℝ} (N : ℕ) (hv : 0 < v) (hα : α < u) (hβ : u < β) :
    2 * π * N - 2 * (N : ℝ) * v * (1 / (β - u) + 1 / (u - α))
      ≤ (N : ℝ) * (polePhase u v β - polePhase u v α) := by
  have hbase := polePhase_gain_ge hv hα hβ
  have hN : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  nlinarith

/-- As the pole approaches the axis the gain tends to a full turn. -/
theorem tendsto_polePhase_gain {u α β : ℝ} (hα : α < u) (hβ : u < β) :
    Tendsto (fun v : ℝ => polePhase u v β - polePhase u v α) (𝓝[>] 0) (𝓝 (2 * π)) := by
  have hlow : Tendsto
      (fun v : ℝ => 2 * π - 2 * v * (1 / (β - u) + 1 / (u - α))) (𝓝[>] 0) (𝓝 (2 * π)) := by
    have hcont : Continuous (fun v : ℝ => 2 * π - 2 * v * (1 / (β - u) + 1 / (u - α))) := by
      fun_prop
    have hlim := hcont.tendsto (0 : ℝ)
    simpa using hlim.mono_left nhdsWithin_le_nhds
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with v hv
    exact polePhase_gain_ge hv hα hβ
  · filter_upwards [self_mem_nhdsWithin] with v hv
    exact (polePhase_gain_lt u v α β).le

end GaloisForLFunctions.HTGeometry
