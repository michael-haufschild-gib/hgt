/-
# The u-plane reflection structure: the descent halves the symmetry group

In the `s`-plane the completed zeta `ξ` carries the Klein four-group
`V₄ = {s, 1−s, s̄, 1−s̄}` (functional equation × Schwarz reflection).  Under the descent
`w = (s − 1/2)²`, `xiDescent w = ξ(1/2 + √w)`, the functional-equation reflection
`s ↦ 1 − s`, i.e. `z ↦ −z` on `z = s − 1/2`, is **absorbed** by the squaring `z ↦ z²`.
What survives on the `u`-plane is exactly the residual `ℤ/2`, conjugation `w ↦ w̄`:

* `xiDescent (w̄) = conj (xiDescent w)` (`xiDescent_conj`) — the u-plane reality, obtained
  from `ξ(s̄) = conj ξ(s)` and `√(w̄) = conj √w` off the slit, then propagated to the whole
  plane by continuity across the dense slit plane (`dense_slitPlane`).

The consequence is geometric and is the point of Phase D: the map `z ↦ z²` carries the
`s`-plane right **upper** quadrant `{Re z > 0, Im z ≥ 0}` bijectively and order-preservingly
onto the `u`-plane upper half of the slit plane `{Im w ≥ 0} ∩ slitPlane`, while conjugation
supplies the lower half for free.  Hence the whole RH multiplicity-parity ladder is decided on
**half** the slit plane:

  `RHLadder k ↔ ∀ w ∈ slitPlane, 0 ≤ Im w → xiDescent w = 0 → 2^k ∣ ord_w xiDescent`
  (`rhLadder_iff_xiDescent_upperHalf`).

The conjugation constraint — not any flow — cuts the verification domain in half.  Nothing
here integrates a loop or constructs a carrier: the reduction is a symmetry of the *given*
descended function.
-/
import GaloisForLFunctions.RHTower.UPlaneDescent
import GaloisForLFunctions.RHTower.RHLadderTheory

namespace RHTower

open Complex Filter Topology Metric Set

/-! ### The slit plane is dense, and conjugation preserves it -/

/-- The slit plane `ℂ ∖ (−∞, 0]` is dense: its complement is a closed half-line, nowhere dense.
Any point off the slit already lies in it; a point on the slit is approximated by pushing a small
imaginary part. -/
theorem dense_slitPlane : Dense (slitPlane : Set ℂ) := by
  rw [Metric.dense_iff]
  intro x r hr
  by_cases hx : x ∈ slitPlane
  · exact ⟨x, Metric.mem_ball_self hr, hx⟩
  · rw [Complex.mem_slitPlane_iff, not_or, not_lt, ne_eq, not_not] at hx
    obtain ⟨_, hxim⟩ := hx
    refine ⟨x + ((r / 2 : ℝ) : ℂ) * I, ?_, ?_⟩
    · rw [Metric.mem_ball, Complex.dist_eq,
        show x + ((r / 2 : ℝ) : ℂ) * I - x = ((r / 2 : ℝ) : ℂ) * I from by ring,
        norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (by linarith)]
      linarith
    · rw [Complex.mem_slitPlane_iff]
      refine Or.inr ?_
      simp only [Complex.add_im, hxim, Complex.mul_im, Complex.ofReal_re, Complex.I_im,
        Complex.ofReal_im, Complex.I_re, mul_one, mul_zero, add_zero, zero_add]
      linarith

/-! ### The principal square root and the descent commute with conjugation -/

/-- The principal square root commutes with conjugation off the slit: `√(w̄) = conj(√w)`.
The half-power is real, so it passes through `log(w̄) = conj(log w)` and `exp(conj·) = conj(exp·)`. -/
theorem uSqrt_conj {w : ℂ} (hw : w ∈ slitPlane) :
    uSqrt ((starRingEnd ℂ) w) = (starRingEnd ℂ) (uSqrt w) := by
  simp only [uSqrt]
  rw [Complex.log_conj _ (Complex.slitPlane_arg_ne_pi hw), ← Complex.exp_conj, map_mul,
    Complex.conj_ofReal]

/-- **The u-plane reality.**  The descended function is conjugation-equivariant:
`xiDescent(w̄) = conj(xiDescent w)`.  On the slit plane it is `ξ(s̄) = conj ξ(s)` transported
through `√(w̄) = conj √w`; both sides are continuous and the slit plane is dense, so the identity
holds on all of `ℂ`. -/
theorem xiDescent_conj (w : ℂ) :
    xiDescent ((starRingEnd ℂ) w) = (starRingEnd ℂ) (xiDescent w) := by
  have hEqOn : Set.EqOn (fun w => xiDescent ((starRingEnd ℂ) w))
      (fun w => (starRingEnd ℂ) (xiDescent w)) slitPlane := by
    intro z hz
    have hzne : z ≠ 0 := slitPlane_ne_zero hz
    have hcne : (starRingEnd ℂ) z ≠ 0 := (map_ne_zero _).mpr hzne
    simp only
    rw [xiDescent_of_ne_zero hcne, uSqrt_conj hz, xiDescent_of_ne_zero hzne, ← xi_conj, map_add,
      show (starRingEnd ℂ) (1 / 2 : ℂ) = (1 / 2 : ℂ) from by rw [map_div₀, map_one, map_ofNat]]
  have hcont1 : Continuous (fun w => xiDescent ((starRingEnd ℂ) w)) :=
    xiDescent_continuous.comp Complex.continuous_conj
  have hcont2 : Continuous (fun w => (starRingEnd ℂ) (xiDescent w)) :=
    Complex.continuous_conj.comp xiDescent_continuous
  exact congrFun (Continuous.ext_on dense_slitPlane hcont1 hcont2 hEqOn) w

/-- **Reality pairing of u-plane orders.**  `ord_{w̄}(xiDescent) = ord_w(xiDescent)`: conjugation is
an order-preserving involution of the descended divisor. -/
theorem xiDescent_orderAt_conj (w : ℂ) :
    analyticOrderAt xiDescent ((starRingEnd ℂ) w) = analyticOrderAt xiDescent w := by
  have hfun : (fun z => (starRingEnd ℂ) (xiDescent ((starRingEnd ℂ) z))) = xiDescent := by
    funext z
    rw [xiDescent_conj, Complex.conj_conj]
  have h := analyticOrderAt_conj_conj xiDescent_differentiable w
  rwa [hfun] at h

/-! ### The upper-half correspondence of the square descent -/

/-- The principal square root of an upper-half slit point stays in the closed upper half:
`0 ≤ Im w → 0 ≤ Im(√w)`.  Its imaginary part is `√‖w‖ · sin(arg w / 2)` and `arg w / 2 ∈ [0, π/2]`. -/
theorem uSqrt_im_nonneg {w : ℂ} (him : 0 ≤ w.im) :
    0 ≤ (uSqrt w).im := by
  simp only [uSqrt, Complex.exp_im]
  refine mul_nonneg (Real.exp_pos _).le ?_
  have himval : (((1 / 2 : ℝ) : ℂ) * Complex.log w).im = (1 / 2) * w.arg := by
    rw [Complex.im_ofReal_mul, Complex.log_im]
  rw [himval]
  refine Real.sin_nonneg_of_nonneg_of_le_pi ?_ ?_
  · have := Complex.arg_nonneg_iff.mpr him; linarith
  · have := Complex.arg_le_pi w; linarith [Real.pi_pos]

/-! ### The domain-halving capstone -/

/-- **The RH ladder is decided on the upper half of the slit plane.**  Because the descent absorbs
the functional-equation reflection and conjugation `w ↦ w̄` is an order-preserving symmetry of
`xiDescent`, the rung-`k` divisibility condition need only be checked for slit-plane zeros with
`0 ≤ Im w`; the lower half is supplied by the reality pairing.  The map `s ↦ (s − 1/2)²` is the
order-preserving bijection between the `s`-plane right upper quadrant and the `u`-plane upper-half
slit plane that transports the two conditions into one another. -/
theorem rhLadder_iff_xiDescent_upperHalf (k : ℕ) :
    RHLadder k ↔
      ∀ w ∈ slitPlane, 0 ≤ w.im → xiDescent w = 0 →
        ((2 ^ k : ℕ) : ℕ∞) ∣ analyticOrderAt xiDescent w := by
  rw [rhLadder_iff_upperHalf]
  constructor
  · intro h w hw hwim hw0
    set ρ : ℂ := (1 / 2 : ℂ) + uSqrt w with hρdef
    have hρ : ρ ∈ rightHalf := by
      rw [mem_rightHalf, hρdef, Complex.add_re, show (1 / 2 : ℂ).re = (1 / 2 : ℝ) from by norm_num]
      have := uSqrt_re_pos hw; linarith
    have hρim : 0 ≤ ρ.im := by
      rw [hρdef, Complex.add_im, show (1 / 2 : ℂ).im = (0 : ℝ) from by norm_num, zero_add]
      exact uSqrt_im_nonneg hwim
    have hxi0 : xi ρ = 0 := by
      rw [hρdef, ← xiDescent_of_ne_zero (slitPlane_ne_zero hw)]; exact hw0
    have hord : analyticOrderAt xiDescent w = analyticOrderAt xi ρ := by
      have hsq : (ρ - (1 / 2 : ℂ)) ^ (2 : ℕ) = w := by
        rw [hρdef, add_sub_cancel_left]; exact uSqrt_sq (slitPlane_ne_zero hw)
      rw [← hsq]; exact analyticOrderAt_xiDescent_center_sq hρ
    rw [hord]; exact h ρ hρ hρim hxi0
  · intro h ρ hρ hρim hxi0
    set w : ℂ := (ρ - (1 / 2 : ℂ)) ^ (2 : ℕ) with hwdef
    have hwre : 0 < (ρ - (1 / 2 : ℂ)).re := by
      rw [Complex.sub_re, show (1 / 2 : ℂ).re = (1 / 2 : ℝ) from by norm_num]
      linarith [mem_rightHalf.mp hρ]
    have hw : w ∈ slitPlane := sq_mem_slitPlane_of_re_pos hwre
    have hwim : 0 ≤ w.im := by
      have himρ : 0 ≤ (ρ - (1 / 2 : ℂ)).im := by
        rw [Complex.sub_im, show (1 / 2 : ℂ).im = (0 : ℝ) from by norm_num, sub_zero]; exact hρim
      rw [hwdef, pow_two, Complex.mul_im]
      have := mul_nonneg hwre.le himρ; nlinarith
    have hw0 : xiDescent w = 0 := by rw [hwdef, ← xi_eq_xiDescent]; exact hxi0
    have hord := analyticOrderAt_xiDescent_center_sq hρ
    rw [← hwdef] at hord
    rw [← hord]; exact h w hw hwim hw0

end RHTower
