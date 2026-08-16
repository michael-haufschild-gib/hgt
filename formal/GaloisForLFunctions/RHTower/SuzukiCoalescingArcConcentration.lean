import GaloisForLFunctions.RHTower.SuzukiCoalescingBlaschkeFragmentation
import GaloisForLFunctions.HTGeometry.BlaschkePoissonArcTail

/-!
# A shallow Blaschke section is trivial away from its centre

The section centred at a boundary point `ζ` sends `ζ` to `-1` and, once its radial depth `1 - r` is
small, sends every boundary point at distance at least `d` from `ζ` to within
`2(1 - r)/(√r · d)` of `1`.  So all of its boundary phase is spent on the arc of radius `d` about
`ζ`, and the phase left over outside that arc is bounded by the radial depth alone.

The estimate is algebraic: subtracting one from the section leaves the factor `r - 1` explicitly,
and the denominator is bounded below by the radial split of the boundary distance.  No boundary
integral and no Poisson mass computation is needed.
-/

noncomputable section

namespace RHTower

open Complex

/-- The section sends its own centre to `-1`. -/
theorem suzukiCenteredBlaschkeSection_center {ζ : ℂ} (hζ : ‖ζ‖ = 1) {r : ℝ} (hr : r ≠ 1) :
    suzukiCenteredBlaschkeSection ζ r ζ = -1 := by
  have hconj : (starRingEnd ℂ) ζ * ζ = 1 := star_mul_self_eq_one_of_norm_eq_one hζ
  have hrne : (1 : ℂ) - (r : ℂ) ≠ 0 := by
    intro hzero
    apply hr
    have : ((r : ℝ) : ℂ) = 1 := by linear_combination -hzero
    exact_mod_cast this
  rw [suzukiCenteredBlaschkeSection_eq_paperFormula]
  have hden : (1 : ℂ) - (r : ℂ) * (starRingEnd ℂ) ζ * ζ = 1 - (r : ℂ) := by
    rw [mul_assoc, hconj, mul_one]
  have hnum : (r : ℂ) * ζ - ζ = -((1 - (r : ℂ)) * ζ) := by ring
  rw [hden, hnum, neg_div, mul_comm ((1 : ℂ) - (r : ℂ)) ζ, mul_div_assoc,
    div_self hrne, mul_one, mul_neg, hconj]

/-- **Arc concentration.**  Outside a `d`-arc about its centre a section of radial depth `1 - r` is
uniformly close to one. -/
theorem norm_suzukiCenteredBlaschkeSection_sub_one_le
    {ζ : ℂ} (hζ : ‖ζ‖ = 1) {r d : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1)
    (hd : 0 < d) {w : ℂ} (hw : ‖w‖ = 1) (hwd : d ≤ ‖w - ζ‖) :
    ‖suzukiCenteredBlaschkeSection ζ r w - 1‖ ≤ 2 * (1 - r) / (Real.sqrt r * d) := by
  have hconj : (starRingEnd ℂ) ζ * ζ = 1 := star_mul_self_eq_one_of_norm_eq_one hζ
  have hswap : ‖ζ - w‖ = ‖w - ζ‖ := norm_sub_rev _ _
  -- the radial split bounds the denominator below
  have hsplit : ‖ζ - (r : ℂ) * w‖ ^ 2 = (1 - r) ^ 2 + r * ‖ζ - w‖ ^ 2 :=
    GaloisForLFunctions.HTGeometry.norm_sub_radial_sq hw hζ r
  have hsqrtpos : 0 < Real.sqrt r * d := by positivity
  have hden_lb : Real.sqrt r * d ≤ ‖ζ - (r : ℂ) * w‖ := by
    have h1 : r * d ^ 2 ≤ ‖ζ - (r : ℂ) * w‖ ^ 2 := by
      rw [hsplit, hswap]
      have hsq : d ^ 2 ≤ ‖w - ζ‖ ^ 2 := pow_le_pow_left₀ hd.le hwd 2
      have hmul : r * d ^ 2 ≤ r * ‖w - ζ‖ ^ 2 := mul_le_mul_of_nonneg_left hsq hr0.le
      linarith [sq_nonneg (1 - r)]
    have h2 : Real.sqrt (r * d ^ 2) ≤ Real.sqrt (‖ζ - (r : ℂ) * w‖ ^ 2) := Real.sqrt_le_sqrt h1
    rwa [Real.sqrt_mul hr0.le, Real.sqrt_sq hd.le, Real.sqrt_sq (norm_nonneg _)] at h2
  have hDeq : (starRingEnd ℂ) ζ * (ζ - (r : ℂ) * w)
      = 1 - (r : ℂ) * (starRingEnd ℂ) ζ * w := by
    rw [mul_sub, hconj]
    ring
  have hDnorm : ‖(1 : ℂ) - (r : ℂ) * (starRingEnd ℂ) ζ * w‖ = ‖ζ - (r : ℂ) * w‖ := by
    rw [← hDeq, norm_mul, Complex.norm_conj, hζ, one_mul]
  have hne : (1 : ℂ) - (r : ℂ) * (starRingEnd ℂ) ζ * w ≠ 0 := by
    intro hzero
    rw [hzero, norm_zero] at hDnorm
    exact absurd hDnorm.symm (ne_of_gt (lt_of_lt_of_le hsqrtpos hden_lb))
  -- subtracting one leaves the radial defect as an explicit factor
  have hform : suzukiCenteredBlaschkeSection ζ r w - 1
      = (((r : ℂ) - 1) * (1 + (starRingEnd ℂ) ζ * w))
        / (1 - (r : ℂ) * (starRingEnd ℂ) ζ * w) := by
    rw [suzukiCenteredBlaschkeSection_eq_paperFormula, ← mul_div_assoc, div_sub_one hne]
    congr 1
    have hrζ : (starRingEnd ℂ) ζ * ((r : ℂ) * ζ) = (r : ℂ) := by
      rw [show (starRingEnd ℂ) ζ * ((r : ℂ) * ζ) = (r : ℂ) * ((starRingEnd ℂ) ζ * ζ) by ring,
        hconj, mul_one]
    rw [mul_sub, hrζ]
    ring
  rw [hform, norm_div, hDnorm]
  have hnum : ‖((r : ℂ) - 1) * (1 + (starRingEnd ℂ) ζ * w)‖ ≤ 2 * (1 - r) := by
    rw [norm_mul]
    have h1 : ‖((r : ℂ) - 1)‖ = 1 - r := by
      have : ((r : ℂ) - 1) = ((r - 1 : ℝ) : ℂ) := by push_cast; ring
      rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
      ring
    have h2 : ‖(1 : ℂ) + (starRingEnd ℂ) ζ * w‖ ≤ 2 := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_one, norm_mul, Complex.norm_conj, hζ, hw]
      norm_num
    rw [h1]
    calc (1 - r) * ‖(1 : ℂ) + (starRingEnd ℂ) ζ * w‖ ≤ (1 - r) * 2 :=
          mul_le_mul_of_nonneg_left h2 (by linarith)
      _ = 2 * (1 - r) := by ring
  exact div_le_div₀ (by linarith) hnum hsqrtpos hden_lb

/-- A unimodular number stays within `N` times its own defect after taking an `N`-th power. -/
theorem norm_pow_sub_one_le {x : ℂ} (hx : ‖x‖ = 1) (N : ℕ) :
    ‖x ^ N - 1‖ ≤ (N : ℝ) * ‖x - 1‖ := by
  induction N with
  | zero => simp
  | succ n ih =>
      have hstep : x ^ (n + 1) - 1 = x * (x ^ n - 1) + (x - 1) := by ring
      calc ‖x ^ (n + 1) - 1‖ = ‖x * (x ^ n - 1) + (x - 1)‖ := by rw [hstep]
        _ ≤ ‖x * (x ^ n - 1)‖ + ‖x - 1‖ := norm_add_le _ _
        _ = ‖x ^ n - 1‖ + ‖x - 1‖ := by rw [norm_mul, hx, one_mul]
        _ ≤ (n : ℝ) * ‖x - 1‖ + ‖x - 1‖ := by linarith
        _ = ((n + 1 : ℕ) : ℝ) * ‖x - 1‖ := by push_cast; ring

/-- Outside the arc the whole `N`-fold cascade is close to one. -/
theorem norm_suzukiCenteredBlaschkeSection_pow_sub_one_le
    {ζ : ℂ} (hζ : ‖ζ‖ = 1) {r d : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    (hd : 0 < d) (N : ℕ) {w : ℂ} (hw : ‖w‖ = 1) (hwd : d ≤ ‖w - ζ‖) :
    ‖suzukiCenteredBlaschkeSection ζ r w ^ N - 1‖
      ≤ (N : ℝ) * (2 * (1 - r) / (Real.sqrt r * d)) := by
  refine (norm_pow_sub_one_le
    (norm_suzukiCenteredBlaschkeSection_eq_one hζ hr0.le hr1 hw) N).trans ?_
  exact mul_le_mul_of_nonneg_left
    (norm_suzukiCenteredBlaschkeSection_sub_one_le hζ hr0 hr1.le hd hw hwd)
    (Nat.cast_nonneg N)

/-- **The loss outside the arc is the radial budget, not the number of factors.**  For the
fragmentation radius the cascade deviates from one by at most `2(-log κ)/(√r d)` outside the
`d`-arc, uniformly in `N`. -/
theorem norm_suzukiBlaschkeFragment_pow_sub_one_le
    {ζ : ℂ} (hζ : ‖ζ‖ = 1) {κ d : ℝ} (hκ0 : 0 < κ) (hκ1 : κ < 1)
    (hd : 0 < d) {N : ℕ} (hN : 0 < N) {w : ℂ} (hw : ‖w‖ = 1) (hwd : d ≤ ‖w - ζ‖) :
    ‖suzukiCenteredBlaschkeSection ζ (suzukiBlaschkeFragmentRadius κ N) w ^ N - 1‖
      ≤ 2 * (-Real.log κ) / (Real.sqrt (suzukiBlaschkeFragmentRadius κ N) * d) := by
  have hr0 : 0 < suzukiBlaschkeFragmentRadius κ N := suzukiBlaschkeFragmentRadius_pos hκ0 N
  have hr1 : suzukiBlaschkeFragmentRadius κ N < 1 :=
    suzukiBlaschkeFragmentRadius_lt_one hκ0.le hκ1 hN
  have hden : 0 < Real.sqrt (suzukiBlaschkeFragmentRadius κ N) * d := by positivity
  refine (norm_suzukiCenteredBlaschkeSection_pow_sub_one_le hζ hr0 hr1 hd N hw hwd).trans ?_
  have hbudget := suzukiBlaschkeFragment_radialBudget hκ0 hN
  rw [mul_div_assoc'] at *
  refine div_le_div_of_nonneg_right ?_ hden.le
  · calc (N : ℝ) * (2 * (1 - suzukiBlaschkeFragmentRadius κ N))
        = 2 * ((N : ℝ) * (1 - suzukiBlaschkeFragmentRadius κ N)) := by ring
      _ ≤ 2 * (-Real.log κ) := by linarith

end RHTower
