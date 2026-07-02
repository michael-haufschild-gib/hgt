/-
# The window branch for EVERY large parameter: `phiB b` on the disk, `‖b‖ ≥ 5`

Parameterization of the `b = 4` window construction (`U0PhiFourWindow`) over all `‖b‖ ≥ 5`.
The far field becomes `farB b = {‖w‖ > ‖b‖ − 3/2}`:

* one quadratic step from the disk `‖z‖ < 21/20` lands in it (`‖z² + b‖ ≥ ‖b‖ − (21/20)²`);
* it is forward invariant with escape factor `3/2` and series ratio `‖b/w²‖ ≤ 1/2`
  (all margins are polynomial inequalities in `‖b‖`, valid from `‖b‖ = 5`).

For complex `b` the one-step image `z² + b` need not avoid the negative real slit, so the branch
is rotated through the parameter:

  `phiB b z := exp(½·(log b + log(1 + z²/b) + tail(z² + b)))`

— `1 + z²/b` stays in the right half-plane (`‖z²/b‖ < 1/2`), so `phiB` is analytic on the WHOLE
disk `ball 0 (21/20)` across the unit circle, and `phiB² = bottcherCoord b ∘ (z ↦ z² + b)`
branch-free at the `exp` level.  The functional equation, escape growth, dyadic pullback chain,
and the natural-boundary window engine instance all parameterize verbatim.
-/
import GaloisForLFunctions.U0.U0PhiFourWindow
import GaloisForLFunctions.U0.U0WindowNormalization

open Complex Filter Topology Metric Set Polynomial Bottcher
open U0 U0NaturalBoundary U0WindowNormalization

namespace U0PhiLargeWindow

/-- The parameterized far field `{‖w‖ > ‖b‖ − 3/2}`. -/
def farB (b : ℂ) : Set ℂ := {w : ℂ | ‖b‖ - 3 / 2 < ‖w‖}

theorem isOpen_farB (b : ℂ) : IsOpen (farB b) := isOpen_lt continuous_const continuous_norm

theorem farB_ne_zero {b w : ℂ} (hb : 5 ≤ ‖b‖) (hw : w ∈ farB b) : w ≠ 0 := by
  intro h0
  have h1 : ‖b‖ - 3 / 2 < ‖w‖ := hw
  rw [h0] at h1
  simp at h1
  linarith

/-- One quadratic step grows the norm on `farB`. -/
theorem farB_invariant {b w : ℂ} (hb : 5 ≤ ‖b‖) (hw : w ∈ farB b) :
    quadratic b w ∈ farB b := by
  have h1 : ‖b‖ - 3 / 2 < ‖w‖ := hw
  show ‖b‖ - 3 / 2 < ‖w ^ 2 + b‖
  have htri : ‖w ^ 2‖ ≤ ‖w ^ 2 + b‖ + ‖b‖ := norm_le_add_norm_add _ _
  have hp : ‖w ^ 2‖ = ‖w‖ ^ 2 := norm_pow w 2
  nlinarith [h1, htri, hb, norm_nonneg w]

theorem farB_iterate {b : ℂ} (hb : 5 ≤ ‖b‖) (k : ℕ) {w : ℂ} (hw : w ∈ farB b) :
    (quadratic b)^[k] w ∈ farB b := by
  induction k with
  | zero => simpa using hw
  | succ m ih =>
    rw [Function.iterate_succ_apply']
    exact farB_invariant hb ih

/-- The series ratio is uniformly small on `farB`: `‖b/w²‖ ≤ 1/2`. -/
theorem farB_ratio_le {b w : ℂ} (hb : 5 ≤ ‖b‖) (hw : w ∈ farB b) :
    ‖b / w ^ 2‖ ≤ 1 / 2 := by
  have h1 : ‖b‖ - 3 / 2 < ‖w‖ := hw
  rw [norm_div, norm_pow]
  rw [div_le_iff₀ (by nlinarith [hb, h1])]
  nlinarith [h1, hb]

/-- Geometric term bound on the parameterized far field. -/
theorem norm_term_le_B {b w : ℂ} (hb : 5 ≤ ‖b‖) (hw : w ∈ farB b) (k : ℕ) :
    ‖bottcherLogTerm b w k‖ ≤ (1 / 2 : ℝ) ^ (k + 1) := by
  have hA : (quadratic b)^[k] w ∈ farB b := farB_iterate hb k hw
  have hq : ‖b / ((quadratic b)^[k] w) ^ 2‖ ≤ 1 / 2 := farB_ratio_le hb hA
  have hlog := norm_clog_one_add_le hq
  unfold bottcherLogTerm
  rw [norm_mul, norm_inv, norm_pow, Complex.norm_ofNat]
  calc ((2 : ℝ) ^ (k + 1))⁻¹ * ‖Complex.log (1 + b / ((quadratic b)^[k] w) ^ 2)‖
      ≤ ((2 : ℝ) ^ (k + 1))⁻¹ * (2 * (1 / 2)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        calc ‖Complex.log (1 + b / ((quadratic b)^[k] w) ^ 2)‖
            ≤ 2 * ‖b / ((quadratic b)^[k] w) ^ 2‖ := hlog
          _ ≤ 2 * (1 / 2) := by linarith
    _ = (1 / 2 : ℝ) ^ (k + 1) := by
        rw [one_div, inv_pow]
        norm_num

theorem summable_term_B {b w : ℂ} (hb : 5 ≤ ‖b‖) (hw : w ∈ farB b) :
    Summable (fun k => bottcherLogTerm b w k) := by
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => norm_term_le_B hb hw k)
  have h := summable_geometric_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
  exact (h.mul_left (1 / 2)).congr fun k => by ring

/-- The Böttcher log-series tail is differentiable on the parameterized far field. -/
theorem tail_differentiableOn_B {b : ℂ} (hb : 5 ≤ ‖b‖) :
    DifferentiableOn ℂ (fun w => ∑' k, bottcherLogTerm b w k) (farB b) := by
  have hqd : Differentiable ℂ (quadratic b) := by
    have : (quadratic b) = fun z => z ^ 2 + b := by
      funext z; exact quadratic_apply b z
    rw [this]
    exact (differentiable_pow 2).add_const b
  refine differentiableOn_tsum_of_summable_norm
    (u := fun k => (1 / 2 : ℝ) ^ (k + 1)) ?_ ?_ (isOpen_farB b) ?_
  · have hgeom : Summable (fun k : ℕ => (1 / 2 : ℝ) ^ k * (1 / 2)) :=
      (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_right _
    refine hgeom.congr fun k => ?_
    rw [← pow_succ]
  · intro k w hw
    apply DifferentiableAt.differentiableWithinAt
    have hA : (quadratic b)^[k] w ∈ farB b := farB_iterate hb k hw
    have hAne : ((quadratic b)^[k] w) ^ 2 ≠ 0 := pow_ne_zero 2 (farB_ne_zero hb hA)
    have hiter : DifferentiableAt ℂ ((quadratic b)^[k]) w := (hqd.iterate k).differentiableAt
    have hinner : DifferentiableAt ℂ (fun v => 1 + b / ((quadratic b)^[k] v) ^ 2) w := by
      have hdiv : DifferentiableAt ℂ (fun v => b / ((quadratic b)^[k] v) ^ 2) w :=
        (differentiableAt_const _).div (hiter.pow 2) hAne
      exact (differentiableAt_const (1 : ℂ)).add hdiv
    have hslit : (1 + b / ((quadratic b)^[k] w) ^ 2) ∈ slitPlane := by
      refine Or.inl ?_
      have hre : |(b / ((quadratic b)^[k] w) ^ 2).re|
          ≤ ‖b / ((quadratic b)^[k] w) ^ 2‖ := Complex.abs_re_le_norm _
      have hq := farB_ratio_le hb hA
      have : (1 + b / ((quadratic b)^[k] w) ^ 2).re
          = 1 + (b / ((quadratic b)^[k] w) ^ 2).re := by
        simp [Complex.add_re]
      rw [this]
      have habs := abs_le.mp hre
      linarith [habs.1]
    exact (hinner.clog hslit).const_mul _
  · intro k w hw
    exact norm_term_le_B hb hw k

/-! ## The parameterized branch -/

/-- **The window branch at parameter `b`**: the branch is rotated through `log b`, so it is
well defined for every complex `b` with `‖b‖ ≥ 5` — no slit-plane condition on `z² + b`. -/
noncomputable def phiB (b z : ℂ) : ℂ :=
  Complex.exp ((2 : ℂ)⁻¹ * (Complex.log b + Complex.log (1 + z ^ 2 / b)
    + ∑' k, bottcherLogTerm b (quadratic b z) k))

theorem phiB_ne_zero (b z : ℂ) : phiB b z ≠ 0 := Complex.exp_ne_zero _

theorem b_ne_zero {b : ℂ} (hb : 5 ≤ ‖b‖) : b ≠ 0 := by
  intro h0
  rw [h0] at hb
  simp at hb
  linarith

/-- On the window disk the normalized ratio stays in the right half-plane. -/
theorem ratio_re_ge {b z : ℂ} (hb : 5 ≤ ‖b‖) (hz : z ∈ ball (0 : ℂ) (21 / 20)) :
    (1 / 2 : ℝ) ≤ (1 + z ^ 2 / b).re := by
  have hz' : ‖z‖ < 21 / 20 := by simpa [mem_ball, dist_zero_right] using hz
  have hb0 : (0 : ℝ) < ‖b‖ := by linarith
  have hnorm : ‖z ^ 2 / b‖ ≤ 1 / 2 := by
    rw [norm_div, norm_pow, div_le_iff₀ hb0]
    nlinarith [hz', norm_nonneg z, hb]
  have hre : |(z ^ 2 / b).re| ≤ ‖z ^ 2 / b‖ := Complex.abs_re_le_norm _
  have habs := abs_le.mp (le_trans hre hnorm)
  have h1 : (1 + z ^ 2 / b).re = 1 + (z ^ 2 / b).re := by
    simp [Complex.add_re]
  rw [h1]
  linarith [habs.1]

theorem ratio_ne_zero {b z : ℂ} (hb : 5 ≤ ‖b‖) (hz : z ∈ ball (0 : ℂ) (21 / 20)) :
    (1 : ℂ) + z ^ 2 / b ≠ 0 := by
  intro h0
  have := ratio_re_ge hb hz
  rw [h0] at this
  simp at this
  linarith

theorem ratio_mem_slitPlane {b z : ℂ} (hb : 5 ≤ ‖b‖) (hz : z ∈ ball (0 : ℂ) (21 / 20)) :
    (1 : ℂ) + z ^ 2 / b ∈ slitPlane := by
  refine Or.inl ?_
  have := ratio_re_ge hb hz
  linarith

/-- One quadratic step from the disk lands in the parameterized far field. -/
theorem quadB_mem_farB {b z : ℂ} (_hb : 5 ≤ ‖b‖) (hz : z ∈ ball (0 : ℂ) (21 / 20)) :
    quadratic b z ∈ farB b := by
  have hz' : ‖z‖ < 21 / 20 := by simpa [mem_ball, dist_zero_right] using hz
  show ‖b‖ - 3 / 2 < ‖z ^ 2 + b‖
  have htri : ‖b‖ ≤ ‖z ^ 2 + b‖ + ‖z ^ 2‖ := by
    calc ‖b‖ = ‖z ^ 2 + b - z ^ 2‖ := by ring_nf
      _ ≤ ‖z ^ 2 + b‖ + ‖z ^ 2‖ := norm_sub_le _ _
  have hp : ‖z ^ 2‖ = ‖z‖ ^ 2 := norm_pow z 2
  nlinarith [htri, hz', norm_nonneg z]

theorem quadB_ne_zero {b z : ℂ} (hb : 5 ≤ ‖b‖) (hz : z ∈ ball (0 : ℂ) (21 / 20)) :
    z ^ 2 + b ≠ 0 := by
  have hfar : quadratic b z ∈ farB b := quadB_mem_farB hb hz
  have := farB_ne_zero hb hfar
  simpa [quadratic_apply] using this

/-- The branch squares to the genuine Böttcher coordinate one step ahead — branch-free at the
`exp` level, for every `‖b‖ ≥ 5`. -/
theorem phiB_sq {b z : ℂ} (hb : 5 ≤ ‖b‖) (hz : z ∈ ball (0 : ℂ) (21 / 20)) :
    phiB b z ^ 2 = bottcherCoord b (quadratic b z) := by
  have hb0 : b ≠ 0 := b_ne_zero hb
  have hrne : (1 : ℂ) + z ^ 2 / b ≠ 0 := ratio_ne_zero hb hz
  have hzsq : z ^ 2 + b ≠ 0 := quadB_ne_zero hb hz
  have hδ : Complex.exp (Complex.log b + Complex.log (1 + z ^ 2 / b)
      - Complex.log (z ^ 2 + b)) = 1 := by
    rw [Complex.exp_sub, Complex.exp_add, Complex.exp_log hb0, Complex.exp_log hrne,
      Complex.exp_log hzsq]
    rw [div_eq_one_iff_eq hzsq]
    field_simp
    ring
  have hqz : quadratic b z = z ^ 2 + b := rfl
  unfold phiB bottcherCoord bottcherLog
  rw [pow_two, ← Complex.exp_add]
  calc Complex.exp ((2 : ℂ)⁻¹ * (Complex.log b + Complex.log (1 + z ^ 2 / b)
        + ∑' k, bottcherLogTerm b (quadratic b z) k)
      + (2 : ℂ)⁻¹ * (Complex.log b + Complex.log (1 + z ^ 2 / b)
        + ∑' k, bottcherLogTerm b (quadratic b z) k))
      = Complex.exp ((Complex.log (quadratic b z)
          + ∑' k, bottcherLogTerm b (quadratic b z) k)
        + (Complex.log b + Complex.log (1 + z ^ 2 / b) - Complex.log (z ^ 2 + b))) := by
        rw [hqz]
        congr 1
        ring
    _ = Complex.exp (Complex.log (quadratic b z)
          + ∑' k, bottcherLogTerm b (quadratic b z) k)
        * Complex.exp (Complex.log b + Complex.log (1 + z ^ 2 / b)
          - Complex.log (z ^ 2 + b)) := Complex.exp_add _ _
    _ = Complex.exp (Complex.log (quadratic b z)
          + ∑' k, bottcherLogTerm b (quadratic b z) k) := by
        rw [hδ, mul_one]

/-- **`phiB b` is analytic on the whole disk `ball 0 (21/20)` — across the unit circle.** -/
theorem phiB_analytic {b : ℂ} (hb : 5 ≤ ‖b‖) :
    AnalyticOnNhd ℂ (phiB b) (ball (0 : ℂ) (21 / 20)) := by
  apply DifferentiableOn.analyticOnNhd _ isOpen_ball
  intro z hz
  apply DifferentiableAt.differentiableWithinAt
  have hqd : DifferentiableAt ℂ (quadratic b) z := by
    have : (quadratic b) = fun v => v ^ 2 + b := by
      funext v; exact quadratic_apply b v
    rw [this]
    exact ((differentiable_pow 2).add_const b).differentiableAt
  have hratio : DifferentiableAt ℂ (fun v => Complex.log (1 + v ^ 2 / b)) z := by
    have hin : DifferentiableAt ℂ (fun v : ℂ => 1 + v ^ 2 / b) z := by
      have : DifferentiableAt ℂ (fun v : ℂ => v ^ 2 / b) z :=
        (differentiableAt_pow 2).div_const b
      exact (differentiableAt_const (1 : ℂ)).add this
    exact hin.clog (ratio_mem_slitPlane hb hz)
  have htail : DifferentiableAt ℂ (fun v => ∑' k, bottcherLogTerm b (quadratic b v) k) z := by
    have hT : DifferentiableAt ℂ (fun w => ∑' k, bottcherLogTerm b w k) (quadratic b z) :=
      (tail_differentiableOn_B hb).differentiableAt
        ((isOpen_farB b).mem_nhds (quadB_mem_farB hb hz))
    exact hT.comp z hqd
  have hsum : DifferentiableAt ℂ (fun v => Complex.log b + Complex.log (1 + v ^ 2 / b)
      + ∑' k, bottcherLogTerm b (quadratic b v) k) z :=
    ((differentiableAt_const _).add hratio).add htail
  exact (hsum.const_mul _).cexp

/-! ## The functional equation and escape growth on the far field -/

/-- **The Böttcher functional equation on the parameterized far field** — branch-free at the
`exp` level: `φ(z² + b) = φ(z)²` for every `‖z‖ > ‖b‖ − 3/2`. -/
theorem bottcherCoord_quadratic_farB {b z : ℂ} (hb : 5 ≤ ‖b‖) (hz : z ∈ farB b) :
    bottcherCoord b (quadratic b z) = (bottcherCoord b z) ^ 2 := by
  have hz0 : z ≠ 0 := farB_ne_zero hb hz
  have hz2 : ‖b‖ - 3 / 2 < ‖z‖ := hz
  have hzsq : z ^ 2 + b ≠ 0 := by
    have hfar : quadratic b z ∈ farB b := farB_invariant hb hz
    have := farB_ne_zero hb hfar
    simpa [quadratic_apply] using this
  have hratio : (1 : ℂ) + b / z ^ 2 ≠ 0 := by
    intro h0
    have h1 : ‖b / z ^ 2‖ = 1 := by
      rw [show b / z ^ 2 = -1 from by linear_combination h0]
      simp
    have h2 := farB_ratio_le hb hz
    rw [h1] at h2
    linarith
  have hshift : ∀ k, bottcherLogTerm b (quadratic b z) k = 2 * bottcherLogTerm b z (k + 1) := by
    intro k
    unfold bottcherLogTerm
    have hiter : (quadratic b)^[k] (quadratic b z) = (quadratic b)^[k + 1] z := by
      rw [Function.iterate_succ_apply]
    rw [hiter]
    have h2 : ((2 : ℂ) ^ (k + 1 + 1))⁻¹ * 2 = ((2 : ℂ) ^ (k + 1))⁻¹ := by
      rw [pow_succ]
      field_simp
    rw [← h2]
    ring
  have hsum : ∑' k, bottcherLogTerm b (quadratic b z) k
      = 2 * (∑' k, bottcherLogTerm b z k) - 2 * bottcherLogTerm b z 0 := by
    have hsummable := summable_term_B hb hz
    have h1 : ∑' k, bottcherLogTerm b (quadratic b z) k
        = ∑' k, 2 * bottcherLogTerm b z (k + 1) := tsum_congr hshift
    rw [h1, tsum_mul_left]
    have h2 : ∑' k, bottcherLogTerm b z (k + 1)
        = (∑' k, bottcherLogTerm b z k) - bottcherLogTerm b z 0 := by
      have := hsummable.tsum_eq_zero_add
      linear_combination -this
    rw [h2]
    ring
  unfold bottcherCoord bottcherLog
  rw [hsum]
  have hterm0 : bottcherLogTerm b z 0 = (2 : ℂ)⁻¹ * Complex.log (1 + b / z ^ 2) := by
    unfold bottcherLogTerm
    simp
  rw [hterm0]
  have hqz : quadratic b z = z ^ 2 + b := rfl
  have hδ : Complex.exp (Complex.log (z ^ 2 + b) - Complex.log (1 + b / z ^ 2)
      - 2 * Complex.log z) = 1 := by
    rw [sub_sub, Complex.exp_sub, Complex.exp_add, Complex.exp_log hzsq,
      Complex.exp_log hratio]
    rw [show (2 : ℂ) * Complex.log z = Complex.log z + Complex.log z from by ring,
      Complex.exp_add, Complex.exp_log hz0]
    rw [div_eq_one_iff_eq (by
      intro h0
      rcases mul_eq_zero.mp h0 with h1 | h1
      · exact hratio h1
      · exact hz0 (by rcases mul_eq_zero.mp h1 with h2 | h2 <;> exact h2))]
    field_simp
  calc Complex.exp (Complex.log (quadratic b z)
        + (2 * (∑' k, bottcherLogTerm b z k) - 2 * ((2 : ℂ)⁻¹
            * Complex.log (1 + b / z ^ 2))))
      = Complex.exp ((2 : ℂ) * (Complex.log z + ∑' k, bottcherLogTerm b z k)
          + (Complex.log (z ^ 2 + b) - Complex.log (1 + b / z ^ 2)
            - 2 * Complex.log z)) := by
        rw [hqz]
        congr 1
        ring
    _ = Complex.exp ((2 : ℂ) * (Complex.log z + ∑' k, bottcherLogTerm b z k))
          * Complex.exp (Complex.log (z ^ 2 + b) - Complex.log (1 + b / z ^ 2)
            - 2 * Complex.log z) := Complex.exp_add _ _
    _ = Complex.exp ((2 : ℂ) * (Complex.log z + ∑' k, bottcherLogTerm b z k)) := by
        rw [hδ, mul_one]
    _ = Complex.exp (Complex.log z + ∑' k, bottcherLogTerm b z k) ^ 2 := by
        rw [pow_two, ← Complex.exp_add]
        congr 1
        ring

/-- **Escape growth on the parameterized far field**: factor `3/2` per quadratic step. -/
theorem farB_growth {b : ℂ} (hb : 5 ≤ ‖b‖) (m : ℕ) {w : ℂ} (hw : w ∈ farB b) :
    (3 / 2 : ℝ) ^ m * ‖w‖ ≤ ‖(quadratic b)^[m] w‖ := by
  induction m with
  | zero =>
    simp
  | succ m ihm =>
    have hmem : (quadratic b)^[m] w ∈ farB b := farB_iterate hb m hw
    have hx : ‖b‖ - 3 / 2 < ‖(quadratic b)^[m] w‖ := hmem
    have hstep : (3 / 2 : ℝ) * ‖(quadratic b)^[m] w‖ ≤ ‖(quadratic b)^[m + 1] w‖ := by
      rw [Function.iterate_succ_apply']
      have hq : quadratic b ((quadratic b)^[m] w)
          = ((quadratic b)^[m] w) ^ 2 + b := rfl
      rw [hq]
      have h1 : ‖((quadratic b)^[m] w) ^ 2‖ ≤ ‖((quadratic b)^[m] w) ^ 2 + b‖ + ‖b‖ :=
        norm_le_add_norm_add _ _
      rw [norm_pow] at h1
      nlinarith [hx, hb]
    calc (3 / 2 : ℝ) ^ (m + 1) * ‖w‖ = (3 / 2) * ((3 / 2 : ℝ) ^ m * ‖w‖) := by ring
      _ ≤ (3 / 2) * ‖(quadratic b)^[m] w‖ := by nlinarith [ihm]
      _ ≤ ‖(quadratic b)^[m + 1] w‖ := hstep

/-- **The dyadic pullback chain at parameter `b`**: on the window,
`phiB^(2^(m+1))` is the genuine Böttcher coordinate `m + 1` quadratic steps ahead. -/
theorem phiB_pow_iterate {b z : ℂ} (hb : 5 ≤ ‖b‖) (hz : z ∈ Metric.ball (0 : ℂ) (21 / 20))
    (m : ℕ) :
    phiB b z ^ (2 ^ (m + 1)) = bottcherCoord b ((quadratic b)^[m] (quadratic b z)) := by
  induction m with
  | zero =>
    simpa using phiB_sq hb hz
  | succ m ihm =>
    have hmem : (quadratic b)^[m] (quadratic b z) ∈ farB b :=
      farB_iterate hb m (quadB_mem_farB hb hz)
    have hpow : phiB b z ^ (2 ^ (m + 1 + 1)) = (phiB b z ^ (2 ^ (m + 1))) ^ 2 := by
      rw [← pow_mul, ← pow_succ]
    rw [hpow, ihm, Function.iterate_succ_apply', bottcherCoord_quadratic_farB hb hmem]

/-! ## The window engine instance at parameter `b` -/

/-- **`u₀ ⟂ phiB b`, separability-free, for every `‖b‖ ≥ 5`.**  A polynomial relation
`P(z, phiB b z, u₀ z) = 0` on a nonempty open subset of the annulus `{1 < ‖z‖ < 21/20}` with some
positive-index coefficient not identically zero is impossible.  The natural-boundary window engine
is φ-generic; only the constructed branch was parameter-specific. -/
theorem u0_phiB_no_relation_nondegenerate {b : ℂ} (hb : 5 ≤ ‖b‖)
    (P : (Polynomial (Polynomial ℂ))[X]) {i₀ : ℕ} (hi₀ : 1 ≤ i₀)
    (hnondeg : ∃ z ∈ Metric.ball (0 : ℂ) (21 / 20) ∩ Ext,
      coeffFun (phiB b) (P.coeff i₀) z ≠ 0)
    {V : Set ℂ} (hVo : IsOpen V) (hVne : V.Nonempty)
    (hVD : V ⊆ Metric.ball (0 : ℂ) (21 / 20) ∩ Ext)
    (hrel : ∀ z ∈ V, P.eval₂ (eval₂RingHom (evalRingHom z) (phiB b z)) (u0 z) = 0) :
    False := by
  refine u0_windowed_no_relation_nondegenerate isOpen_ball
    ((convex_ball (0 : ℂ) (21 / 20)).isPreconnected) U0PhiFourWindow.isPreconnected_annulus
    (phiB_analytic hb) (z₁ := 1) ?_ ?_ P hi₀ hnondeg hVo hVne hVD hrel
  · show (1 : ℂ) ∈ Metric.ball (0 : ℂ) (21 / 20)
    simp only [Metric.mem_ball, dist_zero_right, norm_one]
    norm_num
  · simp

end U0PhiLargeWindow
