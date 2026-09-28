import GaloisForLFunctions.RHTower.ThetaSourceTailDerivativeModeration
import GaloisForLFunctions.HTGeometry.SmoothWeight

/-!
# Logarithmic interpolation between the theta source and a derivative packet

With an even smooth window `χ_R` (`1` on `[-R, R]`, `0` outside `(-R-1, R+1)`, derivatives bounded
uniformly in `R`) put `b_R = exp((1-χ_R) log k + χ_R log k_t) = k e^{χ_R L}`,
`L = log k_t - log k`. Then `b_R = k_t` near `[-R, R]`, `b_R = k` outside `(-R-1, R+1)`, and
`(log b_R)'' = (1-χ)(log k)'' + χ(log k_t)'' + 2χ'L' + χ''L`. On the tail both curvatures are
`-4π e^{2x} + O(1)` while `L' = O(1)` and `L = o(e^{2x})`, so for all large `R` the interpolant is
globally strongly log-concave whenever `k_t` is. Outside `(-R, R)` it lies between `k` and `k_t`.
-/
open Filter Topology Set
open scoped ContDiff
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-! ## An even smooth window -/

/-- The even window `χ_R`: `1` on `[-R, R]`, `0` outside `(-R-1, R+1)`, with values in `[0,1]`. -/
def thetaTailWindow (R x : ℝ) : ℝ := smoothWeight R 1 x * smoothWeight R 1 (-x)

theorem contDiff_smoothWeight_top (R : ℝ) : ContDiff ℝ ∞ (smoothWeight R 1) :=
  smoothWeight_contDiff R 1 (n := ⊤)

theorem contDiff_thetaTailWindow (R : ℝ) : ContDiff ℝ ∞ (thetaTailWindow R) :=
  (contDiff_smoothWeight_top R).mul ((contDiff_smoothWeight_top R).comp contDiff_neg)

theorem thetaTailWindow_neg (R x : ℝ) : thetaTailWindow R (-x) = thetaTailWindow R x := by
  unfold thetaTailWindow
  rw [neg_neg, mul_comm]

theorem thetaTailWindow_nonneg (R x : ℝ) : 0 ≤ thetaTailWindow R x :=
  mul_nonneg (smoothWeight_nonneg R 1 x) (smoothWeight_nonneg R 1 (-x))

theorem thetaTailWindow_le_one (R x : ℝ) : thetaTailWindow R x ≤ 1 :=
  mul_le_one₀ (smoothWeight_le_one R 1 x) (smoothWeight_nonneg R 1 (-x))
    (smoothWeight_le_one R 1 (-x))

theorem thetaTailWindow_eq_zero {R x : ℝ} (hx : R + 1 ≤ |x|) : thetaTailWindow R x = 0 := by
  unfold thetaTailWindow
  rcases le_or_gt 0 x with h | h
  · rw [abs_of_nonneg h] at hx
    rw [smoothWeight_eq_zero one_pos hx, zero_mul]
  · rw [abs_of_neg h] at hx
    rw [smoothWeight_eq_zero one_pos hx, mul_zero]

theorem thetaTailWindow_eventuallyEq_one {R x : ℝ} (hx : |x| < R) :
    thetaTailWindow R =ᶠ[𝓝 x] fun _ => 1 := by
  have hopen : IsOpen {y : ℝ | |y| < R} := isOpen_lt continuous_abs continuous_const
  filter_upwards [hopen.mem_nhds hx] with y hy
  have hy' : |y| < R := hy
  unfold thetaTailWindow
  rw [smoothWeight_eq_one one_pos (by linarith [le_abs_self y]),
    smoothWeight_eq_one one_pos (by linarith [neg_abs_le y]), one_mul]

theorem thetaTailWindow_eventuallyEq_zero {R x : ℝ} (hx : R + 1 < |x|) :
    thetaTailWindow R =ᶠ[𝓝 x] fun _ => 0 := by
  have hopen : IsOpen {y : ℝ | R + 1 < |y|} := isOpen_lt continuous_const continuous_abs
  filter_upwards [hopen.mem_nhds hx] with y hy
  exact thetaTailWindow_eq_zero (le_of_lt hy)

/-- Every derivative of the window is bounded uniformly in the position `R > 0`. -/
theorem exists_bound_iteratedDeriv_thetaTailWindow (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R → ∀ x : ℝ, |iteratedDeriv j (thetaTailWindow R) x| ≤ C := by
  obtain ⟨C, hC, hbd⟩ := exists_bound_iteratedDeriv_smoothWeight_uniform j
  refine ⟨C, hC, fun R hR x => ?_⟩
  have hb : ∀ y, |iteratedDeriv j (smoothWeight R 1) y| ≤ C := fun y => by
    simpa using hbd R 1 one_pos y
  rcases le_or_gt 0 x with hx | hx
  · have heq : thetaTailWindow R =ᶠ[𝓝 x] smoothWeight R 1 := by
      filter_upwards [Ioi_mem_nhds (show -R < x by linarith)] with y hy
      unfold thetaTailWindow
      rw [smoothWeight_eq_one one_pos (by linarith [mem_Ioi.1 hy] : -y ≤ R), mul_one]
    rw [heq.iteratedDeriv_eq]
    exact hb x
  · have heq : thetaTailWindow R =ᶠ[𝓝 x] fun y => smoothWeight R 1 (-y) := by
      filter_upwards [Iio_mem_nhds (show x < R by linarith)] with y hy
      unfold thetaTailWindow
      rw [smoothWeight_eq_one one_pos (le_of_lt (mem_Iio.1 hy)), one_mul]
    rw [heq.iteratedDeriv_eq, iteratedDeriv_comp_neg, smul_eq_mul, abs_mul, abs_pow, abs_neg,
      abs_one, one_pow, one_mul]
    exact hb (-x)

/-! ## The logarithmic interpolation between `k` and `k_t` -/

/-- `b_R = exp((1-χ_R) log k + χ_R log k_t) = k exp(χ_R L)`. -/
def thetaTailInterpolant (m : ℕ) (t R x : ℝ) : ℝ :=
  thetaCuspFullSource x * Real.exp (thetaTailWindow R x * thetaPacketLogRatio m t x)

section Interpolant

variable {m : ℕ} {t : ℝ} (hpos : ∀ x, 0 < thetaDerivativePacket m t x)
include hpos

theorem thetaCuspFullSource_mul_exp_thetaPacketLogRatio (x : ℝ) :
    thetaCuspFullSource x * Real.exp (thetaPacketLogRatio m t x) = thetaDerivativePacket m t x := by
  unfold thetaPacketLogRatio
  rw [Real.exp_sub, Real.exp_log (hpos x), Real.exp_log (thetaCuspFullSource_pos_all x)]
  field_simp [(thetaCuspFullSource_pos_all x).ne']

omit hpos in
theorem thetaTailInterpolant_pos (R x : ℝ) : 0 < thetaTailInterpolant m t R x :=
  mul_pos (thetaCuspFullSource_pos_all x) (Real.exp_pos _)

omit hpos in
theorem thetaPacketLogRatio_neg (x : ℝ) : thetaPacketLogRatio m t (-x) = thetaPacketLogRatio m t x := by
  unfold thetaPacketLogRatio
  rw [thetaDerivativePacket_neg, thetaCuspFullSource_neg]

omit hpos in
theorem thetaTailInterpolant_neg (R x : ℝ) :
    thetaTailInterpolant m t R (-x) = thetaTailInterpolant m t R x := by
  unfold thetaTailInterpolant
  rw [thetaCuspFullSource_neg, thetaTailWindow_neg, thetaPacketLogRatio_neg]

theorem contDiff_thetaTailInterpolant (R : ℝ) : ContDiff ℝ ∞ (thetaTailInterpolant m t R) :=
  contDiff_thetaCuspFullSource.mul
    (((contDiff_thetaTailWindow R).mul (contDiff_thetaPacketLogRatio m t hpos)).exp)

omit hpos in
theorem log_thetaTailInterpolant (R x : ℝ) :
    Real.log (thetaTailInterpolant m t R x) =
      Real.log (thetaCuspFullSource x) + thetaTailWindow R x * thetaPacketLogRatio m t x := by
  unfold thetaTailInterpolant
  rw [Real.log_mul (thetaCuspFullSource_pos_all x).ne' (Real.exp_pos _).ne', Real.log_exp]

theorem thetaTailInterpolant_eq_mul_exp (R x : ℝ) :
    thetaTailInterpolant m t R x = thetaDerivativePacket m t x *
      Real.exp ((thetaTailWindow R x - 1) * thetaPacketLogRatio m t x) := by
  rw [← thetaCuspFullSource_mul_exp_thetaPacketLogRatio hpos x, mul_assoc, ← Real.exp_add]
  unfold thetaTailInterpolant
  congr 2
  ring

theorem thetaTailInterpolant_eventuallyEq_packet {R x : ℝ} (hx : |x| < R) :
    thetaTailInterpolant m t R =ᶠ[𝓝 x] thetaDerivativePacket m t := by
  filter_upwards [thetaTailWindow_eventuallyEq_one hx] with y hy
  rw [thetaTailInterpolant_eq_mul_exp hpos, hy, sub_self, zero_mul, Real.exp_zero, mul_one]

omit hpos in
theorem thetaTailInterpolant_eq_source {R x : ℝ} (hx : R + 1 ≤ |x|) :
    thetaTailInterpolant m t R x = thetaCuspFullSource x := by
  unfold thetaTailInterpolant
  rw [thetaTailWindow_eq_zero hx, zero_mul, Real.exp_zero, mul_one]

/-- The second logarithmic derivative of the interpolant:
`(log b)'' = (1-χ)(log k)'' + χ (log k_t)'' + 2χ'L' + χ''L`. -/
theorem iteratedDeriv_two_log_thetaTailInterpolant (R x : ℝ) :
    iteratedDeriv 2 (fun y => Real.log (thetaTailInterpolant m t R y)) x =
      (1 - thetaTailWindow R x) * iteratedDeriv 2 (fun y => Real.log (thetaCuspFullSource y)) x +
        thetaTailWindow R x *
          iteratedDeriv 2 (fun y => Real.log (thetaDerivativePacket m t y)) x +
        2 * iteratedDeriv 1 (thetaTailWindow R) x * iteratedDeriv 1 (thetaPacketLogRatio m t) x +
        iteratedDeriv 2 (thetaTailWindow R) x * thetaPacketLogRatio m t x := by
  have hlk : ContDiff ℝ ∞ (fun y => Real.log (thetaCuspFullSource y)) :=
    contDiff_thetaCuspFullSource.log fun x => (thetaCuspFullSource_pos_all x).ne'
  have hlkt : ContDiff ℝ ∞ (fun y => Real.log (thetaDerivativePacket m t y)) :=
    (contDiff_thetaDerivativePacket m t).log fun x => (hpos x).ne'
  have hχ := contDiff_thetaTailWindow R
  have hL := contDiff_thetaPacketLogRatio m t hpos
  have hfun : (fun y => Real.log (thetaTailInterpolant m t R y)) =
      (fun y => Real.log (thetaCuspFullSource y)) + (thetaTailWindow R * thetaPacketLogRatio m t) := by
    funext y
    rw [log_thetaTailInterpolant]
    rfl
  rw [hfun, iteratedDeriv_add (f := fun y => Real.log (thetaCuspFullSource y))
    (g := thetaTailWindow R * thetaPacketLogRatio m t)
    (hlk.contDiffAt.of_le (by norm_cast))
    ((hχ.mul hL).contDiffAt.of_le (by norm_cast)),
    iteratedDeriv_mul (hχ.contDiffAt.of_le (by norm_cast))
      (hL.contDiffAt.of_le (by norm_cast))]
  have hL2 : iteratedDeriv 2 (thetaPacketLogRatio m t) x =
      iteratedDeriv 2 (fun y => Real.log (thetaDerivativePacket m t y)) x -
        iteratedDeriv 2 (fun y => Real.log (thetaCuspFullSource y)) x :=
    iteratedDeriv_sub (hlkt.contDiffAt.of_le (by norm_cast))
      (hlk.contDiffAt.of_le (by norm_cast))
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.choose_zero_right,
    Nat.choose_one_right, Nat.choose_self, iteratedDeriv_zero, Nat.sub_zero,
    show (2 - 1 : ℕ) = 1 by norm_num, Nat.sub_self]
  rw [hL2]
  push_cast
  ring

/-- **Global strong log-concavity of the interpolant.** If `(log k_t)'' ≤ -δ` on `ℝ`, then for all
large `R`, `(log b_R)'' ≤ -min 1 δ` on `ℝ`: inside `(-R, R)` it equals `k_t`, while on the tail
the curvature `-4π e^{2x}` dominates the window terms `2χ'L' + χ''L`. -/
theorem exists_thetaTailInterpolant_stronglyLogConcave (hm : 0 < m) (ht : 0 ≤ t) {δ : ℝ}
    (hδ : ∀ x, iteratedDeriv 2 (fun y => Real.log (thetaDerivativePacket m t y)) x ≤ -δ) :
    ∃ R₀ > 0, ∀ R ≥ R₀, ∀ x,
      iteratedDeriv 2 (fun y => Real.log (thetaTailInterpolant m t R y)) x ≤ -min 1 δ := by
  obtain ⟨C₁, hC₁, hb₁⟩ := exists_bound_iteratedDeriv_thetaTailWindow 1
  obtain ⟨C₂, hC₂, hb₂⟩ := exists_bound_iteratedDeriv_thetaTailWindow 2
  set c₂ : ℝ := (2 * (4 * m : ℕ) : ℝ) ^ 2 + 2
  set c₃ : ℝ := c₂ + 2 * C₁ * (2 * (4 * m : ℕ) + 1)
  have hq := tendsto_thetaTailScale.eventually_ge_atTop ((c₃ + 1) / 3)
  have hLq := eventually_thetaPacketLogRatio_le_mul_scale m hm ht hpos
    (ε := 1 / (C₂ + 1)) (by positivity)
  have htail : ∀ᶠ x in atTop,
      iteratedDeriv 2 (fun y => Real.log (thetaCuspFullSource y)) x ≤
        -4 * thetaCuspSingleAtomReflectionScale 1 x + 1 ∧
      iteratedDeriv 2 (fun y => Real.log (thetaDerivativePacket m t y)) x ≤
        -4 * thetaCuspSingleAtomReflectionScale 1 x + c₂ ∧
      |iteratedDeriv 1 (thetaPacketLogRatio m t) x| ≤ 2 * (4 * m : ℕ) + 1 ∧
      0 ≤ thetaPacketLogRatio m t x ∧
      thetaPacketLogRatio m t x ≤ 1 / (C₂ + 1) * thetaCuspSingleAtomReflectionScale 1 x ∧
      (c₃ + 1) / 3 ≤ thetaCuspSingleAtomReflectionScale 1 x := by
    filter_upwards [eventually_iteratedDeriv_two_log_thetaCuspFullSource_le,
      eventually_thetaDerivativePacketNumerator_le_scale m hm,
      eventually_abs_deriv_thetaPacketLogRatio_le m hm ht hpos,
      eventually_thetaPacketLogRatio_nonneg m hm ht, hLq, hq] with x h1 h2 h3 h4 h5 h6
    refine ⟨h1, ?_, h3, h4, h5, h6⟩
    rw [iteratedDeriv_two_log_thetaDerivativePacket m t hpos, div_le_iff₀ (by positivity [hpos x])]
    exact h2 t ht
  obtain ⟨X, hX⟩ := eventually_atTop.1 htail
  refine ⟨max X 0 + 1, by positivity, fun R hR x => ?_⟩
  have hR0 : 0 < R := by linarith [le_max_right X 0]
  -- the tail estimate, valid for every `x ≥ X`
  have hbound : ∀ y, X ≤ y →
      iteratedDeriv 2 (fun z => Real.log (thetaTailInterpolant m t R z)) y ≤ -1 := by
    intro y hy
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hX y hy
    rw [iteratedDeriv_two_log_thetaTailInterpolant hpos]
    set q := thetaCuspSingleAtomReflectionScale 1 y
    set χ := thetaTailWindow R y
    have hχ0 := thetaTailWindow_nonneg R y
    have hχ1 := thetaTailWindow_le_one R y
    have hc₂ : 1 ≤ c₂ := by simp only [c₂]; nlinarith [sq_nonneg ((2 * (4 * m : ℕ) : ℝ))]
    have hmix : (1 - χ) * iteratedDeriv 2 (fun y => Real.log (thetaCuspFullSource y)) y +
        χ * iteratedDeriv 2 (fun y => Real.log (thetaDerivativePacket m t y)) y ≤ -4 * q + c₂ := by
      have e1 := mul_le_mul_of_nonneg_left h1 (by linarith : 0 ≤ 1 - χ)
      have e2 := mul_le_mul_of_nonneg_left h2 hχ0
      nlinarith
    have hw1 : 2 * iteratedDeriv 1 (thetaTailWindow R) y * iteratedDeriv 1 (thetaPacketLogRatio m t) y ≤
        2 * C₁ * (2 * (4 * m : ℕ) + 1) := by
      have := abs_mul (iteratedDeriv 1 (thetaTailWindow R) y) (iteratedDeriv 1 (thetaPacketLogRatio m t) y)
      have hp := mul_le_mul (hb₁ R hR0 y) h3 (abs_nonneg _) hC₁
      have := le_abs_self (iteratedDeriv 1 (thetaTailWindow R) y * iteratedDeriv 1 (thetaPacketLogRatio m t) y)
      nlinarith
    have hw2 : iteratedDeriv 2 (thetaTailWindow R) y * thetaPacketLogRatio m t y ≤ q := by
      have hle : iteratedDeriv 2 (thetaTailWindow R) y ≤ C₂ := (le_abs_self _).trans (hb₂ R hR0 y)
      have e1 : iteratedDeriv 2 (thetaTailWindow R) y * thetaPacketLogRatio m t y ≤
          C₂ * thetaPacketLogRatio m t y := mul_le_mul_of_nonneg_right hle h4
      have e2 : C₂ * thetaPacketLogRatio m t y ≤ C₂ * (1 / (C₂ + 1) * q) :=
        mul_le_mul_of_nonneg_left h5 hC₂
      have e3 : C₂ * (1 / (C₂ + 1) * q) ≤ q := by
        have hq0 : 0 ≤ q := (thetaTailScale_pos y).le
        rw [← mul_assoc, mul_one_div]
        exact mul_le_of_le_one_left hq0 ((div_le_one (by positivity)).2 (by linarith))
      linarith
    have : -4 * q + c₂ + 2 * C₁ * (2 * (4 * m : ℕ) + 1) + q ≤ -1 := by
      simp only [c₃] at h6; linarith
    linarith
  rcases lt_or_ge |x| R with hx | hx
  · -- inside the window the interpolant is `k_t`
    have heq : (fun y => Real.log (thetaTailInterpolant m t R y)) =ᶠ[𝓝 x]
        fun y => Real.log (thetaDerivativePacket m t y) :=
      (thetaTailInterpolant_eventuallyEq_packet hpos hx).mono fun y hy => by simp only [hy]
    rw [heq.iteratedDeriv_eq]
    exact (hδ x).trans (neg_le_neg (min_le_right _ _))
  · have hXR : X ≤ R := by linarith [le_max_left X 0]
    rcases le_or_gt 0 x with hx0 | hx0
    · rw [abs_of_nonneg hx0] at hx
      exact (hbound x (hXR.trans hx)).trans (neg_le_neg (min_le_left _ _))
    · rw [abs_of_neg hx0] at hx
      have heven : (fun y => Real.log (thetaTailInterpolant m t R y)) =
          fun y => (fun z => Real.log (thetaTailInterpolant m t R z)) (-y) := by
        funext y; simp only [thetaTailInterpolant_neg]
      have hsym : iteratedDeriv 2 (fun y => Real.log (thetaTailInterpolant m t R y)) x =
          iteratedDeriv 2 (fun y => Real.log (thetaTailInterpolant m t R y)) (-x) := by
        conv_lhs => rw [heven]
        rw [iteratedDeriv_comp_neg 2 (fun z => Real.log (thetaTailInterpolant m t R z)) x,
          smul_eq_mul]
        norm_num
      rw [hsym]
      exact (hbound (-x) (hXR.trans hx)).trans (neg_le_neg (min_le_left _ _))

/-- Outside `(-R, R)` the interpolant lies between `k` and `k_t` once `R` is large; hence
`|b_R - k_t| ≤ k_t` there, and `b_R = k_t` inside. -/
theorem eventually_abs_thetaTailInterpolant_sub_le (hm : 0 < m) (ht : 0 ≤ t) :
    ∃ X, ∀ R ≥ X, ∀ x, |thetaTailInterpolant m t R x - thetaDerivativePacket m t x| ≤
      if R ≤ |x| then thetaDerivativePacket m t x else 0 := by
  obtain ⟨X, hX⟩ := eventually_atTop.1 (eventually_thetaPacketLogRatio_nonneg m hm ht)
  refine ⟨max X 0, fun R hR x => ?_⟩
  split_ifs with hx
  · have hL : 0 ≤ thetaPacketLogRatio m t x := by
      rcases le_or_gt 0 x with h | h
      · exact hX x (by rw [abs_of_nonneg h] at hx; linarith [le_max_left X 0])
      · rw [← thetaPacketLogRatio_neg]
        exact hX (-x) (by rw [abs_of_neg h] at hx; linarith [le_max_left X 0])
    rw [thetaTailInterpolant_eq_mul_exp hpos]
    have he1 : Real.exp ((thetaTailWindow R x - 1) * thetaPacketLogRatio m t x) ≤ 1 :=
      Real.exp_le_one_iff.2 (mul_nonpos_of_nonpos_of_nonneg (by linarith [thetaTailWindow_le_one R x]) hL)
    have he0 := Real.exp_pos ((thetaTailWindow R x - 1) * thetaPacketLogRatio m t x)
    have hk := hpos x
    rw [abs_le]
    constructor <;> nlinarith
  · have hx' : |x| < R := lt_of_not_ge hx
    rw [(thetaTailInterpolant_eventuallyEq_packet hpos hx').self_of_nhds, sub_self, abs_zero]

end Interpolant

end

end RHTower
