import GaloisForLFunctions.RHTower.ModularArcTwoScaleHyperbolicWitness

/-!
# Quadratic strip-edge vanishing and double-pole cancellation for two-scale modular arc witnesses

In `ModularArcAtomicSublatticeBlind`, the 5-point pole-filtered modular arc witness
`H_{b,ν} = arcLineAtomicVector b ν` was shown to have Laplace/Mellin strip transform
`(1 − cosh(lb)/cosh(b/2))² ∫ e^{lv} B_ν(v) dv` for `l ∈ [0, 1/2)`, where the second-order
zero `(1 − cosh(lb)/cosh(b/2))² = O((1/2 − l)²)` cancels the simple pole `O((1/2 − l)⁻¹)` of
`∫ e^{lv} B_ν(v) dv` at the strip boundary `l = 1/2` (`s = 1` and `s = 0`), leaving first-order
vanishing `O(1/2 − l)`.

In this module we prove that the **two-scale hyperbolic pole-filtered witness**
`W_{k,ν} = arcLineTwoScaleVector k ν` introduced in `ModularArcTwoScaleHyperbolicWitness` acquires
a **third-order** zero `(1 − cosh(2l log k)/cosh(log k)) (1 − cosh(l log k)/cosh(½ log k))²`
against exponential tilts `e^{lv}`, upgrading the strip-edge decay from `O(1/2 − l)` to
**quadratic vanishing `O((1/2 − l)²)`** at `l → (1/2)⁻`:

1. **Exact strip Laplace/Mellin factorization (`integral_exp_mul_arcLineTwoScaleProfile`):**
   For `k ≥ 1`, symmetric `ν`, and `l ∈ [0, 1/2)`,
   `∫ e^{lv} W_{k,ν}^{prof}(v) dv = (1 − cosh(l · 2 log k)/cosh(log k)) (1 − cosh(l log k)/cosh(½ log k))² ∫ e^{lv} B_ν(v) dv`.
2. **Quadratic strip-edge bound (`abs_integral_exp_mul_arcLineTwoScaleProfile_le`):**
   `|∫ e^{lv} W_{k,ν}^{prof}(v) dv| ≤ 20 · ν.real univ · (log k)³ · (1/2 − l)²` for all `l ∈ [0, 1/2)`.
3. **Double-pole / divided-difference edge vanishing (`abs_div_sub_half_integral_exp_mul_arcLineTwoScaleProfile_le`,
   `tendsto_div_sub_half_integral_exp_mul_arcLineTwoScaleProfile_nhdsWithin`):**
   Even after dividing by the simple-pole distance `1/2 − l`, the ratio satisfies
   `|(∫ e^{lv} W_{k,ν}^{prof}(v) dv) / (1/2 − l)| ≤ 20 · ν.real univ · (log k)³ · (1/2 − l)`
   and converges to `0` as `l → (1/2)⁻` (`𝓝[<] (1/2)`), so `W_{k,ν}` annihilates both simple and
   double poles at the critical strip edges `s = 1` and `s = 0`.
4. **Master unconditional theorem (`exists_twoScale_quadraticEdge_arcWitness`):**
   Combines quadratic strip-edge vanishing, double-pole cancellation, strict critical-line positive
   definiteness, `k⁴`-sublattice blindness, and `k²`-sublattice asymptotic vanishing for all `k ≥ 2`.
-/

open MeasureTheory Set Filter Topology
open GaloisForLFunctions.HTGeometry RHTower.BesselKZero

namespace RHTower

noncomputable section

/-! ### Strip Laplace/Mellin factorization for `arcLineAtomicProfile` and `arcLineSymAtomicProfile` -/

theorem integrable_exp_mul_arcLineAtomicProfile (b : ℝ)
    {ν : Measure ArcParam} [IsFiniteMeasure ν] (hν : ν.map arcNeg = ν)
    {l : ℝ} (hl0 : 0 ≤ l) (hl : l < 1 / 2) :
    Integrable fun v => Real.exp (l * v) * arcLineAtomicProfile b ν v := by
  have hi : ∀ w, Integrable fun v => Real.exp (l * v) * arcPoissonProfile ν (v - w) := fun w => by
    have h := (integrable_exp_mul_arcPoissonProfile hν hl0 hl).comp_sub_right w
    refine (h.const_mul (Real.exp (l * w))).congr (Eventually.of_forall fun v => ?_)
    simp only
    rw [show l * v = l * w + l * (v - w) by ring, Real.exp_add]; ring
  have e : (fun v => Real.exp (l * v) * arcLineAtomicProfile b ν v) = fun v =>
      ∑ j, atomWeight b j * (Real.exp (l * v) * arcPoissonProfile ν (v - atomShift b j)) := by
    funext v
    unfold arcLineAtomicProfile
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [e]
  exact integrable_finsetSum _ fun j _ => (hi _).const_mul _

theorem integrable_exp_mul_arcLineAtomicProfile_sub (b : ℝ)
    {ν : Measure ArcParam} [IsFiniteMeasure ν] (hν : ν.map arcNeg = ν)
    {l : ℝ} (hl0 : 0 ≤ l) (hl : l < 1 / 2) (w : ℝ) :
    Integrable fun v => Real.exp (l * v) * arcLineAtomicProfile b ν (v - w) := by
  have h := (integrable_exp_mul_arcLineAtomicProfile b hν hl0 hl).comp_sub_right w
  refine (h.const_mul (Real.exp (l * w))).congr (Eventually.of_forall fun v => ?_)
  simp only
  rw [show l * v = l * w + l * (v - w) by ring, Real.exp_add]; ring

theorem integral_exp_mul_arcLineAtomicProfile_sub (b : ℝ) (ν : Measure ArcParam) (l w : ℝ) :
    ∫ v, Real.exp (l * v) * arcLineAtomicProfile b ν (v - w) =
      Real.exp (l * w) * ∫ v, Real.exp (l * v) * arcLineAtomicProfile b ν v := by
  rw [← integral_add_right_eq_self (μ := volume)
    (fun v => Real.exp (l * v) * arcLineAtomicProfile b ν (v - w)) w, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun v => ?_)
  simp only
  rw [add_sub_cancel_right, show l * (v + w) = l * w + l * v by ring, Real.exp_add]; ring

/-- **Exact Laplace/Mellin strip factorization for `arcLineAtomicProfile b ν`.** -/
theorem integral_exp_mul_arcLineAtomicProfile (b : ℝ)
    {ν : Measure ArcParam} [IsFiniteMeasure ν] (hν : ν.map arcNeg = ν)
    {l : ℝ} (hl0 : 0 ≤ l) (hl : l < 1 / 2) :
    ∫ v, Real.exp (l * v) * arcLineAtomicProfile b ν v =
      (1 - Real.cosh (l * b) / Real.cosh (b / 2)) ^ 2 *
        ∫ v, Real.exp (l * v) * arcPoissonProfile ν v := by
  have hi : ∀ w, Integrable fun v => Real.exp (l * v) * arcPoissonProfile ν (v - w) := fun w => by
    have h := (integrable_exp_mul_arcPoissonProfile hν hl0 hl).comp_sub_right w
    refine (h.const_mul (Real.exp (l * w))).congr (Eventually.of_forall fun v => ?_)
    simp only
    rw [show l * v = l * w + l * (v - w) by ring, Real.exp_add]; ring
  have e : ∀ v, Real.exp (l * v) * arcLineAtomicProfile b ν v =
      ∑ j, atomWeight b j * (Real.exp (l * v) * arcPoissonProfile ν (v - atomShift b j)) :=
    fun v => by
      unfold arcLineAtomicProfile
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
  simp_rw [e]
  rw [integral_finsetSum _ fun j _ => (hi _).const_mul _]
  simp_rw [integral_const_mul, integral_exp_mul_arcPoissonProfile_sub]
  rw [← atomicWeight_exp]
  simp only [Fin.sum_univ_five, atomWeight, atomShift, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons,
    Matrix.tail_cons, mul_zero, Real.exp_zero]
  ring

/-- **Exact Laplace/Mellin strip transform of `arcLineSymAtomicProfile k ν`.** -/
theorem integral_exp_mul_arcLineSymAtomicProfile (k : ℕ)
    {ν : Measure ArcParam} [IsFiniteMeasure ν] (hν : ν.map arcNeg = ν)
    {l : ℝ} (hl0 : 0 ≤ l) (hl : l < 1 / 2) :
    ∫ v, Real.exp (l * v) * arcLineSymAtomicProfile k ν v =
      Real.cosh (l * (2 * Real.log k)) *
        ∫ v, Real.exp (l * v) * arcLineAtomicProfile (Real.log k) ν v := by
  have hF : Integrable fun v => Real.exp (l * v) * arcLineForwardAtomicProfile k ν v :=
    integrable_exp_mul_arcLineAtomicProfile_sub (Real.log k) hν hl0 hl (2 * Real.log k)
  have hB : Integrable fun v => Real.exp (l * v) * arcLineBackwardAtomicProfile k ν v := by
    have e : (fun v => Real.exp (l * v) * arcLineBackwardAtomicProfile k ν v) =
        fun v => Real.exp (l * v) *
          arcLineAtomicProfile (Real.log k) ν (v - (-(2 * Real.log k))) := by
      funext v; unfold arcLineBackwardAtomicProfile; rw [sub_neg_eq_add]
    rw [e]
    exact integrable_exp_mul_arcLineAtomicProfile_sub (Real.log k) hν hl0 hl (-(2 * Real.log k))
  have e : (fun v => Real.exp (l * v) * arcLineSymAtomicProfile k ν v) = fun v =>
      (1 / 2 : ℝ) * (Real.exp (l * v) * arcLineForwardAtomicProfile k ν v +
        Real.exp (l * v) * arcLineBackwardAtomicProfile k ν v) := by
    funext v; unfold arcLineSymAtomicProfile; ring
  have eB : ∫ v, Real.exp (l * v) * arcLineBackwardAtomicProfile k ν v =
      Real.exp (-(l * (2 * Real.log k))) *
        ∫ v, Real.exp (l * v) * arcLineAtomicProfile (Real.log k) ν v := by
    have e' : (fun v => Real.exp (l * v) * arcLineBackwardAtomicProfile k ν v) =
        fun v => Real.exp (l * v) *
          arcLineAtomicProfile (Real.log k) ν (v - (-(2 * Real.log k))) := by
      funext v; unfold arcLineBackwardAtomicProfile; rw [sub_neg_eq_add]
    rw [e', integral_exp_mul_arcLineAtomicProfile_sub, mul_neg]
  rw [e, integral_const_mul, integral_add hF hB]
  unfold arcLineForwardAtomicProfile
  rw [integral_exp_mul_arcLineAtomicProfile_sub, eB, Real.cosh_eq]
  ring

/-! ### Exact two-scale strip factorization and quadratic edge-vanishing bounds -/

/-- **Exact Laplace/Mellin strip factorization for `arcLineTwoScaleProfile k ν`.** -/
theorem integral_exp_mul_arcLineTwoScaleProfile (k : ℕ)
    {ν : Measure ArcParam} [IsFiniteMeasure ν] (hν : ν.map arcNeg = ν)
    {l : ℝ} (hl0 : 0 ≤ l) (hl : l < 1 / 2) :
    ∫ v, Real.exp (l * v) * arcLineTwoScaleProfile k ν v =
      (1 - Real.cosh (l * (2 * Real.log k)) / Real.cosh (Real.log k)) *
        (1 - Real.cosh (l * Real.log k) / Real.cosh (Real.log k / 2)) ^ 2 *
        ∫ v, Real.exp (l * v) * arcPoissonProfile ν v := by
  have hH := integrable_exp_mul_arcLineAtomicProfile (Real.log k) hν hl0 hl
  have hS : Integrable fun v => Real.exp (l * v) * arcLineSymAtomicProfile k ν v := by
    have hF := integrable_exp_mul_arcLineAtomicProfile_sub (Real.log k) hν hl0 hl (2 * Real.log k)
    have hB : Integrable fun v => Real.exp (l * v) * arcLineBackwardAtomicProfile k ν v := by
      have e : (fun v => Real.exp (l * v) * arcLineBackwardAtomicProfile k ν v) =
          fun v => Real.exp (l * v) *
            arcLineAtomicProfile (Real.log k) ν (v - (-(2 * Real.log k))) := by
        funext v; unfold arcLineBackwardAtomicProfile; rw [sub_neg_eq_add]
      rw [e]
      exact integrable_exp_mul_arcLineAtomicProfile_sub (Real.log k) hν hl0 hl (-(2 * Real.log k))
    have e : (fun v => Real.exp (l * v) * arcLineSymAtomicProfile k ν v) = fun v =>
        (1 / 2 : ℝ) * (Real.exp (l * v) * arcLineForwardAtomicProfile k ν v +
          Real.exp (l * v) * arcLineBackwardAtomicProfile k ν v) := by
      funext v; unfold arcLineSymAtomicProfile; ring
    rw [e]
    exact (hF.add hB).const_mul _
  have e : (fun v => Real.exp (l * v) * arcLineTwoScaleProfile k ν v) = fun v =>
      Real.exp (l * v) * arcLineAtomicProfile (Real.log k) ν v -
        (1 / Real.cosh (Real.log k)) * (Real.exp (l * v) * arcLineSymAtomicProfile k ν v) := by
    funext v; unfold arcLineTwoScaleProfile; ring
  rw [e, integral_sub hH (hS.const_mul _), integral_const_mul,
    integral_exp_mul_arcLineSymAtomicProfile k hν hl0 hl,
    integral_exp_mul_arcLineAtomicProfile (Real.log k) hν hl0 hl]
  ring

/-- **Quadratic strip-edge vanishing bound for `arcLineTwoScaleProfile k ν`.**
Because the two-scale hyperbolic filter introduces a third-order zero at `l = 1/2`, the strip
Laplace/Mellin transform vanishes quadratically as `O((1/2 − l)²)` at `l → (1/2)⁻`. -/
theorem abs_integral_exp_mul_arcLineTwoScaleProfile_le {k : ℕ} (hk : 1 ≤ k)
    {ν : Measure ArcParam} [IsFiniteMeasure ν] (hν : ν.map arcNeg = ν)
    {l : ℝ} (hl0 : 0 ≤ l) (hl : l < 1 / 2) :
    |∫ v, Real.exp (l * v) * arcLineTwoScaleProfile k ν v| ≤
      20 * ν.real univ * (Real.log k) ^ 3 * (1 / 2 - l) ^ 2 := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hb : 0 ≤ Real.log k := Real.log_nonneg hk1
  have hb2 : 0 ≤ 2 * Real.log k := by positivity
  have hκ : 0 < 1 / 2 - l := by linarith
  obtain ⟨h1_lo, h1_hi⟩ := one_sub_cosh_div_le hb hl0 hl.le
  obtain ⟨h2_lo, h2_hi⟩ := one_sub_cosh_div_le hb2 hl0 hl.le
  have hdiv : 2 * Real.log k / 2 = Real.log k := by ring
  rw [hdiv] at h2_lo h2_hi
  have hQ := abs_integral_exp_mul_arcPoissonProfile_le hν hl0 hl
  rw [integral_exp_mul_arcLineTwoScaleProfile k hν hl0 hl, abs_mul, abs_mul,
    abs_of_nonneg h2_lo, abs_of_nonneg (sq_nonneg _)]
  have hprod : (1 - Real.cosh (l * (2 * Real.log k)) / Real.cosh (Real.log k)) *
      (1 - Real.cosh (l * Real.log k) / Real.cosh (Real.log k / 2)) ^ 2 ≤
      (2 * Real.log k * (1 / 2 - l)) * (Real.log k * (1 / 2 - l)) ^ 2 :=
    mul_le_mul h2_hi (pow_le_pow_left₀ h1_lo h1_hi 2) (sq_nonneg _) (by positivity)
  calc (1 - Real.cosh (l * (2 * Real.log k)) / Real.cosh (Real.log k)) *
        (1 - Real.cosh (l * Real.log k) / Real.cosh (Real.log k / 2)) ^ 2 *
        |∫ v, Real.exp (l * v) * arcPoissonProfile ν v|
      ≤ ((2 * Real.log k * (1 / 2 - l)) * (Real.log k * (1 / 2 - l)) ^ 2) *
          (10 * ν.real univ / (1 / 2 - l)) :=
        mul_le_mul hprod hQ (abs_nonneg _) (by positivity)
    _ = 20 * ν.real univ * (Real.log k) ^ 3 * (1 / 2 - l) ^ 2 := by
        field_simp; ring

/-- **Double-pole divided-difference bound at the strip edge `l = 1/2`:**
dividing the strip Laplace/Mellin transform by the simple-pole factor `1/2 − l` still leaves
linear vanishing `O(1/2 − l)`. -/
theorem abs_div_sub_half_integral_exp_mul_arcLineTwoScaleProfile_le {k : ℕ} (hk : 1 ≤ k)
    {ν : Measure ArcParam} [IsFiniteMeasure ν] (hν : ν.map arcNeg = ν)
    {l : ℝ} (hl0 : 0 ≤ l) (hl : l < 1 / 2) :
    |(∫ v, Real.exp (l * v) * arcLineTwoScaleProfile k ν v) / (1 / 2 - l)| ≤
      20 * ν.real univ * (Real.log k) ^ 3 * (1 / 2 - l) := by
  have hκ : 0 < 1 / 2 - l := by linarith
  rw [abs_div, abs_of_pos hκ, div_le_iff₀ hκ]
  calc |∫ v, Real.exp (l * v) * arcLineTwoScaleProfile k ν v|
      ≤ 20 * ν.real univ * (Real.log k) ^ 3 * (1 / 2 - l) ^ 2 :=
        abs_integral_exp_mul_arcLineTwoScaleProfile_le hk hν hl0 hl
    _ = 20 * ν.real univ * (Real.log k) ^ 3 * (1 / 2 - l) * (1 / 2 - l) := by ring

/-- **Double-pole edge vanishing as `l → (1/2)⁻`:**
`(∫ e^{lv} W_{k,ν}^{prof}(v) dv) / (1/2 − l) → 0` on `𝓝[<] (1/2)`. -/
theorem tendsto_div_sub_half_integral_exp_mul_arcLineTwoScaleProfile_nhdsWithin
    {k : ℕ} (hk : 1 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν] (hν : ν.map arcNeg = ν) :
    Tendsto (fun l : ℝ => (∫ v, Real.exp (l * v) * arcLineTwoScaleProfile k ν v) / (1 / 2 - l))
      (𝓝[<] (1 / 2)) (𝓝 0) := by
  set D := 20 * ν.real univ * (Real.log k) ^ 3
  have hlin : Tendsto (fun l : ℝ => D * (1 / 2 - l)) (𝓝[<] (1 / 2)) (𝓝 0) := by
    have hcont : Continuous fun l : ℝ => D * (1 / 2 - l) := by fun_prop
    have h := (hcont.continuousAt (x := (1 / 2 : ℝ))).tendsto.mono_left
      (nhdsWithin_le_nhds (s := Iio (1 / 2 : ℝ)))
    rwa [sub_self, mul_zero] at h
  refine squeeze_zero_norm' ?_ hlin
  have hmem : Ioo (0 : ℝ) (1 / 2) ∈ 𝓝[<] (1 / 2 : ℝ) :=
    Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1 / 2)
  filter_upwards [hmem] with l hl
  rw [Real.norm_eq_abs]
  exact abs_div_sub_half_integral_exp_mul_arcLineTwoScaleProfile_le hk hν hl.1.le hl.2

/-- **Master unconditional theorem for two-scale quadratic strip-edge vanishing.**
For every integer `k ≥ 2`, the two-scale hyperbolic modular arc witness
`W_k = arcLineTwoScaleVector k ν` is strictly self-reciprocal, zero-mean, strictly positive
definite on the critical line, blind on the `k⁴`-sublattice, contracted on the `k²`-sublattice,
and vanishes quadratically `O((1/2 − l)²)` at the critical strip edge `l → (1/2)⁻` so that even
its divided difference `(∫ e^{lv} W_k^{prof}(v) dv) / (1/2 − l)` tends to `0`. -/
theorem exists_twoScale_quadraticEdge_arcWitness :
    ∃ ν : Measure ArcParam, IsFiniteMeasure ν ∧ ν ≠ 0 ∧ ν.map arcNeg = ν ∧
      ∀ k : ℕ, 2 ≤ k →
        (∀ x, x ≠ 0 → arcLineTwoScaleVector k ν (1 / x) =
          |x| * arcLineTwoScaleVector k ν x) ∧
        ∫ x, arcLineTwoScaleVector k ν x = 0 ∧
        (∀ m : ℕ, ∫ x, arcLineTwoScaleDeriv k ν x *
          Real.sin (arcFreq (k ^ 4 * (m + 1) - 1) * x) = 0) ∧
        (∀ τ : ℝ, 0 < ∫ v, Real.cos (τ * v) * arcLineTwoScaleProfile k ν v) ∧
        (∀ l : ℝ, 0 ≤ l → l < 1 / 2 →
          |∫ v, Real.exp (l * v) * arcLineTwoScaleProfile k ν v| ≤
            20 * ν.real univ * (Real.log k) ^ 3 * (1 / 2 - l) ^ 2) ∧
        Tendsto (fun l : ℝ =>
          (∫ v, Real.exp (l * v) * arcLineTwoScaleProfile k ν v) / (1 / 2 - l))
          (𝓝[<] (1 / 2)) (𝓝 0) := by
  obtain ⟨ν, hfin, hne, hsym, hblind_whittaker, hpd⟩ := exists_arcWitness
  have hblind : ∀ n : ℕ, ∫ t, arcLineDeriv ν t * Real.sin (arcFreq n * t) = 0 := fun n => by
    rw [integral_arcLineDeriv_mul_sin, (hblind_whittaker n).1, mul_zero, neg_zero]
  refine ⟨ν, hfin, hne, hsym, fun k hk => ?_⟩
  have hk1 : 1 ≤ k := by omega
  exact ⟨fun x hx => arcLineTwoScaleVector_inv hk1 ν hx,
    integral_arcLineTwoScaleVector_eq_zero hk1 hsym,
    integral_arcLineTwoScaleDeriv_mul_sin_pow4_mul_eq_zero hblind hk1,
    integral_cos_mul_arcLineTwoScaleProfile_pos hk ν hpd,
    fun l hl0 hl => abs_integral_exp_mul_arcLineTwoScaleProfile_le hk1 hsym hl0 hl,
    tendsto_div_sub_half_integral_exp_mul_arcLineTwoScaleProfile_nhdsWithin hk1 hsym⟩

end

end RHTower
