import GaloisForLFunctions.RHTower.XiGaussianHeatWindowRHCriterion

/-!
# RH is even Weil positivity

**Theorem** (`riemannHypothesis_iff_forall_evenPoleWeilNonneg`). RH holds if and only if, for
every `A > 0`, every smooth even real source vanishing outside `[-A, A]` with `∫ u e^{x/2} = 0`
has nonnegative zero-side energy `Re Σ_q F_u(z_q)²`. Equivalently
(`riemannHypothesis_iff_forall_evenHodgeIndexAtLevel`), Weil positivity on even tests holds at
every level.

Proof of the converse: under ¬RH some heat window fails (`riemannHypothesis_iff_forall_heatWindowNonneg`),
so a Gaussian heat test `g` is a negative even pole-free source.
* Its cutoffs `u_R = χ(·/R) g − c_R χ` are compactly supported, even and pole-free.
* `u_R → g` in `∫|·| e^{|x|/2}`, and the strip bound `|z| |F_u(z)| ≤ ∫|u'| e^{|x|/2}` is uniform
  in `R`.
* So `Σ F_{u_R}(z_q)² → Σ F_g(z_q)²` by dominated convergence against `Σ 1/|z_q|²`.
-/

open Complex MeasureTheory Filter Topology Set Polynomial
open scoped Real
open Zeta23
open GaloisForLFunctions (gaussPolyFun)

namespace RHTower

noncomputable section

/-! ## The cutoff -/

/-- The fixed even bump, `1` on `[-1, 1]` and `0` outside `(-2, 2)`. -/
def unitCutoff : ContDiffBump (0 : ℝ) := ⟨1, 2, one_pos, one_lt_two⟩

theorem contDiff_unitCutoff : ContDiff ℝ (⊤ : ℕ∞) (unitCutoff : ℝ → ℝ) := unitCutoff.contDiff

theorem unitCutoff_eq_one {x : ℝ} (hx : |x| ≤ 1) : (unitCutoff : ℝ → ℝ) x = 1 :=
  unitCutoff.one_of_mem_closedBall (by rw [Metric.mem_closedBall, Real.dist_eq, sub_zero]; exact hx)

theorem unitCutoff_eq_zero {x : ℝ} (hx : 2 ≤ |x|) : (unitCutoff : ℝ → ℝ) x = 0 :=
  unitCutoff.zero_of_le_dist (by rw [Real.dist_eq, sub_zero]; exact hx)

theorem exists_bound_deriv_unitCutoff :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |deriv (unitCutoff : ℝ → ℝ) x| ≤ C := by
  have hc := contDiff_unitCutoff.continuous_deriv (by exact_mod_cast le_top)
  obtain ⟨C, hC⟩ := unitCutoff.hasCompactSupport.deriv.exists_bound_of_continuous hc
  refine ⟨max C 0, le_max_right _ _, fun x => ?_⟩
  rw [← Real.norm_eq_abs]
  exact (hC x).trans (le_max_left _ _)

theorem hasDerivAt_unitCutoff_div {R : ℝ} (x : ℝ) :
    HasDerivAt (fun y => (unitCutoff : ℝ → ℝ) (y / R))
      (deriv (unitCutoff : ℝ → ℝ) (x / R) / R) x := by
  have h1 : HasDerivAt (fun y : ℝ => y / R) (1 / R) x := (hasDerivAt_id x).div_const R
  have h2 := (contDiff_unitCutoff.differentiable (by simp) (x / R)).hasDerivAt
  have := h2.comp x h1
  rw [show deriv (unitCutoff : ℝ → ℝ) (x / R) / R = deriv (unitCutoff : ℝ → ℝ) (x / R) * (1 / R) by
    ring]
  exact this

theorem unitCutoff_moment_pos : 0 < ∫ x, (unitCutoff : ℝ → ℝ) x * Real.exp (x / 2) := by
  refine Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := 0)
    (contDiff_unitCutoff.continuous.mul (Real.continuous_exp.comp (continuous_id.div_const 2)))
    unitCutoff.hasCompactSupport.mul_right (fun x => mul_nonneg unitCutoff.nonneg
      (Real.exp_pos _).le) ?_
  rw [unitCutoff_eq_one (by simp)]
  simp

/-! ## Cutting a source off -/

/-- The cut source `χ(x/R) g(x) - c χ(x)`. -/
def cutSource (g : ℝ → ℝ) (c R : ℝ) (x : ℝ) : ℝ :=
  (unitCutoff : ℝ → ℝ) (x / R) * g x - c * (unitCutoff : ℝ → ℝ) x

/-- Its derivative. -/
def cutSourceDeriv (g g' : ℝ → ℝ) (c R : ℝ) (x : ℝ) : ℝ :=
  deriv (unitCutoff : ℝ → ℝ) (x / R) / R * g x + (unitCutoff : ℝ → ℝ) (x / R) * g' x -
    c * deriv (unitCutoff : ℝ → ℝ) x

theorem hasDerivAt_cutSource {g g' : ℝ → ℝ} (hd : ∀ x, HasDerivAt g (g' x) x) (c R x : ℝ) :
    HasDerivAt (cutSource g c R) (cutSourceDeriv g g' c R x) x := by
  have h1 := (hasDerivAt_unitCutoff_div (R := R) x).mul (hd x)
  have h2 := ((contDiff_unitCutoff.differentiable (by simp) x).hasDerivAt).const_mul c
  have := h1.sub h2
  unfold cutSource cutSourceDeriv
  exact this

theorem contDiff_cutSource {g : ℝ → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (c R : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (cutSource g c R) :=
  ((contDiff_unitCutoff.comp (contDiff_id.div_const R)).mul hg).sub
    (contDiff_const.mul contDiff_unitCutoff)

theorem continuous_cutSourceDeriv {g g' : ℝ → ℝ} (hg : Continuous g) (hg' : Continuous g')
    (c R : ℝ) : Continuous (cutSourceDeriv g g' c R) := by
  have hc := contDiff_unitCutoff.continuous_deriv (by exact_mod_cast le_top)
  unfold cutSourceDeriv
  exact (((hc.comp (continuous_id.div_const R)).div_const R).mul hg).add
    ((contDiff_unitCutoff.continuous.comp (continuous_id.div_const R)).mul hg') |>.sub
    (continuous_const.mul hc)

theorem cutSource_neg {g : ℝ → ℝ} (heven : ∀ x, g (-x) = g x) (c R x : ℝ) :
    cutSource g c R (-x) = cutSource g c R x := by
  unfold cutSource
  rw [neg_div, unitCutoff.neg, unitCutoff.neg, heven]

theorem cutSource_eq_zero {g : ℝ → ℝ} {c R : ℝ} (hR : 1 ≤ R) {t : ℝ} (ht : 2 * R < |t|) :
    cutSource g c R t = 0 := by
  have hR0 : 0 < R := by linarith
  have h1 : (unitCutoff : ℝ → ℝ) (t / R) = 0 := unitCutoff_eq_zero (by
    rw [abs_div, abs_of_pos hR0, le_div_iff₀ hR0]; linarith)
  have h2 : (unitCutoff : ℝ → ℝ) t = 0 := unitCutoff_eq_zero (by linarith)
  simp [cutSource, h1, h2]

theorem cutSourceDeriv_eq_zero {g g' : ℝ → ℝ} {c R : ℝ} (hR : 1 ≤ R) {t : ℝ} (ht : 2 * R < |t|) :
    cutSourceDeriv g g' c R t = 0 := by
  have hR0 : 0 < R := by linarith
  have hz : ∀ y : ℝ, 2 < |y| → deriv (unitCutoff : ℝ → ℝ) y = 0 := fun y hy => by
    have hev : (unitCutoff : ℝ → ℝ) =ᶠ[𝓝 y] fun _ => 0 := by
      have : ∀ᶠ w in 𝓝 y, 2 < |w| := (continuous_abs.tendsto y).eventually (lt_mem_nhds hy)
      filter_upwards [this] with w hw
      exact unitCutoff_eq_zero hw.le
    rw [hev.deriv_eq]; simp
  have h1 : |t / R| > 2 := by rw [abs_div, abs_of_pos hR0, gt_iff_lt, lt_div_iff₀ hR0]; linarith
  have h2 : (unitCutoff : ℝ → ℝ) (t / R) = 0 := unitCutoff_eq_zero h1.le
  simp [cutSourceDeriv, hz _ h1, hz t (by linarith), h2]

theorem hasCompactSupport_cutSource {g : ℝ → ℝ} {c R : ℝ} (hR : 1 ≤ R) :
    HasCompactSupport (cutSource g c R) :=
  HasCompactSupport.intro (isCompact_Icc (a := -(2 * R)) (b := 2 * R)) fun t ht => by
    apply cutSource_eq_zero hR
    by_contra h
    push Not at h
    exact ht ⟨by linarith [(abs_le.1 h).1], (abs_le.1 h).2⟩

theorem hasCompactSupport_cutSourceDeriv {g g' : ℝ → ℝ} {c R : ℝ} (hR : 1 ≤ R) :
    HasCompactSupport (cutSourceDeriv g g' c R) :=
  HasCompactSupport.intro (isCompact_Icc (a := -(2 * R)) (b := 2 * R)) fun t ht => by
    apply cutSourceDeriv_eq_zero hR
    by_contra h
    push Not at h
    exact ht ⟨by linarith [(abs_le.1 h).1], (abs_le.1 h).2⟩

/-! ## Limits of the cutoffs -/

theorem unitCutoff_div_eventually_one (x : ℝ) :
    ∀ᶠ k : ℕ in atTop, (unitCutoff : ℝ → ℝ) (x / ((k : ℝ) + 1)) = 1 := by
  obtain ⟨N, hN⟩ := exists_nat_ge |x|
  filter_upwards [eventually_ge_atTop N] with k hk
  apply unitCutoff_eq_one
  have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  rw [abs_div, abs_of_pos hk1, div_le_one hk1]
  have : (N : ℝ) ≤ k := by exact_mod_cast hk
  linarith

theorem abs_unitCutoff_le (x : ℝ) : |(unitCutoff : ℝ → ℝ) x| ≤ 1 := by
  rw [abs_of_nonneg unitCutoff.nonneg]; exact unitCutoff.le_one

theorem exp_half_le_exp_abs_half (x : ℝ) : Real.exp (x / 2) ≤ Real.exp (|x| / 2) :=
  Real.exp_le_exp.2 (by linarith [le_abs_self x])

/-- `∫ χ(x/R) g(x) e^{x/2} → ∫ g e^{x/2}`. -/
theorem tendsto_integral_cutoff_mul {g : ℝ → ℝ} (hg : Continuous g)
    (hI0 : Integrable (fun x => |g x| * Real.exp (|x| / 2))) :
    Tendsto (fun k : ℕ => ∫ x, (unitCutoff : ℝ → ℝ) (x / ((k : ℝ) + 1)) * g x * Real.exp (x / 2))
      atTop (𝓝 (∫ x, g x * Real.exp (x / 2))) := by
  refine tendsto_integral_of_dominated_convergence (fun x => |g x| * Real.exp (|x| / 2))
    (fun k => ?_) hI0 (fun k => Filter.Eventually.of_forall fun x => ?_)
    (Filter.Eventually.of_forall fun x => ?_)
  · exact (((contDiff_unitCutoff.continuous.comp (continuous_id.div_const _)).mul hg).mul
      (Real.continuous_exp.comp (continuous_id.div_const 2))).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _)]
    calc |(unitCutoff : ℝ → ℝ) (x / ((k : ℝ) + 1))| * |g x| * Real.exp (x / 2)
        ≤ 1 * |g x| * Real.exp (|x| / 2) := by
          gcongr
          · exact abs_unitCutoff_le _
          · exact le_abs_self x
      _ = |g x| * Real.exp (|x| / 2) := by ring
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [unitCutoff_div_eventually_one x] with k hk
    rw [hk, one_mul]

/-- `∫ |1 - χ(x/R)| |g| e^{|x|/2} → 0`. -/
theorem tendsto_integral_one_sub_cutoff {g : ℝ → ℝ} (hg : Continuous g)
    (hI0 : Integrable (fun x => |g x| * Real.exp (|x| / 2))) :
    Tendsto (fun k : ℕ => ∫ x, |1 - (unitCutoff : ℝ → ℝ) (x / ((k : ℝ) + 1))| * |g x| *
      Real.exp (|x| / 2)) atTop (𝓝 0) := by
  have h := tendsto_integral_of_dominated_convergence (μ := volume)
    (F := fun (k : ℕ) x => |1 - (unitCutoff : ℝ → ℝ) (x / ((k : ℝ) + 1))| * |g x| *
      Real.exp (|x| / 2)) (f := fun _ => (0 : ℝ)) (fun x => |g x| * Real.exp (|x| / 2))
    (fun k => ?_) hI0 (fun k => Filter.Eventually.of_forall fun x => ?_)
    (Filter.Eventually.of_forall fun x => ?_)
  · simpa using h
  · exact (((continuous_const.sub (contDiff_unitCutoff.continuous.comp
      (continuous_id.div_const _))).abs.mul hg.abs).mul
      (Real.continuous_exp.comp (continuous_abs.div_const 2))).aestronglyMeasurable
  · have h0 : 0 ≤ (unitCutoff : ℝ → ℝ) (x / ((k : ℝ) + 1)) := unitCutoff.nonneg
    have h1 : (unitCutoff : ℝ → ℝ) (x / ((k : ℝ) + 1)) ≤ 1 := unitCutoff.le_one
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc |1 - (unitCutoff : ℝ → ℝ) (x / ((k : ℝ) + 1))| * |g x| * Real.exp (|x| / 2)
        ≤ 1 * |g x| * Real.exp (|x| / 2) := by
          gcongr
          rw [abs_of_nonneg (by linarith)]; linarith
      _ = |g x| * Real.exp (|x| / 2) := by ring
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [unitCutoff_div_eventually_one x] with k hk
    rw [hk]; simp

/-! ## Integral estimates for the cut source -/

theorem integrable_cont_compact_weight {h : ℝ → ℝ} (hh : Continuous h) (hc : HasCompactSupport h) :
    Integrable (fun x => |h x| * Real.exp (|x| / 2)) :=
  (hh.abs.mul (Real.continuous_exp.comp (continuous_abs.div_const 2))).integrable_of_hasCompactSupport
    hc.abs.mul_right

theorem integrable_unitCutoff_div_mul_exp {g : ℝ → ℝ} (hg : Continuous g)
    (hI0 : Integrable (fun x => |g x| * Real.exp (|x| / 2))) (R : ℝ) :
    Integrable (fun x => (unitCutoff : ℝ → ℝ) (x / R) * g x * Real.exp (x / 2)) := by
  refine hI0.mono' (((contDiff_unitCutoff.continuous.comp (continuous_id.div_const _)).mul hg).mul
    (Real.continuous_exp.comp (continuous_id.div_const 2))).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _)]
  calc |(unitCutoff : ℝ → ℝ) (x / R)| * |g x| * Real.exp (x / 2)
      ≤ 1 * |g x| * Real.exp (|x| / 2) := by
        gcongr
        · exact abs_unitCutoff_le _
        · exact le_abs_self x
    _ = |g x| * Real.exp (|x| / 2) := by ring

theorem integral_cutSource_mul_exp {g : ℝ → ℝ} (hg : Continuous g)
    (hI0 : Integrable (fun x => |g x| * Real.exp (|x| / 2))) (c R : ℝ) :
    ∫ x, cutSource g c R x * Real.exp (x / 2) =
      (∫ x, (unitCutoff : ℝ → ℝ) (x / R) * g x * Real.exp (x / 2)) -
        c * ∫ x, (unitCutoff : ℝ → ℝ) x * Real.exp (x / 2) := by
  have h2 : Integrable (fun x => (unitCutoff : ℝ → ℝ) x * Real.exp (x / 2)) :=
    (contDiff_unitCutoff.continuous.mul (Real.continuous_exp.comp
      (continuous_id.div_const 2))).integrable_of_hasCompactSupport unitCutoff.hasCompactSupport.mul_right
  have e : (fun x => cutSource g c R x * Real.exp (x / 2)) = fun x =>
      (unitCutoff : ℝ → ℝ) (x / R) * g x * Real.exp (x / 2) -
        c * ((unitCutoff : ℝ → ℝ) x * Real.exp (x / 2)) := by
    funext x; unfold cutSource; ring
  rw [e, integral_sub (integrable_unitCutoff_div_mul_exp hg hI0 R) (h2.const_mul c),
    integral_const_mul]

/-- `∫ |u_R - g| e^{|x|/2} ≤ ∫ |1 - χ(x/R)| |g| e^{|x|/2} + |c| ∫ χ e^{|x|/2}`. -/
theorem integral_cutSource_sub_le {g : ℝ → ℝ} (hg : Continuous g)
    (hI0 : Integrable (fun x => |g x| * Real.exp (|x| / 2))) (c R : ℝ) :
    ∫ x, |cutSource g c R x - g x| * Real.exp (|x| / 2) ≤
      (∫ x, |1 - (unitCutoff : ℝ → ℝ) (x / R)| * |g x| * Real.exp (|x| / 2)) +
        |c| * ∫ x, |(unitCutoff : ℝ → ℝ) x| * Real.exp (|x| / 2) := by
  have hA : Integrable (fun x => |1 - (unitCutoff : ℝ → ℝ) (x / R)| * |g x| * Real.exp (|x| / 2)) := by
    refine hI0.mono' (((continuous_const.sub (contDiff_unitCutoff.continuous.comp
      (continuous_id.div_const _))).abs.mul hg.abs).mul
      (Real.continuous_exp.comp (continuous_abs.div_const 2))).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    have h0 : 0 ≤ (unitCutoff : ℝ → ℝ) (x / R) := unitCutoff.nonneg
    have h1 : (unitCutoff : ℝ → ℝ) (x / R) ≤ 1 := unitCutoff.le_one
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc |1 - (unitCutoff : ℝ → ℝ) (x / R)| * |g x| * Real.exp (|x| / 2)
        ≤ 1 * |g x| * Real.exp (|x| / 2) := by
          gcongr
          rw [abs_of_nonneg (by linarith)]; linarith
      _ = |g x| * Real.exp (|x| / 2) := by ring
  have hB := integrable_cont_compact_weight contDiff_unitCutoff.continuous unitCutoff.hasCompactSupport
  rw [← integral_const_mul, ← integral_add hA (hB.const_mul _)]
  refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => by positivity)
    (hA.add (hB.const_mul _)) (Filter.Eventually.of_forall fun x => ?_)
  dsimp only
  have e : cutSource g c R x - g x =
      -((1 - (unitCutoff : ℝ → ℝ) (x / R)) * g x) - c * (unitCutoff : ℝ → ℝ) x := by
    unfold cutSource; ring
  rw [e]
  have h := abs_sub (-((1 - (unitCutoff : ℝ → ℝ) (x / R)) * g x)) (c * (unitCutoff : ℝ → ℝ) x)
  rw [abs_neg, abs_mul, abs_mul] at h
  have hE := Real.exp_pos (|x| / 2)
  calc |-((1 - (unitCutoff : ℝ → ℝ) (x / R)) * g x) - c * (unitCutoff : ℝ → ℝ) x| *
        Real.exp (|x| / 2)
      ≤ (|1 - (unitCutoff : ℝ → ℝ) (x / R)| * |g x| + |c| * |(unitCutoff : ℝ → ℝ) x|) *
          Real.exp (|x| / 2) := mul_le_mul_of_nonneg_right h hE.le
    _ = _ := by ring

/-- `∫ |u_R'| e^{|x|/2} ≤ C₁ N₀ + N₁ + |c| ∫ |χ'| e^{|x|/2}` for `R ≥ 1`. -/
theorem integral_cutSourceDeriv_le {g g' : ℝ → ℝ}
    (hI0 : Integrable (fun x => |g x| * Real.exp (|x| / 2)))
    (hI1 : Integrable (fun x => |g' x| * Real.exp (|x| / 2))) {C₁ : ℝ} (hC₁0 : 0 ≤ C₁)
    (hC₁ : ∀ x, |deriv (unitCutoff : ℝ → ℝ) x| ≤ C₁) (c : ℝ) {R : ℝ} (hR : 1 ≤ R) :
    ∫ x, |cutSourceDeriv g g' c R x| * Real.exp (|x| / 2) ≤
      C₁ * (∫ x, |g x| * Real.exp (|x| / 2)) + (∫ x, |g' x| * Real.exp (|x| / 2)) +
        |c| * ∫ x, |deriv (unitCutoff : ℝ → ℝ) x| * Real.exp (|x| / 2) := by
  have hR0 : 0 < R := by linarith
  have hcd := contDiff_unitCutoff.continuous_deriv (by exact_mod_cast le_top)
  have hB := integrable_cont_compact_weight hcd unitCutoff.hasCompactSupport.deriv
  have hRHS : ∫ x, (C₁ * (|g x| * Real.exp (|x| / 2)) + |g' x| * Real.exp (|x| / 2) +
      |c| * (|deriv (unitCutoff : ℝ → ℝ) x| * Real.exp (|x| / 2))) =
      C₁ * (∫ x, |g x| * Real.exp (|x| / 2)) + (∫ x, |g' x| * Real.exp (|x| / 2)) +
        |c| * ∫ x, |deriv (unitCutoff : ℝ → ℝ) x| * Real.exp (|x| / 2) := by
    have i0 : Integrable (fun x => C₁ * (|g x| * Real.exp (|x| / 2))) := hI0.const_mul C₁
    have i1 : Integrable (fun x => C₁ * (|g x| * Real.exp (|x| / 2)) +
        |g' x| * Real.exp (|x| / 2)) := i0.add hI1
    have i2 : Integrable (fun x => |c| * (|deriv (unitCutoff : ℝ → ℝ) x| *
        Real.exp (|x| / 2))) := hB.const_mul _
    rw [integral_add i1 i2, integral_add i0 hI1, integral_const_mul, integral_const_mul]
  rw [← hRHS]
  refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => by positivity)
    (((hI0.const_mul _).add hI1).add (hB.const_mul _)) (Filter.Eventually.of_forall fun x => ?_)
  dsimp only
  have hE := Real.exp_pos (|x| / 2)
  have h1 : |deriv (unitCutoff : ℝ → ℝ) (x / R) / R * g x| ≤ C₁ * |g x| := by
    rw [abs_mul, abs_div, abs_of_pos hR0]
    have : |deriv (unitCutoff : ℝ → ℝ) (x / R)| / R ≤ C₁ := by
      rw [div_le_iff₀ hR0]; nlinarith [hC₁ (x / R), abs_nonneg (deriv (unitCutoff : ℝ → ℝ) (x / R))]
    exact mul_le_mul_of_nonneg_right this (abs_nonneg _)
  have h2 : |(unitCutoff : ℝ → ℝ) (x / R) * g' x| ≤ |g' x| := by
    rw [abs_mul]
    calc |(unitCutoff : ℝ → ℝ) (x / R)| * |g' x| ≤ 1 * |g' x| :=
          mul_le_mul_of_nonneg_right (abs_unitCutoff_le _) (abs_nonneg _)
      _ = |g' x| := one_mul _
  have h3 : |c * deriv (unitCutoff : ℝ → ℝ) x| = |c| * |deriv (unitCutoff : ℝ → ℝ) x| := abs_mul _ _
  have htri : |cutSourceDeriv g g' c R x| ≤
      C₁ * |g x| + |g' x| + |c| * |deriv (unitCutoff : ℝ → ℝ) x| := by
    unfold cutSourceDeriv
    calc _ ≤ |deriv (unitCutoff : ℝ → ℝ) (x / R) / R * g x + (unitCutoff : ℝ → ℝ) (x / R) * g' x| +
          |c * deriv (unitCutoff : ℝ → ℝ) x| := abs_sub _ _
      _ ≤ |deriv (unitCutoff : ℝ → ℝ) (x / R) / R * g x| +
          |(unitCutoff : ℝ → ℝ) (x / R) * g' x| + |c * deriv (unitCutoff : ℝ → ℝ) x| := by
          gcongr; exact abs_add_le _ _
      _ ≤ _ := by rw [h3]; linarith
  calc |cutSourceDeriv g g' c R x| * Real.exp (|x| / 2)
      ≤ (C₁ * |g x| + |g' x| + |c| * |deriv (unitCutoff : ℝ → ℝ) x|) * Real.exp (|x| / 2) :=
        mul_le_mul_of_nonneg_right htri hE.le
    _ = _ := by ring

/-! ## The compact witness -/

theorem norm_heatStripTransform_sub_le {u v : ℝ → ℝ} (hu : Continuous u) (hv : Continuous v)
    (hIu : Integrable (fun x => |u x| * Real.exp (|x| / 2)))
    (hIv : Integrable (fun x => |v x| * Real.exp (|x| / 2))) {z : ℂ} (hz : |z.im| ≤ 1 / 2) :
    ‖heatStripTransform (fun x => (u x : ℂ)) z - heatStripTransform (fun x => (v x : ℂ)) z‖ ≤
      ∫ x, |u x - v x| * Real.exp (|x| / 2) := by
  have hn : ∀ w : ℝ → ℝ, (fun x => ‖((w x : ℝ) : ℂ)‖ * Real.exp (|x| / 2)) =
      fun x => |w x| * Real.exp (|x| / 2) := fun w => by
    funext x; rw [Complex.norm_real, Real.norm_eq_abs]
  have hIu' : Integrable (fun x => ‖((u x : ℝ) : ℂ)‖ * Real.exp (|x| / 2)) := by rw [hn]; exact hIu
  have hIv' : Integrable (fun x => ‖((v x : ℝ) : ℂ)‖ * Real.exp (|x| / 2)) := by rw [hn]; exact hIv
  have h1 : Integrable (fun x : ℝ => ((u x : ℝ) : ℂ) * Complex.exp (I * z * x)) :=
    integrable_mul_cexp_of_strip (f := fun x => ((u x : ℝ) : ℂ))
      (Complex.continuous_ofReal.comp hu) hIu' hz
  have h2 : Integrable (fun x : ℝ => ((v x : ℝ) : ℂ) * Complex.exp (I * z * x)) :=
    integrable_mul_cexp_of_strip (f := fun x => ((v x : ℝ) : ℂ))
      (Complex.continuous_ofReal.comp hv) hIv' hz
  have e : heatStripTransform (fun x => (u x : ℂ)) z - heatStripTransform (fun x => (v x : ℂ)) z =
      heatStripTransform (fun x => ((u x - v x : ℝ) : ℂ)) z := by
    simp only [heatStripTransform]
    rw [← integral_sub h1 h2]
    congr 1; funext x; push_cast; ring
  rw [e]
  have hIuv : Integrable (fun x => ‖((u x - v x : ℝ) : ℂ)‖ * Real.exp (|x| / 2)) := by
    refine (hIu.add hIv).mono' ((Complex.continuous_ofReal.comp (hu.sub hv)).norm.mul
      (Real.continuous_exp.comp (continuous_abs.div_const 2))).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    simp only [Pi.add_apply]
    rw [← add_mul]
    exact mul_le_mul_of_nonneg_right (abs_sub _ _) (Real.exp_pos _).le
  have := norm_heatStripTransform_le hIuv hz
  simpa only [Complex.norm_real, Real.norm_eq_abs] using this

/-- **A negative even pole-free source with weighted-integrable derivative has a compactly
supported negative even pole-free cutoff.** -/
theorem exists_not_evenPoleWeilNonneg_of_source {g g' : ℝ → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hd : ∀ x, HasDerivAt g (g' x) x) (hg' : Continuous g') (heven : ∀ x, g (-x) = g x)
    (hI0 : Integrable (fun x => |g x| * Real.exp (|x| / 2)))
    (hI1 : Integrable (fun x => |g' x| * Real.exp (|x| / 2)))
    (hpole : ∫ x, g x * Real.exp (x / 2) = 0)
    (hneg : (∑' q : XiZeroCopy, heatStripTransform (fun x => (g x : ℂ)) (xiSpectralPoint q) ^ 2).re
      < 0) :
    ∃ A : ℝ, 0 < A ∧ ¬ EvenPoleWeilNonneg A := by
  have hgc := hg.continuous
  set M₀ := ∫ x, (unitCutoff : ℝ → ℝ) x * Real.exp (x / 2) with hM₀
  have hM₀0 : 0 < M₀ := unitCutoff_moment_pos
  set N₀ := ∫ x, |g x| * Real.exp (|x| / 2) with hN₀
  set N₁ := ∫ x, |g' x| * Real.exp (|x| / 2) with hN₁
  set Nχ := ∫ x, |(unitCutoff : ℝ → ℝ) x| * Real.exp (|x| / 2) with hNχ
  set Nχ' := ∫ x, |deriv (unitCutoff : ℝ → ℝ) x| * Real.exp (|x| / 2) with hNχ'
  have hN₀0 : 0 ≤ N₀ := integral_nonneg fun _ => by positivity
  have hN₁0 : 0 ≤ N₁ := integral_nonneg fun _ => by positivity
  have hNχ0 : 0 ≤ Nχ := integral_nonneg fun _ => by positivity
  have hNχ'0 : 0 ≤ Nχ' := integral_nonneg fun _ => by positivity
  obtain ⟨C₁, hC₁0, hC₁⟩ := exists_bound_deriv_unitCutoff
  -- the coefficients
  set c : ℕ → ℝ := fun k => (∫ x, (unitCutoff : ℝ → ℝ) (x / ((k : ℝ) + 1)) * g x *
    Real.exp (x / 2)) / M₀ with hc
  have hc0 : Tendsto c atTop (𝓝 0) := by
    have := (tendsto_integral_cutoff_mul hgc hI0).div_const M₀
    rw [hpole, zero_div] at this
    exact this
  have hcb : ∀ k, |c k| ≤ N₀ / M₀ := fun k => by
    rw [hc, abs_div, abs_of_pos hM₀0]
    apply div_le_div_of_nonneg_right _ hM₀0.le
    refine (abs_integral_le_integral_abs).trans (integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun _ => abs_nonneg _) hI0 (Filter.Eventually.of_forall
        fun x => ?_))
    dsimp only
    rw [abs_mul, abs_mul, abs_of_pos (Real.exp_pos _)]
    calc |(unitCutoff : ℝ → ℝ) (x / ((k : ℝ) + 1))| * |g x| * Real.exp (x / 2)
        ≤ 1 * |g x| * Real.exp (|x| / 2) := by
          gcongr
          · exact abs_unitCutoff_le _
          · exact le_abs_self x
      _ = |g x| * Real.exp (|x| / 2) := by ring
  -- the cut sources
  set u : ℕ → ℝ → ℝ := fun k => cutSource g (c k) ((k : ℝ) + 1) with hu
  have hR : ∀ k : ℕ, (1 : ℝ) ≤ (k : ℝ) + 1 := fun k => by
    have := (Nat.cast_nonneg k : (0 : ℝ) ≤ k); linarith
  have hucpt : ∀ k, HasCompactSupport (u k) := fun k => hasCompactSupport_cutSource (hR k)
  have huc : ∀ k, Continuous (u k) := fun k => (contDiff_cutSource hg _ _).continuous
  have hIu : ∀ k, Integrable (fun x => |u k x| * Real.exp (|x| / 2)) := fun k =>
    integrable_cont_compact_weight (huc k) (hucpt k)
  -- distance to `g`
  set D : ℕ → ℝ := fun k => ∫ x, |u k x - g x| * Real.exp (|x| / 2) with hD
  have hD0 : Tendsto D atTop (𝓝 0) := by
    have hT := tendsto_integral_one_sub_cutoff hgc hI0
    have hcN : Tendsto (fun k => |c k| * Nχ) atTop (𝓝 0) := by
      have := (hc0.abs).mul_const Nχ
      simpa using this
    refine squeeze_zero (fun k => integral_nonneg fun _ => by positivity) (fun k => ?_)
      (by simpa using hT.add hcN)
    exact integral_cutSource_sub_le hgc hI0 (c k) ((k : ℝ) + 1)
  -- the uniform derivative bound
  set B := C₁ * N₀ + N₁ + N₀ / M₀ * Nχ' with hB
  have hB0 : 0 ≤ B := by positivity
  have hderiv : ∀ k (z : ℂ), |z.im| ≤ 1 / 2 →
      ‖z‖ * ‖heatStripTransform (fun x => (u k x : ℂ)) z‖ ≤ B := fun k z hz => by
    have hd' : ∀ x, HasDerivAt (fun y => ((u k y : ℝ) : ℂ))
        ((cutSourceDeriv g g' (c k) ((k : ℝ) + 1) x : ℝ) : ℂ) x := fun x =>
      (hasDerivAt_cutSource hd (c k) ((k : ℝ) + 1) x).ofReal_comp
    have hcd := continuous_cutSourceDeriv hgc hg' (c k) ((k : ℝ) + 1)
    have hIu' : Integrable (fun x => ‖((u k x : ℝ) : ℂ)‖ * Real.exp (|x| / 2)) := by
      simpa only [Complex.norm_real, Real.norm_eq_abs] using hIu k
    have hIu'' : Integrable (fun x => ‖((cutSourceDeriv g g' (c k) ((k : ℝ) + 1) x : ℝ) : ℂ)‖ *
        Real.exp (|x| / 2)) := by
      simpa only [Complex.norm_real, Real.norm_eq_abs] using
        integrable_cont_compact_weight hcd (hasCompactSupport_cutSourceDeriv (hR k))
    have h := norm_mul_norm_heatStripTransform_le (Complex.continuous_ofReal.comp (huc k))
      (Complex.continuous_ofReal.comp hcd) hd' hIu' hIu'' hz
    refine h.trans ?_
    simp only [Function.comp_apply, Complex.norm_real, Real.norm_eq_abs]
    refine (integral_cutSourceDeriv_le hI0 hI1 hC₁0 hC₁ (c k) (hR k)).trans ?_
    rw [hB]
    have := mul_le_mul_of_nonneg_right (hcb k) hNχ'0
    linarith
  -- convergence of the zero sums
  set Fg : XiZeroCopy → ℂ := fun q => heatStripTransform (fun x => (g x : ℂ)) (xiSpectralPoint q)
  have hlim : Tendsto (fun k : ℕ => ∑' q : XiZeroCopy,
      heatStripTransform (fun x => (u k x : ℂ)) (xiSpectralPoint q) ^ 2) atTop
      (𝓝 (∑' q : XiZeroCopy, Fg q ^ 2)) := by
    refine tendsto_tsum_of_dominated_convergence
      (xiSpectralPoint_inv_sq_summable.mul_left (B ^ 2)) (fun q => ?_)
      (Filter.Eventually.of_forall fun k q => ?_)
    · have hz := abs_im_xiSpectralPoint_le_half q
      have hpt : Tendsto (fun k => heatStripTransform (fun x => (u k x : ℂ)) (xiSpectralPoint q))
          atTop (𝓝 (Fg q)) := by
        rw [tendsto_iff_norm_sub_tendsto_zero]
        exact squeeze_zero (fun _ => norm_nonneg _)
          (fun k => norm_heatStripTransform_sub_le (huc k) hgc (hIu k) hI0 hz) hD0
      exact hpt.pow 2
    · have hz := abs_im_xiSpectralPoint_le_half q
      have hpos : 0 < ‖xiSpectralPoint q‖ := norm_pos_iff.2 (xiSpectralPoint_ne_zero q)
      have h := hderiv k _ hz
      have h' : ‖heatStripTransform (fun x => (u k x : ℂ)) (xiSpectralPoint q)‖ ≤
          B / ‖xiSpectralPoint q‖ := by
        rw [le_div_iff₀ hpos, mul_comm]; exact h
      rw [norm_pow]
      calc ‖heatStripTransform (fun x => (u k x : ℂ)) (xiSpectralPoint q)‖ ^ 2
          ≤ (B / ‖xiSpectralPoint q‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h' 2
        _ = B ^ 2 * (1 / ‖xiSpectralPoint q‖ ^ 2) := by ring
  have hre := (Complex.continuous_re.tendsto _).comp hlim
  obtain ⟨k, hk⟩ := (hre.eventually (gt_mem_nhds hneg)).exists
  refine ⟨2 * ((k : ℝ) + 1), by positivity, fun hW => ?_⟩
  have hpole' : ∫ x, u k x * Real.exp (x / 2) = 0 := by
    show ∫ x, cutSource g (c k) ((k : ℝ) + 1) x * Real.exp (x / 2) = 0
    rw [integral_cutSource_mul_exp hgc hI0, hc]
    field_simp
    ring
  have := hW (u k) (contDiff_cutSource hg _ _) (hucpt k)
    (fun t ht => cutSource_eq_zero (hR k) ht) (cutSource_neg heven _ _) hpole'
  simp only [Function.comp_apply] at hk
  linarith

/-! ## The criteria -/

theorem abs_ofReal_norm_eq (w : ℝ → ℝ) : (fun x => ‖((w x : ℝ) : ℂ)‖ * Real.exp (|x| / 2)) =
    fun x => |w x| * Real.exp (|x| / 2) := by
  funext x; rw [Complex.norm_real, Real.norm_eq_abs]

/-- **Under RH every even real source has nonnegative zero-side energy.** -/
theorem evenPoleWeilNonneg_of_riemannHypothesis (hRH : RiemannHypothesis) (A : ℝ) :
    EvenPoleWeilNonneg A := by
  intro u hu hcpt _ heven _
  have hreal := (riemannHypothesis_iff_forall_xiSpectralPoint_im_eq_zero).1 hRH
  have hu1 : ContDiff ℝ 1 u := hu.of_le (WithTop.coe_le_coe.2 le_top)
  have hd : ∀ x, HasDerivAt u (deriv u x) x := fun x =>
    ((hu1.differentiable one_ne_zero) x).hasDerivAt
  have hcd : Continuous (deriv u) := hu.continuous_deriv (WithTop.coe_le_coe.2 le_top)
  have hI0 := integrable_cont_compact_weight hu.continuous hcpt
  have hI1 := integrable_cont_compact_weight hcd hcpt.deriv
  set N := ∫ x, |deriv u x| * Real.exp (|x| / 2) with hN
  have hbound : ∀ q : XiZeroCopy, ‖heatStripTransform (fun x => (u x : ℂ)) (xiSpectralPoint q) ^ 2‖ ≤
      N ^ 2 * (1 / ‖xiSpectralPoint q‖ ^ 2) := fun q => by
    have hz := abs_im_xiSpectralPoint_le_half q
    have hpos : 0 < ‖xiSpectralPoint q‖ := norm_pos_iff.2 (xiSpectralPoint_ne_zero q)
    have h := norm_mul_norm_heatStripTransform_le (f := fun x => ((u x : ℝ) : ℂ))
      (f' := fun x => ((deriv u x : ℝ) : ℂ)) (Complex.continuous_ofReal.comp hu.continuous)
      (Complex.continuous_ofReal.comp hcd) (fun x => (hd x).ofReal_comp)
      (by rw [abs_ofReal_norm_eq]; exact hI0) (by rw [abs_ofReal_norm_eq]; exact hI1) hz
    simp only [Complex.norm_real, Real.norm_eq_abs] at h
    have h' : ‖heatStripTransform (fun x => (u x : ℂ)) (xiSpectralPoint q)‖ ≤
        N / ‖xiSpectralPoint q‖ := by
      rw [le_div_iff₀ hpos, mul_comm]; exact h
    rw [norm_pow]
    calc ‖heatStripTransform (fun x => (u x : ℂ)) (xiSpectralPoint q)‖ ^ 2
        ≤ (N / ‖xiSpectralPoint q‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h' 2
      _ = N ^ 2 * (1 / ‖xiSpectralPoint q‖ ^ 2) := by ring
  have hsum : Summable (fun q : XiZeroCopy =>
      heatStripTransform (fun x => (u x : ℂ)) (xiSpectralPoint q) ^ 2) :=
    Summable.of_norm_bounded (xiSpectralPoint_inv_sq_summable.mul_left (N ^ 2)) hbound
  rw [Complex.re_tsum hsum]
  refine tsum_nonneg fun q => ?_
  have hz : (starRingEnd ℂ) (xiSpectralPoint q) = xiSpectralPoint q :=
    Complex.conj_eq_iff_im.2 (hreal q)
  have hc := conj_paperFT_ofReal_conj_of_even heven (xiSpectralPoint q)
  rw [hz] at hc
  have him : (heatStripTransform (fun x => (u x : ℂ)) (xiSpectralPoint q)).im = 0 :=
    Complex.conj_eq_iff_im.1 hc
  rw [sq, Complex.mul_re, him, mul_zero, sub_zero]
  exact mul_self_nonneg _

/-- **RH is even Weil positivity at every half-width.** -/
theorem riemannHypothesis_iff_forall_evenPoleWeilNonneg :
    RiemannHypothesis ↔ ∀ A : ℝ, 0 < A → EvenPoleWeilNonneg A := by
  refine ⟨fun hRH A _ => evenPoleWeilNonneg_of_riemannHypothesis hRH A, fun h => ?_⟩
  by_contra hRH
  obtain ⟨K, hK, hW⟩ : ∃ K : ℝ, 0 < K ∧ ¬ HeatWindowNonneg K := by
    by_contra hc
    push Not at hc
    exact hRH (riemannHypothesis_iff_forall_heatWindowNonneg.2 hc)
  unfold HeatWindowNonneg at hW
  rw [Filter.not_eventually] at hW
  obtain ⟨n, hn1, hnK⟩ := (hW.and_eventually (eventually_gt_atTop ⌈K⌉₊)).exists
  push Not at hn1
  obtain ⟨P, hPd, hPe, hneg⟩ := hn1
  have hn' : K < (n : ℝ) := lt_of_le_of_lt (Nat.le_ceil K) (by exact_mod_cast hnK)
  have hn0 : (0 : ℝ) < n := lt_trans hK hn'
  set a := K / n with ha_def
  have ha : 0 < a := div_pos hK hn0
  have ha1 : a < 1 := by rw [ha_def, div_lt_one hn0]; exact hn'
  have hβ : 1 / 2 < 1 / (2 * a) := by rw [lt_div_iff₀ (by positivity)]; nlinarith
  set Q := heatPolyR a P with hQ
  have hg : ContDiff ℝ (⊤ : ℕ∞) (gaussPolyFun Q (1 / (2 * a))) := contDiff_gaussPolyFun _ _
  have hI0 : Integrable (fun x => |gaussPolyFun Q (1 / (2 * a)) x| * Real.exp (|x| / 2)) := by
    rw [← abs_ofReal_norm_eq]; exact integrable_norm_ofReal_gaussPolyFun_mul_exp Q hβ
  have hI1 : Integrable (fun x => |gaussPolyFun (GaloisForLFunctions.gaussPolyDerivPoly Q
      (1 / (2 * a))) (1 / (2 * a)) x| * Real.exp (|x| / 2)) := by
    rw [← abs_ofReal_norm_eq]; exact integrable_norm_ofReal_gaussPolyFun_mul_exp _ hβ
  have hpole : ∫ x, gaussPolyFun Q (1 / (2 * a)) x * Real.exp (x / 2) = 0 :=
    integral_heatTest_mul_exp_half ha P hPe
  have hneg' : (∑' q : XiZeroCopy, heatStripTransform
      (fun x => (gaussPolyFun Q (1 / (2 * a)) x : ℂ)) (xiSpectralPoint q) ^ 2).re < 0 := by
    rw [hQ, ← heatHankel_map_eq_tsum_sq ha P]; exact hneg
  obtain ⟨A, hA, hnot⟩ := exists_not_evenPoleWeilNonneg_of_source hg
    (GaloisForLFunctions.hasDerivAt_gaussPolyFun Q (1 / (2 * a)))
    (contDiff_gaussPolyFun _ _).continuous (fun x => heatTest_neg a P x) hI0 hI1 hpole hneg'
  exact hnot (h A hA)

/-- **RH is Weil positivity on even tests at every level.** -/
theorem riemannHypothesis_iff_forall_evenHodgeIndexAtLevel :
    RiemannHypothesis ↔ ∀ a : ℝ, EvenHodgeIndexAtLevel zetaZeroConfig a := by
  constructor
  · intro hRH a
    exact evenHodgeIndexAtLevel_of_evenPoleWeilNonneg (lt_add_one a)
      (evenPoleWeilNonneg_of_riemannHypothesis hRH (a + 1))
  · intro h
    refine riemannHypothesis_iff_forall_evenPoleWeilNonneg.2 fun A hA u hu hcpt hsupp heven hpole => ?_
    have hts : tsupport (fun x => (u x : ℂ)) ⊆ Icc (-A) A := by
      refine closure_minimal (fun x hx => ?_) isClosed_Icc
      by_contra hc
      have : A < |x| := by
        rw [Set.mem_Icc, not_and_or] at hc
        rcases hc with h1 | h1
        · push Not at h1; exact lt_abs.2 (Or.inr (by linarith))
        · push Not at h1; exact lt_abs.2 (Or.inl h1)
      exact hx (by simp [hsupp x this])
    have hpole1 : paperFT (fun x => (u x : ℂ)) (I / 2) = 0 := by
      rw [paperFT_ofReal_I_half_eq_integral, ← integral_mul_exp_half_of_even heven, hpole,
        Complex.ofReal_zero]
    have hpole2 : paperFT (fun x => (u x : ℂ)) (-(I / 2)) = 0 := by
      rw [paperFT_ofReal_neg_of_even heven, hpole1]
    have hW := h A (fun x => (u x : ℂ)) (Complex.ofRealCLM.contDiff.comp
      (hu.of_le (WithTop.coe_le_coe.2 le_top))) (fun x => by simp only [heven]) hts hpole1 hpole2
    have hut : tsupport u ⊆ Ioo (-(A + 1)) (A + 1) := by
      refine (closure_minimal (s := Function.support u) (t := Icc (-A) A) (fun x hx => ?_)
        isClosed_Icc).trans (Icc_subset_Ioo (show -(A + 1) < -A by linarith)
          (show A < A + 1 by linarith))
      by_contra hc
      have : A < |x| := by
        rw [Set.mem_Icc, not_and_or] at hc
        rcases hc with h1 | h1
        · push Not at h1; exact lt_abs.2 (Or.inr (by linarith))
        · push Not at h1; exact lt_abs.2 (Or.inl h1)
      exact hx (hsupp x this)
    rw [re_W_ofReal_eq_tsum_sq hu hcpt heven (by linarith) hut] at hW
    exact hW

end

end RHTower
