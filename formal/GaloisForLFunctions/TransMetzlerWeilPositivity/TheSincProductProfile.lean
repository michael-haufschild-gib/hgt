import GaloisForLFunctions.TransMetzlerWeilPositivity.SuperGevreyCriticalGrowth

/-!
# A smooth profile that is an infinite convolution of boxes

With radii `r_0 = 1/4` and `r_{j+1} = a_j = 1/(4(j + 3) log²(j + 3))` (`sincRadius`), the profile
`sincProfile` is the uniform limit of

`boxSeq M = S_{r_M} ∘ ⋯ ∘ S_{r_0} (β_M)`,

`S_r` the Steklov average of radius `r` and `β_M` the smooth unit bump of width `a_M`
(`boxBase`). Since the bumps shrink, the limit is the infinite convolution of the normalized
boxes `(2r_j)⁻¹ 1_{[−r_j, r_j]}` alone, whose Fourier transform is the product of the `sinc`
factors; that computation lives with the Fourier analysis.

* Each derivative order is paid by one radius and the first average turns the unit mass into a
  bounded function: `|∂^q boxSeq M| ≤ 2 Π_{j<q} a_j⁻¹` for `M ≥ q`
  (`abs_iteratedDeriv_boxSeq_le`).
* Replacing the bump `β_M` by `β_{M+1}` costs `O(a_M)` after two averages, because the difference
  has mean zero and lives in `[−a_M, a_M]` (`abs_boxStek_two_le_of_meanZero`); hence every
  derivative converges uniformly (`uniformCauchySeqOn_iteratedDeriv_boxSeq`).
* The limit is smooth, vanishes off `[−1, 1]`, has unit mass and the logarithmic
  Denjoy–Carleman bound `∫ |∂^q sincProfile| ≤ 4 · 12^q q! (log(q + 3))^{2q}`
  (`integral_abs_iteratedDeriv_sincProfile_le`).
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ContDiff

namespace GaloisForLFunctions.TransMetzlerWeilPositivity

open ArithmeticElectrostatics SpacingScaleHarmonicAnalysis

/-! ### Radii and iterated averages -/

/-- Radii of the averages: `1/4`, then the Steklov radii. -/
def sincRadius : ℕ → ℝ
  | 0 => 1 / 4
  | j + 1 => steklovRadius j

theorem sincRadius_pos (j : ℕ) : 0 < sincRadius j := by
  cases j with
  | zero => norm_num [sincRadius]
  | succ j => exact steklovRadius_pos j

theorem steklovRadius_succ_le (m : ℕ) : steklovRadius (m + 1) ≤ steklovRadius m := by
  unfold steklovRadius
  have hm3 : (1 : ℝ) < (m : ℝ) + 3 := by linarith only [Nat.cast_nonneg (α := ℝ) m]
  have hl : 0 < Real.log ((m : ℝ) + 3) := Real.log_pos hm3
  have hle : Real.log ((m : ℝ) + 3) ≤ Real.log (((m + 1 : ℕ) : ℝ) + 3) :=
    Real.log_le_log (by positivity) (by push_cast; linarith)
  apply one_div_le_one_div_of_le (by positivity)
  have : ((m : ℝ) + 3) ≤ ((m + 1 : ℕ) : ℝ) + 3 := by push_cast; linarith
  exact mul_le_mul (mul_le_mul_of_nonneg_left this (by norm_num))
    (pow_le_pow_left₀ hl.le hle 2) (by positivity) (by positivity)

theorem steklovRadius_le_twelfth (m : ℕ) : steklovRadius m ≤ 1 / 12 := by
  unfold steklovRadius
  have hm3 : (3 : ℝ) ≤ (m : ℝ) + 3 := by linarith only [Nat.cast_nonneg (α := ℝ) m]
  have hl : 1 ≤ Real.log ((m : ℝ) + 3) := by
    rw [Real.le_log_iff_exp_le (by positivity)]
    have := Real.exp_one_lt_d9
    linarith
  apply one_div_le_one_div_of_le (by norm_num)
  have h1 : (1 : ℝ) ≤ Real.log ((m : ℝ) + 3) ^ 2 := one_le_pow₀ hl
  nlinarith

/-- Iterated Steklov averages of a base `β` with the radii `sincRadius`. -/
def boxStek (β : ℝ → ℝ) : ℕ → ℝ → ℝ
  | 0 => β
  | j + 1 => steklovAvg (sincRadius j) (boxStek β j)

theorem contDiff_boxStek {β : ℝ → ℝ} (hβ : ContDiff ℝ ∞ β) (m : ℕ) :
    ContDiff ℝ ∞ (boxStek β m) := by
  induction m with
  | zero => exact hβ
  | succ m ih => exact contDiff_steklovAvg ih (sincRadius_pos m)

/-- The supremum of a Steklov average is at most the `L¹` norm divided by `2a`. -/
theorem abs_steklovAvg_le_integral {f : ℝ → ℝ} (hf : Continuous f) (hfi : Integrable f)
    {a : ℝ} (ha : 0 < a) (x : ℝ) :
    |steklovAvg a f x| ≤ (2 * a)⁻¹ * ∫ y, |f y| := by
  unfold steklovAvg
  rw [abs_mul, abs_of_pos (inv_pos.mpr (by positivity : 0 < 2 * a))]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have h1 : |∫ t in (-a)..a, f (x + t)| ≤ ∫ t in (-a)..a, |f (x + t)| :=
    intervalIntegral.abs_integral_le_integral_abs (by linarith)
  have h2 : (∫ t in (-a)..a, |f (x + t)|) = ∫ u in (x + -a)..(x + a), |f u| :=
    intervalIntegral.integral_comp_add_left (fun u => |f u|) x
  have h3 : (∫ u in (x + -a)..(x + a), |f u|) ≤ ∫ u, |f u| := by
    rw [intervalIntegral.integral_of_le (by linarith)]
    exact setIntegral_le_integral hfi.abs (Eventually.of_forall fun _ => abs_nonneg _)
  linarith

/-- Steklov averages are linear in the averaged function. -/
theorem steklovAvg_sub {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g) (a : ℝ) :
    steklovAvg a (fun y => f y - g y) = fun x => steklovAvg a f x - steklovAvg a g x := by
  funext x
  simp only [steklovAvg]
  rw [intervalIntegral.integral_sub (f := fun t => f (x + t)) (g := fun t => g (x + t))
    ((hf.comp (continuous_const.add continuous_id)).intervalIntegrable _ _)
    ((hg.comp (continuous_const.add continuous_id)).intervalIntegrable _ _), mul_sub]

theorem boxStek_sub {β β' : ℝ → ℝ} (hβ : ContDiff ℝ ∞ β) (hβ' : ContDiff ℝ ∞ β') (m : ℕ) :
    boxStek (fun y => β' y - β y) m = fun x => boxStek β' m x - boxStek β m x := by
  induction m with
  | zero => rfl
  | succ m ih =>
    show steklovAvg (sincRadius m) (boxStek (fun y => β' y - β y) m) = _
    rw [ih]
    exact steklovAvg_sub (contDiff_boxStek hβ' m).continuous (contDiff_boxStek hβ m).continuous _

/-! ### Derivative bounds from a bounded level -/

/-- **Peeling.** If the `k`-th average is bounded by `B`, the `q`-th derivative of every later
average is bounded by `B Π_{k ≤ j < k+q} r_j⁻¹`: each derivative is a difference quotient of one
average. -/
theorem abs_iteratedDeriv_boxStek_le_of_level {β : ℝ → ℝ} (hβ : ContDiff ℝ ∞ β) {k : ℕ}
    {B : ℝ} (hB : ∀ x, |boxStek β k x| ≤ B) :
    ∀ m q, k + q ≤ m → ∀ x,
      |iteratedDeriv q (boxStek β m) x| ≤ B * ∏ j ∈ Finset.Ico k (k + q), (sincRadius j)⁻¹
  | 0, q, hq, x => by
      have hk : k = 0 := by omega
      have hq0 : q = 0 := by omega
      subst hk hq0
      simpa using hB x
  | m + 1, q, hq, x => by
      by_cases hle : k + q ≤ m
      · show |iteratedDeriv q (steklovAvg (sincRadius m) (boxStek β m)) x| ≤ _
        rw [iteratedDeriv_steklovAvg (contDiff_boxStek hβ m) (sincRadius_pos m) q]
        exact abs_steklovAvg_le (sincRadius_pos m)
          (abs_iteratedDeriv_boxStek_le_of_level hβ hB m q hle) x
      · have heq : k + q = m + 1 := by omega
        rcases q with _ | q
        · have hk : k = m + 1 := by omega
          subst hk
          simpa using hB x
        · have hkq : k + q = m := by omega
          show |iteratedDeriv (q + 1) (steklovAvg (sincRadius m) (boxStek β m)) x| ≤ _
          rw [iteratedDeriv_succ,
            iteratedDeriv_steklovAvg (contDiff_boxStek hβ m) (sincRadius_pos m) q]
          have hcont : Continuous (iteratedDeriv q (boxStek β m)) :=
            (contDiff_boxStek hβ m).continuous_iteratedDeriv q (natCast_le_infty q)
          have hd := abs_deriv_steklovAvg_le hcont (sincRadius_pos m)
            (abs_iteratedDeriv_boxStek_le_of_level hβ hB m q hkq.le) x
          rw [show k + (q + 1) = k + q + 1 by ring,
            Finset.prod_Ico_succ_top (by omega : k ≤ k + q), hkq]
          have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
          have hP0 : 0 ≤ ∏ j ∈ Finset.Ico k m, (sincRadius j)⁻¹ :=
            Finset.prod_nonneg fun j _ => (inv_pos.mpr (sincRadius_pos j)).le
          rw [hkq] at hd
          calc _ ≤ (sincRadius m)⁻¹ * (B * ∏ j ∈ Finset.Ico k m, (sincRadius j)⁻¹) := hd
            _ = _ := by ring

theorem prod_Ico_one_sincRadius (q : ℕ) :
    ∏ j ∈ Finset.Ico 1 (1 + q), (sincRadius j)⁻¹ = ∏ j ∈ Finset.range q, (steklovRadius j)⁻¹ := by
  rw [Finset.prod_Ico_eq_prod_range, show 1 + q - 1 = q by omega]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [show 1 + j = j + 1 by ring]
  rfl

/-- The first average of a base of `L¹` norm at most one is bounded by `2`. -/
theorem abs_boxStek_one_le {β : ℝ → ℝ} (hβ : Continuous β) (hβi : Integrable β)
    (hβ1 : ∫ y, |β y| ≤ 1) (x : ℝ) : |boxStek β 1 x| ≤ 2 := by
  have h := abs_steklovAvg_le_integral hβ hβi (sincRadius_pos 0) x
  have hr : (2 * sincRadius 0)⁻¹ = 2 := by norm_num [sincRadius]
  rw [hr] at h
  show |steklovAvg (sincRadius 0) β x| ≤ 2
  linarith

/-- `|∂^q (S^{m} β)| ≤ 2 Π_{j<q} a_j⁻¹` for `m ≥ q + 1`. -/
theorem abs_iteratedDeriv_boxStek_le {β : ℝ → ℝ} (hβ : ContDiff ℝ ∞ β) (hβi : Integrable β)
    (hβ1 : ∫ y, |β y| ≤ 1) {m q : ℕ} (hqm : q + 1 ≤ m) (x : ℝ) :
    |iteratedDeriv q (boxStek β m) x| ≤ 2 * ∏ j ∈ Finset.range q, (steklovRadius j)⁻¹ := by
  rw [← prod_Ico_one_sincRadius]
  exact abs_iteratedDeriv_boxStek_le_of_level hβ (abs_boxStek_one_le hβ.continuous hβi hβ1)
    m q (by omega) x

/-! ### A mean-zero base costs its width after two averages -/

/-- If `h` has mean zero, `L¹` norm at most `2` and vanishes for `|u| ≥ e`, then
`|S_{a_0} S_{1/4} h| ≤ 8e/a_0`: the first average is the difference of two translates of the
primitive of `h`, which lives in `[−e, e]` and is bounded by `2`. -/
theorem abs_boxStek_two_le_of_meanZero {h : ℝ → ℝ} (hh : Continuous h) {e : ℝ} (he : 0 ≤ e)
    (hzero : ∀ u, e ≤ |u| → h u = 0) (hmean : ∫ u, h u = 0) (hL1 : ∫ u, |h u| ≤ 2) (x : ℝ) :
    |boxStek h 2 x| ≤ 8 * e / steklovRadius 0 := by
  have hhi : Integrable h := hh.integrable_of_hasCompactSupport
    (HasCompactSupport.intro (isCompact_Icc (a := -e) (b := e)) fun u hu => hzero u (by
      simp only [Set.mem_Icc, not_and_or, not_le] at hu
      rcases hu with hu | hu
      · rw [abs_of_neg (by linarith)]; linarith
      · rw [abs_of_pos (by linarith)]; linarith))
  -- the primitive `H(y) = ∫_{−e}^y h`
  set H : ℝ → ℝ := fun y => ∫ u in (-e)..y, h u with hHdef
  have hHc : Continuous H :=
    continuous_iff_continuousAt.mpr fun y =>
      (intervalIntegral.integral_hasDerivAt_right (hh.intervalIntegrable _ _)
        (hh.stronglyMeasurableAtFilter volume (𝓝 y)) hh.continuousAt).continuousAt
  have hfull : (∫ u in (-e)..e, h u) = 0 := by
    have hset : ∫ u in Set.Ioc (-e) e, h u = ∫ u, h u :=
      setIntegral_eq_integral_of_forall_compl_eq_zero fun u hu => by
        simp only [Set.mem_Ioc, not_and_or, not_lt, not_le] at hu
        refine hzero u ?_
        rcases hu with hu | hu
        · exact (by linarith : e ≤ -u).trans (neg_le_abs u)
        · exact hu.le.trans (le_abs_self u)
    rw [intervalIntegral.integral_of_le (by linarith), hset, hmean]
  have hHzero : ∀ y, e ≤ |y| → H y = 0 := by
    intro y hy
    rcases le_or_gt y 0 with hy0 | hy0
    · have hye : y ≤ -e := by rw [abs_of_nonpos hy0] at hy; linarith
      show (∫ u in (-e)..y, h u) = 0
      rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) fun u hu => hzero u (by
        rw [Set.uIcc_of_ge hye] at hu
        exact (by linarith [hu.2] : e ≤ -u).trans (neg_le_abs u)),
        intervalIntegral.integral_zero]
    · have hye : e ≤ y := by rw [abs_of_pos hy0] at hy; exact hy
      show (∫ u in (-e)..y, h u) = 0
      rw [← intervalIntegral.integral_add_adjacent_intervals (hh.intervalIntegrable (-e) e)
        (hh.intervalIntegrable e y), hfull, zero_add,
        intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) fun u hu => hzero u (by
          rw [Set.uIcc_of_le hye] at hu
          exact hu.1.trans (le_abs_self u)),
        intervalIntegral.integral_zero]
  have hHb : ∀ y, |H y| ≤ 2 := by
    intro y
    have h1 := intervalIntegral.norm_integral_le_abs_integral_norm (a := -e) (b := y) (f := h)
      (μ := volume)
    simp only [Real.norm_eq_abs] at h1
    have h2 : abs (∫ u in (-e)..y, |h u|) ≤ ∫ u, |h u| := by
      rcases le_total (-e) y with hle | hle
      · rw [intervalIntegral.integral_of_le hle, abs_of_nonneg (integral_nonneg fun _ =>
          abs_nonneg _)]
        exact setIntegral_le_integral hhi.abs (Eventually.of_forall fun _ => abs_nonneg _)
      · rw [intervalIntegral.integral_symm, intervalIntegral.integral_of_le hle, abs_neg,
          abs_of_nonneg (integral_nonneg fun _ => abs_nonneg _)]
        exact setIntegral_le_integral hhi.abs (Eventually.of_forall fun _ => abs_nonneg _)
    exact h1.trans (h2.trans hL1)
  have hHsupp : SupportedIn e H := fun y hy => hHzero y hy.le
  have hHcs : HasCompactSupport H := hasCompactSupport_of_vanishes hHsupp
  have hHL1 : ∫ y, |H y| ≤ 4 * e := by
    have := integral_abs_le_of_bound hHc hHcs hHb hHsupp he
    linarith
  -- the first average is a difference of translates of `H`
  have hS1 : boxStek h 1 = fun y => 2 * (H (y + 1 / 4) - H (y - 1 / 4)) := by
    funext y
    show steklovAvg (sincRadius 0) h y = _
    unfold steklovAvg
    have hr : sincRadius 0 = 1 / 4 := rfl
    rw [hr, intervalIntegral.integral_comp_add_left (fun u => h u) y,
      ← intervalIntegral.integral_interval_sub_left (hh.intervalIntegrable (-e) (y + 1 / 4))
        (hh.intervalIntegrable (-e) (y + -(1 / 4)))]
    norm_num [hHdef]
    ring
  set g : ℝ → ℝ := fun y => 2 * (H (y + 1 / 4) - H (y - 1 / 4)) with hgdef
  have hgc : Continuous g := by
    simp only [hgdef]
    fun_prop
  have hgi : Integrable g := by
    have h1 : Integrable fun y => H (y + 1 / 4) :=
      (hHc.integrable_of_hasCompactSupport hHcs).comp_add_right (1 / 4)
    have h2 : Integrable fun y => H (y - 1 / 4) :=
      (hHc.integrable_of_hasCompactSupport hHcs).comp_sub_right (1 / 4)
    exact (h1.sub h2).const_mul 2
  have hgL1 : ∫ y, |g y| ≤ 16 * e := by
    have h1 : Integrable fun y => |H (y + 1 / 4)| :=
      ((hHc.integrable_of_hasCompactSupport hHcs).comp_add_right (1 / 4)).abs
    have h2 : Integrable fun y => |H (y - 1 / 4)| :=
      ((hHc.integrable_of_hasCompactSupport hHcs).comp_sub_right (1 / 4)).abs
    have hle : ∫ y, |g y| ≤ ∫ y, (2 * |H (y + 1 / 4)| + 2 * |H (y - 1 / 4)|) := by
      refine integral_mono hgi.abs ((h1.const_mul 2).add (h2.const_mul 2)) fun y => ?_
      simp only [hgdef, abs_mul, abs_two]
      have := abs_sub (H (y + 1 / 4)) (H (y - 1 / 4))
      linarith
    rw [integral_add (h1.const_mul 2) (h2.const_mul 2), integral_const_mul, integral_const_mul,
      integral_add_right_eq_self (fun y => |H y|), integral_sub_right_eq_self (fun y => |H y|)]
      at hle
    linarith
  have hS2 : boxStek h 2 x = steklovAvg (sincRadius 1) g x := by
    show steklovAvg (sincRadius 1) (boxStek h 1) x = _
    rw [hS1]
  rw [hS2]
  have hb := abs_steklovAvg_le_integral hgc hgi (sincRadius_pos 1) x
  have hr1 : sincRadius 1 = steklovRadius 0 := rfl
  rw [hr1] at hb
  have ha0 := steklovRadius_pos 0
  calc |steklovAvg (sincRadius 1) g x| ≤ (2 * steklovRadius 0)⁻¹ * ∫ y, |g y| := hb
    _ ≤ (2 * steklovRadius 0)⁻¹ * (16 * e) := mul_le_mul_of_nonneg_left hgL1 (by positivity)
    _ = 8 * e / steklovRadius 0 := by field_simp; ring

/-! ### The approximating sequence -/

/-- Unit bump of width `a_M`: `steklovBase` dilated by `a_M⁻¹`, supported in `[−a_M/2, a_M/2]`. -/
def boxBase (M : ℕ) : ℝ → ℝ := dilate (steklovRadius M)⁻¹ steklovBase

theorem steklovBase_nonneg (x : ℝ) : 0 ≤ steklovBase x := by
  unfold steklovBase dilate dcProfile dcBump
  have h0 : 0 ≤ (∫ y, dcBump 1 y)⁻¹ := inv_nonneg.mpr (integral_dcBump_pos odd_one).le
  have h1 := glueR_nonneg (r := 1) (1 + 2 * x)
  have h2 := glueR_nonneg (r := 1) (1 - 2 * x)
  positivity

theorem contDiff_boxBase (M : ℕ) : ContDiff ℝ ∞ (boxBase M) :=
  contDiff_dilate_smooth contDiff_steklovBase _

theorem boxBase_eq_zero {M : ℕ} {u : ℝ} (hu : steklovRadius M / 2 < |u|) : boxBase M u = 0 := by
  have ha := steklovRadius_pos M
  unfold boxBase dilate
  rw [supportedIn_steklovBase _ (by
    rw [abs_mul, abs_of_pos (inv_pos.mpr ha)]
    rw [div_lt_iff₀ (by norm_num : (0 : ℝ) < 2)] at hu
    rw [lt_inv_mul_iff₀ ha]
    linarith), mul_zero]

theorem integral_boxBase (M : ℕ) : ∫ x, boxBase M x = 1 := by
  rw [boxBase, integral_dilate (inv_pos.mpr (steklovRadius_pos M)), integral_steklovBase]

theorem integral_abs_boxBase (M : ℕ) : ∫ x, |boxBase M x| = 1 := by
  rw [boxBase, integral_abs_dilate (inv_pos.mpr (steklovRadius_pos M))]
  simp_rw [abs_of_nonneg (steklovBase_nonneg _)]
  exact integral_steklovBase

theorem integrable_boxBase (M : ℕ) : Integrable (boxBase M) :=
  (contDiff_boxBase M).continuous.integrable_of_hasCompactSupport
    (hasCompactSupport_of_vanishes fun _ hu => boxBase_eq_zero hu)

/-- The approximants `S_{r_M} ⋯ S_{r_0} β_M`. -/
def boxSeq (M : ℕ) : ℝ → ℝ := boxStek (boxBase M) (M + 1)

theorem contDiff_boxSeq (M : ℕ) : ContDiff ℝ ∞ (boxSeq M) :=
  contDiff_boxStek (contDiff_boxBase M) (M + 1)

theorem abs_iteratedDeriv_boxSeq_le {M q : ℕ} (hqM : q ≤ M) (x : ℝ) :
    |iteratedDeriv q (boxSeq M) x| ≤ 2 * ∏ j ∈ Finset.range q, (steklovRadius j)⁻¹ :=
  abs_iteratedDeriv_boxStek_le (contDiff_boxBase M) (integrable_boxBase M)
    (integral_abs_boxBase M).le (by omega) x

/-- One step of the sequence moves the `q`-th derivative by `C_q a_M`. -/
theorem abs_iteratedDeriv_boxSeq_step_le {q M : ℕ} (hqM : q + 1 ≤ M) (x : ℝ) :
    |iteratedDeriv q (boxSeq (M + 1)) x - iteratedDeriv q (boxSeq M) x| ≤
      (2 * ∏ j ∈ Finset.range (q + 1), (steklovRadius j)⁻¹ +
        8 / steklovRadius 0 * ∏ j ∈ Finset.Ico 2 (2 + q), (sincRadius j)⁻¹) *
        steklovRadius M := by
  set β := boxBase M
  set β' := boxBase (M + 1)
  have hβ := contDiff_boxBase M
  have hβ' := contDiff_boxBase (M + 1)
  set g := boxStek β' (M + 1)
  have hg : ContDiff ℝ ∞ g := contDiff_boxStek hβ' (M + 1)
  have hsplit : iteratedDeriv q (boxSeq (M + 1)) x - iteratedDeriv q (boxSeq M) x =
      (steklovAvg (steklovRadius M) (iteratedDeriv q g) x - iteratedDeriv q g x) +
        iteratedDeriv q (boxStek (fun y => β' y - β y) (M + 1)) x := by
    have h1 : boxSeq (M + 1) = steklovAvg (steklovRadius M) g := rfl
    have h2 : boxSeq M = boxStek β (M + 1) := rfl
    have h3 : iteratedDeriv q (boxStek (fun y => β' y - β y) (M + 1)) x =
        iteratedDeriv q g x - iteratedDeriv q (boxStek β (M + 1)) x := by
      rw [boxStek_sub hβ hβ' (M + 1)]
      show iteratedDeriv q (boxStek β' (M + 1) - boxStek β (M + 1)) x = _
      exact iteratedDeriv_sub ((contDiff_boxStek hβ' (M + 1)).contDiffAt.of_le
        (natCast_le_infty q)) ((contDiff_boxStek hβ (M + 1)).contDiffAt.of_le (natCast_le_infty q))
    rw [h1, iteratedDeriv_steklovAvg hg (steklovRadius_pos M) q, h2, h3]
    ring
  rw [hsplit]
  -- the new average
  have hgq : ContDiff ℝ ∞ (iteratedDeriv q g) := by
    rw [iteratedDeriv_eq_iterate]; exact hg.iterate_deriv q
  have h1 : |steklovAvg (steklovRadius M) (iteratedDeriv q g) x - iteratedDeriv q g x| ≤
      (2 * ∏ j ∈ Finset.range (q + 1), (steklovRadius j)⁻¹) * steklovRadius M := by
    refine abs_steklovAvg_sub_self_le hgq (steklovRadius_pos M) (fun y => ?_) x
    rw [← iteratedDeriv_succ]
    exact abs_iteratedDeriv_boxStek_le hβ' (integrable_boxBase (M + 1))
      (integral_abs_boxBase (M + 1)).le (by omega) y
  -- the change of base
  have hmono := steklovRadius_succ_le M
  have ha := steklovRadius_pos M
  have hdiff_zero : ∀ u, steklovRadius M ≤ |u| → β' u - β u = 0 := by
    intro u hu
    show boxBase (M + 1) u - boxBase M u = 0
    rw [boxBase_eq_zero (M := M + 1) (u := u) (by linarith),
      boxBase_eq_zero (M := M) (u := u) (by linarith), sub_zero]
  have hdiff_mean : ∫ u, (β' u - β u) = 0 := by
    rw [integral_sub (integrable_boxBase (M + 1)) (integrable_boxBase M), integral_boxBase,
      integral_boxBase, sub_self]
  have hdiff_L1 : ∫ u, |β' u - β u| ≤ 2 := by
    have hle : ∫ u, |β' u - β u| ≤ ∫ u, (|β' u| + |β u|) :=
      integral_mono (((integrable_boxBase (M + 1)).sub (integrable_boxBase M)).abs)
        ((integrable_boxBase (M + 1)).abs.add (integrable_boxBase M).abs) fun u => abs_sub _ _
    rw [integral_add (integrable_boxBase (M + 1)).abs (integrable_boxBase M).abs,
      integral_abs_boxBase, integral_abs_boxBase] at hle
    linarith
  have hlevel := abs_boxStek_two_le_of_meanZero (hβ'.continuous.sub hβ.continuous) ha.le
    hdiff_zero hdiff_mean hdiff_L1
  have h2 := abs_iteratedDeriv_boxStek_le_of_level (hβ'.sub hβ) hlevel (M + 1) q (by omega) x
  calc _ ≤ |steklovAvg (steklovRadius M) (iteratedDeriv q g) x - iteratedDeriv q g x| +
        |iteratedDeriv q (boxStek (fun y => β' y - β y) (M + 1)) x| := abs_add_le _ _
    _ ≤ (2 * ∏ j ∈ Finset.range (q + 1), (steklovRadius j)⁻¹) * steklovRadius M +
        8 * steklovRadius M / steklovRadius 0 * ∏ j ∈ Finset.Ico 2 (2 + q), (sincRadius j)⁻¹ :=
        add_le_add h1 h2
    _ = _ := by ring

theorem uniformCauchySeqOn_iteratedDeriv_boxSeq (q : ℕ) :
    UniformCauchySeqOn (fun M => iteratedDeriv q (boxSeq M)) atTop Set.univ := by
  rw [Metric.uniformCauchySeqOn_iff]
  intro ε hε
  set C := 2 * ∏ j ∈ Finset.range (q + 1), (steklovRadius j)⁻¹ +
    8 / steklovRadius 0 * ∏ j ∈ Finset.Ico 2 (2 + q), (sincRadius j)⁻¹
  have hC0 : 0 ≤ C := by
    have h1 : 0 ≤ ∏ j ∈ Finset.range (q + 1), (steklovRadius j)⁻¹ :=
      Finset.prod_nonneg fun j _ => (inv_pos.mpr (steklovRadius_pos j)).le
    have h2 : 0 ≤ ∏ j ∈ Finset.Ico 2 (2 + q), (sincRadius j)⁻¹ :=
      Finset.prod_nonneg fun j _ => (inv_pos.mpr (sincRadius_pos j)).le
    have := steklovRadius_pos 0
    positivity
  have hsub : ∀ K L : ℕ, q + 1 ≤ K → K ≤ L → ∀ x,
      |iteratedDeriv q (boxSeq L) x - iteratedDeriv q (boxSeq K) x| ≤
        C / (4 * Real.log ((K : ℝ) + 2)) := by
    intro K L hqK hKL x
    have htel : iteratedDeriv q (boxSeq L) x - iteratedDeriv q (boxSeq K) x =
        ∑ m ∈ Finset.Ico K L,
          (iteratedDeriv q (boxSeq (m + 1)) x - iteratedDeriv q (boxSeq m) x) :=
      (Finset.sum_Ico_sub (fun m => iteratedDeriv q (boxSeq m) x) hKL).symm
    calc _ ≤ ∑ m ∈ Finset.Ico K L,
            |iteratedDeriv q (boxSeq (m + 1)) x - iteratedDeriv q (boxSeq m) x| := by
          rw [htel]; exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ m ∈ Finset.Ico K L, C * steklovRadius m :=
          Finset.sum_le_sum fun m hm =>
            abs_iteratedDeriv_boxSeq_step_le (hqK.trans (Finset.mem_Ico.mp hm).1) x
      _ = C * ∑ m ∈ Finset.Ico K L, steklovRadius m := (Finset.mul_sum _ _ _).symm
      _ ≤ C * (1 / (4 * Real.log ((K : ℝ) + 2))) :=
          mul_le_mul_of_nonneg_left (sum_Ico_steklovRadius_le hKL) hC0
      _ = C / (4 * Real.log ((K : ℝ) + 2)) := by ring
  have htend : Tendsto (fun K : ℕ => C / (4 * Real.log ((K : ℝ) + 2))) atTop (𝓝 0) := by
    have hlog : Tendsto (fun K : ℕ => 4 * Real.log ((K : ℝ) + 2)) atTop atTop :=
      (Real.tendsto_log_atTop.comp
        (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)).const_mul_atTop (by norm_num)
    exact tendsto_const_nhds.div_atTop hlog
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp (htend.eventually (gt_mem_nhds (half_pos hε)))
  refine ⟨max N₀ (q + 1), fun n hn m hm x _ => ?_⟩
  set K := max N₀ (q + 1)
  have hqK : q + 1 ≤ K := le_max_right _ _
  have hKlt : C / (4 * Real.log ((K : ℝ) + 2)) < ε / 2 := hN₀ K (le_max_left _ _)
  have hn' := hsub K n hqK hn x
  have hm' := hsub K m hqK hm x
  rw [Real.dist_eq]
  have htri := abs_sub (iteratedDeriv q (boxSeq n) x - iteratedDeriv q (boxSeq K) x)
    (iteratedDeriv q (boxSeq m) x - iteratedDeriv q (boxSeq K) x)
  rw [sub_sub_sub_cancel_right] at htri
  linarith

/-! ### The limit profile -/

/-- Uniform limits of the derivatives of `boxSeq`. -/
def sincDerivLimit (q : ℕ) : ℝ → ℝ :=
  Classical.choose (HTGeometry.exists_tendstoUniformly_of_uniformCauchySeq
    (uniformCauchySeqOn_iteratedDeriv_boxSeq q))

theorem tendstoUniformly_sincDerivLimit (q : ℕ) :
    TendstoUniformly (fun M => iteratedDeriv q (boxSeq M)) (sincDerivLimit q) atTop :=
  Classical.choose_spec (HTGeometry.exists_tendstoUniformly_of_uniformCauchySeq
    (uniformCauchySeqOn_iteratedDeriv_boxSeq q))

/-- **The sinc-product profile**: the uniform limit of `boxSeq`. -/
def sincProfile : ℝ → ℝ := sincDerivLimit 0

theorem tendstoUniformly_boxSeq : TendstoUniformly boxSeq sincProfile atTop := by
  have h := tendstoUniformly_sincDerivLimit 0
  simp only [iteratedDeriv_zero] at h
  exact h

theorem contDiff_sincProfile : ContDiff ℝ ∞ sincProfile :=
  HTGeometry.contDiff_infty_of_tendstoUniformly_iteratedDeriv
    contDiff_boxSeq tendstoUniformly_sincDerivLimit

theorem iteratedDeriv_sincProfile_eq (q : ℕ) :
    iteratedDeriv q sincProfile = sincDerivLimit q :=
  HTGeometry.iteratedDeriv_eq_of_tendstoUniformly_iteratedDeriv
    contDiff_boxSeq tendstoUniformly_sincDerivLimit q

theorem supportedIn_boxStek {β : ℝ → ℝ} {R : ℝ} (hβ : SupportedIn R β) (m : ℕ) :
    SupportedIn (R + ∑ j ∈ Finset.range m, sincRadius j) (boxStek β m) := by
  induction m with
  | zero =>
    show SupportedIn (R + ∑ j ∈ Finset.range 0, sincRadius j) β
    simpa using hβ
  | succ m ih =>
    rw [Finset.sum_range_succ, ← add_assoc]
    exact supportedIn_steklovAvg (sincRadius_pos m) ih

theorem sum_range_sincRadius_le (m : ℕ) : ∑ j ∈ Finset.range (m + 1), sincRadius j ≤ 3 / 4 := by
  rw [Finset.sum_range_succ']
  have h : ∑ j ∈ Finset.range m, sincRadius (j + 1) ≤ 1 / 2 :=
    (Finset.sum_congr rfl fun j _ => rfl).trans_le (sum_range_steklovRadius_le_half m)
  have h0 : sincRadius 0 = 1 / 4 := rfl
  linarith

theorem supportedIn_boxSeq (M : ℕ) : SupportedIn 1 (boxSeq M) := by
  have hβ : SupportedIn (steklovRadius M / 2) (boxBase M) := fun u hu => boxBase_eq_zero hu
  have hs := supportedIn_boxStek hβ (M + 1)
  have h1 := sum_range_sincRadius_le M
  have h2 := steklovRadius_le_twelfth M
  intro x hx
  exact hs x (by linarith)

theorem sincProfile_vanishesOff : VanishesOff sincProfile := by
  intro x hx
  exact HTGeometry.eq_zero_of_tendsto_of_forall_eq_zero (J := Set.Icc (-1 : ℝ) 1)
    (fun y => tendstoUniformly_boxSeq.tendsto_at y)
    (fun M y hy => supportedIn_boxSeq M y (by
      simp only [Set.mem_Icc, not_and_or, not_le] at hy
      rcases hy with h | h
      · rw [abs_of_neg (by linarith)]; linarith
      · rw [abs_of_pos (by linarith)]; linarith))
    (by
      intro hmem
      have := abs_le.mpr hmem
      linarith)

theorem integral_boxStek {β : ℝ → ℝ} (hβ : ContDiff ℝ ∞ β) {R : ℝ} (hR : 0 ≤ R)
    (hsupp : SupportedIn R β) (m : ℕ) : ∫ x, boxStek β m x = ∫ x, β x := by
  induction m with
  | zero => rfl
  | succ m ih =>
    have hR' : 0 ≤ R + ∑ j ∈ Finset.range m, sincRadius j :=
      add_nonneg hR (Finset.sum_nonneg fun j _ => (sincRadius_pos j).le)
    show ∫ x, steklovAvg (sincRadius m) (boxStek β m) x = _
    rw [integral_steklovAvg (contDiff_boxStek hβ m).continuous (supportedIn_boxStek hsupp m) hR'
      (sincRadius_pos m), ih]

theorem integral_boxSeq (M : ℕ) : ∫ x, boxSeq M x = 1 := by
  rw [boxSeq, integral_boxStek (contDiff_boxBase M) (by linarith [steklovRadius_pos M])
    (fun u hu => boxBase_eq_zero hu) (M + 1), integral_boxBase]

theorem integral_sincProfile : ∫ x, sincProfile x = 1 := by
  have hcs : ∀ M, HasCompactSupport (boxSeq M) := fun M =>
    hasCompactSupport_of_vanishes (supportedIn_boxSeq M)
  have hcs' : HasCompactSupport sincProfile := hasCompactSupport_of_vanishes sincProfile_vanishesOff
  have hint : Tendsto (fun M => ∫ x, boxSeq M x) atTop (𝓝 (∫ x, sincProfile x)) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    have hunif := Metric.tendstoUniformly_iff.mp tendstoUniformly_boxSeq (ε / 4) (by positivity)
    filter_upwards [hunif] with M hM
    rw [Real.dist_eq, ← integral_sub ((contDiff_boxSeq M).continuous.integrable_of_hasCompactSupport
      (hcs M)) (contDiff_sincProfile.continuous.integrable_of_hasCompactSupport hcs')]
    have hd : Continuous fun x => boxSeq M x - sincProfile x :=
      (contDiff_boxSeq M).continuous.sub contDiff_sincProfile.continuous
    have hdR : SupportedIn 1 fun x => boxSeq M x - sincProfile x := fun x hx => by
      simp only [supportedIn_boxSeq M x hx, sincProfile_vanishesOff x hx, sub_zero]
    have hb := integral_abs_le_of_bound hd (hasCompactSupport_of_vanishes hdR)
      (fun x => by
        have := hM x
        rw [Real.dist_eq, abs_sub_comm] at this
        exact this.le) hdR zero_le_one
    calc |∫ x, (boxSeq M x - sincProfile x)| ≤ ∫ x, |boxSeq M x - sincProfile x| :=
          abs_integral_le_integral_abs
      _ ≤ 2 * 1 * (ε / 4) := hb
      _ < ε := by linarith
  have hconst : Tendsto (fun M => ∫ x, boxSeq M x) atTop (𝓝 1) := by
    simp_rw [integral_boxSeq]; exact tendsto_const_nhds
  exact tendsto_nhds_unique hint hconst

theorem abs_iteratedDeriv_sincProfile_le (q : ℕ) (x : ℝ) :
    |iteratedDeriv q sincProfile x| ≤ 2 * 12 ^ q * dcLogWeight q := by
  have hpt : Tendsto (fun M => |iteratedDeriv q (boxSeq M) x|) atTop
      (𝓝 |iteratedDeriv q sincProfile x|) := by
    rw [iteratedDeriv_sincProfile_eq q]
    exact ((tendstoUniformly_sincDerivLimit q).tendsto_at x).abs
  refine le_of_tendsto hpt ?_
  filter_upwards [eventually_ge_atTop q] with M hqM
  calc |iteratedDeriv q (boxSeq M) x| ≤ 2 * ∏ j ∈ Finset.range q, (steklovRadius j)⁻¹ :=
        abs_iteratedDeriv_boxSeq_le hqM x
    _ ≤ 2 * (12 ^ q * dcLogWeight q) :=
        mul_le_mul_of_nonneg_left (prod_inv_steklovRadius_le q) (by norm_num)
    _ = 2 * 12 ^ q * dcLogWeight q := by ring

/-- **Logarithmic Denjoy–Carleman class**: `∫ |∂^q sincProfile| ≤ 4 · 12^q q! (log(q + 3))^{2q}`. -/
theorem integral_abs_iteratedDeriv_sincProfile_le (q : ℕ) :
    ∫ t, |iteratedDeriv q sincProfile t| ≤ 4 * 12 ^ q * dcLogWeight q := by
  have hd : Continuous (iteratedDeriv q sincProfile) :=
    contDiff_sincProfile.continuous_iteratedDeriv q (natCast_le_infty q)
  have hvan : ∀ t, t ∉ Set.Icc (-1 : ℝ) 1 → sincProfile t = 0 := fun t ht =>
    sincProfile_vanishesOff t (by
      simp only [Set.mem_Icc, not_and_or, not_le] at ht
      rcases ht with h | h
      · rw [abs_of_neg (by linarith)]; linarith
      · rw [abs_of_pos (by linarith)]; linarith)
  have hdR : SupportedIn 1 (iteratedDeriv q sincProfile) := fun t ht =>
    iteratedDeriv_eq_zero_of_vanish hvan q fun h => by
      have := abs_le.mpr ⟨h.1, h.2⟩; linarith
  have hbound := integral_abs_le_of_bound hd (hasCompactSupport_of_vanishes hdR)
    (abs_iteratedDeriv_sincProfile_le q) hdR zero_le_one
  linarith

end GaloisForLFunctions.TransMetzlerWeilPositivity
