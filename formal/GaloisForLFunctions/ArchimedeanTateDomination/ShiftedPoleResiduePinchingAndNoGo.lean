import GaloisForLFunctions.ArchimedeanTateDomination.UnshiftedImpossibilityAndHorizonCollapse
import GaloisForLFunctions.RHTower.BurnolMoebiusLine
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Shifted-pole residue pinching and global no-go across all pole weights

Even when the pole form `windowPoleForm` is replaced by its dimension-`k` Tate-shifted counterpart
`shiftedPoleForm k H = 2 (∫ H(u) e^{(1/2+k)u} du)(∫ H(u) e^{-(1/2+k)u} du)` — which grows like
`e^{k A}` on wide windows and satisfies `∂_k (k · shiftedPoleForm k H)|_{k=0} = windowPoleForm H` —
no archimedean combination `A_k = Γ_k + φ(k) · shiftedPoleForm k` can dominate `tatePointCount A H k`
across all windows `{W_A}_{A ≥ 0}`:

* **Dirichlet hyperbola asymptotic** (`abs_tatePointCount_sub_eulerProduct_shiftedPoleForm_le`):
  for every `k ∈ (0, 1)` and `C²` window test `H` with `|H(w)|, |H'(w)| ≤ K e^{w/2}`,
  `|tatePointCount A H k − (1 / ζ(1 + k)) · shiftedPoleForm k H| ≤ C_k K² (A + 1)²`.
* **Two-sided residue pinching** (`shiftedPole_weight_pinched_eq_eulerProduct`): testing on both
  positive-pole (`H_+`) and negative-pole (`H_-`) wide harmonic plateaus forces any dominating
  shifted-pole weight `φ` to equal `eulerProductPoleWeight k = 1 / ζ(1 + k)` — an Euler-product
  quantity strictly smaller than the archimedean weight `k` (`eulerProductPoleWeight_lt_self`).
* **Refutation of `φ = 1 / ζ(1 + k)` and all `φ ∈ ℝ`** (`four_mul_riemannPhiTransform_sq_lt_mul_zeta`,
  `not_exists_shiftedPole_weight_domination_linear`,
  `not_exists_shiftedPole_weight_domination_backwardTateGamma`,
  `not_exists_shiftedPole_weight_domination_symTateGamma`): on `windowRiemannKernel A`,
  `4 ξ(1 + k)² < k ζ(1 + k)` makes `(1 / ζ(1 + k)) · shiftedPoleForm k H_A − k · windowPoleForm H_A`
  strictly negative for large `A`, refuting every `φ ≤ 1 / ζ(1 + k)` while `H_-` refutes every
  `φ > 1 / ζ(1 + k)`.
-/

noncomputable section

open MeasureTheory Set Filter Topology Complex
open scoped BigOperators

namespace GaloisForLFunctions.ArchimedeanTateDomination

open CohomologyOfWindowsOfSpecZ WindowTowerOfSpecZ SpacingScaleHarmonicAnalysis
open ArithmeticDegenerationTheory _root_.RHTower _root_.RHTower.WeilMarkovPole

/-! ### The Tate-shifted pole form and its dimension-zero jet -/

/-- The dimension-`k` Tate-shifted pole form `2 (∫ H(u) e^{(1/2+k)u} du)(∫ H(u) e^{-(1/2+k)u} du)`. -/
def shiftedPoleForm (k : ℝ) (H : ℝ → ℝ) : ℝ :=
  2 * ((∫ u, H u * Real.exp ((1 / 2 + k) * u)) * ∫ u, H u * Real.exp (-(1 / 2 + k) * u))

/-- At `k = 0`, `shiftedPoleForm 0 H` coincides with `windowPoleForm H`. -/
theorem shiftedPoleForm_zero {A : ℝ} {H : ℝ → ℝ} (hH : IsWindowTest A H) :
    shiftedPoleForm 0 H = windowPoleForm H := by
  rw [windowPoleForm_eq_exp_prod hH]
  unfold shiftedPoleForm
  congr 1
  congr 1
  · refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    exact congrArg (fun x => H u * Real.exp x) (by ring)
  · refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    exact congrArg (fun x => H u * Real.exp x) (by ring)

private theorem continuousAt_integral_mul_exp {A : ℝ} (_ : 0 ≤ A) {H : ℝ → ℝ}
    (hH : IsWindowTest A H) (sgn : ℝ) (hsgn : |sgn| ≤ 1) :
    ContinuousAt (fun k : ℝ => ∫ u, H u * Real.exp (sgn * (1 / 2 + k) * u)) 0 := by
  set B : ℝ → ℝ := Set.indicator (Icc (-A) 0) fun u => |H u| * Real.exp (3 / 2 * A)
  have hB_int : Integrable B := by
    have hc : Continuous fun u => |H u| * Real.exp (3 / 2 * A) :=
      hH.continuous.abs.mul continuous_const
    exact hc.integrableOn_Icc.integrable_indicator measurableSet_Icc
  refine MeasureTheory.continuousAt_of_dominated ?_ ?_ hB_int ?_
  · exact Eventually.of_forall fun k =>
      (hH.continuous.mul (by fun_prop : Continuous fun u : ℝ =>
        Real.exp (sgn * (1 / 2 + k) * u))).aestronglyMeasurable
  · filter_upwards [Metric.closedBall_mem_nhds (0 : ℝ) zero_lt_one] with k hk
    rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at hk
    refine Eventually.of_forall fun u => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    dsimp only [B]
    by_cases hu : u ∈ Icc (-A) 0
    · rw [Set.indicator_of_mem hu]
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (abs_nonneg _)
      have h1 : |sgn * (1 / 2 + k)| ≤ 3 / 2 := by
        rw [abs_mul]
        have h2 : |1 / 2 + k| ≤ 3 / 2 := by
          linarith [abs_add_le (1 / 2 : ℝ) k, show |(1 / 2 : ℝ)| = 1 / 2 by norm_num]
        calc |sgn| * |1 / 2 + k| ≤ 1 * (3 / 2) :=
              mul_le_mul hsgn h2 (abs_nonneg _) zero_le_one
          _ = 3 / 2 := one_mul _
      have hu_abs : |u| ≤ A := by rw [abs_of_nonpos hu.2]; linarith [hu.1]
      calc sgn * (1 / 2 + k) * u
          ≤ |sgn * (1 / 2 + k) * u| := le_abs_self _
        _ = |sgn * (1 / 2 + k)| * |u| := abs_mul _ _
        _ ≤ 3 / 2 * A := mul_le_mul h1 hu_abs (abs_nonneg _) (by positivity)
    · rw [Set.indicator_of_notMem hu, hH.vanish u hu, abs_zero, zero_mul]
  · exact Eventually.of_forall fun u => (by fun_prop : Continuous fun k : ℝ =>
      H u * Real.exp (sgn * (1 / 2 + k) * u)).continuousAt

theorem continuousAt_shiftedPoleForm_zero {A : ℝ} (hA : 0 ≤ A) {H : ℝ → ℝ}
    (hH : IsWindowTest A H) :
    ContinuousAt (fun k => shiftedPoleForm k H) 0 := by
  have hp := continuousAt_integral_mul_exp hA hH 1 (by norm_num)
  have hm := continuousAt_integral_mul_exp hA hH (-1) (by norm_num)
  have heq : (fun k => shiftedPoleForm k H) = fun k =>
      2 * ((∫ u, H u * Real.exp (1 * (1 / 2 + k) * u)) *
        ∫ u, H u * Real.exp ((-1) * (1 / 2 + k) * u)) := by
    funext k; unfold shiftedPoleForm; simp only [one_mul, neg_one_mul]
  rw [heq]
  exact continuousAt_const.mul (hp.mul hm)

/-- Two-sided derivative at `k = 0`: `∂_k (k · shiftedPoleForm k H)|_{k=0} = windowPoleForm H`. -/
theorem hasDerivAt_mul_shiftedPoleForm_zero {A : ℝ} (hA : 0 ≤ A) {H : ℝ → ℝ}
    (hH : IsWindowTest A H) :
    HasDerivAt (fun k => k * shiftedPoleForm k H) (windowPoleForm H) 0 := by
  rw [hasDerivAt_iff_tendsto_slope_zero]
  have hc := (continuousAt_shiftedPoleForm_zero hA hH).tendsto.mono_left
    (nhdsWithin_le_nhds (s := {0}ᶜ))
  rw [shiftedPoleForm_zero hH] at hc
  refine hc.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  rw [Set.mem_compl_singleton_iff] at ht
  simp only [zero_add, zero_mul, sub_zero, smul_eq_mul]
  exact (inv_mul_cancel_left₀ ht (shiftedPoleForm t H)).symm

/-! ### The Euler-product pole weight `1 / ζ(1 + k)` and sharp `ζ` / `ξ` bounds -/

/-- The Euler-product pole residue weight `Σ_{m ≥ 1} μ(m) / m^{1 + k} = 1 / ζ(1 + k)`. -/
def eulerProductPoleWeight (k : ℝ) : ℝ :=
  ∑' m : ℕ, (ArithmeticFunction.moebius m : ℝ) / (m : ℝ) ^ (1 + k)

private theorem abs_moebius_le_one (m : ℕ) : |(ArithmeticFunction.moebius m : ℝ)| ≤ 1 := by
  rcases eq_or_ne (ArithmeticFunction.moebius m) 0 with h0 | h0
  · rw [h0]; norm_num
  · rcases (ArithmeticFunction.moebius_ne_zero_iff_eq_or.mp h0) with h1 | h1 <;>
      rw [h1] <;> norm_num

theorem summable_moebius_div_rpow {k : ℝ} (hk : 0 < k) :
    Summable fun m : ℕ => (ArithmeticFunction.moebius m : ℝ) / (m : ℝ) ^ (1 + k) := by
  have hdom : Summable fun m : ℕ => 1 / (m : ℝ) ^ (1 + k) :=
    Real.summable_one_div_nat_rpow.mpr (by linarith)
  refine Summable.of_norm_bounded hdom fun m => ?_
  rw [Real.norm_eq_abs, abs_div, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg m) _)]
  exact div_le_div_of_nonneg_right (abs_moebius_le_one m) (Real.rpow_nonneg (Nat.cast_nonneg m) _)

theorem riemannZeta_ofReal_eq_tsum {s : ℝ} (hs : 1 < s) :
    riemannZeta (s : ℂ) = ((∑' n : ℕ, 1 / (n + 1 : ℝ) ^ s : ℝ) : ℂ) := by
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow (by simpa using hs), Complex.ofReal_tsum]
  congr 1 with n
  rw [show ((n : ℂ) + 1) = ((n + 1 : ℝ) : ℂ) by push_cast; rfl,
    Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_cpow (by positivity)]

theorem riemannZeta_ofReal_re_eq_tsum {s : ℝ} (hs : 1 < s) :
    (riemannZeta (s : ℂ)).re = ∑' n : ℕ, 1 / (n + 1 : ℝ) ^ s := by
  rw [riemannZeta_ofReal_eq_tsum hs, Complex.ofReal_re]

theorem eulerProductPoleWeight_mul_zeta_eq_one {k : ℝ} (hk : 0 < k) :
    eulerProductPoleWeight k * (riemannZeta ((1 + k : ℝ) : ℂ)).re = 1 := by
  set s : ℝ := 1 + k
  have hs : 1 < s := by dsimp only [s]; linarith
  have hs_re : 1 < ((s : ℂ)).re := by simpa using hs
  have hinv := _root_.RHTower.riemannZeta_inv_eq_tsum_term hs_re
  have hterm : (fun m : ℕ =>
      LSeries.term (fun n : ℕ => ((ArithmeticFunction.moebius n : ℤ) : ℂ)) (s : ℂ) m) =
      fun m : ℕ => (((ArithmeticFunction.moebius m : ℝ) / (m : ℝ) ^ s : ℝ) : ℂ) := by
    funext m
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp [LSeries.term, Real.zero_rpow (by linarith : s ≠ 0)]
    · rw [LSeries.term_of_ne_zero hm.ne', Complex.ofReal_div,
        show (m : ℂ) ^ (s : ℂ) = (((m : ℝ) ^ s : ℝ) : ℂ) by
          rw [← Complex.ofReal_natCast, Complex.ofReal_cpow (Nat.cast_nonneg m)]]
      push_cast; rfl
  rw [hterm, ← Complex.ofReal_tsum] at hinv
  have hζ := riemannZeta_ofReal_eq_tsum hs
  set Z : ℝ := ∑' n : ℕ, 1 / (n + 1 : ℝ) ^ s
  rw [hζ] at hinv
  have hZpos : 0 < Z := by
    have hsum : Summable fun n : ℕ => 1 / (n + 1 : ℝ) ^ s := by
      exact_mod_cast (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_rpow.mpr hs)
    have h0 := hsum.le_tsum 0 fun j _ => by positivity
    simp only [Nat.cast_zero, zero_add, Real.one_rpow, div_one] at h0
    linarith
  have hre := congrArg Complex.re hinv
  rw [← Complex.ofReal_inv, Complex.ofReal_re, Complex.ofReal_re] at hre
  rw [riemannZeta_ofReal_re_eq_tsum hs]
  change eulerProductPoleWeight k * Z = 1
  unfold eulerProductPoleWeight
  rw [← show s = 1 + k from rfl, ← hre, inv_mul_cancel₀ hZpos.ne']

/-- Midpoint Chebyshev bound on `ZetaAsymptotics.term`: for `n ≥ 1` and `s > 1`,
`term n s ≤ (1 / (2 s)) (1 / n^s − 1 / (n + 1)^s)`. -/
private theorem zetaTerm_le_half_telescoping {n : ℕ} (hn : 0 < n) {s : ℝ} (hs : 1 < s) :
    ZetaAsymptotics.term n s ≤ 1 / (2 * s) * (1 / (n : ℝ) ^ s - 1 / ((n : ℝ) + 1) ^ s) := by
  set c : ℝ := (n : ℝ) + 1 / 2
  have hc : 0 < c := by dsimp only [c]; positivity
  have hv : ∀ x ∈ uIcc (n : ℝ) (n + 1), 0 < x := by
    intro x hx
    rw [uIcc_of_le (by linarith)] at hx
    exact (Nat.cast_pos.mpr hn).trans_le hx.1
  have hpt : ∀ x ∈ Ioc (n : ℝ) (n + 1), (x - n) / x ^ (s + 1) ≤
      1 / 2 * x ^ (-(s + 1)) + 1 / c ^ (s + 1) * (x - n - 1 / 2) := by
    intro x hx
    have hx_pos : 0 < x := (Nat.cast_pos.mpr hn).trans hx.1
    have hcheb : (x - n - 1 / 2) * (1 / x ^ (s + 1) - 1 / c ^ (s + 1)) ≤ 0 := by
      rcases le_or_gt x c with hxc | hcx
      · refine mul_nonpos_of_nonpos_of_nonneg (by dsimp only [c] at hxc; linarith) ?_
        exact sub_nonneg.mpr (one_div_le_one_div_of_le (Real.rpow_pos_of_pos hx_pos _)
          (Real.rpow_le_rpow hx_pos.le hxc (by linarith)))
      · refine mul_nonpos_of_nonneg_of_nonpos (by dsimp only [c] at hcx; linarith) ?_
        exact sub_nonpos.mpr (one_div_le_one_div_of_le (Real.rpow_pos_of_pos hc _)
          (Real.rpow_le_rpow hc.le hcx.le (by linarith)))
    have hrp : 1 / x ^ (s + 1) = x ^ (-(s + 1)) := by
      rw [one_div, Real.rpow_neg hx_pos.le]
    have hexp : (x - n) * (1 / x ^ (s + 1)) -
        (1 / 2 * (1 / x ^ (s + 1)) + 1 / c ^ (s + 1) * (x - n - 1 / 2)) =
        (x - n - 1 / 2) * (1 / x ^ (s + 1) - 1 / c ^ (s + 1)) := by ring
    rw [div_eq_mul_one_div, ← hrp]
    linarith
  have hi_lhs : IntervalIntegrable (fun x : ℝ => (x - n) / x ^ (s + 1)) volume n (n + 1) :=
    ZetaAsymptotics.term_welldef hn (zero_lt_one.trans hs)
  have hi_rpow : IntervalIntegrable (fun x : ℝ => x ^ (-(s + 1))) volume n (n + 1) := by
    refine intervalIntegral.intervalIntegrable_rpow (Or.inr <| notMem_uIcc_of_lt ?_ ?_)
    · exact_mod_cast hn
    · positivity
  have hi_lin : IntervalIntegrable (fun x : ℝ => x - n - 1 / 2) volume n (n + 1) :=
    (by fun_prop : Continuous fun x : ℝ => x - n - 1 / 2).intervalIntegrable _ _
  have hi_rhs : IntervalIntegrable
      (fun x : ℝ => 1 / 2 * x ^ (-(s + 1)) + 1 / c ^ (s + 1) * (x - n - 1 / 2)) volume n (n + 1) :=
    (hi_rpow.const_mul _).add (hi_lin.const_mul _)
  have hmono : ZetaAsymptotics.term n s ≤
      ∫ x : ℝ in (n : ℝ)..(n + 1),
        (1 / 2 * x ^ (-(s + 1)) + 1 / c ^ (s + 1) * (x - n - 1 / 2)) := by
    unfold ZetaAsymptotics.term
    rw [intervalIntegral.integral_of_le (by linarith), intervalIntegral.integral_of_le (by linarith)]
    exact setIntegral_mono_on hi_lhs.1 hi_rhs.1 measurableSet_Ioc hpt
  rw [intervalIntegral.integral_add (hi_rpow.const_mul _) (hi_lin.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hmono
  have hlin_zero : (∫ x : ℝ in (n : ℝ)..(n + 1), (x - (n : ℝ) - 1 / 2)) = 0 := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun x : ℝ => (x - ((n : ℝ) + 1 / 2)) * (x - ((n : ℝ) + 1 / 2)) / 2)
      (f' := fun x : ℝ => x - (n : ℝ) - 1 / 2)
      (fun x _ => by
        have hg := (hasDerivAt_id x).sub_const ((n : ℝ) + 1 / 2)
        exact ((hg.mul hg).div_const 2).congr_deriv (by dsimp only [id]; ring))
      hi_lin]
    ring
  have hrpow_val : (∫ x : ℝ in (n : ℝ)..(n + 1), x ^ (-(s + 1))) =
      1 / s * (1 / (n : ℝ) ^ s - 1 / ((n : ℝ) + 1) ^ s) := by
    have h0 : (0 : ℝ) ∉ uIcc (n : ℝ) (n + 1) := fun h => (lt_irrefl 0 (hv 0 h))
    rw [integral_rpow (Or.inr ⟨by linarith, h0⟩)]
    rw [show -(s + 1) + 1 = -s by ring, div_neg, ← neg_div, neg_sub,
      Real.rpow_neg (Nat.cast_nonneg n), one_div, Real.rpow_neg (by positivity), one_div]
    ring
  rw [hlin_zero, mul_zero, add_zero, hrpow_val] at hmono
  refine hmono.trans_eq ?_
  simp only [one_div, mul_inv_rev]
  ring

/-- For every `k > 0`, `ζ(1 + k) ≥ 1 / k + 1 / 2`. -/
theorem zeta_re_ge_inv_add_half {k : ℝ} (hk : 0 < k) :
    1 / k + 1 / 2 ≤ (riemannZeta ((1 + k : ℝ) : ℂ)).re := by
  set s : ℝ := 1 + k
  have hs : 1 < s := by dsimp only [s]; linarith
  rw [riemannZeta_ofReal_re_eq_tsum hs]
  have haux := ZetaAsymptotics.zeta_limit_aux1 hs
  rw [show s - 1 = k by dsimp only [s]; ring] at haux
  have htsum_le : ZetaAsymptotics.termTSum s ≤ 1 / (2 * s) := by
    refine Real.tsum_le_of_sum_range_le (fun m => ZetaAsymptotics.term_nonneg (m + 1) s) fun N => ?_
    have hstep : ∑ m ∈ Finset.range N, ZetaAsymptotics.term (m + 1) s ≤
        ∑ m ∈ Finset.range N,
          1 / (2 * s) * (1 / ((m + 1 : ℕ) : ℝ) ^ s - 1 / (((m + 1 : ℕ) : ℝ) + 1) ^ s) :=
      Finset.sum_le_sum fun m _ => zetaTerm_le_half_telescoping m.succ_pos hs
    have htel : ∀ M : ℕ, ∑ m ∈ Finset.range M,
        (1 / ((m + 1 : ℕ) : ℝ) ^ s - 1 / (((m + 1 : ℕ) : ℝ) + 1) ^ s) =
        1 - 1 / ((M + 1 : ℕ) : ℝ) ^ s := by
      intro M
      induction M with
      | zero => simp
      | succ M ih =>
        rw [Finset.sum_range_succ, ih]
        push_cast; ring
    rw [← Finset.mul_sum, htel N] at hstep
    have hnn : 0 ≤ 1 / ((N + 1 : ℕ) : ℝ) ^ s := by positivity
    have hle1 : 1 - 1 / ((N + 1 : ℕ) : ℝ) ^ s ≤ 1 := by linarith
    calc ∑ m ∈ Finset.range N, ZetaAsymptotics.term (m + 1) s
        ≤ 1 / (2 * s) * (1 - 1 / ((N + 1 : ℕ) : ℝ) ^ s) := hstep
      _ ≤ 1 / (2 * s) * 1 := mul_le_mul_of_nonneg_left hle1 (by positivity)
      _ = 1 / (2 * s) := mul_one _
  have hmul : s * ZetaAsymptotics.termTSum s ≤ 1 / 2 := by
    calc s * ZetaAsymptotics.termTSum s ≤ s * (1 / (2 * s)) :=
          mul_le_mul_of_nonneg_left htsum_le (by positivity)
      _ = 1 / 2 := by field_simp [(by positivity : s ≠ 0)]
  linarith

theorem eulerProductPoleWeight_pos {k : ℝ} (hk : 0 < k) : 0 < eulerProductPoleWeight k := by
  have hprod := eulerProductPoleWeight_mul_zeta_eq_one hk
  have hζ : 0 < (riemannZeta ((1 + k : ℝ) : ℂ)).re :=
    lt_of_lt_of_le (by positivity) (zeta_re_ge_inv_add_half hk)
  nlinarith

/-- For every `k > 0`, the Euler-product pole weight `1 / ζ(1 + k)` is strictly smaller than `k`. -/
theorem eulerProductPoleWeight_lt_self {k : ℝ} (hk : 0 < k) : eulerProductPoleWeight k < k := by
  have hprod := eulerProductPoleWeight_mul_zeta_eq_one hk
  have hw := eulerProductPoleWeight_pos hk
  have hζ := zeta_re_ge_inv_add_half hk
  have h1 : eulerProductPoleWeight k * (1 / k + 1 / 2) ≤ 1 := by nlinarith
  have h2 : eulerProductPoleWeight k * (1 / k) < 1 := by nlinarith
  rwa [mul_one_div, div_lt_one hk] at h2

/-- Sharp upper bound on `(1, 2]`: for `0 < k ≤ 1`, `ζ(1 + k) < 1 / k + 7 / 8`. -/
theorem zeta_re_lt_inv_add_seven_eighths {k : ℝ} (hk0 : 0 < k) (hk1 : k ≤ 1) :
    (riemannZeta ((1 + k : ℝ) : ℂ)).re < 1 / k + 7 / 8 := by
  set s : ℝ := 1 + k
  have hs1 : 1 < s := by dsimp only [s]; linarith
  have hs2 : s ≤ 2 := by dsimp only [s]; linarith
  rw [riemannZeta_ofReal_re_eq_tsum hs1]
  have haux := ZetaAsymptotics.zeta_limit_aux1 hs1
  rw [show s - 1 = k by dsimp only [s]; ring] at haux
  have hsum : Summable fun m : ℕ => ZetaAsymptotics.term (m + 1) s := by
    refine ZetaAsymptotics.term_tsum_one.summable.of_nonneg_of_le
      (fun m => ZetaAsymptotics.term_nonneg (m + 1) s) fun m => ?_
    unfold ZetaAsymptotics.term
    rw [intervalIntegral.integral_of_le (by linarith),
      intervalIntegral.integral_of_le (by linarith)]
    refine setIntegral_mono_on
      (ZetaAsymptotics.term_welldef m.succ_pos (zero_lt_one.trans hs1)).1
      (ZetaAsymptotics.term_welldef m.succ_pos zero_lt_one).1
      measurableSet_Ioc fun x hx => ?_
    have hx1 : 1 ≤ x := le_trans (by exact_mod_cast m.succ_pos) hx.1.le
    exact div_le_div_of_nonneg_left (sub_nonneg.mpr hx.1.le) (by positivity)
      (Real.rpow_le_rpow_of_exponent_le hx1 (by linarith))
  have ht2 : ZetaAsymptotics.term 1 2 = 1 / 8 := by
    rw [ZetaAsymptotics.term_of_lt zero_lt_one one_lt_two]
    norm_num
  have ht_mono : ZetaAsymptotics.term 1 2 ≤ ZetaAsymptotics.term 1 s := by
    unfold ZetaAsymptotics.term
    rw [intervalIntegral.integral_of_le (by norm_num), intervalIntegral.integral_of_le (by norm_num)]
    refine setIntegral_mono_on
      (ZetaAsymptotics.term_welldef zero_lt_one zero_lt_two).1
      (ZetaAsymptotics.term_welldef zero_lt_one (zero_lt_one.trans hs1)).1
      measurableSet_Ioc fun x hx => ?_
    simp only [Nat.cast_one] at hx ⊢
    have hx0 : 0 < x := zero_lt_one.trans hx.1
    exact div_le_div_of_nonneg_left (sub_nonneg.mpr hx.1.le) (Real.rpow_pos_of_pos hx0 _)
      (Real.rpow_le_rpow_of_exponent_le hx.1.le (by linarith))
  have ht_tsum : ZetaAsymptotics.term 1 s ≤ ZetaAsymptotics.termTSum s :=
    hsum.le_tsum 0 fun j _ => ZetaAsymptotics.term_nonneg (j + 1) s
  have hge : 1 / 8 ≤ ZetaAsymptotics.termTSum s := by linarith
  have hstrict : 1 / 8 < s * ZetaAsymptotics.termTSum s := by nlinarith
  linarith

/-- **Key strict inequality for `windowRiemannKernel` refutation**: for every `k ∈ (0, 1]`,
`4 · ξ(1 + k)² < k · ζ(1 + k)`. -/
theorem four_mul_riemannPhiTransform_sq_lt_mul_zeta {k : ℝ} (hk0 : 0 < k) (hk1 : k ≤ 1) :
    4 * ((_root_.RHTower.riemannPhiTransform ((1 + k : ℝ) : ℂ)).re) ^ 2 <
      k * (riemannZeta ((1 + k : ℝ) : ℂ)).re := by
  set s : ℝ := 1 + k
  have hs1 : 1 < s := by dsimp only [s]; linarith
  have hs_pos : 0 < s := by linarith
  have hs0 : (s : ℂ) ≠ 0 := by exact_mod_cast hs_pos.ne'
  set Z : ℝ := (riemannZeta (s : ℂ)).re
  have hZ_eq : riemannZeta (s : ℂ) = (Z : ℂ) := by
    rw [riemannZeta_ofReal_eq_tsum hs1]
    dsimp only [Z]
    rw [riemannZeta_ofReal_re_eq_tsum hs1]
  have hZ_pos : 0 < Z := lt_of_lt_of_le (by positivity) (zeta_re_ge_inv_add_half hk0)
  have hkZ_pos : 0 < k * Z := mul_pos hk0 hZ_pos
  have hkZ_lt : k * Z < Real.exp (7 / 8 * k) := by
    have hlt := mul_lt_mul_of_pos_left (zeta_re_lt_inv_add_seven_eighths hk0 hk1) hk0
    have hmul : k * (1 / k + 7 / 8) = 1 + 7 / 8 * k := by field_simp [hk0.ne']
    have hexp : 1 + 7 / 8 * k ≤ Real.exp (7 / 8 * k) := by
      linarith [Real.add_one_le_exp (7 / 8 * k)]
    exact (hlt.trans_eq hmul).trans_le hexp
  have hΓC : Complex.Gammaℝ (s : ℂ) = ((Real.pi ^ (-s / 2) * Real.Gamma (s / 2) : ℝ) : ℂ) := by
    rw [Complex.Gammaℝ_def, show -(s : ℂ) / 2 = ((-s / 2 : ℝ) : ℂ) by push_cast; ring,
      show (s : ℂ) / 2 = ((s / 2 : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_cpow Real.pi_pos.le, Complex.Gamma_ofReal, Complex.ofReal_mul]
  have hΛ : completedRiemannZeta (s : ℂ) =
      ((Z * (Real.pi ^ (-s / 2) * Real.Gamma (s / 2)) : ℝ) : ℂ) := by
    have hne : Complex.Gammaℝ (s : ℂ) ≠ 0 :=
      Complex.Gammaℝ_ne_zero_of_re_pos (by simpa using hs_pos)
    have hd := riemannZeta_def_of_ne_zero hs0
    have hmul : completedRiemannZeta (s : ℂ) = riemannZeta (s : ℂ) * Complex.Gammaℝ (s : ℂ) := by
      rw [hd, div_mul_cancel₀ _ hne]
    rw [hmul, hZ_eq, hΓC, ← Complex.ofReal_mul]
  have hΦ : (_root_.RHTower.riemannPhiTransform (s : ℂ)).re =
      k * Real.Gamma ((3 + k) / 2) * Real.pi ^ (-s / 2) * Z := by
    rw [_root_.RHTower.riemannPhiTransform_eq_of_one_lt_re (by simpa using hs1), hΛ]
    have hcast : (s : ℂ) * ((s : ℂ) - 1) / 2 = ((s * k / 2 : ℝ) : ℂ) := by
      dsimp only [s]; push_cast; ring
    rw [hcast, ← Complex.ofReal_mul, Complex.ofReal_re]
    have hΓrec : Real.Gamma ((3 + k) / 2) = (s / 2) * Real.Gamma (s / 2) := by
      rw [show (3 + k) / 2 = s / 2 + 1 by dsimp only [s]; ring,
        Real.Gamma_add_one (by positivity)]
    rw [hΓrec]; ring
  have hsq : 4 * ((_root_.RHTower.riemannPhiTransform (s : ℂ)).re) ^ 2 =
      (4 * Real.Gamma ((3 + k) / 2) ^ 2 * Real.pi ^ (-s)) * (k * Z) * (k * Z) := by
    rw [hΦ]
    have hpi : (Real.pi ^ (-s / 2)) ^ 2 = Real.pi ^ (-s) := by
      rw [sq, ← Real.rpow_add Real.pi_pos]; congr 1; ring
    calc 4 * (k * Real.Gamma ((3 + k) / 2) * Real.pi ^ (-s / 2) * Z) ^ 2
        = 4 * Real.Gamma ((3 + k) / 2) ^ 2 * (Real.pi ^ (-s / 2)) ^ 2 * (k * Z) * (k * Z) := by ring
      _ = (4 * Real.Gamma ((3 + k) / 2) ^ 2 * Real.pi ^ (-s)) * (k * Z) * (k * Z) := by
          rw [hpi]
  have hΓ_conv : 4 * Real.Gamma ((3 + k) / 2) ^ 2 * Real.pi ^ (-s) ≤
      (4 / Real.pi ^ 2) ^ k := by
    have hconv := Real.convexOn_log_Gamma.2
      (show (3 / 2 : ℝ) ∈ Ioi 0 by norm_num) (show (2 : ℝ) ∈ Ioi 0 by norm_num)
      (by linarith : 0 ≤ 1 - k) hk0.le (by ring)
    simp only [Function.comp_apply, smul_eq_mul] at hconv
    have harg : (1 - k) * (3 / 2) + k * 2 = (3 + k) / 2 := by ring
    rw [harg] at hconv
    have hΓ32 : Real.Gamma (3 / 2) = Real.sqrt Real.pi / 2 := by
      rw [show (3 / 2 : ℝ) = 1 / 2 + 1 by norm_num, Real.Gamma_add_one (by norm_num),
        Real.Gamma_one_half_eq]
      ring
    have hΓ2 : Real.Gamma 2 = 1 := by
      rw [show (2 : ℝ) = ((1 : ℕ) : ℝ) + 1 by norm_num, Real.Gamma_nat_eq_factorial]
      norm_num [Nat.factorial]
    rw [hΓ2, Real.log_one, mul_zero, add_zero] at hconv
    have hexp_le := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hconv zero_le_two)
    have hlhs : Real.exp (2 * Real.log (Real.Gamma ((3 + k) / 2))) =
        Real.Gamma ((3 + k) / 2) ^ 2 := by
      rw [mul_comm, Real.exp_mul, Real.exp_log (Real.Gamma_pos_of_pos (by positivity)),
        Real.rpow_two]
    have hrhs : Real.exp (2 * ((1 - k) * Real.log (Real.Gamma (3 / 2)))) =
        (Real.pi / 4) ^ (1 - k) := by
      have hsq32 : Real.Gamma (3 / 2) ^ 2 = Real.pi / 4 := by
        rw [hΓ32, div_pow, Real.sq_sqrt Real.pi_pos.le]; norm_num
      rw [show 2 * ((1 - k) * Real.log (Real.Gamma (3 / 2))) =
          Real.log (Real.Gamma (3 / 2) ^ 2) * (1 - k) by
          rw [Real.log_pow]; push_cast; ring,
        hsq32, ← Real.rpow_def_of_pos (by positivity : 0 < Real.pi / 4)]
    rw [hlhs, hrhs] at hexp_le
    calc 4 * Real.Gamma ((3 + k) / 2) ^ 2 * Real.pi ^ (-s)
        ≤ 4 * (Real.pi / 4) ^ (1 - k) * Real.pi ^ (-s) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hexp_le (by norm_num))
            (Real.rpow_nonneg Real.pi_pos.le _)
      _ = (4 / Real.pi ^ 2) ^ k := by
          have hp := Real.pi_pos
          rw [Real.div_rpow hp.le (by norm_num), Real.div_rpow (by norm_num) (sq_pos_of_pos hp).le,
            ← Real.rpow_natCast Real.pi 2, ← Real.rpow_mul hp.le]
          have h4 : (4 : ℝ) * (1 / (4 : ℝ) ^ (1 - k)) = (4 : ℝ) ^ k := by
            rw [one_div, ← Real.rpow_neg (by norm_num), ← Real.rpow_one_add' (by norm_num) (by linarith)]
            congr 1; ring
          have hpi2 : Real.pi ^ (1 - k) * Real.pi ^ (-s) = 1 / Real.pi ^ (2 * k) := by
            rw [← Real.rpow_add hp, one_div, ← Real.rpow_neg hp.le]
            congr 1; dsimp only [s]; ring
          calc 4 * (Real.pi ^ (1 - k) / (4 : ℝ) ^ (1 - k)) * Real.pi ^ (-s)
              = (4 * (1 / (4 : ℝ) ^ (1 - k))) * (Real.pi ^ (1 - k) * Real.pi ^ (-s)) := by ring
            _ = (4 : ℝ) ^ k * (1 / Real.pi ^ (2 * k)) := by rw [h4, hpi2]
            _ = (4 : ℝ) ^ k / Real.pi ^ (↑(2 : ℕ) * k) := by push_cast; ring
  have hprod_lt : (4 * Real.Gamma ((3 + k) / 2) ^ 2 * Real.pi ^ (-s)) * (k * Z) < 1 := by
    have hbase_lt : 4 / Real.pi ^ 2 * Real.exp (7 / 8) < 1 := by
      have he8 : Real.exp (7 / 8) ^ 8 < (12 / 5 : ℝ) ^ 8 := by
        rw [← Real.exp_nat_mul, show (8 : ℕ) * (7 / 8 : ℝ) = (7 : ℕ) * (1 : ℝ) by norm_num,
          Real.exp_nat_mul]
        calc Real.exp 1 ^ 7 < (2.7182818286 : ℝ) ^ 7 :=
              pow_lt_pow_left₀ Real.exp_one_lt_d9 (Real.exp_pos 1).le (by omega)
          _ < (12 / 5 : ℝ) ^ 8 := by norm_num
      have he_lt : Real.exp (7 / 8) < 12 / 5 := by
        by_contra hge; push Not at hge
        exact absurd (pow_le_pow_left₀ (by norm_num) hge 8) (not_le.mpr he8)
      have hpi_sq : (9.85 : ℝ) < Real.pi ^ 2 := by
        calc (9.85 : ℝ) < 3.14 ^ 2 := by norm_num
          _ < Real.pi ^ 2 := pow_lt_pow_left₀ Real.pi_gt_d2 (by norm_num) (by omega)
      rw [div_mul_eq_mul_div, div_lt_one (sq_pos_of_pos Real.pi_pos)]
      linarith
    have hexp_k : Real.exp (7 / 8 * k) = Real.exp (7 / 8) ^ k := by
      rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
    calc (4 * Real.Gamma ((3 + k) / 2) ^ 2 * Real.pi ^ (-s)) * (k * Z)
        < (4 / Real.pi ^ 2) ^ k * Real.exp (7 / 8 * k) := by
          refine mul_lt_mul_of_nonneg_of_pos' hΓ_conv hkZ_lt hkZ_pos.le ?_
          exact Real.rpow_pos_of_pos (by positivity) k
      _ = (4 / Real.pi ^ 2 * Real.exp (7 / 8)) ^ k := by
          rw [hexp_k, ← Real.mul_rpow (by positivity) (Real.exp_pos _).le]
      _ < 1 := Real.rpow_lt_one (by positivity) hbase_lt hk0
  rw [hsq]
  nlinarith

/-! ### Zero-Fubini 1D Dirichlet hyperbola asymptotic -/

/-- Continuous 1D Mellin–Laplace profile `∫_{x > 0} x^{k − 1/2} H(y + log x) dx`. -/
def tateProfileIntegral (H : ℝ → ℝ) (k y : ℝ) : ℝ :=
  ∫ x in Ioi (0 : ℝ), x ^ (k - 1 / 2) * H (y + Real.log x)

/-- Exact 1D change of variables `x = e^{w − y}` evaluating `tateProfileIntegral`. -/
theorem tateProfileIntegral_eq (H : ℝ → ℝ) (k y : ℝ) :
    tateProfileIntegral H k y =
      Real.exp (-(1 / 2 + k) * y) * ∫ w : ℝ, H w * Real.exp ((1 / 2 + k) * w) := by
  have himage : (fun w : ℝ => Real.exp (w - y)) '' Set.univ = Ioi (0 : ℝ) := by
    ext x; constructor
    · rintro ⟨w, -, rfl⟩; exact Real.exp_pos _
    · intro hx
      refine ⟨Real.log x + y, trivial, ?_⟩
      simp only [add_sub_cancel_right, Real.exp_log hx]
  have hder : ∀ w ∈ (Set.univ : Set ℝ), HasDerivWithinAt (fun w : ℝ => Real.exp (w - y))
      (Real.exp (w - y)) Set.univ w := by
    intro w _
    have h : HasDerivAt (fun w : ℝ => Real.exp (w - y)) (Real.exp (w - y)) w :=
      (((hasDerivAt_id w).sub_const y).exp).congr_deriv (mul_one _)
    exact h.hasDerivWithinAt
  have hinj : Set.InjOn (fun w : ℝ => Real.exp (w - y)) Set.univ := by
    intro a _ b _ hab
    linarith [Real.exp_injective hab]
  have hcv := integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ hder hinj
    (fun x : ℝ => x ^ (k - 1 / 2) * H (y + Real.log x))
  rw [himage, Measure.restrict_univ] at hcv
  unfold tateProfileIntegral
  rw [hcv, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun w => ?_)
  dsimp only [smul_eq_mul]
  rw [abs_of_pos (Real.exp_pos _), Real.log_exp, show y + (w - y) = w by ring,
    Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
  have hexp : Real.exp (w - y) * Real.exp ((w - y) * (k - 1 / 2)) =
      Real.exp (-(1 / 2 + k) * y) * Real.exp ((1 / 2 + k) * w) := by
    rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  calc Real.exp (w - y) * (Real.exp ((w - y) * (k - 1 / 2)) * H w)
      = (Real.exp (w - y) * Real.exp ((w - y) * (k - 1 / 2))) * H w := by ring
    _ = Real.exp (-(1 / 2 + k) * y) * (H w * Real.exp ((1 / 2 + k) * w)) := by rw [hexp]; ring

/-- Pairing `H(u)` against `tateProfileIntegral H k (u + log d)` produces `d^{−(1+k)} shiftedPoleForm k H`. -/
theorem two_mul_integral_mul_tateProfileIntegral (H : ℝ → ℝ) (k : ℝ) {d : ℕ} (hd : 1 ≤ d) :
    2 * (((ArithmeticFunction.moebius d : ℝ) / Real.sqrt d) *
      ∫ u, H u * tateProfileIntegral H k (u + Real.log d)) =
      ((ArithmeticFunction.moebius d : ℝ) / (d : ℝ) ^ (1 + k)) * shiftedPoleForm k H := by
  have hd_pos : (0 : ℝ) < d := by exact_mod_cast hd
  have hpt : ∀ u : ℝ, H u * tateProfileIntegral H k (u + Real.log d) =
      ((d : ℝ) ^ (-(1 / 2 + k)) * ∫ w, H w * Real.exp ((1 / 2 + k) * w)) *
        (H u * Real.exp (-(1 / 2 + k) * u)) := fun u => by
    rw [tateProfileIntegral_eq]
    have hexp : Real.exp (-(1 / 2 + k) * (u + Real.log d)) =
        (d : ℝ) ^ (-(1 / 2 + k)) * Real.exp (-(1 / 2 + k) * u) := by
      rw [mul_add, Real.exp_add, mul_comm (-(1 / 2 + k)) (Real.log d),
        ← Real.rpow_def_of_pos hd_pos, mul_comm]
    rw [hexp]; ring
  simp_rw [hpt]
  rw [integral_const_mul]
  have hd_rpow : (1 / Real.sqrt d) * (d : ℝ) ^ (-(1 / 2 + k)) = 1 / (d : ℝ) ^ (1 + k) := by
    rw [Real.sqrt_eq_rpow, one_div ((d : ℝ) ^ _), ← Real.rpow_neg hd_pos.le,
      ← Real.rpow_add hd_pos, one_div ((d : ℝ) ^ _), ← Real.rpow_neg hd_pos.le]
    congr 1; ring
  unfold shiftedPoleForm
  calc 2 * ((ArithmeticFunction.moebius d : ℝ) / Real.sqrt d *
        (((d : ℝ) ^ (-(1 / 2 + k)) * ∫ w, H w * Real.exp ((1 / 2 + k) * w)) *
          ∫ u, H u * Real.exp (-(1 / 2 + k) * u)))
      = (ArithmeticFunction.moebius d : ℝ) * ((1 / Real.sqrt d) * (d : ℝ) ^ (-(1 / 2 + k))) *
          (2 * ((∫ w, H w * Real.exp ((1 / 2 + k) * w)) *
            ∫ u, H u * Real.exp (-(1 / 2 + k) * u))) := by ring
    _ = ((ArithmeticFunction.moebius d : ℝ) / (d : ℝ) ^ (1 + k)) *
          (2 * ((∫ w, H w * Real.exp ((1 / 2 + k) * w)) *
            ∫ u, H u * Real.exp (-(1 / 2 + k) * u))) := by rw [hd_rpow]; ring

/-- Exact Möbius–divisor expansion of `2 · tateFunction A H k` before integrating over `u`. -/
theorem two_mul_tateFunction_eq_moebius_sum {A : ℝ} {H : ℝ → ℝ} (hH : IsWindowTest A H) (k : ℝ) :
    2 * tateFunction A H k =
      2 * ∑ d ∈ Finset.Icc 1 (windowLevel A),
        ((ArithmeticFunction.moebius d : ℝ) / Real.sqrt d) *
          ∫ u, H u * ∑ m ∈ Finset.Icc 1 (windowLevel A / d),
            (m : ℝ) ^ (k - 1 / 2) * H (u + Real.log d + Real.log m) := by
  set N := windowLevel A
  rw [tateFunction_eq hH]
  congr 1
  have hexpand : ∑ n ∈ Finset.Icc 1 N,
      jordanTotient k n / Real.sqrt n * ∫ u, H u * H (u + Real.log n) =
      ∑ p ∈ (Finset.Icc 1 N).sigma (fun n => n.divisors),
        ((ArithmeticFunction.moebius (p.1 / p.2) : ℝ) * (p.2 : ℝ) ^ k / Real.sqrt p.1 *
          ∫ u, H u * H (u + Real.log p.1)) := by
    have hpt_n : ∀ n ∈ Finset.Icc 1 N,
        jordanTotient k n / Real.sqrt n * (∫ u, H u * H (u + Real.log n)) =
          ∑ m ∈ n.divisors,
            (ArithmeticFunction.moebius (n / m) : ℝ) * (m : ℝ) ^ k / Real.sqrt n *
              ∫ u, H u * H (u + Real.log n) := fun n _ => by
      unfold jordanTotient; rw [Finset.sum_div, Finset.sum_mul]
    rw [Finset.sum_congr rfl hpt_n, Finset.sum_sigma']
  rw [hexpand]
  have hbij : ∑ p ∈ (Finset.Icc 1 N).sigma (fun n => n.divisors),
      ((ArithmeticFunction.moebius (p.1 / p.2) : ℝ) * (p.2 : ℝ) ^ k / Real.sqrt p.1 *
        ∫ u, H u * H (u + Real.log p.1)) =
      ∑ q ∈ (Finset.Icc 1 N).sigma (fun d => Finset.Icc 1 (N / d)),
        ((ArithmeticFunction.moebius q.1 : ℝ) / Real.sqrt q.1 *
          ((q.2 : ℝ) ^ (k - 1 / 2) * ∫ u, H u * H (u + Real.log q.1 + Real.log q.2))) := by
    refine (Finset.sum_bij'
      (fun (q : (d : ℕ) × ℕ) _ => (⟨q.1 * q.2, q.2⟩ : (n : ℕ) × ℕ))
      (fun (p : (n : ℕ) × ℕ) _ => (⟨p.1 / p.2, p.2⟩ : (d : ℕ) × ℕ))
      ?_ ?_ ?_ ?_ ?_).symm
    · intro ⟨d, m⟩ hq
      simp only [Finset.mem_sigma, Finset.mem_Icc, Nat.mem_divisors] at hq ⊢
      obtain ⟨⟨hd1, hd2⟩, ⟨hm1, hm2⟩⟩ := hq
      have hpos : 0 < d * m := Nat.mul_pos hd1 hm1
      have hle : d * m ≤ N := by
        rw [mul_comm]
        exact (Nat.le_div_iff_mul_le hd1).mp hm2
      exact ⟨⟨hpos, hle⟩, dvd_mul_left m d, hpos.ne'⟩
    · intro ⟨n, m⟩ hp
      simp only [Finset.mem_sigma, Finset.mem_Icc, Nat.mem_divisors] at hp ⊢
      obtain ⟨⟨hn1, hn2⟩, hm_dvd, _⟩ := hp
      have hm_pos : 0 < m := Nat.pos_of_dvd_of_pos hm_dvd hn1
      have hd_mul : n / m * m = n := Nat.div_mul_cancel hm_dvd
      have hd_pos : 0 < n / m := Nat.div_pos (Nat.le_of_dvd hn1 hm_dvd) hm_pos
      have hd_le : n / m ≤ N := (Nat.div_le_self n m).trans hn2
      have hm_le : m ≤ N / (n / m) :=
        (Nat.le_div_iff_mul_le hd_pos).mpr (by rw [mul_comm, hd_mul]; exact hn2)
      exact ⟨⟨hd_pos, hd_le⟩, ⟨hm_pos, hm_le⟩⟩
    · intro ⟨d, m⟩ hq
      simp only [Finset.mem_sigma, Finset.mem_Icc] at hq
      ext <;> simp [Nat.mul_div_cancel d hq.2.1]
    · intro ⟨n, m⟩ hp
      simp only [Finset.mem_sigma, Nat.mem_divisors] at hp
      ext <;> simp [Nat.div_mul_cancel hp.2.1]
    · intro ⟨d, m⟩ hq
      simp only [Finset.mem_sigma, Finset.mem_Icc] at hq
      have hd_pos : (0 : ℝ) < d := by exact_mod_cast hq.1.1
      have hm_pos : (0 : ℝ) < m := by exact_mod_cast hq.2.1
      simp only [Nat.mul_div_cancel d hq.2.1, Nat.cast_mul]
      rw [Real.sqrt_mul hd_pos.le, Real.log_mul hd_pos.ne' hm_pos.ne']
      have hmr : (m : ℝ) ^ k / Real.sqrt m = (m : ℝ) ^ (k - 1 / 2) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_sub hm_pos]
      have hadd : ∀ u : ℝ, u + (Real.log d + Real.log m) = u + Real.log d + Real.log m :=
        fun u => by ring
      simp_rw [hadd]
      exact (calc (ArithmeticFunction.moebius d : ℝ) * (m : ℝ) ^ k / (Real.sqrt d * Real.sqrt m) *
            ∫ u, H u * H (u + Real.log d + Real.log m)
          = (ArithmeticFunction.moebius d : ℝ) / Real.sqrt d *
              (((m : ℝ) ^ k / Real.sqrt m) * ∫ u, H u * H (u + Real.log d + Real.log m)) := by ring
        _ = (ArithmeticFunction.moebius d : ℝ) / Real.sqrt d *
              ((m : ℝ) ^ (k - 1 / 2) * ∫ u, H u * H (u + Real.log d + Real.log m)) := by rw [hmr]).symm
  have hsig : (∑ d ∈ Finset.Icc 1 N, ∑ m ∈ Finset.Icc 1 (N / d),
      ((ArithmeticFunction.moebius d : ℝ) / Real.sqrt d *
        ((m : ℝ) ^ (k - 1 / 2) * ∫ u, H u * H (u + Real.log d + Real.log m)))) =
      ∑ q ∈ (Finset.Icc 1 N).sigma (fun d => Finset.Icc 1 (N / d)),
        ((ArithmeticFunction.moebius q.1 : ℝ) / Real.sqrt q.1 *
          ((q.2 : ℝ) ^ (k - 1 / 2) * ∫ u, H u * H (u + Real.log q.1 + Real.log q.2))) :=
    Finset.sum_sigma' _ _ _
  rw [hbij, ← hsig]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [← Finset.mul_sum]
  congr 1
  have hint : ∀ m ∈ Finset.Icc 1 (N / d),
      Integrable fun u => H u * ((m : ℝ) ^ (k - 1 / 2) * H (u + Real.log d + Real.log m)) :=
    fun m _ => (hH.continuous.mul (continuous_const.mul
      (hH.continuous.comp ((continuous_id.add continuous_const).add continuous_const)))).integrable_of_hasCompactSupport
        hH.hasCompactSupport.mul_right
  have hsum_eq : (fun u => H u * ∑ m ∈ Finset.Icc 1 (N / d),
      (m : ℝ) ^ (k - 1 / 2) * H (u + Real.log d + Real.log m)) =
      fun u => ∑ m ∈ Finset.Icc 1 (N / d),
        H u * ((m : ℝ) ^ (k - 1 / 2) * H (u + Real.log d + Real.log m)) := by
    funext u; rw [Finset.mul_sum]
  rw [hsum_eq, integral_finsetSum _ hint]
  refine Finset.sum_congr rfl fun m _ => ?_
  have hpull : (fun u => H u * ((m : ℝ) ^ (k - 1 / 2) * H (u + Real.log d + Real.log m))) =
      fun u => (m : ℝ) ^ (k - 1 / 2) * (H u * H (u + Real.log d + Real.log m)) := by
    funext u; ring
  rw [hpull, integral_const_mul]

/-- Harmonic sum bound `Σ_{1 ≤ d ≤ N} 1 / d ≤ A + 1` for `N = ⌊e^A⌋₊`, `A ≥ 0`. -/
private theorem sum_Icc_one_div_le_window {A : ℝ} (hA : 0 ≤ A) :
    ∑ d ∈ Finset.Icc 1 (windowLevel A), 1 / (d : ℝ) ≤ A + 1 := by
  have hN1 : 1 ≤ windowLevel A := one_le_windowLevel_of_nonneg hA
  have hlog : ∀ M : ℕ, 1 ≤ M → ∑ d ∈ Finset.Icc 1 M, 1 / (d : ℝ) ≤ Real.log M + 1 := by
    intro M hM
    induction M with
    | zero => omega
    | succ M ih =>
      rcases eq_or_lt_of_le (by omega : 0 ≤ M) with rfl | hMpos
      · simp
      · have h1M : 1 ≤ M := hMpos
        rw [Finset.sum_Icc_succ_top (by omega)]
        have hstep : 1 / ((M + 1 : ℕ) : ℝ) ≤ Real.log ((M + 1 : ℕ) : ℝ) - Real.log (M : ℝ) := by
          have hM_pos : (0 : ℝ) < M := by exact_mod_cast hMpos
          have hM1_pos : (0 : ℝ) < ((M + 1 : ℕ) : ℝ) := by positivity
          have hexp := Real.add_one_le_exp (Real.log (M : ℝ) - Real.log ((M + 1 : ℕ) : ℝ))
          rw [Real.exp_sub, Real.exp_log hM_pos, Real.exp_log hM1_pos] at hexp
          have hdiv : ((M : ℝ) / ((M + 1 : ℕ) : ℝ)) = 1 - 1 / ((M + 1 : ℕ) : ℝ) := by
            push_cast; field_simp; ring
          linarith
        linarith [ih h1M]
  have hN_le : (windowLevel A : ℝ) ≤ Real.exp A := Nat.floor_le (Real.exp_pos A).le
  have hlogN : Real.log (windowLevel A : ℝ) ≤ A := by
    have hpos : (0 : ℝ) < windowLevel A := by exact_mod_cast hN1
    calc Real.log (windowLevel A : ℝ) ≤ Real.log (Real.exp A) := Real.log_le_log hpos hN_le
      _ = A := Real.log_exp A
  linarith [hlog (windowLevel A) hN1]

/-- Power-sum bound `Σ_{1 ≤ m ≤ L} m^{k − 1} ≤ 1 + L^k / k` for `0 < k < 1` and `L ≥ 1`. -/
private theorem sum_Icc_rpow_sub_one_le {k : ℝ} (hk0 : 0 < k) (hk1 : k < 1) {L : ℕ} (hL : 1 ≤ L) :
    ∑ m ∈ Finset.Icc 1 L, (m : ℝ) ^ (k - 1) ≤ 1 + (L : ℝ) ^ k / k := by
  induction L with
  | zero => omega
  | succ L ih =>
    rcases eq_or_lt_of_le (by omega : 0 ≤ L) with rfl | hLpos
    · simp only [zero_add, Finset.Icc_self, Finset.sum_singleton, Nat.cast_one, Real.one_rpow]
      have : 0 ≤ 1 / k := by positivity
      linarith
    · rw [Finset.sum_Icc_succ_top (by omega)]
      have hL_real : (0 : ℝ) < L := by exact_mod_cast hLpos
      have hstep : ((L + 1 : ℕ) : ℝ) ^ (k - 1) ≤ (((L + 1 : ℕ) : ℝ) ^ k - (L : ℝ) ^ k) / k := by
        have hmono : ((L + 1 : ℕ) : ℝ) ^ (k - 1) ≤
            ∫ t : ℝ in (L : ℝ)..((L + 1 : ℕ) : ℝ), t ^ (k - 1) := by
          have hconst : ((L + 1 : ℕ) : ℝ) ^ (k - 1) =
              ∫ _ : ℝ in (L : ℝ)..((L + 1 : ℕ) : ℝ), ((L + 1 : ℕ) : ℝ) ^ (k - 1) := by
            rw [intervalIntegral.integral_const, smul_eq_mul]; push_cast; ring
          rw [hconst, intervalIntegral.integral_of_le (by push_cast; linarith),
            intervalIntegral.integral_of_le (by push_cast; linarith)]
          have hi : IntervalIntegrable (fun t : ℝ => t ^ (k - 1)) volume
              (L : ℝ) ((L + 1 : ℕ) : ℝ) := by
            refine intervalIntegral.intervalIntegrable_rpow
              (Or.inr <| notMem_uIcc_of_lt hL_real (by positivity))
          refine setIntegral_mono_on
            (integrableOn_const (hs := ((measure_mono Ioc_subset_Icc_self).trans_lt
              isCompact_Icc.measure_lt_top).ne))
            hi.1 measurableSet_Ioc fun t ht => ?_
          have ht_pos : 0 < t := hL_real.trans ht.1
          rw [show k - 1 = -(1 - k) by ring, Real.rpow_neg (by positivity),
            Real.rpow_neg ht_pos.le]
          exact inv_anti₀ (Real.rpow_pos_of_pos ht_pos _)
            (Real.rpow_le_rpow ht_pos.le ht.2 (by linarith))
        have h0 : (0 : ℝ) ∉ uIcc (L : ℝ) ((L + 1 : ℕ) : ℝ) :=
          notMem_uIcc_of_lt hL_real (by positivity)
        rw [integral_rpow (Or.inr ⟨by linarith, h0⟩), show k - 1 + 1 = k by ring] at hmono
        exact hmono
      have hih := ih hLpos
      linarith [show (L : ℝ) ^ k / k + (((L + 1 : ℕ) : ℝ) ^ k - (L : ℝ) ^ k) / k =
        ((L + 1 : ℕ) : ℝ) ^ k / k by ring]

private theorem abs_setIntegral_le_setIntegral {s : Set ℝ} (hs : MeasurableSet s)
    {f : ℝ → ℝ} (C : ℝ) (hf : IntegrableOn f s) (hC : IntegrableOn (fun _ : ℝ => C) s)
    (hbound : ∀ x ∈ s, |f x| ≤ C) :
    |∫ x in s, f x| ≤ ∫ _ in s, C := by
  have h1 : |∫ x in s, f x| ≤ ∫ x in s, |f x| := by
    simpa only [Real.norm_eq_abs] using
      norm_integral_le_integral_norm (μ := volume.restrict s) f
  exact h1.trans (setIntegral_mono_on hf.abs hC hs hbound)

/-- Pointwise 1D Euler–Maclaurin bound comparing the discrete `m`-sum to `tateProfileIntegral`. -/
private theorem abs_mul_sum_sub_tateProfileIntegral_le {k A K : ℝ} (hk0 : 0 < k) (hk1 : k < 1)
    (_ : 0 ≤ A) (hK : 0 ≤ K) {H : ℝ → ℝ} (hH : IsWindowTest A H)
    (hK0 : ∀ w, |H w| ≤ K * Real.exp (w / 2)) (hK1 : ∀ w, |deriv H w| ≤ K * Real.exp (w / 2))
    {d : ℕ} (hd1 : 1 ≤ d) (hdN : d ≤ windowLevel A) (u : ℝ) :
    |H u * (∑ m ∈ Finset.Icc 1 (windowLevel A / d),
        (m : ℝ) ^ (k - 1 / 2) * H (u + Real.log d + Real.log m) -
      tateProfileIntegral H k (u + Real.log d))| ≤
      Set.indicator (Icc (-A) 0)
        (fun _ => (3 + 2 / k) * K ^ 2 / Real.sqrt d) u := by
  by_cases hu : u ∈ Icc (-A) 0
  · rw [Set.indicator_of_mem hu, abs_mul]
    set y : ℝ := u + Real.log d
    set M : ℕ := windowLevel A / d
    have hd_pos : (0 : ℝ) < d := by exact_mod_cast hd1
    have hM1 : 1 ≤ M := Nat.div_pos hdN hd1
    set g : ℝ → ℝ := fun x => x ^ (k - 1 / 2) * H (y + Real.log x)
    have hg_bound : ∀ {x : ℝ}, 0 < x → |g x| ≤ K * Real.exp (y / 2) * x ^ k := by
      intro x hx
      dsimp only [g]
      rw [abs_mul, abs_of_pos (Real.rpow_pos_of_pos hx _)]
      have h1 := hK0 (y + Real.log x)
      have hexp : Real.exp ((y + Real.log x) / 2) = Real.exp (y / 2) * x ^ (1 / 2 : ℝ) := by
        rw [add_div, Real.exp_add, Real.rpow_def_of_pos hx]
        congr 1; congr 1; ring
      calc x ^ (k - 1 / 2) * |H (y + Real.log x)|
          ≤ x ^ (k - 1 / 2) * (K * Real.exp ((y + Real.log x) / 2)) :=
            mul_le_mul_of_nonneg_left h1 (Real.rpow_pos_of_pos hx _).le
        _ = K * Real.exp (y / 2) * (x ^ (k - 1 / 2) * x ^ (1 / 2 : ℝ)) := by rw [hexp]; ring
        _ = K * Real.exp (y / 2) * x ^ k := by
            rw [← Real.rpow_add hx]; congr 2; ring
    have hg_vanish_gt : ∀ {x : ℝ}, Real.exp (-y) < x → g x = 0 := by
      intro x hx
      have hly : 0 < y + Real.log x := by
        have := Real.log_lt_log (Real.exp_pos _) hx
        rw [Real.log_exp] at this; linarith
      dsimp only [g]
      rw [hH.vanish _ (fun hm => by linarith [hm.2]), mul_zero]
    have hexp_lt_M1 : Real.exp (-y) < ((M + 1 : ℕ) : ℝ) := by
      have hN_lt : Real.exp A < ((windowLevel A : ℝ) + 1) := Nat.lt_floor_add_one (Real.exp A)
      have hdiv_gt : windowLevel A + 1 ≤ (M + 1) * d := by
        have hmod := Nat.div_add_mod (windowLevel A) d
        have hlt := Nat.mod_lt (windowLevel A) hd1
        dsimp only [M]; nlinarith
      have hcast : (windowLevel A : ℝ) + 1 ≤ ((M + 1 : ℕ) : ℝ) * (d : ℝ) := by
        exact_mod_cast hdiv_gt
      have hexp_u : Real.exp (-u) ≤ Real.exp A := Real.exp_le_exp.mpr (by linarith [hu.1])
      have hexp_y : Real.exp (-y) = Real.exp (-u) / (d : ℝ) := by
        dsimp only [y]
        simp only [neg_add, Real.exp_add, Real.exp_neg, Real.exp_log hd_pos, div_eq_mul_inv]
      rw [hexp_y, div_lt_iff₀ hd_pos]
      linarith
    have hg_int_Ioc : ∀ R : ℝ, IntegrableOn g (Ioc 0 R) := by
      intro R
      set B0 := K * Real.exp (y / 2) * (max 1 R) ^ k
      have hdom : IntegrableOn (fun _ : ℝ => B0) (Ioc 0 R) :=
        integrableOn_const (hs := ((measure_mono Ioc_subset_Icc_self).trans_lt
          isCompact_Icc.measure_lt_top).ne)
      have hcont : ContinuousOn g (Ioc 0 R) := by
        intro x hx
        refine ContinuousAt.continuousWithinAt ?_
        dsimp only [g]
        exact (continuousAt_id.rpow continuousAt_const (Or.inl hx.1.ne')).mul
          (hH.continuous.continuousAt.comp
            (continuousAt_const.add (Real.continuousAt_log hx.1.ne')))
      refine Integrable.mono' hdom (hcont.aestronglyMeasurable measurableSet_Ioc) ?_
      refine (ae_restrict_mem measurableSet_Ioc).mono fun x hx => ?_
      rw [Real.norm_eq_abs]
      calc |g x| ≤ K * Real.exp (y / 2) * x ^ k := hg_bound hx.1
        _ ≤ B0 := mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow hx.1.le (hx.2.trans (le_max_right 1 R)) hk0.le)
            (by positivity)
    have hsplit_Ioi : tateProfileIntegral H k y =
        (∫ x in (0 : ℝ)..1, g x) +
          ∑ m ∈ Finset.Icc 1 M, ∫ x in (m : ℝ)..((m + 1 : ℕ) : ℝ), g x := by
      unfold tateProfileIntegral
      change (∫ x in Ioi (0 : ℝ), g x) = _
      have hunion : Ioi (0 : ℝ) = Ioc 0 ((M + 1 : ℕ) : ℝ) ∪ Ioi ((M + 1 : ℕ) : ℝ) :=
        (Ioc_union_Ioi_eq_Ioi (by positivity)).symm
      have hdisj : Disjoint (Ioc 0 ((M + 1 : ℕ) : ℝ)) (Ioi ((M + 1 : ℕ) : ℝ)) :=
        Ioc_disjoint_Ioi le_rfl
      have hzero_tail : ∀ x ∈ Ioi ((M + 1 : ℕ) : ℝ), g x = 0 := fun x hx =>
        hg_vanish_gt (hexp_lt_M1.trans hx)
      have hint_tail : IntegrableOn g (Ioi ((M + 1 : ℕ) : ℝ)) :=
        (integrableOn_zero (μ := volume) (s := Ioi ((M + 1 : ℕ) : ℝ))).congr_fun
          (fun x hx => (hzero_tail x hx).symm) measurableSet_Ioi
      rw [hunion, setIntegral_union hdisj measurableSet_Ioi
        (hg_int_Ioc ((M + 1 : ℕ) : ℝ)) hint_tail,
        setIntegral_eq_zero_of_forall_eq_zero hzero_tail, add_zero,
        ← intervalIntegral.integral_of_le (by positivity)]
      have hadj : ∀ L : ℕ, 1 ≤ L →
          (∫ x in (0 : ℝ)..((L + 1 : ℕ) : ℝ), g x) =
            (∫ x in (0 : ℝ)..1, g x) +
              ∑ m ∈ Finset.Icc 1 L, ∫ x in (m : ℝ)..((m + 1 : ℕ) : ℝ), g x := by
        intro L hL1
        induction L with
        | zero => omega
        | succ L ih =>
          rcases eq_or_lt_of_le (by omega : 0 ≤ L) with rfl | hLpos
          · simp only [zero_add, Finset.Icc_self, Finset.sum_singleton, Nat.cast_one]
            exact (intervalIntegral.integral_add_adjacent_intervals
              (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one |>.mpr (hg_int_Ioc 1))
              (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num) |>.mpr
                ((hg_int_Ioc 2).mono_set (Ioc_subset_Ioc_left zero_le_one)))).symm
          · rw [Finset.sum_Icc_succ_top (by omega), ← add_assoc, ← ih hLpos]
            exact (intervalIntegral.integral_add_adjacent_intervals
              (intervalIntegrable_iff_integrableOn_Ioc_of_le (by positivity) |>.mpr
                (hg_int_Ioc ((L + 1 : ℕ) : ℝ)))
              (intervalIntegrable_iff_integrableOn_Ioc_of_le (by push_cast; linarith) |>.mpr
                ((hg_int_Ioc ((L + 1 + 1 : ℕ) : ℝ)).mono_set
                  (Ioc_subset_Ioc_left (by positivity))))).symm
      exact hadj M hM1
    have hsum_g : ∑ m ∈ Finset.Icc 1 M,
        (m : ℝ) ^ (k - 1 / 2) * H (u + Real.log d + Real.log m) =
        ∑ m ∈ Finset.Icc 1 M, g m := rfl
    rw [hsum_g, hsplit_Ioi]
    have hrew : (∑ m ∈ Finset.Icc 1 M, g m) -
        ((∫ x in (0 : ℝ)..1, g x) +
          ∑ m ∈ Finset.Icc 1 M, ∫ x in (m : ℝ)..((m + 1 : ℕ) : ℝ), g x) =
        -(∫ x in (0 : ℝ)..1, g x) +
          ∑ m ∈ Finset.Icc 1 M, (g m - ∫ x in (m : ℝ)..((m + 1 : ℕ) : ℝ), g x) := by
      rw [← sub_sub, Finset.sum_sub_distrib]; ring
    rw [hrew]
    rcases le_or_gt y 0 with hy | hy
    · have h01 : |∫ x in (0 : ℝ)..1, g x| ≤ K * Real.exp (y / 2) := by
        rw [intervalIntegral.integral_of_le zero_le_one]
        have h1 : |∫ x in Ioc (0 : ℝ) 1, g x| ≤
            ∫ _ in Ioc (0 : ℝ) 1, K * Real.exp (y / 2) := by
          refine abs_setIntegral_le_setIntegral measurableSet_Ioc (K * Real.exp (y / 2))
            (hg_int_Ioc 1)
            (integrableOn_const (hs := ((measure_mono Ioc_subset_Icc_self).trans_lt
              isCompact_Icc.measure_lt_top).ne)) fun x hx => ?_
          calc |g x| ≤ K * Real.exp (y / 2) * x ^ k := hg_bound hx.1
            _ ≤ K * Real.exp (y / 2) * 1 := mul_le_mul_of_nonneg_left
                (Real.rpow_le_one hx.1.le hx.2 hk0.le) (by positivity)
            _ = K * Real.exp (y / 2) := mul_one _
        rw [setIntegral_const, Real.volume_real_Ioc_of_le zero_le_one,
          sub_zero, one_smul] at h1
        exact h1
      set L : ℕ := ⌊Real.exp (-y)⌋₊
      have hL1 : 1 ≤ L := (Nat.one_le_floor_iff _).mpr (Real.one_le_exp (by linarith))
      have hm_term : ∀ m ∈ Finset.Icc 1 M,
          |g m - ∫ x in (m : ℝ)..((m + 1 : ℕ) : ℝ), g x| ≤
            if m ≤ L then 2 * K * Real.exp (y / 2) * (m : ℝ) ^ (k - 1) else 0 := by
        intro m hm
        have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
        split_ifs with hmL
        · have hgm_const : g m = ∫ _ in (m : ℝ)..((m + 1 : ℕ) : ℝ), g m := by
            rw [intervalIntegral.integral_const, smul_eq_mul]; push_cast; ring
          have hint_m : IntervalIntegrable g volume (m : ℝ) ((m + 1 : ℕ) : ℝ) :=
            (intervalIntegrable_iff_integrableOn_Ioc_of_le (by push_cast; linarith)).mpr
              ((hg_int_Ioc ((m + 1 : ℕ) : ℝ)).mono_set (Ioc_subset_Ioc_left (by positivity)))
          rw [hgm_const, ← intervalIntegral.integral_sub intervalIntegrable_const hint_m,
            intervalIntegral.integral_of_le (by push_cast; linarith)]
          set C_m := 2 * K * Real.exp (y / 2) * (m : ℝ) ^ (k - 1)
          have hder_m : ∀ t ∈ Icc (m : ℝ) ((m + 1 : ℕ) : ℝ),
              HasDerivWithinAt g
                ((k - 1 / 2) * t ^ (k - 3 / 2) * H (y + Real.log t) +
                  t ^ (k - 1 / 2) * (deriv H (y + Real.log t) * t⁻¹))
                (Icc (m : ℝ) ((m + 1 : ℕ) : ℝ)) t := by
            intro t ht
            have ht_pos : 0 < t := lt_of_lt_of_le (by exact_mod_cast hm1) ht.1
            have hd_rpow : HasDerivAt (fun s : ℝ => s ^ (k - 1 / 2))
                ((k - 1 / 2) * t ^ (k - 1 / 2 - 1)) t := by
              simpa using Real.hasDerivAt_rpow_const (p := k - 1 / 2) (Or.inl ht_pos.ne')
            have hd_H : HasDerivAt (fun s : ℝ => H (y + Real.log s))
                (deriv H (y + Real.log t) * t⁻¹) t := by
              have hH_diff : DifferentiableAt ℝ H (y + Real.log t) :=
                (hH.contDiff.differentiable (by norm_num)).differentiableAt
              exact hH_diff.hasDerivAt.comp t ((Real.hasDerivAt_log ht_pos.ne').const_add y)
            refine (hd_rpow.mul hd_H).congr_deriv ?_ |>.hasDerivWithinAt
            rw [show k - 1 / 2 - 1 = k - 3 / 2 by ring]
          have hbound_m : ∀ t ∈ Icc (m : ℝ) ((m + 1 : ℕ) : ℝ),
              ‖(k - 1 / 2) * t ^ (k - 3 / 2) * H (y + Real.log t) +
                t ^ (k - 1 / 2) * (deriv H (y + Real.log t) * t⁻¹)‖ ≤ C_m := by
            intro t ht
            have hm_pos : (0 : ℝ) < m := by exact_mod_cast hm1
            have ht_pos : 0 < t := lt_of_lt_of_le hm_pos ht.1
            rw [Real.norm_eq_abs]
            have hexp_t : Real.exp ((y + Real.log t) / 2) =
                Real.exp (y / 2) * t ^ (1 / 2 : ℝ) := by
              rw [add_div, Real.exp_add, Real.rpow_def_of_pos ht_pos]
              congr 1; congr 1; ring
            have ht_le_m : t ^ (k - 1) ≤ (m : ℝ) ^ (k - 1) := by
              rw [show k - 1 = -(1 - k) by ring, Real.rpow_neg ht_pos.le,
                Real.rpow_neg hm_pos.le]
              exact inv_anti₀ (Real.rpow_pos_of_pos hm_pos _)
                (Real.rpow_le_rpow hm_pos.le ht.1 (by linarith))
            have hterm1 : |(k - 1 / 2) * t ^ (k - 3 / 2) * H (y + Real.log t)| ≤
                K * Real.exp (y / 2) * (m : ℝ) ^ (k - 1) := by
              rw [abs_mul, abs_mul, abs_of_pos (Real.rpow_pos_of_pos ht_pos _)]
              have hk_abs : |k - 1 / 2| ≤ 1 := by rw [abs_le]; constructor <;> linarith
              calc |k - 1 / 2| * t ^ (k - 3 / 2) * |H (y + Real.log t)|
                  ≤ 1 * t ^ (k - 3 / 2) * (K * Real.exp ((y + Real.log t) / 2)) :=
                    mul_le_mul (mul_le_mul_of_nonneg_right hk_abs
                      (Real.rpow_pos_of_pos ht_pos _).le) (hK0 _) (abs_nonneg _) (by positivity)
                _ = K * Real.exp (y / 2) * (t ^ (k - 3 / 2) * t ^ (1 / 2 : ℝ)) := by
                    rw [hexp_t]; ring
                _ = K * Real.exp (y / 2) * t ^ (k - 1) := by
                    rw [← Real.rpow_add ht_pos]; congr 2; ring
                _ ≤ K * Real.exp (y / 2) * (m : ℝ) ^ (k - 1) :=
                    mul_le_mul_of_nonneg_left ht_le_m (by positivity)
            have hterm2 : |t ^ (k - 1 / 2) * (deriv H (y + Real.log t) * t⁻¹)| ≤
                K * Real.exp (y / 2) * (m : ℝ) ^ (k - 1) := by
              rw [abs_mul, abs_mul, abs_of_pos (Real.rpow_pos_of_pos ht_pos _),
                abs_of_pos (inv_pos.mpr ht_pos)]
              calc t ^ (k - 1 / 2) * (|deriv H (y + Real.log t)| * t⁻¹)
                  ≤ t ^ (k - 1 / 2) * (K * Real.exp ((y + Real.log t) / 2) * t⁻¹) :=
                    mul_le_mul_of_nonneg_left
                      (mul_le_mul_of_nonneg_right (hK1 _) (inv_pos.mpr ht_pos).le)
                      (Real.rpow_pos_of_pos ht_pos _).le
                _ = K * Real.exp (y / 2) * (t ^ (k - 1 / 2) * t ^ (1 / 2 : ℝ) * t ^ (-1 : ℝ)) := by
                    rw [hexp_t, Real.rpow_neg_one]; ring
                _ = K * Real.exp (y / 2) * t ^ (k - 1) := by
                    rw [← Real.rpow_add ht_pos, ← Real.rpow_add ht_pos]; congr 2; ring
                _ ≤ K * Real.exp (y / 2) * (m : ℝ) ^ (k - 1) :=
                    mul_le_mul_of_nonneg_left ht_le_m (by positivity)
            calc |((k - 1 / 2) * t ^ (k - 3 / 2) * H (y + Real.log t)) +
                  (t ^ (k - 1 / 2) * (deriv H (y + Real.log t) * t⁻¹))|
                ≤ |((k - 1 / 2) * t ^ (k - 3 / 2) * H (y + Real.log t))| +
                  |t ^ (k - 1 / 2) * (deriv H (y + Real.log t) * t⁻¹)| := abs_add_le _ _
              _ ≤ C_m := by dsimp only [C_m]; linarith
          have hmvt : ∀ x ∈ Ioc (m : ℝ) ((m + 1 : ℕ) : ℝ), ‖g m - g x‖ ≤ C_m := by
            intro x hx
            have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hder_m hbound_m
              (convex_Icc _ _) ⟨hx.1.le, hx.2⟩ ⟨le_rfl, by push_cast; linarith⟩
            have hlen : ‖(m : ℝ) - x‖ ≤ 1 := by
              rw [Real.norm_eq_abs, abs_sub_comm, abs_of_pos (sub_pos.mpr hx.1)]
              push_cast at hx; linarith [hx.2]
            calc ‖g m - g x‖ ≤ C_m * ‖(m : ℝ) - x‖ := h
              _ ≤ C_m * 1 := mul_le_mul_of_nonneg_left hlen (by dsimp only [C_m]; positivity)
              _ = C_m := mul_one _
          have hint_diff : IntegrableOn (fun x => g m - g x) (Ioc (m : ℝ) ((m + 1 : ℕ) : ℝ)) :=
            (integrableOn_const (hs := ((measure_mono Ioc_subset_Icc_self).trans_lt
              isCompact_Icc.measure_lt_top).ne)).sub hint_m.1
          have hnorm := abs_setIntegral_le_setIntegral measurableSet_Ioc C_m hint_diff
            (integrableOn_const (hs := ((measure_mono Ioc_subset_Icc_self).trans_lt
              isCompact_Icc.measure_lt_top).ne))
            (fun x hx => by simpa only [Real.norm_eq_abs] using hmvt x hx)
          rw [setIntegral_const,
            Real.volume_real_Ioc_of_le (by push_cast; linarith), smul_eq_mul] at hnorm
          have h1 : ((m + 1 : ℕ) : ℝ) - (m : ℝ) = 1 := by push_cast; ring
          rw [h1, one_mul] at hnorm
          exact hnorm
        · have hm_gt : Real.exp (-y) < (m : ℝ) :=
            Nat.lt_of_floor_lt (not_le.mp hmL)
          have hgm0 : g m = 0 := hg_vanish_gt hm_gt
          have hint0 : (∫ x in (m : ℝ)..((m + 1 : ℕ) : ℝ), g x) = 0 := by
            rw [intervalIntegral.integral_of_le (by push_cast; linarith)]
            exact setIntegral_eq_zero_of_forall_eq_zero fun x hx =>
              hg_vanish_gt (hm_gt.trans hx.1)
          rw [hgm0, hint0, sub_zero, abs_zero]
      have hsum_le : |∑ m ∈ Finset.Icc 1 M, (g m - ∫ x in (m : ℝ)..((m + 1 : ℕ) : ℝ), g x)| ≤
          2 * K * Real.exp (y / 2) * (1 + Real.exp (-k * y) / k) := by
        have htri := (Finset.abs_sum_le_sum_abs _ (Finset.Icc 1 M)).trans
          (Finset.sum_le_sum hm_term)
        have hsub_sum : ∑ m ∈ Finset.Icc 1 M,
            (if m ≤ L then 2 * K * Real.exp (y / 2) * (m : ℝ) ^ (k - 1) else 0) ≤
            ∑ m ∈ Finset.Icc 1 L, 2 * K * Real.exp (y / 2) * (m : ℝ) ^ (k - 1) := by
          rw [← Finset.sum_filter]
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => by positivity
          intro m hm
          simp only [Finset.mem_filter, Finset.mem_Icc] at hm ⊢
          exact ⟨hm.1.1, hm.2⟩
        rw [← Finset.mul_sum] at hsub_sum
        have hLk : (L : ℝ) ^ k ≤ Real.exp (-k * y) := by
          have hL_le : (L : ℝ) ≤ Real.exp (-y) := Nat.floor_le (Real.exp_pos _).le
          calc (L : ℝ) ^ k ≤ Real.exp (-y) ^ k :=
                Real.rpow_le_rpow (Nat.cast_nonneg L) hL_le hk0.le
            _ = Real.exp (-k * y) := by
                rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]; congr 1; ring
        have hrp := sum_Icc_rpow_sub_one_le hk0 hk1 hL1
        have htot : 2 * K * Real.exp (y / 2) * ∑ m ∈ Finset.Icc 1 L, (m : ℝ) ^ (k - 1) ≤
            2 * K * Real.exp (y / 2) * (1 + Real.exp (-k * y) / k) :=
          mul_le_mul_of_nonneg_left
            (hrp.trans (add_le_add_right (div_le_div_of_nonneg_right hLk hk0.le) 1))
            (by positivity)
        exact htri.trans (hsub_sum.trans htot)
      have htot_diff : |-(∫ x in (0 : ℝ)..1, g x) +
          ∑ m ∈ Finset.Icc 1 M, (g m - ∫ x in (m : ℝ)..((m + 1 : ℕ) : ℝ), g x)| ≤
          3 * K * Real.exp (y / 2) + (2 / k) * K * Real.exp ((1 / 2 - k) * y) := by
        have habs_add := abs_add_le (-(∫ x in (0 : ℝ)..1, g x))
          (∑ m ∈ Finset.Icc 1 M, (g m - ∫ x in (m : ℝ)..((m + 1 : ℕ) : ℝ), g x))
        rw [abs_neg] at habs_add
        have hexp_prod : Real.exp (y / 2) * Real.exp (-k * y) = Real.exp ((1 / 2 - k) * y) := by
          rw [← Real.exp_add]; congr 1; ring
        have h2 : 2 * K * Real.exp (y / 2) * (1 + Real.exp (-k * y) / k) =
            2 * K * Real.exp (y / 2) + (2 / k) * K * Real.exp ((1 / 2 - k) * y) := by
          calc 2 * K * Real.exp (y / 2) * (1 + Real.exp (-k * y) / k)
              = 2 * K * Real.exp (y / 2) +
                (2 / k) * K * (Real.exp (y / 2) * Real.exp (-k * y)) := by ring
            _ = 2 * K * Real.exp (y / 2) + (2 / k) * K * Real.exp ((1 / 2 - k) * y) := by
                rw [hexp_prod]
        linarith
      have hexp1 : Real.exp (u / 2) * Real.exp (y / 2) ≤ 1 / Real.sqrt d := by
        rw [← Real.exp_add, Real.sqrt_eq_rpow, one_div, ← Real.rpow_neg hd_pos.le,
          Real.rpow_def_of_pos hd_pos]
        refine Real.exp_le_exp.mpr ?_
        have h1 : u / 2 + y / 2 = y - Real.log d / 2 := by dsimp only [y]; ring
        linarith
      have hexp2 : Real.exp (u / 2) * Real.exp ((1 / 2 - k) * y) ≤ 1 / Real.sqrt d := by
        rw [← Real.exp_add, Real.sqrt_eq_rpow, one_div ((d : ℝ) ^ _), ← Real.rpow_neg hd_pos.le,
          Real.rpow_def_of_pos hd_pos]
        refine Real.exp_le_exp.mpr ?_
        have h1 : u / 2 + (1 / 2 - k) * y = (1 - k) * y - Real.log d / 2 := by
          dsimp only [y]; ring
        have h2 : (1 - k) * y ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith) hy
        linarith
      calc |H u| * |-(∫ x in (0 : ℝ)..1, g x) +
            ∑ m ∈ Finset.Icc 1 M, (g m - ∫ x in (m : ℝ)..((m + 1 : ℕ) : ℝ), g x)|
          ≤ (K * Real.exp (u / 2)) *
              (3 * K * Real.exp (y / 2) + (2 / k) * K * Real.exp ((1 / 2 - k) * y)) :=
            mul_le_mul (hK0 u) htot_diff (abs_nonneg _) (by positivity)
        _ = 3 * K ^ 2 * (Real.exp (u / 2) * Real.exp (y / 2)) +
              (2 / k) * K ^ 2 * (Real.exp (u / 2) * Real.exp ((1 / 2 - k) * y)) := by ring
        _ ≤ 3 * K ^ 2 * (1 / Real.sqrt d) + (2 / k) * K ^ 2 * (1 / Real.sqrt d) :=
            add_le_add (mul_le_mul_of_nonneg_left hexp1 (by positivity))
              (mul_le_mul_of_nonneg_left hexp2 (by positivity))
        _ = (3 + 2 / k) * K ^ 2 / Real.sqrt d := by ring
    · have hexp_lt1 : Real.exp (-y) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
      have h01 : |∫ x in (0 : ℝ)..1, g x| ≤ K * Real.exp (-y / 2) := by
        rw [intervalIntegral.integral_of_le zero_le_one]
        have hunion : Ioc (0 : ℝ) 1 = Ioc 0 (Real.exp (-y)) ∪ Ioc (Real.exp (-y)) 1 :=
          (Ioc_union_Ioc_eq_Ioc (Real.exp_pos _).le hexp_lt1.le).symm
        have hdisj : Disjoint (Ioc 0 (Real.exp (-y))) (Ioc (Real.exp (-y)) 1) :=
          Set.disjoint_iff.mpr fun x hx => lt_irrefl _ (hx.1.2.trans_lt hx.2.1)
        have hzero2 : (∫ x in Ioc (Real.exp (-y)) 1, g x) = 0 :=
          setIntegral_eq_zero_of_forall_eq_zero fun x hx => hg_vanish_gt hx.1
        rw [hunion, setIntegral_union hdisj measurableSet_Ioc
          (hg_int_Ioc (Real.exp (-y)))
          ((hg_int_Ioc 1).mono_set (Ioc_subset_Ioc_left (Real.exp_pos _).le)),
          hzero2, add_zero]
        have hnorm := abs_setIntegral_le_setIntegral measurableSet_Ioc (K * Real.exp (y / 2))
          (hg_int_Ioc (Real.exp (-y)))
          (integrableOn_const (hs := ((measure_mono Ioc_subset_Icc_self).trans_lt
            isCompact_Icc.measure_lt_top).ne))
          (fun x hx => by
            calc |g x| ≤ K * Real.exp (y / 2) * x ^ k := hg_bound hx.1
              _ ≤ K * Real.exp (y / 2) * 1 := mul_le_mul_of_nonneg_left
                  (Real.rpow_le_one hx.1.le (hx.2.trans hexp_lt1.le) hk0.le) (by positivity)
              _ = K * Real.exp (y / 2) := mul_one _)
        rw [setIntegral_const,
          Real.volume_real_Ioc_of_le (Real.exp_pos _).le, sub_zero, smul_eq_mul] at hnorm
        have hprod : Real.exp (-y) * (K * Real.exp (y / 2)) = K * Real.exp (-y / 2) := by
          calc Real.exp (-y) * (K * Real.exp (y / 2))
              = K * (Real.exp (-y) * Real.exp (y / 2)) := by ring
            _ = K * Real.exp (-y / 2) := by rw [← Real.exp_add]; congr 1; congr 1; ring
        rwa [hprod] at hnorm
      have hsum_zero : ∑ m ∈ Finset.Icc 1 M,
          (g m - ∫ x in (m : ℝ)..((m + 1 : ℕ) : ℝ), g x) = 0 := by
        refine Finset.sum_eq_zero fun m hm => ?_
        have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (Finset.mem_Icc.mp hm).1
        rw [hg_vanish_gt (hexp_lt1.trans_le hm1),
          intervalIntegral.integral_of_le (by push_cast; linarith),
          setIntegral_eq_zero_of_forall_eq_zero (fun x hx =>
            hg_vanish_gt ((hexp_lt1.trans_le hm1).trans hx.1)), sub_self]
      rw [hsum_zero, add_zero, abs_neg]
      have hexp_eq : Real.exp (u / 2) * Real.exp (-y / 2) = 1 / Real.sqrt d := by
        rw [← Real.exp_add, show u / 2 + -y / 2 = -(Real.log d * (1 / 2)) by dsimp only [y]; ring,
          Real.exp_neg, ← Real.rpow_def_of_pos hd_pos, ← Real.sqrt_eq_rpow, one_div]
      calc |H u| * |∫ x in (0 : ℝ)..1, g x|
          ≤ (K * Real.exp (u / 2)) * (K * Real.exp (-y / 2)) :=
            mul_le_mul (hK0 u) h01 (abs_nonneg _) (by positivity)
        _ = K ^ 2 * (Real.exp (u / 2) * Real.exp (-y / 2)) := by ring
        _ = K ^ 2 / Real.sqrt d := by rw [hexp_eq]; ring
        _ ≤ (3 + 2 / k) * K ^ 2 / Real.sqrt d := by
            refine div_le_div_of_nonneg_right ?_ (Real.sqrt_nonneg _)
            have : 0 ≤ (2 + 2 / k) * K ^ 2 := by positivity
            linarith
  · rw [Set.indicator_of_notMem hu, hH.vanish u hu, zero_mul, abs_zero]

/-- **1D Dirichlet hyperbola asymptotic for `tatePointCount`**: for every `k ∈ (0, 1)`, there exists
`C_k ≥ 0` such that on any window test `H` with `|H(w)|, |H'(w)| ≤ K e^{w/2}`,
`|tatePointCount A H k − eulerProductPoleWeight k · shiftedPoleForm k H| ≤ C_k K² (A + 1)²`. -/
theorem abs_tatePointCount_sub_eulerProduct_shiftedPoleForm_le {k : ℝ} (hk0 : 0 < k) (hk1 : k < 1) :
    ∃ C_k : ℝ, 0 ≤ C_k ∧ ∀ A K : ℝ, 0 ≤ A → 0 ≤ K → ∀ H : ℝ → ℝ, IsWindowTest A H →
      (∀ w, |H w| ≤ K * Real.exp (w / 2)) →
      (∀ w, |deriv H w| ≤ K * Real.exp (w / 2)) →
      |tatePointCount A H k - eulerProductPoleWeight k * shiftedPoleForm k H| ≤
        C_k * K ^ 2 * (A + 1) ^ 2 := by
  set C_k : ℝ := 2 * (3 + 2 / k) + 2 + 4 * (2 : ℝ) ^ k / k
  refine ⟨C_k, by positivity, fun A K hA hK H hH hK0 hK1 => ?_⟩
  set N := windowLevel A
  have hN1 : 1 ≤ N := one_le_windowLevel_of_nonneg hA
  have hmain_id : tatePointCount A H k -
      (∑ d ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius d : ℝ) / (d : ℝ) ^ (1 + k)) *
        shiftedPoleForm k H =
      (2 * tateFunction A H k -
        ∑ d ∈ Finset.Icc 1 N, 2 * (((ArithmeticFunction.moebius d : ℝ) / Real.sqrt d) *
          ∫ u, H u * tateProfileIntegral H k (u + Real.log d))) -
        2 * ∫ u, H u ^ 2 := by
    rw [tatePointCount, Finset.sum_mul]
    have hcongr : ∑ d ∈ Finset.Icc 1 N,
        ((ArithmeticFunction.moebius d : ℝ) / (d : ℝ) ^ (1 + k)) * shiftedPoleForm k H =
        ∑ d ∈ Finset.Icc 1 N, 2 * (((ArithmeticFunction.moebius d : ℝ) / Real.sqrt d) *
          ∫ u, H u * tateProfileIntegral H k (u + Real.log d)) :=
      Finset.sum_congr rfl fun d hd =>
        (two_mul_integral_mul_tateProfileIntegral H k (Finset.mem_Icc.mp hd).1).symm
    rw [hcongr]; ring
  have herr_sum : |2 * tateFunction A H k -
      ∑ d ∈ Finset.Icc 1 N, 2 * (((ArithmeticFunction.moebius d : ℝ) / Real.sqrt d) *
        ∫ u, H u * tateProfileIntegral H k (u + Real.log d))| ≤
      2 * (3 + 2 / k) * K ^ 2 * (A * (A + 1)) := by
    rw [two_mul_tateFunction_eq_moebius_sum hH k, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hd_bound : ∀ d ∈ Finset.Icc 1 N,
        |2 * (((ArithmeticFunction.moebius d : ℝ) / Real.sqrt d) *
            ∫ u, H u * ∑ m ∈ Finset.Icc 1 (N / d),
              (m : ℝ) ^ (k - 1 / 2) * H (u + Real.log d + Real.log m)) -
          2 * (((ArithmeticFunction.moebius d : ℝ) / Real.sqrt d) *
            ∫ u, H u * tateProfileIntegral H k (u + Real.log d))| ≤
        2 * (3 + 2 / k) * K ^ 2 * A * (1 / (d : ℝ)) := by
      intro d hd
      obtain ⟨hd1, hdN⟩ := Finset.mem_Icc.mp hd
      have hd_pos : (0 : ℝ) < d := by exact_mod_cast hd1
      have hint1 : Integrable fun u => H u * ∑ m ∈ Finset.Icc 1 (N / d),
          (m : ℝ) ^ (k - 1 / 2) * H (u + Real.log d + Real.log m) := by
        have hc : Continuous fun u => ∑ m ∈ Finset.Icc 1 (N / d),
            (m : ℝ) ^ (k - 1 / 2) * H (u + Real.log d + Real.log m) :=
          continuous_finsetSum _ fun m _ => continuous_const.mul
            (hH.continuous.comp ((continuous_id.add continuous_const).add continuous_const))
        exact (hH.continuous.mul hc).integrable_of_hasCompactSupport hH.hasCompactSupport.mul_right
      have hint2 : Integrable fun u => H u * tateProfileIntegral H k (u + Real.log d) := by
        have heq : (fun u => H u * tateProfileIntegral H k (u + Real.log d)) = fun u =>
            H u * (Real.exp (-(1 / 2 + k) * (u + Real.log d)) *
              ∫ w, H w * Real.exp ((1 / 2 + k) * w)) := by
          funext u; rw [tateProfileIntegral_eq]
        rw [heq]
        exact (hH.continuous.mul ((by fun_prop : Continuous fun u : ℝ =>
          Real.exp (-(1 / 2 + k) * (u + Real.log d))).mul continuous_const)).integrable_of_hasCompactSupport
            hH.hasCompactSupport.mul_right
      have hcomb : 2 * (((ArithmeticFunction.moebius d : ℝ) / Real.sqrt d) *
            ∫ u, H u * ∑ m ∈ Finset.Icc 1 (N / d),
              (m : ℝ) ^ (k - 1 / 2) * H (u + Real.log d + Real.log m)) -
          2 * (((ArithmeticFunction.moebius d : ℝ) / Real.sqrt d) *
            ∫ u, H u * tateProfileIntegral H k (u + Real.log d)) =
          2 * ((ArithmeticFunction.moebius d : ℝ) / Real.sqrt d) *
            ∫ u, H u * (∑ m ∈ Finset.Icc 1 (N / d),
              (m : ℝ) ^ (k - 1 / 2) * H (u + Real.log d + Real.log m) -
                tateProfileIntegral H k (u + Real.log d)) := by
        have hsub : (∫ u, H u * ∑ m ∈ Finset.Icc 1 (N / d),
              (m : ℝ) ^ (k - 1 / 2) * H (u + Real.log d + Real.log m)) -
            (∫ u, H u * tateProfileIntegral H k (u + Real.log d)) =
            ∫ u, H u * (∑ m ∈ Finset.Icc 1 (N / d),
              (m : ℝ) ^ (k - 1 / 2) * H (u + Real.log d + Real.log m) -
                tateProfileIntegral H k (u + Real.log d)) := by
          rw [← integral_sub hint1 hint2]
          exact integral_congr_ae (Eventually.of_forall fun u => (mul_sub _ _ _).symm)
        rw [← hsub]; ring
      rw [hcomb, abs_mul, abs_mul, abs_of_pos (two_pos : (0 : ℝ) < 2), abs_div,
        abs_of_pos (Real.sqrt_pos.mpr hd_pos)]
      have hdom_ind : Integrable
          (Set.indicator (Icc (-A) 0) fun _ : ℝ => (3 + 2 / k) * K ^ 2 / Real.sqrt d) :=
        (integrableOn_const (hs := isCompact_Icc.measure_lt_top.ne)).integrable_indicator
          measurableSet_Icc
      have hint_u : |∫ u, H u * (∑ m ∈ Finset.Icc 1 (N / d),
            (m : ℝ) ^ (k - 1 / 2) * H (u + Real.log d + Real.log m) -
              tateProfileIntegral H k (u + Real.log d))| ≤
          A * ((3 + 2 / k) * K ^ 2 / Real.sqrt d) := by
        have h1 : |∫ u, H u * (∑ m ∈ Finset.Icc 1 (N / d),
              (m : ℝ) ^ (k - 1 / 2) * H (u + Real.log d + Real.log m) -
                tateProfileIntegral H k (u + Real.log d))| ≤
            ∫ u, |H u * (∑ m ∈ Finset.Icc 1 (N / d),
              (m : ℝ) ^ (k - 1 / 2) * H (u + Real.log d + Real.log m) -
                tateProfileIntegral H k (u + Real.log d))| := by
          simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (μ := volume)
            (fun u => H u * (∑ m ∈ Finset.Icc 1 (N / d),
              (m : ℝ) ^ (k - 1 / 2) * H (u + Real.log d + Real.log m) -
                tateProfileIntegral H k (u + Real.log d)))
        have h2 : ∫ u, |H u * (∑ m ∈ Finset.Icc 1 (N / d),
              (m : ℝ) ^ (k - 1 / 2) * H (u + Real.log d + Real.log m) -
                tateProfileIntegral H k (u + Real.log d))| ≤
            ∫ u, Set.indicator (Icc (-A) 0)
              (fun _ : ℝ => (3 + 2 / k) * K ^ 2 / Real.sqrt d) u :=
          integral_mono ((hint1.sub hint2).congr (Eventually.of_forall fun u => (mul_sub _ _ _).symm)).abs
            hdom_ind (abs_mul_sum_sub_tateProfileIntegral_le hk0 hk1 hA hK hH hK0 hK1 hd1 hdN)
        rw [integral_indicator measurableSet_Icc, setIntegral_const,
          Real.volume_real_Icc_of_le (by linarith), smul_eq_mul, sub_neg_eq_add, zero_add] at h2
        exact h1.trans h2
      have hmoeb : |(ArithmeticFunction.moebius d : ℝ)| / Real.sqrt d ≤ 1 / Real.sqrt d :=
        div_le_div_of_nonneg_right (abs_moebius_le_one d) (Real.sqrt_nonneg _)
      calc 2 * (|(ArithmeticFunction.moebius d : ℝ)| / Real.sqrt d) *
            |∫ u, H u * (∑ m ∈ Finset.Icc 1 (N / d),
              (m : ℝ) ^ (k - 1 / 2) * H (u + Real.log d + Real.log m) -
                tateProfileIntegral H k (u + Real.log d))|
          ≤ 2 * (1 / Real.sqrt d) * (A * ((3 + 2 / k) * K ^ 2 / Real.sqrt d)) :=
            mul_le_mul (mul_le_mul_of_nonneg_left hmoeb zero_le_two) hint_u
              (abs_nonneg _) (by positivity)
        _ = 2 * (3 + 2 / k) * K ^ 2 * A * (1 / (Real.sqrt d * Real.sqrt d)) := by ring
        _ = 2 * (3 + 2 / k) * K ^ 2 * A * (1 / (d : ℝ)) := by rw [Real.mul_self_sqrt hd_pos.le]
    calc ∑ d ∈ Finset.Icc 1 N, _
        ≤ ∑ d ∈ Finset.Icc 1 N, 2 * (3 + 2 / k) * K ^ 2 * A * (1 / (d : ℝ)) :=
          Finset.sum_le_sum hd_bound
      _ = 2 * (3 + 2 / k) * K ^ 2 * A * ∑ d ∈ Finset.Icc 1 N, 1 / (d : ℝ) :=
          (Finset.mul_sum _ _ _).symm
      _ ≤ 2 * (3 + 2 / k) * K ^ 2 * A * (A + 1) :=
          mul_le_mul_of_nonneg_left (sum_Icc_one_div_le_window hA) (by positivity)
      _ = 2 * (3 + 2 / k) * K ^ 2 * (A * (A + 1)) := by ring
  have hnorm_sq : |2 * ∫ u, H u ^ 2| ≤ 2 * K ^ 2 * A := by
    have hnn : 0 ≤ 2 * ∫ u, H u ^ 2 :=
      mul_nonneg zero_le_two (integral_nonneg fun _ => sq_nonneg _)
    rw [abs_of_nonneg hnn]
    have hind : Integrable (Set.indicator (Icc (-A) 0) fun _ : ℝ => K ^ 2) :=
      (integrableOn_const (hs := isCompact_Icc.measure_lt_top.ne)).integrable_indicator
        measurableSet_Icc
    have hle : (∫ u, H u ^ 2) ≤ ∫ u, Set.indicator (Icc (-A) 0) (fun _ : ℝ => K ^ 2) u := by
      refine integral_mono (integrable_sq hH.continuous hH.hasCompactSupport) hind fun u => ?_
      dsimp only
      by_cases hu : u ∈ Icc (-A) 0
      · rw [Set.indicator_of_mem hu, ← sq_abs (H u)]
        have h1 : |H u| ≤ K := by
          calc |H u| ≤ K * Real.exp (u / 2) := hK0 u
            _ ≤ K * 1 := mul_le_mul_of_nonneg_left (Real.exp_le_one_iff.mpr (by linarith [hu.2])) hK
            _ = K := mul_one _
        exact pow_le_pow_left₀ (abs_nonneg _) h1 2
      · rw [Set.indicator_of_notMem hu, hH.vanish u hu, sq, zero_mul]
    rw [integral_indicator measurableSet_Icc, setIntegral_const,
      Real.volume_real_Icc_of_le (by linarith), smul_eq_mul, sub_neg_eq_add, zero_add] at hle
    linarith
  have hshift_le : |shiftedPoleForm k H| ≤ 2 * K ^ 2 * A ^ 2 * Real.exp (k * A) := by
    unfold shiftedPoleForm
    rw [abs_mul, abs_mul, abs_of_pos (two_pos : (0 : ℝ) < 2)]
    have hind1 : Integrable (Set.indicator (Icc (-A) 0) fun _ : ℝ => K) :=
      (integrableOn_const (hs := isCompact_Icc.measure_lt_top.ne)).integrable_indicator
        measurableSet_Icc
    have hind2 : Integrable (Set.indicator (Icc (-A) 0) fun _ : ℝ => K * Real.exp (k * A)) :=
      (integrableOn_const (hs := isCompact_Icc.measure_lt_top.ne)).integrable_indicator
        measurableSet_Icc
    have hp : |∫ u, H u * Real.exp ((1 / 2 + k) * u)| ≤ K * A := by
      have h1 : |∫ u, H u * Real.exp ((1 / 2 + k) * u)| ≤
          ∫ u, |H u * Real.exp ((1 / 2 + k) * u)| := by
        simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (μ := volume)
          (fun u => H u * Real.exp ((1 / 2 + k) * u))
      have h2 : (∫ u, |H u * Real.exp ((1 / 2 + k) * u)|) ≤
          ∫ u, Set.indicator (Icc (-A) 0) (fun _ : ℝ => K) u := by
        refine integral_mono
          ((hH.continuous.mul (by fun_prop : Continuous fun u : ℝ =>
            Real.exp ((1 / 2 + k) * u))).integrable_of_hasCompactSupport
            hH.hasCompactSupport.mul_right).abs hind1 fun u => ?_
        dsimp only [Pi.mul_apply]
        by_cases hu : u ∈ Icc (-A) 0
        · rw [Set.indicator_of_mem hu, abs_mul, abs_of_pos (Real.exp_pos _)]
          calc |H u| * Real.exp ((1 / 2 + k) * u)
              ≤ K * Real.exp (u / 2) * Real.exp ((1 / 2 + k) * u) :=
                mul_le_mul_of_nonneg_right (hK0 u) (Real.exp_pos _).le
            _ = K * Real.exp ((1 + k) * u) := by
                rw [mul_assoc, ← Real.exp_add]; congr 1; congr 1; ring
            _ ≤ K * 1 := mul_le_mul_of_nonneg_left
                (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonneg_of_nonpos (by linarith) hu.2)) hK
            _ = K := mul_one _
        · rw [Set.indicator_of_notMem hu, hH.vanish u hu, zero_mul, abs_zero]
      rw [integral_indicator measurableSet_Icc, setIntegral_const,
        Real.volume_real_Icc_of_le (by linarith), smul_eq_mul, sub_neg_eq_add, zero_add] at h2
      linarith
    have hm : |∫ u, H u * Real.exp (-(1 / 2 + k) * u)| ≤ K * A * Real.exp (k * A) := by
      have h1 : |∫ u, H u * Real.exp (-(1 / 2 + k) * u)| ≤
          ∫ u, |H u * Real.exp (-(1 / 2 + k) * u)| := by
        simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (μ := volume)
          (fun u => H u * Real.exp (-(1 / 2 + k) * u))
      have h2 : (∫ u, |H u * Real.exp (-(1 / 2 + k) * u)|) ≤
          ∫ u, Set.indicator (Icc (-A) 0) (fun _ : ℝ => K * Real.exp (k * A)) u := by
        refine integral_mono
          ((hH.continuous.mul (by fun_prop : Continuous fun u : ℝ =>
            Real.exp (-(1 / 2 + k) * u))).integrable_of_hasCompactSupport
            hH.hasCompactSupport.mul_right).abs hind2 fun u => ?_
        dsimp only [Pi.mul_apply]
        by_cases hu : u ∈ Icc (-A) 0
        · rw [Set.indicator_of_mem hu, abs_mul, abs_of_pos (Real.exp_pos _)]
          calc |H u| * Real.exp (-(1 / 2 + k) * u)
              ≤ K * Real.exp (u / 2) * Real.exp (-(1 / 2 + k) * u) :=
                mul_le_mul_of_nonneg_right (hK0 u) (Real.exp_pos _).le
            _ = K * Real.exp (-k * u) := by
                rw [mul_assoc, ← Real.exp_add]; congr 1; congr 1; ring
            _ ≤ K * Real.exp (k * A) := mul_le_mul_of_nonneg_left
                (Real.exp_le_exp.mpr (by nlinarith [hu.1])) hK
        · rw [Set.indicator_of_notMem hu, hH.vanish u hu, zero_mul, abs_zero]
      rw [integral_indicator measurableSet_Icc, setIntegral_const,
        Real.volume_real_Icc_of_le (by linarith), smul_eq_mul, sub_neg_eq_add, zero_add] at h2
      linarith
    calc 2 * (|∫ u, H u * Real.exp ((1 / 2 + k) * u)| * |∫ u, H u * Real.exp (-(1 / 2 + k) * u)|)
        ≤ 2 * ((K * A) * (K * A * Real.exp (k * A))) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul hp hm (abs_nonneg _) (by positivity)) zero_le_two
      _ = 2 * K ^ 2 * A ^ 2 * Real.exp (k * A) := by ring
  have htail_moeb : |eulerProductPoleWeight k -
      ∑ d ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius d : ℝ) / (d : ℝ) ^ (1 + k)| ≤
      2 * (2 : ℝ) ^ k / k * Real.exp (-k * A) := by
    unfold eulerProductPoleWeight
    have hsum := summable_moebius_div_rpow hk0
    have hset : ∑ d ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius d : ℝ) / (d : ℝ) ^ (1 + k) =
        ∑ d ∈ Finset.range (N + 1), (ArithmeticFunction.moebius d : ℝ) / (d : ℝ) ^ (1 + k) := by
      have h0 : (ArithmeticFunction.moebius 0 : ℝ) / ((0 : ℕ) : ℝ) ^ (1 + k) = 0 := by
        rw [Nat.cast_zero, Real.zero_rpow (by linarith), div_zero]
      have hIco : Finset.Ico 0 (N + 1) = insert 0 (Finset.Icc 1 N) := by
        ext x; simp only [Finset.mem_Ico, Finset.mem_insert, Finset.mem_Icc]; omega
      rw [Finset.range_eq_Ico, hIco, Finset.sum_insert (by simp), h0, zero_add]
    rw [hset, ← hsum.sum_add_tsum_nat_add (N + 1), add_sub_cancel_left]
    have hshift_sum : Summable fun m : ℕ => 1 / ((m + (N + 1) : ℕ) : ℝ) ^ (1 + k) :=
      (summable_nat_add_iff (f := fun n : ℕ => 1 / (n : ℝ) ^ (1 + k)) (N + 1)).mpr
        (Real.summable_one_div_nat_rpow.mpr (by linarith))
    have hsum_shift : Summable fun m : ℕ =>
        ‖(ArithmeticFunction.moebius (m + (N + 1)) : ℝ) / ((m + (N + 1) : ℕ) : ℝ) ^ (1 + k)‖ :=
      ((summable_nat_add_iff (f := fun m : ℕ =>
        (ArithmeticFunction.moebius m : ℝ) / (m : ℝ) ^ (1 + k)) (N + 1)).mpr hsum).norm
    have hnorm_tsum : |∑' m : ℕ, (ArithmeticFunction.moebius (m + (N + 1)) : ℝ) /
          ((m + (N + 1) : ℕ) : ℝ) ^ (1 + k)| ≤
        ∑' m : ℕ, 1 / ((m + (N + 1) : ℕ) : ℝ) ^ (1 + k) := by
      have h1 := norm_tsum_le_tsum_norm hsum_shift
      rw [Real.norm_eq_abs] at h1
      refine h1.trans (Summable.tsum_le_tsum (fun m => ?_) hsum_shift hshift_sum)
      rw [Real.norm_eq_abs, abs_div, abs_of_pos (Real.rpow_pos_of_pos (by positivity) _)]
      exact div_le_div_of_nonneg_right (abs_moebius_le_one _) (by positivity)
    have htsum_int : ∑' m : ℕ, 1 / ((m + (N + 1) : ℕ) : ℝ) ^ (1 + k) ≤ 1 / (k * (N : ℝ) ^ k) := by
      refine Real.tsum_le_of_sum_range_le (fun m => by positivity) fun M => ?_
      have hstep : ∀ m : ℕ, 1 / ((m + (N + 1) : ℕ) : ℝ) ^ (1 + k) ≤
          1 / k * (1 / ((m + N : ℕ) : ℝ) ^ k - 1 / ((m + (N + 1) : ℕ) : ℝ) ^ k) := by
        intro m
        have ha_pos : (0 : ℝ) < ((m + N : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < m + N)
        have hb_eq : ((m + (N + 1) : ℕ) : ℝ) = ((m + N : ℕ) : ℝ) + 1 := by push_cast; ring
        have hmono : 1 / ((m + (N + 1) : ℕ) : ℝ) ^ (1 + k) ≤
            ∫ x : ℝ in ((m + N : ℕ) : ℝ)..(((m + N : ℕ) : ℝ) + 1), x ^ (-(1 + k)) := by
          have hconst : 1 / ((m + (N + 1) : ℕ) : ℝ) ^ (1 + k) =
              ∫ _ : ℝ in ((m + N : ℕ) : ℝ)..(((m + N : ℕ) : ℝ) + 1),
                1 / ((m + (N + 1) : ℕ) : ℝ) ^ (1 + k) := by
            rw [intervalIntegral.integral_const, smul_eq_mul]; ring
          rw [hconst, intervalIntegral.integral_of_le (by linarith),
            intervalIntegral.integral_of_le (by linarith)]
          have hi : IntervalIntegrable (fun x : ℝ => x ^ (-(1 + k))) volume
              ((m + N : ℕ) : ℝ) (((m + N : ℕ) : ℝ) + 1) :=
            intervalIntegral.intervalIntegrable_rpow
              (Or.inr <| notMem_uIcc_of_lt ha_pos (by positivity))
          refine setIntegral_mono_on
            (integrableOn_const (hs := ((measure_mono Ioc_subset_Icc_self).trans_lt
              isCompact_Icc.measure_lt_top).ne))
            hi.1 measurableSet_Ioc fun x hx => ?_
          have hx_pos : 0 < x := ha_pos.trans hx.1
          rw [Real.rpow_neg hx_pos.le, ← one_div, hb_eq]
          exact one_div_le_one_div_of_le (Real.rpow_pos_of_pos hx_pos _)
            (Real.rpow_le_rpow hx_pos.le hx.2 (by linarith))
        have h0 : (0 : ℝ) ∉ uIcc ((m + N : ℕ) : ℝ) (((m + N : ℕ) : ℝ) + 1) :=
          notMem_uIcc_of_lt ha_pos (by positivity)
        rw [integral_rpow (Or.inr ⟨by linarith, h0⟩), show -(1 + k) + 1 = -k by ring,
          div_neg, ← neg_div, neg_sub, Real.rpow_neg ha_pos.le,
          Real.rpow_neg (by positivity)] at hmono
        simp only [← one_div, ← hb_eq] at hmono
        exact hmono.trans_eq (by ring)
      have htel : ∀ M : ℕ, ∑ m ∈ Finset.range M,
          (1 / ((m + N : ℕ) : ℝ) ^ k - 1 / ((m + (N + 1) : ℕ) : ℝ) ^ k) =
          1 / (N : ℝ) ^ k - 1 / ((M + N : ℕ) : ℝ) ^ k := by
        intro M
        induction M with
        | zero => simp
        | succ M ih =>
          rw [Finset.sum_range_succ, ih]
          have : M + (N + 1) = M + 1 + N := by omega
          rw [this]; ring
      calc ∑ m ∈ Finset.range M, 1 / ((m + (N + 1) : ℕ) : ℝ) ^ (1 + k)
          ≤ ∑ m ∈ Finset.range M,
              1 / k * (1 / ((m + N : ℕ) : ℝ) ^ k - 1 / ((m + (N + 1) : ℕ) : ℝ) ^ k) :=
            Finset.sum_le_sum fun m _ => hstep m
        _ = 1 / k * (1 / (N : ℝ) ^ k - 1 / ((M + N : ℕ) : ℝ) ^ k) := by
            rw [← Finset.mul_sum, htel M]
        _ ≤ 1 / k * (1 / (N : ℝ) ^ k) :=
            mul_le_mul_of_nonneg_left (sub_le_self _ (by positivity)) (by positivity)
        _ = 1 / (k * (N : ℝ) ^ k) := by ring
    have hNk : 1 / (N : ℝ) ^ k ≤ (2 : ℝ) ^ k * Real.exp (-k * A) := by
      have hN_gt : Real.exp A / 2 < (N : ℝ) := by
        have hlt : Real.exp A < (N : ℝ) + 1 := Nat.lt_floor_add_one (Real.exp A)
        have h1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
        linarith
      calc 1 / (N : ℝ) ^ k ≤ 1 / (Real.exp A / 2) ^ k :=
            one_div_le_one_div_of_le (Real.rpow_pos_of_pos (by positivity) _)
              (Real.rpow_le_rpow (by positivity) hN_gt.le hk0.le)
        _ = (2 : ℝ) ^ k * Real.exp (-k * A) := by
            rw [Real.div_rpow (Real.exp_pos A).le zero_le_two, one_div_div,
              Real.rpow_def_of_pos (Real.exp_pos A), Real.log_exp, div_eq_mul_inv,
              ← Real.exp_neg]
            exact congrArg (fun x => (2 : ℝ) ^ k * Real.exp x) (by ring)
    calc |∑' m : ℕ, (ArithmeticFunction.moebius (m + (N + 1)) : ℝ) /
            ((m + (N + 1) : ℕ) : ℝ) ^ (1 + k)|
        ≤ 1 / (k * (N : ℝ) ^ k) := hnorm_tsum.trans htsum_int
      _ = (1 / k) * (1 / (N : ℝ) ^ k) := by ring
      _ ≤ (1 / k) * ((2 : ℝ) ^ k * Real.exp (-k * A)) :=
          mul_le_mul_of_nonneg_left hNk (by positivity)
      _ ≤ 2 * (2 : ℝ) ^ k / k * Real.exp (-k * A) := by
          have hnn : 0 ≤ (2 : ℝ) ^ k / k * Real.exp (-k * A) := by positivity
          have heq : 2 * (2 : ℝ) ^ k / k * Real.exp (-k * A) -
              (1 / k) * ((2 : ℝ) ^ k * Real.exp (-k * A)) =
              (2 : ℝ) ^ k / k * Real.exp (-k * A) := by ring
          linarith only [hnn, heq]
  have htail_prod : |(eulerProductPoleWeight k -
      ∑ d ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius d : ℝ) / (d : ℝ) ^ (1 + k)) *
        shiftedPoleForm k H| ≤ 4 * (2 : ℝ) ^ k / k * K ^ 2 * A ^ 2 := by
    rw [abs_mul]
    calc |eulerProductPoleWeight k -
          ∑ d ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius d : ℝ) / (d : ℝ) ^ (1 + k)| *
          |shiftedPoleForm k H|
        ≤ (2 * (2 : ℝ) ^ k / k * Real.exp (-k * A)) *
            (2 * K ^ 2 * A ^ 2 * Real.exp (k * A)) :=
          mul_le_mul htail_moeb hshift_le (abs_nonneg _) (by positivity)
      _ = 4 * (2 : ℝ) ^ k / k * K ^ 2 * A ^ 2 * (Real.exp (-k * A) * Real.exp (k * A)) := by ring
      _ = 4 * (2 : ℝ) ^ k / k * K ^ 2 * A ^ 2 := by
          rw [← Real.exp_add, show -k * A + k * A = 0 by ring, Real.exp_zero, mul_one]
  have hsplit_tot : tatePointCount A H k - eulerProductPoleWeight k * shiftedPoleForm k H =
      (tatePointCount A H k -
        (∑ d ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius d : ℝ) / (d : ℝ) ^ (1 + k)) *
          shiftedPoleForm k H) -
      (eulerProductPoleWeight k -
        ∑ d ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius d : ℝ) / (d : ℝ) ^ (1 + k)) *
        shiftedPoleForm k H := by ring
  rw [hsplit_tot, hmain_id]
  have htri1 := abs_sub_le
    ((2 * tateFunction A H k -
        ∑ d ∈ Finset.Icc 1 N, 2 * (((ArithmeticFunction.moebius d : ℝ) / Real.sqrt d) *
          ∫ u, H u * tateProfileIntegral H k (u + Real.log d))) -
      2 * ∫ u, H u ^ 2) 0
    ((eulerProductPoleWeight k -
        ∑ d ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius d : ℝ) / (d : ℝ) ^ (1 + k)) *
      shiftedPoleForm k H)
  rw [sub_zero, zero_sub, abs_neg] at htri1
  have htri2 := abs_sub_le
    (2 * tateFunction A H k -
      ∑ d ∈ Finset.Icc 1 N, 2 * (((ArithmeticFunction.moebius d : ℝ) / Real.sqrt d) *
        ∫ u, H u * tateProfileIntegral H k (u + Real.log d))) 0
    (2 * ∫ u, H u ^ 2)
  rw [sub_zero, zero_sub, abs_neg] at htri2
  have hpoly1 : A * (A + 1) ≤ (A + 1) ^ 2 := by nlinarith
  have hpoly2 : A ≤ (A + 1) ^ 2 := by nlinarith
  have hpoly3 : A ^ 2 ≤ (A + 1) ^ 2 := by nlinarith
  calc _ ≤ 2 * (3 + 2 / k) * K ^ 2 * (A * (A + 1)) + 2 * K ^ 2 * A +
          4 * (2 : ℝ) ^ k / k * K ^ 2 * A ^ 2 := by linarith
    _ ≤ 2 * (3 + 2 / k) * K ^ 2 * (A + 1) ^ 2 + 2 * K ^ 2 * (A + 1) ^ 2 +
          4 * (2 : ℝ) ^ k / k * K ^ 2 * (A + 1) ^ 2 := by
        refine add_le_add (add_le_add ?_ ?_) ?_
        · exact mul_le_mul_of_nonneg_left hpoly1 (by positivity)
        · exact mul_le_mul_of_nonneg_left hpoly2 (by positivity)
        · exact mul_le_mul_of_nonneg_left hpoly3 (by positivity)
    _ = C_k * K ^ 2 * (A + 1) ^ 2 := by dsimp only [C_k]; ring


/-! ### Two-sided shifted-pole residue pinching -/

private theorem abs_windowPoleForm_le_of_exp_bound {A K : ℝ} (hA : 0 ≤ A) (hK : 0 ≤ K)
    {H : ℝ → ℝ} (hH : IsWindowTest A H) (hK0 : ∀ w, |H w| ≤ K * Real.exp (w / 2)) :
    |windowPoleForm H| ≤ 2 * K ^ 2 * A ^ 2 := by
  rw [windowPoleForm_eq_exp_prod hH, abs_mul, abs_mul, abs_of_pos (two_pos : (0 : ℝ) < 2)]
  have hind : Integrable (Set.indicator (Icc (-A) 0) fun _ : ℝ => K) :=
    (integrableOn_const (hs := isCompact_Icc.measure_lt_top.ne)).integrable_indicator
      measurableSet_Icc
  have hp : |∫ u, H u * Real.exp (u / 2)| ≤ K * A := by
    have h1 : |∫ u, H u * Real.exp (u / 2)| ≤ ∫ u, |H u * Real.exp (u / 2)| := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (μ := volume)
        (fun u => H u * Real.exp (u / 2))
    have h2 : (∫ u, |H u * Real.exp (u / 2)|) ≤
        ∫ u, Set.indicator (Icc (-A) 0) (fun _ : ℝ => K) u := by
      refine integral_mono
        ((hH.continuous.mul (by fun_prop : Continuous fun u : ℝ =>
          Real.exp (u / 2))).integrable_of_hasCompactSupport
          hH.hasCompactSupport.mul_right).abs hind fun u => ?_
      dsimp only [Pi.mul_apply]
      by_cases hu : u ∈ Icc (-A) 0
      · rw [Set.indicator_of_mem hu, abs_mul, abs_of_pos (Real.exp_pos _)]
        calc |H u| * Real.exp (u / 2)
            ≤ K * Real.exp (u / 2) * Real.exp (u / 2) :=
              mul_le_mul_of_nonneg_right (hK0 u) (Real.exp_pos _).le
          _ = K * Real.exp u := by rw [mul_assoc, ← Real.exp_add]; congr 1; congr 1; ring
          _ ≤ K * 1 := mul_le_mul_of_nonneg_left (Real.exp_le_one_iff.mpr hu.2) hK
          _ = K := mul_one _
      · rw [Set.indicator_of_notMem hu, hH.vanish u hu, zero_mul, abs_zero]
    rw [integral_indicator measurableSet_Icc, setIntegral_const,
      Real.volume_real_Icc_of_le (by linarith), smul_eq_mul, sub_neg_eq_add, zero_add] at h2
    linarith
  have hm : |∫ u, H u * Real.exp (-u / 2)| ≤ K * A := by
    have h1 : |∫ u, H u * Real.exp (-u / 2)| ≤ ∫ u, |H u * Real.exp (-u / 2)| := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (μ := volume)
        (fun u => H u * Real.exp (-u / 2))
    have h2 : (∫ u, |H u * Real.exp (-u / 2)|) ≤
        ∫ u, Set.indicator (Icc (-A) 0) (fun _ : ℝ => K) u := by
      refine integral_mono
        ((hH.continuous.mul (by fun_prop : Continuous fun u : ℝ =>
          Real.exp (-u / 2))).integrable_of_hasCompactSupport
          hH.hasCompactSupport.mul_right).abs hind fun u => ?_
      dsimp only [Pi.mul_apply]
      by_cases hu : u ∈ Icc (-A) 0
      · rw [Set.indicator_of_mem hu, abs_mul, abs_of_pos (Real.exp_pos _)]
        calc |H u| * Real.exp (-u / 2)
            ≤ K * Real.exp (u / 2) * Real.exp (-u / 2) :=
              mul_le_mul_of_nonneg_right (hK0 u) (Real.exp_pos _).le
          _ = K * 1 := by
              rw [mul_assoc, ← Real.exp_add, show u / 2 + -u / 2 = 0 by ring, Real.exp_zero]
          _ = K := mul_one _
      · rw [Set.indicator_of_notMem hu, hH.vanish u hu, zero_mul, abs_zero]
    rw [integral_indicator measurableSet_Icc, setIntegral_const,
      Real.volume_real_Icc_of_le (by linarith), smul_eq_mul, sub_neg_eq_add, zero_add] at h2
    linarith
  calc 2 * (|∫ u, H u * Real.exp (u / 2)| * |∫ u, H u * Real.exp (-u / 2)|)
      ≤ 2 * ((K * A) * (K * A)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul hp hm (abs_nonneg _) (by positivity)) zero_le_two
    _ = 2 * K ^ 2 * A ^ 2 := by ring

private theorem abs_archGammaForm_le_of_deriv_exp_bound {A K E_H : ℝ}
    (_ : 0 ≤ A) (hK : 0 ≤ K) (hE : 0 ≤ E_H) {H : ℝ → ℝ} (hH : IsWindowTest A H)
    (hsq : ∫ u, H u ^ 2 ≤ E_H) (hder : ∀ w, |deriv H w| ≤ K * Real.exp (w / 2)) :
    |archGammaForm H| ≤ |Zeta23.EF.gammaBracket 0| * E_H +
      ∫ x in Ioi (0 : ℝ),
        (3 / 2 * K ^ 2 * Real.exp 1 * (∫ u, Real.exp (-|u|)) + 6 * E_H) *
          Real.exp (-(1 / 2 * x)) := by
  set E₀ := ∫ u, Real.exp (-|u|)
  have hE₀ : 0 ≤ E₀ := integral_nonneg fun _ => (Real.exp_pos _).le
  set M₀ := 3 / 2 * K ^ 2 * Real.exp 1 * E₀ + 6 * E_H
  have hM₀ : 0 ≤ M₀ := by positivity
  have hint_half : IntegrableOn (fun x : ℝ => Real.exp (-(1 / 2 * x))) (Ioi 0) := by
    have hG : IntegrableOn (fun y : ℝ => Real.exp (-y) * y ^ ((1 : ℝ) - 1)) (Ioi 0) :=
      Real.GammaIntegral_convergent zero_lt_one
    have hG1 : IntegrableOn (fun y : ℝ => Real.exp (-y)) (Ioi 0) :=
      IntegrableOn.congr_fun hG (fun y _ => by
        show Real.exp (-y) * y ^ ((1 : ℝ) - 1) = Real.exp (-y)
        rw [sub_self, Real.rpow_zero, mul_one]) measurableSet_Ioi
    exact (integrableOn_Ioi_comp_mul_left_iff (fun y : ℝ => Real.exp (-y)) 0
      (by norm_num : (0 : ℝ) < 1 / 2)).mpr (by simpa using hG1)
  have hdom : IntegrableOn (fun x : ℝ => M₀ * Real.exp (-(1 / 2 * x))) (Ioi 0) :=
    hint_half.const_mul M₀
  have hω_le : ∀ {x : ℝ}, 0 < x →
      archLevyDensity x ≤ Real.exp (-(1 / 2 * x)) * (1 + 2 * x) / (2 * x) := by
    intro x hx
    unfold archLevyDensity
    have hden : 2 * x / (1 + 2 * x) ≤ 1 - Real.exp (-2 * x) := by
      have h1 : 1 + 2 * x ≤ Real.exp (2 * x) := by linarith [Real.add_one_le_exp (2 * x)]
      have h2 : Real.exp (-2 * x) ≤ 1 / (1 + 2 * x) := by
        rw [show -2 * x = -(2 * x) by ring, Real.exp_neg, inv_eq_one_div]
        exact one_div_le_one_div_of_le (by positivity) h1
      have h3 : 2 * x / (1 + 2 * x) = 1 - 1 / (1 + 2 * x) := by field_simp; ring
      linarith
    refine (div_le_div_of_nonneg_left (Real.exp_pos (-x / 2)).le (by positivity) hden).trans_eq ?_
    rw [show -x / 2 = -(1 / 2 * x) by ring]; field_simp
  have hpt : ∀ x ∈ Ioi (0 : ℝ),
      archLevyDensity x * (∫ u, (H u - H (u + x)) ^ 2) ≤ M₀ * Real.exp (-(1 / 2 * x)) := by
    intro x hx
    have hx0 : 0 < x := hx
    have hω := hω_le hx0
    have hnn_int : 0 ≤ ∫ u, (H u - H (u + x)) ^ 2 := integral_nonneg fun _ => sq_nonneg _
    rcases le_or_gt x 1 with hx1 | hx1
    · have hsmall : ∫ u, (H u - H (u + x)) ^ 2 ≤ K ^ 2 * Real.exp 1 * E₀ * x ^ 2 := by
        have hint := integrable_sub_shift_sq hH.continuous hH.hasCompactSupport x
        have hdom_u := _root_.RHTower.integrable_exp_neg_abs.const_mul (K ^ 2 * Real.exp 1 * x ^ 2)
        have hm := integral_mono hint hdom_u fun u => ?_
        · rw [integral_const_mul] at hm; linarith
        · dsimp only
          rcases lt_or_ge 0 u with hu | hu
          · rw [hH.vanish u (fun hm => by linarith [hm.2]),
              hH.vanish (u + x) (fun hm => by linarith [hm.2]), sub_self, sq, zero_mul]
            exact mul_nonneg (by positivity) (Real.exp_pos _).le
          · have hmvt : |H (u + x) - H u| ≤ K * Real.exp ((u + 1) / 2) * x := by
              have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
                (f := H) (f' := deriv H) (s := Icc u (u + x)) (C := K * Real.exp ((u + 1) / 2))
                (fun t _ => ((hH.contDiff.differentiable (by norm_num)).differentiableAt.hasDerivAt).hasDerivWithinAt)
                (fun t ht => by
                  rw [Real.norm_eq_abs]
                  exact (hder t).trans
                    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith [ht.2])) hK))
                (convex_Icc u (u + x)) (left_mem_Icc.mpr (by linarith))
                (right_mem_Icc.mpr (by linarith))
              simpa only [Real.norm_eq_abs, add_sub_cancel_left, abs_of_pos hx0] using h
            rw [abs_sub_comm] at hmvt
            have hsq_u : (H u - H (u + x)) ^ 2 ≤ (K * Real.exp ((u + 1) / 2) * x) ^ 2 := by
              rw [← sq_abs (H u - H (u + x))]
              exact pow_le_pow_left₀ (abs_nonneg _) hmvt 2
            have hexp : (K * Real.exp ((u + 1) / 2) * x) ^ 2 =
                K ^ 2 * Real.exp 1 * x ^ 2 * Real.exp (-|u|) := by
              have he : Real.exp ((u + 1) / 2) ^ 2 = Real.exp 1 * Real.exp (-|u|) := by
                rw [sq, ← Real.exp_add, ← Real.exp_add, abs_of_nonpos hu]; congr 1; ring
              calc (K * Real.exp ((u + 1) / 2) * x) ^ 2
                  = K ^ 2 * Real.exp ((u + 1) / 2) ^ 2 * x ^ 2 := by ring
                _ = K ^ 2 * (Real.exp 1 * Real.exp (-|u|)) * x ^ 2 := by rw [he]
                _ = K ^ 2 * Real.exp 1 * x ^ 2 * Real.exp (-|u|) := by ring
            rwa [hexp] at hsq_u
      have hω1 : archLevyDensity x ≤ 3 / (2 * x) * Real.exp (-(1 / 2 * x)) := by
        refine hω.trans ?_
        have : 1 + 2 * x ≤ 3 := by linarith
        calc Real.exp (-(1 / 2 * x)) * (1 + 2 * x) / (2 * x)
            ≤ Real.exp (-(1 / 2 * x)) * 3 / (2 * x) :=
              div_le_div_of_nonneg_right
                (mul_le_mul_of_nonneg_left this (Real.exp_pos _).le) (by positivity)
          _ = 3 / (2 * x) * Real.exp (-(1 / 2 * x)) := by ring
      set C_s := K ^ 2 * Real.exp 1 * E₀
      calc archLevyDensity x * ∫ u, (H u - H (u + x)) ^ 2
          ≤ (3 / (2 * x) * Real.exp (-(1 / 2 * x))) * (C_s * x ^ 2) :=
            mul_le_mul hω1 hsmall hnn_int (by positivity)
        _ = 3 / 2 * C_s * x * Real.exp (-(1 / 2 * x)) := by field_simp
        _ ≤ 3 / 2 * C_s * 1 * Real.exp (-(1 / 2 * x)) :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hx1 (by positivity)) (Real.exp_pos _).le
        _ ≤ M₀ * Real.exp (-(1 / 2 * x)) :=
            mul_le_mul_of_nonneg_right (by dsimp only [M₀, C_s]; linarith) (Real.exp_pos _).le
    · have hlarge : ∫ u, (H u - H (u + x)) ^ 2 ≤ 4 * E_H := by
        have i1 := integrable_sq hH.continuous hH.hasCompactSupport
        have i2 : Integrable fun u => H (u + x) ^ 2 := i1.comp_add_right x
        have isub := integrable_sub_shift_sq hH.continuous hH.hasCompactSupport x
        have isum : Integrable fun u => 2 * H u ^ 2 + 2 * H (u + x) ^ 2 :=
          (i1.const_mul 2).add (i2.const_mul 2)
        have hm := integral_mono isub isum fun u => by
          dsimp only; nlinarith only [sq_nonneg (H u + H (u + x))]
        rw [integral_add (i1.const_mul 2) (i2.const_mul 2), integral_const_mul, integral_const_mul,
          integral_add_right_eq_self (μ := volume) (fun u => H u ^ 2) x] at hm
        linarith
      have hω2 : archLevyDensity x ≤ 3 / 2 * Real.exp (-(1 / 2 * x)) := by
        refine hω.trans ?_
        have : 1 + 2 * x ≤ 3 * x := by linarith
        calc Real.exp (-(1 / 2 * x)) * (1 + 2 * x) / (2 * x)
            ≤ Real.exp (-(1 / 2 * x)) * (3 * x) / (2 * x) :=
              div_le_div_of_nonneg_right
                (mul_le_mul_of_nonneg_left this (Real.exp_pos _).le) (by positivity)
          _ = 3 / 2 * Real.exp (-(1 / 2 * x)) := by field_simp
      calc archLevyDensity x * ∫ u, (H u - H (u + x)) ^ 2
          ≤ (3 / 2 * Real.exp (-(1 / 2 * x))) * (4 * E_H) :=
            mul_le_mul hω2 hlarge hnn_int (by positivity)
        _ = 6 * E_H * Real.exp (-(1 / 2 * x)) := by ring
        _ ≤ M₀ * Real.exp (-(1 / 2 * x)) := by
            refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
            dsimp only [M₀]; linarith [show 0 ≤ 3 / 2 * K ^ 2 * Real.exp 1 * E₀ by positivity]
  have hJ_le : levyJump H ≤ ∫ x in Ioi (0 : ℝ), M₀ * Real.exp (-(1 / 2 * x)) := by
    have hl_le : (∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal
        (archLevyDensity x * ∫ u, (H u - H (u + x)) ^ 2)) ≤
        ∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal (M₀ * Real.exp (-(1 / 2 * x))) :=
      setLIntegral_mono' measurableSet_Ioi fun x hx => ENNReal.ofReal_le_ofReal (hpt x hx)
    have hl_eq : (∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal (M₀ * Real.exp (-(1 / 2 * x)))) =
        ENNReal.ofReal (∫ x in Ioi (0 : ℝ), M₀ * Real.exp (-(1 / 2 * x))) :=
      (ofReal_integral_eq_lintegral_ofReal hdom
        (ae_of_all _ fun _ => mul_nonneg hM₀ (Real.exp_pos _).le)).symm
    have htr := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hl_le.trans_eq hl_eq)
    rw [ENNReal.toReal_ofReal (setIntegral_nonneg measurableSet_Ioi fun _ _ =>
      mul_nonneg hM₀ (Real.exp_pos _).le)] at htr
    exact htr
  unfold archGammaForm
  have hsq0 : 0 ≤ ∫ u, H u ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have hJ0 : 0 ≤ levyJump H := ENNReal.toReal_nonneg
  have h1 : |Zeta23.EF.gammaBracket 0 * ∫ u, H u ^ 2| ≤ |Zeta23.EF.gammaBracket 0| * E_H := by
    rw [abs_mul, abs_of_nonneg hsq0]
    exact mul_le_mul_of_nonneg_left hsq (abs_nonneg _)
  have h2 : |levyJump H| ≤ ∫ x in Ioi (0 : ℝ), M₀ * Real.exp (-(1 / 2 * x)) := by
    rwa [abs_of_nonneg hJ0]
  linarith [abs_add_le (Zeta23.EF.gammaBracket 0 * ∫ u, H u ^ 2) (levyJump H)]

private theorem integral_harmonicPlateauTest_exp_pos_ge {B k : ℝ} (hB : 4 ≤ B) (hk : 0 ≤ k) :
    2 * Real.exp (-3 * (1 + k)) ≤
      ∫ u, harmonicPlateauTest B u * Real.exp ((1 / 2 + k) * u) := by
  have hB0 : 0 ≤ B := by linarith
  have hH := isWindowTest_harmonicPlateauTest hB0
  have hint : Integrable fun u => harmonicPlateauTest B u * Real.exp ((1 / 2 + k) * u) :=
    (hH.continuous.mul (by fun_prop : Continuous fun u : ℝ =>
      Real.exp ((1 / 2 + k) * u))).integrable_of_hasCompactSupport hH.hasCompactSupport.mul_right
  have hsub : ∫ u in Ioc (-3 : ℝ) (-1), harmonicPlateauTest B u * Real.exp ((1 / 2 + k) * u) ≤
      ∫ u, harmonicPlateauTest B u * Real.exp ((1 / 2 + k) * u) :=
    setIntegral_le_integral hint (Eventually.of_forall fun u =>
      mul_nonneg (harmonicPlateauTest_nonneg B u) (Real.exp_pos _).le)
  have hlow : (∫ _ in Ioc (-3 : ℝ) (-1), Real.exp (-3 * (1 + k))) ≤
      ∫ u in Ioc (-3 : ℝ) (-1), harmonicPlateauTest B u * Real.exp ((1 / 2 + k) * u) := by
    refine setIntegral_mono_on
      (integrableOn_const (hs := ((measure_mono Ioc_subset_Icc_self).trans_lt
        isCompact_Icc.measure_lt_top).ne))
      hint.integrableOn measurableSet_Ioc fun u hu => ?_
    rw [harmonicPlateauTest_eq_exp_of_mem ⟨by linarith [hu.1], hu.2⟩, ← Real.exp_add]
    exact Real.exp_le_exp.mpr (by nlinarith [hu.1])
  rw [setIntegral_const, Real.volume_real_Ioc_of_le (by norm_num), smul_eq_mul] at hlow
  linarith

private theorem integral_harmonicPlateauTest_exp_neg_ge {B k : ℝ} (hB : 6 ≤ B) (hk : 0 ≤ k) :
    Real.exp (k * (B - 2)) ≤
      ∫ u, harmonicPlateauTest B u * Real.exp (-(1 / 2 + k) * u) := by
  have hB0 : 0 ≤ B := by linarith
  have hH := isWindowTest_harmonicPlateauTest hB0
  have hint : Integrable fun u => harmonicPlateauTest B u * Real.exp (-(1 / 2 + k) * u) :=
    (hH.continuous.mul (by fun_prop : Continuous fun u : ℝ =>
      Real.exp (-(1 / 2 + k) * u))).integrable_of_hasCompactSupport hH.hasCompactSupport.mul_right
  have hsub : ∫ u in Ioc (-B + 1) (-B + 2),
      harmonicPlateauTest B u * Real.exp (-(1 / 2 + k) * u) ≤
      ∫ u, harmonicPlateauTest B u * Real.exp (-(1 / 2 + k) * u) :=
    setIntegral_le_integral hint (Eventually.of_forall fun u =>
      mul_nonneg (harmonicPlateauTest_nonneg B u) (Real.exp_pos _).le)
  have hlow : (∫ _ in Ioc (-B + 1) (-B + 2), Real.exp (k * (B - 2))) ≤
      ∫ u in Ioc (-B + 1) (-B + 2), harmonicPlateauTest B u * Real.exp (-(1 / 2 + k) * u) := by
    refine setIntegral_mono_on
      (integrableOn_const (hs := ((measure_mono Ioc_subset_Icc_self).trans_lt
        isCompact_Icc.measure_lt_top).ne))
      hint.integrableOn measurableSet_Ioc fun u hu => ?_
    rw [harmonicPlateauTest_eq_exp_of_mem ⟨hu.1.le, by linarith [hu.2]⟩, ← Real.exp_add]
    exact Real.exp_le_exp.mpr (by nlinarith [hu.2])
  rw [setIntegral_const, Real.volume_real_Ioc_of_le (by linarith), smul_eq_mul] at hlow
  have hlen : (-B + 2) - (-B + 1) = 1 := by ring
  rw [hlen, one_mul] at hlow
  exact hlow.trans hsub

theorem shiftedPoleForm_harmonicPlateauTest_ge {B k : ℝ} (hB : 6 ≤ B) (hk : 0 ≤ k) :
    4 * Real.exp (-3 * (1 + k)) * Real.exp (k * (B - 2)) ≤
      shiftedPoleForm k (harmonicPlateauTest B) := by
  unfold shiftedPoleForm
  have hp := integral_harmonicPlateauTest_exp_pos_ge (by linarith : 4 ≤ B) hk
  have hm := integral_harmonicPlateauTest_exp_neg_ge hB hk
  have hprod := mul_le_mul hp hm (Real.exp_pos _).le
    (le_trans (by positivity) hp)
  linarith

/-- Signed two-bump plateau `harmonicPlateauTest B (u + 4) − M · harmonicPlateauTest 4 u` on
`[−(B + 4), 0]`, giving `shiftedPoleForm k` a strictly negative exponentially growing value. -/
def signedPlateauTest (M B u : ℝ) : ℝ :=
  harmonicPlateauTest B (u + 4) - M * harmonicPlateauTest 4 u

theorem isWindowTest_signedPlateauTest {B : ℝ} (hB : 0 ≤ B) (M : ℝ) :
    IsWindowTest (B + 4) (signedPlateauTest M B) := by
  have h1 := isWindowTest_harmonicPlateauTest hB
  have h2 := isWindowTest_harmonicPlateauTest (by norm_num : (0 : ℝ) ≤ 4)
  refine ⟨(h1.contDiff.comp (contDiff_id.add contDiff_const)).sub
    (contDiff_const.mul h2.contDiff), fun u hu => ?_⟩
  simp only [mem_Icc, not_and_or, not_le] at hu
  unfold signedPlateauTest
  rcases hu with hlt | hgt
  · rw [h1.vanish (u + 4) (fun hm => by linarith [hm.1]),
      h2.vanish u (fun hm => by linarith [hm.1]), mul_zero, sub_self]
  · rw [h1.vanish (u + 4) (fun hm => by linarith [hm.2]),
      h2.vanish u (fun hm => by linarith [hm.2]), mul_zero, sub_self]

private theorem abs_signedPlateauTest_le (M B w : ℝ) :
    |signedPlateauTest M B w| ≤ (Real.exp 2 + |M|) * Real.exp (w / 2) := by
  unfold signedPlateauTest
  have h1 : |harmonicPlateauTest B (w + 4)| ≤ Real.exp 2 * Real.exp (w / 2) := by
    rw [abs_of_nonneg (harmonicPlateauTest_nonneg B _)]
    refine (harmonicPlateauTest_le_exp B (w + 4)).trans_eq ?_
    rw [show (w + 4) / 2 = 2 + w / 2 by ring, Real.exp_add]
  have h2 : |M * harmonicPlateauTest 4 w| ≤ |M| * Real.exp (w / 2) := by
    rw [abs_mul, abs_of_nonneg (harmonicPlateauTest_nonneg 4 w)]
    exact mul_le_mul_of_nonneg_left (harmonicPlateauTest_le_exp 4 w) (abs_nonneg M)
  have htri := abs_sub (harmonicPlateauTest B (w + 4)) (M * harmonicPlateauTest 4 w)
  linarith

private theorem abs_deriv_signedPlateauTest_le {Λ : ℝ}
    (hΛ : ∀ x : ℝ, |deriv Real.smoothTransition x| ≤ Λ) (M B w : ℝ) :
    |deriv (signedPlateauTest M B) w| ≤
      (Real.exp 2 + |M|) * (1 / 2 + 2 * Λ) * Real.exp (w / 2) := by
  have hd1 : HasDerivAt (fun u => harmonicPlateauTest B (u + 4))
      (harmonicPlateauDeriv B (w + 4)) w :=
    (hasDerivAt_harmonicPlateauTest B (w + 4)).comp_add_const w 4
  have hd2 : HasDerivAt (fun u => M * harmonicPlateauTest 4 u)
      (M * harmonicPlateauDeriv 4 w) w :=
    (hasDerivAt_harmonicPlateauTest 4 w).const_mul M
  have hd : deriv (signedPlateauTest M B) w =
      deriv (harmonicPlateauTest B) (w + 4) - M * deriv (harmonicPlateauTest 4) w := by
    have hsub : HasDerivAt (signedPlateauTest M B)
        (harmonicPlateauDeriv B (w + 4) - M * harmonicPlateauDeriv 4 w) w := hd1.sub hd2
    rw [hsub.deriv, deriv_harmonicPlateauTest, deriv_harmonicPlateauTest]
  rw [hd]
  have hb1 : |deriv (harmonicPlateauTest B) (w + 4)| ≤
      Real.exp 2 * (1 / 2 + 2 * Λ) * Real.exp (w / 2) := by
    refine (abs_deriv_harmonicPlateauTest_le hΛ B (w + 4)).trans_eq ?_
    rw [show (w + 4) / 2 = 2 + w / 2 by ring, Real.exp_add]; ring
  have hb2 : |M * deriv (harmonicPlateauTest 4) w| ≤
      |M| * (1 / 2 + 2 * Λ) * Real.exp (w / 2) := by
    rw [abs_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (abs_deriv_harmonicPlateauTest_le hΛ 4 w) (abs_nonneg M)
  have htri := abs_sub (deriv (harmonicPlateauTest B) (w + 4))
    (M * deriv (harmonicPlateauTest 4) w)
  linarith

private theorem integral_signedPlateauTest_sq_le {B : ℝ} (hB : 0 ≤ B) (M : ℝ) :
    ∫ u, signedPlateauTest M B u ^ 2 ≤ 2 * (1 + M ^ 2) * ∫ u, Real.exp (-|u|) := by
  have hH := isWindowTest_signedPlateauTest hB M
  have h1 := isWindowTest_harmonicPlateauTest hB
  have h2 := isWindowTest_harmonicPlateauTest (by norm_num : (0 : ℝ) ≤ 4)
  have i1 : Integrable fun u => harmonicPlateauTest B (u + 4) ^ 2 :=
    (integrable_sq h1.continuous h1.hasCompactSupport).comp_add_right 4
  have i2 : Integrable fun u => harmonicPlateauTest 4 u ^ 2 :=
    integrable_sq h2.continuous h2.hasCompactSupport
  have isum : Integrable fun u =>
      2 * harmonicPlateauTest B (u + 4) ^ 2 + 2 * M ^ 2 * harmonicPlateauTest 4 u ^ 2 :=
    (i1.const_mul 2).add (i2.const_mul (2 * M ^ 2))
  have hm := integral_mono (integrable_sq hH.continuous hH.hasCompactSupport) isum fun u => by
    dsimp only [signedPlateauTest]
    nlinarith only [sq_nonneg (harmonicPlateauTest B (u + 4) + M * harmonicPlateauTest 4 u)]
  rw [integral_add (i1.const_mul 2) (i2.const_mul (2 * M ^ 2)), integral_const_mul,
    integral_const_mul,
    integral_add_right_eq_self (μ := volume) (fun u => harmonicPlateauTest B u ^ 2) 4] at hm
  have hb1 := integral_harmonicPlateauTest_sq_le hB
  have hb2 := integral_harmonicPlateauTest_sq_le (by norm_num : (0 : ℝ) ≤ 4)
  nlinarith [sq_nonneg M]

private def signedPlateauScale (k : ℝ) : ℝ :=
  ((∫ u, Real.exp (-|u|)) + 1) / (2 * Real.exp (-3 * (1 + k)))

private def signedPlateauNegConst (k : ℝ) : ℝ :=
  signedPlateauScale k * ∫ u, harmonicPlateauTest 4 u * Real.exp (-(1 / 2 + k) * u)

private theorem shiftedPoleForm_signedPlateauTest_le {B k : ℝ} (hB : 6 ≤ B) (hk : 0 ≤ k)
    (hC_neg : signedPlateauNegConst k ≤ Real.exp (k * (B - 2))) :
    shiftedPoleForm k (signedPlateauTest (signedPlateauScale k) B) ≤
      -2 * (Real.exp (k * (B - 2)) - signedPlateauNegConst k) := by
  have hB0 : 0 ≤ B := by linarith
  have hE₀ : 0 ≤ ∫ u, Real.exp (-|u|) := integral_nonneg fun _ => (Real.exp_pos _).le
  have hM_pos : 0 < signedPlateauScale k := by unfold signedPlateauScale; positivity
  have h1_win : IsWindowTest (B + 4) (fun u => harmonicPlateauTest B (u + 4)) := by
    have h1 := isWindowTest_harmonicPlateauTest hB0
    refine ⟨h1.contDiff.comp (contDiff_id.add contDiff_const), fun u hu => ?_⟩
    simp only [mem_Icc, not_and_or, not_le] at hu
    rcases hu with hlt | hgt
    · exact h1.vanish (u + 4) (fun hm => by linarith [hm.1])
    · exact h1.vanish (u + 4) (fun hm => by linarith [hm.2])
  have h2_win : IsWindowTest 4 (harmonicPlateauTest 4) :=
    isWindowTest_harmonicPlateauTest (by norm_num)
  have hint1_pos : Integrable fun u =>
      harmonicPlateauTest B (u + 4) * Real.exp ((1 / 2 + k) * u) :=
    (h1_win.continuous.mul (by fun_prop : Continuous fun u : ℝ =>
      Real.exp ((1 / 2 + k) * u))).integrable_of_hasCompactSupport
      h1_win.hasCompactSupport.mul_right
  have hint2_pos : Integrable fun u =>
      harmonicPlateauTest 4 u * Real.exp ((1 / 2 + k) * u) :=
    (h2_win.continuous.mul (by fun_prop : Continuous fun u : ℝ =>
      Real.exp ((1 / 2 + k) * u))).integrable_of_hasCompactSupport
      h2_win.hasCompactSupport.mul_right
  have hint1_neg : Integrable fun u =>
      harmonicPlateauTest B (u + 4) * Real.exp (-(1 / 2 + k) * u) :=
    (h1_win.continuous.mul (by fun_prop : Continuous fun u : ℝ =>
      Real.exp (-(1 / 2 + k) * u))).integrable_of_hasCompactSupport
      h1_win.hasCompactSupport.mul_right
  have hint2_neg : Integrable fun u =>
      harmonicPlateauTest 4 u * Real.exp (-(1 / 2 + k) * u) :=
    (h2_win.continuous.mul (by fun_prop : Continuous fun u : ℝ =>
      Real.exp (-(1 / 2 + k) * u))).integrable_of_hasCompactSupport
      h2_win.hasCompactSupport.mul_right
  have hI_pos_le : ∫ u, signedPlateauTest (signedPlateauScale k) B u *
      Real.exp ((1 / 2 + k) * u) ≤ -1 := by
    have hsplit : (∫ u, signedPlateauTest (signedPlateauScale k) B u *
        Real.exp ((1 / 2 + k) * u)) =
        (∫ u, harmonicPlateauTest B (u + 4) * Real.exp ((1 / 2 + k) * u)) -
          signedPlateauScale k * ∫ u, harmonicPlateauTest 4 u * Real.exp ((1 / 2 + k) * u) := by
      have heq : (fun u => signedPlateauTest (signedPlateauScale k) B u *
          Real.exp ((1 / 2 + k) * u)) =
          fun u => harmonicPlateauTest B (u + 4) * Real.exp ((1 / 2 + k) * u) -
            signedPlateauScale k * (harmonicPlateauTest 4 u * Real.exp ((1 / 2 + k) * u)) := by
        funext u; unfold signedPlateauTest; ring
      rw [heq, integral_sub hint1_pos (hint2_pos.const_mul (signedPlateauScale k)),
        integral_const_mul]
    have h1_le : (∫ u, harmonicPlateauTest B (u + 4) * Real.exp ((1 / 2 + k) * u)) ≤
        ∫ u, Real.exp (-|u|) := by
      have hshift : (∫ u, harmonicPlateauTest B (u + 4) * Real.exp ((1 / 2 + k) * u)) =
          ∫ v, harmonicPlateauTest B v * Real.exp ((1 / 2 + k) * (v - 4)) := by
        have := integral_add_right_eq_self (μ := volume)
          (fun v => harmonicPlateauTest B v * Real.exp ((1 / 2 + k) * (v - 4))) 4
        rw [← this]
        refine integral_congr_ae (Eventually.of_forall fun u => ?_)
        exact congrArg (fun x => harmonicPlateauTest B (u + 4) * Real.exp x) (by ring)
      rw [hshift]
      have hB_win := isWindowTest_harmonicPlateauTest hB0
      refine integral_mono
        ((hB_win.continuous.mul (by fun_prop : Continuous fun v : ℝ =>
          Real.exp ((1 / 2 + k) * (v - 4)))).integrable_of_hasCompactSupport
          hB_win.hasCompactSupport.mul_right)
        _root_.RHTower.integrable_exp_neg_abs fun v => ?_
      dsimp only [Pi.mul_apply]
      rcases le_or_gt 0 v with hv | hv
      · rw [harmonicPlateauTest_eq_zero_of_nonneg hB0 hv, zero_mul]
        exact (Real.exp_pos _).le
      · calc harmonicPlateauTest B v * Real.exp ((1 / 2 + k) * (v - 4))
            ≤ Real.exp (v / 2) * Real.exp ((1 / 2 + k) * (v - 4)) :=
              mul_le_mul_of_nonneg_right (harmonicPlateauTest_le_exp B v) (Real.exp_pos _).le
          _ = Real.exp (v + k * v - 4 * (1 / 2 + k)) := by
              rw [← Real.exp_add]; congr 1; ring
          _ ≤ Real.exp (-|v|) := by
              rw [abs_of_neg hv, neg_neg]
              exact Real.exp_le_exp.mpr (by nlinarith)
    have h2_ge := integral_harmonicPlateauTest_exp_pos_ge (le_rfl : (4 : ℝ) ≤ 4) hk
    have hM_mul : signedPlateauScale k * (2 * Real.exp (-3 * (1 + k))) =
        (∫ u, Real.exp (-|u|)) + 1 := by
      unfold signedPlateauScale
      exact div_mul_cancel₀ _ (by positivity)
    have hM2 : (∫ u, Real.exp (-|u|)) + 1 ≤
        signedPlateauScale k * ∫ u, harmonicPlateauTest 4 u * Real.exp ((1 / 2 + k) * u) := by
      rw [← hM_mul]
      exact mul_le_mul_of_nonneg_left h2_ge hM_pos.le
    linarith only [hsplit, h1_le, hM2]
  have hI_neg_ge : Real.exp (k * (B - 2)) - signedPlateauNegConst k ≤
      ∫ u, signedPlateauTest (signedPlateauScale k) B u * Real.exp (-(1 / 2 + k) * u) := by
    have hsplit : (∫ u, signedPlateauTest (signedPlateauScale k) B u *
        Real.exp (-(1 / 2 + k) * u)) =
        (∫ u, harmonicPlateauTest B (u + 4) * Real.exp (-(1 / 2 + k) * u)) -
          signedPlateauNegConst k := by
      have heq : (fun u => signedPlateauTest (signedPlateauScale k) B u *
          Real.exp (-(1 / 2 + k) * u)) =
          fun u => harmonicPlateauTest B (u + 4) * Real.exp (-(1 / 2 + k) * u) -
            signedPlateauScale k * (harmonicPlateauTest 4 u * Real.exp (-(1 / 2 + k) * u)) := by
        funext u; unfold signedPlateauTest; ring
      rw [heq, integral_sub hint1_neg (hint2_neg.const_mul (signedPlateauScale k)),
        integral_const_mul]
      rfl
    have h1_ge : Real.exp (k * (B - 2)) ≤
        ∫ u, harmonicPlateauTest B (u + 4) * Real.exp (-(1 / 2 + k) * u) := by
      have hshift : (∫ u, harmonicPlateauTest B (u + 4) * Real.exp (-(1 / 2 + k) * u)) =
          Real.exp (4 * (1 / 2 + k)) *
            ∫ v, harmonicPlateauTest B v * Real.exp (-(1 / 2 + k) * v) := by
        calc (∫ u, harmonicPlateauTest B (u + 4) * Real.exp (-(1 / 2 + k) * u))
            = ∫ u, harmonicPlateauTest B (u + 4) * Real.exp (-(1 / 2 + k) * ((u + 4) - 4)) :=
              integral_congr_ae (Eventually.of_forall fun u =>
                congrArg (fun x => harmonicPlateauTest B (u + 4) * Real.exp x) (by ring))
          _ = ∫ v, harmonicPlateauTest B v * Real.exp (-(1 / 2 + k) * (v - 4)) :=
              integral_add_right_eq_self (μ := volume)
                (fun v => harmonicPlateauTest B v * Real.exp (-(1 / 2 + k) * (v - 4))) 4
          _ = Real.exp (4 * (1 / 2 + k)) *
                ∫ v, harmonicPlateauTest B v * Real.exp (-(1 / 2 + k) * v) := by
              rw [← integral_const_mul]
              refine integral_congr_ae (Eventually.of_forall fun v => ?_)
              dsimp only
              rw [← mul_assoc, mul_comm (Real.exp (4 * (1 / 2 + k))), mul_assoc, ← Real.exp_add]
              exact congrArg (fun x => harmonicPlateauTest B v * Real.exp x) (by ring)
      rw [hshift]
      have hge := integral_harmonicPlateauTest_exp_neg_ge hB hk
      have he1 : 1 ≤ Real.exp (4 * (1 / 2 + k)) := Real.one_le_exp (by positivity)
      calc Real.exp (k * (B - 2)) = 1 * Real.exp (k * (B - 2)) := (one_mul _).symm
        _ ≤ Real.exp (4 * (1 / 2 + k)) *
              ∫ v, harmonicPlateauTest B v * Real.exp (-(1 / 2 + k) * v) :=
            mul_le_mul he1 hge (Real.exp_pos _).le (by positivity)
    linarith only [hsplit, h1_ge]
  unfold shiftedPoleForm
  have hIn_nn : 0 ≤ ∫ u, signedPlateauTest (signedPlateauScale k) B u *
      Real.exp (-(1 / 2 + k) * u) :=
    (sub_nonneg.mpr hC_neg).trans hI_neg_ge
  have hp1 := mul_le_mul_of_nonneg_right hI_pos_le hIn_nn
  have hp2 := mul_le_mul_of_nonpos_left hI_neg_ge (by norm_num : (-1 : ℝ) ≤ 0)
  linarith only [hp1, hp2]

private theorem exists_gt_of_pos_exp {c k P Q : ℝ} (hc : 0 < c) (hk : 0 < k) :
    ∃ B : ℝ, 6 ≤ B ∧ P + Q * (B + 5) ^ 2 < c * Real.exp (k * (B - 2)) := by
  set P' := max 1 |P|
  set Q' := max 1 |Q|
  have hP' : 1 ≤ P' := le_max_left _ _
  have hQ' : 1 ≤ Q' := le_max_left _ _
  set γ := c * k ^ 3 / 6
  have hγ : 0 < γ := by positivity
  set B := max 6 ((P' + 64 * Q' + 1) / γ + 2)
  have hB6 : 6 ≤ B := le_max_left _ _
  have hBγ : (P' + 64 * Q' + 1) / γ + 2 ≤ B := le_max_right _ _
  refine ⟨B, hB6, ?_⟩
  have hB2_ge4 : 4 ≤ B - 2 := by linarith
  have hB5_le : (B + 5) ^ 2 ≤ 64 * (B - 2) ^ 2 := by
    have : B + 5 ≤ 8 * (B - 2) := by linarith
    nlinarith
  have hP_le : P ≤ P' := (le_abs_self P).trans (le_max_right _ _)
  have hQ_le : Q * (B + 5) ^ 2 ≤ Q' * 64 * (B - 2) ^ 2 := by
    calc Q * (B + 5) ^ 2 ≤ |Q| * (B + 5) ^ 2 :=
          mul_le_mul_of_nonneg_right (le_abs_self Q) (sq_nonneg _)
      _ ≤ Q' * (64 * (B - 2) ^ 2) :=
          mul_le_mul (le_max_right _ _) hB5_le (sq_nonneg _) (by linarith)
      _ = Q' * 64 * (B - 2) ^ 2 := by ring
  have hsq1 : 1 ≤ (B - 2) ^ 2 := by nlinarith
  have hmul_γ : P' + 64 * Q' + 1 ≤ γ * (B - 2) := by
    have : (P' + 64 * Q' + 1) / γ ≤ B - 2 := by linarith
    linarith [(div_le_iff₀ hγ).mp this]
  have hcub : (P' + 64 * Q' + 1) * (B - 2) ^ 2 ≤ γ * (B - 2) ^ 3 := by
    have := mul_le_mul_of_nonneg_right hmul_γ (sq_nonneg (B - 2))
    linarith [show γ * (B - 2) * (B - 2) ^ 2 = γ * (B - 2) ^ 3 by ring]
  have hexp : γ * (B - 2) ^ 3 ≤ c * Real.exp (k * (B - 2)) := by
    have hp := Real.pow_div_factorial_le_exp (x := k * (B - 2)) (by positivity) 3
    norm_num [Nat.factorial] at hp
    have hm := mul_le_mul_of_nonneg_left hp hc.le
    linarith [show c * ((k * (B - 2)) ^ 3 / 6) = γ * (B - 2) ^ 3 by dsimp only [γ]; ring]
  nlinarith

private theorem exists_harmonicPlateauTest_exp_bounds :
    ∃ K_pos : ℝ, 0 ≤ K_pos ∧ ∀ B : ℝ,
      (∀ w, |harmonicPlateauTest B w| ≤ K_pos * Real.exp (w / 2)) ∧
      (∀ w, |deriv (harmonicPlateauTest B) w| ≤ K_pos * Real.exp (w / 2)) := by
  obtain ⟨Λ, hΛ0, hΛ⟩ := GaloisForLFunctions.HTGeometry.exists_bound_deriv_smoothTransition
  refine ⟨1 + (1 / 2 + 2 * Λ), by positivity, fun B => ⟨fun w => ?_, fun w => ?_⟩⟩
  · rw [abs_of_nonneg (harmonicPlateauTest_nonneg B w)]
    exact (harmonicPlateauTest_le_exp B w).trans
      (le_mul_of_one_le_left (Real.exp_pos _).le (by linarith))
  · exact (abs_deriv_harmonicPlateauTest_le hΛ B w).trans
      (mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le)

private theorem exists_signedPlateauTest_exp_bounds (M : ℝ) :
    ∃ K_M : ℝ, 0 ≤ K_M ∧ ∀ B : ℝ,
      (∀ w, |signedPlateauTest M B w| ≤ K_M * Real.exp (w / 2)) ∧
      (∀ w, |deriv (signedPlateauTest M B) w| ≤ K_M * Real.exp (w / 2)) := by
  obtain ⟨Λ, hΛ0, hΛ⟩ := GaloisForLFunctions.HTGeometry.exists_bound_deriv_smoothTransition
  refine ⟨(Real.exp 2 + |M|) * (1 + (1 / 2 + 2 * Λ)), by positivity,
    fun B => ⟨fun w => ?_, fun w => ?_⟩⟩
  · refine (abs_signedPlateauTest_le M B w).trans (mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le)
    have h1 : 0 ≤ Real.exp 2 + |M| := by positivity
    nlinarith
  · refine (abs_deriv_signedPlateauTest_le hΛ M B w).trans
      (mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le)
    have h1 : 0 ≤ Real.exp 2 + |M| := by positivity
    nlinarith

private theorem exists_integral_signedPlateauTest_sq_le (M : ℝ) :
    ∃ E_M : ℝ, 0 ≤ E_M ∧ ∀ B : ℝ, 0 ≤ B → ∫ u, signedPlateauTest M B u ^ 2 ≤ E_M := by
  have hE₀ : 0 ≤ ∫ u, Real.exp (-|u|) := integral_nonneg fun _ => (Real.exp_pos _).le
  exact ⟨2 * (1 + M ^ 2) * ∫ u, Real.exp (-|u|), by positivity,
    fun B hB => integral_signedPlateauTest_sq_le hB M⟩

private theorem exists_abs_archGammaForm_signedPlateauTest_le (M : ℝ) :
    ∃ C_M : ℝ, 0 ≤ C_M ∧ ∀ B : ℝ, 0 ≤ B → |archGammaForm (signedPlateauTest M B)| ≤ C_M := by
  obtain ⟨K_M, hKM0, hKM⟩ := exists_signedPlateauTest_exp_bounds M
  obtain ⟨E_M, hEM0, hEM⟩ := exists_integral_signedPlateauTest_sq_le M
  have hE₀ : 0 ≤ ∫ u, Real.exp (-|u|) := integral_nonneg fun _ => (Real.exp_pos _).le
  refine ⟨|Zeta23.EF.gammaBracket 0| * E_M +
    ∫ x in Ioi (0 : ℝ),
      (3 / 2 * K_M ^ 2 * Real.exp 1 * (∫ u, Real.exp (-|u|)) + 6 * E_M) *
        Real.exp (-(1 / 2 * x)), ?_, fun B hB => ?_⟩
  · refine add_nonneg (mul_nonneg (abs_nonneg _) hEM0)
      (setIntegral_nonneg measurableSet_Ioi fun _ _ =>
        mul_nonneg (by positivity) (Real.exp_pos _).le)
  · exact abs_archGammaForm_le_of_deriv_exp_bound (by linarith : 0 ≤ B + 4) hKM0 hEM0
      (isWindowTest_signedPlateauTest hB M) (hEM B hB) (hKM B).2

/-- General two-sided shifted-pole residue pinching for any Gamma functional `Γ_form` bounded
uniformly in `B` on `harmonicPlateauTest B` and `signedPlateauTest M B`. -/
private theorem shiftedPole_weight_pinched_of_bounded_gamma {k : ℝ}
    (hk0 : 0 < k) (hk1 : k < 1) {Γ_form : (ℝ → ℝ) → ℝ} {β φ : ℝ}
    (hΓ_plat : ∃ C_Γ : ℝ, 0 ≤ C_Γ ∧ ∀ B : ℝ, 0 ≤ B → Γ_form (harmonicPlateauTest B) ≤ C_Γ)
    (hΓ_signed : ∀ M : ℝ, ∃ C_M : ℝ, 0 ≤ C_M ∧
      ∀ B : ℝ, 0 ≤ B → Γ_form (signedPlateauTest M B) ≤ C_M)
    (hdom : ∀ A : ℝ, 0 ≤ A → ∀ H : ℝ → ℝ, IsWindowTest A H →
      tatePointCount A H k ≤ Γ_form H + β * windowPoleForm H + φ * shiftedPoleForm k H) :
    φ = eulerProductPoleWeight k := by
  apply le_antisymm
  · by_contra hgt_phi
    push Not at hgt_phi
    obtain ⟨δ, hδ_eq⟩ : ∃ x, x = φ - eulerProductPoleWeight k := ⟨_, rfl⟩
    have hδ : 0 < δ := by rw [hδ_eq]; exact sub_pos.mpr hgt_phi
    obtain ⟨C_k, hCk, hasymp⟩ := abs_tatePointCount_sub_eulerProduct_shiftedPoleForm_le hk0 hk1
    obtain ⟨C_M, hCM0, hCM⟩ := hΓ_signed (signedPlateauScale k)
    obtain ⟨K_M, hKM0, hKM⟩ := exists_signedPlateauTest_exp_bounds (signedPlateauScale k)
    obtain ⟨C_neg, hC_neg_eq⟩ : ∃ x, x = signedPlateauNegConst k := ⟨_, rfl⟩
    obtain ⟨B, hB6, hgt⟩ := exists_gt_of_pos_exp
      (c := 2 * δ) (k := k)
      (P := C_M + 2 * δ * |C_neg| + δ * (|C_neg| + 1))
      (Q := (2 * |β| + C_k) * K_M ^ 2)
      (by positivity) hk0
    have hB0 : 0 ≤ B := by linarith
    have hA0 : 0 ≤ B + 4 := by linarith
    have hH := isWindowTest_signedPlateauTest hB0 (signedPlateauScale k)
    obtain ⟨hK0, hK1⟩ := hKM B
    have hC_neg_le : signedPlateauNegConst k ≤ Real.exp (k * (B - 2)) := by
      have hQ0 : 0 ≤ (2 * |β| + C_k) * K_M ^ 2 * (B + 5) ^ 2 := by positivity
      have hC1 : 2 * δ * C_neg ≤ 2 * δ * |C_neg| :=
        mul_le_mul_of_nonneg_left (le_abs_self C_neg) (by positivity)
      have hC2 : 0 < δ * (|C_neg| + 1) := by positivity
      have hlt_exp : 2 * δ * C_neg < 2 * δ * Real.exp (k * (B - 2)) := by
        linarith only [hCM0, hQ0, hC1, hC2, hgt]
      rw [← hC_neg_eq]
      exact (lt_of_mul_lt_mul_left hlt_exp (by positivity)).le
    have hshift := shiftedPoleForm_signedPlateauTest_le hB6 hk0.le hC_neg_le
    rw [← hC_neg_eq] at hshift
    have herr := (neg_abs_le _).trans'
      (neg_le_neg (hasymp (B + 4) K_M hA0 hKM0 (signedPlateauTest (signedPlateauScale k) B)
        hH hK0 hK1))
    rw [show (B + 4 + 1) ^ 2 = (B + 5) ^ 2 by ring] at herr
    have hd := hdom (B + 4) hA0 (signedPlateauTest (signedPlateauScale k) B) hH
    have h1 : Γ_form (signedPlateauTest (signedPlateauScale k) B) ≤ C_M := hCM B hB0
    have h2 : β * windowPoleForm (signedPlateauTest (signedPlateauScale k) B) ≤
        2 * |β| * K_M ^ 2 * (B + 5) ^ 2 := by
      have hp := abs_windowPoleForm_le_of_exp_bound hA0 hKM0 hH hK0
      have hsq : (B + 4) ^ 2 ≤ (B + 5) ^ 2 := by nlinarith
      calc β * windowPoleForm (signedPlateauTest (signedPlateauScale k) B)
          ≤ |β| * |windowPoleForm (signedPlateauTest (signedPlateauScale k) B)| := by
            rw [← abs_mul]; exact le_abs_self _
        _ ≤ |β| * (2 * K_M ^ 2 * (B + 4) ^ 2) := mul_le_mul_of_nonneg_left hp (abs_nonneg _)
        _ = 2 * |β| * K_M ^ 2 * (B + 4) ^ 2 := by ring
        _ ≤ 2 * |β| * K_M ^ 2 * (B + 5) ^ 2 := mul_le_mul_of_nonneg_left hsq (by positivity)
    have hmul_S : δ * (-shiftedPoleForm k (signedPlateauTest (signedPlateauScale k) B)) =
        eulerProductPoleWeight k * shiftedPoleForm k (signedPlateauTest (signedPlateauScale k) B) -
          φ * shiftedPoleForm k (signedPlateauTest (signedPlateauScale k) B) := by
      rw [hδ_eq]; ring
    have hrhs : δ * (-shiftedPoleForm k (signedPlateauTest (signedPlateauScale k) B)) ≤
        C_M + (2 * |β| + C_k) * K_M ^ 2 * (B + 5) ^ 2 := by
      have hring : 2 * |β| * K_M ^ 2 * (B + 5) ^ 2 + C_k * K_M ^ 2 * (B + 5) ^ 2 =
          (2 * |β| + C_k) * K_M ^ 2 * (B + 5) ^ 2 := by ring
      linarith only [hmul_S, herr, hd, h1, h2, hring]
    have hlhs : 2 * δ * (Real.exp (k * (B - 2)) - C_neg) ≤
        δ * (-shiftedPoleForm k (signedPlateauTest (signedPlateauScale k) B)) := by
      have hm := mul_le_mul_of_nonneg_left (neg_le_neg hshift) hδ.le
      linarith only [hm]
    have hC_le : 2 * δ * C_neg ≤ 2 * δ * |C_neg| + δ * (|C_neg| + 1) := by
      have hC1 : 2 * δ * C_neg ≤ 2 * δ * |C_neg| :=
        mul_le_mul_of_nonneg_left (le_abs_self C_neg) (by positivity)
      have hC2 : 0 ≤ δ * (|C_neg| + 1) := by positivity
      linarith only [hC1, hC2]
    linarith only [hgt, hlhs, hrhs, hC_le]
  · by_contra hlt_phi
    push Not at hlt_phi
    obtain ⟨δ, hδ_eq⟩ : ∃ x, x = eulerProductPoleWeight k - φ := ⟨_, rfl⟩
    have hδ : 0 < δ := by rw [hδ_eq]; exact sub_pos.mpr hlt_phi
    obtain ⟨C_k, hCk, hasymp⟩ := abs_tatePointCount_sub_eulerProduct_shiftedPoleForm_le hk0 hk1
    obtain ⟨C_Γ, hCΓ0, hCΓ⟩ := hΓ_plat
    obtain ⟨K_pos, hKpos0, hKpos⟩ := exists_harmonicPlateauTest_exp_bounds
    obtain ⟨c, hc_eq⟩ : ∃ x, x = δ * (4 * Real.exp (-3 * (1 + k))) := ⟨_, rfl⟩
    have hc : 0 < c := by rw [hc_eq]; positivity
    obtain ⟨B, hB6, hgt⟩ := exists_gt_of_pos_exp
      (c := c) (k := k) (P := C_Γ) (Q := 2 * |β| + C_k * K_pos ^ 2) hc hk0
    have hB0 : 0 ≤ B := by linarith
    have hH := isWindowTest_harmonicPlateauTest hB0
    obtain ⟨hK0, hK1⟩ := hKpos B
    have herr := (neg_abs_le _).trans'
      (neg_le_neg (hasymp B K_pos hB0 hKpos0 (harmonicPlateauTest B) hH hK0 hK1))
    have hd := hdom B hB0 (harmonicPlateauTest B) hH
    have hshift := shiftedPoleForm_harmonicPlateauTest_ge hB6 hk0.le
    have h1 : Γ_form (harmonicPlateauTest B) ≤ C_Γ := hCΓ B hB0
    have h2 : β * windowPoleForm (harmonicPlateauTest B) ≤ 2 * |β| * (B + 5) ^ 2 := by
      have hp := (windowPoleForm_harmonicPlateauTest_bounds hB0).2
      have hB_sq : B ^ 2 ≤ (B + 5) ^ 2 := by nlinarith
      calc β * windowPoleForm (harmonicPlateauTest B)
          ≤ |β| * |windowPoleForm (harmonicPlateauTest B)| := by
            rw [← abs_mul]; exact le_abs_self _
        _ ≤ |β| * (2 * B ^ 2) := mul_le_mul_of_nonneg_left hp (abs_nonneg _)
        _ = 2 * |β| * B ^ 2 := by ring
        _ ≤ 2 * |β| * (B + 5) ^ 2 := mul_le_mul_of_nonneg_left hB_sq (by positivity)
    have herr_B5 : C_k * K_pos ^ 2 * (B + 1) ^ 2 ≤ C_k * K_pos ^ 2 * (B + 5) ^ 2 :=
      mul_le_mul_of_nonneg_left (by nlinarith) (by positivity)
    have hlhs : c * Real.exp (k * (B - 2)) ≤ δ * shiftedPoleForm k (harmonicPlateauTest B) := by
      have hm := mul_le_mul_of_nonneg_left hshift hδ.le
      have hring : δ * (4 * Real.exp (-3 * (1 + k)) * Real.exp (k * (B - 2))) =
          c * Real.exp (k * (B - 2)) := by rw [hc_eq]; ring
      linarith only [hm, hring]
    have hmul_S : δ * shiftedPoleForm k (harmonicPlateauTest B) =
        eulerProductPoleWeight k * shiftedPoleForm k (harmonicPlateauTest B) -
          φ * shiftedPoleForm k (harmonicPlateauTest B) := by
      rw [hδ_eq]; ring
    have hrhs : δ * shiftedPoleForm k (harmonicPlateauTest B) ≤
        C_Γ + (2 * |β| + C_k * K_pos ^ 2) * (B + 5) ^ 2 := by
      have hring : 2 * |β| * (B + 5) ^ 2 + C_k * K_pos ^ 2 * (B + 5) ^ 2 =
          (2 * |β| + C_k * K_pos ^ 2) * (B + 5) ^ 2 := by ring
      linarith only [hmul_S, herr, herr_B5, hd, h1, h2, hring]
    linarith only [hgt, hlhs, hrhs]

/-- **Two-sided shifted-pole residue pinching**: for `0 < k < 1` and arbitrary `α, β, φ ∈ ℝ`,
if `α · archGammaForm H + β · windowPoleForm H + φ · shiftedPoleForm k H` dominates
`tatePointCount A H k` across all windows, then `φ = eulerProductPoleWeight k = 1 / ζ(1 + k)`. -/
theorem shiftedPole_weight_pinched_eq_eulerProduct {k : ℝ} (hk0 : 0 < k) (hk1 : k < 1)
    {α β φ : ℝ}
    (hdom : ∀ A : ℝ, 0 ≤ A → ∀ H : ℝ → ℝ, IsWindowTest A H →
      tatePointCount A H k ≤ α * archGammaForm H + β * windowPoleForm H + φ * shiftedPoleForm k H) :
    φ = eulerProductPoleWeight k := by
  refine shiftedPole_weight_pinched_of_bounded_gamma hk0 hk1
    (Γ_form := fun H => α * archGammaForm H) ?_ (fun M => ?_) hdom
  · obtain ⟨C_Γ, hCΓ0, hCΓ⟩ := exists_abs_archGammaForm_harmonicPlateauTest_le
    refine ⟨|α| * C_Γ, by positivity, fun B hB => ?_⟩
    exact (le_abs_self _).trans ((abs_mul _ _).le.trans
      (mul_le_mul_of_nonneg_left (hCΓ B hB) (abs_nonneg _)))
  · obtain ⟨C_M, hCM0, hCM⟩ := exists_abs_archGammaForm_signedPlateauTest_le M
    refine ⟨|α| * C_M, by positivity, fun B hB => ?_⟩
    exact (le_abs_self _).trans ((abs_mul _ _).le.trans
      (mul_le_mul_of_nonneg_left (hCM B hB) (abs_nonneg _)))

theorem eulerProductPoleWeight_le_of_domination_archGamma_poles {k : ℝ}
    (hk0 : 0 < k) (hk1 : k < 1) {α β φ : ℝ}
    (hdom : ∀ A : ℝ, 0 ≤ A → ∀ H : ℝ → ℝ, IsWindowTest A H →
      tatePointCount A H k ≤ α * archGammaForm H + β * windowPoleForm H + φ * shiftedPoleForm k H) :
    eulerProductPoleWeight k ≤ φ :=
  (shiftedPole_weight_pinched_eq_eulerProduct hk0 hk1 hdom).ge

theorem le_eulerProductPoleWeight_of_domination_archGamma_poles {k : ℝ}
    (hk0 : 0 < k) (hk1 : k < 1) {α β φ : ℝ}
    (hdom : ∀ A : ℝ, 0 ≤ A → ∀ H : ℝ → ℝ, IsWindowTest A H →
      tatePointCount A H k ≤ α * archGammaForm H + β * windowPoleForm H + φ * shiftedPoleForm k H) :
    φ ≤ eulerProductPoleWeight k :=
  (shiftedPole_weight_pinched_eq_eulerProduct hk0 hk1 hdom).le

/-- Two-sided residue pinching for `backwardTateGammaForm` on `0 < k ≤ 1 / 4`. -/
theorem shiftedPole_weight_pinched_backwardTateGamma {k : ℝ} (hk0 : 0 < k) (hk4 : k ≤ 1 / 4)
    {φ : ℝ}
    (hdom : ∀ A : ℝ, 0 ≤ A → ∀ H : ℝ → ℝ, IsWindowTest A H →
      tatePointCount A H k ≤ backwardTateGammaForm k H + φ * shiftedPoleForm k H) :
    φ = eulerProductPoleWeight k := by
  have hk_abs : |k| ≤ 1 / 4 := by rw [abs_of_pos hk0]; exact hk4
  refine shiftedPole_weight_pinched_of_bounded_gamma hk0 (by linarith)
    (Γ_form := backwardTateGammaForm k) (β := 0) ?_ (fun M => ?_)
    (fun A hA H hH => by simpa using hdom A hA H hH)
  · obtain ⟨C_Γ, hCΓ0, hCΓ⟩ := exists_abs_archGammaForm_harmonicPlateauTest_le
    refine ⟨k * C_Γ, by positivity, fun B hB => ?_⟩
    exact (backwardTateGammaForm_le_mul_archGammaForm_of_nonneg
      (harmonicPlateauTest_nonneg B) k).trans
      (mul_le_mul_of_nonneg_left ((le_abs_self _).trans (hCΓ B hB)) hk0.le)
  · obtain ⟨C_M, hCM0, hCM⟩ := exists_abs_archGammaForm_signedPlateauTest_le M
    obtain ⟨E_M, hEM0, hEM⟩ := exists_integral_signedPlateauTest_sq_le M
    refine ⟨k * C_M + 18 * k ^ 2 * E_M, by positivity, fun B hB => ?_⟩
    have hrem := (le_abs_self _).trans
      (abs_backwardTateGammaForm_sub_linear_le (isWindowTest_signedPlateauTest hB M) hk_abs)
    have h1 : k * archGammaForm (signedPlateauTest M B) ≤ k * C_M :=
      mul_le_mul_of_nonneg_left ((le_abs_self _).trans (hCM B hB)) hk0.le
    have h2 : 18 * k ^ 2 * ∫ u, signedPlateauTest M B u ^ 2 ≤ 18 * k ^ 2 * E_M :=
      mul_le_mul_of_nonneg_left (hEM B hB) (by positivity)
    linarith only [hrem, h1, h2]

/-- Two-sided residue pinching for `symTateGammaForm` on `0 < k ≤ 1 / 4`. -/
theorem shiftedPole_weight_pinched_symTateGamma {k : ℝ} (hk0 : 0 < k) (hk4 : k ≤ 1 / 4)
    {φ : ℝ}
    (hdom : ∀ A : ℝ, 0 ≤ A → ∀ H : ℝ → ℝ, IsWindowTest A H →
      tatePointCount A H k ≤ symTateGammaForm k H + φ * shiftedPoleForm k H) :
    φ = eulerProductPoleWeight k := by
  have hk_abs : |k| ≤ 1 / 4 := by rw [abs_of_pos hk0]; exact hk4
  refine shiftedPole_weight_pinched_of_bounded_gamma hk0 (by linarith)
    (Γ_form := symTateGammaForm k) (β := 0) ?_ (fun M => ?_)
    (fun A hA H hH => by simpa using hdom A hA H hH)
  · obtain ⟨C_Γ, hCΓ0, hCΓ⟩ := exists_abs_archGammaForm_harmonicPlateauTest_le
    refine ⟨k * C_Γ, by positivity, fun B hB => ?_⟩
    exact (symTateGammaForm_le_mul_archGammaForm_of_nonneg
      (harmonicPlateauTest_nonneg B) hk0.le).trans
      (mul_le_mul_of_nonneg_left ((le_abs_self _).trans (hCΓ B hB)) hk0.le)
  · obtain ⟨C_M, hCM0, hCM⟩ := exists_abs_archGammaForm_signedPlateauTest_le M
    obtain ⟨E_M, hEM0, hEM⟩ := exists_integral_signedPlateauTest_sq_le M
    refine ⟨k * C_M + 18 * k ^ 2 * E_M, by positivity, fun B hB => ?_⟩
    have hrem := (le_abs_self _).trans
      (abs_symTateGammaForm_sub_linear_le (isWindowTest_signedPlateauTest hB M) hk_abs)
    have h1 : k * archGammaForm (signedPlateauTest M B) ≤ k * C_M :=
      mul_le_mul_of_nonneg_left ((le_abs_self _).trans (hCM B hB)) hk0.le
    have h2 : 18 * k ^ 2 * ∫ u, signedPlateauTest M B u ^ 2 ≤ 18 * k ^ 2 * E_M :=
      mul_le_mul_of_nonneg_left (hEM B hB) (by positivity)
    linarith only [hrem, h1, h2]

/-- Immediate refutation of the `1`-jet-compatible shifted-pole archimedean weight `φ = k`
for `k · archGammaForm` (`0 < k < 1`), since `1 / ζ(1 + k) < k`. -/
theorem not_forall_window_domination_linear_shiftedPole {k : ℝ} (hk0 : 0 < k) (hk1 : k < 1) :
    ¬ (∀ A : ℝ, 0 ≤ A → ∀ H : ℝ → ℝ, IsWindowTest A H →
        tatePointCount A H k ≤ k * archGammaForm H + k * shiftedPoleForm k H) := by
  intro hdom
  have hpinch : k = eulerProductPoleWeight k :=
    shiftedPole_weight_pinched_eq_eulerProduct hk0 hk1 (α := k) (β := 0) (φ := k) fun A hA H hH => by
      simpa using hdom A hA H hH
  exact (eulerProductPoleWeight_lt_self hk0).ne hpinch.symm

/-- Immediate refutation of `backwardTateGammaForm k H + k · shiftedPoleForm k H` (`0 < k ≤ 1 / 4`). -/
theorem not_forall_window_domination_backwardTateGamma_shiftedPole {k : ℝ}
    (hk0 : 0 < k) (hk4 : k ≤ 1 / 4) :
    ¬ (∀ A : ℝ, 0 ≤ A → ∀ H : ℝ → ℝ, IsWindowTest A H →
        tatePointCount A H k ≤ backwardTateGammaForm k H + k * shiftedPoleForm k H) := by
  intro hdom
  exact (eulerProductPoleWeight_lt_self hk0).ne
    (shiftedPole_weight_pinched_backwardTateGamma hk0 hk4 hdom).symm

/-- Immediate refutation of `symTateGammaForm k H + k · shiftedPoleForm k H` (`0 < k ≤ 1 / 4`). -/
theorem not_forall_window_domination_symTateGamma_shiftedPole {k : ℝ}
    (hk0 : 0 < k) (hk4 : k ≤ 1 / 4) :
    ¬ (∀ A : ℝ, 0 ≤ A → ∀ H : ℝ → ℝ, IsWindowTest A H →
        tatePointCount A H k ≤ symTateGammaForm k H + k * shiftedPoleForm k H) := by
  intro hdom
  exact (eulerProductPoleWeight_lt_self hk0).ne
    (shiftedPole_weight_pinched_symTateGamma hk0 hk4 hdom).symm

/-! ### Refutation of `φ ≤ 1 / ζ(1 + k)` on `windowRiemannKernel` and complete no-go for all `φ ∈ ℝ` -/

private theorem riemannPhiTransform_one :
    _root_.RHTower.riemannPhiTransform 1 = 1 / 2 := by
  set xi0 : ℂ → ℂ := fun s => s * (s - 1) / 2 * completedRiemannZeta₀ s + 1 / 2
  have hf : AnalyticOnNhd ℂ _root_.RHTower.riemannPhiTransform Set.univ :=
    fun z _ => _root_.RHTower.differentiable_riemannPhiTransform.analyticAt z
  have hg : AnalyticOnNhd ℂ xi0 Set.univ := fun z _ => by
    dsimp only [xi0]
    exact (((by fun_prop : Differentiable ℂ fun s : ℂ => s * (s - 1) / 2).mul
      differentiable_completedZeta₀).add (differentiable_const _)).analyticAt z
  have hev : _root_.RHTower.riemannPhiTransform =ᶠ[𝓝 (2 : ℂ)] xi0 := by
    have hopen : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [hopen.mem_nhds (by simp : (1 : ℝ) < (2 : ℂ).re)] with s hs
    have hs0 : s ≠ 0 := fun h => by rw [h] at hs; norm_num [Set.mem_setOf_eq] at hs
    have hs1 : 1 - s ≠ 0 := fun h => by
      have : s = 1 := by linear_combination -h
      rw [this] at hs; norm_num [Set.mem_setOf_eq] at hs
    rw [_root_.RHTower.riemannPhiTransform_eq_of_one_lt_re hs, completedRiemannZeta_eq s]
    dsimp only [xi0]
    field_simp [hs0, hs1]
    ring
  have h1 := hf.eqOn_of_preconnected_of_eventuallyEq hg isPreconnected_univ
    (mem_univ (2 : ℂ)) hev (mem_univ (1 : ℂ))
  simpa [xi0] using h1

private theorem integrable_riemannKernelReal_mul_exp (c : ℝ) :
    Integrable fun t : ℝ => _root_.RHTower.riemannKernelReal t * Real.exp (c * t) := by
  obtain ⟨C, hC0, hC⟩ :=
    _root_.RHTower.exists_norm_riemannPhiKernel_le_exp (B := |c| + 1) (by positivity)
  refine (_root_.RHTower.integrable_exp_neg_abs.const_mul C).mono'
    ((_root_.RHTower.continuous_riemannKernelReal.mul
      (by fun_prop : Continuous fun t : ℝ => Real.exp (c * t))).aestronglyMeasurable)
    (Eventually.of_forall fun t => ?_)
  have hk_pos := (_root_.RHTower.riemannKernelReal_pos t).le
  have hnorm : _root_.RHTower.riemannKernelReal t = ‖_root_.RHTower.riemannPhiKernel t‖ := by
    rw [_root_.RHTower.riemannPhiKernel_eq_ofReal, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg hk_pos]
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hk_pos (Real.exp_pos _).le), hnorm]
  calc ‖_root_.RHTower.riemannPhiKernel t‖ * Real.exp (c * t)
      ≤ C * Real.exp (-((|c| + 1) * |t|)) * Real.exp (c * t) :=
        mul_le_mul_of_nonneg_right (hC t) (Real.exp_pos _).le
    _ = C * Real.exp (-((|c| + 1) * |t|) + c * t) := by rw [mul_assoc, ← Real.exp_add]
    _ ≤ C * Real.exp (-|t|) := by
        refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hC0
        have : c * t ≤ |c| * |t| := by rw [← abs_mul]; exact le_abs_self _
        linarith

private theorem integral_riemannKernelReal_mul_exp_eq (k : ℝ) :
    ∫ t : ℝ, _root_.RHTower.riemannKernelReal t * Real.exp ((1 / 2 + k) * t) =
      (_root_.RHTower.riemannPhiTransform ((1 + k : ℝ) : ℂ)).re := by
  have hcx : ((∫ t : ℝ, _root_.RHTower.riemannKernelReal t * Real.exp ((1 / 2 + k) * t) : ℝ) : ℂ) =
      _root_.RHTower.riemannPhiTransform ((1 + k : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    unfold _root_.RHTower.riemannPhiTransform
    congr 1; funext t
    rw [Complex.ofReal_mul, _root_.RHTower.riemannPhiKernel_eq_ofReal,
      show (((1 + k : ℝ) : ℂ) - 1 / 2) * (t : ℂ) = (((1 / 2 + k) * t : ℝ) : ℂ) by
        push_cast; ring,
      Complex.ofReal_exp, mul_comm]
  rw [← hcx, Complex.ofReal_re]

/-- By evenness of `truncatedRiemannKernelReal`, `shiftedPoleForm k (windowRiemannKernel A)`
is an exact square `2 (∫ Φ χ_{A/2}(t) e^{(1/2+k)t} dt)²` for all `k, A ∈ ℝ`. -/
theorem shiftedPoleForm_windowRiemannKernel_eq (k A : ℝ) :
    shiftedPoleForm k (windowRiemannKernel A) =
      2 * (∫ t : ℝ, _root_.RHTower.truncatedRiemannKernelReal (A / 2) t *
        Real.exp ((1 / 2 + k) * t)) ^ 2 := by
  set R := A / 2
  have hp : (∫ u : ℝ, windowRiemannKernel A u * Real.exp ((1 / 2 + k) * u)) =
      Real.exp (-(1 / 2 + k) * R) *
        ∫ t : ℝ, _root_.RHTower.truncatedRiemannKernelReal R t * Real.exp ((1 / 2 + k) * t) := by
    calc (∫ u : ℝ, windowRiemannKernel A u * Real.exp ((1 / 2 + k) * u))
        = ∫ u : ℝ, _root_.RHTower.truncatedRiemannKernelReal R (u + R) *
            Real.exp ((1 / 2 + k) * ((u + R) - R)) :=
          integral_congr_ae (Eventually.of_forall fun u => by
            dsimp only [windowRiemannKernel, R]; congr 1; congr 1; ring)
      _ = ∫ t : ℝ, _root_.RHTower.truncatedRiemannKernelReal R t *
            Real.exp ((1 / 2 + k) * (t - R)) :=
          integral_add_right_eq_self (μ := volume)
            (fun t => _root_.RHTower.truncatedRiemannKernelReal R t *
              Real.exp ((1 / 2 + k) * (t - R))) R
      _ = Real.exp (-(1 / 2 + k) * R) *
            ∫ t : ℝ, _root_.RHTower.truncatedRiemannKernelReal R t *
              Real.exp ((1 / 2 + k) * t) := by
          rw [← integral_const_mul]
          refine integral_congr_ae (Eventually.of_forall fun t => ?_)
          dsimp only
          rw [← mul_assoc, mul_comm (Real.exp (-(1 / 2 + k) * R)), mul_assoc, ← Real.exp_add]
          congr 1; congr 1; ring
  have hm : (∫ u : ℝ, windowRiemannKernel A u * Real.exp (-(1 / 2 + k) * u)) =
      Real.exp ((1 / 2 + k) * R) *
        ∫ t : ℝ, _root_.RHTower.truncatedRiemannKernelReal R t * Real.exp ((1 / 2 + k) * t) := by
    have hs := integral_add_right_eq_self (μ := volume)
      (fun t => _root_.RHTower.truncatedRiemannKernelReal R t *
        Real.exp (-(1 / 2 + k) * (t - R))) R
    have heven : ∀ t : ℝ, _root_.RHTower.truncatedRiemannKernelReal R (-t) =
        _root_.RHTower.truncatedRiemannKernelReal R t := fun t => by
      unfold _root_.RHTower.truncatedRiemannKernelReal _root_.RHTower.riemannKernelReal
        _root_.RHTower.bulkCutoff
      rw [abs_neg, show R - -t = R + t by ring, show R + -t = R - t by ring,
        mul_comm (Real.smoothTransition (R + t))]
    have hneg := integral_neg_eq_self (μ := volume) fun t =>
      _root_.RHTower.truncatedRiemannKernelReal R t * Real.exp ((1 / 2 + k) * t)
    have h1 : (∫ u : ℝ, windowRiemannKernel A u * Real.exp (-(1 / 2 + k) * u)) =
        Real.exp ((1 / 2 + k) * R) *
          ∫ t : ℝ, _root_.RHTower.truncatedRiemannKernelReal R t *
            Real.exp (-(1 / 2 + k) * t) := by
      calc (∫ u : ℝ, windowRiemannKernel A u * Real.exp (-(1 / 2 + k) * u))
          = ∫ u : ℝ, _root_.RHTower.truncatedRiemannKernelReal R (u + R) *
              Real.exp (-(1 / 2 + k) * ((u + R) - R)) :=
            integral_congr_ae (Eventually.of_forall fun u => by
              dsimp only [windowRiemannKernel, R]; congr 1; congr 1; ring)
        _ = ∫ t : ℝ, _root_.RHTower.truncatedRiemannKernelReal R t *
              Real.exp (-(1 / 2 + k) * (t - R)) := hs
        _ = Real.exp ((1 / 2 + k) * R) *
              ∫ t : ℝ, _root_.RHTower.truncatedRiemannKernelReal R t *
                Real.exp (-(1 / 2 + k) * t) := by
            rw [← integral_const_mul]
            refine integral_congr_ae (Eventually.of_forall fun t => ?_)
            dsimp only
            rw [← mul_assoc, mul_comm (Real.exp ((1 / 2 + k) * R)), mul_assoc, ← Real.exp_add]
            congr 1; congr 1; ring
    rw [h1, ← hneg]
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    dsimp only
    rw [heven t]; congr 1; congr 1; ring
  unfold shiftedPoleForm
  rw [hp, hm]
  have hexp : Real.exp (-(1 / 2 + k) * R) * Real.exp ((1 / 2 + k) * R) = 1 := by
    rw [← Real.exp_add, show -(1 / 2 + k) * R + (1 / 2 + k) * R = 0 by ring, Real.exp_zero]
  calc 2 * ((Real.exp (-(1 / 2 + k) * R) *
          ∫ t, _root_.RHTower.truncatedRiemannKernelReal R t * Real.exp ((1 / 2 + k) * t)) *
        (Real.exp ((1 / 2 + k) * R) *
          ∫ t, _root_.RHTower.truncatedRiemannKernelReal R t * Real.exp ((1 / 2 + k) * t)))
      = 2 * (Real.exp (-(1 / 2 + k) * R) * Real.exp ((1 / 2 + k) * R)) *
          (∫ t, _root_.RHTower.truncatedRiemannKernelReal R t * Real.exp ((1 / 2 + k) * t)) ^ 2 := by
        ring
    _ = 2 * (∫ t, _root_.RHTower.truncatedRiemannKernelReal R t *
          Real.exp ((1 / 2 + k) * t)) ^ 2 := by rw [hexp, mul_one]

theorem shiftedPoleForm_windowRiemannKernel_nonneg (k A : ℝ) :
    0 ≤ shiftedPoleForm k (windowRiemannKernel A) := by
  rw [shiftedPoleForm_windowRiemannKernel_eq]
  exact mul_nonneg zero_le_two (sq_nonneg _)

/-- Uniform upper bound `shiftedPoleForm k (windowRiemannKernel A) ≤ 2 ξ(1 + k)²` across all `A`. -/
theorem shiftedPoleForm_windowRiemannKernel_le (k A : ℝ) :
    shiftedPoleForm k (windowRiemannKernel A) ≤
      2 * ((_root_.RHTower.riemannPhiTransform ((1 + k : ℝ) : ℂ)).re) ^ 2 := by
  rw [shiftedPoleForm_windowRiemannKernel_eq, ← integral_riemannKernelReal_mul_exp_eq k]
  set R := A / 2
  have hint_tr : Integrable fun t : ℝ =>
      _root_.RHTower.truncatedRiemannKernelReal R t * Real.exp ((1 / 2 + k) * t) :=
    ((_root_.RHTower.continuous_truncatedRiemannKernelReal R).mul
      (by fun_prop : Continuous fun t : ℝ =>
        Real.exp ((1 / 2 + k) * t))).integrable_of_hasCompactSupport
      (_root_.RHTower.hasCompactSupport_truncatedRiemannKernelReal R).mul_right
  have hle : (∫ t : ℝ, _root_.RHTower.truncatedRiemannKernelReal R t * Real.exp ((1 / 2 + k) * t)) ≤
      ∫ t : ℝ, _root_.RHTower.riemannKernelReal t * Real.exp ((1 / 2 + k) * t) := by
    refine integral_mono hint_tr (integrable_riemannKernelReal_mul_exp (1 / 2 + k)) fun t => ?_
    dsimp only [_root_.RHTower.truncatedRiemannKernelReal]
    exact mul_le_mul_of_nonneg_right
      (mul_le_of_le_one_right (_root_.RHTower.riemannKernelReal_pos t).le
        (_root_.RHTower.bulkCutoff_le_one R t))
      (Real.exp_pos _).le
  have hnn : 0 ≤ ∫ t : ℝ,
      _root_.RHTower.truncatedRiemannKernelReal R t * Real.exp ((1 / 2 + k) * t) :=
    integral_nonneg fun t =>
      mul_nonneg (_root_.RHTower.truncatedRiemannKernelReal_nonneg R t) (Real.exp_pos _).le
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hnn hle 2) zero_le_two

private theorem exists_windowPoleForm_windowRiemannKernel_ge {δ : ℝ} (hδ : 0 < δ) :
    ∃ A₁ : ℝ, 0 ≤ A₁ ∧ ∀ A : ℝ, A₁ ≤ A → 1 / 2 - δ ≤ windowPoleForm (windowRiemannKernel A) := by
  obtain ⟨C, hC0, hC⟩ :=
    _root_.RHTower.exists_norm_riemannPhiKernel_le_exp (B := 2) (by norm_num)
  set E₀ := ∫ t : ℝ, Real.exp (-|t|)
  have hE₀ : 0 ≤ E₀ := integral_nonneg fun _ => (Real.exp_pos _).le
  set ε := min (1 / 4) (δ / 2)
  have hε : 0 < ε := lt_min (by norm_num) (by positivity)
  set A₁ := max 4 (2 * (2 * Real.log ((C * E₀ + 1) / ε) + 1))
  refine ⟨A₁, le_trans (by norm_num) (le_max_left _ _), fun A hA => ?_⟩
  have hA0 : 0 ≤ A := le_trans (by norm_num) ((le_max_left _ _).trans hA)
  have hH := isWindowTest_windowRiemannKernel hA0
  rw [← shiftedPoleForm_zero hH, shiftedPoleForm_windowRiemannKernel_eq, add_zero]
  set R := A / 2
  have hR_log : 2 * Real.log ((C * E₀ + 1) / ε) ≤ R - 1 := by
    have := (le_max_right _ _).trans hA; dsimp only [R]; linarith
  have hint_full := integrable_riemannKernelReal_mul_exp (1 / 2)
  have hint_tr : Integrable fun t : ℝ =>
      _root_.RHTower.truncatedRiemannKernelReal R t * Real.exp (1 / 2 * t) :=
    ((_root_.RHTower.continuous_truncatedRiemannKernelReal R).mul
      (by fun_prop : Continuous fun t : ℝ =>
        Real.exp (1 / 2 * t))).integrable_of_hasCompactSupport
      (_root_.RHTower.hasCompactSupport_truncatedRiemannKernelReal R).mul_right
  have hfull_val : (∫ t : ℝ, _root_.RHTower.riemannKernelReal t * Real.exp (1 / 2 * t)) = 1 / 2 := by
    have h := integral_riemannKernelReal_mul_exp_eq 0
    rw [add_zero, show ((1 + (0 : ℝ) : ℝ) : ℂ) = 1 by push_cast; ring,
      riemannPhiTransform_one] at h
    norm_num at h
    exact h
  have htail : (∫ t : ℝ, (_root_.RHTower.riemannKernelReal t -
        _root_.RHTower.truncatedRiemannKernelReal R t) * Real.exp (1 / 2 * t)) ≤ ε := by
    have hpt : ∀ t : ℝ, (_root_.RHTower.riemannKernelReal t -
          _root_.RHTower.truncatedRiemannKernelReal R t) * Real.exp (1 / 2 * t) ≤
        (C * Real.exp (-(1 / 2 * (R - 1)))) * Real.exp (-|t|) := fun t => by
      by_cases ht : |t| ≤ R - 1
      · unfold _root_.RHTower.truncatedRiemannKernelReal
        rw [_root_.RHTower.bulkCutoff_eq_one ht, mul_one, sub_self, zero_mul]
        exact mul_nonneg (mul_nonneg hC0 (Real.exp_pos _).le) (Real.exp_pos _).le
      · push Not at ht
        have hk_pos := (_root_.RHTower.riemannKernelReal_pos t).le
        have hnorm : _root_.RHTower.riemannKernelReal t = ‖_root_.RHTower.riemannPhiKernel t‖ := by
          rw [_root_.RHTower.riemannPhiKernel_eq_ofReal, Complex.norm_real,
            Real.norm_eq_abs, abs_of_nonneg hk_pos]
        have hdiff_le : _root_.RHTower.riemannKernelReal t -
            _root_.RHTower.truncatedRiemannKernelReal R t ≤ _root_.RHTower.riemannKernelReal t := by
          unfold _root_.RHTower.truncatedRiemannKernelReal
          linarith [mul_nonneg hk_pos (_root_.RHTower.bulkCutoff_nonneg R t)]
        calc (_root_.RHTower.riemannKernelReal t -
              _root_.RHTower.truncatedRiemannKernelReal R t) * Real.exp (1 / 2 * t)
            ≤ _root_.RHTower.riemannKernelReal t * Real.exp (1 / 2 * |t|) :=
              mul_le_mul hdiff_le
                (Real.exp_le_exp.mpr (by linarith [le_abs_self t]))
                (Real.exp_pos _).le hk_pos
          _ ≤ C * Real.exp (-(2 * |t|)) * Real.exp (1 / 2 * |t|) := by
              rw [hnorm]; exact mul_le_mul_of_nonneg_right (hC t) (Real.exp_pos _).le
          _ = C * Real.exp (-(1 / 2 * |t|)) * Real.exp (-|t|) := by
              rw [mul_assoc, ← Real.exp_add, mul_assoc, ← Real.exp_add]
              congr 1; congr 1; ring
          _ ≤ (C * Real.exp (-(1 / 2 * (R - 1)))) * Real.exp (-|t|) :=
              mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) hC0)
                (Real.exp_pos _).le
    have hint_diff : Integrable fun t : ℝ =>
        (_root_.RHTower.riemannKernelReal t -
          _root_.RHTower.truncatedRiemannKernelReal R t) * Real.exp (1 / 2 * t) := by
      have heq : (fun t : ℝ => (_root_.RHTower.riemannKernelReal t -
            _root_.RHTower.truncatedRiemannKernelReal R t) * Real.exp (1 / 2 * t)) =
          fun t => _root_.RHTower.riemannKernelReal t * Real.exp (1 / 2 * t) -
            _root_.RHTower.truncatedRiemannKernelReal R t * Real.exp (1 / 2 * t) := by
        funext t; ring
      rw [heq]; exact hint_full.sub hint_tr
    have hm := integral_mono hint_diff
      (_root_.RHTower.integrable_exp_neg_abs.const_mul (C * Real.exp (-(1 / 2 * (R - 1))))) hpt
    rw [integral_const_mul] at hm
    have hexp_le : Real.exp (-(1 / 2 * (R - 1))) ≤ ε / (C * E₀ + 1) := by
      have h1 : Real.log ((C * E₀ + 1) / ε) ≤ 1 / 2 * (R - 1) := by linarith
      have h2 := Real.exp_le_exp.mpr (neg_le_neg h1)
      rwa [Real.exp_neg (Real.log ((C * E₀ + 1) / ε)), Real.exp_log (by positivity), inv_div] at h2
    have hprod_le : C * Real.exp (-(1 / 2 * (R - 1))) * E₀ ≤ ε := by
      calc C * Real.exp (-(1 / 2 * (R - 1))) * E₀
          = (C * E₀) * Real.exp (-(1 / 2 * (R - 1))) := by ring
        _ ≤ (C * E₀ + 1) * (ε / (C * E₀ + 1)) :=
            mul_le_mul (by linarith) hexp_le (Real.exp_pos _).le (by positivity)
        _ = ε := mul_div_cancel₀ _ (by positivity)
    exact hm.trans hprod_le
  have hI_ge : 1 / 2 - ε ≤
      ∫ t : ℝ, _root_.RHTower.truncatedRiemannKernelReal R t * Real.exp (1 / 2 * t) := by
    have hsub : (∫ t : ℝ, (_root_.RHTower.riemannKernelReal t -
          _root_.RHTower.truncatedRiemannKernelReal R t) * Real.exp (1 / 2 * t)) =
        (∫ t : ℝ, _root_.RHTower.riemannKernelReal t * Real.exp (1 / 2 * t)) -
          ∫ t : ℝ, _root_.RHTower.truncatedRiemannKernelReal R t * Real.exp (1 / 2 * t) := by
      rw [← integral_sub hint_full hint_tr]
      exact integral_congr_ae (Eventually.of_forall fun t => by ring)
    linarith
  have hε_le1 : ε ≤ 1 / 4 := min_le_left _ _
  have hε_le2 : ε ≤ δ / 2 := min_le_right _ _
  have hsq : 1 / 2 - 2 * ε ≤ 2 * (1 / 2 - ε) ^ 2 := by nlinarith [sq_nonneg ε]
  have hpow : (1 / 2 - ε) ^ 2 ≤
      (∫ t : ℝ, _root_.RHTower.truncatedRiemannKernelReal R t * Real.exp (1 / 2 * t)) ^ 2 :=
    pow_le_pow_left₀ (by linarith) hI_ge 2
  linarith

private theorem mul_archWindowForm_sub_tatePointCount_le_mul_weilQuad_of_nonneg
    {A k : ℝ} (hA : 0 ≤ A) (hk : 0 ≤ k) {H : ℝ → ℝ} (hH : IsWindowTest A H)
    (hpos : ∀ u, 0 ≤ H u) :
    k * archWindowForm H - tatePointCount A H k ≤ k * weilQuad H := by
  have h1 : 1 ≤ windowLevel A := one_le_windowLevel_of_nonneg hA
  have hset : Finset.Ioc 1 (windowLevel A) = Finset.Icc 2 (windowLevel A) := by
    ext n; simp only [Finset.mem_Ioc, Finset.mem_Icc]; omega
  have hvon : ∫ u, windowRepFun A ArithmeticFunction.vonMangoldt H u * H u =
      ∑ n ∈ Finset.Icc 2 (windowLevel A),
        ArithmeticFunction.vonMangoldt n / Real.sqrt n * ∫ u, H u * H (u + Real.log n) := by
    rw [integral_windowRep_vonMangoldt_eq_sum hH, ← Finset.sum_Ioc_add_eq_sum_Icc h1]
    simp only [ArithmeticFunction.vonMangoldt_apply_one, zero_div, zero_mul, add_zero, hset]
  have hge : 2 * k * ∫ u, windowRepFun A ArithmeticFunction.vonMangoldt H u * H u ≤
      tatePointCount A H k := by
    have hdiff : tatePointCount A H k -
        2 * k * ∫ u, windowRepFun A ArithmeticFunction.vonMangoldt H u * H u =
        2 * ∑ n ∈ Finset.Icc 2 (windowLevel A),
          (jordanTotient k n - k * ArithmeticFunction.vonMangoldt n) / Real.sqrt n *
            ∫ u, H u * H (u + Real.log n) := by
      have hmul : 2 * k * ∑ n ∈ Finset.Icc 2 (windowLevel A),
          ArithmeticFunction.vonMangoldt n / Real.sqrt n * (∫ u, H u * H (u + Real.log n)) =
          2 * ∑ n ∈ Finset.Icc 2 (windowLevel A),
            k * (ArithmeticFunction.vonMangoldt n / Real.sqrt n * ∫ u, H u * H (u + Real.log n)) := by
        rw [mul_assoc, Finset.mul_sum]
      rw [tatePointCount_eq_sum hA hH k, hvon, hmul, ← mul_sub, ← Finset.sum_sub_distrib]
      congr 1; refine Finset.sum_congr rfl fun _ _ => by ring
    have hnn : 0 ≤ 2 * ∑ n ∈ Finset.Icc 2 (windowLevel A),
        (jordanTotient k n - k * ArithmeticFunction.vonMangoldt n) / Real.sqrt n *
          ∫ u, H u * H (u + Real.log n) := by
      refine mul_nonneg zero_le_two (Finset.sum_nonneg fun n hn => ?_)
      have hn2 := (Finset.mem_Icc.mp hn).1
      have hJ : 0 ≤ jordanTotient k n - k * ArithmeticFunction.vonMangoldt n := by
        have ht := jordanTotient_ge_tangent hk n
        rw [if_neg (by omega : n ≠ 1), zero_add] at ht
        linarith
      exact mul_nonneg (div_nonneg hJ (Real.sqrt_nonneg _))
        (integral_nonneg fun u => mul_nonneg (hpos u) (hpos _))
    linarith
  have hQ : k * weilQuad H =
      k * archWindowForm H -
        2 * k * ∫ u, windowRepFun A ArithmeticFunction.vonMangoldt H u * H u := by
    rw [weilQuad_eq_archWindowForm_sub_vonMangoldt hH]; ring
  linarith

/-- On `windowRiemannKernel A`, `4 ξ(1 + k)² < k ζ(1 + k)` refutes every shifted-pole weight
`φ ≤ eulerProductPoleWeight k` for `0 < k ≤ 1`. -/
theorem not_forall_windowRiemannKernel_domination_of_le_eulerProduct {k φ : ℝ}
    (hk0 : 0 < k) (hk1 : k ≤ 1) (hφ : φ ≤ eulerProductPoleWeight k) :
    ¬ (∀ A : ℝ, 0 ≤ A →
        tatePointCount A (windowRiemannKernel A) k ≤
          k * archGammaForm (windowRiemannKernel A) +
            φ * shiftedPoleForm k (windowRiemannKernel A)) := by
  intro hdom
  have hprod := eulerProductPoleWeight_mul_zeta_eq_one hk0
  have hw_pos := eulerProductPoleWeight_pos hk0
  have hξ_lt : eulerProductPoleWeight k *
      (2 * ((_root_.RHTower.riemannPhiTransform ((1 + k : ℝ) : ℂ)).re) ^ 2) < k / 2 := by
    have h4 := four_mul_riemannPhiTransform_sq_lt_mul_zeta hk0 hk1
    have hmul := mul_lt_mul_of_pos_left h4 hw_pos
    have hrhs : eulerProductPoleWeight k * (k * (riemannZeta ((1 + k : ℝ) : ℂ)).re) = k := by
      calc eulerProductPoleWeight k * (k * (riemannZeta ((1 + k : ℝ) : ℂ)).re)
          = k * (eulerProductPoleWeight k * (riemannZeta ((1 + k : ℝ) : ℂ)).re) := by ring
        _ = k * 1 := by rw [hprod]
        _ = k := mul_one k
    rw [hrhs] at hmul
    linarith
  set η := k / 2 - eulerProductPoleWeight k *
    (2 * ((_root_.RHTower.riemannPhiTransform ((1 + k : ℝ) : ℂ)).re) ^ 2)
  have hη : 0 < η := sub_pos.mpr hξ_lt
  obtain ⟨A₁, hA₁, hpole⟩ := exists_windowPoleForm_windowRiemannKernel_ge
    (δ := η / (3 * k)) (by positivity)
  obtain ⟨A₂, C₀, hA₂, hC₀, hQ_bound⟩ := exists_weilQuad_windowRiemannKernel_le_doubleExp
  set A := max (max A₁ A₂) (Real.log (3 * k * (C₀ + 1) / η + 1) + 3)
  have hAA₁ : A₁ ≤ A := (le_max_left A₁ A₂).trans (le_max_left _ _)
  have hAA₂ : A₂ ≤ A := (le_max_right A₁ A₂).trans (le_max_left _ _)
  have hA_log : Real.log (3 * k * (C₀ + 1) / η + 1) + 3 ≤ A := le_max_right _ _
  have hA0 : 0 ≤ A := hA₁.trans hAA₁
  have hH := isWindowTest_windowRiemannKernel hA0
  have hd := hdom A hA0
  have hjet := mul_archWindowForm_sub_tatePointCount_le_mul_weilQuad_of_nonneg
    hA0 hk0.le hH (windowRiemannKernel_nonneg A)
  have hφ_le : φ * shiftedPoleForm k (windowRiemannKernel A) ≤ k / 2 - η := by
    calc φ * shiftedPoleForm k (windowRiemannKernel A)
        ≤ eulerProductPoleWeight k * shiftedPoleForm k (windowRiemannKernel A) :=
          mul_le_mul_of_nonneg_right hφ (shiftedPoleForm_windowRiemannKernel_nonneg k A)
      _ ≤ eulerProductPoleWeight k *
            (2 * ((_root_.RHTower.riemannPhiTransform ((1 + k : ℝ) : ℂ)).re) ^ 2) :=
          mul_le_mul_of_nonneg_left (shiftedPoleForm_windowRiemannKernel_le k A) hw_pos.le
      _ = k / 2 - η := by dsimp only [η]; ring
  have hkpole : k / 2 - η / 3 ≤ k * windowPoleForm (windowRiemannKernel A) := by
    have hp := mul_le_mul_of_nonneg_left (hpole A hAA₁) hk0.le
    have hmul : k * (1 / 2 - η / (3 * k)) = k / 2 - η / 3 := by
      field_simp [hk0.ne']
    rwa [hmul] at hp
  have hkQ : k * weilQuad (windowRiemannKernel A) < η / 3 := by
    have hQ := hQ_bound A hAA₂
    set X := Real.log (3 * k * (C₀ + 1) / η + 1)
    have hX_lt : X < Real.exp (A - 2) := by
      have hp1 : X + 1 ≤ A - 2 := by linarith
      have hp2 : X + 1 ≤ Real.exp (X + 1) := by linarith [Real.add_one_le_exp (X + 1)]
      exact (lt_add_one X).trans_le (hp2.trans (Real.exp_le_exp.mpr hp1))
    have hexp_gt : 3 * k * (C₀ + 1) / η + 1 < Real.exp (Real.exp (A - 2)) := by
      calc 3 * k * (C₀ + 1) / η + 1 = Real.exp X := (Real.exp_log (by positivity)).symm
        _ < Real.exp (Real.exp (A - 2)) := Real.exp_lt_exp.mpr hX_lt
    have hsmall : k * (C₀ + 1) * Real.exp (-Real.exp (A - 2)) < η / 3 := by
      rw [Real.exp_neg, ← div_eq_mul_inv, div_lt_iff₀ (Real.exp_pos _)]
      have h1 := (div_lt_iff₀ hη).mp
        (by linarith : 3 * k * (C₀ + 1) / η < Real.exp (Real.exp (A - 2)))
      linarith
    have hle : k * weilQuad (windowRiemannKernel A) ≤
        k * (C₀ + 1) * Real.exp (-Real.exp (A - 2)) := by
      calc k * weilQuad (windowRiemannKernel A)
          ≤ k * (C₀ * Real.exp (-Real.exp (A - 2))) :=
            mul_le_mul_of_nonneg_left hQ hk0.le
        _ ≤ k * ((C₀ + 1) * Real.exp (-Real.exp (A - 2))) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le) hk0.le
        _ = k * (C₀ + 1) * Real.exp (-Real.exp (A - 2)) := by ring
    exact hle.trans_lt hsmall
  rw [archWindowForm, mul_add] at hjet
  linarith

theorem not_forall_window_domination_of_le_eulerProduct {k φ : ℝ}
    (hk0 : 0 < k) (hk1 : k ≤ 1) (hφ : φ ≤ eulerProductPoleWeight k) :
    ¬ (∀ A : ℝ, 0 ≤ A → ∀ H : ℝ → ℝ, IsWindowTest A H →
        tatePointCount A H k ≤ k * archGammaForm H + φ * shiftedPoleForm k H) := by
  intro hdom
  exact not_forall_windowRiemannKernel_domination_of_le_eulerProduct hk0 hk1 hφ fun A hA =>
    hdom A hA (windowRiemannKernel A) (isWindowTest_windowRiemannKernel hA)

/-- **Complete shifted-pole impossibility for `k · archGammaForm` (`0 < k < 1`)**: for every
dimension `k ∈ (0, 1)`, NO scalar `φ ∈ ℝ` allows `k · archGammaForm H + φ · shiftedPoleForm k H`
to dominate `tatePointCount A H k` across all windows `{W_A}_{A ≥ 0}`. -/
theorem not_exists_shiftedPole_weight_domination_linear {k : ℝ} (hk0 : 0 < k) (hk1 : k < 1) :
    ¬ ∃ φ : ℝ, ∀ A : ℝ, 0 ≤ A → ∀ H : ℝ → ℝ, IsWindowTest A H →
        tatePointCount A H k ≤ k * archGammaForm H + φ * shiftedPoleForm k H := by
  rintro ⟨φ, hdom⟩
  have hpinch : φ = eulerProductPoleWeight k :=
    shiftedPole_weight_pinched_eq_eulerProduct hk0 hk1 (α := k) (β := 0) (φ := φ) fun A hA H hH => by
      simpa using hdom A hA H hH
  exact not_forall_window_domination_of_le_eulerProduct hk0 hk1.le hpinch.le hdom

/-- **Complete shifted-pole impossibility for `backwardTateGammaForm` (`0 < k ≤ 1 / 4`)**: NO
scalar `φ ∈ ℝ` allows `backwardTateGammaForm k H + φ · shiftedPoleForm k H` to dominate
`tatePointCount A H k` across all windows `{W_A}_{A ≥ 0}`. -/
theorem not_exists_shiftedPole_weight_domination_backwardTateGamma {k : ℝ}
    (hk0 : 0 < k) (hk4 : k ≤ 1 / 4) :
    ¬ ∃ φ : ℝ, ∀ A : ℝ, 0 ≤ A → ∀ H : ℝ → ℝ, IsWindowTest A H →
        tatePointCount A H k ≤ backwardTateGammaForm k H + φ * shiftedPoleForm k H := by
  rintro ⟨φ, hdom⟩
  have hpinch := shiftedPole_weight_pinched_backwardTateGamma hk0 hk4 hdom
  refine not_forall_windowRiemannKernel_domination_of_le_eulerProduct hk0 (by linarith) hpinch.le ?_
  intro A hA
  have h1 := hdom A hA (windowRiemannKernel A) (isWindowTest_windowRiemannKernel hA)
  have h2 := backwardTateGammaForm_le_mul_archGammaForm_of_nonneg (windowRiemannKernel_nonneg A) k
  linarith

/-- **Complete shifted-pole impossibility for `symTateGammaForm` (`0 < k ≤ 1 / 4`)**: NO
scalar `φ ∈ ℝ` allows `symTateGammaForm k H + φ · shiftedPoleForm k H` to dominate
`tatePointCount A H k` across all windows `{W_A}_{A ≥ 0}`. -/
theorem not_exists_shiftedPole_weight_domination_symTateGamma {k : ℝ}
    (hk0 : 0 < k) (hk4 : k ≤ 1 / 4) :
    ¬ ∃ φ : ℝ, ∀ A : ℝ, 0 ≤ A → ∀ H : ℝ → ℝ, IsWindowTest A H →
        tatePointCount A H k ≤ symTateGammaForm k H + φ * shiftedPoleForm k H := by
  rintro ⟨φ, hdom⟩
  have hpinch := shiftedPole_weight_pinched_symTateGamma hk0 hk4 hdom
  refine not_forall_windowRiemannKernel_domination_of_le_eulerProduct hk0 (by linarith) hpinch.le ?_
  intro A hA
  have h1 := hdom A hA (windowRiemannKernel A) (isWindowTest_windowRiemannKernel hA)
  have h2 := symTateGammaForm_le_mul_archGammaForm_of_nonneg (windowRiemannKernel_nonneg A) hk0.le
  linarith

end GaloisForLFunctions.ArchimedeanTateDomination

#print axioms GaloisForLFunctions.ArchimedeanTateDomination.abs_tatePointCount_sub_eulerProduct_shiftedPoleForm_le
#print axioms GaloisForLFunctions.ArchimedeanTateDomination.shiftedPole_weight_pinched_eq_eulerProduct
#print axioms GaloisForLFunctions.ArchimedeanTateDomination.not_exists_shiftedPole_weight_domination_linear
#print axioms GaloisForLFunctions.ArchimedeanTateDomination.not_exists_shiftedPole_weight_domination_backwardTateGamma
#print axioms GaloisForLFunctions.ArchimedeanTateDomination.not_exists_shiftedPole_weight_domination_symTateGamma
