import GaloisForLFunctions.RHTower.RiemannKernelCuspSeries
import GaloisForLFunctions.HTGeometry.PolynomialExtrapolationRemez


/-!
# Tail and bulk bounds for cusp series with a bulk-normalized polynomial

Let `Y₀ = e^{2u₀} ≥ 40`, let `R` be a real polynomial of degree at most `k` with
`k + 1 ≤ Y₀/10`, and let `M` be the maximum of `|R|` on the bulk interval `[Y₀/8, Y₀/4]`.

* **Tail** (`cuspSeries_tail_weighted_le`): for `u ≥ u₀`,
  `(|S_R(u)| + |S_{DR}(u)|) e^{u/2} ≤ M · 28k(16e)^k Y₀² e^{-πY₀} · e^{-u}`.  Lagrange extrapolation
  from `[Y₀/8, Y₀/4]` costs only `(16e y/Y₀)^k`, which the factor `e^{-πy}` absorbs.
* **Bulk** (`cuspSeries_bulk_ge`): on the window where `e^{2u} ∈ (Y₀/8, Y₀/4)`,
  `∫ S_R² ≥ M² e^{-πY₀/2}/(176(8e)^{2k})`.  A Remez inequality in the chart `u ↦ e^{2u}` leaves a set
  of measure at least `1/11` where `|R(e^{2u})| ≥ M/(2(8e)^k)`, and there the terms `n ≥ 2` of the
  series are smaller than half the leading term.

The ratio of the two is `(128e²)^{2k} e^{-3πY₀/2}` up to polynomial factors, super-exponentially small
in `Y₀` when `k ≤ Y₀/10`.
-/

open Complex MeasureTheory Filter Topology Set Polynomial
open scoped Real

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry

/-! ## Polynomial bounds past the bulk interval `[Y₀/8, Y₀/4]` -/

theorem exp_one_mul_128_sq_le : 128 * Real.exp 1 ^ 2 ≤ Real.exp 7 := by
  have h5 : (128 : ℝ) ≤ Real.exp 5 := by
    have := Real.exp_one_gt_d9
    have h : Real.exp 5 = Real.exp 1 ^ 5 := by rw [← Real.exp_nat_mul]; norm_num
    rw [h]; nlinarith [pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2.7182818283) this.le 5]
  have : Real.exp 7 = Real.exp 5 * Real.exp 1 ^ 2 := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num
  rw [this]
  exact mul_le_mul_of_nonneg_right h5 (by positivity)

/-- Past the bulk interval: `|R(y)| ≤ M(16ey/Y₀)^k` and `|DR(y)| ≤ 13 k y M(16ey/Y₀)^k`. -/
theorem abs_eval_cusp_le_of_bulk {k : ℕ} (hk : 1 ≤ k) (R : ℝ[X]) (hdeg : R.natDegree ≤ k)
    {Y₀ M : ℝ} (hY₀ : 8 ≤ Y₀) (hM : ∀ t ∈ Icc (Y₀ / 8) (Y₀ / 4), |R.eval t| ≤ M) {y : ℝ}
    (hy : Y₀ / 4 ≤ y) :
    |R.eval y| ≤ M * (16 * Real.exp 1 * y / Y₀) ^ k ∧
      |(cuspDeriv R).eval y| ≤ 13 * k * y * (M * (16 * Real.exp 1 * y / Y₀) ^ k) := by
  have hαβ : Y₀ / 8 < Y₀ / 4 := by linarith
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM (Y₀ / 8) ⟨le_rfl, hαβ.le⟩)
  have hy1 : 1 ≤ y := by linarith
  have hYpos : 0 < Y₀ := by linarith
  have hya : 0 < y - Y₀ / 8 := by linarith
  have hratio : 2 * Real.exp 1 * (y - Y₀ / 8) / (Y₀ / 4 - Y₀ / 8) ≤ 16 * Real.exp 1 * y / Y₀ := by
    rw [show Y₀ / 4 - Y₀ / 8 = Y₀ / 8 by ring, div_le_div_iff₀ (by linarith) hYpos]
    nlinarith [mul_pos (Real.exp_pos 1) (mul_pos hYpos hYpos)]
  have hr0 : 0 ≤ 2 * Real.exp 1 * (y - Y₀ / 8) / (Y₀ / 4 - Y₀ / 8) := by
    apply div_nonneg _ (by linarith); nlinarith [Real.exp_pos 1]
  have hpow : (2 * Real.exp 1 * (y - Y₀ / 8) / (Y₀ / 4 - Y₀ / 8)) ^ k ≤
      (16 * Real.exp 1 * y / Y₀) ^ k := pow_le_pow_left₀ hr0 hratio k
  have h1 := abs_eval_le_extrapolate R hdeg hαβ hM hy
  have h2 := abs_eval_derivative_le_extrapolate R hdeg hαβ hM hy
  have hR : |R.eval y| ≤ M * (16 * Real.exp 1 * y / Y₀) ^ k :=
    h1.trans (mul_le_mul_of_nonneg_left hpow hM0)
  have hQ0 : 0 ≤ M * (16 * Real.exp 1 * y / Y₀) ^ k := by
    have : 0 ≤ 16 * Real.exp 1 * y / Y₀ := by positivity
    positivity
  have hyR' : y * |(derivative R).eval y| ≤ 2 * k * (M * (16 * Real.exp 1 * y / Y₀) ^ k) := by
    have hyy : y * (k / (y - Y₀ / 8)) ≤ 2 * k := by
      rw [mul_div_assoc', div_le_iff₀ hya]
      have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      nlinarith
    calc y * |(derivative R).eval y|
        ≤ y * (M * (k / (y - Y₀ / 8)) *
            (2 * Real.exp 1 * (y - Y₀ / 8) / (Y₀ / 4 - Y₀ / 8)) ^ k) :=
          mul_le_mul_of_nonneg_left h2 (by linarith)
      _ = (y * (k / (y - Y₀ / 8))) * (M *
            (2 * Real.exp 1 * (y - Y₀ / 8) / (Y₀ / 4 - Y₀ / 8)) ^ k) := by ring
      _ ≤ (2 * k) * (M * (16 * Real.exp 1 * y / Y₀) ^ k) := by
          apply mul_le_mul hyy (mul_le_mul_of_nonneg_left hpow hM0) (by positivity)
            (by positivity)
  refine ⟨hR, ?_⟩
  have hD : (cuspDeriv R).eval y = R.eval y / 2 + 2 * y * (derivative R).eval y -
      2 * π * y * R.eval y := by
    simp [cuspDeriv]; ring
  rw [hD]
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hpi : π ≤ 4 := by linarith [Real.pi_lt_four]
  calc |R.eval y / 2 + 2 * y * (derivative R).eval y - 2 * π * y * R.eval y|
      ≤ |R.eval y| / 2 + 2 * (y * |(derivative R).eval y|) + 2 * π * y * |R.eval y| := by
        have hy0 : (0 : ℝ) < y := by linarith
        have e1 := abs_sub (R.eval y / 2 + 2 * y * (derivative R).eval y) (2 * π * y * R.eval y)
        have e2 := abs_add_le (R.eval y / 2) (2 * y * (derivative R).eval y)
        have e3 : |R.eval y / 2| = |R.eval y| / 2 := by rw [abs_div, abs_two]
        have e4 : |2 * y * (derivative R).eval y| = 2 * (y * |(derivative R).eval y|) := by
          rw [abs_mul, abs_mul, abs_two, abs_of_pos hy0]; ring
        have e5 : |2 * π * y * R.eval y| = 2 * π * y * |R.eval y| := by
          rw [abs_mul, abs_mul, abs_mul, abs_two, abs_of_pos Real.pi_pos, abs_of_pos hy0]
        linarith
    _ ≤ (M * (16 * Real.exp 1 * y / Y₀) ^ k) / 2 + 2 * (2 * k * (M * (16 * Real.exp 1 * y / Y₀) ^ k)) +
          2 * π * y * (M * (16 * Real.exp 1 * y / Y₀) ^ k) := by
        gcongr
    _ ≤ 13 * k * y * (M * (16 * Real.exp 1 * y / Y₀) ^ k) := by
        have hky : 1 ≤ (k : ℝ) * y := by nlinarith
        nlinarith [mul_nonneg hQ0 (by linarith : (0:ℝ) ≤ (k : ℝ) * y - 1),
          mul_nonneg hQ0 (by nlinarith : (0:ℝ) ≤ 4 * (k : ℝ) * y - 4 * k),
          mul_nonneg hQ0 (by nlinarith : (0:ℝ) ≤ 8 * (k:ℝ) * y - 2 * π * y)]


/-- The tail profile: for `y ≥ Y₀` and `k + 1 ≤ Y₀/10`,
`(16ey/Y₀)^k y e^{-πy} ≤ (16e)^k Y₀ e^{-πY₀} e^{-3(y-Y₀)}`. -/
theorem tail_profile_le {k : ℕ} {Y₀ y : ℝ} (hY₀ : 0 < Y₀) (hk : (k : ℝ) + 1 ≤ Y₀ / 10)
    (hy : Y₀ ≤ y) :
    (16 * Real.exp 1 * y / Y₀) ^ k * y * Real.exp (-π * y) ≤
      (16 * Real.exp 1) ^ k * Y₀ * Real.exp (-π * Y₀) * Real.exp (-3 * (y - Y₀)) := by
  set x := y / Y₀ with hx
  have hx1 : 1 ≤ x := by rw [hx, le_div_iff₀ hY₀]; linarith
  have hyx : y = Y₀ * x := by rw [hx]; field_simp
  have hxe : x ≤ Real.exp (x - 1) := by linarith [Real.add_one_le_exp (x - 1)]
  have hxpow : x ^ (k + 1) ≤ Real.exp ((k + 1) * (x - 1)) := by
    calc x ^ (k + 1) ≤ Real.exp (x - 1) ^ (k + 1) := pow_le_pow_left₀ (by linarith) hxe _
      _ = Real.exp ((k + 1) * (x - 1)) := by rw [← Real.exp_nat_mul]; push_cast; ring_nf
  have hexp1 : (k + 1) * (x - 1) ≤ (y - Y₀) / 10 := by
    have : (k + 1 : ℝ) * (x - 1) = ((k : ℝ) + 1) * (y - Y₀) / Y₀ := by
      rw [hyx]; field_simp
    rw [this, div_le_div_iff₀ hY₀ (by norm_num)]
    have hyY : 0 ≤ y - Y₀ := by linarith
    nlinarith
  have hsplit : (16 * Real.exp 1 * y / Y₀) ^ k * y = (16 * Real.exp 1) ^ k * Y₀ * x ^ (k + 1) := by
    rw [mul_div_assoc, mul_pow, ← hx, hyx, pow_succ]; ring
  rw [hsplit]
  have hE : Real.exp (-π * y) = Real.exp (-π * Y₀) * Real.exp (-π * (y - Y₀)) := by
    rw [← Real.exp_add]; ring_nf
  rw [hE]
  have hA : 0 ≤ (16 * Real.exp 1) ^ k * Y₀ * Real.exp (-π * Y₀) := by positivity
  calc (16 * Real.exp 1) ^ k * Y₀ * x ^ (k + 1) * (Real.exp (-π * Y₀) * Real.exp (-π * (y - Y₀)))
      = (16 * Real.exp 1) ^ k * Y₀ * Real.exp (-π * Y₀) * (x ^ (k + 1) *
          Real.exp (-π * (y - Y₀))) := by ring
    _ ≤ (16 * Real.exp 1) ^ k * Y₀ * Real.exp (-π * Y₀) * (Real.exp ((y - Y₀) / 10) *
          Real.exp (-π * (y - Y₀))) := by
        gcongr
        exact hxpow.trans (Real.exp_le_exp.mpr hexp1)
    _ ≤ (16 * Real.exp 1) ^ k * Y₀ * Real.exp (-π * Y₀) * Real.exp (-3 * (y - Y₀)) := by
        gcongr
        rw [← Real.exp_add]
        apply Real.exp_le_exp.mpr
        have : 0 ≤ y - Y₀ := by linarith
        nlinarith [Real.pi_gt_d2]

theorem tsum_exp_neg_three_mul_le : ∑' n : ℕ, Real.exp (-3 * n) ≤ 2 := by
  have hr : Real.exp (-3) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
  have hr0 : 0 ≤ Real.exp (-3) := (Real.exp_pos _).le
  have h := tsum_geometric_of_lt_one hr0 hr
  have heq : (fun n : ℕ => Real.exp (-3 * n)) = fun n : ℕ => Real.exp (-3) ^ n := by
    funext n; rw [← Real.exp_nat_mul]; ring_nf
  rw [heq, h]
  have : Real.exp (-3) ≤ 1 / 2 := by
    have : 2 ≤ Real.exp 3 := by linarith [Real.add_one_le_exp 3]
    rw [Real.exp_neg]; exact inv_le_of_inv_le₀ (by norm_num) (by linarith)
  rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith

theorem summable_exp_neg_three_mul : Summable fun n : ℕ => Real.exp (-3 * n) := by
  have hr : Real.exp (-3) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
  refine (summable_geometric_of_lt_one (Real.exp_pos _).le hr).congr fun n => ?_
  rw [← Real.exp_nat_mul]; ring_nf

/-- **Cusp tail.**  If `|R| ≤ M` on `[Y₀/8, Y₀/4]`, `deg R ≤ k`, and `k + 1 ≤ Y₀/10`, then for
`e^{2u} ≥ Y₀`: `|S_R(u)| + |S_{DR}(u)| ≤ 28 k M (16e)^k Y₀ e^{-πY₀} e^{u/2} e^{-3(e^{2u}-Y₀)}`. -/
theorem cuspSeries_tail_le {k : ℕ} (hk : 1 ≤ k) (R : ℝ[X]) (hdeg : R.natDegree ≤ k)
    {Y₀ M : ℝ} (hY₀ : 8 ≤ Y₀) (hkY : (k : ℝ) + 1 ≤ Y₀ / 10)
    (hM : ∀ t ∈ Icc (Y₀ / 8) (Y₀ / 4), |R.eval t| ≤ M) {u : ℝ} (hu : Y₀ ≤ Real.exp (2 * u)) :
    |cuspSeries R u| + |cuspSeries (cuspDeriv R) u| ≤
      28 * k * M * (16 * Real.exp 1) ^ k * Y₀ * Real.exp (-π * Y₀) * Real.exp (u / 2) *
        Real.exp (-3 * (Real.exp (2 * u) - Y₀)) := by
  set Y := Real.exp (2 * u) with hYdef
  have hY1 : 1 ≤ Y := by linarith
  have hYpos : 0 < Y₀ := by linarith
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM (Y₀ / 8) ⟨le_rfl, by linarith⟩)
  set c : ℝ := 14 * k * M * (16 * Real.exp 1) ^ k * Y₀ * Real.exp (-π * Y₀) * Real.exp (u / 2) *
    Real.exp (-3 * (Y - Y₀)) with hc
  have hterm : ∀ n : ℕ, |cuspTerm R (n + 1) u| + |cuspTerm (cuspDeriv R) (n + 1) u| ≤
      c * Real.exp (-3 * n) := by
    intro n
    set m : ℝ := ((n + 1 : ℕ) : ℝ) with hm
    have hm1 : 1 ≤ m := by rw [hm]; exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
    set y := m ^ 2 * Y with hy
    have hm2 : (1 : ℝ) ≤ m ^ 2 := by nlinarith
    have hyY : Y ≤ y := by rw [hy]; nlinarith
    have hyY₀ : Y₀ ≤ y := le_trans hu hyY
    obtain ⟨h1, h2⟩ := abs_eval_cusp_le_of_bulk hk R hdeg hY₀ hM (y := y) (by linarith)
    have hQ0 : 0 ≤ M * (16 * Real.exp 1 * y / Y₀) ^ k := by
      have : 0 ≤ 16 * Real.exp 1 * y / Y₀ := by
        apply div_nonneg _ hYpos.le; nlinarith [Real.exp_pos 1]
      positivity
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
    have hsum : |R.eval y| + |(cuspDeriv R).eval y| ≤
        14 * k * (M * ((16 * Real.exp 1 * y / Y₀) ^ k * y)) := by
      have : 1 ≤ (k : ℝ) * y := by nlinarith
      nlinarith [mul_nonneg hQ0 (by linarith : (0:ℝ) ≤ (k : ℝ) * y - 1)]
    have hprof := tail_profile_le (k := k) hYpos hkY hyY₀
    have hgap : Real.exp (-3 * (y - Y₀)) ≤ Real.exp (-3 * (Y - Y₀)) * Real.exp (-3 * n) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hn : (n : ℝ) ≤ (m ^ 2 - 1) * Y := by
        have : (n : ℝ) = m - 1 := by rw [hm]; push_cast; ring
        rw [this]; nlinarith
      rw [hy]; nlinarith
    unfold cuspTerm
    rw [← hy]
    rw [abs_mul, abs_mul, abs_of_pos (Real.exp_pos _), abs_of_pos (Real.exp_pos _),
      abs_mul, abs_mul, abs_of_pos (Real.exp_pos (u / 2)), abs_of_pos (Real.exp_pos (-π * y))]
    have hEu := Real.exp_pos (u / 2)
    have hEy := Real.exp_pos (-π * y)
    calc Real.exp (u / 2) * |R.eval y| * Real.exp (-π * y) +
          Real.exp (u / 2) * |(cuspDeriv R).eval y| * Real.exp (-π * y)
        = Real.exp (u / 2) * (|R.eval y| + |(cuspDeriv R).eval y|) * Real.exp (-π * y) := by ring
      _ ≤ Real.exp (u / 2) * (14 * k * (M * ((16 * Real.exp 1 * y / Y₀) ^ k * y))) *
          Real.exp (-π * y) := by gcongr
      _ = 14 * k * M * Real.exp (u / 2) *
          ((16 * Real.exp 1 * y / Y₀) ^ k * y * Real.exp (-π * y)) := by ring
      _ ≤ 14 * k * M * Real.exp (u / 2) *
          ((16 * Real.exp 1) ^ k * Y₀ * Real.exp (-π * Y₀) * Real.exp (-3 * (y - Y₀))) := by
        gcongr
      _ ≤ 14 * k * M * Real.exp (u / 2) *
          ((16 * Real.exp 1) ^ k * Y₀ * Real.exp (-π * Y₀) *
            (Real.exp (-3 * (Y - Y₀)) * Real.exp (-3 * n))) := by gcongr
      _ = c * Real.exp (-3 * n) := by rw [hc]; ring
  have hsR := summable_cuspTerm R u
  have hsD := summable_cuspTerm (cuspDeriv R) u
  have hc0 : 0 ≤ c := by rw [hc]; positivity
  have hbound : ∑' n : ℕ, (|cuspTerm R (n + 1) u| + |cuspTerm (cuspDeriv R) (n + 1) u|) ≤ 2 * c := by
    refine (Summable.tsum_le_tsum hterm (hsR.abs.add hsD.abs)
      (summable_exp_neg_three_mul.mul_left c)).trans ?_
    rw [tsum_mul_left]
    nlinarith [tsum_exp_neg_three_mul_le]
  have habs : |cuspSeries R u| + |cuspSeries (cuspDeriv R) u| ≤
      ∑' n : ℕ, (|cuspTerm R (n + 1) u| + |cuspTerm (cuspDeriv R) (n + 1) u|) := by
    rw [hsR.abs.tsum_add hsD.abs]
    unfold cuspSeries
    have e1 : |∑' n : ℕ, cuspTerm R (n + 1) u| ≤ ∑' n : ℕ, |cuspTerm R (n + 1) u| := by
      rw [← Real.norm_eq_abs]
      refine (norm_tsum_le_tsum_norm hsR.norm).trans (le_of_eq ?_)
      simp_rw [Real.norm_eq_abs]
    have e2 : |∑' n : ℕ, cuspTerm (cuspDeriv R) (n + 1) u| ≤
        ∑' n : ℕ, |cuspTerm (cuspDeriv R) (n + 1) u| := by
      rw [← Real.norm_eq_abs]
      refine (norm_tsum_le_tsum_norm hsD.norm).trans (le_of_eq ?_)
      simp_rw [Real.norm_eq_abs]
    linarith
  refine habs.trans (hbound.trans (le_of_eq ?_))
  rw [hc]; ring

/-- **Weighted cusp tail.**  For `u ≥ u₀` with `Y₀ = e^{2u₀}`:
`(|S_R(u)| + |S_{DR}(u)|) e^{u/2} ≤ M · 28k(16e)^k Y₀² e^{-πY₀} · e^{-u}`. -/
theorem cuspSeries_tail_weighted_le {k : ℕ} (hk : 1 ≤ k) (R : ℝ[X]) (hdeg : R.natDegree ≤ k)
    {u₀ M : ℝ} (hY₀ : 8 ≤ Real.exp (2 * u₀)) (hkY : (k : ℝ) + 1 ≤ Real.exp (2 * u₀) / 10)
    (hM : ∀ t ∈ Icc (Real.exp (2 * u₀) / 8) (Real.exp (2 * u₀) / 4), |R.eval t| ≤ M)
    {u : ℝ} (hu : u₀ ≤ u) :
    (|cuspSeries R u| + |cuspSeries (cuspDeriv R) u|) * Real.exp (u / 2) ≤
      M * (28 * k * (16 * Real.exp 1) ^ k * Real.exp (2 * u₀) ^ 2 *
        Real.exp (-π * Real.exp (2 * u₀))) * Real.exp (-u) := by
  set Y₀ := Real.exp (2 * u₀) with hY₀def
  have hYu : Y₀ ≤ Real.exp (2 * u) := Real.exp_le_exp.mpr (by linarith)
  have h := cuspSeries_tail_le hk R hdeg hY₀ hkY hM hYu
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM (Y₀ / 8) ⟨le_rfl, by linarith⟩)
  have hkey : Real.exp (u / 2) * Real.exp (-3 * (Real.exp (2 * u) - Y₀)) * Real.exp (u / 2) ≤
      Y₀ * Real.exp (-u) := by
    set s := u - u₀ with hs
    have hs0 : 0 ≤ s := by linarith
    have hgrow : Y₀ * (1 + 2 * s) ≤ Real.exp (2 * u) := by
      have : Real.exp (2 * u) = Y₀ * Real.exp (2 * s) := by
        rw [hY₀def, ← Real.exp_add]; congr 1; rw [hs]; ring
      rw [this]
      exact mul_le_mul_of_nonneg_left (by linarith [Real.add_one_le_exp (2 * s)]) (by positivity)
    have hY1 : 1 ≤ Y₀ := by linarith
    rw [← Real.exp_add, ← Real.exp_add, hY₀def, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have : 2 * s ≤ Real.exp (2 * u) - Real.exp (2 * u₀) := by
      rw [← hY₀def]; nlinarith
    linarith
  calc (|cuspSeries R u| + |cuspSeries (cuspDeriv R) u|) * Real.exp (u / 2)
      ≤ (28 * k * M * (16 * Real.exp 1) ^ k * Y₀ * Real.exp (-π * Y₀) * Real.exp (u / 2) *
          Real.exp (-3 * (Real.exp (2 * u) - Y₀))) * Real.exp (u / 2) :=
        mul_le_mul_of_nonneg_right h (Real.exp_pos _).le
    _ = 28 * k * M * (16 * Real.exp 1) ^ k * Y₀ * Real.exp (-π * Y₀) *
          (Real.exp (u / 2) * Real.exp (-3 * (Real.exp (2 * u) - Y₀)) * Real.exp (u / 2)) := by
        ring
    _ ≤ 28 * k * M * (16 * Real.exp 1) ^ k * Y₀ * Real.exp (-π * Y₀) * (Y₀ * Real.exp (-u)) := by
        gcongr
    _ = _ := by ring


/-! ## The bulk lower bound -/

theorem tsum_exp_neg_nat_le_two : ∑' n : ℕ, Real.exp (-(n : ℝ)) ≤ 2 := by
  have hr : Real.exp (-1) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
  have h := tsum_geometric_of_lt_one (Real.exp_pos (-1)).le hr
  have heq : (fun n : ℕ => Real.exp (-(n : ℝ))) = fun n : ℕ => Real.exp (-1) ^ n := by
    funext n; rw [← Real.exp_nat_mul]; ring_nf
  rw [heq, h]
  have : Real.exp (-1) ≤ 1 / 2 := by
    have : 2 ≤ Real.exp 1 := by linarith [Real.add_one_le_exp 1]
    rw [Real.exp_neg]; exact inv_le_of_inv_le₀ (by norm_num) (by linarith)
  rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith

/-- The terms `n ≥ 2` of the cusp series on the bulk interval are of size
`2M(16e)^k e^{-πY₀/2} e^{u/2}`. -/
theorem cuspSeries_rest_le {k : ℕ} (hk : 1 ≤ k) (R : ℝ[X]) (hdeg : R.natDegree ≤ k)
    {Y₀ M : ℝ} (hY₀ : 8 ≤ Y₀) (hkY : (k : ℝ) + 1 ≤ Y₀ / 10)
    (hM : ∀ t ∈ Icc (Y₀ / 8) (Y₀ / 4), |R.eval t| ≤ M) {u : ℝ}
    (hu1 : Y₀ / 8 ≤ Real.exp (2 * u)) (hu2 : Real.exp (2 * u) ≤ Y₀ / 4) :
    |∑' n : ℕ, cuspTerm R (n + 2) u| ≤
      2 * M * (16 * Real.exp 1) ^ k * Real.exp (-π * Y₀ / 2) * Real.exp (u / 2) := by
  set Y := Real.exp (2 * u) with hYdef
  have hYpos : 0 < Y₀ := by linarith
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM (Y₀ / 8) ⟨le_rfl, by linarith⟩)
  set c := M * (16 * Real.exp 1) ^ k * Real.exp (-π * Y₀ / 2) * Real.exp (u / 2) with hc
  have hterm : ∀ n : ℕ, |cuspTerm R (n + 2) u| ≤ c * Real.exp (-(n : ℝ)) := by
    intro n
    set m : ℝ := ((n + 2 : ℕ) : ℝ) with hm
    have hm2 : 2 ≤ m := by rw [hm]; push_cast; linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]
    set y := m ^ 2 * Y with hy
    have hm4 : (4 : ℝ) ≤ m ^ 2 := by nlinarith
    have hY0 : 0 ≤ Y := (Real.exp_pos _).le
    have hy1 : Y₀ / 4 ≤ y := by
      rw [hy]; nlinarith [mul_le_mul_of_nonneg_right hm4 hY0]
    have hyu : y ≤ m ^ 2 * (Y₀ / 4) := by rw [hy]; nlinarith
    have hyl : m ^ 2 * (Y₀ / 8) ≤ y := by rw [hy]; nlinarith
    obtain ⟨h1, -⟩ := abs_eval_cusp_le_of_bulk hk R hdeg hY₀ hM hy1
    -- `(16ey/Y₀)^k ≤ (16e)^k ((m/2)^2)^k`
    have hq : 16 * Real.exp 1 * y / Y₀ ≤ 16 * Real.exp 1 * (m / 2) ^ 2 := by
      rw [div_le_iff₀ hYpos]; nlinarith [Real.exp_pos 1]
    have hq0 : 0 ≤ 16 * Real.exp 1 * y / Y₀ := by
      apply div_nonneg _ hYpos.le; nlinarith [Real.exp_pos 1]
    have hmhalf : ((m / 2) ^ 2) ^ k ≤ Real.exp (k * n) := by
      have hx : (m / 2) ^ 2 ≤ Real.exp (2 * (m / 2 - 1)) := by
        have h := Real.add_one_le_exp (m / 2 - 1)
        have h0 : 0 ≤ m / 2 := by linarith
        calc (m / 2) ^ 2 ≤ Real.exp (m / 2 - 1) ^ 2 := pow_le_pow_left₀ h0 (by linarith) 2
          _ = Real.exp (2 * (m / 2 - 1)) := by rw [← Real.exp_nat_mul]; norm_num
      calc ((m / 2) ^ 2) ^ k ≤ Real.exp (2 * (m / 2 - 1)) ^ k := pow_le_pow_left₀ (by positivity) hx k
        _ = Real.exp (k * n) := by
          rw [← Real.exp_nat_mul]; congr 1; rw [hm]; push_cast; ring
    have hexp : Real.exp (-π * y) ≤ Real.exp (-π * Y₀ / 2) * Real.exp (-(π * Y₀ / 2) * n) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have h4 : (4 : ℝ) + 4 * n ≤ m ^ 2 := by rw [hm]; push_cast; nlinarith
      have hyn : Y₀ / 2 + (Y₀ / 2) * n ≤ y := by
        have := mul_le_mul_of_nonneg_right h4 (by positivity : (0:ℝ) ≤ Y₀ / 8)
        linarith
      have := mul_le_mul_of_nonneg_left hyn Real.pi_pos.le
      linarith
    unfold cuspTerm
    rw [← hy, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _), abs_of_pos (Real.exp_pos _)]
    have hkn : Real.exp (k * n) * Real.exp (-(π * Y₀ / 2) * n) ≤ Real.exp (-(n : ℝ)) := by
      rw [← Real.exp_add]; apply Real.exp_le_exp.mpr
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      have : (k : ℝ) + 1 ≤ π * Y₀ / 2 := by nlinarith [Real.pi_gt_three]
      nlinarith
    calc Real.exp (u / 2) * |R.eval y| * Real.exp (-π * y)
        ≤ Real.exp (u / 2) * (M * (16 * Real.exp 1 * y / Y₀) ^ k) *
            (Real.exp (-π * Y₀ / 2) * Real.exp (-(π * Y₀ / 2) * n)) := by gcongr
      _ ≤ Real.exp (u / 2) * (M * ((16 * Real.exp 1) ^ k * ((m / 2) ^ 2) ^ k)) *
            (Real.exp (-π * Y₀ / 2) * Real.exp (-(π * Y₀ / 2) * n)) := by
          gcongr
          rw [← mul_pow]; exact pow_le_pow_left₀ hq0 hq k
      _ ≤ Real.exp (u / 2) * (M * ((16 * Real.exp 1) ^ k * Real.exp (k * n))) *
            (Real.exp (-π * Y₀ / 2) * Real.exp (-(π * Y₀ / 2) * n)) := by gcongr
      _ = c * (Real.exp (k * n) * Real.exp (-(π * Y₀ / 2) * n)) := by rw [hc]; ring
      _ ≤ c * Real.exp (-(n : ℝ)) := by
          have hc0 : 0 ≤ c := by rw [hc]; positivity
          exact mul_le_mul_of_nonneg_left hkn hc0
  have hs : Summable fun n : ℕ => cuspTerm R (n + 2) u :=
    (summable_nat_add_iff 1).mpr (summable_cuspTerm R u) |>.congr fun n => by ring_nf
  have hc0 : 0 ≤ c := by rw [hc]; positivity
  rw [← Real.norm_eq_abs]
  refine (norm_tsum_le_tsum_norm hs.norm).trans ?_
  simp_rw [Real.norm_eq_abs]
  refine (Summable.tsum_le_tsum hterm hs.abs (Real.summable_exp_neg_nat.mul_left c)).trans ?_
  rw [tsum_mul_left]
  have := tsum_exp_neg_nat_le_two
  calc c * ∑' n : ℕ, Real.exp (-(n : ℝ)) ≤ c * 2 := mul_le_mul_of_nonneg_left this hc0
    _ = _ := by rw [hc]; ring


theorem exp_two_mul_bulk_left (u₀ : ℝ) :
    Real.exp (2 * (u₀ - 3 / 2 * Real.log 2)) = Real.exp (2 * u₀) / 8 := by
  rw [show 2 * (u₀ - 3 / 2 * Real.log 2) = 2 * u₀ - 3 * Real.log 2 by ring, Real.exp_sub,
    show 3 * Real.log 2 = Real.log 8 by
      rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; norm_num,
    Real.exp_log (by norm_num)]

theorem exp_two_mul_bulk_right (u₀ : ℝ) :
    Real.exp (2 * (u₀ - Real.log 2)) = Real.exp (2 * u₀) / 4 := by
  rw [show 2 * (u₀ - Real.log 2) = 2 * u₀ - 2 * Real.log 2 by ring, Real.exp_sub,
    show 2 * Real.log 2 = Real.log 4 by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num,
    Real.exp_log (by norm_num)]

/-- Arithmetic: the terms `n ≥ 2` are at most half of the bulk threshold. -/
theorem bulk_rest_small {k : ℕ} {Y₀ M : ℝ} (hM0 : 0 ≤ M) (hY₀ : 40 ≤ Y₀)
    (hkY : (k : ℝ) + 1 ≤ Y₀ / 10) :
    2 * M * (16 * Real.exp 1) ^ k * Real.exp (-π * Y₀ / 2) ≤
      M / (2 * (8 * Real.exp 1) ^ k) * Real.exp (-π * Y₀ / 4) / 2 := by
  have h7 := exp_one_mul_128_sq_le
  have hpow : (16 * Real.exp 1) ^ k * (8 * Real.exp 1) ^ k ≤ Real.exp (7 * k) := by
    rw [← mul_pow, show 16 * Real.exp 1 * (8 * Real.exp 1) = 128 * Real.exp 1 ^ 2 by ring,
      show 7 * (k : ℝ) = k * 7 by ring, Real.exp_nat_mul]
    exact pow_le_pow_left₀ (by positivity) h7 k
  have h3 : (8 : ℝ) ≤ Real.exp 3 := by
    have h2 : Real.exp 3 = Real.exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
    have : 2.7 ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    rw [h2]; nlinarith
  have hbig : 8 * Real.exp (7 * k) ≤ Real.exp (π * Y₀ / 4) := by
    calc 8 * Real.exp (7 * k) ≤ Real.exp 3 * Real.exp (7 * k) :=
          mul_le_mul_of_nonneg_right h3 (Real.exp_pos _).le
      _ = Real.exp (3 + 7 * k) := by rw [← Real.exp_add]
      _ ≤ Real.exp (π * Y₀ / 4) := Real.exp_le_exp.mpr (by nlinarith [Real.pi_gt_three])
  have hsplitE : Real.exp (-π * Y₀ / 4) = Real.exp (π * Y₀ / 4) * Real.exp (-π * Y₀ / 2) := by
    rw [← Real.exp_add]; ring_nf
  have hpk : 0 < (8 * Real.exp 1) ^ k := by positivity
  have hE2 := Real.exp_pos (-π * Y₀ / 2)
  rw [hsplitE, div_mul_eq_mul_div, div_div, le_div_iff₀ (by positivity)]
  calc 2 * M * (16 * Real.exp 1) ^ k * Real.exp (-π * Y₀ / 2) * (2 * (8 * Real.exp 1) ^ k * 2)
      = 8 * M * Real.exp (-π * Y₀ / 2) * ((16 * Real.exp 1) ^ k * (8 * Real.exp 1) ^ k) := by
        ring
    _ ≤ 8 * M * Real.exp (-π * Y₀ / 2) * Real.exp (7 * k) := by gcongr
    _ = M * Real.exp (-π * Y₀ / 2) * (8 * Real.exp (7 * k)) := by ring
    _ ≤ M * Real.exp (-π * Y₀ / 2) * Real.exp (π * Y₀ / 4) := by gcongr
    _ = M * (Real.exp (π * Y₀ / 4) * Real.exp (-π * Y₀ / 2)) := by ring

/-- On the good set of the bulk window the cusp series is at least
`m₀ = M e^{-πY₀/4}/(4(8e)^k)`. -/
theorem abs_cuspSeries_ge_on_good {k : ℕ} (hk : 1 ≤ k) (R : ℝ[X]) (hdeg : R.natDegree ≤ k)
    {Y₀ M : ℝ} (hM0 : 0 ≤ M) (hY₀ : 40 ≤ Y₀) (hkY : (k : ℝ) + 1 ≤ Y₀ / 10)
    (hM : ∀ t ∈ Icc (Y₀ / 8) (Y₀ / 4), |R.eval t| ≤ M) {u : ℝ}
    (hu1 : Y₀ / 8 < Real.exp (2 * u)) (hu2 : Real.exp (2 * u) < Y₀ / 4)
    (hgood : M / (2 * (8 * Real.exp 1) ^ k) < |R.eval (Real.exp (2 * u))|) :
    M * Real.exp (-π * Y₀ / 4) / (4 * (8 * Real.exp 1) ^ k) ≤ |cuspSeries R u| := by
  set ε := M / (2 * (8 * Real.exp 1) ^ k) with hε
  have hupos : 0 ≤ u := by
    by_contra h; push Not at h
    have : Real.exp (2 * u) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    linarith
  have hsplit : cuspSeries R u = cuspTerm R 1 u + ∑' n : ℕ, cuspTerm R (n + 2) u := by
    unfold cuspSeries
    rw [(summable_cuspTerm R u).tsum_eq_zero_add]
  have hlead : cuspTerm R 1 u = Real.exp (u / 2) * R.eval (Real.exp (2 * u)) *
      Real.exp (-π * Real.exp (2 * u)) := by
    unfold cuspTerm; push_cast; ring_nf
  have hrest := cuspSeries_rest_le hk R hdeg (by linarith) hkY hM hu1.le hu2.le
  set A := ε * Real.exp (-π * Y₀ / 4) with hA
  have hA0 : 0 ≤ A := by rw [hA, hε]; positivity
  set X := Real.exp (u / 2) with hX
  have hX1 : 1 ≤ X := Real.one_le_exp (by linarith)
  have hlead_ge : X * A ≤ |cuspTerm R 1 u| := by
    rw [hlead, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _), abs_of_pos (Real.exp_pos _), hA,
      mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
    apply mul_le_mul hgood.le (Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos]))
      (Real.exp_pos _).le (abs_nonneg _)
  have hsmall := bulk_rest_small (k := k) hM0 hY₀ hkY
  rw [← hε] at hsmall
  have hrest' : |∑' n : ℕ, cuspTerm R (n + 2) u| ≤ X * (A / 2) := by
    refine hrest.trans ?_
    rw [hX, hA, mul_div_assoc']
    have := mul_le_mul_of_nonneg_right hsmall (Real.exp_pos (u / 2)).le
    linarith
  have htri : |cuspTerm R 1 u| ≤ |cuspSeries R u| + |∑' n : ℕ, cuspTerm R (n + 2) u| := by
    have := abs_sub (cuspTerm R 1 u + ∑' n : ℕ, cuspTerm R (n + 2) u)
      (∑' n : ℕ, cuspTerm R (n + 2) u)
    rw [add_sub_cancel_right] at this
    rw [hsplit]; exact this
  have hXA : X * A = 2 * (X * (A / 2)) := by ring
  have hAX : A / 2 ≤ X * (A / 2) := le_mul_of_one_le_left (by linarith) hX1
  have hm : M * Real.exp (-π * Y₀ / 4) / (4 * (8 * Real.exp 1) ^ k) = A / 2 := by
    rw [hA, hε]; field_simp; ring
  rw [hm]
  linarith

/-- The good set of the bulk window has measure at least `1/11`. -/
theorem volume_bulk_good_ge {k : ℕ} (R : ℝ[X]) (hdeg : R.natDegree ≤ k)
    {u₀ z M : ℝ} (hY₀ : 40 ≤ Real.exp (2 * u₀)) (hMpos : 0 < M)
    (hz : z ∈ Icc (Real.exp (2 * u₀) / 8) (Real.exp (2 * u₀) / 4)) (hzM : |R.eval z| = M) :
    1 / 11 ≤ (volume {u ∈ Ioo (u₀ - 3 / 2 * Real.log 2) (u₀ - Real.log 2) |
      M / (2 * (8 * Real.exp 1) ^ k) < |R.eval (Real.exp (2 * u))|}).toReal := by
  set Y₀ := Real.exp (2 * u₀) with hY₀def
  set p := u₀ - 3 / 2 * Real.log 2 with hp
  set q := u₀ - Real.log 2 with hq
  have hlog2 := Real.log_two_gt_d9
  have hYpos : 0 < Y₀ := by linarith
  have e8 : 0 < 8 * Real.exp 1 := by positivity
  set ε := M / (2 * (8 * Real.exp 1) ^ k) with hε
  have hexp_mem : ∀ u ∈ Ioo p q, Y₀ / 8 < Real.exp (2 * u) ∧ Real.exp (2 * u) < Y₀ / 4 := by
    intro u hu
    constructor
    · rw [← exp_two_mul_bulk_left u₀]; exact Real.exp_lt_exp.mpr (by linarith [hu.1])
    · rw [← exp_two_mul_bulk_right u₀]; exact Real.exp_lt_exp.mpr (by linarith [hu.2])
  have hremez := volume_sublevel_comp_le (k := k) R hdeg (g := fun u => Real.exp (2 * u))
    (a := p) (c := q) (lam := Y₀ / 4) (b := Y₀ / 8) (ε := ε) (q := 8 * Real.exp 1)
    (by positivity) (by positivity) e8
    (by
      intro u hu w hw huw
      have h1 := (hexp_mem u hu).1
      have hgrow : Real.exp (2 * u) * (1 + 2 * (w - u)) ≤ Real.exp (2 * w) := by
        have : Real.exp (2 * w) = Real.exp (2 * u) * Real.exp (2 * (w - u)) := by
          rw [← Real.exp_add]; ring_nf
        rw [this]
        exact mul_le_mul_of_nonneg_left (by linarith [Real.add_one_le_exp (2 * (w - u))])
          (Real.exp_pos _).le
      have hwu : 0 ≤ w - u := by linarith
      nlinarith)
    (z := z)
    (by
      intro u hu
      have h := hexp_mem u hu
      rw [abs_le]; constructor <;> linarith [hz.1, hz.2])
    (by
      rw [hzM, hε]
      have : 0 < (8 * Real.exp 1) ^ k := by positivity
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      nlinarith)
  have hremez' : (volume {u ∈ Ioo p q | |R.eval (Real.exp (2 * u))| ≤ ε}).toReal ≤ 1 / 4 := by
    refine hremez.trans (le_of_eq ?_)
    field_simp; ring
  set G := {u ∈ Ioo p q | ε < |R.eval (Real.exp (2 * u))|} with hG
  have hGsub : G ⊆ Ioo p q := fun u hu => hu.1
  have hcover : Ioo p q ⊆ G ∪ {u ∈ Ioo p q | |R.eval (Real.exp (2 * u))| ≤ ε} := by
    intro u hu
    by_cases h : ε < |R.eval (Real.exp (2 * u))|
    · exact Or.inl ⟨hu, h⟩
    · exact Or.inr ⟨hu, le_of_not_gt h⟩
  have h1 : volume (Ioo p q) ≤ volume G +
      volume {u ∈ Ioo p q | |R.eval (Real.exp (2 * u))| ≤ ε} :=
    (measure_mono hcover).trans (measure_union_le _ _)
  have hfinG : volume G ≠ ⊤ := ne_top_of_le_ne_top (by simp) (measure_mono hGsub)
  have hfinS : volume {u ∈ Ioo p q | |R.eval (Real.exp (2 * u))| ≤ ε} ≠ ⊤ :=
    ne_top_of_le_ne_top (by simp) (measure_mono fun u hu => hu.1)
  have h2 := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hfinG, hfinS⟩) h1
  have hpq : p < q := by rw [hp, hq]; linarith
  rw [ENNReal.toReal_add hfinG hfinS, Real.volume_Ioo, ENNReal.toReal_ofReal (by linarith)] at h2
  have : q - p = Real.log 2 / 2 := by rw [hp, hq]; ring
  rw [this] at h2
  linarith

/-- **Bulk lower bound.**  Let `Y₀ = e^{2u₀} ≥ 40`, `deg R ≤ k`, `k + 1 ≤ Y₀/10`, and let
`M = |R(z)|` be the maximum of `|R|` on `[Y₀/8, Y₀/4]`.  On the window
`u ∈ (u₀ - (3/2)log 2, u₀ - log 2)` (where `e^{2u} ∈ (Y₀/8, Y₀/4)`),
`∫ S_R² ≥ M² e^{-πY₀/2} / (176 (8e)^{2k})`.  Remez in the chart `e^{2u}` leaves a set of
measure `≥ 1/11` on which the leading term dominates the terms `n ≥ 2`. -/
theorem cuspSeries_bulk_ge {k : ℕ} (hk : 1 ≤ k) (R : ℝ[X]) (hdeg : R.natDegree ≤ k)
    {u₀ z M : ℝ} (hY₀ : 40 ≤ Real.exp (2 * u₀)) (hkY : (k : ℝ) + 1 ≤ Real.exp (2 * u₀) / 10)
    (hz : z ∈ Icc (Real.exp (2 * u₀) / 8) (Real.exp (2 * u₀) / 4)) (hzM : |R.eval z| = M)
    (hM : ∀ t ∈ Icc (Real.exp (2 * u₀) / 8) (Real.exp (2 * u₀) / 4), |R.eval t| ≤ M) :
    M ^ 2 * (Real.exp (-π * Real.exp (2 * u₀) / 2) / (176 * (8 * Real.exp 1) ^ (2 * k))) ≤
      ∫ u in Ioo (u₀ - 3 / 2 * Real.log 2) (u₀ - Real.log 2), (cuspSeries R u) ^ 2 := by
  set Y₀ := Real.exp (2 * u₀) with hY₀def
  set p := u₀ - 3 / 2 * Real.log 2 with hp
  set q := u₀ - Real.log 2 with hq
  have hM0 : 0 ≤ M := hzM ▸ abs_nonneg _
  have hint : IntegrableOn (fun u => (cuspSeries R u) ^ 2) (Ioo p q) :=
    ((continuous_cuspSeries R).pow 2).integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have hnonneg : 0 ≤ ∫ u in Ioo p q, (cuspSeries R u) ^ 2 :=
    setIntegral_nonneg measurableSet_Ioo fun u _ => sq_nonneg _
  rcases eq_or_lt_of_le hM0 with hM00 | hMpos
  · rw [← hM00]; simpa using hnonneg
  set ε := M / (2 * (8 * Real.exp 1) ^ k) with hε
  set G := {u ∈ Ioo p q | ε < |R.eval (Real.exp (2 * u))|} with hG
  have hGsub : G ⊆ Ioo p q := fun u hu => hu.1
  have hGmeas : MeasurableSet G := by
    have hc : Measurable fun u : ℝ => |R.eval (Real.exp (2 * u))| :=
      ((Polynomial.continuous R).comp (by fun_prop : Continuous fun u : ℝ =>
        Real.exp (2 * u))).abs.measurable
    exact measurableSet_Ioo.inter (measurableSet_lt (f := fun _ : ℝ => ε) measurable_const hc)
  have hvolG := volume_bulk_good_ge (k := k) R hdeg hY₀ hMpos hz hzM
  rw [← hε] at hvolG
  set m₀ := M * Real.exp (-π * Y₀ / 4) / (4 * (8 * Real.exp 1) ^ k) with hm₀
  have hm₀0 : 0 ≤ m₀ := by rw [hm₀]; positivity
  have hptw : ∀ u ∈ G, m₀ ^ 2 ≤ (cuspSeries R u) ^ 2 := by
    intro u hu
    have hmem1 : Y₀ / 8 < Real.exp (2 * u) := by
      rw [← exp_two_mul_bulk_left u₀]; exact Real.exp_lt_exp.mpr (by linarith [hu.1.1])
    have hmem2 : Real.exp (2 * u) < Y₀ / 4 := by
      rw [← exp_two_mul_bulk_right u₀]; exact Real.exp_lt_exp.mpr (by linarith [hu.1.2])
    have hge := abs_cuspSeries_ge_on_good hk R hdeg hM0 hY₀ hkY hM hmem1 hmem2 hu.2
    calc m₀ ^ 2 ≤ |cuspSeries R u| ^ 2 := pow_le_pow_left₀ hm₀0 hge 2
      _ = (cuspSeries R u) ^ 2 := sq_abs _
  have hG_le : ∫ u in G, (cuspSeries R u) ^ 2 ≤ ∫ u in Ioo p q, (cuspSeries R u) ^ 2 :=
    setIntegral_mono_set hint (Eventually.of_forall fun u => sq_nonneg _)
      (Eventually.of_forall hGsub)
  have hfin : volume G ≠ ⊤ := ne_top_of_le_ne_top (by simp) (measure_mono hGsub)
  have hG_ge : m₀ ^ 2 * (volume G).toReal ≤ ∫ u in G, (cuspSeries R u) ^ 2 := by
    have h := setIntegral_mono_on (μ := volume) (s := G) (f := fun _ => m₀ ^ 2)
      (g := fun u => (cuspSeries R u) ^ 2) (integrableOn_const hfin) (hint.mono_set hGsub)
      hGmeas hptw
    rw [setIntegral_const, smul_eq_mul, mul_comm, measureReal_def] at h
    exact h
  have hm2 : m₀ ^ 2 = M ^ 2 * Real.exp (-π * Y₀ / 2) / (16 * (8 * Real.exp 1) ^ (2 * k)) := by
    have hE : Real.exp (-π * Y₀ / 4) ^ 2 = Real.exp (-π * Y₀ / 2) := by
      rw [← Real.exp_nat_mul]; ring_nf
    have hP : ((8 * Real.exp 1) ^ k) ^ 2 = (8 * Real.exp 1) ^ (2 * k) := by
      rw [← pow_mul, Nat.mul_comm]
    rw [hm₀, div_pow, mul_pow, mul_pow, hE, hP]; ring
  have h0 : 0 ≤ M ^ 2 * Real.exp (-π * Y₀ / 2) / (16 * (8 * Real.exp 1) ^ (2 * k)) := by
    positivity
  have hfinal : M ^ 2 * (Real.exp (-π * Y₀ / 2) / (176 * (8 * Real.exp 1) ^ (2 * k))) ≤
      m₀ ^ 2 * (volume G).toReal := by
    rw [hm2]
    calc M ^ 2 * (Real.exp (-π * Y₀ / 2) / (176 * (8 * Real.exp 1) ^ (2 * k)))
        = M ^ 2 * Real.exp (-π * Y₀ / 2) / (16 * (8 * Real.exp 1) ^ (2 * k)) * (1 / 11) := by
          field_simp; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hvolG h0
  linarith

end

end RHTower
