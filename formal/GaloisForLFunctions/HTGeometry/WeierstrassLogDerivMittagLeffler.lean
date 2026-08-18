import GaloisForLFunctions.HTGeometry.MittagLefflerHalfPlaneApproximation
import GaloisForLFunctions.HTGeometry.WeierstrassFactorizationTheorem
import GaloisForLFunctions.HTGeometry.PrescribedDivisorRealization
import Mathlib.Analysis.Calculus.LogDerivUniformlyOn

/-!
# The logarithmic derivative of a Weierstrass product is a Mittag-Leffler series

The genus-`n` elementary factor at `a n` has

```text
logDeriv (fun z => weierstrassFactor n (z / a n)) z = (z / a n)^n / (z - a n)
                                                    = 1/(z - a n) - Q n z ,
Q n z = - (sum_{j<n} z^j (a n)^{n-1-j}) / (a n)^n ,
```

with `Q n` a polynomial, hence entire, and the remainder bounded by `2^{-n} * 2/‖a n‖` on the disc
of radius `‖a n‖/2`.  Termwise logarithmic differentiation of the locally uniformly convergent
product therefore exhibits `logDeriv (weierstrassGenusProduct a)` as a Mittag-Leffler series with
simple poles of residue one at the zeros.

Combined with `exists_entire_approx_sq_mittagLeffler` this gives the Arakelyan step for the
logarithmic derivative of any prescribed-divisor realization.
-/

noncomputable section

open Metric Filter Complex

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

/-- The derivative of the `n`-th Weierstrass factor of a product. -/
theorem hasDerivAt_weierstrassGenusFactorAt (a : ℕ → ℂ) (n : ℕ) (z : ℂ) :
    HasDerivAt (weierstrassGenusFactorAt a n)
      (-((z / a n) ^ n) * Complex.exp (weierstrassLog n (z / a n)) * (1 / a n)) z := by
  have h1 : HasDerivAt (fun w : ℂ => w / a n) (1 / a n) z := by
    simpa [div_eq_mul_inv, one_div] using (hasDerivAt_id z).div_const (a n)
  exact (hasDerivAt_weierstrassFactor n (z / a n)).comp z h1

/-- **The logarithmic derivative of the `n`-th factor.** -/
theorem logDeriv_weierstrassGenusFactorAt {a : ℕ → ℂ} (hane : ∀ n, a n ≠ 0) (n : ℕ) {z : ℂ}
    (hz : z ≠ a n) :
    logDeriv (weierstrassGenusFactorAt a n) z = (z / a n) ^ n / (z - a n) := by
  have han : a n ≠ 0 := hane n
  have hzan : z - a n ≠ 0 := sub_ne_zero.mpr hz
  have hone : (1 : ℂ) - z / a n ≠ 0 := by
    intro h
    apply hzan
    field_simp at h
    linear_combination -h
  have hexp : Complex.exp (weierstrassLog n (z / a n)) ≠ 0 := Complex.exp_ne_zero _
  rw [logDeriv_apply, (hasDerivAt_weierstrassGenusFactorAt a n z).deriv,
    weierstrassGenusFactorAt, weierstrassFactor]
  field_simp
  ring

/-- The polynomial correction attached to the `n`-th factor. -/
def weierstrassMittagLefflerCorrection (a : ℕ → ℂ) (n : ℕ) (z : ℂ) : ℂ :=
  -(∑ j ∈ Finset.range n, z ^ j * (a n) ^ (n - 1 - j)) / (a n) ^ n

theorem differentiable_weierstrassMittagLefflerCorrection (a : ℕ → ℂ) (n : ℕ) :
    Differentiable ℂ (weierstrassMittagLefflerCorrection a n) := by
  unfold weierstrassMittagLefflerCorrection
  exact ((Differentiable.fun_sum fun j _ =>
    (differentiable_id.pow j).mul (differentiable_const _)).neg).div_const _

/-- **The `n`-th factor's logarithmic derivative in Mittag-Leffler form.** -/
theorem logDeriv_weierstrassGenusFactorAt_eq {a : ℕ → ℂ} (hane : ∀ n, a n ≠ 0) (n : ℕ) {z : ℂ}
    (hz : z ≠ a n) :
    logDeriv (weierstrassGenusFactorAt a n) z
      = 1 / (z - a n) - weierstrassMittagLefflerCorrection a n z := by
  have han : a n ≠ 0 := hane n
  have hzan : z - a n ≠ 0 := sub_ne_zero.mpr hz
  have hanpow : (a n) ^ n ≠ 0 := pow_ne_zero _ han
  have hgeom : (∑ j ∈ Finset.range n, z ^ j * (a n) ^ (n - 1 - j)) * (z - a n)
      = z ^ n - (a n) ^ n := geom_sum₂_mul z (a n) n
  rw [logDeriv_weierstrassGenusFactorAt hane n hz, weierstrassMittagLefflerCorrection, div_pow]
  field_simp
  linear_combination -hgeom

/-- The Mittag-Leffler bound sequence attached to a zero sequence. -/
def weierstrassMittagLefflerBound (a : ℕ → ℂ) (n : ℕ) : ℝ := (1 / 2 : ℝ) ^ n * (2 / ‖a n‖)

theorem summable_weierstrassMittagLefflerBound {a : ℕ → ℂ}
    (ha : Tendsto (fun n => ‖a n‖) atTop atTop) :
    Summable (weierstrassMittagLefflerBound a) := by
  refine Summable.of_norm_bounded_eventually_nat
    (g := fun n : ℕ => (1 / 2 : ℝ) ^ n) (summable_geometric_of_lt_one (by norm_num) (by norm_num))
    ?_
  filter_upwards [ha.eventually_ge_atTop 2] with n hn
  have hpos : (0:ℝ) < ‖a n‖ := by linarith
  have hle : 2 / ‖a n‖ ≤ 1 := by
    rw [div_le_one hpos]
    exact hn
  rw [weierstrassMittagLefflerBound, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc (1 / 2 : ℝ) ^ n * (2 / ‖a n‖) ≤ (1 / 2 : ℝ) ^ n * 1 := by
        refine mul_le_mul_of_nonneg_left hle (by positivity)
    _ = (1 / 2 : ℝ) ^ n := by ring

/-- **The Mittag-Leffler bound on the half-modulus disc.** -/
theorem norm_weierstrassMittagLefflerTerm_le {a : ℕ → ℂ} (hane : ∀ n, a n ≠ 0) (n : ℕ) {z : ℂ}
    (hz : z ∈ ball (0 : ℂ) (‖a n‖ / 2)) :
    ‖(1 : ℂ) / (z - a n) - weierstrassMittagLefflerCorrection a n z‖
      ≤ weierstrassMittagLefflerBound a n := by
  have hanpos : (0:ℝ) < ‖a n‖ := norm_pos_iff.mpr (hane n)
  have hzn : ‖z‖ < ‖a n‖ / 2 := by simpa [mem_ball, dist_zero_right] using hz
  have hzne : z ≠ a n := by
    intro h
    rw [h] at hzn
    linarith
  have hzan : (‖a n‖ / 2 : ℝ) < ‖z - a n‖ := by
    have h := norm_sub_norm_le (a n) z
    rw [norm_sub_rev] at h
    linarith
  have hzanpos : (0:ℝ) < ‖z - a n‖ := by linarith
  have heq : (1 : ℂ) / (z - a n) - weierstrassMittagLefflerCorrection a n z
      = (z / a n) ^ n / (z - a n) :=
    ((logDeriv_weierstrassGenusFactorAt_eq hane n hzne).symm.trans
      (logDeriv_weierstrassGenusFactorAt hane n hzne))
  rw [heq, norm_div, norm_pow, norm_div, weierstrassMittagLefflerBound]
  have hratio : ‖z‖ / ‖a n‖ ≤ 1 / 2 := by
    rw [div_le_div_iff₀ hanpos (by norm_num)]
    linarith
  have hnum : (‖z‖ / ‖a n‖) ^ n ≤ (1 / 2 : ℝ) ^ n :=
    pow_le_pow_left₀ (by positivity) hratio n
  calc (‖z‖ / ‖a n‖) ^ n / ‖z - a n‖ ≤ (1 / 2 : ℝ) ^ n / ‖z - a n‖ := by gcongr
    _ ≤ (1 / 2 : ℝ) ^ n * (2 / ‖a n‖) := by
        rw [div_eq_mul_inv]
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        rw [inv_eq_one_div, div_le_div_iff₀ hzanpos hanpos]
        linarith

theorem summable_weierstrassMittagLefflerTerm {a : ℕ → ℂ}
    (ha : Tendsto (fun n => ‖a n‖) atTop atTop) (hane : ∀ n, a n ≠ 0) (z : ℂ) :
    Summable fun n => (1 : ℂ) / (z - a n) - weierstrassMittagLefflerCorrection a n z := by
  refine summable_of_growing_radii
    (g := fun n z => (1 : ℂ) / (z - a n) - weierstrassMittagLefflerCorrection a n z)
    (R := fun n => ‖a n‖ / 2) (summable_weierstrassMittagLefflerBound ha)
    (Filter.Tendsto.atTop_div_const (by norm_num) ha) ?_ z
  intro n w hw
  exact norm_weierstrassMittagLefflerTerm_le hane n (by simpa [mem_ball, dist_zero_right] using hw)

/-- **The logarithmic derivative of the Weierstrass product is the Mittag-Leffler series.** -/
theorem logDeriv_weierstrassGenusProduct_eq_tsum {a : ℕ → ℂ}
    (ha : Tendsto (fun n => ‖a n‖) atTop atTop) (hane : ∀ n, a n ≠ 0) {z : ℂ}
    (hz : ∀ n, z ≠ a n) :
    logDeriv (weierstrassGenusProduct a) z
      = ∑' n : ℕ, ((1 : ℂ) / (z - a n) - weierstrassMittagLefflerCorrection a n z) := by
  have hfac : ∀ n, weierstrassGenusFactorAt a n z ≠ 0 := by
    intro n h
    rw [weierstrassGenusFactorAt_eq_zero_iff hane n z] at h
    exact hz n h
  have hprod : weierstrassGenusProduct a z ≠ 0 := by
    intro h
    obtain ⟨n, hn⟩ := (weierstrassGenusProduct_eq_zero_iff ha hane z).mp h
    exact hz n hn
  have hsum : Summable fun n => logDeriv (weierstrassGenusFactorAt a n) z := by
    refine (summable_weierstrassMittagLefflerTerm ha hane z).congr fun n => ?_
    exact (logDeriv_weierstrassGenusFactorAt_eq hane n (hz n)).symm
  have hmul : MultipliableLocallyUniformlyOn (weierstrassGenusFactorAt a) (Set.univ : Set ℂ) :=
    (hasProdLocallyUniformlyOn_weierstrassGenusFactorAt ha hane).multipliableLocallyUniformlyOn
  have hkey := logDeriv_tprod_eq_tsum isOpen_univ (Set.mem_univ z) hfac
    (fun n => (differentiable_weierstrassGenusFactorAt hane n).differentiableOn) hsum hmul hprod
  rw [show (fun z => ∏' n : ℕ, weierstrassGenusFactorAt a n z) = weierstrassGenusProduct a from
    rfl] at hkey
  rw [hkey]
  exact tsum_congr fun n => logDeriv_weierstrassGenusFactorAt_eq hane n (hz n)

/-- **The Arakelyan step for the logarithmic derivative of a Weierstrass product.** -/
theorem exists_entire_approx_sq_logDeriv_weierstrassGenusProduct {a : ℕ → ℂ}
    (ha : Tendsto (fun n => ‖a n‖) atTop atTop) (hane : ∀ n, a n ≠ 0)
    (hare : ∀ n, (a n).re < 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ G : ℂ → ℂ, Differentiable ℂ G ∧
      ∀ s : ℂ, 1 ≤ s.re → ‖s ^ 2 * logDeriv (weierstrassGenusProduct a) s - G s‖ ≤ ε := by
  obtain ⟨G, hGd, hGb⟩ := exists_entire_approx_sq_mittagLeffler (a := a) (m := fun _ => 1)
    (Q := weierstrassMittagLefflerCorrection a) (u := weierstrassMittagLefflerBound a)
    ha hare (differentiable_weierstrassMittagLefflerCorrection a)
    (summable_weierstrassMittagLefflerBound ha)
    (fun n z hz => norm_weierstrassMittagLefflerTerm_le hane n hz) hε
  refine ⟨G, hGd, fun s hs => ?_⟩
  have hne : ∀ n, s ≠ a n := by
    intro n hsa
    have := hare n
    rw [← hsa] at this
    linarith
  rw [logDeriv_weierstrassGenusProduct_eq_tsum ha hane hne]
  exact hGb s hs

theorem weierstrassGenusProduct_ne_zero_of_re {a : ℕ → ℂ}
    (ha : Tendsto (fun n => ‖a n‖) atTop atTop) (hane : ∀ n, a n ≠ 0)
    (hare : ∀ n, (a n).re < 1) {s : ℂ} (hs : 1 ≤ s.re) :
    weierstrassGenusProduct a s ≠ 0 := by
  intro h
  obtain ⟨n, hn⟩ := (weierstrassGenusProduct_eq_zero_iff ha hane s).mp h
  have := hare n
  rw [← hn] at this
  linarith

/-- **The Arakelyan step for the logarithmic derivative of a prescribed-divisor realization.** -/
theorem exists_entire_approx_sq_logDeriv_divisorFunction {a b : ℕ → ℂ}
    (ha : Tendsto (fun n => ‖a n‖) atTop atTop) (hane : ∀ n, a n ≠ 0)
    (hb : Tendsto (fun n => ‖b n‖) atTop atTop) (hbne : ∀ n, b n ≠ 0)
    (hare : ∀ n, (a n).re < 1) (hbre : ∀ n, (b n).re < 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ G : ℂ → ℂ, Differentiable ℂ G ∧
      ∀ s : ℂ, 1 ≤ s.re → ‖s ^ 2 * logDeriv (divisorFunction a b) s - G s‖ ≤ ε := by
  obtain ⟨Ga, hGad, hGab⟩ :=
    exists_entire_approx_sq_logDeriv_weierstrassGenusProduct ha hane hare (ε := ε / 2)
      (by linarith)
  obtain ⟨Gb, hGbd, hGbb⟩ :=
    exists_entire_approx_sq_logDeriv_weierstrassGenusProduct hb hbne hbre (ε := ε / 2)
      (by linarith)
  refine ⟨fun s => Ga s - Gb s, hGad.sub hGbd, fun s hs => ?_⟩
  have hlog : logDeriv (divisorFunction a b) s
      = logDeriv (weierstrassGenusProduct a) s - logDeriv (weierstrassGenusProduct b) s := by
    have := logDeriv_div (f := weierstrassGenusProduct a) (g := weierstrassGenusProduct b) s
      (weierstrassGenusProduct_ne_zero_of_re ha hane hare hs)
      (weierstrassGenusProduct_ne_zero_of_re hb hbne hbre hs)
      ((differentiable_weierstrassGenusProduct ha hane) s)
      ((differentiable_weierstrassGenusProduct hb hbne) s)
    exact this
  rw [hlog]
  have hsplit : s ^ 2 * (logDeriv (weierstrassGenusProduct a) s
        - logDeriv (weierstrassGenusProduct b) s) - (Ga s - Gb s)
      = (s ^ 2 * logDeriv (weierstrassGenusProduct a) s - Ga s)
        - (s ^ 2 * logDeriv (weierstrassGenusProduct b) s - Gb s) := by ring
  rw [hsplit]
  calc ‖(s ^ 2 * logDeriv (weierstrassGenusProduct a) s - Ga s)
          - (s ^ 2 * logDeriv (weierstrassGenusProduct b) s - Gb s)‖
      ≤ ‖s ^ 2 * logDeriv (weierstrassGenusProduct a) s - Ga s‖
        + ‖s ^ 2 * logDeriv (weierstrassGenusProduct b) s - Gb s‖ := norm_sub_le _ _
    _ ≤ ε / 2 + ε / 2 := add_le_add (hGab s hs) (hGbb s hs)
    _ = ε := by ring

end GaloisForLFunctions.HTGeometry

end
