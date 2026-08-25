import GaloisForLFunctions.RHTower.CriticalPrimeFockRadiusWindow
import GaloisForLFunctions.RHTower.TwoModeFuchsLimit

/-!
# Scalar critical-prime Fock-window phase transition

At the polynomial Fock radius `rho_m(x)`, the exact local prime-log mass has the same trichotomy
as its main term `2 x rho_m(x)`: divergence for `2 < m < 4`, convergence to `2` for `m = 4`,
and convergence to zero for `m > 4`.

This is the arithmetic scalar input to the doubling-Fock Carleson theorem.  It does not by itself
construct the Fock space or prove the normalized evaluation operator's boundedness or compactness.
-/

open Filter Topology

namespace RHTower

noncomputable section

/-- Main local critical-prime mass predicted at the polynomial Fock radius. -/
def criticalPrimeFockWindowMain (m x : ℝ) : ℝ :=
  2 * x * criticalPrimeFockRadius m x

theorem criticalPrimeFockWindowMain_eq_rpow
    (m : ℝ) {x : ℝ} (hx : 0 < x) :
    criticalPrimeFockWindowMain m x = 2 * x ^ (2 - m / 2) := by
  rw [criticalPrimeFockWindowMain, criticalPrimeFockRadius_eq_rpow hx.le]
  calc
    2 * x * x ^ (1 - m / 2) = 2 * (x ^ (1 : ℝ) * x ^ (1 - m / 2)) := by
      rw [Real.rpow_one]
      ring
    _ = 2 * x ^ ((1 : ℝ) + (1 - m / 2)) := by
      rw [Real.rpow_add hx]
    _ = 2 * x ^ (2 - m / 2) := by
      congr 2
      ring

/-- Below quartic degree, the adapted-window main mass diverges. -/
theorem tendsto_criticalPrimeFockWindowMain_atTop
    {m : ℝ} (hm : m < 4) :
    Tendsto (criticalPrimeFockWindowMain m) atTop atTop := by
  have hexp : 0 < 2 - m / 2 := by linarith
  have h : Tendsto (fun x : ℝ => 2 * x ^ (2 - m / 2)) atTop atTop :=
    (tendsto_rpow_atTop hexp).const_mul_atTop (by norm_num)
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  exact (criticalPrimeFockWindowMain_eq_rpow m hx).symm

/-- Above quartic degree, the adapted-window main mass vanishes. -/
theorem tendsto_criticalPrimeFockWindowMain_zero
    {m : ℝ} (hm : 4 < m) :
    Tendsto (criticalPrimeFockWindowMain m) atTop (nhds 0) := by
  have hexp : 0 < m / 2 - 2 := by linarith
  have h : Tendsto (fun x : ℝ => 2 * x ^ (-(m / 2 - 2))) atTop (nhds 0) := by
    simpa using (tendsto_rpow_neg_atTop hexp).const_mul 2
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  rw [criticalPrimeFockWindowMain_eq_rpow m hx]
  congr 2
  ring

/-- At quartic degree, the adapted-window main mass is exactly asymptotic to `2`. -/
theorem tendsto_criticalPrimeFockWindowMain_four :
    Tendsto (criticalPrimeFockWindowMain 4) atTop (nhds 2) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  rw [criticalPrimeFockWindowMain_eq_rpow 4 hx]
  norm_num

theorem primeLogWindowMass_eq_ratio_mul_criticalPrimeFockWindowMain
    (m : ℝ) {x : ℝ} (hx : 0 < x) :
    primeLogWindowMass x (criticalPrimeFockRadius m x) =
      (primeLogWindowMass x (criticalPrimeFockRadius m x) /
        criticalPrimeFockWindowMain m x) *
          criticalPrimeFockWindowMain m x := by
  have hmain : criticalPrimeFockWindowMain m x ≠ 0 := by
    rw [criticalPrimeFockWindowMain]
    exact (mul_pos (mul_pos (by norm_num) hx) (criticalPrimeFockRadius_pos hx)).ne'
  exact (div_mul_cancel₀ _ hmain).symm

/-- Subquartic local prime mass diverges at the exact adapted radius. -/
theorem tendsto_primeLogWindowMass_criticalPrimeFockRadius_atTop
    {m : ℝ} (hm2 : 2 < m) (hm4 : m < 4) :
    Tendsto (fun x => primeLogWindowMass x (criticalPrimeFockRadius m x))
      atTop atTop := by
  have hratio : Tendsto (fun x : ℝ =>
      primeLogWindowMass x (criticalPrimeFockRadius m x) /
        criticalPrimeFockWindowMain m x) atTop (nhds 1) := by
    simpa only [criticalPrimeFockWindowMain] using
      tendsto_primeLogWindowMass_div_criticalPrimeFockModel hm2
  have hmain := tendsto_criticalPrimeFockWindowMain_atTop hm4
  have hmainPos : ∀ᶠ x : ℝ in atTop, 0 < criticalPrimeFockWindowMain m x := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    rw [criticalPrimeFockWindowMain]
    exact mul_pos (mul_pos (by norm_num) hx) (criticalPrimeFockRadius_pos hx)
  have hlower : ∀ᶠ x : ℝ in atTop,
      (1 / 2 : ℝ) * criticalPrimeFockWindowMain m x ≤
        primeLogWindowMass x (criticalPrimeFockRadius m x) :=
    eventually_const_mul_le_of_tendsto_div_atTop hratio hmainPos (by norm_num)
  have hscaled : Tendsto
      (fun x => (1 / 2 : ℝ) * criticalPrimeFockWindowMain m x) atTop atTop :=
    hmain.const_mul_atTop (by norm_num)
  refine tendsto_atTop.2 fun b => ?_
  filter_upwards [hscaled.eventually (eventually_ge_atTop b), hlower] with x hxb hxlower
  exact hxb.trans hxlower

/-- Superquartic local prime mass vanishes at the exact adapted radius. -/
theorem tendsto_primeLogWindowMass_criticalPrimeFockRadius_zero
    {m : ℝ} (hm : 4 < m) :
    Tendsto (fun x => primeLogWindowMass x (criticalPrimeFockRadius m x))
      atTop (nhds 0) := by
  have hratio := tendsto_primeLogWindowMass_div_criticalPrimeFockModel
    (m := m) (by linarith)
  have hmain := tendsto_criticalPrimeFockWindowMain_zero hm
  have hprod := hratio.mul hmain
  simpa only [one_mul] using hprod.congr' (by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    exact (primeLogWindowMass_eq_ratio_mul_criticalPrimeFockWindowMain m hx).symm)

/-- Quartic local prime mass converges to its nonzero critical value `2`. -/
theorem tendsto_primeLogWindowMass_criticalPrimeFockRadius_four :
    Tendsto (fun x => primeLogWindowMass x (criticalPrimeFockRadius 4 x))
      atTop (nhds 2) := by
  have hratio := tendsto_primeLogWindowMass_div_criticalPrimeFockModel
    (m := (4 : ℝ)) (by norm_num)
  have hmain := tendsto_criticalPrimeFockWindowMain_four
  have hprod := hratio.mul hmain
  simpa only [one_mul] using hprod.congr' (by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    exact (primeLogWindowMass_eq_ratio_mul_criticalPrimeFockWindowMain 4 hx).symm)

end

end RHTower
