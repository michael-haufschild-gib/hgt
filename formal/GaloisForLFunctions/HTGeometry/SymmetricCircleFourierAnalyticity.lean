import GaloisForLFunctions.HTGeometry.PowerSeriesDiscBridge
import GaloisForLFunctions.HTGeometry.SummableCircleFourierDensity

/-!
# Holomorphic Laurent extension of a symmetric circle Fourier density

A geometrically bounded real Fourier tail extends from the unit circle to a holomorphic Laurent
series on an annular neighborhood.  Restriction to the circle is exactly the original symmetric
density.  This gives a reusable, source-independent witness for the paper phrase “real-analytic
circle density”.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex Topology
open scoped BigOperators ComplexConjugate

noncomputable section

/-- Explicit Laurent extension of `a₀ + 2 Σ_{n≥1} aₙ Re(zⁿ)` off the unit circle. -/
def symmetricCircleFourierLaurentExtension (a : ℕ → ℝ) (z : ℂ) : ℂ :=
  (a 0 : ℂ) + z * seriesSum (fun n => (a (n + 1) : ℂ)) z +
    z⁻¹ * seriesSum (fun n => (a (n + 1) : ℂ)) z⁻¹

/-- A geometric coefficient bound makes the Laurent extension analytic at every point whose
forward and inverse coordinates both lie inside the coefficient disc. -/
theorem analyticAt_symmetricCircleFourierLaurentExtension
    {a : ℕ → ℝ} {B r : ℝ} (hr : 0 < r)
    (hc : ∀ n : ℕ, ‖(a (n + 1) : ℂ)‖ * r ^ n ≤ B)
    {z : ℂ} (hz : z ≠ 0) (hzr : ‖z‖ < r) (hzinvr : ‖z⁻¹‖ < r) :
    AnalyticAt ℂ (symmetricCircleFourierLaurentExtension a) z := by
  have hseries := analyticOnNhd_seriesSum hr hc
  have hGz : AnalyticAt ℂ (seriesSum (fun n => (a (n + 1) : ℂ))) z :=
    hseries z (by simpa [Metric.mem_ball, dist_eq_norm] using hzr)
  have hGinv : AnalyticAt ℂ (seriesSum (fun n => (a (n + 1) : ℂ))) z⁻¹ :=
    hseries z⁻¹ (by simpa [Metric.mem_ball, dist_eq_norm] using hzinvr)
  have hinv : AnalyticAt ℂ (fun w : ℂ => w⁻¹) z := by
    fun_prop
  have hcomp : AnalyticAt ℂ
      (fun w : ℂ => seriesSum (fun n => (a (n + 1) : ℂ)) w⁻¹) z := by
    change AnalyticAt ℂ
      (seriesSum (fun n => (a (n + 1) : ℂ)) ∘ fun w : ℂ => w⁻¹) z
    exact hGinv.comp hinv
  change AnalyticAt ℂ (fun z => (a 0 : ℂ) +
    z * seriesSum (fun n => (a (n + 1) : ℂ)) z +
    z⁻¹ * seriesSum (fun n => (a (n + 1) : ℂ)) z⁻¹) z
  exact (analyticAt_const.add (analyticAt_id.mul hGz)).add (hinv.mul hcomp)

/-- On the unit circle, the Laurent extension is exactly the symmetric real Fourier density. -/
theorem symmetricCircleFourierLaurentExtension_coe
    {a : ℕ → ℝ} (ha : Summable fun n : ℕ => |a (n + 1)|) (z : Circle) :
    symmetricCircleFourierLaurentExtension a (z : ℂ) =
      (symmetricCircleFourierDensity a z : ℂ) := by
  let p : ℕ → ℂ := fun n => (a (n + 1) : ℂ) * (z : ℂ) ^ (n + 1)
  let q : ℕ → ℂ := fun n => (a (n + 1) : ℂ) * (z : ℂ)⁻¹ ^ (n + 1)
  have hp : Summable p := by
    refine Summable.of_norm_bounded ha ?_
    intro n
    simp [p]
  have hq : Summable q := by
    refine Summable.of_norm_bounded ha ?_
    intro n
    simp [q]
  have hpos : (z : ℂ) * seriesSum (fun n => (a (n + 1) : ℂ)) (z : ℂ) = ∑' n, p n := by
    rw [seriesSum, ← tsum_mul_left]
    apply tsum_congr
    intro n
    simp [p, pow_succ]
    ring
  have hneg : (z : ℂ)⁻¹ * seriesSum (fun n => (a (n + 1) : ℂ)) (z : ℂ)⁻¹ =
      ∑' n, q n := by
    rw [seriesSum, ← tsum_mul_left]
    apply tsum_congr
    intro n
    simp [q, pow_succ]
    ring
  have hpq : (∑' n, p n) + ∑' n, q n = ∑' n, (p n + q n) :=
    (hp.tsum_add hq).symm
  have hterm (n : ℕ) : p n + q n =
      ((2 * (a (n + 1) * ((z : ℂ) ^ (n + 1)).re) : ℝ) : ℂ) := by
    simp only [p, q]
    rw [← Circle.coe_inv, Circle.coe_inv_eq_conj, ← map_pow]
    rw [← mul_add, Complex.add_conj]
    push_cast
    ring
  have hsreal := summable_symmetricCircleFourierDensity_terms ha z
  have hpqterm : (∑' (n : ℕ), (p n + q n)) =
      ∑' (n : ℕ), ((2 * (a (n + 1) * ((z : ℂ) ^ (n + 1)).re) : ℝ) : ℂ) := by
    apply tsum_congr
    intro n
    exact hterm n
  have hs2 : Summable (fun n : ℕ =>
      2 * (a (n + 1) * ((z : ℂ) ^ (n + 1)).re)) := hsreal.mul_left 2
  have hcast2 := Complex.ofRealCLM.map_tsum hs2
  have hscaled :
      (∑' (n : ℕ), ((2 * (a (n + 1) * ((z : ℂ) ^ (n + 1)).re) : ℝ) : ℂ)) =
        2 * ((∑' (n : ℕ), a (n + 1) * ((z : ℂ) ^ (n + 1)).re : ℝ) : ℂ) := by
    calc
      (∑' (n : ℕ), ((2 * (a (n + 1) * ((z : ℂ) ^ (n + 1)).re) : ℝ) : ℂ)) =
          ((∑' (n : ℕ), 2 * (a (n + 1) * ((z : ℂ) ^ (n + 1)).re) : ℝ) : ℂ) :=
        hcast2.symm
      _ = ((2 * ∑' (n : ℕ), a (n + 1) * ((z : ℂ) ^ (n + 1)).re : ℝ) : ℂ) := by
        rw [tsum_mul_left]
      _ = 2 * ((∑' (n : ℕ), a (n + 1) * ((z : ℂ) ^ (n + 1)).re : ℝ) : ℂ) := by
        push_cast
        rfl
  rw [symmetricCircleFourierLaurentExtension, hpos, hneg, add_assoc, hpq]
  simp only [symmetricCircleFourierDensity, Complex.ofReal_add, Complex.ofReal_mul,
    Complex.ofReal_ofNat]
  rw [hpqterm, hscaled]

end

end GaloisForLFunctions.HTGeometry
