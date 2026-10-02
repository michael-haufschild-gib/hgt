import GaloisForLFunctions.RHTower.ZetaChiDualAtomUniform
import GaloisForLFunctions.RHTower.HighBlockCutoffMonotone

open Complex Set Filter Topology MeasureTheory
open scoped BigOperators
noncomputable section
namespace RHTower

/-- The actual unweighted dual summand at physical zero phase. -/
def zetaChiDualInteriorAtom (s : ℂ) (n : ℕ) (t : ℝ) : ℂ :=
  zetaChi (s + (t : ℂ) * I) * (n : ℂ) ^ (s - 1) *
    bourgainOscillation (t * Real.log n)

private theorem continuous_zetaChiDualInteriorAtom {s : ℂ} (hs : s.re < 1) (n : ℕ) :
    Continuous (zetaChiDualInteriorAtom s n) := by
  have hchi : Continuous (fun t : ℝ => zetaChi (s + (t : ℂ) * I)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    have hG : Gammaℝ (1 - (s + (t : ℂ) * I)) ≠ 0 := by
      apply Gammaℝ_ne_zero_of_re_pos
      simpa using sub_pos.mpr hs
    have hpath : Continuous (fun u : ℝ => s + (u : ℂ) * I) := by fun_prop
    exact ContinuousAt.comp (f := fun u : ℝ => s + (u : ℂ) * I) (x := t)
      (zetaChi_analyticAt hG).continuousAt hpath.continuousAt
  unfold zetaChiDualInteriorAtom bourgainOscillation
  exact (hchi.mul continuous_const).mul (by fun_prop)

/-- The literal Gaussian cutoff is strictly positive real on the positive ray. -/
theorem smoothAFECutoff_re_pos {x : ℝ} (hx : 0 < x) : 0 < (smoothAFECutoff x).re := by
  have hanti : StrictAntiOn (fun y : ℝ => (smoothAFECutoff y).re) (Ioi 0) := by
    apply strictAntiOn_of_deriv_neg (convex_Ioi 0)
    · intro y hy
      exact (hasDerivAt_smoothAFECutoff_re hy).continuousAt.continuousWithinAt
    · rw [interior_Ioi]
      intro y hy
      rw [(hasDerivAt_smoothAFECutoff_re hy).deriv]
      unfold smoothAFECutoffDeriv
      have hroot : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
      exact neg_neg_of_pos (div_pos (Real.exp_pos _)
        (mul_pos (mul_pos (by norm_num) hroot) hy))
  exact lt_of_le_of_lt (smoothAFECutoff_re_nonneg (by linarith : 0 < x + 1))
    (hanti hx (by linarith : 0 < x + 1) (by linarith))

private theorem norm_integral_dual_atom_weighted_sum {s : ℂ} (hs : s.re < 1)
    (S : Finset ℕ) (w : ℕ → ℝ) (l u e : ℝ)
    (hw : ∀ n ∈ S, 0 ≤ w n)
    (hb : ∀ n ∈ S, ‖(∫ t in l..u, zetaChiDualInteriorAtom s n t) -
      ((2 * Real.pi : ℝ) : ℂ)‖ ≤ e) :
    ‖(∫ t in l..u, ∑ n ∈ S, (w n : ℂ) * zetaChiDualInteriorAtom s n t) -
      ((2 * Real.pi * ∑ n ∈ S, w n : ℝ) : ℂ)‖ ≤ e * ∑ n ∈ S, w n := by
  have he : ((2 * Real.pi * ∑ n ∈ S, w n : ℝ) : ℂ) =
      ∑ n ∈ S, (w n : ℂ) * ((2 * Real.pi : ℝ) : ℂ) := by
    push_cast
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n _
    ring
  rw [intervalIntegral.integral_finsetSum (fun n _ =>
    ((continuous_zetaChiDualInteriorAtom hs n).const_mul (w n : ℂ)).intervalIntegrable l u), he]
  simp_rw [intervalIntegral.integral_const_mul]
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ n ∈ S, ‖(w n : ℂ) * (∫ t in l..u, zetaChiDualInteriorAtom s n t) -
        (w n : ℂ) * ((2 * Real.pi : ℝ) : ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ S, w n * e := by
      apply Finset.sum_le_sum
      intro n hn
      rw [← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw n hn)]
      exact mul_le_mul_of_nonneg_left (hb n hn) (hw n hn)
    _ = _ := by rw [← Finset.sum_mul]; ring

/-- Complete finite interior blocks retain a relative error independent of
the number of terms, with every nonnegative coefficient paid exactly. -/
theorem exists_zetaChi_dual_weighted_interior_mean
    (c : ℂ) {r : ℝ} (hr : 0 ≤ r) (hc0 : 1 / 2 ≤ c.re - r) (hc1 : c.re + r < 1) :
    ∃ D : ℝ, 0 < D ∧ ∀ᶠ m : ℕ in atTop, ∀ s ∈ Metric.closedBall c r,
      ∀ (S : Finset ℕ) (w : ℕ → ℝ), (∀ n ∈ S, 0 ≤ w n) →
      (∀ n ∈ S, (m : ℝ) ^ 10 + (m : ℝ) ^ 6 ≤ 2 * Real.pi * n ∧
        2 * Real.pi * n + (m : ℝ) ^ 6 ≤ 2 * (m : ℝ) ^ 10) →
      ‖(∫ t in (m : ℝ) ^ 10..(2 * (m : ℝ) ^ 10),
          ∑ n ∈ S, (w n : ℂ) * zetaChiDualInteriorAtom s n t) -
        ((2 * Real.pi * ∑ n ∈ S, w n : ℝ) : ℂ)‖ ≤ (D / m) * ∑ n ∈ S, w n := by
  obtain ⟨D, hD, hb⟩ := exists_zetaChi_dual_atom_disc_uniform c hr hc0 hc1
  refine ⟨D, hD, ?_⟩
  filter_upwards [hb] with m hm
  intro s hs S w hw hS
  have hre : |s.re - c.re| ≤ r := (by
    simpa only [Complex.sub_re, dist_eq_norm] using Complex.abs_re_le_norm (s - c) :
      |s.re - c.re| ≤ dist s c).trans hs
  have hs1 : s.re < 1 := by linarith [(abs_le.mp hre).2]
  exact norm_integral_dual_atom_weighted_sum hs1 S w _ _ _ hw
    (fun n hn => hm s hs n (hS n hn).1 (hS n hn).2)

end RHTower
