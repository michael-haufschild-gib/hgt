import GaloisForLFunctions.RHTower.WeilWorkSingularArithmeticEulerDisk
import GaloisForLFunctions.HTGeometry.CaratheodoryCoefficient
import GaloisForLFunctions.HTGeometry.BoundedCoeffPowerSeries
import Mathlib.Analysis.Complex.AbsMax

/-!
# Finite Euler real-part bounds force simultaneous coefficient gains

The maximum principle extends a finite torus bound through the closed
polydisc. Caratheodory's coefficient inequality detects each local first
coefficient linearly. Compact local maxima and one diagonal disc then
bound the product of these gains, without dependence on dimension.
-/

open Complex Metric Set Filter Topology
open GaloisForLFunctions.HTGeometry
noncomputable section
namespace RHTower.WeilSingularArithmetic

/-- Real-part maximum principle, on the closed unit disc. -/
theorem re_le_of_sphere_re_le {F : ℂ → ℂ} (hF : DiffContOnCl ℂ F (ball 0 1))
    {C : ℝ} (hC : ∀ z, ‖z‖ = 1 → (F z).re ≤ C)
    {z : ℂ} (hz : ‖z‖ ≤ 1) : (F z).re ≤ C := by
  apply Real.exp_le_exp.mp
  have h := Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball
    (Complex.differentiable_exp.comp_diffContOnCl hF) (C := Real.exp C) (z := z) ?_ ?_
  · simpa only [Function.comp_def, Complex.norm_exp] using h
  · intro w hw
    rw [frontier_ball (0 : ℂ) (by norm_num : (1 : ℝ) ≠ 0)] at hw
    simp only [Function.comp_def, Complex.norm_exp]
    exact Real.exp_le_exp.mpr (hC w (mem_sphere_zero_iff_norm.mp hw))
  · rw [closure_ball (0 : ℂ) (by norm_num : (1 : ℝ) ≠ 0)]
    exact mem_closedBall_zero_iff.mpr hz

/-- One-variable real-part bounds extend successively through a finite polydisc. -/
theorem re_finsetProd_le_of_sphere_bound {ι : Type*} [DecidableEq ι]
    (F : ι → ℂ → ℂ) (P : Finset ι)
    (hF : ∀ i ∈ P, DiffContOnCl ℂ (F i) (ball 0 1))
    (c : ℂ) (C : ℝ)
    (hbound : ∀ z : ι → ℂ, (∀ i ∈ P, ‖z i‖ = 1) → (c * ∏ i ∈ P, F i (z i)).re ≤ C)
    (z : ι → ℂ) (hz : ∀ i ∈ P, ‖z i‖ ≤ 1) :
    (c * ∏ i ∈ P, F i (z i)).re ≤ C := by
  induction P using Finset.induction_on generalizing c C with
  | empty => simpa using hbound z (by simp)
  | @insert i P hi ih =>
    simp only [Finset.prod_insert hi]
    rw [← mul_assoc]
    have hFi := hF i (Finset.mem_insert_self i P)
    have hd : DiffContOnCl ℂ (fun w => c * F i w * ∏ j ∈ P, F j (z j)) (ball 0 1) :=
      ⟨((differentiableOn_const c).mul hFi.differentiableOn).mul_const _,
        (continuousOn_const.mul hFi.continuousOn).mul continuousOn_const⟩
    apply re_le_of_sphere_re_le hd ?_ (hz i (by simp))
    intro w hw
    apply ih (fun j hj => hF j (Finset.mem_insert_of_mem hj)) (c * F i w) C ?_
      (fun j hj => hz j (Finset.mem_insert_of_mem hj))
    intro y hy
    have hu := hbound (Function.update y i w) (by
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · simpa using hw
      · rw [Function.update_of_ne (ne_of_mem_of_not_mem hj hi)]
        exact hy j hj)
    have he : (∏ j ∈ P, F j (Function.update y i w j)) = ∏ j ∈ P, F j (y j) := by
      apply Finset.prod_congr rfl
      intro j hj
      rw [Function.update_of_ne (ne_of_mem_of_not_mem hj hi)]
    simpa only [Finset.prod_insert hi, Function.update_self, he, ← mul_assoc] using hu

/-- Carathéodory's first-coefficient estimate stated directly using the derivative. -/
theorem norm_deriv_le_two_sub_one {F : ℂ → ℂ} (hF : DiffContOnCl ℂ F (ball 0 1))
    (hzero : F 0 = 1) {M : ℝ} (hM : ∀ z, ‖z‖ = 1 → ‖F z‖ ≤ M) :
    ‖deriv F 0‖ ≤ 2 * (M - 1) := by
  let G : ℂ → ℂ := fun z => (M : ℂ) - F z
  have hG : DiffContOnCl ℂ G (ball 0 1) := hF.const_sub (M : ℂ)
  have hcoeff := norm_cauchyCoeff_mul_pow_le G (by norm_num : (0 : ℝ) < 1) hG
    (fun z hz => by
      change 0 ≤ M - (F z).re
      exact sub_nonneg.mpr ((Complex.re_le_norm _).trans (hM z (mem_sphere_zero_iff_norm.mp hz))))
    (n := 1) le_rfl
  have hp := hG.hasFPowerSeriesOnBall (R := (1 : NNReal)) (by norm_num)
  have he : cauchyCoeff G 1 1 = deriv G 0 := hp.hasFPowerSeriesAt.deriv.symm
  rw [he] at hcoeff
  have hd : deriv G 0 = -deriv F 0 := by
    exact ((hF.differentiableAt isOpen_ball (by simp)).hasDerivAt.const_sub (M : ℂ)).deriv
  simpa [hd, G, hzero] using hcoeff

@[simp] theorem boundedFun_zero (a : ℕ → ℂ) : boundedFun a 0 = a 0 := by
  unfold boundedFun
  rw [tsum_eq_single 0 (fun n hn => by simp [zero_pow hn])]
  simp

theorem deriv_boundedFun_zero {a : ℕ → ℂ} {C : ℝ} (ha : ∀ n, ‖a n‖ ≤ C) :
    deriv (boundedFun a) 0 = a 1 := by
  have h := (hasFPowerSeriesOnBall_boundedFun ha).hasFPowerSeriesAt.deriv
  exact h.trans (boundedSeries_coeff a 1)

theorem diffContOnCl_scaled_boundedFun {a : ℕ → ℂ} {C r : ℝ}
    (ha : ∀ n, ‖a n‖ ≤ C) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    DiffContOnCl ℂ (fun z : ℂ => boundedFun a ((r : ℂ) * z)) (ball 0 1) := by
  apply DifferentiableOn.diffContOnCl
  apply (differentiableOn_boundedFun ha).comp (differentiable_id.const_mul (r : ℂ)).differentiableOn
  intro z hz
  rw [closure_ball (0 : ℂ) (by norm_num : (1 : ℝ) ≠ 0)] at hz
  rw [mem_ball_zero_iff, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0]
  exact (mul_le_mul_of_nonneg_left (mem_closedBall_zero_iff.mp hz) hr0).trans_lt (by simpa using hr1)

/-- A local analytic maximum detects the first coefficient linearly. -/
theorem one_add_first_coefficient_le_max {a : ℕ → ℂ} {C r M : ℝ}
    (ha : ∀ n, ‖a n‖ ≤ C) (ha0 : a 0 = 1) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hM : ∀ z : ℂ, ‖z‖ = 1 → ‖boundedFun a ((r : ℂ) * z)‖ ≤ M) :
    1 + ‖a 1‖ * r / 2 ≤ M := by
  have hF := diffContOnCl_scaled_boundedFun ha hr0 hr1
  have h := norm_deriv_le_two_sub_one hF (by simp [ha0]) hM
  have hd : deriv (fun z : ℂ => boundedFun a ((r : ℂ) * z)) 0 = a 1 * (r : ℂ) := by
    have hb := (hasFPowerSeriesOnBall_boundedFun ha).hasFPowerSeriesAt.hasDerivAt
    have hder : HasDerivAt (boundedFun a) (a 1) ((r : ℂ) * (0 : ℂ)) := by
      change HasDerivAt (boundedFun a) ((boundedSeries a).coeff 1) 0 at hb
      simpa only [boundedSeries_coeff, mul_zero] using hb
    have hc := hder.comp 0 ((hasDerivAt_id (0 : ℂ)).const_mul (r : ℂ))
    simpa only [Function.comp_def, mul_one] using hc.deriv
  rw [hd, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0] at h
  linarith

/-- Compactness realizes the local norm, while its first coefficient gives a
linear lower bound at that maximizing point. -/
theorem exists_scaled_boundedFun_max {a : ℕ → ℂ} {C r : ℝ}
    (ha : ∀ n, ‖a n‖ ≤ C) (ha0 : a 0 = 1) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ∃ w : ℂ, ‖w‖ ≤ 1 ∧
      1 + ‖a 1‖ * r / 2 ≤ ‖boundedFun a ((r : ℂ) * w)‖ ∧
      ∀ z : ℂ, ‖z‖ ≤ 1 →
        ‖boundedFun a ((r : ℂ) * z)‖ ≤ ‖boundedFun a ((r : ℂ) * w)‖ := by
  have hc := (diffContOnCl_scaled_boundedFun ha hr0 hr1).continuousOn_ball.norm
  obtain ⟨w, hw, hmax⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_isMaxOn
    ⟨0, by simp⟩ hc
  refine ⟨w, mem_closedBall_zero_iff.mp hw, ?_, fun z hz => hmax (mem_closedBall_zero_iff.mpr hz)⟩
  exact one_add_first_coefficient_le_max ha ha0 hr0 hr1
    (fun z hz => hmax (mem_closedBall_zero_iff.mpr hz.le))

/-- A finite torus real-part bound controls the product of all first-coefficient
gains. The constant is independent of the number of variables. -/
theorem prod_one_add_first_coefficient_le {ι : Type*} [Fintype ι]
    (a : ι → ℕ → ℂ) (r : ι → ℝ) {B C : ℝ}
    (ha : ∀ i n, ‖a i n‖ ≤ B) (ha0 : ∀ i, a i 0 = 1)
    (hr0 : ∀ i, 0 ≤ r i) (hr1 : ∀ i, r i < 1)
    (hbound : ∀ z : ι → ℂ, (∀ i, ‖z i‖ = 1) →
      (∏ i, boundedFun (a i) ((r i : ℂ) * z i)).re ≤ C) :
    ∏ i, (1 + ‖a i 1‖ * r i / 4) ≤ 2 * C - 1 := by
  classical
  have hmax (i : ι) := exists_scaled_boundedFun_max (ha i) (ha0 i)
    (div_nonneg (hr0 i) (by norm_num : (0 : ℝ) ≤ 2))
    (by linarith [hr1 i] : r i / 2 < 1)
  choose w hw hcoef hmax using hmax
  let F : ι → ℂ → ℂ := fun i z => boundedFun (a i) ((r i : ℂ) * z)
  have hF (i : ι) : DiffContOnCl ℂ (F i) (ball 0 1) :=
    diffContOnCl_scaled_boundedFun (ha i) (hr0 i) (hr1 i)
  have hpoly (z : ι → ℂ) (hz : ∀ i, ‖z i‖ < 1) : (∏ i, F i (z i)).re ≤ C := by
    have h := re_finsetProd_le_of_sphere_bound F Finset.univ (fun i _ => hF i) 1 C
      (fun z hz => by simpa [F] using hbound z (fun i => hz i (Finset.mem_univ i)))
      z (fun i _ => (hz i).le)
    simpa using h
  have hprod := prod_norm_half_le_of_re_prod_le F (fun i => (hF i).differentiableOn)
    (fun i => by simp [F, ha0]) hpoly w hw
  apply le_trans (Finset.prod_le_prod (fun i _ => by
    have := hr0 i
    positivity) (fun i _ => ?_)) hprod
  have he : ((r i / 2 : ℝ) : ℂ) * w i = (r i : ℂ) * (w i / 2) := by push_cast; ring
  have hs : 1 + ‖a i 1‖ * r i / 4 = 1 + ‖a i 1‖ * (r i / 2) / 2 := by ring
  rw [hs]
  simpa only [F, he] using hcoef i

end RHTower.WeilSingularArithmetic
