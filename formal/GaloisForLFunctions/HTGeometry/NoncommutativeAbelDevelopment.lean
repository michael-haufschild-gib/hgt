import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Topology.Algebra.Algebra

/-!
# Chronological noncommutative Abel development

For real coefficients with bounded partial sums and an algebra-valued sequence tending to zero
with summable successive differences, the chronological product of their exponentials converges
to a unit in any complete real normed algebra. No commutation between different times is assumed.

The exact finite factorization replaces each step by an exponential seam and retains its final
boundary factor. Both seam products and their reverse-ordered inverses converge. The theorem is
about existence and invertibility of the completed history, not triviality of its limit.
-/

noncomputable section
open Filter Topology
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry.NoncommutativeAbel

def orderedProduct {A : Type*} [Monoid A] (f : ℕ → A) : ℕ → A
  | 0 => 1
  | n + 1 => orderedProduct f n * f n

theorem orderedProduct_map {A B : Type*} [Monoid A] [Monoid B]
    (φ : A →* B) (f : ℕ → A) (N : ℕ) :
    φ (orderedProduct f N) = orderedProduct (fun n => φ (f n)) N := by
  induction N with
  | zero => exact map_one φ
  | succ N ih => simp only [orderedProduct, map_mul, ih]

section Product
variable {A : Type*} [NormedRing A] [NormOneClass A] [CompleteSpace A]

omit [CompleteSpace A] in
theorem orderedProduct_norm_le (f : ℕ → A) (N : ℕ) :
    ‖orderedProduct f N‖ ≤ Real.exp (∑ n ∈ Finset.range N, ‖f n - 1‖) := by
  induction N with
  | zero => simp [orderedProduct]
  | succ N ih =>
    have hf : ‖f N‖ ≤ Real.exp ‖f N - 1‖ := by
      calc
        ‖f N‖ = ‖(f N - 1) + 1‖ := by rw [sub_add_cancel]
        _ ≤ ‖f N - 1‖ + ‖(1 : A)‖ := norm_add_le _ _
        _ ≤ Real.exp ‖f N - 1‖ := by simpa using Real.add_one_le_exp ‖f N - 1‖
    calc
      ‖orderedProduct f (N + 1)‖ ≤ ‖orderedProduct f N‖ * ‖f N‖ := norm_mul_le _ _
      _ ≤ Real.exp (∑ n ∈ Finset.range N, ‖f n - 1‖) * Real.exp ‖f N - 1‖ :=
        mul_le_mul ih hf (norm_nonneg _) (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add, Finset.sum_range_succ]

theorem orderedProduct_converges {f : ℕ → A}
    (hf : Summable (fun n => ‖f n - 1‖)) :
    ∃ P : A, Tendsto (orderedProduct f) atTop (nhds P) := by
  let C := Real.exp (∑' n, ‖f n - 1‖)
  have hbound (n : ℕ) : ‖orderedProduct f n‖ ≤ C :=
    (orderedProduct_norm_le f n).trans
      (Real.exp_le_exp.mpr (hf.sum_le_tsum (Finset.range n) (fun _ _ => norm_nonneg _)))
  apply cauchySeq_tendsto_of_complete
  apply cauchySeq_of_summable_dist
  apply Summable.of_nonneg_of_le (fun n => dist_nonneg) (fun n => ?_) (hf.mul_left C)
  rw [dist_eq_norm, norm_sub_rev]
  change ‖orderedProduct f n * f n - orderedProduct f n‖ ≤ C * ‖f n - 1‖
  rw [show orderedProduct f n * f n - orderedProduct f n =
    orderedProduct f n * (f n - 1) by rw [mul_sub, mul_one]]
  exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (hbound n) (norm_nonneg _))

omit [NormOneClass A] [CompleteSpace A] in
theorem orderedProduct_inverse_pair (f g : ℕ → A)
    (hfg : ∀ n, f n * g n = 1) (hgf : ∀ n, g n * f n = 1) (N : ℕ) :
    orderedProduct f N * MulOpposite.unop (orderedProduct (fun n => MulOpposite.op (g n)) N) = 1 ∧
    MulOpposite.unop (orderedProduct (fun n => MulOpposite.op (g n)) N) * orderedProduct f N = 1 := by
  induction N with
  | zero => simp [orderedProduct]
  | succ N ih =>
    simp only [orderedProduct, MulOpposite.unop_mul, MulOpposite.unop_op]
    constructor
    · calc
        _ = (orderedProduct f N * (f N * g N)) *
            MulOpposite.unop (orderedProduct (fun n => MulOpposite.op (g n)) N) := by
              simp only [mul_assoc]
        _ = 1 := by rw [hfg, mul_one, ih.1]
    · calc
        _ = g N *
            (MulOpposite.unop (orderedProduct (fun n => MulOpposite.op (g n)) N) *
              orderedProduct f N) * f N := by simp only [mul_assoc]
        _ = 1 := by rw [ih.2, mul_one, hgf]

theorem orderedProduct_converges_to_unit {f g : ℕ → A}
    (hf : Summable (fun n => ‖f n - 1‖)) (hg : Summable (fun n => ‖g n - 1‖))
    (hfg : ∀ n, f n * g n = 1) (hgf : ∀ n, g n * f n = 1) :
    ∃ P : A, IsUnit P ∧ Tendsto (orderedProduct f) atTop (nhds P) := by
  obtain ⟨P, hP⟩ := orderedProduct_converges hf
  have hgop : Summable (fun n => ‖MulOpposite.op (g n) - 1‖) := by
    simpa only [← MulOpposite.op_one, ← MulOpposite.op_sub, MulOpposite.norm_op] using hg
  obtain ⟨Qop, hQop⟩ := orderedProduct_converges hgop
  let Q := MulOpposite.unop Qop
  have hQ : Tendsto
      (fun n => MulOpposite.unop (orderedProduct (fun n => MulOpposite.op (g n)) n))
      atTop (nhds Q) := MulOpposite.continuous_unop.tendsto Qop |>.comp hQop
  have hPQ : P * Q = 1 := by
    apply tendsto_nhds_unique (hP.mul hQ)
    have heq : (fun N => orderedProduct f N *
        MulOpposite.unop (orderedProduct (fun n => MulOpposite.op (g n)) N)) =
        fun _ => (1 : A) := funext (fun N => (orderedProduct_inverse_pair f g hfg hgf N).1)
    rw [heq]
    exact tendsto_const_nhds
  have hQP : Q * P = 1 := by
    apply tendsto_nhds_unique (hQ.mul hP)
    have heq : (fun N => MulOpposite.unop
        (orderedProduct (fun n => MulOpposite.op (g n)) N) * orderedProduct f N) =
        fun _ => (1 : A) := funext (fun N => (orderedProduct_inverse_pair f g hfg hgf N).2)
    rw [heq]
    exact tendsto_const_nhds
  exact ⟨P, ⟨⟨P, Q, hPQ, hQP⟩, rfl⟩, hP⟩

end Product

section Exponential
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

local instance : NormedAlgebra ℚ A := .restrictScalars ℚ ℝ A

theorem exp_mul_neg (x : A) :
    NormedSpace.exp x * NormedSpace.exp (-x) = 1 := by
  rw [← NormedSpace.exp_add_of_commute (Commute.refl x).neg_right,
    add_neg_cancel, NormedSpace.exp_zero]

theorem exp_neg_mul (x : A) :
    NormedSpace.exp (-x) * NormedSpace.exp x = 1 := by
  rw [← NormedSpace.exp_add_of_commute (Commute.refl x).neg_left,
    neg_add_cancel, NormedSpace.exp_zero]

theorem summable_exponential_seam {x y : ℕ → A}
    (hx : Tendsto x atTop (nhds 0)) (hy : Tendsto y atTop (nhds 0))
    (hd : Summable (fun n => ‖x n - y n‖)) :
    Summable (fun n => ‖NormedSpace.exp (x n) * NormedSpace.exp (-y n) - 1‖) := by
  have hc : ContDiffAt ℝ 1 (NormedSpace.exp : A → A) 0 :=
    (NormedSpace.exp_analytic (𝕂 := ℝ) (0 : A)).contDiffAt
  obtain ⟨K, U, hU, hLip⟩ := hc.exists_lipschitzOnWith
  have he : Tendsto (fun n => ‖NormedSpace.exp (-y n)‖) atTop (nhds ‖(1 : A)‖) := by
    simpa using ((NormedSpace.exp_continuous.tendsto (0 : A)).comp
      (show Tendsto (fun n => -y n) atTop (nhds (0 : A)) by simpa using hy.neg)).norm
  obtain ⟨M, hM⟩ := he.bddAbove_range
  apply Summable.of_norm_bounded_eventually_nat (hd.mul_left ((K : ℝ) * max M 0))
  filter_upwards [hx.eventually hU, hy.eventually hU] with n hxn hyn
  rw [norm_norm]
  have heq : NormedSpace.exp (x n) * NormedSpace.exp (-y n) - 1 =
      (NormedSpace.exp (x n) - NormedSpace.exp (y n)) * NormedSpace.exp (-y n) := by
    rw [sub_mul, exp_mul_neg]
  rw [heq]
  calc
    ‖(NormedSpace.exp (x n) - NormedSpace.exp (y n)) * NormedSpace.exp (-y n)‖ ≤
        ‖NormedSpace.exp (x n) - NormedSpace.exp (y n)‖ * ‖NormedSpace.exp (-y n)‖ :=
      norm_mul_le _ _
    _ ≤ ((K : ℝ) * ‖x n - y n‖) * max M 0 :=
      mul_le_mul (hLip.norm_sub_le hxn hyn)
        ((hM (Set.mem_range_self n)).trans (le_max_left M 0))
        (norm_nonneg _) (by positivity)
    _ = _ := by ring

omit [CompleteSpace A] in
theorem tendsto_bounded_smul_zero {r : ℕ → ℝ} {b : ℕ → A} {C : ℝ}
    (hr : ∀ n, |r n| ≤ C) (hb : Tendsto b atTop (nhds 0)) :
    Tendsto (fun n => r n • b n) atTop (nhds 0) := by
  apply squeeze_zero_norm (fun n => ?_)
    (show Tendsto (fun n => C * ‖b n‖) atTop (nhds 0) by simpa using hb.norm.const_mul C)
  rw [norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (hr n) (norm_nonneg _)

def coefficientSum (a : ℕ → ℝ) (n : ℕ) : ℝ := ∑ k ∈ Finset.range n, a k

theorem coefficientSum_succ (a : ℕ → ℝ) (n : ℕ) :
    coefficientSum a (n + 1) = coefficientSum a n + a n := by
  exact Finset.sum_range_succ _ _

def abelSeam (a : ℕ → ℝ) (b : ℕ → A) (n : ℕ) : A :=
  NormedSpace.exp (coefficientSum a (n + 1) • b n) *
    NormedSpace.exp (-(coefficientSum a (n + 1) • b (n + 1)))

theorem orderedProduct_abel_factorization (a : ℕ → ℝ) (b : ℕ → A) (N : ℕ) :
    orderedProduct (fun n => NormedSpace.exp (a n • b n)) N =
      orderedProduct (abelSeam a b) N * NormedSpace.exp (coefficientSum a N • b N) := by
  induction N with
  | zero => simp [orderedProduct, coefficientSum]
  | succ N ih =>
    rw [orderedProduct, ih, mul_assoc]
    rw [← NormedSpace.exp_add_of_commute
      (((Commute.refl (b N)).smul_left (coefficientSum a N)).smul_right (a N)),
      ← add_smul, ← coefficientSum_succ]
    rw [orderedProduct, abelSeam, mul_assoc, mul_assoc, exp_neg_mul, mul_one]

theorem summable_abelSeam {a : ℕ → ℝ} {b : ℕ → A} {C : ℝ}
    (ha : ∀ n, |coefficientSum a n| ≤ C)
    (hb : Tendsto b atTop (nhds 0))
    (hd : Summable (fun n => ‖b n - b (n + 1)‖)) :
    Summable (fun n => ‖abelSeam a b n - 1‖) := by
  apply summable_exponential_seam
    (tendsto_bounded_smul_zero (fun n => ha (n + 1)) hb)
    (tendsto_bounded_smul_zero (fun n => ha (n + 1))
      (hb.comp (tendsto_add_atTop_nat 1)))
  apply Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_) (hd.mul_left C)
  rw [← smul_sub, norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (ha (n + 1)) (norm_nonneg _)

theorem ordered_exponential_converges [NormOneClass A]
    {a : ℕ → ℝ} {b : ℕ → A} {C : ℝ}
    (ha : ∀ n, |coefficientSum a n| ≤ C)
    (hb : Tendsto b atTop (nhds 0))
    (hd : Summable (fun n => ‖b n - b (n + 1)‖)) :
    ∃ P : A, Tendsto (orderedProduct (fun n => NormedSpace.exp (a n • b n)))
      atTop (nhds P) := by
  obtain ⟨P, hP⟩ := orderedProduct_converges (summable_abelSeam ha hb hd)
  have hlast := (NormedSpace.exp_continuous.tendsto (0 : A)).comp
    (tendsto_bounded_smul_zero ha hb)
  refine ⟨P, ?_⟩
  simpa only [Function.comp_def, NormedSpace.exp_zero, mul_one,
      ← orderedProduct_abel_factorization]
    using hP.mul hlast

theorem ordered_exponential_converges_to_unit [NormOneClass A]
    {a : ℕ → ℝ} {b : ℕ → A} {C : ℝ}
    (ha : ∀ n, |coefficientSum a n| ≤ C)
    (hb : Tendsto b atTop (nhds 0))
    (hd : Summable (fun n => ‖b n - b (n + 1)‖)) :
    ∃ P : A, IsUnit P ∧
      Tendsto (orderedProduct (fun n => NormedSpace.exp (a n • b n))) atTop (nhds P) := by
  let x : ℕ → A := fun n => coefficientSum a (n + 1) • b n
  let y : ℕ → A := fun n => coefficientSum a (n + 1) • b (n + 1)
  let g : ℕ → A := fun n => NormedSpace.exp (y n) * NormedSpace.exp (-x n)
  have hx := tendsto_bounded_smul_zero (fun n => ha (n + 1)) hb
  have hy := tendsto_bounded_smul_zero (fun n => ha (n + 1))
    (hb.comp (tendsto_add_atTop_nat 1))
  have hxy : Summable (fun n => ‖x n - y n‖) := by
    apply Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_) (hd.mul_left C)
    dsimp [x, y]
    rw [← smul_sub, norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (ha (n + 1)) (norm_nonneg _)
  have hg : Summable (fun n => ‖g n - 1‖) :=
    summable_exponential_seam hy hx (by simpa only [norm_sub_rev] using hxy)
  have hfg (n : ℕ) : abelSeam a b n * g n = 1 := by
    change (NormedSpace.exp (x n) * NormedSpace.exp (-y n)) *
      (NormedSpace.exp (y n) * NormedSpace.exp (-x n)) = 1
    calc
      _ = NormedSpace.exp (x n) *
          (NormedSpace.exp (-y n) * NormedSpace.exp (y n)) * NormedSpace.exp (-x n) := by
            simp only [mul_assoc]
      _ = 1 := by rw [exp_neg_mul, mul_one, exp_mul_neg]
  have hgf (n : ℕ) : g n * abelSeam a b n = 1 := by
    change (NormedSpace.exp (y n) * NormedSpace.exp (-x n)) *
      (NormedSpace.exp (x n) * NormedSpace.exp (-y n)) = 1
    calc
      _ = NormedSpace.exp (y n) *
          (NormedSpace.exp (-x n) * NormedSpace.exp (x n)) * NormedSpace.exp (-y n) := by
            simp only [mul_assoc]
      _ = 1 := by rw [exp_neg_mul, mul_one, exp_mul_neg]
  obtain ⟨P, hunit, hP⟩ := orderedProduct_converges_to_unit (summable_abelSeam ha hb hd) hg hfg hgf
  have hlast := (NormedSpace.exp_continuous.tendsto (0 : A)).comp
    (tendsto_bounded_smul_zero ha hb)
  refine ⟨P, hunit, ?_⟩
  simpa only [Function.comp_def, NormedSpace.exp_zero, mul_one,
      ← orderedProduct_abel_factorization] using hP.mul hlast

end Exponential
end GaloisForLFunctions.HTGeometry.NoncommutativeAbel

