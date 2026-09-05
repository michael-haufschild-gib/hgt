import GaloisForLFunctions.RHTower.EulerDeletionJointExponentialRemainder
import GaloisForLFunctions.RHTower.EulerDeletionNoncommutativeDevelopment
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Tactic

/-!
# Joint moduli-two-and-three deletion products above one fifth

The literal factors are `exp ((n+1)^(-s) • (a₂(n+1) • X + a₃(n+1) • Y))`,
where `aₚ(n) = 1 - p * [p divides n]`. For every complete complex normed unital
algebra and arbitrary `X,Y`, their chronological products converge to a unit whenever
`Re s > 1/5`.

The actual six-factor block has summable displacement from the identity: the frozen
block has a fifth-order remainder, and scalar successive variation controls the error
from freezing. Reversed negated exponentials supply inverses with summable displacement.
Exact regrouping and all six residue limits recover every partial prefix.

No zero condition, commutation, or supplied cancellation is assumed. This proves admission
of the joint arithmetic object on a region containing both sides of the critical line;
it gives neither critical-line selection nor a zero-specific identity for the limit.
The general coprime-family extension and the sharpness witness are separate obligations.
-/

open Filter Topology
open scoped BigOperators
namespace RHTower.DeletionJointProduct
noncomputable section

private theorem weight_norm (s : ℂ) (n : ℕ) :
    ‖arithmeticDirichletWeight s n‖ = ((n:ℝ)+1)^(-s.re) := by
  unfold arithmeticDirichletWeight
  rw [Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
  simp

/-- Fifth-power source mass is summable strictly above the proposed admission boundary. -/
theorem summable_weight_fifth {s : ℂ} (hs : (1:ℝ)/5 < s.re) :
    Summable (fun n => ‖arithmeticDirichletWeight s n‖^5) := by
  have h := (Real.summable_nat_rpow.mpr (show -5*s.re < -1 by linarith)).comp_injective
    Nat.succ_injective
  apply h.congr
  intro n
  simp only [Function.comp_def, Nat.cast_succ, weight_norm]
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  congr 1
  norm_num
  ring

theorem stride_tendsto (c : ℕ) : Tendsto (fun k : ℕ => 6*k+c) atTop atTop := by
  apply tendsto_atTop_mono (fun k => show k ≤ 6*k+c by omega) tendsto_id

/-- Freezing each six-term block introduces summable scalar error at every offset. -/
theorem summable_stride_difference {w : ℕ → ℂ}
    (hw : Summable (fun n => ‖w n-w (n+1)‖)) (c : ℕ) :
    Summable (fun k => ‖w (6*k+c)-w (6*k)‖) := by
  induction c with
  | zero => simp
  | succ c ih =>
    have hstep : Summable (fun k => ‖w (6*k+(c+1))-w (6*k+c)‖) := by
      have h := hw.comp_injective (show Function.Injective (fun k : ℕ => 6*k+c) by
        intro a b hab
        dsimp only at hab
        omega)
      exact h.congr (fun k => by simp only [Function.comp_def, Nat.add_assoc, norm_sub_rev])
    exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k =>
      norm_sub_le_norm_sub_add_norm_sub (w (6*k+(c+1))) (w (6*k+c)) (w (6*k))) (hstep.add ih)

def blockWeights (w : ℕ → ℂ) (k : ℕ) : Fin 6 → ℂ := fun j => w (6*k+j)
def frozenWeights (w : ℕ → ℂ) (k : ℕ) : Fin 6 → ℂ := fun _ => w (6*k)

theorem summable_block_input_error {w : ℕ → ℂ}
    (hw : Summable (fun n => ‖w n-w (n+1)‖)) :
    Summable (fun k => ‖blockWeights w k-frozenWeights w k‖) := by
  have h : Summable (fun k => ∑ j : Fin 6, ‖w (6*k+j)-w (6*k)‖) :=
    summable_sum (fun j _ => summable_stride_difference hw j)
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ h
  intro k
  apply (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg (fun _ _ => norm_nonneg _))).2
  intro j
  exact Finset.single_le_sum (fun _ _ => norm_nonneg _) (Finset.mem_univ j)

theorem blockWeights_tendsto {w : ℕ → ℂ} (hw : Tendsto w atTop (nhds 0)) :
    Tendsto (blockWeights w) atTop (nhds 0) := by
  apply tendsto_pi_nhds.2
  intro j
  exact hw.comp (stride_tendsto j)

theorem frozenWeights_tendsto {w : ℕ → ℂ} (hw : Tendsto w atTop (nhds 0)) :
    Tendsto (frozenWeights w) atTop (nhds 0) := by
  apply tendsto_pi_nhds.2
  intro j
  simpa only [Nat.add_zero, Function.comp_def, frozenWeights, Pi.zero_apply] using hw.comp (stride_tendsto 0)

/-- A fixed differentiable finite block map preserves a summable comparison error near zero. -/
theorem summable_image_error {E A : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup A] [NormedSpace ℂ A] {F : E → A}
    (hF : ContDiffAt ℂ 1 F 0) {u v : ℕ → E}
    (hu : Tendsto u atTop (nhds 0)) (hv : Tendsto v atTop (nhds 0))
    (huv : Summable (fun k => ‖u k-v k‖)) : Summable (fun k => ‖F (u k)-F (v k)‖) := by
  obtain ⟨K, U, hU, hLip⟩ := hF.exists_lipschitzOnWith
  apply Summable.of_norm_bounded_eventually_nat (huv.mul_left (K:ℝ))
  filter_upwards [hu.eventually hU, hv.eventually hU] with k huk hvk
  simpa only [norm_norm] using hLip.norm_sub_le huk hvk

section Algebra
variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]
local instance : NormedAlgebra ℝ A := .restrictScalars ℝ ℂ A

/-- The complete frozen blocks have summable displacement from the unit. -/
theorem summable_frozen_block_error (X Y : A) {s : ℂ} (hs : (1:ℝ)/5 < s.re) :
    Summable (fun k => ‖DeletionJointExponential.twoThreeSourceBlock X Y
      (arithmeticDirichletWeight s (6*k))-1‖) := by
  have hspos : 0 < s.re := by linarith
  have hw : Tendsto (fun k => arithmeticDirichletWeight s (6*k)) atTop (nhds 0) := by
    simpa only [Nat.add_zero, Function.comp_def] using
      (arithmeticDirichletWeight_tendsto_zero hspos).comp (stride_tendsto 0)
  have hsum := (summable_weight_fifth hs).comp_injective
    (show Function.Injective (fun k : ℕ => 6*k) by intro a b hab; dsimp only at hab; omega)
  obtain ⟨C, hC⟩ := Asymptotics.isBigO_iff.mp
    (DeletionJointExponential.twoThreeSourceBlock_remainder X Y)
  apply Summable.of_norm_bounded_eventually_nat (hsum.mul_left C)
  filter_upwards [hw.eventually hC] with k hk
  simpa only [Function.comp_def, norm_pow, norm_norm] using hk

/-- The literal six-coordinate block map before diagonal freezing. -/
def variableBlock (X Y : A) (u : Fin 6 → ℂ) : A :=
  NormedSpace.exp (u 0 • DeletionJointExponential.sourceVelocity 2 3 0 X Y) *
  (NormedSpace.exp (u 1 • DeletionJointExponential.sourceVelocity 2 3 1 X Y) *
  (NormedSpace.exp (u 2 • DeletionJointExponential.sourceVelocity 2 3 2 X Y) *
  (NormedSpace.exp (u 3 • DeletionJointExponential.sourceVelocity 2 3 3 X Y) *
  (NormedSpace.exp (u 4 • DeletionJointExponential.sourceVelocity 2 3 4 X Y) *
  NormedSpace.exp (u 5 • DeletionJointExponential.sourceVelocity 2 3 5 X Y)))))

theorem analytic_variableBlock (X Y : A) : AnalyticAt ℂ (variableBlock X Y) 0 := by
  have h (j : Fin 6) (v : A) :
      AnalyticAt ℂ (fun u : Fin 6 → ℂ => NormedSpace.exp (u j • v)) 0 := by
    have hl : AnalyticAt ℂ (fun u : Fin 6 → ℂ => u j • v) 0 := by
      exact ((ContinuousLinearMap.proj j : (Fin 6 → ℂ) →L[ℂ] ℂ).smulRight v).analyticAt 0
    exact (NormedSpace.exp_analytic (𝕂 := ℂ) ((0 : Fin 6 → ℂ) j • v)).comp
      (f := fun u : Fin 6 → ℂ => u j • v) hl
  exact (h 0 _).mul ((h 1 _).mul ((h 2 _).mul ((h 3 _).mul ((h 4 _).mul (h 5 _)))))

omit [CompleteSpace A] in
theorem variableBlock_frozen (X Y : A) (z : ℂ) :
    variableBlock X Y (fun _ => z) = DeletionJointExponential.twoThreeSourceBlock X Y z := by
  simp [variableBlock, DeletionJointExponential.twoThreeSourceBlock,
    DeletionJointExponential.exponentialWord, List.range_succ]

/-- Summability for the actual within-block weights, not only their frozen approximation. -/
theorem summable_actual_block_error (X Y : A) {s : ℂ} (hs : (1:ℝ)/5 < s.re) :
    Summable (fun k => ‖variableBlock X Y (blockWeights (arithmeticDirichletWeight s) k)-1‖) := by
  have hspos : 0 < s.re := by linarith
  have hw := arithmeticDirichletWeight_tendsto_zero hspos
  have hvar := arithmeticDirichletWeight_summable_variation hspos
  have hdiff := summable_image_error (analytic_variableBlock X Y).contDiffAt
    (blockWeights_tendsto hw) (frozenWeights_tendsto hw) (summable_block_input_error hvar)
  have hfrozen : Summable (fun k =>
      ‖variableBlock X Y (frozenWeights (arithmeticDirichletWeight s) k)-1‖) := by
    change Summable (fun k => ‖variableBlock X Y (fun _ => arithmeticDirichletWeight s (6*k))-1‖)
    simp_rw [variableBlock_frozen]
    exact summable_frozen_block_error X Y hs
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ (hdiff.add hfrozen)
  intro k
  calc
    _ = ‖(variableBlock X Y (blockWeights (arithmeticDirichletWeight s) k) -
          variableBlock X Y (frozenWeights (arithmeticDirichletWeight s) k)) +
          (variableBlock X Y (frozenWeights (arithmeticDirichletWeight s) k)-1)‖ := by
      congr 1
      abel
    _ ≤ _ := norm_add_le _ _

def inverseVariableBlock (X Y : A) (u : Fin 6 → ℂ) : A :=
  NormedSpace.exp (-(u 5 • DeletionJointExponential.sourceVelocity 2 3 5 X Y)) *
  (NormedSpace.exp (-(u 4 • DeletionJointExponential.sourceVelocity 2 3 4 X Y)) *
  (NormedSpace.exp (-(u 3 • DeletionJointExponential.sourceVelocity 2 3 3 X Y)) *
  (NormedSpace.exp (-(u 2 • DeletionJointExponential.sourceVelocity 2 3 2 X Y)) *
  (NormedSpace.exp (-(u 1 • DeletionJointExponential.sourceVelocity 2 3 1 X Y)) *
  NormedSpace.exp (-(u 0 • DeletionJointExponential.sourceVelocity 2 3 0 X Y))))))

private theorem exp_cancel_pos (x y : A) :
    NormedSpace.exp x * (NormedSpace.exp (-x) * y) = y := by
  rw [← mul_assoc, GaloisForLFunctions.HTGeometry.NoncommutativeAbel.exp_mul_neg, one_mul]

private theorem exp_cancel_neg (x y : A) :
    NormedSpace.exp (-x) * (NormedSpace.exp x * y) = y := by
  rw [← mul_assoc, GaloisForLFunctions.HTGeometry.NoncommutativeAbel.exp_neg_mul, one_mul]

theorem variableBlock_inverse_pair (X Y : A) (u : Fin 6 → ℂ) :
    variableBlock X Y u * inverseVariableBlock X Y u = 1 ∧
    inverseVariableBlock X Y u * variableBlock X Y u = 1 := by
  constructor
  · simp only [variableBlock, inverseVariableBlock, mul_assoc, exp_cancel_pos,
      GaloisForLFunctions.HTGeometry.NoncommutativeAbel.exp_mul_neg]
  · simp only [variableBlock, inverseVariableBlock, mul_assoc, exp_cancel_neg,
      GaloisForLFunctions.HTGeometry.NoncommutativeAbel.exp_neg_mul]

theorem inverseVariableBlock_tendsto (X Y : A) {w : ℕ → ℂ}
    (hw : Tendsto w atTop (nhds 0)) :
    Tendsto (fun k => inverseVariableBlock X Y (blockWeights w k)) atTop (nhds 1) := by
  have h (j : ℕ) (v : A) :
      Tendsto (fun k => NormedSpace.exp (-(w (6*k+j) • v))) atTop (nhds 1) := by
    have hz : Tendsto (fun k => -(w (6*k+j) • v)) atTop (nhds (0:A)) := by
      simpa only [Function.comp_def, zero_smul, neg_zero] using
        (((hw.comp (stride_tendsto j)).smul (tendsto_const_nhds (x := v))).neg)
    simpa only [NormedSpace.exp_zero, Function.comp_def] using
      (NormedSpace.exp_analytic (𝕂 := ℂ) (0:A)).continuousAt.tendsto.comp hz
  simpa [inverseVariableBlock, blockWeights] using
    (h 5 _).mul ((h 4 _).mul ((h 3 _).mul ((h 2 _).mul ((h 1 _).mul (h 0 _)))))

/-- Actual complete blocks converge to a unit; both inverse identities survive the limit. -/
theorem actual_blocks_converge_to_unit [NormOneClass A] (X Y : A) {s : ℂ}
    (hs : (1:ℝ)/5 < s.re) :
    ∃ U : A, IsUnit U ∧ Tendsto
      (GaloisForLFunctions.HTGeometry.NoncommutativeAbel.orderedProduct
        (fun k => variableBlock X Y (blockWeights (arithmeticDirichletWeight s) k)))
      atTop (nhds U) := by
  let f := fun k => variableBlock X Y (blockWeights (arithmeticDirichletWeight s) k)
  let g := fun k => inverseVariableBlock X Y (blockWeights (arithmeticDirichletWeight s) k)
  have hf : Summable (fun k => ‖f k-1‖) := summable_actual_block_error X Y hs
  have hg : Tendsto g atTop (nhds 1) := inverseVariableBlock_tendsto X Y
    (arithmeticDirichletWeight_tendsto_zero (by linarith))
  obtain ⟨M, hM⟩ := hg.norm.bddAbove_range
  have hsumg : Summable (fun k => ‖g k-1‖) := by
    apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ (hf.mul_left (max M 0))
    intro k
    have hgf : g k*f k = 1 := (variableBlock_inverse_pair X Y _).2
    calc
      ‖g k-1‖ = ‖g k*(1-f k)‖ := by rw [mul_sub, mul_one, hgf]
      _ ≤ ‖g k‖*‖1-f k‖ := norm_mul_le _ _
      _ ≤ max M 0 * ‖f k-1‖ := by
        rw [norm_sub_rev (1:A) (f k)]
        exact mul_le_mul_of_nonneg_right
          ((hM (Set.mem_range_self k)).trans (le_max_left M 0)) (norm_nonneg _)
  exact GaloisForLFunctions.HTGeometry.NoncommutativeAbel.orderedProduct_converges_to_unit
    hf hsumg (fun k => (variableBlock_inverse_pair X Y _).1)
    (fun k => (variableBlock_inverse_pair X Y _).2)

open GaloisForLFunctions.HTGeometry.NoncommutativeAbel

omit [CompleteSpace A] in
/-- The source coefficients, not just the assigned six-letter list, repeat every six steps. -/
theorem sourceVelocity_stride (X Y : A) (k j : ℕ) :
    DeletionJointExponential.sourceVelocity 2 3 (6*k+j) X Y =
      DeletionJointExponential.sourceVelocity 2 3 j X Y := by
  have h2 : blockDeletionCoefficient 2 (6*k+j+1) = blockDeletionCoefficient 2 (j+1) := by
    have h := (DeletionCoprimeWords.shifted_deletion_periodic 2).nat_mul (3*k) j
    simp only [Nat.cast_id] at h
    convert h using 1
    congr 1
    omega
  have h3 : blockDeletionCoefficient 3 (6*k+j+1) = blockDeletionCoefficient 3 (j+1) := by
    have h := (DeletionCoprimeWords.shifted_deletion_periodic 3).nat_mul (2*k) j
    simp only [Nat.cast_id] at h
    convert h using 1
    congr 1
    omega
  simp only [DeletionJointExponential.sourceVelocity, h2, h3]

omit [NormedAlgebra ℂ A] [CompleteSpace A] in
private theorem orderedProduct_add (f : ℕ → A) (m n : ℕ) :
    orderedProduct f (m+n) = orderedProduct f m * orderedProduct (fun j => f (m+j)) n := by
  induction n with
  | zero => simp [orderedProduct]
  | succ n ih =>
    change orderedProduct f (m+n) * f (m+n) =
      orderedProduct f m * (orderedProduct (fun j => f (m+j)) n * f (m+n))
    rw [ih, mul_assoc]

/-- The actual chronological exponential factors with one-based Dirichlet weights. -/
def sourceFactor (X Y : A) (s : ℂ) (n : ℕ) : A :=
  NormedSpace.exp (arithmeticDirichletWeight s n •
    DeletionJointExponential.sourceVelocity 2 3 n X Y)

theorem sourceFactor_stride (X Y : A) (s : ℂ) (k j : ℕ) :
    sourceFactor X Y s (6*k+j) = NormedSpace.exp (arithmeticDirichletWeight s (6*k+j) •
      DeletionJointExponential.sourceVelocity 2 3 j X Y) := by
  rw [sourceFactor, sourceVelocity_stride]

theorem sourceFactor_six (X Y : A) (s : ℂ) (k : ℕ) :
    orderedProduct (fun j => sourceFactor X Y s (6*k+j)) 6 =
      variableBlock X Y (blockWeights (arithmeticDirichletWeight s) k) := by
  have h0 := sourceFactor_stride X Y s k 0
  simp only [Nat.add_zero] at h0
  simp [orderedProduct, sourceFactor_stride, variableBlock, blockWeights, mul_assoc, h0]

/-- Regrouping preserves exactly the source order. -/
theorem sourceProduct_six_mul (X Y : A) (s : ℂ) (k : ℕ) :
    orderedProduct (sourceFactor X Y s) (6*k) =
      orderedProduct (fun k => variableBlock X Y (blockWeights (arithmeticDirichletWeight s) k)) k := by
  induction k with
  | zero => simp [orderedProduct]
  | succ k ih =>
    rw [Nat.mul_succ, orderedProduct_add, ih, sourceFactor_six, orderedProduct]

theorem sourceFactor_stride_tendsto (X Y : A) {s : ℂ} (hs : 0 < s.re) (j : ℕ) :
    Tendsto (fun k => sourceFactor X Y s (6*k+j)) atTop (nhds 1) := by
  have hz : Tendsto (fun k => arithmeticDirichletWeight s (6*k+j) •
      DeletionJointExponential.sourceVelocity 2 3 j X Y) atTop (nhds (0:A)) := by
    simpa only [Function.comp_def, zero_smul] using
      ((arithmeticDirichletWeight_tendsto_zero hs).comp (stride_tendsto j)).smul
        (tendsto_const_nhds (x := DeletionJointExponential.sourceVelocity 2 3 j X Y))
  simpa only [Function.comp_def, sourceFactor_stride, NormedSpace.exp_zero] using
    (NormedSpace.exp_analytic (𝕂 := ℂ) (0:A)).continuousAt.tendsto.comp hz

/-- Every fixed unfinished block tends to the identity. -/
theorem unfinishedBlock_tendsto (X Y : A) {s : ℂ} (hs : 0 < s.re) (r : ℕ) :
    Tendsto (fun k => orderedProduct (fun j => sourceFactor X Y s (6*k+j)) r)
      atTop (nhds 1) := by
  induction r with
  | zero => simpa only [orderedProduct] using (tendsto_const_nhds (x := (1:A)))
  | succ r ih =>
    simpa only [orderedProduct, one_mul] using ih.mul (sourceFactor_stride_tendsto X Y hs r)

omit [NormedAlgebra ℂ A] [CompleteSpace A] in
/-- Finitely many residue limits determine the full sequence limit. -/
private theorem tendsto_of_six_residues {f : ℕ → A} {U : A}
    (h : ∀ r : Fin 6, Tendsto (fun k => f (6*k+r)) atTop (nhds U)) :
    Tendsto f atTop (nhds U) := by
  rw [Filter.tendsto_def]
  intro S hS
  have he : ∀ᶠ k in atTop, ∀ r : Fin 6, f (6*k+r) ∈ S :=
    Filter.eventually_all.2 (fun r => (h r).eventually hS)
  obtain ⟨K, hK⟩ := Filter.eventually_atTop.1 he
  apply Filter.eventually_atTop.2
  refine ⟨6*K, ?_⟩
  intro N hN
  have hk : K ≤ N/6 := by omega
  have hr : N%6 < 6 := Nat.mod_lt N (by norm_num)
  have heq : 6*(N/6)+N%6 = N := by omega
  simpa only [heq] using hK (N/6) hk (⟨N%6, hr⟩ : Fin 6)

/-- The literal joint source product converges to a unit throughout `Re s > 1/5`.
No zero condition and no commutativity or cancellation premise is supplied. -/
theorem sourceProduct_converges_to_unit [NormOneClass A] (X Y : A) {s : ℂ}
    (hs : (1:ℝ)/5 < s.re) :
    ∃ U : A, IsUnit U ∧ Tendsto (orderedProduct (sourceFactor X Y s)) atTop (nhds U) := by
  obtain ⟨U, hunit, hU⟩ := actual_blocks_converge_to_unit X Y hs
  refine ⟨U, hunit, tendsto_of_six_residues (fun r => ?_)⟩
  have hb : Tendsto (fun k => orderedProduct (sourceFactor X Y s) (6*k)) atTop (nhds U) := by
    simpa only [sourceProduct_six_mul] using hU
  have hh := hb.mul (unfinishedBlock_tendsto X Y (by linarith : 0 < s.re) r)
  simpa only [← orderedProduct_add, mul_one] using hh

end Algebra
end
end RHTower.DeletionJointProduct
