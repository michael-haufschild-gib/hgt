import GaloisForLFunctions.RHTower.EulerDeletionJointNilpotentWitness
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Tactic

/-!
# Sharp one-fifth boundary for the actual joint deletion product

The fixed six-coordinate target from `EulerDeletionJointNilpotentWitness` retains exactly
one fifth-order word. Subtracting its frozen value from each actual varying-weight block
leaves summable displacement from the identity for every `Re s > 0`.

The finite source product equals the convergent corrected product minus the sum of those
fifth-order coordinates. On the positive real axis that scalar sum is nonsummable when
`s <= 1/5`. Thus the actual source products in this one fixed target converge exactly for
`s > 1/5`. The boundary nonconvergence theorem has no supplied premise.

This controls the actual within-block weights and uses exact finite identities and ordinary
series proofs. No numerical experiment, external certificate, zero assumption, or additional
axiom occurs. The general coprime-modulus extension is separate. No RH implication or
novelty certificate is claimed.
-/

open Filter Topology
open scoped BigOperators Matrix.Norms.Operator
namespace RHTower.DeletionJointSharpness
open GaloisForLFunctions.HTGeometry.NoncommutativeAbel
noncomputable section
local instance : TopologicalSpace A := (inferInstance : NormedRing A).toUniformSpace.toTopologicalSpace

def fifthCoefficient (s : ℂ) (k : ℕ) : ℂ := arithmeticDirichletWeight s (6*k)^5/60

def actualBlock (s : ℂ) (k : ℕ) : A :=
  DeletionJointProduct.variableBlock generatorX generatorY
    (DeletionJointProduct.blockWeights (arithmeticDirichletWeight s) k)

def correctedBlock (s : ℂ) (k : ℕ) : A := actualBlock s k + fifthCoefficient s k • topWord

/-- Removing the exact surviving coordinate leaves precisely the summable freezing error. -/
theorem correctedBlock_error (s : ℂ) (k : ℕ) :
    correctedBlock s k - 1 = actualBlock s k -
      DeletionJointExponential.twoThreeSourceBlock generatorX generatorY
        (arithmeticDirichletWeight s (6*k)) := by
  rw [frozen_source_exact, correctedBlock, fifthCoefficient]
  module

theorem correctedBlock_summable {s : ℂ} (hs : 0 < s.re) :
    Summable (fun k => ‖correctedBlock s k - 1‖) := by
  have hw := arithmeticDirichletWeight_tendsto_zero hs
  have hd := DeletionJointProduct.summable_image_error
    (DeletionJointProduct.analytic_variableBlock generatorX generatorY).contDiffAt
    (DeletionJointProduct.blockWeights_tendsto hw)
    (DeletionJointProduct.frozenWeights_tendsto hw)
    (DeletionJointProduct.summable_block_input_error
      (arithmeticDirichletWeight_summable_variation hs))
  apply hd.congr
  intro k
  rw [correctedBlock_error]
  change ‖actualBlock s k - DeletionJointProduct.variableBlock generatorX generatorY
    (fun _ => arithmeticDirichletWeight s (6*k))‖ = _
  rw [DeletionJointProduct.variableBlock_frozen]

theorem actualBlock_absorbs (s : ℂ) (k : ℕ) :
    actualBlock s k * topWord = topWord ∧ topWord * actualBlock s k = topWord :=
  variableBlock_absorbs_topWord _

theorem correctedBlock_absorbs (s : ℂ) (k : ℕ) :
    correctedBlock s k * topWord = topWord ∧ topWord * correctedBlock s k = topWord := by
  simp only [correctedBlock, add_mul, mul_add, smul_mul_assoc, mul_smul_comm,
    topWord_sq, smul_zero, add_zero, (actualBlock_absorbs s k).1, (actualBlock_absorbs s k).2,
    and_self]

theorem correctedProduct_absorbs (s : ℂ) (N : ℕ) :
    orderedProduct (correctedBlock s) N * topWord = topWord := by
  induction N with
  | zero => simp [orderedProduct]
  | succ N ih =>
    rw [orderedProduct, mul_assoc, (correctedBlock_absorbs s N).1, ih]

/-- Exact finite identity for the original varying-weight blocks. -/
theorem actualProduct_decomposition (s : ℂ) (N : ℕ) :
    orderedProduct (actualBlock s) N = orderedProduct (correctedBlock s) N -
      (∑ k ∈ Finset.range N, fifthCoefficient s k) • topWord := by
  induction N with
  | zero => simp [orderedProduct]
  | succ N ih =>
    rw [orderedProduct, ih, orderedProduct, Finset.sum_range_succ]
    simp only [correctedBlock, sub_mul, mul_add, smul_mul_assoc, mul_smul_comm,
      (actualBlock_absorbs s N).2, correctedProduct_absorbs, add_smul]
    module

theorem correctedProduct_converges {s : ℂ} (hs : 0 < s.re) :
    ∃ V : A, Tendsto (orderedProduct (correctedBlock s)) atTop (nhds V) :=
  orderedProduct_converges (correctedBlock_summable hs)

private theorem weight_real (σ : ℝ) (n : ℕ) :
    arithmeticDirichletWeight (σ:ℂ) n = ((((n:ℝ)+1)^(-σ) : ℝ) : ℂ) := by
  unfold arithmeticDirichletWeight
  rw [← Complex.ofReal_neg, ← Complex.ofReal_cpow (by positivity)]

theorem fifthCoefficient_real (σ : ℝ) (k : ℕ) :
    (fifthCoefficient (σ:ℂ) k).re = (6*(k:ℝ)+1)^(-5*σ)/60 := by
  rw [fifthCoefficient, weight_real]
  have hp : ((((6*k:ℕ):ℝ)+1)^(-σ)) ^ (5:ℕ) = (6*(k:ℝ)+1)^(-5*σ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    push_cast
    congr 1
    norm_num
    ring
  rw [← Complex.ofReal_pow, show (60:ℂ) = ((60:ℝ):ℂ) by norm_num,
    ← Complex.ofReal_div, Complex.ofReal_re, hp]

/-- The scalar obstruction is nonsummable throughout the claimed sharpness interval. -/
theorem not_summable_fifth_mass {σ : ℝ} (hσ : σ ≤ (1:ℝ)/5) :
    ¬ Summable (fun k : ℕ => (6*(k:ℝ)+1)^(-5*σ)) := by
  intro h
  have hb : Summable (fun k : ℕ => 1/((k:ℝ)+1)) := by
    apply Summable.of_nonneg_of_le (fun k => by positivity) _ (h.mul_left 6)
    intro k
    have hbase : (1:ℝ) ≤ 6*(k:ℝ)+1 := by nlinarith [Nat.cast_nonneg k (α := ℝ)]
    have hr := Real.rpow_le_rpow_of_exponent_le hbase (show (-1:ℝ) ≤ -5*σ by linarith)
    rw [Real.rpow_neg_one] at hr
    have hrec : 1/((k:ℝ)+1) ≤ 6*(6*(k:ℝ)+1)⁻¹ := by
      calc
        1/((k:ℝ)+1) = 6/(6*((k:ℝ)+1)) := by field_simp
        _ ≤ 6/(6*(k:ℝ)+1) := by
          gcongr
          nlinarith [Nat.cast_nonneg k (α := ℝ)]
        _ = _ := rfl

    exact hrec.trans (mul_le_mul_of_nonneg_left hr (by norm_num))
  apply Real.not_summable_one_div_natCast
  exact (summable_nat_add_iff 1).1 (by simpa only [Nat.cast_add, Nat.cast_one] using hb)

private def topEntry : A →ₗ[ℂ] ℂ where
  toFun M := M 0 5
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem continuous_topEntry : Continuous topEntry :=
  topEntry.continuous_of_finiteDimensional

/-- The sharpness witness uses the actual source, all positive real parameters up to one fifth. -/
theorem sourceProduct_not_convergent {σ : ℝ} (hpos : 0 < σ) (hσ : σ ≤ (1:ℝ)/5) :
    ¬ ∃ U : A, Tendsto
      (orderedProduct (DeletionJointProduct.sourceFactor generatorX generatorY (σ:ℂ)))
      atTop (nhds U) := by
  rintro ⟨U, hU⟩
  have hA : Tendsto (orderedProduct (actualBlock (σ:ℂ))) atTop (nhds U) := by
    have h := hU.comp (DeletionJointProduct.stride_tendsto 0)
    simp only [Function.comp_def, Nat.add_zero, DeletionJointProduct.sourceProduct_six_mul] at h
    change Tendsto (orderedProduct (actualBlock (σ:ℂ))) atTop (nhds U) at h
    exact h
  obtain ⟨V, hV⟩ := correctedProduct_converges (s := (σ:ℂ)) (by simpa using hpos)
  have hdiff : Tendsto (fun N => topEntry
      (orderedProduct (correctedBlock (σ:ℂ)) N - orderedProduct (actualBlock (σ:ℂ)) N))
      atTop (nhds (topEntry (V-U))) := by
    simpa only [Function.comp_def] using
      (continuous_topEntry.tendsto (V-U)).comp (hV.sub hA)
  have heq (N : ℕ) :
      topEntry (orderedProduct (correctedBlock (σ:ℂ)) N - orderedProduct (actualBlock (σ:ℂ)) N) =
      ∑ k ∈ Finset.range N, fifthCoefficient (σ:ℂ) k := by
    rw [actualProduct_decomposition]
    simp only [sub_sub_cancel, topEntry, LinearMap.coe_mk, AddHom.coe_mk,
      Matrix.smul_apply, smul_eq_mul, topWord_entry, mul_one]
  have ht : Tendsto (fun N => (60:ℝ) * (∑ k ∈ Finset.range N, fifthCoefficient (σ:ℂ) k).re)
      atTop (nhds (60*(topEntry (V-U)).re)) := by
    simpa only [Function.comp_def, heq] using ((Complex.continuous_re.tendsto (topEntry (V-U))).comp hdiff).const_mul (60:ℝ)
  have hscalar (N : ℕ) :
      (60:ℝ)*(∑ k ∈ Finset.range N, fifthCoefficient (σ:ℂ) k).re =
      ∑ k ∈ Finset.range N, (6*(k:ℝ)+1)^(-5*σ) := by
    rw [Complex.re_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    rw [fifthCoefficient_real]
    ring
  simp only [hscalar] at ht
  obtain ⟨M, hM⟩ := ht.bddAbove_range
  apply not_summable_fifth_mass hσ
  exact summable_of_sum_range_le (fun k => by positivity)
    (fun N => hM (Set.mem_range_self N))


/-- Exact convergence classification on the positive real axis for one fixed explicit target. -/
theorem positive_real_convergence_iff (σ : {r : ℝ // 0 < r}) :
    (∃ U : A, Tendsto
      (orderedProduct (DeletionJointProduct.sourceFactor generatorX generatorY (σ.val:ℂ)))
      atTop (nhds U)) ↔ (1:ℝ)/5 < σ.val := by
  constructor
  · intro h
    by_contra hn
    exact sourceProduct_not_convergent σ.property (le_of_not_gt hn) h
  · intro hs
    obtain ⟨U, _, hU⟩ := DeletionJointProduct.sourceProduct_converges_to_unit
      generatorX generatorY (s := (σ.val:ℂ)) (by simpa using hs)
    exact ⟨U, hU⟩

/-- The boundary failure is a closed statement about the literal source, with no supplied premise. -/
theorem oneFifth_sourceProduct_not_convergent :
    ¬ ∃ U : A, Tendsto
      (orderedProduct (DeletionJointProduct.sourceFactor generatorX generatorY ((1/5:ℝ):ℂ)))
      atTop (nhds U) :=
  sourceProduct_not_convergent (by norm_num) le_rfl

end
end RHTower.DeletionJointSharpness
