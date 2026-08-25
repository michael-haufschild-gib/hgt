import GaloisForLFunctions.HTGeometry.PositiveKernelCompletion

open scoped CStarAlgebra

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open UniformSpace

variable {I B : Type*}
    [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

theorem positiveKernelSeparated_one_op_smul (K : PositiveKernelData I B) (x : PositiveKernelSeparated K) :
    (1 : Bᵐᵒᵖ) • x = x := by
  induction x using Quotient.inductionOn with
  | _ x =>
    change Submodule.Quotient.mk (positiveKernelPreRmul x 1) = Submodule.Quotient.mk x
    congr 1
    ext q
    simp [positiveKernelPreRmul_apply]

theorem positiveKernelSeparated_mul_op_smul (K : PositiveKernelData I B) (b c : Bᵐᵒᵖ)
    (x : PositiveKernelSeparated K) :
    (b * c) • x = b • c • x := by
  induction x using Quotient.inductionOn with
  | _ x =>
    change Submodule.Quotient.mk
        (positiveKernelPreRmul x (MulOpposite.unop (b * c))) =
      Submodule.Quotient.mk
        (positiveKernelPreRmul (positiveKernelPreRmul x (MulOpposite.unop c))
          (MulOpposite.unop b))
    rw [MulOpposite.unop_mul]
    congr 1
    ext q
    simp [positiveKernelPreRmul_apply, mul_assoc]

theorem positiveKernelSeparated_add_op_smul (K : PositiveKernelData I B) (b c : Bᵐᵒᵖ)
    (x : PositiveKernelSeparated K) :
    (b + c) • x = b • x + c • x := by
  induction x using Quotient.inductionOn with
  | _ x =>
    change Submodule.Quotient.mk
        (positiveKernelPreRmul x (MulOpposite.unop (b + c))) =
      Submodule.Quotient.mk
        (positiveKernelPreRmul x (MulOpposite.unop b) +
          positiveKernelPreRmul x (MulOpposite.unop c))
    congr 1
    ext q
    simp [positiveKernelPreRmul_apply, mul_add]

theorem positiveKernelSeparated_op_smul_add (K : PositiveKernelData I B) (b : Bᵐᵒᵖ)
    (x y : PositiveKernelSeparated K) :
    b • (x + y) = b • x + b • y := by
  exact map_add (positiveKernelSeparatedRmul K (MulOpposite.unop b)) x y

noncomputable instance positiveKernelSeparatedModule (K : PositiveKernelData I B) :
    Module Bᵐᵒᵖ (PositiveKernelSeparated K) :=
  Module.ofMinimalAxioms
    (positiveKernelSeparated_op_smul_add K)
    (positiveKernelSeparated_add_op_smul K)
    (positiveKernelSeparated_mul_op_smul K)
    (positiveKernelSeparated_one_op_smul K)

theorem positiveKernelCompleted_one_op_smul (K : PositiveKernelData I B) (x : PositiveKernelCompletion K) :
    (1 : Bᵐᵒᵖ) • x = x := by
  refine Completion.induction_on x ?_ ?_
  · exact isClosed_eq (positiveKernelCompletedActionCLM K 1).continuous continuous_id
  · intro x
    change positiveKernelCompletedActionCLM K 1 (x : PositiveKernelCompletion K) = (x : PositiveKernelCompletion K)
    rw [positiveKernelCompletedActionCLM_coe, positiveKernelSeparated_one_op_smul]

theorem positiveKernelCompleted_mul_op_smul (K : PositiveKernelData I B) (b c : Bᵐᵒᵖ)
    (x : PositiveKernelCompletion K) :
    (b * c) • x = b • c • x := by
  refine Completion.induction_on x ?_ ?_
  · exact isClosed_eq (positiveKernelCompletedActionCLM K (b * c)).continuous
      ((positiveKernelCompletedActionCLM K b).continuous.comp
        (positiveKernelCompletedActionCLM K c).continuous)
  · intro x
    change positiveKernelCompletedActionCLM K (b * c) (x : PositiveKernelCompletion K) =
      positiveKernelCompletedActionCLM K b
        (positiveKernelCompletedActionCLM K c (x : PositiveKernelCompletion K))
    rw [positiveKernelCompletedActionCLM_coe, positiveKernelCompletedActionCLM_coe,
      positiveKernelCompletedActionCLM_coe, positiveKernelSeparated_mul_op_smul]

theorem positiveKernelCompleted_add_op_smul (K : PositiveKernelData I B) (b c : Bᵐᵒᵖ)
    (x : PositiveKernelCompletion K) :
    (b + c) • x = b • x + c • x := by
  refine Completion.induction_on x ?_ ?_
  · exact isClosed_eq (positiveKernelCompletedActionCLM K (b + c)).continuous
      ((positiveKernelCompletedActionCLM K b).continuous.add
        (positiveKernelCompletedActionCLM K c).continuous)
  · intro x
    change positiveKernelCompletedActionCLM K (b + c) (x : PositiveKernelCompletion K) =
      positiveKernelCompletedActionCLM K b (x : PositiveKernelCompletion K) +
        positiveKernelCompletedActionCLM K c (x : PositiveKernelCompletion K)
    rw [positiveKernelCompletedActionCLM_coe, positiveKernelCompletedActionCLM_coe,
      positiveKernelCompletedActionCLM_coe, ← Completion.coe_add,
      positiveKernelSeparated_add_op_smul]

theorem positiveKernelCompleted_op_smul_add (K : PositiveKernelData I B) (b : Bᵐᵒᵖ)
    (x y : PositiveKernelCompletion K) :
    b • (x + y) = b • x + b • y := by
  exact map_add (positiveKernelCompletedActionCLM K b) x y

noncomputable instance positiveKernelCompletedModule (K : PositiveKernelData I B) :
    Module Bᵐᵒᵖ (PositiveKernelCompletion K) :=
  Module.ofMinimalAxioms
    (positiveKernelCompleted_op_smul_add K)
    (positiveKernelCompleted_add_op_smul K)
    (positiveKernelCompleted_mul_op_smul K)
    (positiveKernelCompleted_one_op_smul K)

theorem positiveKernelSeparated_smul_op_smul (K : PositiveKernelData I B) (q : ℂ) (b : Bᵐᵒᵖ)
    (x : PositiveKernelSeparated K) :
    (q • b) • x = q • (b • x) := by
  induction x using Quotient.inductionOn with
  | _ x =>
    change Submodule.Quotient.mk
        (positiveKernelPreRmul x (q • MulOpposite.unop b)) =
      Submodule.Quotient.mk (q • positiveKernelPreRmul x (MulOpposite.unop b))
    congr 1
    ext a
    simp [positiveKernelPreRmul_apply]

theorem positiveKernelCompleted_smul_op_smul (K : PositiveKernelData I B) (q : ℂ) (b : Bᵐᵒᵖ)
    (x : PositiveKernelCompletion K) :
    (q • b) • x = q • (b • x) := by
  refine Completion.induction_on x ?_ ?_
  · exact isClosed_eq (positiveKernelCompletedActionCLM K (q • b)).continuous
      ((continuous_const_smul q).comp (positiveKernelCompletedActionCLM K b).continuous)
  · intro x
    change positiveKernelCompletedActionCLM K (q • b) (x : PositiveKernelCompletion K) =
      q • positiveKernelCompletedActionCLM K b (x : PositiveKernelCompletion K)
    rw [positiveKernelCompletedActionCLM_coe, positiveKernelCompletedActionCLM_coe,
      ← Completion.coe_smul, positiveKernelSeparated_smul_op_smul]

/-- Standard `B`-valued right Hilbert-module operations extracted from the opposite-algebra
encoding used by `CStarModule`. -/
noncomputable def positiveKernelRightInnerModuleData (K : PositiveKernelData I B) :
    RightInnerModuleData B (PositiveKernelCompletion K) where
  inner x y := MulOpposite.unop (inner Bᵐᵒᵖ x y)
  rmul x b := MulOpposite.op b • x
  inner_add_right := by
    intro x y z
    rw [CStarModule.inner_add_right (A := Bᵐᵒᵖ) (E := PositiveKernelCompletion K)]
    rfl
  inner_smul_right := by
    intro q x y
    rw [CStarModule.inner_smul_right_complex
      (A := Bᵐᵒᵖ) (E := PositiveKernelCompletion K)]
    rfl
  inner_rmul_right := by
    intro x y b
    rw [CStarModule.inner_op_smul_right
      (A := Bᵐᵒᵖ) (E := PositiveKernelCompletion K)]
    rfl
  star_inner := by
    intro x y
    have h := CStarModule.star_inner (A := Bᵐᵒᵖ) x y
    exact congrArg MulOpposite.unop h
  rmul_one := by
    intro x
    exact positiveKernelCompleted_one_op_smul K x
  rmul_mul := by
    intro x b c
    have h := positiveKernelCompleted_mul_op_smul K (MulOpposite.op c)
      (MulOpposite.op b) x
    simpa using h.symm
  rmul_add_left := by
    intro x y b
    exact positiveKernelCompleted_op_smul_add K (MulOpposite.op b) x y
  rmul_add_right := by
    intro x b c
    exact positiveKernelCompleted_add_op_smul K (MulOpposite.op b)
      (MulOpposite.op c) x
  rmul_smul := by
    intro q x b
    exact map_smul (positiveKernelCompletedActionCLM K (MulOpposite.op b)) q x


end GaloisForLFunctions.HTGeometry
