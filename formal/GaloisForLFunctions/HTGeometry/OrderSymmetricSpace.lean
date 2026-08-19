import GaloisForLFunctions.HTGeometry.BalancedOrderForm

/-!
# The symmetric space of `SL_n(R)`

The symmetric and balanced forms are a linear subspace of the real matrices, and its positive
definite locus is open and convex there.  `SL_n(R)` acts on it by congruence with the inverse of the
regular representation — a left action that preserves symmetry, balancedness and positive
definiteness.

This is the domain that Macbeath's criterion on a convex domain consumes for matrices over an order.

* `orderForms` : the symmetric balanced subspace.
* `orderCone` : its positive definite locus.
* `isOpen_orderCone`, `convex_orderCone` : its topology.
* `orderSmul`, `orderMulAction` : the action of `SL_n(R)`.
* `isFinitelyPresented_of_orderSiegel` : **Macbeath's criterion, over an order.**
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix

variable {nb d : ℕ} {R : Type*} [CommRing R]

/-- The symmetric balanced forms. -/
def orderForms (ω : Module.Basis (Fin d) ℤ R) :
    Submodule ℝ (Matrix (Fin (nb * d)) (Fin (nb * d)) ℝ) :=
  symmMatrices (nb * d) ⊓ balancedSubspace ω

theorem orderForms_le_symm (ω : Module.Basis (Fin d) ℤ R) :
    orderForms (nb := nb) ω ≤ symmMatrices (nb * d) := inf_le_left

/-- The inclusion into the symmetric matrices. -/
def orderToSymm (ω : Module.Basis (Fin d) ℤ R) :
    ↥(orderForms (nb := nb) ω) →ₗ[ℝ] ↥(symmMatrices (nb * d)) :=
  Submodule.inclusion (orderForms_le_symm ω)

theorem continuous_orderToSymm (ω : Module.Basis (Fin d) ℤ R) :
    Continuous (orderToSymm (nb := nb) ω) :=
  Continuous.subtype_mk continuous_subtype_val _

/-- The positive definite locus of the symmetric balanced forms. -/
def orderCone (ω : Module.Basis (Fin d) ℤ R) : Set ↥(orderForms (nb := nb) ω) :=
  {A | ((A : Matrix (Fin (nb * d)) (Fin (nb * d)) ℝ)).PosDef}

theorem orderCone_eq_preimage (ω : Module.Basis (Fin d) ℤ R) :
    orderCone (nb := nb) ω = (orderToSymm ω) ⁻¹' posDefCone (nb * d) := rfl

theorem isOpen_orderCone (ω : Module.Basis (Fin d) ℤ R) :
    IsOpen (orderCone (nb := nb) ω) := by
  rw [orderCone_eq_preimage]
  exact isOpen_posDefCone.preimage (continuous_orderToSymm ω)

theorem convex_orderCone (ω : Module.Basis (Fin d) ℤ R) :
    Convex ℝ (orderCone (nb := nb) ω) := by
  rw [orderCone_eq_preimage]
  exact convex_posDefCone.linear_preimage (orderToSymm ω)

/-- The regular representation of the inverse of a special linear matrix. -/
noncomputable def orderInvRep (ω : Module.Basis (Fin d) ℤ R)
    (M : Matrix.SpecialLinearGroup (Fin nb) R) : Matrix (Fin (nb * d)) (Fin (nb * d)) ℝ :=
  orderRepR ω ((M⁻¹ : Matrix.SpecialLinearGroup (Fin nb) R) : Matrix (Fin nb) (Fin nb) R)

theorem orderInvRep_one (ω : Module.Basis (Fin d) ℤ R) :
    orderInvRep (nb := nb) ω 1 = 1 := by
  rw [orderInvRep, inv_one]
  have : ((1 : Matrix.SpecialLinearGroup (Fin nb) R) : Matrix (Fin nb) (Fin nb) R) = 1 := rfl
  rw [this, orderRepR_one]

theorem orderInvRep_mul (ω : Module.Basis (Fin d) ℤ R)
    (M N : Matrix.SpecialLinearGroup (Fin nb) R) :
    orderInvRep ω (M * N) = orderInvRep ω N * orderInvRep ω M := by
  rw [orderInvRep, orderInvRep, orderInvRep, _root_.mul_inv_rev, Matrix.SpecialLinearGroup.coe_mul,
    orderRepR_mul]

theorem orderInvRep_isUnit (ω : Module.Basis (Fin d) ℤ R)
    (M : Matrix.SpecialLinearGroup (Fin nb) R) : IsUnit (orderInvRep ω M) := by
  refine orderRepR_isUnit ω ?_
  refine (Matrix.isUnit_iff_isUnit_det _).2 ?_
  rw [Matrix.SpecialLinearGroup.det_coe]
  exact isUnit_one

/-- Congruence of a symmetric balanced form by the inverse regular representation. -/
noncomputable def orderConjForm (ω : Module.Basis (Fin d) ℤ R)
    (M : Matrix.SpecialLinearGroup (Fin nb) R) (A : ↥(orderForms (nb := nb) ω)) :
    ↥(orderForms (nb := nb) ω) :=
  ⟨(orderInvRep ω M)ᵀ * (A : Matrix (Fin (nb * d)) (Fin (nb * d)) ℝ) * orderInvRep ω M, by
    refine ⟨?_, balancedSubspace_congr A.2.2 _⟩
    show ((orderInvRep ω M)ᵀ * (A : Matrix (Fin (nb * d)) (Fin (nb * d)) ℝ) * orderInvRep ω M)ᵀ
      = (orderInvRep ω M)ᵀ * (A : Matrix (Fin (nb * d)) (Fin (nb * d)) ℝ) * orderInvRep ω M
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
      mem_symmMatrices_iff.1 A.2.1, Matrix.mul_assoc]⟩

@[simp]
theorem orderConjForm_coe (ω : Module.Basis (Fin d) ℤ R)
    (M : Matrix.SpecialLinearGroup (Fin nb) R) (A : ↥(orderForms (nb := nb) ω)) :
    ((orderConjForm ω M A : ↥(orderForms (nb := nb) ω)) :
        Matrix (Fin (nb * d)) (Fin (nb * d)) ℝ)
      = (orderInvRep ω M)ᵀ * (A : Matrix (Fin (nb * d)) (Fin (nb * d)) ℝ) * orderInvRep ω M := rfl

theorem orderConjForm_one (ω : Module.Basis (Fin d) ℤ R) (A : ↥(orderForms (nb := nb) ω)) :
    orderConjForm ω 1 A = A := by
  refine Subtype.ext ?_
  rw [orderConjForm_coe, orderInvRep_one, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one]

theorem orderConjForm_mul (ω : Module.Basis (Fin d) ℤ R)
    (M N : Matrix.SpecialLinearGroup (Fin nb) R) (A : ↥(orderForms (nb := nb) ω)) :
    orderConjForm ω (M * N) A = orderConjForm ω M (orderConjForm ω N A) := by
  refine Subtype.ext ?_
  rw [orderConjForm_coe, orderConjForm_coe, orderConjForm_coe, orderInvRep_mul,
    Matrix.transpose_mul]
  simp only [Matrix.mul_assoc]

theorem orderConjForm_posDef (ω : Module.Basis (Fin d) ℤ R)
    (M : Matrix.SpecialLinearGroup (Fin nb) R) {A : ↥(orderForms (nb := nb) ω)}
    (hA : ((A : Matrix (Fin (nb * d)) (Fin (nb * d)) ℝ)).PosDef) :
    (((orderConjForm ω M A : ↥(orderForms (nb := nb) ω)) :
      Matrix (Fin (nb * d)) (Fin (nb * d)) ℝ)).PosDef := by
  rw [orderConjForm_coe]
  refine posDef_congr hA fun x hx => ?_
  exact Matrix.mulVec_injective_of_isUnit (orderInvRep_isUnit ω M)
    (by rw [hx, Matrix.mulVec_zero])

/-- The action of `SL_n(R)` on its symmetric space. -/
noncomputable def orderSmul (ω : Module.Basis (Fin d) ℤ R)
    (M : Matrix.SpecialLinearGroup (Fin nb) R) (A : ↥(orderCone (nb := nb) ω)) :
    ↥(orderCone (nb := nb) ω) :=
  ⟨orderConjForm ω M (A : ↥(orderForms (nb := nb) ω)), orderConjForm_posDef ω M A.2⟩

/-- The action as a `MulAction`. -/
@[reducible]
noncomputable def orderMulAction (ω : Module.Basis (Fin d) ℤ R) :
    MulAction (Matrix.SpecialLinearGroup (Fin nb) R) ↥(orderCone (nb := nb) ω) where
  smul := orderSmul ω
  one_smul _ := Subtype.ext (orderConjForm_one ω _)
  mul_smul M N _ := Subtype.ext (orderConjForm_mul ω M N _)

theorem continuous_orderConjForm (ω : Module.Basis (Fin d) ℤ R)
    (M : Matrix.SpecialLinearGroup (Fin nb) R) :
    Continuous (orderConjForm (nb := nb) ω M) := by
  refine Continuous.subtype_mk ?_ _
  exact (continuous_const.matrix_mul continuous_subtype_val).matrix_mul continuous_const

/-- The symmetric balanced forms are locally path connected, being a submodule of a finite product
of copies of `ℝ`. -/
instance locallyPathConnectedSpace_orderForms (ω : Module.Basis (Fin d) ℤ R) :
    LocallyPathConnectedSpace ↥(orderForms (nb := nb) ω) := by
  let S : Submodule ℝ (Fin (nb * d) → Fin (nb * d) → ℝ) := orderForms ω
  exact (inferInstance : LocallyPathConnectedSpace S)

/-- The action is continuous. -/
theorem orderContinuousConstSMul (ω : Module.Basis (Fin d) ℤ R) :
    @ContinuousConstSMul (Matrix.SpecialLinearGroup (Fin nb) R) ↥(orderCone (nb := nb) ω) _
      (orderMulAction ω).toSMul := by
  letI := orderMulAction (nb := nb) ω
  refine ⟨fun M => ?_⟩
  refine Continuous.subtype_mk ?_ _
  exact (continuous_orderConjForm ω M).comp continuous_subtype_val

/-- **`SL_n(R)` is finitely presented as soon as reduction theory over `R` supplies a connected
fundamental open set with finitely many overlaps.**  All the topology is discharged by the symmetric
balanced forms being an open convex subset of a linear space. -/
theorem isFinitelyPresented_of_orderSiegel (ω : Module.Basis (Fin d) ℤ R)
    (hne : (orderCone (nb := nb) ω).Nonempty)
    (V : Set ↥(orderCone (nb := nb) ω)) (hVopen : IsOpen V) (hVne : V.Nonempty)
    (hVconn : IsPreconnected V)
    (hcover : ∀ A : ↥(orderCone (nb := nb) ω),
      ∃ M : Matrix.SpecialLinearGroup (Fin nb) R, orderSmul ω M A ∈ V)
    (hfin : {M : Matrix.SpecialLinearGroup (Fin nb) R | ∃ A ∈ V, orderSmul ω M A ∈ V}.Finite) :
    IsFinitelyPresented (Matrix.SpecialLinearGroup (Fin nb) R) := by
  classical
  letI := orderMulAction (nb := nb) ω
  letI := orderContinuousConstSMul (nb := nb) ω
  refine isFinitelyPresented_of_macbeath_convex (isOpen_orderCone ω) (convex_orderCone ω) hne
    hVopen hVne hVconn ?_ ?_
  · refine Set.eq_univ_of_forall fun A => ?_
    obtain ⟨M, hM⟩ := hcover A
    refine Set.mem_iUnion.2 ⟨M⁻¹, ?_⟩
    rw [Set.mem_smul_set_iff_inv_smul_mem, inv_inv]
    exact hM
  · have hsub : meetSet (G := Matrix.SpecialLinearGroup (Fin nb) R) V
        ⊆ (fun g : Matrix.SpecialLinearGroup (Fin nb) R => g⁻¹) ⁻¹'
          {M : Matrix.SpecialLinearGroup (Fin nb) R | ∃ A ∈ V, orderSmul ω M A ∈ V} := by
      rintro g ⟨B, hB1, hB2⟩
      exact ⟨B, hB2, Set.mem_smul_set_iff_inv_smul_mem.1 hB1⟩
    refine Set.Finite.subset (Set.Finite.preimage ?_ hfin) hsub
    exact fun a _ b _ h => inv_injective h

end GaloisForLFunctions.HTGeometry
