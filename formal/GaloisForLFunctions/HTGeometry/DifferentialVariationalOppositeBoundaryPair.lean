import GaloisForLFunctions.HTGeometry.CompletedPseudoDiffOpBoundedSplitting

/-!
# The canonical attracting and repelling subspaces are opposite

The canonical variational action of a differential field automorphism `σ` is an additive
automorphism of the completed coordinate space, semilinear for coefficient transport, which
preserves the valuation ring and fixes the uniformizer
(`DifferentialFieldAut.isUniformizerSemilinear_vecBuildingActionEquiv`).  The general splitting
theorem `DiffOp.forwardBoundedSubspace_sup_inv_eq_top` therefore applies to it.

A vector with bounded forward orbit has non-positive growth rate, so it lies in the canonical
attracting core; a vector with bounded backward orbit lies in the canonical repelling core.  Hence

```text
variationalAttractingSubspace_sup_variationalRepellingSubspace_eq_top
    F ⊔ G = ⊤
```

the canonical attracting subspace and the canonical repelling subspace span the coordinate space:
the boundary pair of the variational building is **opposite**.
-/

open Filter

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {C K : Type*} [Field C] [Field K] [Algebra C K] [Differential K]
  [IsConstantBase C K]

attribute [local instance] DiffOp.completedPseudoDiffOpIntegerSMul

/-- The canonical variational action as an additive automorphism of the completed coordinate
space. -/
def DifferentialFieldAut.vecBuildingActionEquiv (σ : DifferentialFieldAut C K) {r : ℕ}
    (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K)) :
    (Fin r → DiffOp.CompletedPseudoDiffOp K) ≃ₗ[ℤ] (Fin r → DiffOp.CompletedPseudoDiffOp K) :=
  AddEquiv.toIntLinearEquiv
    { toFun := σ.vecBuildingAction b
      invFun := σ⁻¹.vecBuildingAction b
      left_inv := fun v => by
        rw [← DifferentialFieldAut.vecBuildingAction_mul, mul_inv_cancel,
          DifferentialFieldAut.vecBuildingAction_one]
      right_inv := fun v => by
        rw [← DifferentialFieldAut.vecBuildingAction_mul, inv_mul_cancel,
          DifferentialFieldAut.vecBuildingAction_one]
      map_add' := σ.vecBuildingAction_add b }

theorem DifferentialFieldAut.vecBuildingActionEquiv_apply (σ : DifferentialFieldAut C K) {r : ℕ}
    (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K))
    (v : Fin r → DiffOp.CompletedPseudoDiffOp K) :
    σ.vecBuildingActionEquiv b v = σ.vecBuildingAction b v := rfl

theorem DifferentialFieldAut.vecBuildingActionEquiv_inv (σ : DifferentialFieldAut C K) {r : ℕ}
    (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K)) :
    (σ.vecBuildingActionEquiv b)⁻¹ = σ⁻¹.vecBuildingActionEquiv b := by
  ext v
  rfl

theorem DifferentialFieldAut.vecBuildingActionEquiv_pow_apply (σ : DifferentialFieldAut C K)
    {r : ℕ} (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K)) (n : ℕ)
    (v : Fin r → DiffOp.CompletedPseudoDiffOp K) :
    (σ.vecBuildingActionEquiv b ^ n) v = (σ ^ n).vecBuildingAction b v := by
  induction n with
  | zero =>
      rw [pow_zero, pow_zero, DifferentialFieldAut.vecBuildingAction_one]
      rfl
  | succ n ih =>
      rw [pow_succ', LinearEquiv.mul_apply, ih, DifferentialFieldAut.vecBuildingActionEquiv_apply,
        ← DifferentialFieldAut.vecBuildingAction_mul, ← pow_succ]

omit [IsConstantBase C K] in
/-- Coefficient transport preserves the valuation ring and fixes the uniformizer. -/
theorem DifferentialFieldAut.isUniformizerRingAut_mapCompletedPseudoRingEquiv
    (σ : DifferentialFieldAut C K) :
    DiffOp.IsUniformizerRingAut (DiffOp.mapCompletedPseudoRingEquiv σ.toRingEquiv σ.deriv_comm) := by
  refine ⟨fun a ha => ?_, fun a ha => ?_, ?_⟩
  · rw [Valuation.mem_integer_iff, DiffOp.completedPseudoDiffOpValuation_mapCompletedPseudoRingEquiv]
    exact ha
  · rw [Valuation.mem_integer_iff, ← DiffOp.completedPseudoDiffOpValuation_mapCompletedPseudoRingEquiv
      σ.toRingEquiv σ.deriv_comm, RingEquiv.apply_symm_apply]
    exact ha
  · have := σ.mapCompletedPseudoRingEquiv_uniformizer_zpow 1
    simpa only [zpow_one] using this

/-- The canonical variational action is uniformizer-semilinear. -/
theorem DifferentialFieldAut.isUniformizerSemilinear_vecBuildingActionEquiv
    (σ : DifferentialFieldAut C K) {r : ℕ}
    (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K)) :
    DiffOp.IsUniformizerSemilinear (K := K) (σ.vecBuildingActionEquiv b) :=
  ⟨_, σ.isUniformizerRingAut_mapCompletedPseudoRingEquiv, fun a v => σ.vecBuildingAction_smul b a v⟩

/-- A vector with bounded forward orbit lies in the canonical attracting core. -/
theorem mem_variationalAttractingCore_of_mem_forwardBoundedSubspace (σ : DifferentialFieldAut C K)
    {r : ℕ} (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K))
    (L : DiffOp.CompletedPseudoDiffOpLattice K (Fin r)) {v : Fin r → DiffOp.CompletedPseudoDiffOp K}
    (hv : v ∈ DiffOp.forwardBoundedSubspace (σ.vecBuildingActionEquiv b)
      (σ.isUniformizerSemilinear_vecBuildingActionEquiv b)) :
    v ∈ variationalAttractingCore σ b L := by
  obtain ⟨M, hM, hMv⟩ := DiffOp.mem_forwardBoundedSubspace.1 hv
  obtain ⟨k, hk⟩ := DiffOp.exists_nat_le_uniformizerDilate_of_fg (M := L.carrier) hM (by
    rw [L.full]
    exact fun _ _ => trivial)
  rw [variationalAttractingCore, Set.mem_iInter]
  intro c
  refine eventually_atTop.2 ⟨(c + 1) * k, fun n hn => ?_⟩
  rw [DiffOp.mem_leftScale_uniformizer_iff]
  have hmem := hk (hMv n)
  rw [DifferentialFieldAut.vecBuildingActionEquiv_pow_apply] at hmem
  have hmem' := DiffOp.uniformizerDilate_antitone L.carrier
    (show (-((n / (c + 1) : ℕ) : ℤ)) ≤ -(k : ℤ) by
      have : k ≤ n / (c + 1) := by
        rw [Nat.le_div_iff_mul_le (by omega)]
        nlinarith
      omega) hmem
  rw [DiffOp.mem_uniformizerDilate, neg_neg] at hmem'
  exact hmem'

/-- **The boundary pair is opposite.**  The canonical attracting subspace and the canonical
repelling subspace of a differential field automorphism span the completed coordinate space. -/
theorem variationalAttractingSubspace_sup_variationalRepellingSubspace_eq_top
    (σ : DifferentialFieldAut C K) {r : ℕ}
    (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K))
    (L : DiffOp.CompletedPseudoDiffOpLattice K (Fin r)) :
    variationalAttractingSubspace σ b L ⊔ variationalRepellingSubspace σ b L = ⊤ := by
  have hT := σ.isUniformizerSemilinear_vecBuildingActionEquiv b
  have htop := DiffOp.forwardBoundedSubspace_sup_inv_eq_top hT
  rw [eq_top_iff, ← htop]
  refine sup_le_sup (fun v hv => ?_) (fun v hv => ?_)
  · exact mem_variationalAttractingCore_of_mem_forwardBoundedSubspace σ b L hv
  · change v ∈ variationalAttractingCore σ⁻¹ b L
    obtain ⟨M, hM, hMv⟩ := DiffOp.mem_forwardBoundedSubspace.1 hv
    refine mem_variationalAttractingCore_of_mem_forwardBoundedSubspace σ⁻¹ b L
      (DiffOp.mem_forwardBoundedSubspace.2 ⟨M, hM, fun n => ?_⟩)
    have := hMv n
    rwa [DifferentialFieldAut.vecBuildingActionEquiv_inv] at this

end

end GaloisForLFunctions.HTGeometry
