import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.FirstAscent.SpectatorPhase

/-! # Exact projective comparison on disjoint sets of sites -/
open Matrix
open scoped Matrix.Norms.L2Operator Kronecker
namespace GaloisForLFunctions.HTGeometry.FirstAscent
noncomputable section

private theorem unitary_right_factor {I A : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    [Fintype A] [DecidableEq A] {Z : Matrix A A ℂ}
    (h : (1 : Matrix I I ℂ) ⊗ₖ Z ∈ unitary _) : Z ∈ unitary _ := by
  have hh := (Unitary.mem_iff.mp h).2
  rw [Matrix.star_eq_conjTranspose,Matrix.conjTranspose_kronecker,
    Matrix.conjTranspose_one,← Matrix.mul_kronecker_mul,one_mul] at hh
  apply Matrix.mem_unitaryGroup_iff.mpr
  let i := Classical.arbitrary I
  ext a b
  have he := congrArg (fun X : Matrix (I×A) (I×A) ℂ => X (i,a) (i,b)) hh
  simpa [Matrix.kroneckerMap_apply,Matrix.one_apply,Matrix.star_eq_conjTranspose] using he

variable {Q : Type*} [Fintype Q] [DecidableEq Q] {A : Q → Type*}
    [∀ q, Fintype (A q)] [∀ q, DecidableEq (A q)] [∀ q, Nonempty (A q)]
private abbrev Reg := Matrix (∀ q, A q) (∀ q, A q) ℂ

/-- For disjoint supports, a unitary approximation always supplies a single
global phase at the same operator error. -/
theorem disjoint_unitary_phase {S T : Finset Q} (hST : Disjoint S T) {X Y : Reg (A := A)}
    (hX : IsSiteSupported S X) (hY : IsSiteSupported T Y) (hu : Y ∈ unitary _) :
    ∃ z : ℂ, ‖z‖=1 ∧ ‖X-z • 1‖ ≤ ‖X-Y‖ := by
  classical
  obtain ⟨B,rfl⟩ := exists_liftLocalMatrix_of_isSiteSupported hX
  obtain ⟨C,rfl⟩ := exists_liftLocalMatrix_of_isSiteSupported hY
  let Z := liftLocalMatrixOutsideDisjoint hST C
  let e := configurationSplitEquiv A S
  let Φ := Matrix.reindexAlgEquiv ℂ ℂ e
  have hB := reindex_liftLocalMatrix_eq_kronecker_one S B
  have hC : Φ (liftLocalMatrix T C) = (1 : Matrix (LocalConfiguration A S) (LocalConfiguration A S) ℂ) ⊗ₖ Z :=
    reindex_liftLocalMatrix_disjoint_eq_one_kronecker hST C
  have hZ : Z ∈ unitary _ := by
    apply unitary_right_factor (I := LocalConfiguration A S)
    rw [←hC]
    apply Matrix.mem_unitaryGroup_iff.mpr
    have hs : star (Φ (liftLocalMatrix T C))=Φ (star (liftLocalMatrix T C)) := rfl
    rw [hs,←map_mul,(Unitary.mem_iff.mp hu).2,map_one]
  obtain ⟨z,hz,h⟩ := spectator_phase B ⟨Z,hZ⟩
  refine ⟨z,hz,?_⟩
  rw [←l2_opNorm_reindexAlgEquiv_eq e (liftLocalMatrix S B-z • 1),
    ←l2_opNorm_reindexAlgEquiv_eq e (liftLocalMatrix S B-liftLocalMatrix T C)]
  change ‖Φ _‖ ≤ ‖Φ _‖
  rw [map_sub,map_sub,map_smul,map_one,hC]
  rw [show Φ (liftLocalMatrix S B)=_ from hB]
  have he : B ⊗ₖ (1 : Matrix (OutsideConfiguration A S) (OutsideConfiguration A S) ℂ)-z • 1 =
      (B-z • 1) ⊗ₖ (1 : Matrix (OutsideConfiguration A S) (OutsideConfiguration A S) ℂ) := by
    ext ⟨i,a⟩ ⟨j,b⟩
    by_cases hij : i=j <;> by_cases hab : a=b <;>
      simp [Matrix.kroneckerMap_apply,hij,hab]
  rwa [he,l2_opNorm_kronecker_one]

/-- Deleting the generator terms incident to a circuit costs at most twice
their operator norm times elapsed time in the projective scalar test. -/
theorem deleted_evolution_phase {S T : Finset Q} (hST : Disjoint S T)
    (H K : selfAdjoint (Reg (A := A))) (hK : IsSiteSupported S K.val)
    (C : unitary (Reg (A := A))) (hC : IsSiteSupported T C.val) (t : ℝ) :
    ∃ z : ℂ, ‖z‖=1 ∧ ‖unitaryEvolution H.val t-z • 1‖ ≤
      ‖unitaryEvolution H.val t-C.val‖ + 2* |t| * ‖H.val-K.val‖ := by
  let U := unitaryEvolution H.val t
  let V := unitaryEvolution K.val t
  obtain ⟨z,hu,hz⟩ := disjoint_unitary_phase hST (isSiteSupported_unitaryEvolution hK t) hC C.property
  refine ⟨z,hu,?_⟩
  have hpert : ‖U-V‖ ≤ |t| * ‖H.val-K.val‖ := norm_unitaryEvolution_sub_le _ _ H.2 K.2 t
  have h₁ := norm_sub_le_norm_sub_add_norm_sub U V (z • 1)
  have h₂ := norm_sub_le_norm_sub_add_norm_sub V U C.val
  rw [norm_sub_rev V U] at h₂
  change ‖V-z • 1‖ ≤ ‖V-C.val‖ at hz
  change ‖U-z • 1‖ ≤ ‖U-C.val‖ + _
  linarith only [hz,hpert,h₁,h₂]

#print axioms deleted_evolution_phase
end
end GaloisForLFunctions.HTGeometry.FirstAscent
