import GaloisForLFunctions.RHTower.PrimeUHFCStarAlgebra

/-!
# Prime UHF circle operator K-one continuity

This module compares literal finite matrix-stage based unitary loops with based unitary loops in
the norm-completed prime UHF algebra.  The finite-stage inclusions below are the actual isometric
star-algebra maps into the completion, not a transported charge model.
-/

namespace PrimeQuasiLocalCharge

noncomputable section

open GaloisForLFunctions.HTGeometry

noncomputable local instance {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] : CommGroup (FundamentalGroup G 1) :=
  fundamentalGroupCommGroup

/-- Canonical star-algebra map from one matrix stage to the algebraic direct limit. -/
def matrixAFStageToAlgebraicLimit
    (localDim : ℕ → ℕ) (i : ℕ) :
    PrimeAFMatrixStageAlgebra localDim i →⋆ₐ[ℂ]
      PrimeAFAlgebraicLimit localDim where
  toFun A := ⟦⟨i, A⟩⟧
  map_one' := (DirectLimit.one_def i).symm
  map_mul' A B := (DirectLimit.mul_def i A B).symm
  map_zero' := (DirectLimit.zero_def i).symm
  map_add' A B := (DirectLimit.add_def i A B).symm
  commutes' c := by
    change (⟦⟨i, (algebraMap ℂ (PrimeAFMatrixStageAlgebra localDim i)) c⟩⟧ :
      PrimeAFAlgebraicLimit localDim) =
        (algebraMap ℂ (PrimeAFAlgebraicLimit localDim)) c
    rw [show (algebraMap ℂ (PrimeAFMatrixStageAlgebra localDim i)) c =
        c • (1 : PrimeAFMatrixStageAlgebra localDim i) by rw [Algebra.smul_def, mul_one]]
    rw [← DirectLimit.smul_def, ← DirectLimit.one_def i]
    exact (Algebra.smul_def c (1 : PrimeAFAlgebraicLimit localDim)).trans (mul_one _)
  map_star' A := (DirectLimit.star_def i A).symm

/-- Canonical dense star-algebra map into the completed UHF algebra. -/
def primeAFAlgebraicLimitToUHF
    {localDim : ℕ → ℕ} [Fact (∀ k, 0 < localDim k)] :
    PrimeAFAlgebraicLimit localDim →⋆ₐ[ℂ] PrimeUHFAlgebra localDim where
  toFun q := (q : PrimeUHFAlgebra localDim)
  map_one' := UniformSpace.Completion.coe_one
    (α := PrimeAFAlgebraicLimit localDim)
  map_mul' q r := UniformSpace.Completion.coe_mul q r
  map_zero' := UniformSpace.Completion.coe_zero
  map_add' q r := UniformSpace.Completion.coe_add q r
  commutes' _ := rfl
  map_star' q := (star_primeUHFAlgebra_coe q).symm

/-- Canonical isometric finite-stage inclusion into the completed UHF algebra. -/
def matrixAFStageToUHF
    {localDim : ℕ → ℕ} [Fact (∀ k, 0 < localDim k)] (i : ℕ) :
    PrimeAFMatrixStageAlgebra localDim i →⋆ₐ[ℂ] PrimeUHFAlgebra localDim :=
  primeAFAlgebraicLimitToUHF.comp (matrixAFStageToAlgebraicLimit localDim i)

theorem norm_matrixAFStageToUHF
    {localDim : ℕ → ℕ} [Fact (∀ k, 0 < localDim k)] (i : ℕ)
    (A : PrimeAFMatrixStageAlgebra localDim i) :
    ‖matrixAFStageToUHF i A‖ = ‖A‖ := by
  exact UniformSpace.Completion.norm_coe _

/-- Successor-stage inclusion represents the same element of the algebraic direct limit. -/
theorem matrixAFStageToAlgebraicLimit_succ
    (localDim : ℕ → ℕ) (i : ℕ)
    (A : PrimeAFMatrixStageAlgebra localDim i) :
    matrixAFStageToAlgebraicLimit localDim (i + 1)
        (matrixAFStageSuccHom localDim i A) =
      matrixAFStageToAlgebraicLimit localDim i A := by
  change (⟦⟨i + 1, matrixAFStageSuccHom localDim i A⟩⟧ :
      PrimeAFAlgebraicLimit localDim) = ⟦⟨i, A⟩⟧
  symm
  rw [DirectLimit.eq_of_le ⟨i, A⟩ (i + 1) (Nat.le_succ i)]
  rw [matrixAFStageTransition_succ localDim le_rfl]
  simp
  rfl

/-- Successor-stage inclusion commutes exactly with inclusion into the completion. -/
theorem matrixAFStageToUHF_succ
    {localDim : ℕ → ℕ} [Fact (∀ k, 0 < localDim k)] (i : ℕ)
    (A : PrimeAFMatrixStageAlgebra localDim i) :
    matrixAFStageToUHF (i + 1) (matrixAFStageSuccHom localDim i A) =
      matrixAFStageToUHF i A := by
  exact congrArg UniformSpace.Completion.coe'
    (matrixAFStageToAlgebraicLimit_succ localDim i A)

/-- Finite-stage unitaries included into the completed UHF unitary group. -/
def matrixAFStageUnitaryToUHF
    {localDim : ℕ → ℕ} [Fact (∀ k, 0 < localDim k)] (i : ℕ) :
    Matrix.unitaryGroup (Fin (matrixAFStageDimension localDim i)) ℂ →*
      unitary (PrimeUHFAlgebra localDim) where
  toFun U := ⟨matrixAFStageToUHF i U, by
    rcases U.property with ⟨h1, h2⟩
    constructor
    · rw [← map_star, ← map_mul, h1, map_one]
    · rw [← map_star, ← map_mul, h2, map_one]⟩
  map_one' := by ext; exact map_one _
  map_mul' U V := by ext; exact map_mul _ _ _

theorem continuous_matrixAFStageUnitaryToUHF
    {localDim : ℕ → ℕ} [Fact (∀ k, 0 < localDim k)] (i : ℕ) :
    Continuous (matrixAFStageUnitaryToUHF (localDim := localDim) i) := by
  apply Continuous.subtype_mk
  have hiso : Isometry (fun A :
      Matrix.unitaryGroup (Fin (matrixAFStageDimension localDim i)) ℂ =>
      matrixAFStageToUHF (localDim := localDim) i
        (A : PrimeAFMatrixStageAlgebra localDim i)) := by
    apply Isometry.of_dist_eq
    intro A B
    change dist (matrixAFStageToUHF (localDim := localDim) i
        (A : PrimeAFMatrixStageAlgebra localDim i))
      (matrixAFStageToUHF (localDim := localDim) i
        (B : PrimeAFMatrixStageAlgebra localDim i)) =
      dist (A : PrimeAFMatrixStageAlgebra localDim i) B
    rw [dist_eq_norm, dist_eq_norm, ← map_sub]
    exact norm_matrixAFStageToUHF (localDim := localDim) i _
  exact hiso.continuous

/-- Physical tensor-identity amplification commutes with inclusion into the UHF completion. -/
theorem matrixAFStageUnitaryToUHF_physical_succ
    {localDim : ℕ → ℕ} [Fact (∀ k, 0 < localDim k)] (i : ℕ)
    (U : Matrix.unitaryGroup (Fin (matrixAFStageDimension localDim i)) ℂ) :
    matrixAFStageUnitaryToUHF (i + 1)
        (unitaryGroupReindex (matrixAFStageSuccIndexEquiv localDim i)
          (amplifyUnitary (localDim (i + 1)) U)) =
      matrixAFStageUnitaryToUHF i U := by
  apply Subtype.ext
  exact matrixAFStageToUHF_succ (localDim := localDim) i
    (U : PrimeAFMatrixStageAlgebra localDim i)

/-- Based-loop model for reduced operator `K₁` of the UHF circle algebra. -/
abbrev PrimeUHFCircleOperatorKOne
    (localDim : ℕ → ℕ) [Fact (∀ k, 0 < localDim k)] :=
  Additive (FundamentalGroup (unitary (PrimeUHFAlgebra localDim)) 1)

/-- Map on based unitary-loop classes induced by one finite-stage inclusion. -/
def matrixAFStageToUHFKOne
    {localDim : ℕ → ℕ} [Fact (∀ k, 0 < localDim k)] (i : ℕ) :
    MatrixAFStageOperatorKOne localDim i →+
      PrimeUHFCircleOperatorKOne localDim := by
  let f : C(Matrix.unitaryGroup (Fin (matrixAFStageDimension localDim i)) ℂ,
      unitary (PrimeUHFAlgebra localDim)) :=
    ⟨matrixAFStageUnitaryToUHF i, continuous_matrixAFStageUnitaryToUHF i⟩
  let g : FundamentalGroup (Matrix.unitaryGroup
      (Fin (matrixAFStageDimension localDim i)) ℂ) 1 →*
      FundamentalGroup (unitary (PrimeUHFAlgebra localDim)) 1 := by
    have h := FundamentalGroup.map f 1
    have hone : f 1 = 1 := by
      change matrixAFStageUnitaryToUHF i 1 = 1
      exact map_one _
    rw [hone] at h
    exact h
  exact g.toAdditive

/-- Explicit image of a based finite-stage unitary loop in the completed UHF algebra. -/
def matrixAFStageToUHFBasedPath
    {localDim : ℕ → ℕ} [Fact (∀ k, 0 < localDim k)] (i : ℕ)
    (p : Path (1 : Matrix.unitaryGroup
      (Fin (matrixAFStageDimension localDim i)) ℂ) 1) :
    Path (1 : unitary (PrimeUHFAlgebra localDim)) 1 :=
  basedMapPath
    ⟨matrixAFStageUnitaryToUHF i, continuous_matrixAFStageUnitaryToUHF i⟩ 1 1
    (map_one (matrixAFStageUnitaryToUHF i)) p

/-- Explicit quotient map underlying the finite-stage map to completed UHF loop classes. -/
def matrixAFStageToUHFBasedKOneMap
    {localDim : ℕ → ℕ} [Fact (∀ k, 0 < localDim k)] (i : ℕ) :
    FundamentalGroup (Matrix.unitaryGroup
      (Fin (matrixAFStageDimension localDim i)) ℂ) 1 →
      FundamentalGroup (unitary (PrimeUHFAlgebra localDim)) 1 :=
  Quotient.map (matrixAFStageToUHFBasedPath i)
    (fun _ _ h ↦ basedMapPath_homotopic _ _ _ _ h)

theorem matrixAFStageToUHFKOne_apply_based
    {localDim : ℕ → ℕ} [Fact (∀ k, 0 < localDim k)] (i : ℕ)
    (q : FundamentalGroup (Matrix.unitaryGroup
      (Fin (matrixAFStageDimension localDim i)) ℂ) 1) :
    matrixAFStageToUHFKOne i (Additive.ofMul q) =
      Additive.ofMul (matrixAFStageToUHFBasedKOneMap i q) := by
  let f : C(Matrix.unitaryGroup (Fin (matrixAFStageDimension localDim i)) ℂ,
      unitary (PrimeUHFAlgebra localDim)) :=
    ⟨matrixAFStageUnitaryToUHF i, continuous_matrixAFStageUnitaryToUHF i⟩
  let g : FundamentalGroup (Matrix.unitaryGroup
      (Fin (matrixAFStageDimension localDim i)) ℂ) 1 →*
      FundamentalGroup (unitary (PrimeUHFAlgebra localDim)) 1 := by
      have h := FundamentalGroup.map f 1
      have hone : f 1 = 1 := by
        change matrixAFStageUnitaryToUHF i 1 = 1
        exact map_one _
      rw [hone] at h
      exact h
  change Additive.ofMul (g q) = _
  apply congrArg Additive.ofMul
  exact fundamentalGroupMap_eq_basedMapPath f 1 1
    (map_one (matrixAFStageUnitaryToUHF i)) q

theorem matrixAFStageToUHFBasedPath_physical_succ
    {localDim : ℕ → ℕ} [Fact (∀ k, 0 < localDim k)] (i : ℕ)
    (p : Path (1 : Matrix.unitaryGroup
      (Fin (matrixAFStageDimension localDim i)) ℂ) 1) :
    matrixAFStageToUHFBasedPath (i + 1)
        (unitaryGroupReindexBasedPath (matrixAFStageSuccIndexEquiv localDim i)
          (amplifyUnitaryBasedPath (localDim (i + 1)) p)) =
      matrixAFStageToUHFBasedPath i p := by
  apply Path.ext
  funext t
  exact matrixAFStageUnitaryToUHF_physical_succ i (p t)

/-- A physical successor amplification has the same completed-UHF based-loop class. -/
theorem matrixAFStageToUHFKOne_physical_succ
    {localDim : ℕ → ℕ} [Fact (∀ k, 0 < localDim k)] (i : ℕ)
    (x : MatrixAFStageOperatorKOne localDim i) :
    matrixAFStageToUHFKOne (i + 1) (matrixAFPhysicalSuccKOneHom localDim i x) =
      matrixAFStageToUHFKOne i x := by
  let q : FundamentalGroup
      (Matrix.unitaryGroup (Fin (matrixAFStageDimension localDim i)) ℂ) 1 := Additive.toMul x
  have hx : x = Additive.ofMul q := rfl
  rw [hx]
  refine Path.Homotopic.Quotient.ind (motive := fun q : FundamentalGroup
      (Matrix.unitaryGroup (Fin (matrixAFStageDimension localDim i)) ℂ) 1 =>
        matrixAFStageToUHFKOne (i + 1)
            (matrixAFPhysicalSuccKOneHom localDim i (Additive.ofMul q)) =
          matrixAFStageToUHFKOne i (Additive.ofMul q)) ?_ q
  intro (p : Path (1 : Matrix.unitaryGroup
    (Fin (matrixAFStageDimension localDim i)) ℂ) 1)
  let qp : FundamentalGroup
      (Matrix.unitaryGroup (Fin (matrixAFStageDimension localDim i)) ℂ) 1 :=
    Path.Homotopic.Quotient.mk p
  change matrixAFStageToUHFKOne (i + 1)
      (unitaryGroupReindexKOneHom
        (κ := Fin (matrixAFStageDimension localDim i) × Fin (localDim (i + 1)))
        (κ' := Fin (matrixAFStageDimension localDim (i + 1)))
        (matrixAFStageSuccIndexEquiv localDim i)
        (amplifyUnitaryKOneHom (localDim (i + 1))
          (Additive.ofMul qp))) =
    matrixAFStageToUHFKOne i
      (Additive.ofMul qp)
  rw [amplifyUnitaryKOneHom_apply_based,
    unitaryGroupReindexKOneHom_apply_based]
  rw [matrixAFStageToUHFKOne_apply_based,
    matrixAFStageToUHFKOne_apply_based]
  apply Additive.toMul.injective
  change matrixAFStageToUHFBasedKOneMap (i + 1)
        (Path.Homotopic.Quotient.mk
        (unitaryGroupReindexBasedPath (matrixAFStageSuccIndexEquiv localDim i)
          (amplifyUnitaryBasedPath (localDim (i + 1)) p))) =
    matrixAFStageToUHFBasedKOneMap i (Path.Homotopic.Quotient.mk p)
  change Path.Homotopic.Quotient.mk
        (matrixAFStageToUHFBasedPath (i + 1)
        (unitaryGroupReindexBasedPath (matrixAFStageSuccIndexEquiv localDim i)
          (amplifyUnitaryBasedPath (localDim (i + 1)) p))) =
    Path.Homotopic.Quotient.mk (matrixAFStageToUHFBasedPath i p)
  rw [matrixAFStageToUHFBasedPath_physical_succ]

/-- The abstract successor transition has the same completed-UHF loop class. -/
theorem matrixAFStageToUHFKOne_transition_succ
    {localDim : ℕ → ℕ} [Fact (∀ k, 0 < localDim k)] (i : ℕ)
    (x : MatrixAFStageOperatorKOne localDim i) :
    matrixAFStageToUHFKOne (i + 1)
        (matrixAFOperatorKOneTransition Fact.out i (i + 1) (Nat.le_succ i) x) =
      matrixAFStageToUHFKOne i x := by
  rw [DFunLike.congr_fun
    (matrixAFOperatorKOneTransition_succ_eq_physical Fact.out i) x]
  exact matrixAFStageToUHFKOne_physical_succ i x

/-- All finite-stage loop maps are compatible with the matrix AF directed system. -/
theorem matrixAFStageToUHFKOne_compatible
    {localDim : ℕ → ℕ} [Fact (∀ k, 0 < localDim k)]
    (i j : ℕ) (hij : i ≤ j) (x : MatrixAFStageOperatorKOne localDim i) :
    matrixAFStageToUHFKOne j
        (matrixAFOperatorKOneTransition Fact.out i j hij x) =
      matrixAFStageToUHFKOne i x := by
  letI := matrixAFOperatorKOneDirectedSystem
    (localDim := localDim) Fact.out
  induction hij using Nat.leRec with
  | refl =>
      have hself : matrixAFOperatorKOneTransition Fact.out i i le_rfl x = x :=
        DirectedSystem.map_self
          (f := fun {_i _j : ℕ} hij ↦
            matrixAFOperatorKOneTransition Fact.out _i _j hij) x
      rw [hself]
  | @le_succ_of_le j hij ih =>
      have hmap : matrixAFOperatorKOneTransition Fact.out j (j + 1)
          (Nat.le_succ j) (matrixAFOperatorKOneTransition Fact.out i j hij x) =
          matrixAFOperatorKOneTransition Fact.out i (j + 1)
            (hij.trans (Nat.le_succ j)) x :=
        DirectedSystem.map_map
          (f := fun {_i _j : ℕ} hij ↦
            matrixAFOperatorKOneTransition Fact.out _i _j hij)
          hij (Nat.le_succ j) x
      rw [← hmap]
      rw [matrixAFStageToUHFKOne_transition_succ, ih]

/-- Canonical integer-module structure on completed-UHF based-loop classes. -/
local instance primeUHFCircleOperatorKOneModule
    (localDim : ℕ → ℕ) [Fact (∀ k, 0 < localDim k)] :
    Module ℤ (PrimeUHFCircleOperatorKOne localDim) :=
  AddCommGroup.toIntModule (PrimeUHFCircleOperatorKOne localDim)

/-- Finite-stage map to completed-UHF loops as an integer-linear map. -/
def matrixAFStageToUHFKOneLinearMap
    {localDim : ℕ → ℕ} [Fact (∀ k, 0 < localDim k)] (i : ℕ) :
    MatrixAFStageOperatorKOne localDim i →ₗ[ℤ]
      PrimeUHFCircleOperatorKOne localDim :=
  { matrixAFStageToUHFKOne i with
    map_smul' := fun n x ↦ map_zsmul (matrixAFStageToUHFKOne i) n x }

theorem matrixAFStageToUHFKOneLinearMap_compatible
    {localDim : ℕ → ℕ} [Fact (∀ k, 0 < localDim k)]
    (i j : ℕ) (hij : i ≤ j) (x : MatrixAFStageOperatorKOne localDim i) :
    matrixAFStageToUHFKOneLinearMap j
        (matrixAFOperatorKOneTransition Fact.out i j hij x) =
      matrixAFStageToUHFKOneLinearMap i x :=
  matrixAFStageToUHFKOne_compatible i j hij x

/-- Canonical comparison from finite matrix-loop colimit to completed-UHF based loops. -/
def primeAFCircleOperatorKOneToUHF
    {localDim : ℕ → ℕ} [hd : Fact (∀ k, 0 < localDim k)] :
    PrimeAFCircleOperatorKOne (localDim := localDim) hd.out →ₗ[ℤ]
      PrimeUHFCircleOperatorKOne localDim :=
  Module.DirectLimit.lift ℤ ℕ
    (fun i ↦ MatrixAFStageOperatorKOne localDim i)
    (fun i j hij ↦ matrixAFOperatorKOneTransition hd.out i j hij)
    (matrixAFStageToUHFKOneLinearMap (localDim := localDim))
    (matrixAFStageToUHFKOneLinearMap_compatible (localDim := localDim))

@[simp] theorem primeAFCircleOperatorKOneToUHF_finiteStage
    {localDim : ℕ → ℕ} [hd : Fact (∀ k, 0 < localDim k)] (i : ℕ)
    (x : MatrixAFStageOperatorKOne localDim i) :
    primeAFCircleOperatorKOneToUHF (localDim := localDim)
        (finiteStageMatrixOperatorKOne (localDim := localDim) hd.out i x) =
      matrixAFStageToUHFKOne i x := by
  unfold primeAFCircleOperatorKOneToUHF finiteStageMatrixOperatorKOne
  exact Module.DirectLimit.lift_of
    (matrixAFStageToUHFKOneLinearMap (localDim := localDim))
    (matrixAFStageToUHFKOneLinearMap_compatible (localDim := localDim)) x

end

end PrimeQuasiLocalCharge
