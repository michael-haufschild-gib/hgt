import GaloisForLFunctions.RHTower.PrimeAFMatrixDeterminantSplit
import GaloisForLFunctions.RHTower.PrimeAFChargeDirectLimit
import GaloisForLFunctions.HTGeometry.FiniteUnitaryHaarReindex
import Mathlib.Algebra.Colimit.Module

/-!
# Prime AF matrix-circle loop group as a literal stage direct limit

This module constructs the algebraic matrix-loop colimit associated to a prime AF circle system
from literal based unitary-loop homotopy quotients.  Determinant classifies every positive-dimensional
finite matrix stage by `ℤ`; tensoring with an identity of dimension `d` induces multiplication by
`d`; and the physical successor maps assemble into a direct system.

The resulting matrix-loop direct limit is proved linearly equivalent to `AFChargeLimit`.  Thus
every class has a finite matrix-stage ancestor, positive-dimensional tensor amplification is
injective, and neither algebraic passage to the AF limit nor norm-regular winding convergence can
nucleate a class absent at all finite stages.  No operator-K-theory identification premise is used:
the finite-stage loop groups, physical maps, direct limit, forward charge, and inverse are all
constructed here.  A separate theorem must still identify this algebraic colimit with operator
`K₁` of the norm-completed C-star AF circle algebra; this module does not make that identification
by definition.
-/

open GaloisForLFunctions.HTGeometry

namespace PrimeQuasiLocalCharge

noncomputable section

noncomputable local instance {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] : CommGroup (FundamentalGroup G 1) :=
  fundamentalGroupCommGroup

noncomputable local instance primeAFMatrixOperatorKOneDirectLimitInst1 : CommGroup (FundamentalGroup (Units ℂ) 1) :=
  fundamentalGroupCommGroup

theorem fundamentalGroupMap_eq_basedMapPath
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (x : X) (y : Y) (hbase : f x = y)
    (q : FundamentalGroup X x) :
    (by
      have h := FundamentalGroup.map f x
      rw [hbase] at h
      exact h q) =
      Quotient.map (basedMapPath f x y hbase)
        (fun _ _ h ↦ basedMapPath_homotopic f x y hbase h) q := by
  cases hbase
  induction q using Path.Homotopic.Quotient.ind with
  | mk p => rfl

/-- Pointwise natural power of a based loop in a topological group. -/
def loopPointwisePowPath {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (p : Path (1 : G) 1) (d : ℕ) : Path (1 : G) 1 where
  toFun t := p t ^ d
  continuous_toFun := by fun_prop
  source' := by simp
  target' := by simp

def complexUnitsFundamentalGroupPow
    (q : FundamentalGroup (Units ℂ) 1) (d : ℕ) :
    FundamentalGroup (Units ℂ) 1 := q ^ d

def complexUnitsFundamentalGroupMul
    (q r : FundamentalGroup (Units ℂ) 1) :
    FundamentalGroup (Units ℂ) 1 := q * r

/-- Pointwise `d`th power represents the ordinary `d`th power in `π₁(ℂˣ)`. -/
theorem complexUnitsLoopPointwisePowPath_mk
    (p : Path (1 : Units ℂ) 1) (d : ℕ) :
    Path.Homotopic.Quotient.mk (loopPointwisePowPath p d) =
      complexUnitsFundamentalGroupPow (Path.Homotopic.Quotient.mk p) d := by
  induction d with
  | zero =>
      change Path.Homotopic.Quotient.mk (loopPointwisePowPath p 0) =
        Path.Homotopic.Quotient.mk (Path.refl 1)
      apply congrArg Path.Homotopic.Quotient.mk
      ext t
      simp [loopPointwisePowPath]
  | succ d ih =>
      change Path.Homotopic.Quotient.mk (loopPointwisePowPath p (d + 1)) =
        complexUnitsFundamentalGroupMul
          (complexUnitsFundamentalGroupPow (Path.Homotopic.Quotient.mk p) d)
          (Path.Homotopic.Quotient.mk p)
      have hpath : loopPointwisePowPath p (d + 1) =
          loopPointwiseMulPath (loopPointwisePowPath p d) p := by
        ext t
        simp [loopPointwisePowPath, loopPointwiseMulPath, pow_succ]
      rw [hpath, ← fundamentalGroupPointwiseMul_mk, ih]
      exact congrFun (congrFun
        (EckmannHilton.mul fundamentalGroupPointwiseMul_isUnital
          EckmannHilton.MulOneClass.isUnital
          fundamentalGroupPointwiseMul_interchange)
        (complexUnitsFundamentalGroupPow (Path.Homotopic.Quotient.mk p) d))
        (Path.Homotopic.Quotient.mk p)

theorem additive_ofMul_complexUnitsFundamentalGroupPow
    (q : FundamentalGroup (Units ℂ) 1) (d : ℕ) :
    Additive.ofMul (complexUnitsFundamentalGroupPow q d) =
      d • Additive.ofMul q := by
  rfl

/-- Explicit based determinant loop for an arbitrary finite matrix carrier. -/
def finiteMatrixDeterminantBasedPath
    {iota : Type*} [Fintype iota] [DecidableEq iota]
    (p : Path (1 : Matrix.unitaryGroup iota ℂ) 1) :
    Path (1 : Units ℂ) 1 :=
  basedMapPath
    ⟨unitaryDeterminantUnits, continuous_unitaryDeterminantUnits⟩ 1 1
    unitaryDeterminantUnits_one p

def finiteMatrixDeterminantBasedKOneMap
    {iota : Type*} [Fintype iota] [DecidableEq iota] :
    FundamentalGroup (Matrix.unitaryGroup iota ℂ) 1 →
      FundamentalGroup (Units ℂ) 1 :=
  Quotient.map finiteMatrixDeterminantBasedPath
    (fun _ _ h ↦ basedMapPath_homotopic _ _ _ _ h)

theorem finiteMatrixDeterminantKOneHom_apply_based
    {iota : Type*} [Fintype iota] [DecidableEq iota]
    (q : FundamentalGroup (Matrix.unitaryGroup iota ℂ) 1) :
    finiteMatrixDeterminantKOneHom (iota := iota) (Additive.ofMul q) =
      Additive.ofMul (finiteMatrixDeterminantBasedKOneMap q) := by
  let f : C(Matrix.unitaryGroup iota ℂ, Units ℂ) :=
    ⟨unitaryDeterminantUnits, continuous_unitaryDeterminantUnits⟩
  let g : FundamentalGroup (Matrix.unitaryGroup iota ℂ) 1 →*
      FundamentalGroup (Units ℂ) 1 := by
    have h := FundamentalGroup.map f 1
    have hone : f 1 = 1 := unitaryDeterminantUnits_one
    rw [hone] at h
    exact h
  change Additive.ofMul (g q) = _
  apply congrArg Additive.ofMul
  exact fundamentalGroupMap_eq_basedMapPath f 1 1
    unitaryDeterminantUnits_one q

/-- Explicit based tensor-amplification loop. -/
def amplifyUnitaryBasedPath
    {iota : Type*} [Fintype iota] [DecidableEq iota]
    (d : ℕ) (p : Path (1 : Matrix.unitaryGroup iota ℂ) 1) :
    Path (1 : Matrix.unitaryGroup (iota × Fin d) ℂ) 1 :=
  basedMapPath
    ⟨amplifyUnitary d, continuous_amplifyUnitary d⟩ 1 1
    (amplifyUnitary_one d) p

def amplifyUnitaryBasedKOneMap
    {iota : Type*} [Fintype iota] [DecidableEq iota] (d : ℕ) :
    FundamentalGroup (Matrix.unitaryGroup iota ℂ) 1 →
      FundamentalGroup (Matrix.unitaryGroup (iota × Fin d) ℂ) 1 :=
  Quotient.map (amplifyUnitaryBasedPath d)
    (fun _ _ h ↦ basedMapPath_homotopic _ _ _ _ h)

theorem amplifyUnitaryKOneHom_apply_based
    {iota : Type*} [Fintype iota] [DecidableEq iota] (d : ℕ)
    (q : FundamentalGroup (Matrix.unitaryGroup iota ℂ) 1) :
    amplifyUnitaryKOneHom d (Additive.ofMul q) =
      Additive.ofMul (amplifyUnitaryBasedKOneMap d q) := by
  let f : C(Matrix.unitaryGroup iota ℂ,
      Matrix.unitaryGroup (iota × Fin d) ℂ) :=
    ⟨amplifyUnitary d, continuous_amplifyUnitary d⟩
  let g : FundamentalGroup (Matrix.unitaryGroup iota ℂ) 1 →*
      FundamentalGroup (Matrix.unitaryGroup (iota × Fin d) ℂ) 1 := by
    have h := FundamentalGroup.map f 1
    have hone : f 1 = 1 := amplifyUnitary_one d
    rw [hone] at h
    exact h
  change Additive.ofMul (g q) = _
  apply congrArg Additive.ofMul
  exact fundamentalGroupMap_eq_basedMapPath f 1 1 (amplifyUnitary_one d) q

theorem finiteMatrixDeterminantBasedKOneMap_amplify
    {iota : Type*} [Fintype iota] [DecidableEq iota] (d : ℕ)
    (q : FundamentalGroup (Matrix.unitaryGroup iota ℂ) 1) :
    finiteMatrixDeterminantBasedKOneMap
        (amplifyUnitaryBasedKOneMap d q) =
      complexUnitsFundamentalGroupPow
        (finiteMatrixDeterminantBasedKOneMap q) d := by
  induction q using Path.Homotopic.Quotient.ind with
  | mk p =>
      have hpath : finiteMatrixDeterminantBasedPath
          (amplifyUnitaryBasedPath d p) =
          loopPointwisePowPath (finiteMatrixDeterminantBasedPath p) d := by
        ext t
        exact congrArg (fun z : Units ℂ ↦ (z : ℂ))
          (unitaryDeterminantUnits_amplifyUnitary d (p t))
      change Path.Homotopic.Quotient.mk
          (finiteMatrixDeterminantBasedPath (amplifyUnitaryBasedPath d p)) =
        complexUnitsFundamentalGroupPow
          (Path.Homotopic.Quotient.mk (finiteMatrixDeterminantBasedPath p)) d
      rw [hpath]
      exact complexUnitsLoopPointwisePowPath_mk
        (finiteMatrixDeterminantBasedPath p) d

/-- Tensor amplification multiplies finite-stage determinant `K₁` by matrix multiplicity. -/
theorem finiteMatrixDeterminantKOneHom_amplifyUnitary
    {iota : Type*} [Fintype iota] [DecidableEq iota]
    (d : ℕ) (q : FundamentalGroup (Matrix.unitaryGroup iota ℂ) 1) :
    finiteMatrixDeterminantKOneHom
        (amplifyUnitaryKOneHom d (Additive.ofMul q)) =
      d • finiteMatrixDeterminantKOneHom (Additive.ofMul q) := by
  rw [amplifyUnitaryKOneHom_apply_based,
    finiteMatrixDeterminantKOneHom_apply_based,
    finiteMatrixDeterminantKOneHom_apply_based,
    finiteMatrixDeterminantBasedKOneMap_amplify,
    additive_ofMul_complexUnitsFundamentalGroupPow]

/-- Integer determinant charge transforms by `z ↦ d z` under tensor amplification. -/
theorem finiteMatrixOperatorKOneCharge_amplifyUnitary
    {iota : Type*} [Fintype iota] [DecidableEq iota]
    (d : ℕ) (q : FundamentalGroup (Matrix.unitaryGroup iota ℂ) 1) :
    finiteMatrixOperatorKOneCharge
        (amplifyUnitaryKOneHom d (Additive.ofMul q)) =
      (d : ℤ) * finiteMatrixOperatorKOneCharge (Additive.ofMul q) := by
  change complexUnitsOperatorKOneEquivInt
      (finiteMatrixDeterminantKOneHom
        (amplifyUnitaryKOneHom d (Additive.ofMul q))) =
    (d : ℤ) * complexUnitsOperatorKOneEquivInt
      (finiteMatrixDeterminantKOneHom (Additive.ofMul q))
  rw [finiteMatrixDeterminantKOneHom_amplifyUnitary, map_nsmul]
  simp

@[simp] theorem unitaryDeterminantUnits_reindex
    {κ κ' : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype κ'] [DecidableEq κ'] (e : κ ≃ κ')
    (U : Matrix.unitaryGroup κ ℂ) :
    unitaryDeterminantUnits (unitaryGroupReindex e U) =
      unitaryDeterminantUnits U := by
  apply Units.ext
  simp [unitaryDeterminantUnits_coe, unitaryGroupReindex]

/-- Coordinate reindexing on finite matrix-circle operator `K₁`. -/
def unitaryGroupReindexKOneHom
    {κ κ' : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype κ'] [DecidableEq κ'] (e : κ ≃ κ') :
    FiniteMatrixCircleOperatorKOne κ →+
      FiniteMatrixCircleOperatorKOne κ' := by
  let f : C(Matrix.unitaryGroup κ ℂ, Matrix.unitaryGroup κ' ℂ) :=
    ⟨unitaryGroupReindex e, continuous_unitaryGroupReindex e⟩
  have h := FundamentalGroup.map f (1 : Matrix.unitaryGroup κ ℂ)
  have hone : f (1 : Matrix.unitaryGroup κ ℂ) = 1 :=
    (unitaryGroupReindex e).map_one
  rw [hone] at h
  exact MonoidHom.toAdditive h

def unitaryGroupReindexBasedPath
    {κ κ' : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype κ'] [DecidableEq κ'] (e : κ ≃ κ')
    (p : Path (1 : Matrix.unitaryGroup κ ℂ) 1) :
    Path (1 : Matrix.unitaryGroup κ' ℂ) 1 :=
  basedMapPath
    ⟨unitaryGroupReindex e, continuous_unitaryGroupReindex e⟩ 1 1
    ((unitaryGroupReindex e).map_one) p

def unitaryGroupReindexBasedKOneMap
    {κ κ' : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype κ'] [DecidableEq κ'] (e : κ ≃ κ') :
    FundamentalGroup (Matrix.unitaryGroup κ ℂ) 1 →
      FundamentalGroup (Matrix.unitaryGroup κ' ℂ) 1 :=
  Quotient.map (unitaryGroupReindexBasedPath e)
    (fun _ _ h ↦ basedMapPath_homotopic _ _ _ _ h)

theorem unitaryGroupReindexKOneHom_apply_based
    {κ κ' : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype κ'] [DecidableEq κ'] (e : κ ≃ κ')
    (q : FundamentalGroup (Matrix.unitaryGroup κ ℂ) 1) :
    unitaryGroupReindexKOneHom e (Additive.ofMul q) =
      Additive.ofMul (unitaryGroupReindexBasedKOneMap e q) := by
  let f : C(Matrix.unitaryGroup κ ℂ, Matrix.unitaryGroup κ' ℂ) :=
    ⟨unitaryGroupReindex e, continuous_unitaryGroupReindex e⟩
  let g : FundamentalGroup (Matrix.unitaryGroup κ ℂ) 1 →*
      FundamentalGroup (Matrix.unitaryGroup κ' ℂ) 1 := by
    have h := FundamentalGroup.map f 1
    have hone : f 1 = 1 := (unitaryGroupReindex e).map_one
    rw [hone] at h
    exact h
  change Additive.ofMul (g q) = _
  apply congrArg Additive.ofMul
  exact fundamentalGroupMap_eq_basedMapPath f 1 1
    (unitaryGroupReindex e).map_one q

theorem finiteMatrixDeterminantBasedKOneMap_reindex
    {κ κ' : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype κ'] [DecidableEq κ'] (e : κ ≃ κ')
    (q : FundamentalGroup (Matrix.unitaryGroup κ ℂ) 1) :
    finiteMatrixDeterminantBasedKOneMap
        (unitaryGroupReindexBasedKOneMap e q) =
      finiteMatrixDeterminantBasedKOneMap q := by
  induction q using Path.Homotopic.Quotient.ind with
  | mk p =>
      change Path.Homotopic.Quotient.mk
          (finiteMatrixDeterminantBasedPath
            (unitaryGroupReindexBasedPath e p)) =
        Path.Homotopic.Quotient.mk (finiteMatrixDeterminantBasedPath p)
      apply congrArg Path.Homotopic.Quotient.mk
      ext t
      exact congrArg (fun z : Units ℂ ↦ (z : ℂ))
        (unitaryDeterminantUnits_reindex e (p t))

theorem finiteMatrixDeterminantKOneHom_reindex
    {κ κ' : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype κ'] [DecidableEq κ'] (e : κ ≃ κ')
    (q : FundamentalGroup (Matrix.unitaryGroup κ ℂ) 1) :
    finiteMatrixDeterminantKOneHom
        (unitaryGroupReindexKOneHom e (Additive.ofMul q)) =
      finiteMatrixDeterminantKOneHom (Additive.ofMul q) := by
  rw [unitaryGroupReindexKOneHom_apply_based,
    finiteMatrixDeterminantKOneHom_apply_based,
    finiteMatrixDeterminantKOneHom_apply_based,
    finiteMatrixDeterminantBasedKOneMap_reindex]

theorem finiteMatrixOperatorKOneCharge_reindex
    {κ κ' : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype κ'] [DecidableEq κ'] (e : κ ≃ κ')
    (q : FundamentalGroup (Matrix.unitaryGroup κ ℂ) 1) :
    finiteMatrixOperatorKOneCharge
        (unitaryGroupReindexKOneHom e (Additive.ofMul q)) =
      finiteMatrixOperatorKOneCharge (Additive.ofMul q) := by
  change complexUnitsOperatorKOneEquivInt
      (finiteMatrixDeterminantKOneHom
        (unitaryGroupReindexKOneHom e (Additive.ofMul q))) =
    complexUnitsOperatorKOneEquivInt
      (finiteMatrixDeterminantKOneHom (Additive.ofMul q))
  rw [finiteMatrixDeterminantKOneHom_reindex]

theorem finiteMatrixDeterminantKOneHom_apply (n : ℕ)
    (q : FundamentalGroup (Matrix.unitaryGroup (Fin (n + 1)) ℂ) 1) :
    finiteMatrixDeterminantKOneHom (iota := Fin (n + 1))
        (Additive.ofMul q) =
      Additive.ofMul (finiteUnitaryDeterminantKOneMap n q) := by
  rw [finiteMatrixDeterminantKOneHom_apply_based]
  rfl

theorem finiteMatrixDeterminantKOneHom_bijective_fin (n : ℕ) :
    Function.Bijective
      (finiteMatrixDeterminantKOneHom (iota := Fin (n + 1))) := by
  constructor
  · intro x y hxy
    apply Additive.toMul.injective
    apply finiteUnitaryDeterminantKOneMap_injective_all n
    apply Additive.ofMul.injective
    rw [← finiteMatrixDeterminantKOneHom_apply n (Additive.toMul x),
      ← finiteMatrixDeterminantKOneHom_apply n (Additive.toMul y)]
    simpa using hxy
  · intro y
    obtain ⟨x, hx⟩ := finiteUnitaryDeterminantKOneMap_surjective n
      (Additive.toMul y)
    refine ⟨Additive.ofMul x, ?_⟩
    apply Additive.toMul.injective
    simpa [finiteMatrixDeterminantKOneHom_apply] using hx

theorem finiteMatrixOperatorKOneCharge_bijective_fin (n : ℕ) :
    Function.Bijective
      (finiteMatrixOperatorKOneCharge (iota := Fin (n + 1))) := by
  exact (complexUnitsOperatorKOneEquivInt.bijective.comp
    (finiteMatrixDeterminantKOneHom_bijective_fin n))

theorem finiteMatrixOperatorKOneCharge_bijective_of_pos
    (D : ℕ) (hD : 0 < D) :
    Function.Bijective
      (finiteMatrixOperatorKOneCharge (iota := Fin D)) := by
  cases D with
  | zero => omega
  | succ n => exact finiteMatrixOperatorKOneCharge_bijective_fin n

/-- Exact integer classification of a nonempty finite matrix-circle operator `K₁` stage. -/
def finiteMatrixOperatorKOneEquivInt (n : ℕ) :
    FiniteMatrixCircleOperatorKOne (Fin (n + 1)) ≃+ ℤ :=
  AddEquiv.ofBijective
    (finiteMatrixOperatorKOneCharge (iota := Fin (n + 1)))
    (finiteMatrixOperatorKOneCharge_bijective_fin n)

/-! ## Literal finite matrix stages and their directed system -/

/-- Matrix size at stage `i`; stage zero is scalar and each successor tensors by the new factor. -/
def matrixAFStageDimension (localDim : ℕ → ℕ) : ℕ → ℕ
  | 0 => 1
  | i + 1 => matrixAFStageDimension localDim i * localDim (i + 1)

@[simp] theorem matrixAFStageDimension_zero (localDim : ℕ → ℕ) :
    matrixAFStageDimension localDim 0 = 1 := rfl

@[simp] theorem matrixAFStageDimension_succ (localDim : ℕ → ℕ) (i : ℕ) :
    matrixAFStageDimension localDim (i + 1) =
      matrixAFStageDimension localDim i * localDim (i + 1) := rfl

theorem matrixAFStageDimension_pos {localDim : ℕ → ℕ}
    (hd : ∀ k, 0 < localDim k) :
    ∀ i, 0 < matrixAFStageDimension localDim i := by
  intro i
  induction i with
  | zero => simp
  | succ i ih =>
      simp only [matrixAFStageDimension_succ]
      exact Nat.mul_pos ih (hd (i + 1))

/-- Literal matrix-circle operator `K₁` at AF stage `i`. -/
abbrev MatrixAFStageOperatorKOne (localDim : ℕ → ℕ) (i : ℕ) :=
  FiniteMatrixCircleOperatorKOne (Fin (matrixAFStageDimension localDim i))

/-- Determinant charge is an exact additive equivalence at every positive-dimensional stage. -/
def matrixAFStageOperatorKOneEquivInt {localDim : ℕ → ℕ}
    (hd : ∀ k, 0 < localDim k) (i : ℕ) :
    MatrixAFStageOperatorKOne localDim i ≃+ ℤ := by
  refine AddEquiv.ofBijective finiteMatrixOperatorKOneCharge ?_
  exact finiteMatrixOperatorKOneCharge_bijective_of_pos
    (matrixAFStageDimension localDim i) (matrixAFStageDimension_pos hd i)

@[simp] theorem matrixAFStageOperatorKOneEquivInt_apply
    {localDim : ℕ → ℕ} (hd : ∀ k, 0 < localDim k) (i : ℕ)
    (x : MatrixAFStageOperatorKOne localDim i) :
    matrixAFStageOperatorKOneEquivInt hd i x =
      finiteMatrixOperatorKOneCharge x := rfl

def matrixAFStageOperatorKOneLinearEquivInt {localDim : ℕ → ℕ}
    (hd : ∀ k, 0 < localDim k) (i : ℕ) :
    MatrixAFStageOperatorKOne localDim i ≃ₗ[ℤ] ℤ :=
  (matrixAFStageOperatorKOneEquivInt hd i).toIntLinearEquiv

/-- All-pair matrix-stage transition, transported through the proved determinant classification. -/
def matrixAFOperatorKOneTransition {localDim : ℕ → ℕ}
    (hd : ∀ k, 0 < localDim k) (i j : ℕ) (hij : i ≤ j) :
    MatrixAFStageOperatorKOne localDim i →ₗ[ℤ]
      MatrixAFStageOperatorKOne localDim j :=
  (matrixAFStageOperatorKOneLinearEquivInt hd j).symm.toLinearMap.comp
    ((chargeTransition localDim i j hij).comp
      (matrixAFStageOperatorKOneLinearEquivInt hd i).toLinearMap)

@[simp] theorem matrixAFOperatorKOneTransition_charge
    {localDim : ℕ → ℕ} (hd : ∀ k, 0 < localDim k)
    (i j : ℕ) (hij : i ≤ j) (x : MatrixAFStageOperatorKOne localDim i) :
    matrixAFStageOperatorKOneEquivInt hd j
        (matrixAFOperatorKOneTransition hd i j hij x) =
      chargeTransition localDim i j hij
        (matrixAFStageOperatorKOneEquivInt hd i x) := by
  simp [matrixAFOperatorKOneTransition,
    matrixAFStageOperatorKOneLinearEquivInt]

instance matrixAFOperatorKOneDirectedSystem
    {localDim : ℕ → ℕ} (hd : ∀ k, 0 < localDim k) :
    DirectedSystem (fun i ↦ MatrixAFStageOperatorKOne localDim i)
      (fun i j hij ↦ matrixAFOperatorKOneTransition hd i j hij) where
  map_self := by
    intro i x
    apply (matrixAFStageOperatorKOneEquivInt hd i).injective
    simp [matrixAFOperatorKOneTransition, chargeTransition]
  map_map := by
    intro i j k hij hjk x
    apply (matrixAFStageOperatorKOneEquivInt hd i).injective
    simp only [matrixAFOperatorKOneTransition_charge]
    simp only [chargeTransition_apply]
    rw [← mul_assoc, ← Nat.cast_mul,
      Nat.mul_comm (chargeTransitionFactor localDim j i),
      chargeTransitionFactor_mul hij hjk]

/-- Physical successor inclusion: tensor by identity, then canonically flatten product indices. -/
def matrixAFPhysicalSuccKOneHom (localDim : ℕ → ℕ) (i : ℕ) :
    MatrixAFStageOperatorKOne localDim i →+
      MatrixAFStageOperatorKOne localDim (i + 1) :=
  (unitaryGroupReindexKOneHom finProdFinEquiv).comp
    (amplifyUnitaryKOneHom (localDim (i + 1)))

theorem matrixAFPhysicalSuccKOneHom_charge
    (localDim : ℕ → ℕ) (i : ℕ)
    (x : MatrixAFStageOperatorKOne localDim i) :
    finiteMatrixOperatorKOneCharge (matrixAFPhysicalSuccKOneHom localDim i x) =
      (localDim (i + 1) : ℤ) * finiteMatrixOperatorKOneCharge x := by
  calc
    finiteMatrixOperatorKOneCharge (matrixAFPhysicalSuccKOneHom localDim i x) =
        finiteMatrixOperatorKOneCharge
          (amplifyUnitaryKOneHom (localDim (i + 1)) x) := by
      change finiteMatrixOperatorKOneCharge
          (unitaryGroupReindexKOneHom finProdFinEquiv
            (amplifyUnitaryKOneHom (localDim (i + 1)) x)) = _
      simpa [matrixAFPhysicalSuccKOneHom] using
        finiteMatrixOperatorKOneCharge_reindex finProdFinEquiv
          (Additive.toMul (amplifyUnitaryKOneHom (localDim (i + 1)) x))
    _ = (localDim (i + 1) : ℤ) * finiteMatrixOperatorKOneCharge x := by
      simpa using finiteMatrixOperatorKOneCharge_amplifyUnitary
        (localDim (i + 1)) (Additive.toMul x)

/-- The abstract directed-system successor is exactly physical tensor-identity amplification. -/
theorem matrixAFOperatorKOneTransition_succ_eq_physical
    {localDim : ℕ → ℕ} (hd : ∀ k, 0 < localDim k) (i : ℕ) :
    matrixAFOperatorKOneTransition hd i (i + 1) (Nat.le_succ i) =
      (matrixAFPhysicalSuccKOneHom localDim i).toIntLinearMap := by
  apply LinearMap.ext
  intro x
  apply (matrixAFStageOperatorKOneEquivInt hd (i + 1)).injective
  rw [matrixAFOperatorKOneTransition_charge]
  simp only [matrixAFStageOperatorKOneEquivInt_apply,
    chargeTransition_apply, chargeTransitionFactor_succ]
  change (localDim (i + 1) : ℤ) * finiteMatrixOperatorKOneCharge x =
    finiteMatrixOperatorKOneCharge (matrixAFPhysicalSuccKOneHom localDim i x)
  exact (matrixAFPhysicalSuccKOneHom_charge localDim i x).symm

theorem matrixAFStageDimension_eq_chargeDenominator
    (localDim : ℕ → ℕ) (i : ℕ) :
    matrixAFStageDimension localDim i = chargeDenominator localDim i := by
  induction i with
  | zero => simp [chargeDenominator]
  | succ i ih =>
      rw [matrixAFStageDimension_succ, ih]
      have h := chargeDenominator_mul_factor
        (localDim := localDim) (i := i) (j := i + 1) (Nat.le_succ i)
      simpa using h

/-! ## Operator-`K₁` direct limit and exact charge identification -/

/-- Literal direct limit of finite matrix-circle operator `K₁` groups. -/
abbrev PrimeAFCircleOperatorKOne {localDim : ℕ → ℕ}
    (hd : ∀ k, 0 < localDim k) :=
  Module.DirectLimit (fun i ↦ MatrixAFStageOperatorKOne localDim i)
    (fun i j hij ↦ matrixAFOperatorKOneTransition hd i j hij)

local instance primeAFCircleOperatorKOneModule
    {localDim : ℕ → ℕ} (hd : ∀ k, 0 < localDim k) :
    Module ℤ (PrimeAFCircleOperatorKOne hd) :=
  Module.DirectLimit.module
    (fun i ↦ MatrixAFStageOperatorKOne localDim i)
    (fun i j hij ↦ matrixAFOperatorKOneTransition hd i j hij)

/-- Canonical inclusion of a literal finite matrix-stage class. -/
def finiteStageMatrixOperatorKOne {localDim : ℕ → ℕ}
    (hd : ∀ k, 0 < localDim k) (i : ℕ) :
    MatrixAFStageOperatorKOne localDim i →ₗ[ℤ]
      PrimeAFCircleOperatorKOne hd :=
  Module.DirectLimit.of ℤ ℕ (fun i ↦ MatrixAFStageOperatorKOne localDim i)
    (fun i j hij ↦ matrixAFOperatorKOneTransition hd i j hij) i

/-- Stage determinant charge followed by the canonical charge-limit inclusion. -/
def matrixAFStageToChargeLimit {localDim : ℕ → ℕ}
    (hd : ∀ k, 0 < localDim k) (i : ℕ) :
    MatrixAFStageOperatorKOne localDim i →ₗ[ℤ] AFChargeLimit localDim :=
  (finiteStageCharge localDim i).comp
    (matrixAFStageOperatorKOneLinearEquivInt hd i).toLinearMap

@[simp] theorem matrixAFStageToChargeLimit_apply
    {localDim : ℕ → ℕ} (hd : ∀ k, 0 < localDim k) (i : ℕ)
    (x : MatrixAFStageOperatorKOne localDim i) :
    matrixAFStageToChargeLimit hd i x =
      finiteStageCharge localDim i (finiteMatrixOperatorKOneCharge x) := rfl

theorem matrixAFStageToChargeLimit_compatible
    {localDim : ℕ → ℕ} (hd : ∀ k, 0 < localDim k)
    (i j : ℕ) (hij : i ≤ j) (x : MatrixAFStageOperatorKOne localDim i) :
    matrixAFStageToChargeLimit hd j
        (matrixAFOperatorKOneTransition hd i j hij x) =
      matrixAFStageToChargeLimit hd i x := by
  calc
    matrixAFStageToChargeLimit hd j
        (matrixAFOperatorKOneTransition hd i j hij x) =
        finiteStageCharge localDim j
          (matrixAFStageOperatorKOneEquivInt hd j
            (matrixAFOperatorKOneTransition hd i j hij x)) := rfl
    _ = finiteStageCharge localDim j
        (chargeTransition localDim i j hij
          (matrixAFStageOperatorKOneEquivInt hd i x)) := by
      rw [matrixAFOperatorKOneTransition_charge]
    _ = finiteStageCharge localDim i
        (matrixAFStageOperatorKOneEquivInt hd i x) := by
      rw [chargeTransition_apply]
      exact finiteStageCharge_transition localDim hij _
    _ = matrixAFStageToChargeLimit hd i x := rfl

/-- Determinant charge on the literal operator-`K₁` direct limit. -/
def primeAFCircleOperatorKOneToChargeLimit {localDim : ℕ → ℕ}
    (hd : ∀ k, 0 < localDim k) :
    PrimeAFCircleOperatorKOne hd →ₗ[ℤ] AFChargeLimit localDim :=
  Module.DirectLimit.lift ℤ ℕ
    (fun i ↦ MatrixAFStageOperatorKOne localDim i)
    (fun i j hij ↦ matrixAFOperatorKOneTransition hd i j hij)
    (matrixAFStageToChargeLimit hd)
    (matrixAFStageToChargeLimit_compatible hd)

@[simp] theorem primeAFCircleOperatorKOneToChargeLimit_finiteStage
    {localDim : ℕ → ℕ} (hd : ∀ k, 0 < localDim k) (i : ℕ)
    (x : MatrixAFStageOperatorKOne localDim i) :
    primeAFCircleOperatorKOneToChargeLimit hd
        (finiteStageMatrixOperatorKOne hd i x) =
      finiteStageCharge localDim i (finiteMatrixOperatorKOneCharge x) := by
  unfold primeAFCircleOperatorKOneToChargeLimit finiteStageMatrixOperatorKOne
  exact Module.DirectLimit.lift_of (matrixAFStageToChargeLimit hd)
    (matrixAFStageToChargeLimit_compatible hd) x

theorem matrixAFOperatorKOneTransition_symm_charge
    {localDim : ℕ → ℕ} (hd : ∀ k, 0 < localDim k)
    (i j : ℕ) (hij : i ≤ j) (z : ℤ) :
    matrixAFOperatorKOneTransition hd i j hij
        ((matrixAFStageOperatorKOneEquivInt hd i).symm z) =
      (matrixAFStageOperatorKOneEquivInt hd j).symm
        (chargeTransition localDim i j hij z) := by
  apply (matrixAFStageOperatorKOneEquivInt hd j).injective
  calc
    matrixAFStageOperatorKOneEquivInt hd j
        (matrixAFOperatorKOneTransition hd i j hij
          ((matrixAFStageOperatorKOneEquivInt hd i).symm z)) =
        chargeTransition localDim i j hij
          (matrixAFStageOperatorKOneEquivInt hd i
            ((matrixAFStageOperatorKOneEquivInt hd i).symm z)) := by
      rw [matrixAFOperatorKOneTransition_charge]
    _ = chargeTransition localDim i j hij z := by simp
    _ = matrixAFStageOperatorKOneEquivInt hd j
        ((matrixAFStageOperatorKOneEquivInt hd j).symm
          (chargeTransition localDim i j hij z)) := by simp

/-- Canonical operator-`K₁` direct-limit class of an integer charge at stage `i`. -/
def chargeStageToPrimeAFCircleOperatorKOne {localDim : ℕ → ℕ}
    (hd : ∀ k, 0 < localDim k) (i : ℕ) :
    ℤ →ₗ[ℤ] PrimeAFCircleOperatorKOne hd :=
  (finiteStageMatrixOperatorKOne hd i).comp
    (matrixAFStageOperatorKOneLinearEquivInt hd i).symm.toLinearMap

theorem chargeStageToPrimeAFCircleOperatorKOne_compatible
    {localDim : ℕ → ℕ} (hd : ∀ k, 0 < localDim k)
    (i j : ℕ) (hij : i ≤ j) (z : ℤ) :
    chargeStageToPrimeAFCircleOperatorKOne hd j
        (chargeTransition localDim i j hij z) =
      chargeStageToPrimeAFCircleOperatorKOne hd i z := by
  have h : finiteStageMatrixOperatorKOne hd j
      (matrixAFOperatorKOneTransition hd i j hij
        ((matrixAFStageOperatorKOneEquivInt hd i).symm z)) =
      finiteStageMatrixOperatorKOne hd i
        ((matrixAFStageOperatorKOneEquivInt hd i).symm z) :=
    Module.DirectLimit.of_f
    (R := ℤ) (G := fun i ↦ MatrixAFStageOperatorKOne localDim i)
    (f := fun i j hij ↦ matrixAFOperatorKOneTransition hd i j hij)
    (hij := hij)
  rw [matrixAFOperatorKOneTransition_symm_charge] at h
  exact h

/-- Inverse map from the integer charge limit to the literal matrix operator-`K₁` limit. -/
def chargeLimitToPrimeAFCircleOperatorKOne {localDim : ℕ → ℕ}
    (hd : ∀ k, 0 < localDim k) :
    AFChargeLimit localDim →ₗ[ℤ] PrimeAFCircleOperatorKOne hd :=
  Module.DirectLimit.lift ℤ ℕ (fun _ : ℕ ↦ ℤ) (chargeTransition localDim)
    (chargeStageToPrimeAFCircleOperatorKOne hd)
    (chargeStageToPrimeAFCircleOperatorKOne_compatible hd)

@[simp] theorem chargeLimitToPrimeAFCircleOperatorKOne_finiteStage
    {localDim : ℕ → ℕ} (hd : ∀ k, 0 < localDim k)
    (i : ℕ) (z : ℤ) :
    chargeLimitToPrimeAFCircleOperatorKOne hd
        (finiteStageCharge localDim i z) =
      finiteStageMatrixOperatorKOne hd i
        ((matrixAFStageOperatorKOneEquivInt hd i).symm z) := by
  unfold chargeLimitToPrimeAFCircleOperatorKOne finiteStageCharge
    chargeStageToPrimeAFCircleOperatorKOne
  exact Module.DirectLimit.lift_of
    (chargeStageToPrimeAFCircleOperatorKOne hd)
    (chargeStageToPrimeAFCircleOperatorKOne_compatible hd) z

theorem chargeLimitToPrimeAFCircleOperatorKOne_leftInverse
    {localDim : ℕ → ℕ} (hd : ∀ k, 0 < localDim k) :
    Function.LeftInverse (chargeLimitToPrimeAFCircleOperatorKOne hd)
      (primeAFCircleOperatorKOneToChargeLimit hd) := by
  intro q
  induction q using Module.DirectLimit.induction_on with
  | ih i x =>
      change chargeLimitToPrimeAFCircleOperatorKOne hd
          (primeAFCircleOperatorKOneToChargeLimit hd
            (finiteStageMatrixOperatorKOne hd i x)) =
        finiteStageMatrixOperatorKOne hd i x
      rw [primeAFCircleOperatorKOneToChargeLimit_finiteStage,
        chargeLimitToPrimeAFCircleOperatorKOne_finiteStage]
      apply congrArg (finiteStageMatrixOperatorKOne hd i)
      apply (matrixAFStageOperatorKOneEquivInt hd i).injective
      rw [AddEquiv.apply_symm_apply]
      rfl

theorem chargeLimitToPrimeAFCircleOperatorKOne_rightInverse
    {localDim : ℕ → ℕ} (hd : ∀ k, 0 < localDim k) :
    Function.RightInverse (chargeLimitToPrimeAFCircleOperatorKOne hd)
      (primeAFCircleOperatorKOneToChargeLimit hd) := by
  intro q
  induction q using Module.DirectLimit.induction_on with
  | ih i z =>
      change primeAFCircleOperatorKOneToChargeLimit hd
          (chargeLimitToPrimeAFCircleOperatorKOne hd
            (finiteStageCharge localDim i z)) =
        finiteStageCharge localDim i z
      rw [chargeLimitToPrimeAFCircleOperatorKOne_finiteStage,
        primeAFCircleOperatorKOneToChargeLimit_finiteStage]
      rw [← matrixAFStageOperatorKOneEquivInt_apply hd i
        ((matrixAFStageOperatorKOneEquivInt hd i).symm z)]
      simp

/-- Exact equivalence between the matrix-loop colimit and `colim(ℤ, ×dᵢ)`. -/
def primeAFCircleOperatorKOneEquivChargeLimit
    {localDim : ℕ → ℕ} (hd : ∀ k, 0 < localDim k) :
    PrimeAFCircleOperatorKOne hd ≃ₗ[ℤ] AFChargeLimit localDim :=
  LinearEquiv.ofBijective (primeAFCircleOperatorKOneToChargeLimit hd)
    ⟨(chargeLimitToPrimeAFCircleOperatorKOne_leftInverse hd).injective,
      (chargeLimitToPrimeAFCircleOperatorKOne_rightInverse hd).surjective⟩

/-- Physical one-factor amplification represents the same operator-`K₁` direct-limit class. -/
theorem finiteStageMatrixOperatorKOne_physical_succ
    {localDim : ℕ → ℕ} (hd : ∀ k, 0 < localDim k)
    (i : ℕ) (x : MatrixAFStageOperatorKOne localDim i) :
    finiteStageMatrixOperatorKOne hd (i + 1)
        (matrixAFPhysicalSuccKOneHom localDim i x) =
      finiteStageMatrixOperatorKOne hd i x := by
  have h : finiteStageMatrixOperatorKOne hd (i + 1)
      (matrixAFOperatorKOneTransition hd i (i + 1) (Nat.le_succ i) x) =
      finiteStageMatrixOperatorKOne hd i x :=
    Module.DirectLimit.of_f
    (R := ℤ) (G := fun i ↦ MatrixAFStageOperatorKOne localDim i)
    (f := fun i j hij ↦ matrixAFOperatorKOneTransition hd i j hij)
    (hij := Nat.le_succ i)
  rw [matrixAFOperatorKOneTransition_succ_eq_physical] at h
  exact h

/-- Every literal AF operator-`K₁` class has a finite matrix-stage ancestor. -/
theorem primeAFCircleOperatorKOne_has_finiteAncestor
    {localDim : ℕ → ℕ} (hd : ∀ k, 0 < localDim k)
    (q : PrimeAFCircleOperatorKOne hd) :
    ∃ i x, finiteStageMatrixOperatorKOne hd i x = q := by
  exact Module.DirectLimit.exists_of q

/-- Every nonzero AF operator-`K₁` class has a nonzero finite matrix-stage ancestor. -/
theorem nonzero_primeAFCircleOperatorKOne_has_nonzero_finiteAncestor
    {localDim : ℕ → ℕ} (hd : ∀ k, 0 < localDim k)
    {q : PrimeAFCircleOperatorKOne hd} (hq : q ≠ 0) :
    ∃ i x, x ≠ 0 ∧ finiteStageMatrixOperatorKOne hd i x = q := by
  obtain ⟨i, x, hx⟩ := primeAFCircleOperatorKOne_has_finiteAncestor hd q
  refine ⟨i, x, ?_, hx⟩
  intro hx0
  subst x
  exact hq (by simpa using hx.symm)

/-- Positive local dimensions prevent collapse of every finite matrix-stage operator-`K₁` class. -/
theorem finiteStageMatrixOperatorKOne_injective
    {localDim : ℕ → ℕ} (hd : ∀ k, 0 < localDim k) (i : ℕ) :
    Function.Injective (finiteStageMatrixOperatorKOne hd i) := by
  intro x y hxy
  have hcharge := congrArg (primeAFCircleOperatorKOneToChargeLimit hd) hxy
  rw [primeAFCircleOperatorKOneToChargeLimit_finiteStage,
    primeAFCircleOperatorKOneToChargeLimit_finiteStage] at hcharge
  have hxyCharge := finiteStageCharge_injective hd i hcharge
  exact (matrixAFStageOperatorKOneEquivInt hd i).injective hxyCharge

/-- Tensoring by a positive-dimensional identity is injective on literal finite-stage `K₁`. -/
theorem matrixAFPhysicalSuccKOneHom_injective
    {localDim : ℕ → ℕ} (hd : ∀ k, 0 < localDim k) (i : ℕ) :
    Function.Injective (matrixAFPhysicalSuccKOneHom localDim i) := by
  intro x y hxy
  apply (matrixAFStageOperatorKOneEquivInt hd i).injective
  have hmul : (localDim (i + 1) : ℤ) * finiteMatrixOperatorKOneCharge x =
      (localDim (i + 1) : ℤ) * finiteMatrixOperatorKOneCharge y := by
    rw [← matrixAFPhysicalSuccKOneHom_charge localDim i x,
      ← matrixAFPhysicalSuccKOneHom_charge localDim i y, hxy]
  exact mul_left_cancel₀ (Int.ofNat_ne_zero.mpr (hd (i + 1)).ne') hmul

theorem matrixAFPhysicalSuccKOneHom_eq_zero_iff
    {localDim : ℕ → ℕ} (hd : ∀ k, 0 < localDim k) (i : ℕ)
    (x : MatrixAFStageOperatorKOne localDim i) :
    matrixAFPhysicalSuccKOneHom localDim i x = 0 ↔ x = 0 := by
  constructor
  · intro hx
    apply matrixAFPhysicalSuccKOneHom_injective hd i
    simpa using hx
  · rintro rfl
    simp

/-- If every finite ancestor of an AF operator-`K₁` class is zero, the class itself is zero. -/
theorem primeAFCircleOperatorKOne_eq_zero_of_all_ancestors_zero
    {localDim : ℕ → ℕ} (hd : ∀ k, 0 < localDim k)
    {q : PrimeAFCircleOperatorKOne hd}
    (hzero : ∀ i x, finiteStageMatrixOperatorKOne hd i x = q → x = 0) :
    q = 0 := by
  obtain ⟨i, x, hx⟩ := primeAFCircleOperatorKOne_has_finiteAncestor hd q
  rw [hzero i x hx] at hx
  simpa using hx.symm

theorem primeAFCircleOperatorKOneToChargeLimit_injective
    {localDim : ℕ → ℕ} (hd : ∀ k, 0 < localDim k) :
    Function.Injective (primeAFCircleOperatorKOneToChargeLimit hd) :=
  (chargeLimitToPrimeAFCircleOperatorKOne_leftInverse hd).injective

theorem primeAFCircleOperatorKOne_charge_eq_zero_iff
    {localDim : ℕ → ℕ} (hd : ∀ k, 0 < localDim k)
    (q : PrimeAFCircleOperatorKOne hd) :
    primeAFCircleOperatorKOneToChargeLimit hd q = 0 ↔ q = 0 := by
  constructor
  · intro hq
    apply primeAFCircleOperatorKOneToChargeLimit_injective hd
    simpa using hq
  · rintro rfl
    simp

/-- Faithful normalized rational charge of the literal AF operator-`K₁` group. -/
def primeAFCircleOperatorKOneToRational
    {localDim : ℕ → ℕ} (hd : ∀ k, 0 < localDim k) :
    PrimeAFCircleOperatorKOne hd →ₗ[ℤ] ℚ :=
  (afChargeToRational hd).comp
    (primeAFCircleOperatorKOneToChargeLimit hd)

theorem primeAFCircleOperatorKOneToRational_injective
    {localDim : ℕ → ℕ} (hd : ∀ k, 0 < localDim k) :
    Function.Injective (primeAFCircleOperatorKOneToRational hd) :=
  (afChargeToRational_injective hd).comp
    (primeAFCircleOperatorKOneToChargeLimit_injective hd)

@[simp] theorem primeAFCircleOperatorKOneToRational_finiteStage
    {localDim : ℕ → ℕ} (hd : ∀ k, 0 < localDim k)
    (i : ℕ) (x : MatrixAFStageOperatorKOne localDim i) :
    primeAFCircleOperatorKOneToRational hd
        (finiteStageMatrixOperatorKOne hd i x) =
      (finiteMatrixOperatorKOneCharge x : ℚ) /
        matrixAFStageDimension localDim i := by
  rw [primeAFCircleOperatorKOneToRational,
    LinearMap.comp_apply,
    primeAFCircleOperatorKOneToChargeLimit_finiteStage,
    afChargeToRational_finiteStage]
  congr 1
  norm_cast
  exact (matrixAFStageDimension_eq_chargeDenominator localDim i).symm

end

end PrimeQuasiLocalCharge
