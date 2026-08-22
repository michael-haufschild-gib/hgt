import GaloisForLFunctions.HTGeometry.FiniteSpecialUnitaryPauliHybridAtlas
import GaloisForLFunctions.HTGeometry.HaferkampSpecialUnitaryPauliL2Chart

/-!
# L2-analytic hybrid Pauli/exponential atlas

For every fixed normalized Euclidean exponential word, the Pauli factor of
the hybrid atlas is real analytic in the same L2 operator norm.  At its zero
Pauli coordinate, its derivative retains all fifteen Pauli directions.  The
uniform-word theorem therefore supplies a full-rank analytic slice through
every finite two-qubit special unitary, with no norm transport and no resource
limit override.
-/

open Matrix
open scoped Matrix.Norms.L2Operator

namespace GaloisForLFunctions.HTGeometry

noncomputable section

local instance : DecidableEq boolNonidentityTwoQubitPauliLabel := Classical.decEq _
local instance : Fintype boolNonidentityTwoQubitPauliLabel := Fintype.ofFinite _

/-- Right multiplication by a two-qubit unitary as a real continuous linear map. -/
def boolTwoQubitMatrixRightMulCLM (U : Matrix.unitaryGroup (Bool × Bool) ℂ) :
    Matrix (Bool × Bool) (Bool × Bool) ℂ →L[ℝ]
      Matrix (Bool × Bool) (Bool × Bool) ℂ :=
  (show Matrix (Bool × Bool) (Bool × Bool) ℂ →ₗ[ℝ]
      Matrix (Bool × Bool) (Bool × Bool) ℂ from
    { toFun := fun A => A * (U : Matrix (Bool × Bool) (Bool × Bool) ℂ)
      map_add' := by
        intro A B
        exact Matrix.add_mul A B (U : Matrix (Bool × Bool) (Bool × Bool) ℂ)
      map_smul' := by
        intro c A
        exact Matrix.smul_mul c A (U : Matrix (Bool × Bool) (Bool × Bool) ℂ) }).toContinuousLinearMap

@[simp] theorem boolTwoQubitMatrixRightMulCLM_apply
    (U : Matrix.unitaryGroup (Bool × Bool) ℂ)
    (A : Matrix (Bool × Bool) (Bool × Bool) ℂ) :
    boolTwoQubitMatrixRightMulCLM U A = A * (U : Matrix (Bool × Bool) (Bool × Bool) ℂ) := rfl

/-- Right multiplication by a unitary matrix is injective. -/
theorem boolTwoQubitMatrixRightMulCLM_injective
    (U : Matrix.unitaryGroup (Bool × Bool) ℂ) :
    Function.Injective (boolTwoQubitMatrixRightMulCLM U) := by
  intro A B h
  have hmul := congrArg (fun M : Matrix (Bool × Bool) (Bool × Bool) ℂ =>
    M * ((U⁻¹ : Matrix.unitaryGroup (Bool × Bool) ℂ) :
      Matrix (Bool × Bool) (Bool × Bool) ℂ)) h
  simp only [boolTwoQubitMatrixRightMulCLM_apply, Matrix.mul_assoc] at hmul
  simpa using hmul

/-- A fixed normalized Euclidean word leaves a fifteen-coordinate Pauli slice. -/
def boolNonidentityTwoQubitPauliHybridSlice
    (N : ℕ) (Y : boolTwoQubitEuclideanWordCoordinates N) :
    (boolNonidentityTwoQubitPauliLabel → ℝ) →
      Matrix (Bool × Bool) (Bool × Bool) ℂ :=
  fun x => boolNonidentityTwoQubitPauliHybridAtlas N x Y

/-- The hybrid slice is literally the Pauli chart followed by a fixed right unitary. -/
theorem boolNonidentityTwoQubitPauliHybridSlice_eq
    (N : ℕ) (Y : boolTwoQubitEuclideanWordCoordinates N) :
    boolNonidentityTwoQubitPauliHybridSlice N Y = fun x =>
      boolNonidentityTwoQubitPauliCoordinateChart x *
        (specialUnitaryNormalize (false, false)
          (finiteUnitaryEuclideanExponentialWord (Bool × Bool) N Y) :
          Matrix (Bool × Bool) (Bool × Bool) ℂ) := by
  funext x
  simpa [boolNonidentityTwoQubitPauliHybridSlice,
    boolNonidentityTwoQubitPauliCoordinateGate_coe] using
    congrArg (fun V : Matrix.specialUnitaryGroup (Bool × Bool) ℂ =>
      (V : Matrix (Bool × Bool) (Bool × Bool) ℂ))
      (boolNonidentityTwoQubitPauliHybridAtlas_eq N x Y)

/-- Every fixed hybrid Pauli slice is real analytic in its Pauli coordinates. -/
theorem analyticAt_boolNonidentityTwoQubitPauliHybridSlice
    (N : ℕ) (Y : boolTwoQubitEuclideanWordCoordinates N)
    (x : boolNonidentityTwoQubitPauliLabel → ℝ) :
    AnalyticAt ℝ (boolNonidentityTwoQubitPauliHybridSlice N Y) x := by
  let V : Matrix.specialUnitaryGroup (Bool × Bool) ℂ :=
    specialUnitaryNormalize (false, false)
      (finiteUnitaryEuclideanExponentialWord (Bool × Bool) N Y)
  let R := boolTwoQubitMatrixRightMulCLM (specialUnitaryToUnitary V)
  have hR : AnalyticAt ℝ (fun A : Matrix (Bool × Bool) (Bool × Bool) ℂ => R A)
      (boolNonidentityTwoQubitPauliCoordinateChart x) := R.analyticAt _
  have h := hR.comp (analyticAt_boolNonidentityTwoQubitPauliCoordinateChart_l2 x)
  change AnalyticAt ℝ
    (fun z => R (boolNonidentityTwoQubitPauliCoordinateChart z)) x at h
  rw [show boolNonidentityTwoQubitPauliHybridSlice N Y =
      fun z => R (boolNonidentityTwoQubitPauliCoordinateChart z) by
        rw [boolNonidentityTwoQubitPauliHybridSlice_eq]
        funext z
        exact boolTwoQubitMatrixRightMulCLM_apply (specialUnitaryToUnitary V) _]
  exact h

/-- The hybrid slice derivative at zero is the Pauli tangent map followed by its fixed right unitary. -/
theorem hasFDerivAt_boolNonidentityTwoQubitPauliHybridSlice_zero
    (N : ℕ) (Y : boolTwoQubitEuclideanWordCoordinates N) :
    HasFDerivAt (boolNonidentityTwoQubitPauliHybridSlice N Y)
      ((boolTwoQubitMatrixRightMulCLM
        (specialUnitaryToUnitary (specialUnitaryNormalize (false, false)
          (finiteUnitaryEuclideanExponentialWord (Bool × Bool) N Y)))).comp
        boolNonidentityTwoQubitPauliTangentMap) 0 := by
  let V : Matrix.specialUnitaryGroup (Bool × Bool) ℂ :=
    specialUnitaryNormalize (false, false)
      (finiteUnitaryEuclideanExponentialWord (Bool × Bool) N Y)
  let R := boolTwoQubitMatrixRightMulCLM (specialUnitaryToUnitary V)
  have h := R.hasFDerivAt.comp 0
    hasFDerivAt_boolNonidentityTwoQubitPauliCoordinateChart_zero_l2
  change HasFDerivAt
    (fun z => R (boolNonidentityTwoQubitPauliCoordinateChart z))
    (R.comp boolNonidentityTwoQubitPauliTangentMap) 0 at h
  rw [show boolNonidentityTwoQubitPauliHybridSlice N Y =
      fun z => R (boolNonidentityTwoQubitPauliCoordinateChart z) by
        rw [boolNonidentityTwoQubitPauliHybridSlice_eq]
        funext z
        exact boolTwoQubitMatrixRightMulCLM_apply (specialUnitaryToUnitary V) _]
  exact h

/-- Every globally centred hybrid Pauli slice has exact derivative rank fifteen at its centre. -/
theorem finrank_range_fderiv_boolNonidentityTwoQubitPauliHybridSlice_zero
    (N : ℕ) (Y : boolTwoQubitEuclideanWordCoordinates N) :
    Module.finrank ℝ
      (fderiv ℝ (boolNonidentityTwoQubitPauliHybridSlice N Y) 0).range = 15 := by
  let V : Matrix.specialUnitaryGroup (Bool × Bool) ℂ :=
    specialUnitaryNormalize (false, false)
      (finiteUnitaryEuclideanExponentialWord (Bool × Bool) N Y)
  let R := boolTwoQubitMatrixRightMulCLM (specialUnitaryToUnitary V)
  let D : (boolNonidentityTwoQubitPauliLabel → ℝ) →L[ℝ]
      Matrix (Bool × Bool) (Bool × Bool) ℂ :=
    fderiv ℝ (boolNonidentityTwoQubitPauliHybridSlice N Y) 0
  change Module.finrank ℝ D.range = 15
  have hD : D = R.comp boolNonidentityTwoQubitPauliTangentMap := by
    exact hasFDerivAt_boolNonidentityTwoQubitPauliHybridSlice_zero N Y |>.fderiv
  rw [hD]
  apply le_antisymm
  · calc
      Module.finrank ℝ (R.comp boolNonidentityTwoQubitPauliTangentMap).range ≤
          Module.finrank ℝ (boolNonidentityTwoQubitPauliLabel → ℝ) :=
        LinearMap.finrank_range_le (R.comp boolNonidentityTwoQubitPauliTangentMap).toLinearMap
      _ = Fintype.card boolNonidentityTwoQubitPauliLabel := Module.finrank_pi ℝ
      _ = 15 := card_boolNonidentityTwoQubitPauliLabel
  · rw [← card_boolNonidentityTwoQubitPauliLabel]
    let values : boolNonidentityTwoQubitPauliLabel →
        (R.comp boolNonidentityTwoQubitPauliTangentMap).range :=
      fun pq => ⟨(R.comp boolNonidentityTwoQubitPauliTangentMap) (Pi.single pq 1),
        ⟨Pi.single pq 1, rfl⟩⟩
    have hbase : LinearIndependent ℝ (fun pq : boolNonidentityTwoQubitPauliLabel =>
        boolNonidentityTwoQubitPauliTangentMap (Pi.single pq 1)) :=
      linearIndependent_boolNonidentityTwoQubitPauliTangentMap_single
    have hker : R.toLinearMap.ker = ⊥ :=
      LinearMap.ker_eq_bot_of_injective (boolTwoQubitMatrixRightMulCLM_injective _)
    have himages : LinearIndependent ℝ (fun pq : boolNonidentityTwoQubitPauliLabel =>
        (R.comp boolNonidentityTwoQubitPauliTangentMap) (Pi.single pq 1)) := by
      simpa [Function.comp_def] using hbase.map' R.toLinearMap hker
    have hcomp : LinearIndependent ℝ
        ((R.comp boolNonidentityTwoQubitPauliTangentMap).range.subtype ∘ values) := by
      have hfun :
          (R.comp boolNonidentityTwoQubitPauliTangentMap).range.subtype ∘ values =
            fun pq : boolNonidentityTwoQubitPauliLabel =>
              (R.comp boolNonidentityTwoQubitPauliTangentMap) (Pi.single pq 1) := by
        funext pq
        rfl
      rw [hfun]
      exact himages
    have hvalues : LinearIndependent ℝ values :=
      LinearIndependent.of_comp
        (R.comp boolNonidentityTwoQubitPauliTangentMap).range.subtype hcomp
    calc
      Fintype.card boolNonidentityTwoQubitPauliLabel =
          (Set.range values).finrank ℝ := by
            simpa using (linearIndependent_iff_card_eq_finrank_span.mp hvalues)
      _ = Module.finrank ℝ
          (Submodule.span ℝ (Set.range values)) := rfl
      _ ≤ Module.finrank ℝ
          (R.comp boolNonidentityTwoQubitPauliTangentMap).range :=
        Submodule.finrank_le _

/-- One fixed word length supplies a rank-fifteen analytic Pauli slice through every `SU(4)` point. -/
theorem exists_uniform_boolNonidentityTwoQubitPauliHybridSlice_l2 :
    ∃ N : ℕ, ∀ S : Matrix.specialUnitaryGroup (Bool × Bool) ℂ,
      ∃ Y : boolTwoQubitEuclideanWordCoordinates N,
        boolNonidentityTwoQubitPauliHybridSlice N Y 0 =
          (S : Matrix (Bool × Bool) (Bool × Bool) ℂ) ∧
        AnalyticAt ℝ (boolNonidentityTwoQubitPauliHybridSlice N Y) 0 ∧
        Module.finrank ℝ
          (fderiv ℝ (boolNonidentityTwoQubitPauliHybridSlice N Y) 0).range = 15 := by
  obtain ⟨N, hN⟩ := exists_boolNonidentityTwoQubitPauliHybridAtlas_center
  refine ⟨N, fun S => ?_⟩
  obtain ⟨Y, hY⟩ := hN S
  refine ⟨Y, ?_,
    analyticAt_boolNonidentityTwoQubitPauliHybridSlice N Y 0,
    finrank_range_fderiv_boolNonidentityTwoQubitPauliHybridSlice_zero N Y⟩
  simpa [boolNonidentityTwoQubitPauliHybridSlice] using
    congrArg (fun V : Matrix.specialUnitaryGroup (Bool × Bool) ℂ =>
      (V : Matrix (Bool × Bool) (Bool × Bool) ℂ)) hY

end

end GaloisForLFunctions.HTGeometry
