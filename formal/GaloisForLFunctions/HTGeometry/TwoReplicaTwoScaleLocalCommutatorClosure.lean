import GaloisForLFunctions.HTGeometry.TwoReplicaRationalLocalRotationCovariance
import GaloisForLFunctions.HTGeometry.TwoReplicaTwoScaleCommutatorDealiasing

/-!
# Two-scale closure of every one-site collective commutator

Exact conjugation at rational scales `1` and `2` removes the relative-parity
alias present at a single Clifford scale.  The resulting identity recovers
the full one-site collective commutator, for every input matrix, from four
finite conjugates.  Hence every one-site collective commutator acts internally
on the canonical greatest q-local Hall obstruction, with no character-sector
premise.
-/

open scoped Matrix Kronecker
open Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

theorem finiteSingleSiteDoubleRotationGate_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (j : V) (a : Fin 3) :
    finiteSingleSiteDoubleRotationGate j a =
      1 + (2 * Complex.I) •
        finitePauliMatrix (finiteSingleSitePauliLabel j a) := by
  rw [finiteSingleSiteDoubleRotationGate, boolPauliDoubleRotationGate,
    finiteSingleSiteMatrix_add, finiteSingleSiteMatrix_one,
    finiteSingleSiteMatrix_smul, finiteSingleSiteMatrix_pauli]

theorem finiteSingleSiteDoubleRotationGateInv_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (j : V) (a : Fin 3) :
    finiteSingleSiteDoubleRotationGateInv j a =
      (1 / 5 : ℂ) •
        (1 - (2 * Complex.I) •
          finitePauliMatrix (finiteSingleSitePauliLabel j a)) := by
  rw [finiteSingleSiteDoubleRotationGateInv, boolPauliDoubleRotationGateInv,
    finiteSingleSiteMatrix_smul]
  congr 1
  rw [sub_eq_add_neg, finiteSingleSiteMatrix_add,
    finiteSingleSiteMatrix_one]
  rw [show -((2 * Complex.I) • finiteQubitPauli a) =
      (-1 : ℂ) • ((2 * Complex.I) • finiteQubitPauli a) by module]
  rw [finiteSingleSiteMatrix_smul, finiteSingleSiteMatrix_smul,
    finiteSingleSiteMatrix_pauli]
  module

theorem finiteSingleSiteDoubleRotationDoubledGate_twoScaleRaw
    {V : Type*} [Fintype V] [DecidableEq V]
    (j : V) (a : Fin 3) :
    let P := finiteSingleSitePauliLabel j a
    let A := finiteTwoReplicaPauliLeft P
    let B := finiteTwoReplicaPauliRight P
    let J : FiniteTwoReplicaMatrix V := Complex.I • 1
    let T2p : FiniteTwoReplicaMatrix V :=
      1 + 2 * J * (A + B) - 4 * (A * B)
    finiteSingleSiteDoubleRotationDoubledGate j a = T2p := by
  dsimp
  have htwoMatrix : (2 : FiniteTwoReplicaMatrix V) =
      (2 : ℂ) • (1 : FiniteTwoReplicaMatrix V) := by
    ext x y
    by_cases hxy : x = y <;>
      simp [Matrix.ofNat_apply, Matrix.smul_apply, Matrix.one_apply, hxy]
  have hfourMatrix : (4 : FiniteTwoReplicaMatrix V) =
      (4 : ℂ) • (1 : FiniteTwoReplicaMatrix V) := by
    ext x y
    by_cases hxy : x = y <;>
      simp [Matrix.ofNat_apply, Matrix.smul_apply, Matrix.one_apply, hxy]
  rw [finiteSingleSiteDoubleRotationDoubledGate,
    finiteSingleSiteDoubleRotationGate_eq]
  simp only [Matrix.add_kronecker, Matrix.kronecker_add,
    Matrix.smul_kronecker, Matrix.kronecker_smul]
  rw [Matrix.one_kronecker_one, finiteTwoReplicaPauliLeft_mul_right,
    htwoMatrix, hfourMatrix]
  simp only [smul_mul_assoc, Matrix.one_mul, Matrix.mul_smul, smul_smul]
  simp only [finiteTwoReplicaPauliLeft, finiteTwoReplicaPauliRight,
    finiteTwoReplicaPairedPauli, smul_add, smul_smul]
  have hcoeff : (2 * Complex.I) * (2 * Complex.I) = (-4 : ℂ) := by
    calc
      (2 * Complex.I) * (2 * Complex.I) = 4 * (Complex.I * Complex.I) := by ring
      _ = -4 := by rw [Complex.I_mul_I]; norm_num
  rw [hcoeff]
  module

theorem finiteSingleSiteDoubleRotationDoubledGateInv_twoScaleRaw
    {V : Type*} [Fintype V] [DecidableEq V]
    (j : V) (a : Fin 3) :
    let P := finiteSingleSitePauliLabel j a
    let A := finiteTwoReplicaPauliLeft P
    let B := finiteTwoReplicaPauliRight P
    let J : FiniteTwoReplicaMatrix V := Complex.I • 1
    let T2m : FiniteTwoReplicaMatrix V :=
      1 - 2 * J * (A + B) - 4 * (A * B)
    finiteSingleSiteDoubleRotationDoubledGateInv j a =
      (1 / 25 : ℂ) • T2m := by
  dsimp
  have htwoMatrix : (2 : FiniteTwoReplicaMatrix V) =
      (2 : ℂ) • (1 : FiniteTwoReplicaMatrix V) := by
    ext x y
    by_cases hxy : x = y <;>
      simp [Matrix.ofNat_apply, Matrix.smul_apply, Matrix.one_apply, hxy]
  have hfourMatrix : (4 : FiniteTwoReplicaMatrix V) =
      (4 : ℂ) • (1 : FiniteTwoReplicaMatrix V) := by
    ext x y
    by_cases hxy : x = y <;>
      simp [Matrix.ofNat_apply, Matrix.smul_apply, Matrix.one_apply, hxy]
  rw [finiteSingleSiteDoubleRotationDoubledGateInv,
    finiteSingleSiteDoubleRotationGateInv_eq]
  simp only [sub_eq_add_neg, ← neg_smul, Matrix.smul_kronecker,
    Matrix.kronecker_smul, smul_smul, Matrix.add_kronecker,
    Matrix.kronecker_add]
  rw [Matrix.one_kronecker_one, finiteTwoReplicaPauliLeft_mul_right,
    htwoMatrix, hfourMatrix]
  simp only [smul_mul_assoc, Matrix.one_mul, Matrix.mul_smul, smul_smul]
  simp only [finiteTwoReplicaPauliLeft, finiteTwoReplicaPauliRight,
    finiteTwoReplicaPairedPauli, smul_add, smul_smul]
  have hcoeff :
      (1 / 5 : ℂ) * (-(2 * Complex.I) * (1 / 5) * -(2 * Complex.I)) =
        (-4 / 25 : ℂ) := by
    rw [show (1 / 5 : ℂ) * (-(2 * Complex.I) * (1 / 5) * -(2 * Complex.I)) =
        (4 / 25 : ℂ) * (Complex.I * Complex.I) by ring,
      Complex.I_mul_I]
    norm_num
  rw [hcoeff]
  module

theorem finiteTwoReplicaSingleSiteCollectiveCommutator_eq_twoScaleDifference
    {V : Type*} [Fintype V] [DecidableEq V]
    (j : V) (a : Fin 3) (X : FiniteTwoReplicaMatrix V) :
    finiteTwoReplicaCollectiveCommutatorLinear
        (finiteSingleSitePauliLabel j a) X =
      (Complex.I / 12 : ℂ) •
        ((25 : ℂ) •
            (finiteSingleSiteDoubleRotationDoubledConjugationEquiv j a X -
              (finiteSingleSiteDoubleRotationDoubledConjugationEquiv j a).symm X) -
          (32 : ℂ) •
            (finiteProductCliffordDoubledConjugationEquiv
                (finiteSingleSiteQuarterTurnCode j a) X -
              (finiteProductCliffordDoubledConjugationEquiv
                (finiteSingleSiteQuarterTurnCode j a)).symm X)) := by
  let P := finiteSingleSitePauliLabel j a
  let A := finiteTwoReplicaPauliLeft P
  let B := finiteTwoReplicaPauliRight P
  let J : FiniteTwoReplicaMatrix V := Complex.I • 1
  let T1p : FiniteTwoReplicaMatrix V := 1 + J * (A + B) - A * B
  let T1m : FiniteTwoReplicaMatrix V := 1 - J * (A + B) - A * B
  let T2p : FiniteTwoReplicaMatrix V := 1 + 2 * J * (A + B) - 4 * (A * B)
  let T2m : FiniteTwoReplicaMatrix V := 1 - 2 * J * (A + B) - 4 * (A * B)
  have hA : A * A = 1 := by simp [A]
  have hB : B * B = 1 := by simp [B]
  have hAB : A * B = B * A := by
    dsimp [A, B]
    rw [finiteTwoReplicaPauliLeft_mul_right,
      finiteTwoReplicaPauliRight_mul_left]
  have hJ : J * J = -1 := by
    dsimp [J]
    rw [smul_mul_assoc, Matrix.one_mul, smul_smul]
    norm_num
  have hJA : J * A = A * J := by
    dsimp [J]
    rw [smul_mul_assoc, mul_smul_comm]
    simp
  have hJB : J * B = B * J := by
    dsimp [J]
    rw [smul_mul_assoc, mul_smul_comm]
    simp
  have hJX : J * X = X * J := by
    dsimp [J]
    rw [smul_mul_assoc, mul_smul_comm]
    simp
  have hraw := twoInvolutionTwoScaleDifferenceIdentity
    A B J X hA hB hAB hJ hJA hJB hJX
  have hquarter :
      finiteProductCliffordDoubledGate
          (finiteSingleSiteQuarterTurnCode j a) =
        (1 / 2 : ℂ) • T1p := by
    rw [finiteProductCliffordDoubledGate_singleSiteQuarterTurn]
    congr 1
    dsimp [T1p, J, A, B, P]
    rw [smul_mul_assoc]
    simp [finiteTwoReplicaPauliLeft_mul_right]
  have hquarterInv :
      (finiteProductCliffordDoubledGate
          (finiteSingleSiteQuarterTurnCode j a))ᴴ =
        (1 / 2 : ℂ) • T1m := by
    rw [finiteProductCliffordDoubledGate_singleSiteQuarterTurn_conjTranspose]
    congr 1
    dsimp [T1m, J, A, B, P]
    rw [smul_mul_assoc]
    simp [finiteTwoReplicaPauliLeft_mul_right]
  have hdouble : finiteSingleSiteDoubleRotationDoubledGate j a = T2p := by
    simpa [P, A, B, J, T2p] using
      finiteSingleSiteDoubleRotationDoubledGate_twoScaleRaw j a
  have hdoubleInv :
      finiteSingleSiteDoubleRotationDoubledGateInv j a =
        (1 / 25 : ℂ) • T2m := by
    simpa [P, A, B, J, T2m] using
      finiteSingleSiteDoubleRotationDoubledGateInv_twoScaleRaw j a
  rw [finiteSingleSiteDoubleRotationDoubledConjugationEquiv_apply,
    finiteSingleSiteDoubleRotationDoubledConjugationEquiv_symm_apply,
    finiteProductCliffordDoubledConjugationEquiv_apply,
    finiteProductCliffordDoubledConjugationEquiv_symm_apply,
    hdouble, hdoubleInv, hquarterInv, hquarter]
  change finiteTwoReplicaCollectiveCommutator P X = _
  rw [finiteTwoReplicaCollectiveCommutator, ← ringCommutator_add_left']
  change ringCommutator (A + B) X = _
  have hscale2 :
      T2p * X * ((1 / 25 : ℂ) • T2m) -
          ((1 / 25 : ℂ) • T2m) * X * T2p =
        (1 / 25 : ℂ) • (T2p * X * T2m - T2m * X * T2p) := by
    simp only [Matrix.smul_mul, Matrix.mul_smul]
    module
  have hscale1 :
      ((1 / 2 : ℂ) • T1p) * X * ((1 / 2 : ℂ) • T1m) -
          ((1 / 2 : ℂ) • T1m) * X * ((1 / 2 : ℂ) • T1p) =
        (1 / 4 : ℂ) • (T1p * X * T1m - T1m * X * T1p) := by
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    module
  rw [hscale2, hscale1]
  change 12 * ringCommutator (A + B) X =
      J * ((T2p * X * T2m - T2m * X * T2p) -
        8 * (T1p * X * T1m - T1m * X * T1p)) at hraw
  have hJmul (Y : FiniteTwoReplicaMatrix V) : J * Y = Complex.I • Y := by
    dsimp [J]
    rw [smul_mul_assoc, Matrix.one_mul]
  have htwelveMatrix : (12 : FiniteTwoReplicaMatrix V) =
      (12 : ℂ) • (1 : FiniteTwoReplicaMatrix V) := by
    ext x y
    by_cases hxy : x = y <;>
      simp [Matrix.ofNat_apply, Matrix.smul_apply, Matrix.one_apply, hxy]
  have heightMatrix : (8 : FiniteTwoReplicaMatrix V) =
      (8 : ℂ) • (1 : FiniteTwoReplicaMatrix V) := by
    ext x y
    by_cases hxy : x = y <;>
      simp [Matrix.ofNat_apply, Matrix.smul_apply, Matrix.one_apply, hxy]
  rw [htwelveMatrix, heightMatrix, smul_mul_assoc, Matrix.one_mul,
    smul_mul_assoc, Matrix.one_mul] at hraw
  simp only [smul_mul_assoc, Matrix.one_mul] at hraw
  have hsolve : ringCommutator (A + B) X =
      (Complex.I / 12 : ℂ) •
        ((T2p * X * T2m - T2m * X * T2p) -
          (8 : ℂ) • (T1p * X * T1m - T1m * X * T1p)) := by
    calc
      ringCommutator (A + B) X =
          (1 / 12 : ℂ) • ((12 : ℂ) • ringCommutator (A + B) X) := by
            module
      _ = (1 / 12 : ℂ) •
          (Complex.I • ((T2p * X * T2m - T2m * X * T2p) -
            (8 : ℂ) • (T1p * X * T1m - T1m * X * T1p))) := by
              rw [hraw]
      _ = (Complex.I / 12 : ℂ) •
          ((T2p * X * T2m - T2m * X * T2p) -
            (8 : ℂ) • (T1p * X * T1m - T1m * X * T1p)) := by
              module
  rw [hsolve]
  module

/-- Every one-site collective commutator maps the canonical greatest q-local
Hall obstruction back into itself.  Unlike quarter-turn interpolation alone,
this conclusion has no Pauli-character parity premise. -/
theorem finiteTwoReplicaSingleSiteCollectiveCommutator_mem_greatestMaximizer
    {V : Type*} [Fintype V] [DecidableEq V]
    (q : ℕ) (U : Submodule ℂ (FiniteTwoReplicaMatrix V))
    (hgreatest : ∀ W : Submodule ℂ (FiniteTwoReplicaMatrix V),
      linearFamilyDefect
          (finiteTwoReplicaQLocalCollectiveCommutatorLinear V q) W =
        linearFamilyDefect
          (finiteTwoReplicaQLocalCollectiveCommutatorLinear V q) U →
      W ≤ U)
    (j : V) (a : Fin 3) (X : FiniteTwoReplicaMatrix V) (hX : X ∈ U) :
    finiteTwoReplicaCollectiveCommutatorLinear
        (finiteSingleSitePauliLabel j a) X ∈ U := by
  let r := finiteSingleSiteDoubleRotationDoubledConjugationEquiv j a
  let c := finiteProductCliffordDoubledConjugationEquiv
    (finiteSingleSiteQuarterTurnCode j a)
  have hrFix : U.map (r : FiniteTwoReplicaMatrix V →ₗ[ℂ]
      FiniteTwoReplicaMatrix V) = U := by
    exact finiteTwoReplicaQLocal_greatestMaximizer_doubleRotation_fixed
      q U hgreatest j a
  have hrX : r X ∈ U := by
    rw [← hrFix]
    exact Submodule.mem_map_of_mem hX
  have hrInvX : r.symm X ∈ U := by
    have hmap : r (r.symm X) ∈ U.map
        (r : FiniteTwoReplicaMatrix V →ₗ[ℂ] FiniteTwoReplicaMatrix V) := by
      rw [hrFix]
      simpa using hX
    rcases hmap with ⟨Y, hYU, hY⟩
    have hYX : Y = r.symm X := by
      apply r.injective
      simpa using hY
    simpa [hYX] using hYU
  have hcX : c X ∈ U := by
    rw [← finiteTwoReplicaQLocal_greatestMaximizer_productClifford_fixed
      q U hgreatest (finiteSingleSiteQuarterTurnCode j a)]
    exact Submodule.mem_map_of_mem hX
  have hcInvX : c.symm X ∈ U := by
    rw [finiteProductCliffordDoubledConjugationEquiv_symm_eq]
    rw [← finiteTwoReplicaQLocal_greatestMaximizer_productClifford_fixed
      q U hgreatest _]
    exact Submodule.mem_map_of_mem hX
  rw [finiteTwoReplicaSingleSiteCollectiveCommutator_eq_twoScaleDifference
    j a X]
  exact U.smul_mem _
    (U.sub_mem
      (U.smul_mem _ (U.sub_mem hrX hrInvX))
      (U.smul_mem _ (U.sub_mem hcX hcInvX)))

end

end GaloisForLFunctions.HTGeometry
