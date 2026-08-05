import GaloisForLFunctions.HTGeometry.TwoReplicaGlobalCliffordHallSymmetryReduction
import GaloisForLFunctions.HTGeometry.PauliCharacterFirstDefectCovariance

/-!
# First-order Clifford interpolation on odd paired-Pauli characters

On a paired-Pauli odd sector, a collective Pauli commutator is exactly a
scalar multiple of the difference between two inverse strict Clifford
quarter-turn conjugations.  This is a first-order statement: it upgrades the
existing group-algebra formula for the square of the commutator and proves
that selected first images remain inside every product-Clifford-invariant
subspace.
-/

open scoped Matrix Kronecker

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open QuantumAlg

/-- Pure ring identity behind first-order quarter-turn interpolation on the
odd sector of two commuting involutions. -/
theorem twoInvolutionQuarterTurnOddDifferenceIdentity
    {R : Type*} [Ring R]
    (A B J X : R)
    (hA : A * A = 1) (hB : B * B = 1) (hAB : A * B = B * A)
    (hJA : J * A = A * J)
    (hJB : J * B = B * J) (hJX : J * X = X * J)
    (hodd : (A * B) * X * (A * B) = -X) :
    let Tp : R := 1 + J * (A + B) - A * B
    let Tm : R := 1 - J * (A + B) - A * B
    Tp * X * Tm - Tm * X * Tp =
      4 * J * ringCommutator (A + B) X := by
  let H := A + B
  let R0 := A * B
  have hBA : B * A = A * B := hAB.symm
  have hR0A : R0 * A = B := by
    dsimp [R0]
    rw [mul_assoc, hBA, ← mul_assoc, hA, one_mul]
  have hR0B : R0 * B = A := by
    dsimp [R0]
    rw [mul_assoc, hB, mul_one]
  have hAR0 : A * R0 = B := by
    dsimp [R0]
    rw [← mul_assoc, hA, one_mul]
  have hBR0 : B * R0 = A := by
    dsimp [R0]
    rw [← mul_assoc, hBA, mul_assoc, hB, mul_one]
  have hR0H : R0 * H = H := by
    dsimp [H]
    rw [mul_add, hR0A, hR0B, add_comm]
  have hHR0 : H * R0 = H := by
    dsimp [H]
    rw [add_mul, hAR0, hBR0, add_comm]
  have hR0_sq : R0 * R0 = 1 := by
    calc
      R0 * R0 = (R0 * A) * B := by simp [R0, mul_assoc]
      _ = B * B := by rw [hR0A]
      _ = 1 := hB
  have hR0Xodd : R0 * X * R0 = -X := by simpa [R0] using hodd
  have hR0X : R0 * X = -X * R0 := by
    calc
      R0 * X = (R0 * X) * 1 := by rw [mul_one]
      _ = (R0 * X) * (R0 * R0) := by rw [hR0_sq]
      _ = (R0 * X * R0) * R0 := by noncomm_ring
      _ = -X * R0 := by rw [hR0Xodd]
  have hXR0 : X * R0 = -R0 * X := by
    calc
      X * R0 = 1 * (X * R0) := by rw [one_mul]
      _ = (R0 * R0) * (X * R0) := by rw [hR0_sq]
      _ = R0 * (R0 * X * R0) := by noncomm_ring
      _ = -R0 * X := by rw [hR0Xodd, mul_neg, neg_mul]
  have hJH : J * H = H * J := by
    dsimp [H]
    rw [mul_add, add_mul, hJA, hJB]
  have hJR0 : J * R0 = R0 * J := by
    dsimp [R0]
    calc
      J * (A * B) = (J * A) * B := by rw [mul_assoc]
      _ = (A * J) * B := by rw [hJA]
      _ = A * (J * B) := by rw [mul_assoc]
      _ = A * (B * J) := by rw [hJB]
      _ = (A * B) * J := by rw [mul_assoc]
  dsimp
  change (1 + J * H - R0) * X * (1 - J * H - R0) -
      (1 - J * H - R0) * X * (1 + J * H - R0) =
    4 * J * ringCommutator H X
  have hHXR0 : H * X * R0 = -(H * X) := by
    calc
      H * X * R0 = H * (X * R0) := by rw [mul_assoc]
      _ = H * (-R0 * X) := by rw [hXR0]
      _ = -(H * R0) * X := by simp [mul_assoc]
      _ = -(H * X) := by rw [hHR0, neg_mul]
  have hR0XH : R0 * X * H = -(X * H) := by
    calc
      R0 * X * H = (-X * R0) * H := by rw [hR0X]
      _ = -X * (R0 * H) := by simp [mul_assoc]
      _ = -(X * H) := by rw [hR0H, neg_mul]
  have hexpand :
      (1 + J * H - R0) * X * (1 - J * H - R0) -
          (1 - J * H - R0) * X * (1 + J * H - R0) =
        2 * (J * H * X * (1 - R0) - (1 - R0) * X * J * H) := by
    noncomm_ring
  rw [hexpand]
  unfold ringCommutator
  have hJHXR0 : J * H * X * R0 = -(J * H * X) := by
    calc
      J * H * X * R0 = J * (H * X * R0) := by noncomm_ring
      _ = J * (-(H * X)) := by rw [hHXR0]
      _ = -(J * H * X) := by simp [mul_assoc]
  have hXJH : X * J * H = J * X * H := by
    calc
      X * J * H = (X * J) * H := rfl
      _ = (J * X) * H := by rw [hJX]
      _ = J * X * H := rfl
  have hJRX : J * (R0 * X) = (R0 * X) * J := by
    calc
      J * (R0 * X) = (J * R0) * X := by rw [← mul_assoc]
      _ = (R0 * J) * X := by rw [hJR0]
      _ = R0 * (J * X) := by rw [mul_assoc]
      _ = R0 * (X * J) := by rw [hJX]
      _ = (R0 * X) * J := by rw [← mul_assoc]
  have hR0XJH : R0 * X * J * H = -(J * X * H) := by
    calc
      R0 * X * J * H = J * (R0 * X) * H := by rw [hJRX]
      _ = J * (R0 * X * H) := by rw [mul_assoc]
      _ = J * (-(X * H)) := by rw [hR0XH]
      _ = -(J * X * H) := by simp [mul_assoc]
  calc
    2 * (J * H * X * (1 - R0) - (1 - R0) * X * J * H) =
        2 * (J * H * X - J * H * X * R0 -
          (X * J * H - R0 * X * J * H)) := by noncomm_ring
    _ = 4 * J * (H * X - X * H) := by
      rw [hJHXR0, hXJH, hR0XJH]
      noncomm_ring

/-- On an odd paired-Pauli character, the physical one-site collective
commutator is the inverse-quarter-turn difference inside the strict product
Clifford representation. -/
theorem finiteTwoReplicaSingleSiteCollectiveCommutator_eq_cliffordDifference_of_relativeOdd
    {V : Type*} [Fintype V] [DecidableEq V]
    (j : V) (a : Fin 3) (X : FiniteTwoReplicaMatrix V)
    (hodd : finiteTwoReplicaPairedPauli (finiteSingleSitePauliLabel j a) * X *
        finiteTwoReplicaPairedPauli (finiteSingleSitePauliLabel j a) = -X) :
    finiteTwoReplicaCollectiveCommutatorLinear
        (finiteSingleSitePauliLabel j a) X =
      (-Complex.I) •
        (finiteProductCliffordDoubledConjugationEquiv
            (finiteSingleSiteQuarterTurnCode j a) X -
          (finiteProductCliffordDoubledConjugationEquiv
            (finiteSingleSiteQuarterTurnCode j a)).symm X) := by
  let P := finiteSingleSitePauliLabel j a
  let A := finiteTwoReplicaPauliLeft P
  let B := finiteTwoReplicaPauliRight P
  let R := finiteTwoReplicaPairedPauli P
  let J : FiniteTwoReplicaMatrix V := Complex.I • 1
  let Tp : FiniteTwoReplicaMatrix V := 1 + J * (A + B) - A * B
  let Tm : FiniteTwoReplicaMatrix V := 1 - J * (A + B) - A * B
  have hA : A * A = 1 := by simp [A]
  have hB : B * B = 1 := by simp [B]
  have hAB : A * B = B * A := by
    dsimp [A, B]
    rw [finiteTwoReplicaPauliLeft_mul_right,
      finiteTwoReplicaPauliRight_mul_left]
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
  have hR : A * B = R := by
    dsimp [A, B, R]
    rw [finiteTwoReplicaPauliLeft_mul_right]
  have hraw := twoInvolutionQuarterTurnOddDifferenceIdentity
    A B J X hA hB hAB hJA hJB hJX (by simpa [hR] using hodd)
  have hgate :
      finiteProductCliffordDoubledGate
          (finiteSingleSiteQuarterTurnCode j a) =
        (1 / 2 : ℂ) • Tp := by
    rw [finiteProductCliffordDoubledGate_singleSiteQuarterTurn]
    congr 1
    dsimp [Tp, J, A, B, R, P]
    rw [smul_mul_assoc]
    simp [finiteTwoReplicaPauliLeft_mul_right]
  have hgateAdj :
      (finiteProductCliffordDoubledGate
          (finiteSingleSiteQuarterTurnCode j a))ᴴ =
        (1 / 2 : ℂ) • Tm := by
    rw [finiteProductCliffordDoubledGate_singleSiteQuarterTurn_conjTranspose]
    congr 1
    dsimp [Tm, J, A, B, R, P]
    rw [smul_mul_assoc]
    simp [finiteTwoReplicaPauliLeft_mul_right]
  rw [finiteProductCliffordDoubledConjugationEquiv_apply,
    finiteProductCliffordDoubledConjugationEquiv_symm_apply,
    hgateAdj, hgate]
  change finiteTwoReplicaCollectiveCommutator P X = _
  rw [finiteTwoReplicaCollectiveCommutator, ← ringCommutator_add_left']
  change ringCommutator (A + B) X = _
  have hscale :
      ((1 / 2 : ℂ) • Tp) * X * ((1 / 2 : ℂ) • Tm) -
          ((1 / 2 : ℂ) • Tm) * X * ((1 / 2 : ℂ) • Tp) =
        (1 / 4 : ℂ) • (Tp * X * Tm - Tm * X * Tp) := by
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    module
  rw [hscale, hraw]
  have hfourMatrix :
      (4 : FiniteTwoReplicaMatrix V) =
        (4 : ℂ) • (1 : FiniteTwoReplicaMatrix V) := by
    ext i k
    rw [Matrix.ofNat_apply, Matrix.smul_apply, Matrix.one_apply]
    by_cases hik : i = k <;> simp [hik]
  have hfourJmul :
      (4 : FiniteTwoReplicaMatrix V) * J *
          ringCommutator (A + B) X =
        ((4 : ℂ) * Complex.I) • ringCommutator (A + B) X := by
    rw [hfourMatrix, smul_mul_assoc, Matrix.one_mul]
    dsimp [J]
    simp only [smul_mul_assoc, Matrix.one_mul, smul_smul]
  rw [hfourJmul, smul_smul, smul_smul]
  have hscalar :
      (-Complex.I) * (1 / 4 : ℂ) * (4 * Complex.I) = 1 := by
    calc
      (-Complex.I) * (1 / 4 : ℂ) * (4 * Complex.I) =
          -(Complex.I * Complex.I) := by ring
      _ = 1 := by rw [Complex.I_mul_I]; norm_num
  rw [hscalar, one_smul]

/-- Every one-site commutator image of an odd direction remains in the
canonical greatest obstruction, because first-order interpolation expresses
it through two product-Clifford conjugates. -/
theorem finiteTwoReplicaSingleSiteCollectiveCommutator_mem_greatestMaximizer_of_relativeOdd
    {V : Type*} [Fintype V] [DecidableEq V]
    (q : ℕ) (U : Submodule ℂ (FiniteTwoReplicaMatrix V))
    (hgreatest : ∀ W : Submodule ℂ (FiniteTwoReplicaMatrix V),
      linearFamilyDefect
          (finiteTwoReplicaQLocalCollectiveCommutatorLinear V q) W =
        linearFamilyDefect
          (finiteTwoReplicaQLocalCollectiveCommutatorLinear V q) U →
      W ≤ U)
    (j : V) (a : Fin 3) (X : FiniteTwoReplicaMatrix V)
    (hX : X ∈ U)
    (hodd : finiteTwoReplicaPairedPauli (finiteSingleSitePauliLabel j a) * X *
        finiteTwoReplicaPairedPauli (finiteSingleSitePauliLabel j a) = -X) :
    finiteTwoReplicaCollectiveCommutatorLinear
        (finiteSingleSitePauliLabel j a) X ∈ U := by
  have hmap (g : V → QubitTwoDesign.BinaryOctahedral) :
      finiteProductCliffordDoubledConjugationEquiv g X ∈ U := by
    rw [← finiteTwoReplicaQLocal_greatestMaximizer_productClifford_fixed
      q U hgreatest g]
    exact Submodule.mem_map_of_mem hX
  have hmapInv (g : V → QubitTwoDesign.BinaryOctahedral) :
      (finiteProductCliffordDoubledConjugationEquiv g).symm X ∈ U := by
    rw [finiteProductCliffordDoubledConjugationEquiv_symm_eq]
    exact hmap _
  rw [finiteTwoReplicaSingleSiteCollectiveCommutator_eq_cliffordDifference_of_relativeOdd
    j a X hodd]
  exact U.smul_mem _ (U.sub_mem (hmap _) (hmapInv _))

/-- The collision-free first-defect selector maps every nonzero Pauli
character component of a canonical greatest obstruction back into that same
obstruction. -/
theorem firstDefectCollectiveCommutator_mem_greatestMaximizer
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (q : ℕ) (U : Submodule ℂ (FiniteTwoReplicaMatrix V))
    (hgreatest : ∀ W : Submodule ℂ (FiniteTwoReplicaMatrix V),
      linearFamilyDefect
          (finiteTwoReplicaQLocalCollectiveCommutatorLinear V q) W =
        linearFamilyDefect
          (finiteTwoReplicaQLocalCollectiveCommutatorLinear V q) U →
      W ≤ U)
    (P : NonzeroPauliCharacter V) (X : FiniteTwoReplicaMatrix V)
    (hXU : X ∈ U)
    (hXP : X ∈ finiteTwoReplicaPauliCharacterSubspace P.1) :
    finiteTwoReplicaCollectiveCommutatorLinear
        (firstDefectPauliLabel P) X ∈ U := by
  let j := firstActivePauliSite P
  let a := pauliAxisPrev (firstActivePauliAxis P)
  have hlabel : firstDefectPauliLabel P = finiteSingleSitePauliLabel j a := by
    rfl
  have hchar :=
    (mem_finiteTwoReplicaPauliCharacterSubspace_iff P.1 X).mp hXP
      (firstDefectPauliLabel P)
  rw [finitePauliConjugationSign_firstDefect_source] at hchar
  have hodd : finiteTwoReplicaPairedPauli (finiteSingleSitePauliLabel j a) * X *
      finiteTwoReplicaPairedPauli (finiteSingleSitePauliLabel j a) = -X := by
    simpa [hlabel, finiteTwoReplicaPairedPauliConjugationLinear] using hchar
  rw [hlabel]
  exact finiteTwoReplicaSingleSiteCollectiveCommutator_mem_greatestMaximizer_of_relativeOdd
    q U hgreatest j a X hXU hodd

end

end GaloisForLFunctions.HTGeometry
