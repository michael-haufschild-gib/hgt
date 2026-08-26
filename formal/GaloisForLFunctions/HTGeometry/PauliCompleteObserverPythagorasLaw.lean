import GaloisForLFunctions.HTGeometry.FiniteUnitaryEnergyDefectLaw
import GaloisForLFunctions.HTGeometry.PauliCommutatorGramStableRankFloor
import GaloisForLFunctions.HTGeometry.PauliCommutatorReturnTubeLaw
import GaloisForLFunctions.HTGeometry.TwoLocalPauliGaussianEnergyCap

/-!
# Complete local-observer Pythagoras law

A commutator observer alone can lose every generator direction on an
autonomous orbit.  The loss is not destruction of source information: it is
an exact transfer to the complementary anticommutator channel.

For every finite unitary target, the stacked commutator--anticommutator
observer of an ordinary two-local Pauli Hamiltonian is a scaled isometry.
Its squared norm is exactly `4 * 2^n` times coefficient energy, independently
of target, spectrum, time, or spectral gaps.  Hence it is injective and has
full source rank at every target.  On the actual autonomous orbit the
commutator channel vanishes, so the anticommutator channel carries the full
energy.  This identifies the precise longitudinal information omitted by a
pure commutator/coarea argument.
-/

open scoped BigOperators Matrix Matrix.Norms.L2Operator
open Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

private theorem finiteMatrixHilbertSchmidtEnergy_eq_hsNorm_sq_direct
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) :
    finiteMatrixHilbertSchmidtEnergy A = hsNorm A ^ 2 := by
  rw [finiteMatrixHilbertSchmidtEnergy_eq_sum_normSq, hsNorm_sq,
    Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  exact (Complex.sq_norm (A i j)).symm

private theorem finiteMatrixHilbertSchmidtEnergy_unitaryMulLeft_direct
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (U : Matrix.unitaryGroup ι ℂ) :
    finiteMatrixHilbertSchmidtEnergy ((U : Matrix ι ι ℂ) * A) =
      finiteMatrixHilbertSchmidtEnergy A := by
  unfold finiteMatrixHilbertSchmidtEnergy
  have hleft : star (U : Matrix ι ι ℂ) * (U : Matrix ι ι ℂ) = 1 :=
    Unitary.coe_star_mul_self U
  congr 1
  congr 1
  rw [star_mul]
  calc
    star A * star (U : Matrix ι ι ℂ) * ((U : Matrix ι ι ℂ) * A) =
        star A * (star (U : Matrix ι ι ℂ) * (U : Matrix ι ι ℂ)) * A := by
      noncomm_ring
    _ = star A * A := by rw [hleft]; noncomm_ring

/-- Hilbert--Schmidt norm is invariant under left multiplication by a finite
unitary. -/
theorem hsNorm_unitaryMulLeft_eq
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (U : Matrix.unitaryGroup ι ℂ) :
    hsNorm ((U : Matrix ι ι ℂ) * A) = hsNorm A := by
  have hsq : hsNorm ((U : Matrix ι ι ℂ) * A) ^ 2 = hsNorm A ^ 2 := by
    rw [← finiteMatrixHilbertSchmidtEnergy_eq_hsNorm_sq_direct,
      ← finiteMatrixHilbertSchmidtEnergy_eq_hsNorm_sq_direct]
    exact finiteMatrixHilbertSchmidtEnergy_unitaryMulLeft_direct A U
  nlinarith [hsNorm_nonneg ((U : Matrix ι ι ℂ) * A), hsNorm_nonneg A]

/-- Hilbert--Schmidt norm is invariant under right multiplication by a finite
unitary. -/
theorem hsNorm_unitaryMulRight_eq
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (U : Matrix.unitaryGroup ι ℂ) :
    hsNorm (A * (U : Matrix ι ι ℂ)) = hsNorm A := by
  have hstar :
      hsNorm (A * (U : Matrix ι ι ℂ)) =
        hsNorm (star (U : Matrix ι ι ℂ) * star A) := by
    calc
      hsNorm (A * (U : Matrix ι ι ℂ)) =
          hsNorm (star (A * (U : Matrix ι ι ℂ))) :=
        (hsNorm_conjTranspose (A * (U : Matrix ι ι ℂ))).symm
      _ = hsNorm (star (U : Matrix ι ι ℂ) * star A) := by rw [star_mul]
  rw [hstar]
  let Ustar : Matrix.unitaryGroup ι ℂ := star U
  exact (hsNorm_unitaryMulLeft_eq (star A) Ustar).trans
    (hsNorm_conjTranspose A)

/-- **Commutator--anticommutator Pythagoras.**  The two channels partition
four times the source Hilbert--Schmidt energy at every unitary target. -/
theorem hsNorm_commutator_add_anticommutator_sq
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : Matrix ι ι ℂ) (U : Matrix.unitaryGroup ι ℂ) :
    hsNorm (H * (U : Matrix ι ι ℂ) - (U : Matrix ι ι ℂ) * H) ^ 2 +
        hsNorm (H * (U : Matrix ι ι ℂ) + (U : Matrix ι ι ℂ) * H) ^ 2 =
      4 * hsNorm H ^ 2 := by
  let A := matVec (H * (U : Matrix ι ι ℂ))
  let B := matVec ((U : Matrix ι ι ℂ) * H)
  have hpara := parallelogram_law_with_norm ℂ A B
  change hsNorm (H * (U : Matrix ι ι ℂ) + (U : Matrix ι ι ℂ) * H) ^ 2 +
      hsNorm (H * (U : Matrix ι ι ℂ) - (U : Matrix ι ι ℂ) * H) ^ 2 =
        2 * (hsNorm (H * (U : Matrix ι ι ℂ)) ^ 2 +
          hsNorm ((U : Matrix ι ι ℂ) * H) ^ 2) at hpara
  rw [add_comm]
  rw [hpara, hsNorm_unitaryMulRight_eq H U,
    hsNorm_unitaryMulLeft_eq H U]
  ring

/-- Complementary longitudinal observer for an ordinary two-local Pauli
Hamiltonian at a unitary target. -/
def twoLocalPauliUnitaryAnticommutatorMap
    {n : ℕ}
    (U : Matrix.unitaryGroup (FiniteQubitConfiguration (Fin n)) ℂ) :
    TwoLocalPauliCoefficientSpace n →ₗ[ℝ]
      EuclideanSpace ℂ
        (FiniteQubitConfiguration (Fin n) × FiniteQubitConfiguration (Fin n)) where
  toFun x := matVec
    (realActivePauliHamiltonian x *
        (U : Matrix (FiniteQubitConfiguration (Fin n))
          (FiniteQubitConfiguration (Fin n)) ℂ) +
      (U : Matrix (FiniteQubitConfiguration (Fin n))
          (FiniteQubitConfiguration (Fin n)) ℂ) *
        realActivePauliHamiltonian x)
  map_add' x y := by
    rw [realActivePauliHamiltonian_add]
    have hmatrix :
        (realActivePauliHamiltonian x + realActivePauliHamiltonian y) *
            (U : Matrix (FiniteQubitConfiguration (Fin n))
              (FiniteQubitConfiguration (Fin n)) ℂ) +
          (U : Matrix (FiniteQubitConfiguration (Fin n))
              (FiniteQubitConfiguration (Fin n)) ℂ) *
            (realActivePauliHamiltonian x + realActivePauliHamiltonian y) =
          (realActivePauliHamiltonian x * U + U * realActivePauliHamiltonian x) +
            (realActivePauliHamiltonian y * U + U * realActivePauliHamiltonian y) := by
      noncomm_ring
    rw [hmatrix]
    rfl
  map_smul' r x := by
    rw [realActivePauliHamiltonian_smul]
    rw [Matrix.smul_mul, Matrix.mul_smul, ← smul_add]
    rfl

theorem norm_twoLocalPauliUnitaryAnticommutatorMap_sq
    {n : ℕ}
    (U : Matrix.unitaryGroup (FiniteQubitConfiguration (Fin n)) ℂ)
    (x : TwoLocalPauliCoefficientSpace n) :
    ‖twoLocalPauliUnitaryAnticommutatorMap U x‖ ^ 2 =
      frobSq
        (realActivePauliHamiltonian x *
            (U : Matrix (FiniteQubitConfiguration (Fin n))
              (FiniteQubitConfiguration (Fin n)) ℂ) +
          (U : Matrix (FiniteQubitConfiguration (Fin n))
              (FiniteQubitConfiguration (Fin n)) ℂ) *
            realActivePauliHamiltonian x) := by
  change hsNorm
      (realActivePauliHamiltonian x *
          (U : Matrix (FiniteQubitConfiguration (Fin n))
            (FiniteQubitConfiguration (Fin n)) ℂ) +
        (U : Matrix (FiniteQubitConfiguration (Fin n))
            (FiniteQubitConfiguration (Fin n)) ℂ) *
          realActivePauliHamiltonian x) ^ 2 = _
  rw [hsNorm_sq]
  rfl

/-- Stacked transverse and longitudinal local-Hamiltonian observer. -/
def twoLocalPauliUnitaryCompleteObserverMap
    {n : ℕ}
    (U : Matrix.unitaryGroup (FiniteQubitConfiguration (Fin n)) ℂ) :
    TwoLocalPauliCoefficientSpace n →ₗ[ℝ]
      EuclideanSpace ℂ
        (Bool × (FiniteQubitConfiguration (Fin n) × FiniteQubitConfiguration (Fin n))) where
  toFun x := (EuclideanSpace.equiv _ ℂ).symm fun p =>
    if p.1 then
      twoLocalPauliUnitaryCommutatorMap U x p.2
    else
      twoLocalPauliUnitaryAnticommutatorMap U x p.2
  map_add' x y := by
    apply (EuclideanSpace.equiv _ ℂ).injective
    ext p
    by_cases hp : p.1
    · simp [hp]
    · simp [hp]
  map_smul' r x := by
    apply (EuclideanSpace.equiv _ ℂ).injective
    ext p
    by_cases hp : p.1
    · simp [hp]
    · simp [hp]

theorem norm_twoLocalPauliUnitaryCompleteObserverMap_sq_split
    {n : ℕ}
    (U : Matrix.unitaryGroup (FiniteQubitConfiguration (Fin n)) ℂ)
    (x : TwoLocalPauliCoefficientSpace n) :
    ‖twoLocalPauliUnitaryCompleteObserverMap U x‖ ^ 2 =
      ‖twoLocalPauliUnitaryCommutatorMap U x‖ ^ 2 +
        ‖twoLocalPauliUnitaryAnticommutatorMap U x‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  change (
    ∑ p : Bool ×
        (FiniteQubitConfiguration (Fin n) × FiniteQubitConfiguration (Fin n)),
      ‖if p.1 then twoLocalPauliUnitaryCommutatorMap U x p.2
        else twoLocalPauliUnitaryAnticommutatorMap U x p.2‖ ^ 2) = _
  rw [Fintype.sum_prod_type, Fintype.sum_bool]
  simp only [Bool.false_eq_true, if_true, if_false]
  rw [← EuclideanSpace.norm_sq_eq, ← EuclideanSpace.norm_sq_eq]

/-- **Target-independent complete-observer law.**  Every ordinary two-local
coefficient direction survives with the same gain at every unitary target. -/
theorem norm_twoLocalPauliUnitaryCompleteObserverMap_sq
    {n : ℕ}
    (U : Matrix.unitaryGroup (FiniteQubitConfiguration (Fin n)) ℂ)
    (x : TwoLocalPauliCoefficientSpace n) :
    ‖twoLocalPauliUnitaryCompleteObserverMap U x‖ ^ 2 =
      (4 * (2 : ℝ) ^ n) * ‖x‖ ^ 2 := by
  rw [norm_twoLocalPauliUnitaryCompleteObserverMap_sq_split,
    norm_twoLocalPauliUnitaryCommutatorMap_sq,
    norm_twoLocalPauliUnitaryAnticommutatorMap_sq,
    frobSq_eq_hsNorm_sq, frobSq_eq_hsNorm_sq,
    hsNorm_commutator_add_anticommutator_sq,
    ← frobSq_eq_hsNorm_sq,
    frobSq_realActivePauliHamiltonian]
  ring

theorem twoLocalPauliUnitaryCompleteObserverMap_injective
    {n : ℕ}
    (U : Matrix.unitaryGroup (FiniteQubitConfiguration (Fin n)) ℂ) :
    Function.Injective (twoLocalPauliUnitaryCompleteObserverMap U) := by
  rw [← LinearMap.ker_eq_bot]
  ext x
  constructor
  · intro hx
    have hzero : twoLocalPauliUnitaryCompleteObserverMap U x = 0 :=
      LinearMap.mem_ker.mp hx
    have henergy := norm_twoLocalPauliUnitaryCompleteObserverMap_sq U x
    rw [hzero, norm_zero, zero_pow (by omega : (2 : ℕ) ≠ 0)] at henergy
    have hscale : 0 < 4 * (2 : ℝ) ^ n := by positivity
    have hxnormsq : ‖x‖ ^ 2 = 0 :=
      (mul_eq_zero.mp henergy.symm).resolve_left (ne_of_gt hscale)
    have hxnorm : ‖x‖ = 0 := by nlinarith [norm_nonneg x]
    simpa using norm_eq_zero.mp hxnorm
  · rintro rfl
    exact Submodule.zero_mem _

/-- The complete observer has full local-parameter rank at every target. -/
theorem twoLocalPauliUnitaryCompleteObserverMap_full_rank
    {n : ℕ}
    (U : Matrix.unitaryGroup (FiniteQubitConfiguration (Fin n)) ℂ) :
    Module.finrank ℝ
        (LinearMap.range (twoLocalPauliUnitaryCompleteObserverMap U)) =
      Fintype.card (PauliTracelessLabel n 2) := by
  rw [LinearMap.finrank_range_of_inj
    (twoLocalPauliUnitaryCompleteObserverMap_injective U)]
  simp [TwoLocalPauliCoefficientSpace]

/-- On the actual autonomous orbit the transverse channel vanishes exactly. -/
theorem twoLocalPauliUnitaryCommutatorMap_autonomous_eq_zero
    {n : ℕ} (x : TwoLocalPauliCoefficientSpace n) (t : ℝ) :
    twoLocalPauliUnitaryCommutatorMap
        ⟨unitaryEvolution (realActivePauliHamiltonian x) t,
          unitaryEvolution_mem_unitary
            (isSelfAdjoint_realActivePauliHamiltonian x) t⟩ x = 0 := by
  apply (EuclideanSpace.equiv _ ℂ).injective
  ext p
  change (realActivePauliHamiltonian x *
      unitaryEvolution (realActivePauliHamiltonian x) t -
    unitaryEvolution (realActivePauliHamiltonian x) t *
      realActivePauliHamiltonian x) p.1 p.2 = 0
  rw [unitaryEvolution_commutes_generator, sub_self]
  rfl

/-- Consequently the longitudinal channel carries all complete-observer
energy on every autonomous orbit point. -/
theorem norm_twoLocalPauliUnitaryAnticommutatorMap_autonomous_sq
    {n : ℕ} (x : TwoLocalPauliCoefficientSpace n) (t : ℝ) :
    ‖twoLocalPauliUnitaryAnticommutatorMap
        ⟨unitaryEvolution (realActivePauliHamiltonian x) t,
          unitaryEvolution_mem_unitary
            (isSelfAdjoint_realActivePauliHamiltonian x) t⟩ x‖ ^ 2 =
      (4 * (2 : ℝ) ^ n) * ‖x‖ ^ 2 := by
  let U : Matrix.unitaryGroup (FiniteQubitConfiguration (Fin n)) ℂ :=
    ⟨unitaryEvolution (realActivePauliHamiltonian x) t,
      unitaryEvolution_mem_unitary
        (isSelfAdjoint_realActivePauliHamiltonian x) t⟩
  have hcomplete := norm_twoLocalPauliUnitaryCompleteObserverMap_sq U x
  rw [norm_twoLocalPauliUnitaryCompleteObserverMap_sq_split,
    twoLocalPauliUnitaryCommutatorMap_autonomous_eq_zero,
    norm_zero, zero_pow (by omega : (2 : ℕ) ≠ 0), zero_add] at hcomplete
  exact hcomplete

end

end GaloisForLFunctions.HTGeometry
