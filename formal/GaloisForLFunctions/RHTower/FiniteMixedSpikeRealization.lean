import GaloisForLFunctions.HTGeometry.HilbertSchmidtRankOne
import Mathlib.LinearAlgebra.Matrix.Hermitian

/-!
# Finite spectral realization of weighted clocks

Every nonnegative finite probability packet is realized as a unit vector in a
finite complex Hilbert space, and every real energy packet is realized as a
self-adjoint diagonal Hamiltonian.  The vector variance of this realization is
exactly the elementary weighted variance.
-/

open scoped BigOperators InnerProductSpace

namespace RHTower

noncomputable section

/-- Finite complex Hilbert space carrying a spectral clock. -/
abbrev FiniteClockSpace (d : ℕ) := EuclideanSpace ℂ (Fin d)

/-- Complex Hilbert space carried by an arbitrary finite index type. -/
abbrev FiniteIndexClockSpace (ι : Type*) [Fintype ι] :=
  EuclideanSpace ℂ ι

/-- Canonical nonnegative ket on an arbitrary finite index type. -/
def finiteIndexWeightKet
    {ι : Type*} [Fintype ι] (w : ι → ℝ) : FiniteIndexClockSpace ι :=
  WithLp.toLp 2 fun i => (Real.sqrt (w i) : ℂ)

/-- Weight ket after applying coordinatewise unit phases. -/
def finiteIndexPhasedWeightKet
    {ι : Type*} [Fintype ι] (w : ι → ℝ) (phase : ι → ℂ) :
    FiniteIndexClockSpace ι :=
  WithLp.toLp 2 fun i => (Real.sqrt (w i) : ℂ) * phase i

/-- Diagonal Hamiltonian on an arbitrary finite index type. -/
def finiteIndexDiagonalHamiltonian
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (energy : ι → ℝ) : FiniteIndexClockSpace ι →L[ℂ] FiniteIndexClockSpace ι :=
  LinearMap.toContinuousLinearMap
    (Matrix.toEuclideanLin (Matrix.diagonal fun i => (energy i : ℂ)))

/-- Canonical nonnegative ket whose squared coordinates are the weights. -/
def finiteWeightKet {d : ℕ} (w : Fin d → ℝ) : FiniteClockSpace d :=
  WithLp.toLp 2 fun i => (Real.sqrt (w i) : ℂ)

/-- Diagonal bounded Hamiltonian associated with a finite real energy list. -/
def finiteDiagonalHamiltonian {d : ℕ}
    (energy : Fin d → ℝ) : FiniteClockSpace d →L[ℂ] FiniteClockSpace d :=
  LinearMap.toContinuousLinearMap
    (Matrix.toEuclideanLin (Matrix.diagonal fun i => (energy i : ℂ)))

/-- Elementary weighted variance of a finite energy packet. -/
def finiteSpectralVariance {d : ℕ}
    (w energy : Fin d → ℝ) : ℝ :=
  (∑ i, w i * energy i ^ 2) - (∑ i, w i * energy i) ^ 2

/-- Matrix of the finite mixed-spike state with background `b` and spike `c`. -/
def finiteMixedSpikeMatrix {d : ℕ}
    (b c : ℝ) (w : Fin d → ℝ) : Matrix (Fin d) (Fin d) ℂ :=
  fun i j =>
    (if i = j then (b : ℂ) else 0) +
      (c : ℂ) * (Real.sqrt (w i) : ℂ) * (Real.sqrt (w j) : ℂ)

/-- Trace of a finite mixed-spike matrix. -/
theorem finiteMixedSpikeMatrix_trace {d : ℕ}
    (b c : ℝ) (w : Fin d → ℝ) (hw : ∀ i, 0 ≤ w i) :
    Matrix.trace (finiteMixedSpikeMatrix b c w) =
      (((d : ℝ) * b + c * ∑ i, w i : ℝ) : ℂ) := by
  change (∑ i, ((if i = i then (b : ℂ) else 0) +
      (c : ℂ) * (Real.sqrt (w i) : ℂ) * (Real.sqrt (w i) : ℂ))) = _
  simp only [if_pos]
  calc
    ∑ x, ((b : ℂ) + (c : ℂ) * (Real.sqrt (w x) : ℂ) *
        (Real.sqrt (w x) : ℂ)) =
        ∑ x, ((b : ℂ) + (c : ℂ) * (w x : ℂ)) := by
          apply Finset.sum_congr rfl
          intro i _hi
          norm_cast
          calc
            b + c * Real.sqrt (w i) * Real.sqrt (w i) =
                b + c * Real.sqrt (w i) ^ 2 := by ring
            _ = b + c * w i := by rw [Real.sq_sqrt (hw i)]
    _ = (((d : ℝ) * b + c * ∑ i, w i : ℝ) : ℂ) := by
      simp_rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
      rw [Finset.mul_sum]
      push_cast
      ring

@[simp] theorem finiteIndexWeightKet_apply
    {ι : Type*} [Fintype ι] (w : ι → ℝ) (i : ι) :
    finiteIndexWeightKet w i = (Real.sqrt (w i) : ℂ) := rfl

@[simp] theorem finiteIndexPhasedWeightKet_apply
    {ι : Type*} [Fintype ι] (w : ι → ℝ) (phase : ι → ℂ) (i : ι) :
    finiteIndexPhasedWeightKet w phase i =
      (Real.sqrt (w i) : ℂ) * phase i := rfl

@[simp] theorem finiteIndexDiagonalHamiltonian_apply
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (energy : ι → ℝ) (x : FiniteIndexClockSpace ι) (i : ι) :
    finiteIndexDiagonalHamiltonian energy x i = (energy i : ℂ) * x i := by
  simp [finiteIndexDiagonalHamiltonian, Matrix.toLpLin_apply,
    Matrix.mulVec_diagonal]

/-- A real diagonal Hamiltonian on any finite index type is self-adjoint. -/
theorem finiteIndexDiagonalHamiltonian_selfAdjoint
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (energy : ι → ℝ) :
    ContinuousLinearMap.adjoint (finiteIndexDiagonalHamiltonian energy) =
      finiteIndexDiagonalHamiltonian energy := by
  have hm :
      (Matrix.diagonal fun i => (energy i : ℂ)).conjTranspose =
        Matrix.diagonal fun i => (energy i : ℂ) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [Matrix.conjTranspose, Matrix.diagonal]
    · simp [Matrix.conjTranspose, Matrix.diagonal, hij, Ne.symm hij]
  rw [finiteIndexDiagonalHamiltonian,
    ← LinearMap.adjoint_toContinuousLinearMap,
    ← Matrix.toEuclideanLin_conjTranspose_eq_adjoint, hm]

/-- Squared norm of an arbitrary finite-index canonical ket. -/
theorem finiteIndexWeightKet_norm_sq
    {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) :
    ‖finiteIndexWeightKet w‖ ^ 2 = ∑ i, w i := by
  rw [EuclideanSpace.norm_sq_eq]
  apply Finset.sum_congr rfl
  intro i _hi
  simp [finiteIndexWeightKet, Real.sq_sqrt (hw i)]

/-- A nonnegative unit-mass packet on any finite index type gives a unit ket. -/
theorem finiteIndexWeightKet_norm_eq_one
    {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hsum : ∑ i, w i = 1) :
    ‖finiteIndexWeightKet w‖ = 1 := by
  have hsq := finiteIndexWeightKet_norm_sq w hw
  rw [hsum] at hsq
  nlinarith [norm_nonneg (finiteIndexWeightKet w)]

/-- Coordinatewise unit phases preserve the norm of a finite weight ket. -/
theorem finiteIndexPhasedWeightKet_norm_sq
    {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (phase : ι → ℂ) (hw : ∀ i, 0 ≤ w i)
    (hphase : ∀ i, ‖phase i‖ = 1) :
    ‖finiteIndexPhasedWeightKet w phase‖ ^ 2 = ∑ i, w i := by
  rw [EuclideanSpace.norm_sq_eq]
  apply Finset.sum_congr rfl
  intro i _hi
  simp [finiteIndexPhasedWeightKet, hphase,
    Real.sq_sqrt (hw i)]

/-- Survival amplitude of a phased finite weight ket is its weighted phase sum. -/
theorem finiteIndexWeightKet_inner_phasedWeightKet
    {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (phase : ι → ℂ) (hw : ∀ i, 0 ≤ w i) :
    inner ℂ (finiteIndexWeightKet w)
        (finiteIndexPhasedWeightKet w phase) =
      ∑ i, (w i : ℂ) * phase i := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct]
  change
    (∑ i, ((Real.sqrt (w i) : ℂ) * phase i) *
      (starRingEnd ℂ) (Real.sqrt (w i) : ℂ)) =
        ∑ i, (w i : ℂ) * phase i
  simp_rw [Complex.conj_ofReal]
  apply Finset.sum_congr rfl
  intro i _hi
  calc
    ((Real.sqrt (w i) : ℂ) * phase i) *
        (Real.sqrt (w i) : ℂ) =
      ((Real.sqrt (w i) ^ 2 : ℝ) : ℂ) * phase i := by
        push_cast
        ring
    _ = (w i : ℂ) * phase i := by rw [Real.sq_sqrt (hw i)]

/-- Second Hamiltonian moment of an arbitrary finite-index weight ket. -/
theorem finiteIndexDiagonalHamiltonian_weightKet_norm_sq
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w energy : ι → ℝ) (hw : ∀ i, 0 ≤ w i) :
    ‖finiteIndexDiagonalHamiltonian energy (finiteIndexWeightKet w)‖ ^ 2 =
      ∑ i, w i * energy i ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [finiteIndexDiagonalHamiltonian_apply, finiteIndexWeightKet_apply]
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  rw [mul_pow, sq_abs, sq_abs, Real.sq_sqrt (hw i)]
  ring

/-- First Hamiltonian moment of an arbitrary finite-index weight ket. -/
theorem finiteIndexWeightKet_inner_diagonalHamiltonian
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w energy : ι → ℝ) (hw : ∀ i, 0 ≤ w i) :
    inner ℂ (finiteIndexWeightKet w)
        (finiteIndexDiagonalHamiltonian energy (finiteIndexWeightKet w)) =
      ((∑ i, w i * energy i : ℝ) : ℂ) := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  rw [dotProduct]
  simp_rw [finiteIndexDiagonalHamiltonian_apply]
  change
    (∑ i, ((energy i : ℂ) * (Real.sqrt (w i) : ℂ)) *
      (starRingEnd ℂ) (Real.sqrt (w i) : ℂ)) =
        ((∑ i, w i * energy i : ℝ) : ℂ)
  simp_rw [Complex.conj_ofReal]
  norm_cast
  apply Finset.sum_congr rfl
  intro i _hi
  calc
    energy i * Real.sqrt (w i) * Real.sqrt (w i) =
        energy i * Real.sqrt (w i) ^ 2 := by ring
    _ = energy i * w i := by rw [Real.sq_sqrt (hw i)]
    _ = w i * energy i := by ring

/-- Hilbert-space variance equals weighted variance on every finite index. -/
theorem finiteIndexWeightKet_diagonal_variance
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w energy : ι → ℝ) (hw : ∀ i, 0 ≤ w i) :
    ‖finiteIndexDiagonalHamiltonian energy (finiteIndexWeightKet w)‖ ^ 2 -
        ‖inner ℂ (finiteIndexWeightKet w)
          (finiteIndexDiagonalHamiltonian energy
            (finiteIndexWeightKet w))‖ ^ 2 =
      (∑ i, w i * energy i ^ 2) - (∑ i, w i * energy i) ^ 2 := by
  rw [finiteIndexDiagonalHamiltonian_weightKet_norm_sq w energy hw,
    finiteIndexWeightKet_inner_diagonalHamiltonian w energy hw]
  simp only [Complex.norm_real, Real.norm_eq_abs]
  rw [sq_abs]

@[simp] theorem finiteWeightKet_apply {d : ℕ} (w : Fin d → ℝ) (i : Fin d) :
    finiteWeightKet w i = (Real.sqrt (w i) : ℂ) := rfl

@[simp] theorem finiteDiagonalHamiltonian_apply {d : ℕ}
    (energy : Fin d → ℝ) (x : FiniteClockSpace d) (i : Fin d) :
    finiteDiagonalHamiltonian energy x i = (energy i : ℂ) * x i := by
  classical
  simp [finiteDiagonalHamiltonian, Matrix.toLpLin_apply,
    Matrix.mulVec_diagonal]

/-- A real diagonal finite Hamiltonian is self-adjoint. -/
theorem finiteDiagonalHamiltonian_selfAdjoint {d : ℕ}
    (energy : Fin d → ℝ) :
    ContinuousLinearMap.adjoint (finiteDiagonalHamiltonian energy) =
      finiteDiagonalHamiltonian energy := by
  have hm :
      (Matrix.diagonal fun i => (energy i : ℂ)).conjTranspose =
        Matrix.diagonal fun i => (energy i : ℂ) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [Matrix.conjTranspose, Matrix.diagonal]
    · simp [Matrix.conjTranspose, Matrix.diagonal, hij, Ne.symm hij]
  rw [finiteDiagonalHamiltonian,
    ← LinearMap.adjoint_toContinuousLinearMap,
    ← Matrix.toEuclideanLin_conjTranspose_eq_adjoint, hm]

/-- Squared norm of the canonical weight ket is total weight. -/
theorem finiteWeightKet_norm_sq {d : ℕ}
    (w : Fin d → ℝ) (hw : ∀ i, 0 ≤ w i) :
    ‖finiteWeightKet w‖ ^ 2 = ∑ i, w i := by
  rw [EuclideanSpace.norm_sq_eq]
  apply Finset.sum_congr rfl
  intro i _hi
  simp [finiteWeightKet, Real.sq_sqrt (hw i)]

/-- A nonnegative unit-mass packet gives a unit ket. -/
theorem finiteWeightKet_norm_eq_one {d : ℕ}
    (w : Fin d → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hsum : ∑ i, w i = 1) :
    ‖finiteWeightKet w‖ = 1 := by
  have hsq := finiteWeightKet_norm_sq w hw
  rw [hsum] at hsq
  nlinarith [norm_nonneg (finiteWeightKet w)]

/-- Second moment of the diagonal Hamiltonian in the weight ket. -/
theorem finiteDiagonalHamiltonian_weightKet_norm_sq {d : ℕ}
    (w energy : Fin d → ℝ) (hw : ∀ i, 0 ≤ w i) :
    ‖finiteDiagonalHamiltonian energy (finiteWeightKet w)‖ ^ 2 =
      ∑ i, w i * energy i ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [finiteDiagonalHamiltonian_apply, finiteWeightKet_apply]
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  rw [mul_pow, sq_abs, sq_abs, Real.sq_sqrt (hw i)]
  ring

/-- First moment of the diagonal Hamiltonian in the weight ket. -/
theorem finiteWeightKet_inner_diagonalHamiltonian {d : ℕ}
    (w energy : Fin d → ℝ) (hw : ∀ i, 0 ≤ w i) :
    inner ℂ (finiteWeightKet w)
        (finiteDiagonalHamiltonian energy (finiteWeightKet w)) =
      ((∑ i, w i * energy i : ℝ) : ℂ) := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  rw [dotProduct]
  simp_rw [finiteDiagonalHamiltonian_apply]
  change
    (∑ i, ((energy i : ℂ) * (Real.sqrt (w i) : ℂ)) *
      (starRingEnd ℂ) (Real.sqrt (w i) : ℂ)) =
        ((∑ i, w i * energy i : ℝ) : ℂ)
  simp_rw [Complex.conj_ofReal]
  norm_cast
  apply Finset.sum_congr rfl
  intro i _hi
  calc
    energy i * Real.sqrt (w i) * Real.sqrt (w i) =
        energy i * Real.sqrt (w i) ^ 2 := by ring
    _ = energy i * w i := by rw [Real.sq_sqrt (hw i)]
    _ = w i * energy i := by ring

/-- Exact agreement between Hilbert-space variance and weighted variance. -/
theorem finiteWeightKet_diagonal_variance {d : ℕ}
    (w energy : Fin d → ℝ) (hw : ∀ i, 0 ≤ w i) :
    ‖finiteDiagonalHamiltonian energy (finiteWeightKet w)‖ ^ 2 -
        ‖inner ℂ (finiteWeightKet w)
          (finiteDiagonalHamiltonian energy (finiteWeightKet w))‖ ^ 2 =
      finiteSpectralVariance w energy := by
  rw [finiteDiagonalHamiltonian_weightKet_norm_sq w energy hw,
    finiteWeightKet_inner_diagonalHamiltonian w energy hw]
  simp only [Complex.norm_real, Real.norm_eq_abs]
  rw [sq_abs]
  rfl

end

end RHTower
