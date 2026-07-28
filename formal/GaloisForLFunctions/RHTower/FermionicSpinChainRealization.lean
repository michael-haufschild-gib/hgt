import GaloisForLFunctions.RHTower.EndpointKrylovNearestNeighborRealization
import Mathlib.LinearAlgebra.Matrix.Hermitian

/-!
# Local spin-chain realization of the recurrence ambiguity

A Hermitian tridiagonal one-particle Hamiltonian is the one-excitation
block of a number-conserving nearest-neighbour XX chain.  This module builds
the finite occupation-basis matrix explicitly.  The lift is Hermitian,
preserves every particle-number sector, and restricts exactly to the
original Hamiltonian on singleton occupations.

Applied to the block-Krylov representatives, every return probability in
the closed interval `[0,1]` is therefore realized inside a finite local
spin chain, with a fixed single-excitation preparation and return test.
-/

open scoped BigOperators InnerProductSpace
open Complex

noncomputable section

namespace RHTower.ParityForecast

/-- Two different sites are neighbours in the open linear chain. -/
def AdjacentSites {r : ℕ} (i j : Fin r) : Prop :=
  (i : ℕ) + 1 = (j : ℕ) ∨ (j : ℕ) + 1 = (i : ℕ)

/-- Move one occupied mode from `j` to `i`. -/
def moveOccupation {r : ℕ} (T : Finset (Fin r)) (j i : Fin r) :
    Finset (Fin r) :=
  insert i (T.erase j)

theorem moveOccupation_card {r : ℕ} {T : Finset (Fin r)}
    {j i : Fin r} (hj : j ∈ T) (hi : i ∉ T) :
    (moveOccupation T j i).card = T.card := by
  unfold moveOccupation
  have hiErase : i ∉ T.erase j := by simp [hi]
  rw [Finset.card_insert_of_notMem hiErase,
    Finset.card_erase_of_mem hj]
  have hpos : 0 < T.card := Finset.card_pos.mpr ⟨j, hj⟩
  omega

/-- Occupation-number matrix of one site. -/
def occupationNumberMatrix {r : ℕ} (i : Fin r) :
    Matrix (Finset (Fin r)) (Finset (Fin r)) ℂ :=
  fun S T => if S = T ∧ i ∈ T then 1 else 0

/-- Directed number-conserving hopping matrix from `j` to `i`. -/
def occupationHopMatrix {r : ℕ} (i j : Fin r) :
    Matrix (Finset (Fin r)) (Finset (Fin r)) ℂ :=
  fun S T =>
    if j ∈ T ∧ i ∉ T ∧ S = moveOccupation T j i then 1 else 0

theorem occupationHopMatrix_eq_zero_of_card_ne {r : ℕ}
    (i j : Fin r) {S T : Finset (Fin r)}
    (hcard : S.card ≠ T.card) :
    occupationHopMatrix i j S T = 0 := by
  unfold occupationHopMatrix
  split_ifs with h
  · exfalso
    apply hcard
    rw [h.2.2, moveOccupation_card h.1 h.2.1]
  · rfl

/--
Raw onsite-plus-hopping occupation matrix.  Only neighbouring sites are
coupled; the Hermitian physical lift below takes its Hermitian part.
-/
def rawXXOccupationMatrix {r : ℕ}
    (A : Matrix (Fin r) (Fin r) ℂ) :
    Matrix (Finset (Fin r)) (Finset (Fin r)) ℂ := by
  classical
  exact fun S T =>
    (∑ i, A i i * occupationNumberMatrix i S T) +
      ∑ i, ∑ j, A i j *
        occupationHopMatrix i j S T *
          if AdjacentSites i j then 1 else 0

/-- Matrix entries vanish between distinct non-neighbouring sites. -/
def MatrixNearestNeighbor {r : ℕ}
    (A : Matrix (Fin r) (Fin r) ℂ) : Prop :=
  ∀ i j, i ≠ j → ¬ AdjacentSites i j → A i j = 0

theorem rawXXOccupationMatrix_eq_zero_of_card_ne {r : ℕ}
    (A : Matrix (Fin r) (Fin r) ℂ)
    {S T : Finset (Fin r)} (hcard : S.card ≠ T.card) :
    rawXXOccupationMatrix A S T = 0 := by
  have hST : S ≠ T := by
    intro h
    exact hcard (congrArg Finset.card h)
  unfold rawXXOccupationMatrix
  simp [occupationNumberMatrix, hST,
    occupationHopMatrix_eq_zero_of_card_ne _ _ hcard]

@[simp] theorem occupationNumberMatrix_singleton {r : ℕ}
    (i a b : Fin r) :
    occupationNumberMatrix i {a} {b} =
      if a = b ∧ i = b then 1 else 0 := by
  simp [occupationNumberMatrix]

@[simp] theorem occupationHopMatrix_singleton {r : ℕ}
    (i j a b : Fin r) :
    occupationHopMatrix i j {a} {b} =
      if j = b ∧ i ≠ b ∧ i = a then 1 else 0 := by
  simp [occupationHopMatrix, moveOccupation]
  aesop

theorem rawXXOccupationMatrix_singleton {r : ℕ}
    {A : Matrix (Fin r) (Fin r) ℂ}
    (hA : MatrixNearestNeighbor A) (a b : Fin r) :
    rawXXOccupationMatrix A {a} {b} = A a b := by
  classical
  have hnum :
      (∑ i, A i i * occupationNumberMatrix i {a} {b}) =
        if a = b then A b b else 0 := by
    by_cases hab : a = b
    · subst a
      simp [occupationNumberMatrix]
    · simp [occupationNumberMatrix, hab]
  have hhop :
      (∑ i, ∑ j, A i j *
          occupationHopMatrix i j {a} {b} *
            if AdjacentSites i j then 1 else 0) =
        if AdjacentSites a b ∧ a ≠ b then A a b else 0 := by
    rw [Fintype.sum_eq_single a]
    · rw [Fintype.sum_eq_single b]
      · by_cases hab : a = b
        · simp [occupationHopMatrix_singleton, hab]
        · by_cases hadj : AdjacentSites a b
          · simp [occupationHopMatrix_singleton, hab, hadj]
          · simp [occupationHopMatrix_singleton, hab, hadj]
      · intro j hj
        simp [occupationHopMatrix_singleton, hj]
    · intro i hi
      simp [occupationHopMatrix_singleton, hi]
  rw [rawXXOccupationMatrix, hnum, hhop]
  by_cases hab : a = b
  · subst a
    simp [AdjacentSites]
  · by_cases hadj : AdjacentSites a b
    · simp [hab, hadj]
    · rw [hA a b hab hadj]
      simp [hab, hadj]

/--
Hermitian nearest-neighbour number-conserving XX occupation matrix.  The
Hermitian symmetrization is redundant on a Hermitian nearest-neighbour
one-particle block, but makes self-adjointness of the full spin matrix
unconditional.
-/
def xxOccupationMatrix {r : ℕ}
    (A : Matrix (Fin r) (Fin r) ℂ) :
    Matrix (Finset (Fin r)) (Finset (Fin r)) ℂ :=
  (2 : ℂ)⁻¹ •
    (rawXXOccupationMatrix A +
      Matrix.conjTranspose (rawXXOccupationMatrix A))

theorem xxOccupationMatrix_isHermitian {r : ℕ}
    (A : Matrix (Fin r) (Fin r) ℂ) :
    (xxOccupationMatrix A).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro S T
  simp [xxOccupationMatrix, Matrix.conjTranspose_apply]
  ring

theorem xxOccupationMatrix_eq_zero_of_card_ne {r : ℕ}
    (A : Matrix (Fin r) (Fin r) ℂ)
    {S T : Finset (Fin r)} (hcard : S.card ≠ T.card) :
    xxOccupationMatrix A S T = 0 := by
  simp [xxOccupationMatrix,
    rawXXOccupationMatrix_eq_zero_of_card_ne A hcard,
    rawXXOccupationMatrix_eq_zero_of_card_ne A (Ne.symm hcard)]

theorem xxOccupationMatrix_preserves_oneExcitation {r : ℕ}
    (A : Matrix (Fin r) (Fin r) ℂ) (j : Fin r)
    {S : Finset (Fin r)} (hS : S.card ≠ 1) :
    xxOccupationMatrix A S {j} = 0 := by
  apply xxOccupationMatrix_eq_zero_of_card_ne
  simpa using hS

theorem xxOccupationMatrix_singleton {r : ℕ}
    {A : Matrix (Fin r) (Fin r) ℂ}
    (hA : MatrixNearestNeighbor A) (hAH : A.IsHermitian)
    (a b : Fin r) :
    xxOccupationMatrix A {a} {b} = A a b := by
  rw [xxOccupationMatrix, Matrix.smul_apply, Matrix.add_apply,
    rawXXOccupationMatrix_singleton hA,
    Matrix.conjTranspose_apply,
    rawXXOccupationMatrix_singleton hA,
    hAH.apply]
  change (2 : ℂ)⁻¹ * (A a b + A a b) = A a b
  ring

/-- Matrix of a finite Hilbert-space operator in the standard site basis. -/
def finiteOperatorMatrix {r : ℕ}
    (A : FiniteIndexClockSpace (Fin r) →L[ℂ]
      FiniteIndexClockSpace (Fin r)) :
    Matrix (Fin r) (Fin r) ℂ :=
  fun i j =>
    inner ℂ (EuclideanSpace.basisFun (Fin r) ℂ i)
      (A (EuclideanSpace.basisFun (Fin r) ℂ j))

theorem finiteOperatorMatrix_isHermitian {r : ℕ}
    {A : FiniteIndexClockSpace (Fin r) →L[ℂ]
      FiniteIndexClockSpace (Fin r)}
    (hA : ContinuousLinearMap.adjoint A = A) :
    (finiteOperatorMatrix A).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  unfold finiteOperatorMatrix
  calc
    starRingEnd ℂ
        (inner ℂ (EuclideanSpace.basisFun (Fin r) ℂ j)
          (A (EuclideanSpace.basisFun (Fin r) ℂ i))) =
      inner ℂ (A (EuclideanSpace.basisFun (Fin r) ℂ i))
        (EuclideanSpace.basisFun (Fin r) ℂ j) := by
          exact inner_conj_symm _ _
    _ = inner ℂ (EuclideanSpace.basisFun (Fin r) ℂ i)
        ((ContinuousLinearMap.adjoint A)
          (EuclideanSpace.basisFun (Fin r) ℂ j)) := by
          symm
          exact ContinuousLinearMap.adjoint_inner_right A _ _
    _ = inner ℂ (EuclideanSpace.basisFun (Fin r) ℂ i)
        (A (EuclideanSpace.basisFun (Fin r) ℂ j)) := by rw [hA]

theorem finiteOperatorMatrix_nearestNeighbor {r : ℕ}
    {A : FiniteIndexClockSpace (Fin r) →L[ℂ]
      FiniteIndexClockSpace (Fin r)}
    (hA : NearestNeighborHamiltonian A) :
    MatrixNearestNeighbor (finiteOperatorMatrix A) := by
  intro i j hij hnot
  apply hA i j
  unfold AdjacentSites at hnot
  have hv : (i : ℕ) ≠ (j : ℕ) := by
    exact fun h => hij (Fin.ext h)
  omega

/--
Every self-adjoint nearest-neighbour one-particle Hamiltonian is exactly the
one-excitation block of a Hermitian, particle-number-preserving local XX
spin-chain matrix.
-/
theorem localSpinChain_singleExcitation_block {r : ℕ}
    {A : FiniteIndexClockSpace (Fin r) →L[ℂ]
      FiniteIndexClockSpace (Fin r)}
    (hA : NearestNeighborHamiltonian A)
    (hAH : ContinuousLinearMap.adjoint A = A)
    (i j : Fin r) :
    xxOccupationMatrix (finiteOperatorMatrix A) {i} {j} =
      finiteOperatorMatrix A i j := by
  exact xxOccupationMatrix_singleton
    (finiteOperatorMatrix_nearestNeighbor hA)
    (finiteOperatorMatrix_isHermitian hAH) i j

/--
Universal local-spin realization including the perfect-return endpoint.
The full occupation matrix is Hermitian and particle-number preserving, and
its one-excitation block is exactly the fixed-protocol block-Jacobi
Hamiltonian. Thus the same fixed one-excitation preparation and return test
inherit every terminal probability in `[0,1]` from the one-particle theorem.
-/
theorem one_fixed_local_spin_chain_every_future_probability
    (m : ℕ) (T H : ℝ) (hT : 0 < T) (hH0 : 0 ≤ H)
    (hHT : H < T) {δ : ℝ} (hδ : 0 < δ) :
    ∃ n : ℕ,
      m < n ∧
      ‖fixedClock n‖ = 1 ∧
      ∀ p : ℝ, p ∈ Set.Icc (0 : ℝ) 1 →
        ∃ U : ClockSpace n ≃ₗᵢ[ℂ] ClockSpace n,
          U (fixedClock n) =
              interpolatedClock n (Real.sqrt p) ∧
          NearestNeighborHamiltonian
            (fixedProtocolHamiltonian T n U) ∧
          (∀ k : ℕ, k ≤ m →
            inner ℂ (fixedClock n)
                (((fixedProtocolHamiltonian T n U) ^ k)
                  (fixedClock n)) =
              (∑ j : Fin (n + 1),
                fullWeight n j *
                  angularEnergy T n j ^ k : ℝ)) ∧
          ContinuousLinearMap.adjoint
              (fixedProtocolHamiltonian T n U) =
            fixedProtocolHamiltonian T n U ∧
          (∀ x : ClockSpace n,
            U (fixedProtocolHamiltonian T n U x) =
              scaledClockHamiltonian T n (U x)) ∧
          (∀ t : ℝ, |t| ≤ H →
            |fixedProtocolProbability
                T n (Real.sqrt p) t U -
              scaledFullProbability T n t| < δ) ∧
          fixedProtocolProbability
              T n (Real.sqrt p) T U = p ∧
          let A := fixedProtocolHamiltonian T n U
          let X := xxOccupationMatrix (finiteOperatorMatrix A)
          X.IsHermitian ∧
            (∀ S R : Finset (Fin (n + 1)),
              S.card ≠ R.card → X S R = 0) ∧
            (∀ i j : Fin (n + 1),
              X {i} {j} = finiteOperatorMatrix A i j) := by
  obtain ⟨n, hmn, hnorm, hall⟩ :=
    one_fixed_nearestNeighbor_chain_every_future_probability
      m T H hT hH0 hHT hδ
  refine ⟨n, hmn, hnorm, ?_⟩
  intro p hp
  obtain ⟨U, hU, hNN, hmom, hAdj, hInter, hwindow, htarget⟩ :=
    hall p hp
  refine ⟨U, hU, hNN, hmom, hAdj, hInter, hwindow,
    htarget, ?_⟩
  dsimp only
  refine ⟨xxOccupationMatrix_isHermitian _, ?_, ?_⟩
  · intro S R hcard
    exact xxOccupationMatrix_eq_zero_of_card_ne _ hcard
  · intro i j
    exact localSpinChain_singleExcitation_block hNN hAdj i j

end RHTower.ParityForecast
