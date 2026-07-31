import GaloisForLFunctions.RHTower.ParityConditionedForecastingInstability
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho

/-!
# Krylov nearest-neighbour realization of the recurrence ambiguity

A positive finite spectral measure is cyclic.  Its power orbit is a
Vandermonde basis; Gram--Schmidt in that orbit turns the diagonal generator
into a tridiagonal one while keeping the cyclic state as the first basis
vector.  Applied to the parity-interpolated clocks, this realizes every
strictly subunit terminal return probability by a nearest-neighbour
one-particle chain with the same spectrum and fixed endpoint protocol.
-/

open scoped BigOperators InnerProductSpace
open Complex

noncomputable section

namespace RHTower.ParityForecast

/-- Power orbit of a finite weight ket under its diagonal Hamiltonian. -/
def finiteKrylovVector {r : ℕ}
    (energy weight : Fin r → ℝ) (k : Fin r) :
    FiniteIndexClockSpace (Fin r) :=
  ((finiteIndexDiagonalHamiltonian energy) ^ (k : ℕ))
    (finiteIndexWeightKet weight)

@[simp] theorem finiteKrylovVector_apply {r : ℕ}
    (energy weight : Fin r → ℝ) (k j : Fin r) :
    finiteKrylovVector energy weight k j =
      ((energy j : ℂ) ^ (k : ℕ)) *
        (Real.sqrt (weight j) : ℂ) := by
  exact finiteIndexDiagonalHamiltonian_pow_apply
    energy (k : ℕ) (finiteIndexWeightKet weight) j

/--
Positive weights at distinct energies make the complete finite Krylov orbit
linearly independent.
-/
theorem finiteKrylovVector_linearIndependent {r : ℕ}
    {energy weight : Fin r → ℝ}
    (henergy : Function.Injective energy)
    (hweight : ∀ j, 0 < weight j) :
    LinearIndependent ℂ (finiteKrylovVector energy weight) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc k
  have hsqrt : ∀ j : Fin r,
      (Real.sqrt (weight j) : ℂ) ≠ 0 := by
    intro j
    exact_mod_cast (Real.sqrt_pos.2 (hweight j)).ne'
  have hrelations : ∀ j : Fin r,
      ∑ i : Fin r, c i * (energy j : ℂ) ^ (i : ℕ) = 0 := by
    intro j
    have hj := congrArg
      (fun x : FiniteIndexClockSpace (Fin r) =>
        (WithLp.linearEquiv 2 ℂ (Fin r → ℂ)) x j) hc
    simp only [map_sum, map_smul, Finset.sum_apply,
      Pi.smul_apply,
      smul_eq_mul, map_zero, Pi.zero_apply] at hj
    change
      (∑ i : Fin r, c i * finiteKrylovVector energy weight i j) =
        0 at hj
    simp_rw [finiteKrylovVector_apply] at hj
    apply (mul_right_cancel₀ (hsqrt j))
    calc
      (∑ i : Fin r, c i * (energy j : ℂ) ^ (i : ℕ)) *
          (Real.sqrt (weight j) : ℂ) =
        ∑ i : Fin r,
          c i * ((energy j : ℂ) ^ (i : ℕ) *
            (Real.sqrt (weight j) : ℂ)) := by
              rw [Finset.sum_mul]
              apply Finset.sum_congr rfl
              intro i _hi
              ring
      _ = 0 := hj
      _ = 0 * (Real.sqrt (weight j) : ℂ) := by ring
  have henergyC : Function.Injective
      (fun j : Fin r => (energy j : ℂ)) := by
    intro i j hij
    apply henergy
    exact Complex.ofReal_injective hij
  have hc0 :
      c = 0 :=
    Matrix.eq_zero_of_forall_index_sum_mul_pow_eq_zero
      henergyC hrelations
  exact congrFun hc0 k

/-- Orthonormal Krylov basis attached to a positive finite spectral packet. -/
def finiteKrylovBasis {r : ℕ}
    (energy weight : Fin r → ℝ) :
    OrthonormalBasis (Fin r) ℂ (FiniteIndexClockSpace (Fin r)) :=
  InnerProductSpace.gramSchmidtOrthonormalBasis
    (by simp [FiniteIndexClockSpace])
    (finiteKrylovVector energy weight)

theorem finiteKrylovBasis_eq_gramSchmidtNormed {r : ℕ}
    {energy weight : Fin r → ℝ}
    (henergy : Function.Injective energy)
    (hweight : ∀ j, 0 < weight j)
    (i : Fin r) :
    finiteKrylovBasis energy weight i =
      InnerProductSpace.gramSchmidtNormed ℂ
        (finiteKrylovVector energy weight) i := by
  apply InnerProductSpace.gramSchmidtOrthonormalBasis_apply
  have hnorm :=
    InnerProductSpace.gramSchmidtNormed_unit_length i
      (finiteKrylovVector_linearIndependent henergy hweight)
  exact (norm_ne_zero_iff.mp (by simp [hnorm]))

/-- The first Krylov basis vector is the original normalized weight ket. -/
theorem finiteKrylovBasis_zero {r : ℕ} [NeZero r]
    {energy weight : Fin r → ℝ}
    (henergy : Function.Injective energy)
    (hweight : ∀ j, 0 < weight j)
    (hweightSum : ∑ j : Fin r, weight j = 1) :
    finiteKrylovBasis energy weight 0 =
      finiteIndexWeightKet weight := by
  rw [finiteKrylovBasis_eq_gramSchmidtNormed
    henergy hweight]
  rw [InnerProductSpace.gramSchmidtNormed]
  have hgs :
      InnerProductSpace.gramSchmidt ℂ
          (finiteKrylovVector energy weight) (0 : Fin r) =
        finiteKrylovVector energy weight 0 := by
    rw [InnerProductSpace.gramSchmidt_def]
    have hempty : Finset.Iio (0 : Fin r) = ∅ := by
      ext i
      simp only [Finset.mem_Iio, Finset.notMem_empty, iff_false]
      have hz : ((0 : Fin r) : ℕ) = 0 := Fin.val_zero r
      omega
    rw [hempty]
    simp
  rw [hgs]
  have hnorm :
      ‖finiteIndexWeightKet weight‖ = 1 :=
    finiteIndexWeightKet_norm_eq_one weight
      (fun j => (hweight j).le) hweightSum
  simp [finiteKrylovVector, hnorm]

/-- Standard coordinates transported to the orthonormal Krylov basis. -/
def finiteKrylovUnitary {r : ℕ}
    (energy weight : Fin r → ℝ) :
    FiniteIndexClockSpace (Fin r) ≃ₗᵢ[ℂ]
      FiniteIndexClockSpace (Fin r) :=
  (EuclideanSpace.basisFun (Fin r) ℂ).equiv
    (finiteKrylovBasis energy weight) (Equiv.refl (Fin r))

@[simp] theorem finiteKrylovUnitary_basis {r : ℕ}
    (energy weight : Fin r → ℝ) (i : Fin r) :
    finiteKrylovUnitary energy weight
        (EuclideanSpace.basisFun (Fin r) ℂ i) =
      finiteKrylovBasis energy weight i := by
  exact OrthonormalBasis.equiv_apply_basis _ _ _ i

/-- Matrix locality: entries vanish beyond the two nearest diagonals. -/
def NearestNeighborHamiltonian {r : ℕ}
    (A : FiniteIndexClockSpace (Fin r) →L[ℂ]
      FiniteIndexClockSpace (Fin r)) : Prop :=
  ∀ i j : Fin r,
    ((i : ℕ) + 1 < (j : ℕ) ∨
      (j : ℕ) + 1 < (i : ℕ)) →
      inner ℂ (EuclideanSpace.basisFun (Fin r) ℂ i)
        (A (EuclideanSpace.basisFun (Fin r) ℂ j)) = 0

private theorem finiteKrylovVector_step {r : ℕ}
    (energy weight : Fin r → ℝ) {k : Fin r}
    (hk : (k : ℕ) + 1 < r) :
    finiteIndexDiagonalHamiltonian energy
        (finiteKrylovVector energy weight k) =
      finiteKrylovVector energy weight
        ⟨(k : ℕ) + 1, hk⟩ := by
  ext j
  simp only [finiteIndexDiagonalHamiltonian_apply,
    finiteKrylovVector_apply]
  ring

private theorem finiteKrylovBasis_upper_entry_zero {r : ℕ}
    {energy weight : Fin r → ℝ}
    (henergy : Function.Injective energy)
    (hweight : ∀ j, 0 < weight j)
    {i j : Fin r} (hji : (j : ℕ) + 1 < (i : ℕ)) :
    inner ℂ (finiteKrylovBasis energy weight i)
      (finiteIndexDiagonalHamiltonian energy
        (finiteKrylovBasis energy weight j)) = 0 := by
  let f := finiteKrylovVector energy weight
  let b := finiteKrylovBasis energy weight
  have hli : LinearIndependent ℂ f :=
    finiteKrylovVector_linearIndependent henergy hweight
  have hbspan :
      b j ∈ Submodule.span ℂ (f '' Set.Iic j) := by
    rw [show b j =
        InnerProductSpace.gramSchmidtNormed ℂ f j by
      exact finiteKrylovBasis_eq_gramSchmidtNormed
        henergy hweight j]
    exact Submodule.smul_mem _ _
      (InnerProductSpace.gramSchmidt_mem_span ℂ f le_rfl)
  refine Submodule.span_induction
    (p := fun x _ =>
      inner ℂ (b i)
        (finiteIndexDiagonalHamiltonian energy x) = 0)
    ?_ ?_ ?_ ?_ hbspan
  · intro x hx
    obtain ⟨k, hk, rfl⟩ := hx
    have hkn : (k : ℕ) + 1 < r := by
      have hkj : (k : ℕ) ≤ (j : ℕ) := hk
      omega
    let ks : Fin r := ⟨(k : ℕ) + 1, hkn⟩
    have hksi : ks < i := by
      change (k : ℕ) + 1 < (i : ℕ)
      have hkj : (k : ℕ) ≤ (j : ℕ) := hk
      omega
    rw [finiteKrylovVector_step energy weight hkn]
    exact
      InnerProductSpace.gramSchmidtOrthonormalBasis_inv_triangular
        (by simp [FiniteIndexClockSpace]) f hksi
  · simp
  · intro x y _hx _hy hzx hzy
    simp only [map_add, inner_add_right, hzx, hzy, add_zero]
  · intro c x _hx hzx
    simp only [map_smul, inner_smul_right, hzx, mul_zero]

/--
The diagonal Hamiltonian is exactly tridiagonal in its normalized Krylov
basis.
-/
theorem finiteKrylovBasis_nearestNeighbor {r : ℕ}
    {energy weight : Fin r → ℝ}
    (henergy : Function.Injective energy)
    (hweight : ∀ j, 0 < weight j) :
    ∀ i j : Fin r,
      ((i : ℕ) + 1 < (j : ℕ) ∨
        (j : ℕ) + 1 < (i : ℕ)) →
      inner ℂ (finiteKrylovBasis energy weight i)
        (finiteIndexDiagonalHamiltonian energy
          (finiteKrylovBasis energy weight j)) = 0 := by
  intro i j hij
  rcases hij with hij | hji
  · have hzero :=
      finiteKrylovBasis_upper_entry_zero
        henergy hweight hij
    have hadj :=
      ContinuousLinearMap.adjoint_inner_right
        (finiteIndexDiagonalHamiltonian energy)
        (finiteKrylovBasis energy weight i)
        (finiteKrylovBasis energy weight j)
    rw [finiteIndexDiagonalHamiltonian_selfAdjoint] at hadj
    calc
      inner ℂ (finiteKrylovBasis energy weight i)
          (finiteIndexDiagonalHamiltonian energy
            (finiteKrylovBasis energy weight j)) =
          inner ℂ
            (finiteIndexDiagonalHamiltonian energy
              (finiteKrylovBasis energy weight i))
            (finiteKrylovBasis energy weight j) := hadj
      _ = starRingEnd ℂ
          (inner ℂ (finiteKrylovBasis energy weight j)
            (finiteIndexDiagonalHamiltonian energy
              (finiteKrylovBasis energy weight i))) := by
            symm
            exact inner_conj_symm _ _
      _ = 0 := by rw [hzero]; simp
  · exact finiteKrylovBasis_upper_entry_zero
      henergy hweight hji

/--
Pulling the diagonal Hamiltonian back through the Krylov unitary gives a
nearest-neighbour Hamiltonian in the fixed standard coordinates.
-/
theorem finiteKrylov_conjugate_nearestNeighbor {r : ℕ}
    {energy weight : Fin r → ℝ}
    (henergy : Function.Injective energy)
    (hweight : ∀ j, 0 < weight j) :
    NearestNeighborHamiltonian
      ((finiteKrylovUnitary energy weight).symm.toContinuousLinearEquiv.toContinuousLinearMap ∘L
        finiteIndexDiagonalHamiltonian energy ∘L
          (finiteKrylovUnitary energy weight).toContinuousLinearEquiv.toContinuousLinearMap) := by
  intro i j hij
  let U := finiteKrylovUnitary energy weight
  have hUi :
      U (EuclideanSpace.basisFun (Fin r) ℂ i) =
        finiteKrylovBasis energy weight i := by
    simpa [U] using finiteKrylovUnitary_basis energy weight i
  have hUj :
      U (EuclideanSpace.basisFun (Fin r) ℂ j) =
        finiteKrylovBasis energy weight j := by
    simpa [U] using finiteKrylovUnitary_basis energy weight j
  have htransport :
      U (((U.symm.toContinuousLinearEquiv.toContinuousLinearMap ∘L
          finiteIndexDiagonalHamiltonian energy ∘L
            U.toContinuousLinearEquiv.toContinuousLinearMap))
          (EuclideanSpace.basisFun (Fin r) ℂ j)) =
        finiteIndexDiagonalHamiltonian energy
          (U (EuclideanSpace.basisFun (Fin r) ℂ j)) := by
    simp
  calc
    inner ℂ (EuclideanSpace.basisFun (Fin r) ℂ i)
        (((U.symm.toContinuousLinearEquiv.toContinuousLinearMap ∘L
          finiteIndexDiagonalHamiltonian energy ∘L
            U.toContinuousLinearEquiv.toContinuousLinearMap))
          (EuclideanSpace.basisFun (Fin r) ℂ j)) =
      inner ℂ (U (EuclideanSpace.basisFun (Fin r) ℂ i))
        (U (((U.symm.toContinuousLinearEquiv.toContinuousLinearMap ∘L
          finiteIndexDiagonalHamiltonian energy ∘L
            U.toContinuousLinearEquiv.toContinuousLinearMap))
          (EuclideanSpace.basisFun (Fin r) ℂ j))) := by
            symm
            exact U.inner_map_map _ _
    _ = inner ℂ (finiteKrylovBasis energy weight i)
        (finiteIndexDiagonalHamiltonian energy
          (finiteKrylovBasis energy weight j)) := by
            rw [htransport, hUi, hUj]
    _ = 0 :=
      finiteKrylovBasis_nearestNeighbor henergy hweight i j hij

/-- Every fair-binomial weight is strictly positive. -/
theorem fullWeight_pos (n : ℕ) (j : Fin (n + 1)) :
    0 < fullWeight n j := by
  unfold fullWeight RHTower.FiniteWindow.binomialWeight
  exact div_pos
    (by exact_mod_cast Nat.choose_pos (Nat.le_of_lt_succ j.isLt))
    (pow_pos (by norm_num) _)

/-- Interpolated weights remain strictly positive before the parity endpoint. -/
theorem interpolatedWeight_pos
    (n : ℕ) {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)
    (j : Fin (n + 1)) :
    0 < interpolatedWeight n θ j := by
  unfold interpolatedWeight
  exact add_pos_of_pos_of_nonneg
    (mul_pos (sub_pos.mpr hθ1) (fullWeight_pos n j))
    (mul_nonneg hθ0 (parityWeight_nonneg n j))

/-- The angular-energy list has no repeated levels. -/
theorem angularEnergy_injective {T : ℝ} (hT : 0 < T) (n : ℕ) :
    Function.Injective (angularEnergy T n) := by
  intro i j hij
  apply Fin.ext
  rw [angularEnergy_eq, angularEnergy_eq] at hij
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hT0 : T ≠ 0 := ne_of_gt hT
  apply_fun fun x : ℝ => x * T at hij
  field_simp [hT0] at hij
  have hijR : (i : ℝ) = (j : ℝ) := by
    nlinarith [Real.pi_pos]
  exact_mod_cast hijR

/-- Krylov unitary sends the fixed endpoint state to the interpolated clock. -/
theorem finiteKrylovUnitary_fixedClock
    {T : ℝ} (hT : 0 < T) {n : ℕ} (hn : 0 < n)
    {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) :
    finiteKrylovUnitary (angularEnergy T n)
        (interpolatedWeight n θ) (fixedClock n) =
      interpolatedClock n θ := by
  rw [fixedClock, finiteKrylovUnitary_basis]
  exact finiteKrylovBasis_zero
    (angularEnergy_injective hT n)
    (interpolatedWeight_pos n hθ0 hθ1)
    (interpolatedWeight_sum hn θ)

/--
Every strict subunit member of the fixed-protocol family admits a
nearest-neighbour one-particle-chain representative with the same diagonal
spectrum.
-/
theorem fixedProtocolHamiltonian_krylov_nearestNeighbor
    {T : ℝ} (hT : 0 < T) {n : ℕ}
    {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) :
    NearestNeighborHamiltonian
      (fixedProtocolHamiltonian T n
        (finiteKrylovUnitary (angularEnergy T n)
          (interpolatedWeight n θ))) := by
  exact finiteKrylov_conjugate_nearestNeighbor
    (angularEnergy_injective hT n)
    (interpolatedWeight_pos n hθ0 hθ1)

/--
Nearest-neighbour universal law below the closed parity endpoint. One fixed
normalized state and projector admit every terminal return probability
`p < 1` under an isospectral family of finite tridiagonal Hamiltonians,
while any prescribed finite collection of energy moments and the full
strictly earlier survival record remain common.
-/
theorem one_fixed_nearestNeighbor_chain_every_strict_future_probability
    (m : ℕ) (T H : ℝ) (hT : 0 < T) (hH0 : 0 ≤ H)
    (hHT : H < T) {δ : ℝ} (hδ : 0 < δ) :
    ∃ n : ℕ,
      m < n ∧
      ‖fixedClock n‖ = 1 ∧
      ∀ p : ℝ, p ∈ Set.Ico (0 : ℝ) 1 →
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
              T n (Real.sqrt p) T U = p := by
  obtain ⟨n, hmn, hall⟩ :=
    one_record_compatible_with_every_future_probability
      m T H hT hH0 hHT hδ
  have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le m) hmn
  refine ⟨n, hmn, fixedClock_norm n, ?_⟩
  intro p hp
  obtain ⟨_hmom, hwindow, htarget⟩ :=
    hall p ⟨hp.1, hp.2.le⟩
  have hθ0 : 0 ≤ Real.sqrt p := Real.sqrt_nonneg p
  have hθ1 : Real.sqrt p < 1 := by
    rw [Real.sqrt_lt' zero_lt_one]
    simpa using hp.2
  let U : ClockSpace n ≃ₗᵢ[ℂ] ClockSpace n :=
    finiteKrylovUnitary (angularEnergy T n)
      (interpolatedWeight n (Real.sqrt p))
  have hU :
      U (fixedClock n) =
        interpolatedClock n (Real.sqrt p) := by
    exact finiteKrylovUnitary_fixedClock
      hT hn hθ0 hθ1
  refine ⟨U, hU,
    fixedProtocolHamiltonian_krylov_nearestNeighbor
      hT hθ0 hθ1, ?_,
    fixedProtocolHamiltonian_selfAdjoint T n U,
    fixedProtocolHamiltonian_intertwines T n U, ?_, ?_⟩
  · intro k hk
    exact fixedProtocol_energyMoment_eq_full
      (lt_of_le_of_lt hk hmn) hθ0 hθ1.le hU
  · intro t ht
    rw [fixedProtocolProbability_eq
      hT n hθ0 hθ1.le t hU]
    exact hwindow t ht
  · rw [fixedProtocolProbability_eq
      hT n hθ0 hθ1.le T hU]
    exact htarget

end RHTower.ParityForecast
