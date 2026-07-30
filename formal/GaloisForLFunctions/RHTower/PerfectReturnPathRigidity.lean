import GaloisForLFunctions.RHTower.EndpointKrylovNearestNeighborRealization

/-!
# Perfect-return path rigidity

An endpoint of a tridiagonal path with no zero forward coupling is cyclic:
no nonzero eigenvector can be orthogonal to that endpoint.  The
parity-supported perfect-return clock has explicit missing spectral
coordinates.  Consequently every tridiagonal fixed-protocol realization of
that clock must contain a zero path coupling.
-/

open scoped BigOperators InnerProductSpace
open Complex

noncomputable section

namespace RHTower.ParityForecast

/-- Every forward matrix element along the path is nonzero. -/
def ForwardConnectedHamiltonian {n : ℕ}
    (A : ClockSpace n →L[ℂ] ClockSpace n) : Prop :=
  ∀ i : Fin n,
    inner ℂ
        (EuclideanSpace.basisFun (Fin (n + 1)) ℂ i.castSucc)
        (A (EuclideanSpace.basisFun (Fin (n + 1)) ℂ i.succ)) ≠ 0

/-- Expand one row of an operator in the standard orthonormal basis. -/
theorem inner_map_eq_sum_matrix {n : ℕ}
    (A : ClockSpace n →L[ℂ] ClockSpace n)
    (i : Fin (n + 1)) (v : ClockSpace n) :
    inner ℂ (EuclideanSpace.basisFun (Fin (n + 1)) ℂ i) (A v) =
      ∑ j : Fin (n + 1),
        inner ℂ (EuclideanSpace.basisFun (Fin (n + 1)) ℂ j) v *
          inner ℂ (EuclideanSpace.basisFun (Fin (n + 1)) ℂ i)
            (A (EuclideanSpace.basisFun (Fin (n + 1)) ℂ j)) := by
  let b := EuclideanSpace.basisFun (Fin (n + 1)) ℂ
  conv_lhs =>
    rw [← b.sum_repr' v]
  simp only [map_sum, map_smul, inner_sum, inner_smul_right]
  rfl

/--
Every nonzero eigenvector of a connected nearest-neighbour path has nonzero
overlap with its first endpoint.
-/
theorem connected_nearestNeighbor_eigenvector_endpoint_ne_zero
    {n : ℕ}
    {A : ClockSpace n →L[ℂ] ClockSpace n}
    (hnn : NearestNeighborHamiltonian A)
    (hconn : ForwardConnectedHamiltonian A)
    {v : ClockSpace n} {μ : ℂ}
    (heigen : A v = μ • v)
    (hv : v ≠ 0) :
    inner ℂ (EuclideanSpace.basisFun (Fin (n + 1)) ℂ 0) v ≠ 0 := by
  intro hzero
  have hall :
      ∀ k : Fin (n + 1), ∀ j : Fin (n + 1),
        (j : ℕ) ≤ (k : ℕ) →
          inner ℂ
            (EuclideanSpace.basisFun (Fin (n + 1)) ℂ j) v = 0 := by
    intro k
    induction k using Fin.induction with
    | zero =>
        intro j hj
        change (j : ℕ) ≤ 0 at hj
        have hj0 : j = 0 := by
          apply Fin.ext
          exact Nat.eq_zero_of_le_zero hj
        simpa [hj0] using hzero
    | succ i ih =>
        intro j hj
        change (j : ℕ) ≤ (i : ℕ) + 1 at hj
        by_cases hjle : (j : ℕ) ≤ (i : ℕ)
        · exact ih j hjle
        · have hji : j = i.succ := by
            apply Fin.ext
            change (j : ℕ) = (i : ℕ) + 1
            exact Nat.le_antisymm hj (by omega)
          subst j
          have hrow :
              inner ℂ
                  (EuclideanSpace.basisFun (Fin (n + 1)) ℂ i.castSucc)
                  (A v) = 0 := by
            rw [heigen, inner_smul_right]
            rw [ih i.castSucc (by simp)]
            simp
          rw [inner_map_eq_sum_matrix A i.castSucc v] at hrow
          have hsum :
              (∑ j : Fin (n + 1),
                inner ℂ
                    (EuclideanSpace.basisFun (Fin (n + 1)) ℂ j) v *
                  inner ℂ
                    (EuclideanSpace.basisFun (Fin (n + 1)) ℂ i.castSucc)
                    (A (EuclideanSpace.basisFun (Fin (n + 1)) ℂ j))) =
                inner ℂ
                    (EuclideanSpace.basisFun (Fin (n + 1)) ℂ i.succ) v *
                  inner ℂ
                    (EuclideanSpace.basisFun (Fin (n + 1)) ℂ i.castSucc)
                    (A (EuclideanSpace.basisFun
                      (Fin (n + 1)) ℂ i.succ)) := by
            apply Finset.sum_eq_single i.succ
            · intro j _hj hji
              by_cases hjle : (j : ℕ) ≤ (i : ℕ)
              · rw [ih j hjle]
                simp
              · have hfar :
                    (i.castSucc : ℕ) + 1 < (j : ℕ) := by
                  change (i : ℕ) + 1 < (j : ℕ)
                  have hjne : (j : ℕ) ≠ (i : ℕ) + 1 := by
                    intro h
                    apply hji
                    apply Fin.ext
                    simpa using h
                  omega
                rw [hnn i.castSucc j (Or.inl hfar)]
                simp
            · simp
          rw [hsum] at hrow
          exact (mul_eq_zero.mp hrow).resolve_right (hconn i)
  apply hv
  ext k
  have hk := hall k k le_rfl
  rw [EuclideanSpace.basisFun_inner] at hk
  exact hk

/--
A nonzero endpoint-orthogonal eigenvector forces at least one zero path
coupling in every tridiagonal representation.
-/
theorem nearestNeighbor_endpointOrthogonal_eigenvector_forces_disconnection
    {n : ℕ}
    {A : ClockSpace n →L[ℂ] ClockSpace n}
    (hnn : NearestNeighborHamiltonian A)
    {v : ClockSpace n} {μ : ℂ}
    (heigen : A v = μ • v)
    (hv : v ≠ 0)
    (horthogonal :
      inner ℂ (EuclideanSpace.basisFun (Fin (n + 1)) ℂ 0) v = 0) :
    ∃ i : Fin n,
      inner ℂ
        (EuclideanSpace.basisFun (Fin (n + 1)) ℂ i.castSucc)
        (A (EuclideanSpace.basisFun (Fin (n + 1)) ℂ i.succ)) = 0 := by
  by_contra hnone
  have hconn : ForwardConnectedHamiltonian A := by
    intro i hzero
    exact hnone ⟨i, hzero⟩
  exact
    (connected_nearestNeighbor_eigenvector_endpoint_ne_zero
      hnn hconn heigen hv) horthogonal

/-- One missing even spectral mode transported into fixed coordinates. -/
def endpointTransportedSpectator
    (q : ℕ)
    (U : ClockSpace (endpointN q) ≃ₗᵢ[ℂ]
      ClockSpace (endpointN q)) :
    ClockSpace (endpointN q) :=
  U.symm
    (EuclideanSpace.basisFun (Fin (endpointN q + 1)) ℂ
      (endpointEvenIndex q 0))

theorem endpointTransportedSpectator_ne_zero
    (q : ℕ)
    (U : ClockSpace (endpointN q) ≃ₗᵢ[ℂ]
      ClockSpace (endpointN q)) :
    endpointTransportedSpectator q U ≠ 0 := by
  intro hzero
  have himage := congrArg U hzero
  simp [endpointTransportedSpectator] at himage

theorem endpointTransportedSpectator_eigen
    (T : ℝ) (q : ℕ)
    (U : ClockSpace (endpointN q) ≃ₗᵢ[ℂ]
      ClockSpace (endpointN q)) :
    fixedProtocolHamiltonian T (endpointN q) U
        (endpointTransportedSpectator q U) =
      (angularEnergy T (endpointN q) (endpointEvenIndex q 0) : ℂ) •
        endpointTransportedSpectator q U := by
  apply U.injective
  rw [fixedProtocolHamiltonian_intertwines]
  rw [map_smul]
  simp only [endpointTransportedSpectator,
    LinearIsometryEquiv.apply_symm_apply]
  ext j
  by_cases hj : j = endpointEvenIndex q 0
  · subst j
    simp [scaledClockHamiltonian,
      RHTower.finiteIndexDiagonalHamiltonian_apply]
  · simp [scaledClockHamiltonian,
      RHTower.finiteIndexDiagonalHamiltonian_apply, hj]

theorem endpointTransportedSpectator_orthogonal_fixedClock
    (q : ℕ)
    (U : ClockSpace (endpointN q) ≃ₗᵢ[ℂ]
      ClockSpace (endpointN q))
    (hU : U (fixedClock (endpointN q)) =
      parityClock (endpointN q)) :
    inner ℂ (fixedClock (endpointN q))
      (endpointTransportedSpectator q U) = 0 := by
  calc
    inner ℂ (fixedClock (endpointN q))
        (endpointTransportedSpectator q U) =
      inner ℂ (U (fixedClock (endpointN q)))
        (U (endpointTransportedSpectator q U)) := by
          symm
          exact U.inner_map_map _ _
    _ = 0 := by
      rw [hU]
      simp only [endpointTransportedSpectator,
        LinearIsometryEquiv.apply_symm_apply, parityClock,
        EuclideanSpace.basisFun_apply,
        EuclideanSpace.inner_single_right, one_mul,
        RHTower.finiteIndexWeightKet_apply,
        endpointEvenWeight_zero, Real.sqrt_zero, Complex.ofReal_zero,
        map_zero]

/--
Sharp perfect-return locality boundary: every tridiagonal fixed-protocol
realization of the parity-supported endpoint has a zero path coupling.
-/
theorem endpoint_paritySupport_forces_path_disconnection
    (T : ℝ) (q : ℕ)
    (U : ClockSpace (endpointN q) ≃ₗᵢ[ℂ]
      ClockSpace (endpointN q))
    (hU : U (fixedClock (endpointN q)) =
      parityClock (endpointN q))
    (hnn : NearestNeighborHamiltonian
      (fixedProtocolHamiltonian T (endpointN q) U)) :
    ∃ i : Fin (endpointN q),
      inner ℂ
        (EuclideanSpace.basisFun (Fin (endpointN q + 1)) ℂ i.castSucc)
        (fixedProtocolHamiltonian T (endpointN q) U
          (EuclideanSpace.basisFun
            (Fin (endpointN q + 1)) ℂ i.succ)) = 0 := by
  exact nearestNeighbor_endpointOrthogonal_eigenvector_forces_disconnection
    hnn
    (endpointTransportedSpectator_eigen T q U)
    (endpointTransportedSpectator_ne_zero q U)
    (endpointTransportedSpectator_orthogonal_fixedClock q U hU)

/-- A Gram--Schmidt vector has nonzero overlap with its input vector. -/
theorem inner_gramSchmidt_input_ne_zero
    {r : ℕ}
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {f : Fin r → E} (hli : LinearIndependent ℂ f) (i : Fin r) :
    inner ℂ (InnerProductSpace.gramSchmidt ℂ f i) (f i) ≠ 0 := by
  intro hinner
  have hsum :
      inner ℂ (InnerProductSpace.gramSchmidt ℂ f i)
        (∑ j ∈ Finset.Iio i,
          (inner ℂ (InnerProductSpace.gramSchmidt ℂ f j) (f i) /
            (‖InnerProductSpace.gramSchmidt ℂ f j‖ : ℂ) ^ 2) •
              InnerProductSpace.gramSchmidt ℂ f j) = 0 := by
    rw [inner_sum]
    apply Finset.sum_eq_zero
    intro j hj
    rw [inner_smul_right]
    rw [InnerProductSpace.gramSchmidt_orthogonal ℂ f
      (ne_of_gt (Finset.mem_Iio.mp hj))]
    simp
  have hself :
      inner ℂ (InnerProductSpace.gramSchmidt ℂ f i)
        (InnerProductSpace.gramSchmidt ℂ f i) = 0 := by
    have hdef := congrArg
      (fun x : E =>
        inner ℂ (InnerProductSpace.gramSchmidt ℂ f i) x)
      (InnerProductSpace.gramSchmidt_def'' ℂ f i)
    change
      inner ℂ (InnerProductSpace.gramSchmidt ℂ f i) (f i) =
        inner ℂ (InnerProductSpace.gramSchmidt ℂ f i)
          (InnerProductSpace.gramSchmidt ℂ f i +
            ∑ j ∈ Finset.Iio i,
              (inner ℂ (InnerProductSpace.gramSchmidt ℂ f j) (f i) /
                (‖InnerProductSpace.gramSchmidt ℂ f j‖ : ℂ) ^ 2) •
                  InnerProductSpace.gramSchmidt ℂ f j) at hdef
    rw [inner_add_right, hinner, hsum, add_zero] at hdef
    exact hdef.symm
  exact
    (inner_self_ne_zero.mpr
      (InnerProductSpace.gramSchmidt_ne_zero i hli)) hself

/-- Each normalized Krylov vector has nonzero leading Krylov coefficient. -/
theorem finiteKrylovBasis_diagonal_overlap_ne_zero {r : ℕ}
    {energy weight : Fin r → ℝ}
    (henergy : Function.Injective energy)
    (hweight : ∀ j, 0 < weight j)
    (i : Fin r) :
    inner ℂ (finiteKrylovBasis energy weight i)
      (finiteKrylovVector energy weight i) ≠ 0 := by
  rw [finiteKrylovBasis_eq_gramSchmidtNormed henergy hweight]
  rw [InnerProductSpace.gramSchmidtNormed, inner_smul_left]
  apply mul_ne_zero
  · simp [InnerProductSpace.gramSchmidt_ne_zero i
      (finiteKrylovVector_linearIndependent henergy hweight)]
  · exact inner_gramSchmidt_input_ne_zero
      (finiteKrylovVector_linearIndependent henergy hweight) i

/--
Every adjacent matrix element in the finite Krylov basis is nonzero when
the spectral weights are strictly positive.
-/
theorem finiteKrylovBasis_forward_entry_ne_zero
    {n : ℕ}
    {energy weight : Fin (n + 1) → ℝ}
    (henergy : Function.Injective energy)
    (hweight : ∀ j, 0 < weight j)
    (i : Fin n) :
    inner ℂ (finiteKrylovBasis energy weight i.succ)
      (finiteIndexDiagonalHamiltonian energy
        (finiteKrylovBasis energy weight i.castSucc)) ≠ 0 := by
  let b := finiteKrylovBasis energy weight
  let f := finiteKrylovVector energy weight
  have hstep :
      finiteIndexDiagonalHamiltonian energy (f i.castSucc) =
        f i.succ := by
    ext j
    simp only [f, finiteKrylovVector_apply,
      RHTower.finiteIndexDiagonalHamiltonian_apply]
    change
      (energy j : ℂ) *
          ((energy j : ℂ) ^ (i : ℕ) *
            (Real.sqrt (weight j) : ℂ)) =
        (energy j : ℂ) ^ ((i : ℕ) + 1) *
          (Real.sqrt (weight j) : ℂ)
    rw [pow_succ]
    ring
  have hexpand := b.sum_repr' (f i.castSucc)
  have hmap := congrArg
    (finiteIndexDiagonalHamiltonian energy) hexpand
  have hrow :
      inner ℂ (b i.succ) (f i.succ) =
        ∑ j : Fin (n + 1),
          inner ℂ (b j) (f i.castSucc) *
            inner ℂ (b i.succ)
              (finiteIndexDiagonalHamiltonian energy (b j)) := by
    calc
      inner ℂ (b i.succ) (f i.succ) =
          inner ℂ (b i.succ)
            (finiteIndexDiagonalHamiltonian energy (f i.castSucc)) := by
              rw [hstep]
      _ = inner ℂ (b i.succ)
          (finiteIndexDiagonalHamiltonian energy
            (∑ j : Fin (n + 1),
              inner ℂ (b j) (f i.castSucc) • b j)) := by
            rw [hmap]
      _ = _ := by
        simp only [map_sum, map_smul, inner_sum, inner_smul_right]
  have hsingle :
      (∑ j : Fin (n + 1),
          inner ℂ (b j) (f i.castSucc) *
            inner ℂ (b i.succ)
              (finiteIndexDiagonalHamiltonian energy (b j))) =
        inner ℂ (b i.castSucc) (f i.castSucc) *
          inner ℂ (b i.succ)
            (finiteIndexDiagonalHamiltonian energy (b i.castSucc)) := by
    apply Finset.sum_eq_single i.castSucc
    · intro j _hj hji
      by_cases hjlt : (j : ℕ) < (i : ℕ)
      · have hfar : (j : ℕ) + 1 < (i.succ : ℕ) := by
          change (j : ℕ) + 1 < (i : ℕ) + 1
          omega
        rw [finiteKrylovBasis_nearestNeighbor
          henergy hweight i.succ j (Or.inr hfar)]
        simp
      · have hij : i.castSucc < j := by
          change (i : ℕ) < (j : ℕ)
          have hjne : (j : ℕ) ≠ (i : ℕ) := by
            intro h
            apply hji
            apply Fin.ext
            simpa using h
          omega
        rw [show inner ℂ (b j) (f i.castSucc) = 0 by
          exact
            InnerProductSpace.gramSchmidtOrthonormalBasis_inv_triangular
              (by simp [FiniteIndexClockSpace]) f hij]
        simp
    · simp
  rw [hsingle] at hrow
  have hleft :
      inner ℂ (b i.succ) (f i.succ) ≠ 0 := by
    exact finiteKrylovBasis_diagonal_overlap_ne_zero
      henergy hweight i.succ
  have hprod :
      inner ℂ (b i.castSucc) (f i.castSucc) *
          inner ℂ (b i.succ)
            (finiteIndexDiagonalHamiltonian energy (b i.castSucc)) ≠ 0 := by
    rwa [← hrow]
  exact (mul_ne_zero_iff.mp hprod).2

/-- Positive spectral weights give a connected Krylov path. -/
theorem finiteKrylov_conjugate_forwardConnected
    {n : ℕ}
    {energy weight : Fin (n + 1) → ℝ}
    (henergy : Function.Injective energy)
    (hweight : ∀ j, 0 < weight j) :
    ForwardConnectedHamiltonian
      ((finiteKrylovUnitary energy weight).symm.toContinuousLinearEquiv.toContinuousLinearMap ∘L
        finiteIndexDiagonalHamiltonian energy ∘L
          (finiteKrylovUnitary energy weight).toContinuousLinearEquiv.toContinuousLinearMap) := by
  intro i
  let U := finiteKrylovUnitary energy weight
  have hUi :
      U (EuclideanSpace.basisFun (Fin (n + 1)) ℂ i.castSucc) =
        finiteKrylovBasis energy weight i.castSucc := by
    simpa [U] using finiteKrylovUnitary_basis energy weight i.castSucc
  have hUis :
      U (EuclideanSpace.basisFun (Fin (n + 1)) ℂ i.succ) =
        finiteKrylovBasis energy weight i.succ := by
    simpa [U] using finiteKrylovUnitary_basis energy weight i.succ
  have htransport :
      U (((U.symm.toContinuousLinearEquiv.toContinuousLinearMap ∘L
          finiteIndexDiagonalHamiltonian energy ∘L
            U.toContinuousLinearEquiv.toContinuousLinearMap))
          (EuclideanSpace.basisFun (Fin (n + 1)) ℂ i.succ)) =
        finiteIndexDiagonalHamiltonian energy
          (U (EuclideanSpace.basisFun
            (Fin (n + 1)) ℂ i.succ)) := by
    simp
  rw [← U.inner_map_map]
  rw [htransport, hUi, hUis]
  intro hforward
  have hadj :=
    ContinuousLinearMap.adjoint_inner_right
      (finiteIndexDiagonalHamiltonian energy)
      (finiteKrylovBasis energy weight i.castSucc)
      (finiteKrylovBasis energy weight i.succ)
  rw [RHTower.finiteIndexDiagonalHamiltonian_selfAdjoint] at hadj
  have hreverse :
      inner ℂ (finiteKrylovBasis energy weight i.succ)
        (finiteIndexDiagonalHamiltonian energy
          (finiteKrylovBasis energy weight i.castSucc)) = 0 := by
    rw [← inner_conj_symm]
    rw [← hadj, hforward]
    simp
  exact
    (finiteKrylovBasis_forward_entry_ne_zero henergy hweight i)
      hreverse

theorem fixedProtocolHamiltonian_krylov_forwardConnected
    {T : ℝ} (hT : 0 < T) {n : ℕ}
    {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) :
    ForwardConnectedHamiltonian
      (fixedProtocolHamiltonian T n
        (finiteKrylovUnitary (angularEnergy T n)
          (interpolatedWeight n θ))) := by
  simpa [fixedProtocolHamiltonian] using!
    finiteKrylov_conjugate_forwardConnected
      (angularEnergy_injective hT n)
      (interpolatedWeight_pos n hθ0 hθ1)

/--
Exact connectedness phase law: every strict terminal probability has a
connected path representative, whereas every tridiagonal perfect-return
endpoint representative is disconnected.
-/
theorem endpoint_return_connectedness_dichotomy
    {T : ℝ} (hT : 0 < T) (q : ℕ) :
    (∀ p : ℝ, p ∈ Set.Ico (0 : ℝ) 1 →
      ∃ U : ClockSpace (endpointN q) ≃ₗᵢ[ℂ]
          ClockSpace (endpointN q),
        U (fixedClock (endpointN q)) =
            interpolatedClock (endpointN q) (Real.sqrt p) ∧
        NearestNeighborHamiltonian
          (fixedProtocolHamiltonian T (endpointN q) U) ∧
        ForwardConnectedHamiltonian
          (fixedProtocolHamiltonian T (endpointN q) U)) ∧
    (∀ U : ClockSpace (endpointN q) ≃ₗᵢ[ℂ]
        ClockSpace (endpointN q),
      U (fixedClock (endpointN q)) =
          parityClock (endpointN q) →
      NearestNeighborHamiltonian
          (fixedProtocolHamiltonian T (endpointN q) U) →
      ¬ ForwardConnectedHamiltonian
          (fixedProtocolHamiltonian T (endpointN q) U)) := by
  constructor
  · intro p hp
    have hn : 0 < endpointN q := by
      simp [endpointN]
    have hθ0 : 0 ≤ Real.sqrt p := Real.sqrt_nonneg p
    have hθ1 : Real.sqrt p < 1 := by
      rw [Real.sqrt_lt' zero_lt_one]
      simpa using hp.2
    let U : ClockSpace (endpointN q) ≃ₗᵢ[ℂ]
        ClockSpace (endpointN q) :=
      finiteKrylovUnitary (angularEnergy T (endpointN q))
        (interpolatedWeight (endpointN q) (Real.sqrt p))
    refine ⟨U, finiteKrylovUnitary_fixedClock
      hT hn hθ0 hθ1,
      fixedProtocolHamiltonian_krylov_nearestNeighbor
        hT hθ0 hθ1,
      fixedProtocolHamiltonian_krylov_forwardConnected
        hT hθ0 hθ1⟩
  · intro U hU hnn hconn
    obtain ⟨i, hi⟩ :=
      endpoint_paritySupport_forces_path_disconnection T q U hU hnn
    exact hconn i hi

end RHTower.ParityForecast
