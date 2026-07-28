import GaloisForLFunctions.RHTower.KrylovGramPrefixTransfer
import GaloisForLFunctions.RHTower.EndpointKrylovNearestNeighborRealization
import GaloisForLFunctions.HTGeometry.HilbertSchmidtMatrix

/-!
# Local-horizon quantum return law

Exact agreement of a finite nearest-neighbour Hamiltonian on an arbitrarily
large endpoint neighbourhood does not determine a later return probability.
The construction is isospectral, self-adjoint and has an exact
fixed-coordinate endpoint protocol.
-/

open scoped BigOperators InnerProductSpace
open Complex

noncomputable section

namespace RHTower.ParityForecast

/-- The active odd sector carries the entire parity spectral measure; the
even sector consists only of zero-weight spectators. -/
theorem endpointActive_weighted_sum_eq_parity
    (q : ℕ) (f : Fin (endpointN q + 1) → ℝ) :
    (∑ i : Fin (q + 1),
        endpointActiveWeight q i * f (endpointOddIndex q i)) =
      ∑ j : Fin (endpointN q + 1),
        parityWeight (endpointN q) j * f j := by
  have hsplit :
      (∑ s : Fin (q + 1) ⊕ Fin (q + 1),
          parityWeight (endpointN q) (endpointParityIndexEquiv q s) *
            f (endpointParityIndexEquiv q s)) =
        ∑ j : Fin (endpointN q + 1),
          parityWeight (endpointN q) j * f j := by
    exact Equiv.sum_comp (endpointParityIndexEquiv q)
      (fun j => parityWeight (endpointN q) j * f j)
  rw [Fintype.sum_sum_type] at hsplit
  have hleft :
      (∑ i : Fin (q + 1),
          parityWeight (endpointN q)
              (endpointParityIndexEquiv q (Sum.inl i)) *
            f (endpointParityIndexEquiv q (Sum.inl i))) =
        ∑ i : Fin (q + 1),
          endpointActiveWeight q i * f (endpointOddIndex q i) := by
    apply Finset.sum_congr rfl
    intro i _hi
    rfl
  have hright :
      (∑ i : Fin (q + 1),
          parityWeight (endpointN q)
              (endpointParityIndexEquiv q (Sum.inr i)) *
            f (endpointParityIndexEquiv q (Sum.inr i))) = 0 := by
    apply Finset.sum_eq_zero
    intro i _hi
    rw [endpointParityIndexEquiv_inr, endpointEvenWeight_zero, zero_mul]
  rw [hleft, hright, add_zero] at hsplit
  exact hsplit

/-- Canonical active-sector basis with the zero-weight levels retained as
spectators. -/
def endpointCanonicalProductBasis
    {T : ℝ} (hT : 0 < T) (q : ℕ) :
    OrthonormalBasis
      (Fin (q + 1) ⊕ Fin (q + 1)) ℂ
      (WithLp 2
        (FiniteIndexClockSpace (Fin (q + 1)) ×
          FiniteIndexClockSpace (Fin (q + 1)))) :=
  (canonicalKrylovBasis
      (endpointActiveEnergy T q) (endpointActiveWeight q)
      (endpointActiveEnergy_injective hT q)
      (endpointActiveWeight_pos q)).prod
    (EuclideanSpace.basisFun (Fin (q + 1)) ℂ)

def endpointCanonicalSpectralBasis
    {T : ℝ} (hT : 0 < T) (q : ℕ) :
    OrthonormalBasis
      (Fin (q + 1) ⊕ Fin (q + 1)) ℂ
      (ClockSpace (endpointN q)) :=
  (endpointCanonicalProductBasis hT q).map
    (endpointProductUnitary q)

def endpointCanonicalBlockBasis
    {T : ℝ} (hT : 0 < T) (q : ℕ) :
    OrthonormalBasis (Fin (endpointN q + 1)) ℂ
      (ClockSpace (endpointN q)) :=
  (endpointCanonicalSpectralBasis hT q).reindex
    (endpointBlockIndexEquiv q)

def endpointCanonicalKrylovUnitary
    {T : ℝ} (hT : 0 < T) (q : ℕ) :
    ClockSpace (endpointN q) ≃ₗᵢ[ℂ] ClockSpace (endpointN q) :=
  (EuclideanSpace.basisFun (Fin (endpointN q + 1)) ℂ).equiv
    (endpointCanonicalBlockBasis hT q) (Equiv.refl _)

@[simp] theorem endpointCanonicalKrylovUnitary_basis
    {T : ℝ} (hT : 0 < T) (q : ℕ)
    (i : Fin (endpointN q + 1)) :
    endpointCanonicalKrylovUnitary hT q
        (EuclideanSpace.basisFun (Fin (endpointN q + 1)) ℂ i) =
      endpointCanonicalBlockBasis hT q i := by
  exact OrthonormalBasis.equiv_apply_basis _ _ _ i

theorem endpointCanonicalBlockBasis_active
    {T : ℝ} (hT : 0 < T) (q : ℕ) (i : Fin (q + 1)) :
    endpointCanonicalBlockBasis hT q
        (endpointBlockIndexEquiv q (Sum.inl i)) =
      endpointProductUnitary q
        (WithLp.toLp 2
          (canonicalKrylovBasis
              (endpointActiveEnergy T q) (endpointActiveWeight q)
              (endpointActiveEnergy_injective hT q)
              (endpointActiveWeight_pos q) i,
            0)) := by
  rw [endpointCanonicalBlockBasis, OrthonormalBasis.reindex_apply,
    Equiv.symm_apply_apply, endpointCanonicalSpectralBasis,
    OrthonormalBasis.map_apply, endpointCanonicalProductBasis,
    OrthonormalBasis.prod_apply]
  rfl

theorem endpointCanonicalBlockBasis_spectator
    {T : ℝ} (hT : 0 < T) (q : ℕ) (i : Fin (q + 1)) :
    endpointCanonicalBlockBasis hT q
        (endpointBlockIndexEquiv q (Sum.inr i)) =
      endpointProductUnitary q
        (WithLp.toLp 2
          (0, EuclideanSpace.basisFun (Fin (q + 1)) ℂ i)) := by
  rw [endpointCanonicalBlockBasis, OrthonormalBasis.reindex_apply,
    Equiv.symm_apply_apply, endpointCanonicalSpectralBasis,
    OrthonormalBasis.map_apply, endpointCanonicalProductBasis,
    OrthonormalBasis.prod_apply]
  rfl

/-- Active-sector matrix entries are the canonical compression of the
positive endpoint measure. -/
theorem endpointCanonicalBlockBasis_active_matrix
    {T : ℝ} (hT : 0 < T) (q : ℕ)
    (i j : Fin (q + 1)) :
    inner ℂ
        (endpointCanonicalBlockBasis hT q
          (endpointBlockIndexEquiv q (Sum.inl i)))
        (finiteIndexDiagonalHamiltonian
          (angularEnergy T (endpointN q))
          (endpointCanonicalBlockBasis hT q
            (endpointBlockIndexEquiv q (Sum.inl j)))) =
      canonicalKrylovCompression
        (endpointActiveEnergy T q) (endpointActiveWeight q)
        (endpointActiveEnergy_injective hT q)
        (endpointActiveWeight_pos q) i j := by
  rw [endpointCanonicalBlockBasis_active,
    endpointCanonicalBlockBasis_active,
    endpointProductUnitary_intertwines_diagonal,
    endpointProductUnitary q |>.inner_map_map]
  simp only [WithLp.prod_inner_apply, inner_zero_left, add_zero]
  rw [canonicalKrylovBasis_apply, canonicalKrylovBasis_apply]
  rfl

theorem endpointCanonicalBlockBasis_cross_matrix
    {T : ℝ} (hT : 0 < T) (q : ℕ)
    (i j : Fin (q + 1)) :
    inner ℂ
        (endpointCanonicalBlockBasis hT q
          (endpointBlockIndexEquiv q (Sum.inl i)))
        (finiteIndexDiagonalHamiltonian
          (angularEnergy T (endpointN q))
          (endpointCanonicalBlockBasis hT q
            (endpointBlockIndexEquiv q (Sum.inr j)))) = 0 := by
  rw [endpointCanonicalBlockBasis_active,
    endpointCanonicalBlockBasis_spectator,
    endpointProductUnitary_intertwines_diagonal,
    endpointProductUnitary q |>.inner_map_map]
  simp [WithLp.prod_inner_apply]

theorem endpointCanonicalBlockBasis_cross_matrix'
    {T : ℝ} (hT : 0 < T) (q : ℕ)
    (i j : Fin (q + 1)) :
    inner ℂ
        (endpointCanonicalBlockBasis hT q
          (endpointBlockIndexEquiv q (Sum.inr i)))
        (finiteIndexDiagonalHamiltonian
          (angularEnergy T (endpointN q))
          (endpointCanonicalBlockBasis hT q
            (endpointBlockIndexEquiv q (Sum.inl j)))) = 0 := by
  rw [endpointCanonicalBlockBasis_spectator,
    endpointCanonicalBlockBasis_active,
    endpointProductUnitary_intertwines_diagonal,
    endpointProductUnitary q |>.inner_map_map]
  simp [WithLp.prod_inner_apply]

theorem endpointCanonicalBlockBasis_spectator_matrix
    {T : ℝ} (hT : 0 < T) (q : ℕ)
    (i j : Fin (q + 1)) (hij : i ≠ j) :
    inner ℂ
        (endpointCanonicalBlockBasis hT q
          (endpointBlockIndexEquiv q (Sum.inr i)))
        (finiteIndexDiagonalHamiltonian
          (angularEnergy T (endpointN q))
          (endpointCanonicalBlockBasis hT q
            (endpointBlockIndexEquiv q (Sum.inr j)))) = 0 := by
  rw [endpointCanonicalBlockBasis_spectator,
    endpointCanonicalBlockBasis_spectator,
    endpointProductUnitary_intertwines_diagonal,
    endpointProductUnitary q |>.inner_map_map]
  simp only [WithLp.prod_inner_apply, inner_zero_left, zero_add]
  have hdiag :
      finiteIndexDiagonalHamiltonian
          (endpointSpectatorEnergy T q)
          (EuclideanSpace.basisFun (Fin (q + 1)) ℂ j) =
        (endpointSpectatorEnergy T q j : ℂ) •
          EuclideanSpace.basisFun (Fin (q + 1)) ℂ j := by
    ext x
    by_cases hxj : x = j
    · subst x
      simp [finiteIndexDiagonalHamiltonian_apply,
        EuclideanSpace.basisFun_apply]
    · simp [finiteIndexDiagonalHamiltonian_apply,
        EuclideanSpace.basisFun_apply, hxj]
  rw [hdiag, inner_smul_right]
  have hinner :
      inner ℂ
          (EuclideanSpace.basisFun (Fin (q + 1)) ℂ i)
          (EuclideanSpace.basisFun (Fin (q + 1)) ℂ j) = 0 :=
    (EuclideanSpace.basisFun (Fin (q + 1)) ℂ).orthonormal.2 hij
  rw [hinner, mul_zero]

/-- The active canonical path followed by diagonal spectators is globally
nearest-neighbour. -/
theorem endpointCanonicalBlockBasis_nearestNeighbor
    {T : ℝ} (hT : 0 < T) (q : ℕ) :
    ∀ i j : Fin (endpointN q + 1),
      ((i : ℕ) + 1 < (j : ℕ) ∨
        (j : ℕ) + 1 < (i : ℕ)) →
      inner ℂ (endpointCanonicalBlockBasis hT q i)
        (finiteIndexDiagonalHamiltonian
          (angularEnergy T (endpointN q))
          (endpointCanonicalBlockBasis hT q j)) = 0 := by
  intro i j hij
  obtain ⟨si, rfl⟩ := (endpointBlockIndexEquiv q).surjective i
  obtain ⟨sj, rfl⟩ := (endpointBlockIndexEquiv q).surjective j
  cases si with
  | inl ai =>
      cases sj with
      | inl aj =>
          rw [endpointCanonicalBlockBasis_active_matrix]
          apply canonicalKrylovCompression_nearestNeighbor
          simpa using hij
      | inr aj =>
          exact endpointCanonicalBlockBasis_cross_matrix hT q ai aj
  | inr ai =>
      cases sj with
      | inl aj =>
          exact endpointCanonicalBlockBasis_cross_matrix' hT q ai aj
      | inr aj =>
          apply endpointCanonicalBlockBasis_spectator_matrix hT q ai aj
          intro haij
          subst aj
          simp at hij

/-- Closed-endpoint path Hamiltonian: canonical active Krylov block plus
diagonal spectators. -/
def endpointCanonicalPathHamiltonian
    {T : ℝ} (hT : 0 < T) (q : ℕ) :
    ClockSpace (endpointN q) →L[ℂ] ClockSpace (endpointN q) :=
  fixedProtocolHamiltonian T (endpointN q)
    (endpointCanonicalKrylovUnitary hT q)

theorem endpointCanonicalPathHamiltonian_nearestNeighbor
    {T : ℝ} (hT : 0 < T) (q : ℕ) :
    NearestNeighborHamiltonian
      (endpointCanonicalPathHamiltonian hT q) := by
  intro i j hij
  let U := endpointCanonicalKrylovUnitary hT q
  have hUi :
      U (EuclideanSpace.basisFun (Fin (endpointN q + 1)) ℂ i) =
        endpointCanonicalBlockBasis hT q i := by
    simpa [U] using endpointCanonicalKrylovUnitary_basis hT q i
  have hUj :
      U (EuclideanSpace.basisFun (Fin (endpointN q + 1)) ℂ j) =
        endpointCanonicalBlockBasis hT q j := by
    simpa [U] using endpointCanonicalKrylovUnitary_basis hT q j
  calc
    inner ℂ
        (EuclideanSpace.basisFun
          (Fin (endpointN q + 1)) ℂ i)
        (endpointCanonicalPathHamiltonian hT q
          (EuclideanSpace.basisFun
            (Fin (endpointN q + 1)) ℂ j)) =
      inner ℂ
        (U (EuclideanSpace.basisFun
          (Fin (endpointN q + 1)) ℂ i))
        (U (endpointCanonicalPathHamiltonian hT q
          (EuclideanSpace.basisFun
            (Fin (endpointN q + 1)) ℂ j))) := by
              symm
              exact U.inner_map_map _ _
    _ = inner ℂ (endpointCanonicalBlockBasis hT q i)
        (finiteIndexDiagonalHamiltonian
          (angularEnergy T (endpointN q))
          (endpointCanonicalBlockBasis hT q j)) := by
            rw [endpointCanonicalPathHamiltonian,
              fixedProtocolHamiltonian_intertwines,
              hUi, hUj, scaledClockHamiltonian]
    _ = 0 :=
      endpointCanonicalBlockBasis_nearestNeighbor hT q i j hij

/-- First-block entries of the closed-endpoint Hamiltonian are exactly the
active canonical compression. -/
theorem endpointCanonicalPathHamiltonian_active_entry
    {T : ℝ} (hT : 0 < T) (q : ℕ)
    (i j : Fin (q + 1)) :
    inner ℂ
        (EuclideanSpace.basisFun (Fin (endpointN q + 1)) ℂ
          (endpointBlockIndexEquiv q (Sum.inl i)))
        (endpointCanonicalPathHamiltonian hT q
          (EuclideanSpace.basisFun (Fin (endpointN q + 1)) ℂ
            (endpointBlockIndexEquiv q (Sum.inl j)))) =
      canonicalKrylovCompression
        (endpointActiveEnergy T q) (endpointActiveWeight q)
        (endpointActiveEnergy_injective hT q)
        (endpointActiveWeight_pos q) i j := by
  let U := endpointCanonicalKrylovUnitary hT q
  calc
    inner ℂ
        (EuclideanSpace.basisFun (Fin (endpointN q + 1)) ℂ
          (endpointBlockIndexEquiv q (Sum.inl i)))
        (endpointCanonicalPathHamiltonian hT q
          (EuclideanSpace.basisFun (Fin (endpointN q + 1)) ℂ
            (endpointBlockIndexEquiv q (Sum.inl j)))) =
      inner ℂ
        (U (EuclideanSpace.basisFun (Fin (endpointN q + 1)) ℂ
          (endpointBlockIndexEquiv q (Sum.inl i))))
        (U (endpointCanonicalPathHamiltonian hT q
          (EuclideanSpace.basisFun (Fin (endpointN q + 1)) ℂ
            (endpointBlockIndexEquiv q (Sum.inl j))))) := by
              symm
              exact U.inner_map_map _ _
    _ = inner ℂ
        (endpointCanonicalBlockBasis hT q
          (endpointBlockIndexEquiv q (Sum.inl i)))
        (finiteIndexDiagonalHamiltonian
          (angularEnergy T (endpointN q))
          (endpointCanonicalBlockBasis hT q
            (endpointBlockIndexEquiv q (Sum.inl j)))) := by
      rw [endpointCanonicalPathHamiltonian,
        fixedProtocolHamiltonian_intertwines,
        endpointCanonicalKrylovUnitary_basis,
        endpointCanonicalKrylovUnitary_basis,
        scaledClockHamiltonian]
    _ = _ :=
      endpointCanonicalBlockBasis_active_matrix hT q i j

/-- The endpoint canonical unitary maps the fixed endpoint to the parity
clock up to one global unit phase. -/
theorem exists_endpointCanonicalKrylovUnitary_zero_phase
    {T : ℝ} (hT : 0 < T) (q : ℕ) :
    ∃ c : ℂ, ‖c‖ = 1 ∧
      endpointCanonicalKrylovUnitary hT q
          (fixedClock (endpointN q)) =
        c • parityClock (endpointN q) := by
  obtain ⟨c, hc, hactive⟩ :=
    canonicalKrylovUnitary_zero_phase
      (endpointActiveEnergy T q) (endpointActiveWeight q)
      (endpointActiveEnergy_injective hT q)
      (endpointActiveWeight_pos q)
      (endpointActiveWeight_sum q)
  refine ⟨c, hc, ?_⟩
  rw [fixedClock, endpointCanonicalKrylovUnitary_basis]
  have hzero :
      (0 : Fin (endpointN q + 1)) =
        endpointBlockIndexEquiv q (Sum.inl 0) := by
    apply Fin.ext
    rfl
  rw [hzero, endpointCanonicalBlockBasis_active]
  have hactiveBasis :
      canonicalKrylovBasis
          (endpointActiveEnergy T q) (endpointActiveWeight q)
          (endpointActiveEnergy_injective hT q)
          (endpointActiveWeight_pos q) 0 =
        c • finiteIndexWeightKet (endpointActiveWeight q) := by
    rw [canonicalKrylovBasis_apply,
      ← canonicalKrylovUnitary_basis]
    exact hactive
  rw [hactiveBasis]
  calc
    endpointProductUnitary q
        (WithLp.toLp 2
          (c • finiteIndexWeightKet (endpointActiveWeight q), 0)) =
      c • endpointProductUnitary q
        (WithLp.toLp 2
          (finiteIndexWeightKet (endpointActiveWeight q), 0)) := by
      rw [← map_smul]
      congr 1
      apply WithLp.ofLp_injective
      simp
    _ = c • parityClock (endpointN q) := by
      rw [endpointProductUnitary_activeKet_eq_parityClock]

/-- Closed-endpoint spectral trajectory transported to the fixed path
coordinates. -/
def endpointCanonicalPathState
    {T : ℝ} (hT : 0 < T) (q : ℕ)
    (c : ℂ) (x : ClockSpace (endpointN q)) :
    ClockSpace (endpointN q) :=
  (endpointCanonicalKrylovUnitary hT q).symm (c • x)

def endpointCanonicalPathReturnProbability
    {T : ℝ} (hT : 0 < T) (q : ℕ)
    (c : ℂ) (x : ClockSpace (endpointN q)) : ℝ :=
  ‖inner ℂ (fixedClock (endpointN q))
      (endpointCanonicalPathState hT q c x)‖ ^ 2

theorem endpointCanonicalPathReturnProbability_eq
    {T : ℝ} (hT : 0 < T) (q : ℕ)
    (c : ℂ) (hc : ‖c‖ = 1)
    (x₀ x : ClockSpace (endpointN q))
    (hzero :
      endpointCanonicalKrylovUnitary hT q
          (fixedClock (endpointN q)) = c • x₀) :
    endpointCanonicalPathReturnProbability hT q c x =
      ‖inner ℂ x₀ x‖ ^ 2 := by
  let U := endpointCanonicalKrylovUnitary hT q
  have hcc : star c * c = 1 := by
    change (starRingEnd ℂ) c * c = 1
    rw [← Complex.normSq_eq_conj_mul_self,
      Complex.normSq_eq_norm_sq, hc]
    norm_num
  unfold endpointCanonicalPathReturnProbability
  have hamp :
      inner ℂ (fixedClock (endpointN q))
          (endpointCanonicalPathState hT q c x) =
        inner ℂ x₀ x := by
    calc
      inner ℂ (fixedClock (endpointN q))
          (endpointCanonicalPathState hT q c x) =
        inner ℂ (U (fixedClock (endpointN q))) (c • x) := by
          change
            inner ℂ (fixedClock (endpointN q)) (U.symm (c • x)) =
              inner ℂ (U (fixedClock (endpointN q))) (c • x)
          calc
            _ = inner ℂ (U (fixedClock (endpointN q)))
                (U (U.symm (c • x))) := by
                  symm
                  exact U.inner_map_map
                    (fixedClock (endpointN q)) (U.symm (c • x))
            _ = _ := by rw [U.apply_symm_apply]
      _ = inner ℂ (c • x₀) (c • x) := by rw [hzero]
      _ = inner ℂ x₀ x := by
        rw [inner_smul_left, inner_smul_right]
        calc
          star c * (c * inner ℂ x₀ x) =
              (star c * c) * inner ℂ x₀ x := by ring
          _ = inner ℂ x₀ x := by rw [hcc, one_mul]
  rw [hamp]

/-- The closed endpoint has an exact fixed-coordinate path realization of
the parity return record. -/
theorem exists_endpointCanonicalPathPhase
    {T : ℝ} (hT : 0 < T) (q : ℕ) :
    ∃ c : ℂ,
      ‖c‖ = 1 ∧
      endpointCanonicalKrylovUnitary hT q
          (fixedClock (endpointN q)) =
        c • parityClock (endpointN q) ∧
      ∀ t : ℝ,
        endpointCanonicalPathReturnProbability hT q c
            (scaledInterpolatedClockAt T (endpointN q) 1 t) =
          scaledInterpolatedProbability T (endpointN q) 1 t := by
  obtain ⟨c, hc, hzero⟩ :=
    exists_endpointCanonicalKrylovUnitary_zero_phase hT q
  refine ⟨c, hc, hzero, ?_⟩
  intro t
  rw [endpointCanonicalPathReturnProbability_eq
      hT q c hc (parityClock (endpointN q))
      (scaledInterpolatedClockAt T (endpointN q) 1 t) hzero]
  have hclock : interpolatedClock (endpointN q) 1 =
      parityClock (endpointN q) := interpolatedClock_one _
  rw [← hclock,
    scaledInterpolatedClock_survivalAmplitude
      hT (endpointN q) (by norm_num) (by norm_num)]
  rfl

/-- The rank-dropped closed endpoint is locally identical to the positive
baseline through any prescribed radius that fits inside its active block. -/
theorem endpointCanonicalPathHamiltonian_local_eq_full
    (R : ℕ) {T : ℝ} (hT : 0 < T) (q : ℕ)
    (hRq : R + 2 ≤ q + 1)
    (i j : Fin (R + 2))
    (hdegree : (i : ℕ) + (j : ℕ) + 1 ≤ 2 * R + 2) :
    inner ℂ
        (EuclideanSpace.basisFun (Fin (endpointN q + 1)) ℂ
          (Fin.castLE (by
            simp [endpointN]
            omega) i))
        (endpointCanonicalPathHamiltonian hT q
          (EuclideanSpace.basisFun (Fin (endpointN q + 1)) ℂ
            (Fin.castLE
              (by
                simp [endpointN]
                omega) j))) =
      inner ℂ
        (EuclideanSpace.basisFun (Fin (endpointN q + 1)) ℂ
          (Fin.castLE (by
            simp [endpointN]
            omega) i))
        (canonicalKrylovPathHamiltonian
          (angularEnergy T (endpointN q))
          (interpolatedWeight (endpointN q) 0)
          (angularEnergy_injective hT (endpointN q))
          (interpolatedWeight_pos (endpointN q)
            (by norm_num) (by norm_num))
          (EuclideanSpace.basisFun (Fin (endpointN q + 1)) ℂ
            (Fin.castLE
              (by
                simp [endpointN]
                omega) j))) := by
  let ia : Fin (q + 1) := Fin.castLE hRq i
  let ja : Fin (q + 1) := Fin.castLE hRq j
  have hsizeFull : R + 2 ≤ endpointN q + 1 := by
    simp [endpointN]
    omega
  have hidxi :
      endpointBlockIndexEquiv q (Sum.inl ia) =
        Fin.castLE hsizeFull i := by
    apply Fin.ext
    rfl
  have hidxj :
      endpointBlockIndexEquiv q (Sum.inl ja) =
        Fin.castLE hsizeFull j := by
    apply Fin.ext
    rfl
  rw [← hidxi, ← hidxj,
    endpointCanonicalPathHamiltonian_active_entry,
    canonicalKrylovPathHamiltonian_entry]
  apply canonicalKrylovCompression_local_eq_of_moments_cross_of_sizes
    (R := R) (r := q + 1) (s := endpointN q + 1)
    hRq hsizeFull
    (endpointActiveEnergy T q) (endpointActiveWeight q)
    (angularEnergy T (endpointN q))
    (interpolatedWeight (endpointN q) 0)
    (endpointActiveEnergy_injective hT q)
    (angularEnergy_injective hT (endpointN q))
    (endpointActiveWeight_pos q)
    (interpolatedWeight_pos (endpointN q)
      (by norm_num) (by norm_num))
    ?_ i j hdegree
  intro d hd
  calc
    (∑ x : Fin (q + 1),
        endpointActiveWeight q x *
          endpointActiveEnergy T q x ^ d) =
      ∑ x : Fin (endpointN q + 1),
        parityWeight (endpointN q) x *
          angularEnergy T (endpointN q) x ^ d := by
      simpa [endpointActiveEnergy] using
        endpointActive_weighted_sum_eq_parity q
          (fun x => angularEnergy T (endpointN q) x ^ d)
    _ = ∑ x : Fin (endpointN q + 1),
        fullWeight (endpointN q) x *
          angularEnergy T (endpointN q) x ^ d := by
      have hm :=
        angular_interpolated_energyMoment_eq_full
          (T := T) (n := endpointN q) (k := d)
          (by
            simp [endpointN]
            omega) 1
      simpa [interpolatedWeight] using hm
    _ = ∑ x : Fin (endpointN q + 1),
        interpolatedWeight (endpointN q) 0 x *
          angularEnergy T (endpointN q) x ^ d := by
      apply Finset.sum_congr rfl
      intro x _hx
      simp [interpolatedWeight]

/-- Every strict interpolated spectral packet has a canonical path phase for
which its endpoint return probability is exactly its spectral return
probability at every time. -/
theorem exists_canonicalInterpolatedPathPhase
    {T : ℝ} (hT : 0 < T) {n : ℕ} (hn : 0 < n)
    {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) :
    ∃ c : ℂ,
      ‖c‖ = 1 ∧
      canonicalKrylovUnitary
          (angularEnergy T n) (interpolatedWeight n θ)
          (angularEnergy_injective hT n)
          (interpolatedWeight_pos n hθ0 hθ1)
          (EuclideanSpace.basisFun (Fin (n + 1)) ℂ 0) =
        c • interpolatedClock n θ ∧
      ∀ t : ℝ,
        canonicalKrylovPathReturnProbability
            (angularEnergy T n) (interpolatedWeight n θ)
            (angularEnergy_injective hT n)
            (interpolatedWeight_pos n hθ0 hθ1)
            c (scaledInterpolatedClockAt T n θ t) =
          scaledInterpolatedProbability T n θ t := by
  obtain ⟨c, hc, hzero⟩ :=
    canonicalKrylovUnitary_zero_phase
      (angularEnergy T n) (interpolatedWeight n θ)
      (angularEnergy_injective hT n)
      (interpolatedWeight_pos n hθ0 hθ1)
      (interpolatedWeight_sum hn θ)
  refine ⟨c, hc, ?_, ?_⟩
  · simpa [interpolatedClock] using hzero
  · intro t
    rw [canonicalKrylovPathReturnProbability_eq
      (angularEnergy T n) (interpolatedWeight n θ)
      (angularEnergy_injective hT n)
      (interpolatedWeight_pos n hθ0 hθ1)
      c hc (interpolatedClock n θ)
      (scaledInterpolatedClockAt T n θ t)]
    · rw [scaledInterpolatedClock_survivalAmplitude
        hT n hθ0 hθ1.le]
      rfl
    · simpa [interpolatedClock] using hzero

/-- Fixed-endpoint realization of one interpolated spectral clock. -/
structure FixedEndpointPathModel
    (T : ℝ) (n : ℕ) (θ : ℝ) where
  unitary : ClockSpace n ≃ₗᵢ[ℂ] ClockSpace n
  phase : ℂ
  phase_norm : ‖phase‖ = 1
  prepares :
    unitary (fixedClock n) = phase • interpolatedClock n θ

def FixedEndpointPathModel.hamiltonian
    {T : ℝ} {n : ℕ} {θ : ℝ}
    (M : FixedEndpointPathModel T n θ) :
    ClockSpace n →L[ℂ] ClockSpace n :=
  fixedProtocolHamiltonian T n M.unitary

def FixedEndpointPathModel.stateAt
    {T : ℝ} {n : ℕ} {θ : ℝ}
    (M : FixedEndpointPathModel T n θ) (t : ℝ) :
    ClockSpace n :=
  M.unitary.symm
    (M.phase • scaledInterpolatedClockAt T n θ t)

def FixedEndpointPathModel.returnProbability
    {T : ℝ} {n : ℕ} {θ : ℝ}
    (M : FixedEndpointPathModel T n θ) (t : ℝ) : ℝ :=
  ‖inner ℂ (fixedClock n) (M.stateAt t)‖ ^ 2

theorem FixedEndpointPathModel.selfAdjoint
    {T : ℝ} {n : ℕ} {θ : ℝ}
    (M : FixedEndpointPathModel T n θ) :
    ContinuousLinearMap.adjoint M.hamiltonian = M.hamiltonian :=
  fixedProtocolHamiltonian_selfAdjoint T n M.unitary

theorem FixedEndpointPathModel.intertwines
    {T : ℝ} {n : ℕ} {θ : ℝ}
    (M : FixedEndpointPathModel T n θ) (x : ClockSpace n) :
    M.unitary (M.hamiltonian x) =
      scaledClockHamiltonian T n (M.unitary x) :=
  fixedProtocolHamiltonian_intertwines T n M.unitary x

/-- Every model's fixed-coordinate return probability is exactly the
corresponding spectral return probability. -/
theorem FixedEndpointPathModel.returnProbability_eq
    {T : ℝ} (hT : 0 < T) {n : ℕ}
    {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (M : FixedEndpointPathModel T n θ) (t : ℝ) :
    M.returnProbability t =
      scaledInterpolatedProbability T n θ t := by
  have hcc : star M.phase * M.phase = 1 := by
    change (starRingEnd ℂ) M.phase * M.phase = 1
    rw [← Complex.normSq_eq_conj_mul_self,
      Complex.normSq_eq_norm_sq, M.phase_norm]
    norm_num
  have hamp :
      inner ℂ (fixedClock n) (M.stateAt t) =
        inner ℂ (interpolatedClock n θ)
          (scaledInterpolatedClockAt T n θ t) := by
    calc
      inner ℂ (fixedClock n) (M.stateAt t) =
        inner ℂ (M.unitary (fixedClock n))
          (M.phase • scaledInterpolatedClockAt T n θ t) := by
        change
          inner ℂ (fixedClock n)
              (M.unitary.symm
                (M.phase • scaledInterpolatedClockAt T n θ t)) =
            inner ℂ (M.unitary (fixedClock n))
              (M.phase • scaledInterpolatedClockAt T n θ t)
        calc
          _ = inner ℂ (M.unitary (fixedClock n))
              (M.unitary
                (M.unitary.symm
                  (M.phase • scaledInterpolatedClockAt T n θ t))) := by
                symm
                exact M.unitary.inner_map_map
                  (fixedClock n)
                  (M.unitary.symm
                    (M.phase • scaledInterpolatedClockAt T n θ t))
          _ = _ := by rw [M.unitary.apply_symm_apply]
      _ = inner ℂ
          (M.phase • interpolatedClock n θ)
          (M.phase • scaledInterpolatedClockAt T n θ t) := by
            rw [M.prepares]
      _ = inner ℂ (interpolatedClock n θ)
          (scaledInterpolatedClockAt T n θ t) := by
        rw [inner_smul_left, inner_smul_right]
        calc
          star M.phase *
              (M.phase * inner ℂ (interpolatedClock n θ)
                (scaledInterpolatedClockAt T n θ t)) =
            (star M.phase * M.phase) *
              inner ℂ (interpolatedClock n θ)
                (scaledInterpolatedClockAt T n θ t) := by ring
          _ = _ := by rw [hcc, one_mul]
  rw [FixedEndpointPathModel.returnProbability, hamp,
    scaledInterpolatedClock_survivalAmplitude hT n hθ0 hθ1]
  rfl

/-- The canonical positive realization is exactly the fixed-protocol
Hamiltonian of its path model. -/
theorem canonicalKrylovPathHamiltonian_eq_fixedProtocol
    {T : ℝ} (hT : 0 < T) (n : ℕ) {θ : ℝ}
    (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) :
    canonicalKrylovPathHamiltonian
        (angularEnergy T n) (interpolatedWeight n θ)
        (angularEnergy_injective hT n)
        (interpolatedWeight_pos n hθ0 hθ1) =
      fixedProtocolHamiltonian T n
        (canonicalKrylovUnitary
          (angularEnergy T n) (interpolatedWeight n θ)
          (angularEnergy_injective hT n)
          (interpolatedWeight_pos n hθ0 hθ1)) := by
  rfl

/--
**Universal local-horizon return law, strict endpoint form.**

For every observation radius `R`, positive target time `T`, strict earlier
window `|t| ≤ H < T`, positive precision `δ`, and every exact terminal return
probability `p ∈ [0,1)`, there is one common finite dimension and an
isospectral family of self-adjoint nearest-neighbour Hamiltonians such that:

* all onsite terms through site `R` and all bonds through `R ↔ R+1` are
  exactly common;
* the whole earlier endpoint return record is `δ`-close to one baseline;
* the endpoint return probability at `T` is exactly `p`.

The same dimension and baseline work simultaneously for every `p < 1`.
-/
theorem localHorizon_every_strict_future_probability
    (R : ℕ) (T H : ℝ) (hT : 0 < T) (hH0 : 0 ≤ H)
    (hHT : H < T) {δ : ℝ} (hδ : 0 < δ) :
    ∃ n : ℕ,
      ∃ _hnOrder : 2 * R + 2 < n,
      ∃ hsize : R + 2 ≤ n + 1,
      ∃ c₀ : ℂ,
        ‖c₀‖ = 1 ∧
        canonicalKrylovUnitary
            (angularEnergy T n) (interpolatedWeight n 0)
            (angularEnergy_injective hT n)
            (interpolatedWeight_pos n (by norm_num) (by norm_num))
            (EuclideanSpace.basisFun (Fin (n + 1)) ℂ 0) =
          c₀ • interpolatedClock n 0 ∧
        (∀ t : ℝ,
          canonicalKrylovPathReturnProbability
              (angularEnergy T n) (interpolatedWeight n 0)
              (angularEnergy_injective hT n)
              (interpolatedWeight_pos n (by norm_num) (by norm_num))
              c₀ (scaledInterpolatedClockAt T n 0 t) =
            scaledInterpolatedProbability T n 0 t) ∧
        ∀ p : ℝ, p ∈ Set.Ico (0 : ℝ) 1 →
          ∃ hθ1 : Real.sqrt p < 1,
          ∃ c : ℂ,
            ‖c‖ = 1 ∧
            canonicalKrylovUnitary
                (angularEnergy T n)
                (interpolatedWeight n (Real.sqrt p))
                (angularEnergy_injective hT n)
                (interpolatedWeight_pos n
                  (Real.sqrt_nonneg p)
                  hθ1)
                (EuclideanSpace.basisFun (Fin (n + 1)) ℂ 0) =
              c • interpolatedClock n (Real.sqrt p) ∧
            NearestNeighborHamiltonian
              (canonicalKrylovPathHamiltonian
                (angularEnergy T n)
                (interpolatedWeight n (Real.sqrt p))
                (angularEnergy_injective hT n)
                (interpolatedWeight_pos n
                  (Real.sqrt_nonneg p)
                  hθ1)) ∧
            ContinuousLinearMap.adjoint
                (canonicalKrylovPathHamiltonian
                  (angularEnergy T n)
                  (interpolatedWeight n (Real.sqrt p))
                  (angularEnergy_injective hT n)
                  (interpolatedWeight_pos n
                    (Real.sqrt_nonneg p)
                    hθ1)) =
              canonicalKrylovPathHamiltonian
                (angularEnergy T n)
                (interpolatedWeight n (Real.sqrt p))
                (angularEnergy_injective hT n)
                (interpolatedWeight_pos n
                  (Real.sqrt_nonneg p)
                  hθ1) ∧
            (∀ i j : Fin (R + 2),
              (i : ℕ) + (j : ℕ) + 1 ≤ 2 * R + 2 →
              inner ℂ
                  (EuclideanSpace.basisFun (Fin (n + 1)) ℂ
                    (Fin.castLE hsize i))
                  (canonicalKrylovPathHamiltonian
                    (angularEnergy T n)
                    (interpolatedWeight n (Real.sqrt p))
                    (angularEnergy_injective hT n)
                    (interpolatedWeight_pos n
                      (Real.sqrt_nonneg p)
                      hθ1)
                    (EuclideanSpace.basisFun (Fin (n + 1)) ℂ
                      (Fin.castLE hsize j))) =
                inner ℂ
                  (EuclideanSpace.basisFun (Fin (n + 1)) ℂ
                    (Fin.castLE hsize i))
                  (canonicalKrylovPathHamiltonian
                    (angularEnergy T n)
                    (interpolatedWeight n 0)
                    (angularEnergy_injective hT n)
                    (interpolatedWeight_pos n
                      (by norm_num) (by norm_num))
                    (EuclideanSpace.basisFun (Fin (n + 1)) ℂ
                      (Fin.castLE hsize j)))) ∧
            (∀ t : ℝ, |t| ≤ H →
              |canonicalKrylovPathReturnProbability
                    (angularEnergy T n)
                    (interpolatedWeight n (Real.sqrt p))
                    (angularEnergy_injective hT n)
                    (interpolatedWeight_pos n
                      (Real.sqrt_nonneg p)
                      hθ1)
                    c (scaledInterpolatedClockAt
                      T n (Real.sqrt p) t) -
                canonicalKrylovPathReturnProbability
                    (angularEnergy T n)
                    (interpolatedWeight n 0)
                    (angularEnergy_injective hT n)
                    (interpolatedWeight_pos n
                      (by norm_num) (by norm_num))
                    c₀ (scaledInterpolatedClockAt T n 0 t)| < δ) ∧
            canonicalKrylovPathReturnProbability
                (angularEnergy T n)
                (interpolatedWeight n (Real.sqrt p))
                (angularEnergy_injective hT n)
                (interpolatedWeight_pos n
                  (Real.sqrt_nonneg p)
                  hθ1)
                c (scaledInterpolatedClockAt
                  T n (Real.sqrt p) T) = p := by
  obtain ⟨n, hnOrder, hall⟩ :=
    one_record_compatible_with_every_future_probability
      (2 * R + 2) T H hT hH0 hHT hδ
  have hn : 0 < n := by omega
  obtain ⟨c₀, hc₀, hzero₀, hprob₀⟩ :=
    exists_canonicalInterpolatedPathPhase
      hT hn (θ := 0) (by norm_num) (by norm_num)
  have hsize : R + 2 ≤ n + 1 := by omega
  refine ⟨n, hnOrder, hsize, c₀, hc₀, hzero₀, hprob₀, ?_⟩
  intro p hp
  have hθ0 : 0 ≤ Real.sqrt p := Real.sqrt_nonneg p
  have hθ1 : Real.sqrt p < 1 := by
    rw [Real.sqrt_lt' zero_lt_one]
    simpa using hp.2
  obtain ⟨c, hc, hzero, hprob⟩ :=
    exists_canonicalInterpolatedPathPhase hT hn hθ0 hθ1
  obtain ⟨_hmoment, hwindow, htarget⟩ :=
    hall p ⟨hp.1, hp.2.le⟩
  refine ⟨hθ1, c, hc, hzero,
    canonicalKrylovPathHamiltonian_nearestNeighbor
      (angularEnergy_injective hT n)
      (interpolatedWeight_pos n hθ0 hθ1),
    canonicalKrylovPathHamiltonian_selfAdjoint
      (angularEnergy T n) (interpolatedWeight n (Real.sqrt p))
      (angularEnergy_injective hT n)
      (interpolatedWeight_pos n hθ0 hθ1),
    ?_, ?_, ?_⟩
  · intro i j hdegree
    apply canonicalKrylovPathHamiltonian_local_eq_of_moments_of_size
      (R := R) (r := n + 1)
      (by omega : R + 2 ≤ n + 1)
      (angularEnergy T n)
      (interpolatedWeight n (Real.sqrt p))
      (interpolatedWeight n 0)
      (angularEnergy_injective hT n)
      (interpolatedWeight_pos n hθ0 hθ1)
      (interpolatedWeight_pos n (by norm_num) (by norm_num))
      ?_ i j hdegree
    intro d hd
    calc
      (∑ x : Fin (n + 1),
          interpolatedWeight n (Real.sqrt p) x *
            angularEnergy T n x ^ d) =
          ∑ x : Fin (n + 1),
            fullWeight n x * angularEnergy T n x ^ d :=
        angular_interpolated_energyMoment_eq_full
          (by omega) (Real.sqrt p)
      _ = ∑ x : Fin (n + 1),
          interpolatedWeight n 0 x *
            angularEnergy T n x ^ d :=
        (angular_interpolated_energyMoment_eq_full
          (by omega) 0).symm
  · intro t ht
    rw [hprob t, hprob₀ t]
    simpa [scaledInterpolatedProbability,
      interpolatedProbability, interpolatedAmplitude,
      interpolatedWeight] using hwindow t ht
  · rw [hprob T]
    exact htarget

/--
**Closed universal local-horizon return law.**

The strict law extends to every terminal probability in the closed interval
`[0,1]`.  The rank-dropped endpoint `p=1` is realized by its active canonical
chain plus diagonal spectators; no positivity assumption is applied at that
endpoint.
-/
theorem localHorizon_every_future_probability
    (R : ℕ) (T H : ℝ) (hT : 0 < T) (hH0 : 0 ≤ H)
    (hHT : H < T) {δ : ℝ} (hδ : 0 < δ) :
    ∃ q : ℕ,
      ∃ _horder : 2 * R + 2 < endpointN q,
      ∃ hsize : R + 2 ≤ endpointN q + 1,
      ∃ baseline :
          FixedEndpointPathModel T (endpointN q) 0,
        NearestNeighborHamiltonian baseline.hamiltonian ∧
        ContinuousLinearMap.adjoint baseline.hamiltonian =
          baseline.hamiltonian ∧
        ∀ p : ℝ, p ∈ Set.Icc (0 : ℝ) 1 →
          ∃ M :
              FixedEndpointPathModel
                T (endpointN q) (Real.sqrt p),
            NearestNeighborHamiltonian M.hamiltonian ∧
            ContinuousLinearMap.adjoint M.hamiltonian =
              M.hamiltonian ∧
            (∀ x : ClockSpace (endpointN q),
              M.unitary (M.hamiltonian x) =
                scaledClockHamiltonian T (endpointN q)
                  (M.unitary x)) ∧
            (∀ i j : Fin (R + 2),
              (i : ℕ) + (j : ℕ) + 1 ≤ 2 * R + 2 →
              inner ℂ
                  (EuclideanSpace.basisFun
                    (Fin (endpointN q + 1)) ℂ
                    (Fin.castLE hsize i))
                  (M.hamiltonian
                    (EuclideanSpace.basisFun
                      (Fin (endpointN q + 1)) ℂ
                      (Fin.castLE hsize j))) =
                inner ℂ
                  (EuclideanSpace.basisFun
                    (Fin (endpointN q + 1)) ℂ
                    (Fin.castLE hsize i))
                  (baseline.hamiltonian
                    (EuclideanSpace.basisFun
                      (Fin (endpointN q + 1)) ℂ
                      (Fin.castLE hsize j)))) ∧
            (∀ t : ℝ, |t| ≤ H →
              |M.returnProbability t -
                baseline.returnProbability t| < δ) ∧
            M.returnProbability T = p := by
  obtain ⟨q, horder, hall⟩ :=
    one_endpointN_record_compatible_with_every_future_probability
      (2 * R + 2) T H hT hH0 hHT hδ
  have hn : 0 < endpointN q := by simp [endpointN]
  have hsize : R + 2 ≤ endpointN q + 1 := by omega
  obtain ⟨c₀, hc₀, hzero₀, _hprob₀⟩ :=
    exists_canonicalInterpolatedPathPhase
      hT hn (θ := 0) (by norm_num) (by norm_num)
  let baseline :
      FixedEndpointPathModel T (endpointN q) 0 :=
    { unitary :=
        canonicalKrylovUnitary
          (angularEnergy T (endpointN q))
          (interpolatedWeight (endpointN q) 0)
          (angularEnergy_injective hT (endpointN q))
          (interpolatedWeight_pos (endpointN q)
            (by norm_num) (by norm_num))
      phase := c₀
      phase_norm := hc₀
      prepares := hzero₀ }
  have hbaselineHamiltonian :
      baseline.hamiltonian =
        canonicalKrylovPathHamiltonian
          (angularEnergy T (endpointN q))
          (interpolatedWeight (endpointN q) 0)
          (angularEnergy_injective hT (endpointN q))
          (interpolatedWeight_pos (endpointN q)
            (by norm_num) (by norm_num)) := by
    exact (canonicalKrylovPathHamiltonian_eq_fixedProtocol
      hT (endpointN q) (θ := 0)
      (by norm_num) (by norm_num)).symm
  have hbaselineNN :
      NearestNeighborHamiltonian baseline.hamiltonian := by
    rw [hbaselineHamiltonian]
    exact canonicalKrylovPathHamiltonian_nearestNeighbor
      (angularEnergy_injective hT (endpointN q))
      (interpolatedWeight_pos (endpointN q)
        (by norm_num) (by norm_num))
  refine ⟨q, horder, hsize, baseline, hbaselineNN,
    baseline.selfAdjoint, ?_⟩
  intro p hp
  obtain ⟨_hmoment, hwindow, htarget⟩ := hall p hp
  have hθ0 : 0 ≤ Real.sqrt p := Real.sqrt_nonneg p
  have hθle : Real.sqrt p ≤ 1 := Real.sqrt_le_one.mpr hp.2
  by_cases hp1 : p = 1
  · subst p
    obtain ⟨c, hc, hzero, _hprob⟩ :=
      exists_endpointCanonicalPathPhase hT q
    let M :
        FixedEndpointPathModel
          T (endpointN q) (Real.sqrt 1) :=
      { unitary := endpointCanonicalKrylovUnitary hT q
        phase := c
        phase_norm := hc
        prepares := by
          simpa [interpolatedClock_one] using hzero }
    have hMHamiltonian :
        M.hamiltonian = endpointCanonicalPathHamiltonian hT q := by
      rfl
    have hRq : R + 2 ≤ q + 1 := by
      simp [endpointN] at horder
      omega
    refine ⟨M, ?_, M.selfAdjoint, M.intertwines, ?_, ?_, ?_⟩
    · rw [hMHamiltonian]
      exact endpointCanonicalPathHamiltonian_nearestNeighbor hT q
    · intro i j hdegree
      rw [hMHamiltonian, hbaselineHamiltonian]
      exact endpointCanonicalPathHamiltonian_local_eq_full
        R hT q hRq i j hdegree
    · intro t ht
      rw [M.returnProbability_eq hT
          (Real.sqrt_nonneg 1) (Real.sqrt_le_one.mpr (by norm_num)),
        baseline.returnProbability_eq hT (by norm_num) (by norm_num)]
      simpa [scaledInterpolatedProbability,
        interpolatedProbability, interpolatedAmplitude,
        interpolatedWeight] using hwindow t ht
    · rw [M.returnProbability_eq hT
        (Real.sqrt_nonneg 1) (Real.sqrt_le_one.mpr (by norm_num))]
      exact htarget
  · have hp_lt : p < 1 := lt_of_le_of_ne hp.2 hp1
    have hθlt : Real.sqrt p < 1 := by
      rw [Real.sqrt_lt' zero_lt_one]
      simpa using hp_lt
    obtain ⟨c, hc, hzero, _hprob⟩ :=
      exists_canonicalInterpolatedPathPhase hT hn hθ0 hθlt
    let M :
        FixedEndpointPathModel
          T (endpointN q) (Real.sqrt p) :=
      { unitary :=
          canonicalKrylovUnitary
            (angularEnergy T (endpointN q))
            (interpolatedWeight (endpointN q) (Real.sqrt p))
            (angularEnergy_injective hT (endpointN q))
            (interpolatedWeight_pos (endpointN q) hθ0 hθlt)
        phase := c
        phase_norm := hc
        prepares := hzero }
    have hMHamiltonian :
        M.hamiltonian =
          canonicalKrylovPathHamiltonian
            (angularEnergy T (endpointN q))
            (interpolatedWeight (endpointN q) (Real.sqrt p))
            (angularEnergy_injective hT (endpointN q))
            (interpolatedWeight_pos (endpointN q)
              hθ0 hθlt) := by
      exact (canonicalKrylovPathHamiltonian_eq_fixedProtocol
        hT (endpointN q) hθ0 hθlt).symm
    refine ⟨M, ?_, M.selfAdjoint, M.intertwines, ?_, ?_, ?_⟩
    · rw [hMHamiltonian]
      exact canonicalKrylovPathHamiltonian_nearestNeighbor
        (angularEnergy_injective hT (endpointN q))
        (interpolatedWeight_pos (endpointN q) hθ0 hθlt)
    · intro i j hdegree
      rw [hMHamiltonian, hbaselineHamiltonian]
      apply canonicalKrylovPathHamiltonian_local_eq_of_moments_of_size
        (R := R) (r := endpointN q + 1) hsize
        (angularEnergy T (endpointN q))
        (interpolatedWeight (endpointN q) (Real.sqrt p))
        (interpolatedWeight (endpointN q) 0)
        (angularEnergy_injective hT (endpointN q))
        (interpolatedWeight_pos (endpointN q) hθ0 hθlt)
        (interpolatedWeight_pos (endpointN q)
          (by norm_num) (by norm_num))
        ?_ i j hdegree
      intro d hd
      calc
        (∑ x : Fin (endpointN q + 1),
            interpolatedWeight (endpointN q) (Real.sqrt p) x *
              angularEnergy T (endpointN q) x ^ d) =
          ∑ x : Fin (endpointN q + 1),
            fullWeight (endpointN q) x *
              angularEnergy T (endpointN q) x ^ d :=
            angular_interpolated_energyMoment_eq_full
              (by omega) (Real.sqrt p)
        _ = ∑ x : Fin (endpointN q + 1),
            interpolatedWeight (endpointN q) 0 x *
              angularEnergy T (endpointN q) x ^ d :=
          (angular_interpolated_energyMoment_eq_full
            (by omega) 0).symm
    · intro t ht
      rw [M.returnProbability_eq hT hθ0 hθle,
        baseline.returnProbability_eq hT (by norm_num) (by norm_num)]
      simpa [scaledInterpolatedProbability,
        interpolatedProbability, interpolatedAmplitude,
        interpolatedWeight] using hwindow t ht
    · rw [M.returnProbability_eq hT hθ0 hθle]
      exact htarget

/-- Canonical vanishing tolerance for the cofinal local-horizon sequence. -/
def cofinalLocalTolerance (R : ℕ) : ℝ :=
  1 / ((R : ℝ) + 1)

theorem cofinalLocalTolerance_pos (R : ℕ) :
    0 < cofinalLocalTolerance R := by
  unfold cofinalLocalTolerance
  positivity

theorem cofinalLocalTolerance_tendsto_zero :
    Filter.Tendsto cofinalLocalTolerance Filter.atTop (nhds 0) := by
  simpa only [cofinalLocalTolerance] using
    (tendsto_one_div_add_atTop_nhds_zero_nat :
      Filter.Tendsto (fun R : ℕ => 1 / ((R : ℝ) + 1))
        Filter.atTop (nhds 0))

/-- One stage of the cofinal thermodynamic local-horizon construction. -/
structure CofinalLocalHorizonWitness
    (R : ℕ) (T H p : ℝ) where
  q : ℕ
  horder : 2 * R + 2 < endpointN q
  hsize : R + 2 ≤ endpointN q + 1
  baseline : FixedEndpointPathModel T (endpointN q) 0
  model :
    FixedEndpointPathModel T (endpointN q) (Real.sqrt p)
  baseline_nearestNeighbor :
    NearestNeighborHamiltonian baseline.hamiltonian
  model_nearestNeighbor :
    NearestNeighborHamiltonian model.hamiltonian
  local_eq :
    ∀ i j : Fin (R + 2),
      (i : ℕ) + (j : ℕ) + 1 ≤ 2 * R + 2 →
      inner ℂ
          (EuclideanSpace.basisFun
            (Fin (endpointN q + 1)) ℂ (Fin.castLE hsize i))
          (model.hamiltonian
            (EuclideanSpace.basisFun
              (Fin (endpointN q + 1)) ℂ
              (Fin.castLE hsize j))) =
        inner ℂ
          (EuclideanSpace.basisFun
            (Fin (endpointN q + 1)) ℂ (Fin.castLE hsize i))
          (baseline.hamiltonian
            (EuclideanSpace.basisFun
              (Fin (endpointN q + 1)) ℂ
              (Fin.castLE hsize j)))
  window :
    ∀ t : ℝ, |t| ≤ H →
      |model.returnProbability t -
        baseline.returnProbability t| < cofinalLocalTolerance R
  baseline_target :
    baseline.returnProbability T = 0
  model_target :
    model.returnProbability T = p

theorem nonempty_cofinalLocalHorizonWitness
    (R : ℕ) (p : ℝ) (hp : p ∈ Set.Icc (0 : ℝ) 1)
    (T H : ℝ) (hT : 0 < T) (hH0 : 0 ≤ H) (hHT : H < T) :
    Nonempty (CofinalLocalHorizonWitness R T H p) := by
  obtain ⟨q, horder, hsize, baseline, hbaselineNN,
      _hbaselineSA, hall⟩ :=
    localHorizon_every_future_probability
      R T H hT hH0 hHT (cofinalLocalTolerance_pos R)
  obtain ⟨model, hmodelNN, _hmodelSA, _hintertwines,
      hlocal, hwindow, htarget⟩ := hall p hp
  have hn : 0 < endpointN q := by omega
  have hbaselineTarget :
      baseline.returnProbability T = 0 := by
    rw [baseline.returnProbability_eq hT
      (by norm_num) (by norm_num),
      scaledInterpolatedProbability_target hT hn (by norm_num)]
    norm_num
  exact ⟨
    { q := q
      horder := horder
      hsize := hsize
      baseline := baseline
      model := model
      baseline_nearestNeighbor := hbaselineNN
      model_nearestNeighbor := hmodelNN
      local_eq := hlocal
      window := hwindow
      baseline_target := hbaselineTarget
      model_target := htarget }⟩

/--
**Cofinal thermodynamic local-horizon law.**

For every fixed `p ∈ [0,1]`, a sequence of finite isospectral
nearest-neighbour models exists whose exactly common local radius tends to
infinity and whose entire strict earlier return record converges pointwise to
the baseline record, while the target-time probability gap remains exactly
`p` at every stage.
-/
theorem exists_cofinalLocalHorizonSequence
    (p : ℝ) (hp : p ∈ Set.Icc (0 : ℝ) 1)
    (T H : ℝ) (hT : 0 < T) (hH0 : 0 ≤ H) (hHT : H < T) :
    ∃ W : ∀ R : ℕ, CofinalLocalHorizonWitness R T H p,
      (∀ t : ℝ, |t| ≤ H →
        Filter.Tendsto
          (fun R =>
            |(W R).model.returnProbability t -
              (W R).baseline.returnProbability t|)
          Filter.atTop (nhds 0)) ∧
      (∀ R : ℕ,
        |(W R).model.returnProbability T -
          (W R).baseline.returnProbability T| = p) := by
  let W : ∀ R : ℕ, CofinalLocalHorizonWitness R T H p :=
    fun R => Classical.choice
      (nonempty_cofinalLocalHorizonWitness
        R p hp T H hT hH0 hHT)
  refine ⟨W, ?_, ?_⟩
  · intro t ht
    apply squeeze_zero'
    · exact Filter.Eventually.of_forall fun R => abs_nonneg _
    · exact Filter.Eventually.of_forall fun R =>
        ((W R).window t ht).le
    · exact cofinalLocalTolerance_tendsto_zero
  · intro R
    rw [(W R).model_target, (W R).baseline_target, sub_zero,
      abs_of_nonneg hp.1]

/--
**Global-identity boundary on `ℓ²(ℕ)`.**

Two bounded operators with every canonical matrix entry equal are the same
operator.  Thus the cofinal law cannot be strengthened to two distinct fixed
infinite Hamiltonians that agree exactly at every finite site; its
noncommuting large-radius/target-time limit is essential.
-/
theorem infiniteBoundedOperator_eq_of_all_matrixEntries_eq
    (A B :
      lp (fun _ : ℕ => ℂ) 2 →L[ℂ]
        lp (fun _ : ℕ => ℂ) 2)
    (hentry : ∀ i j : ℕ,
      A (lp.single 2 j (1 : ℂ)) i =
        B (lp.single 2 j (1 : ℂ)) i) :
    A = B := by
  apply ContinuousLinearMap.ext_on
    (Submodule.dense_iff_topologicalClosure_eq_top.mpr
      (HilbertSchmidt.lpBasis ℕ).dense_span)
  rintro x ⟨j, rfl⟩
  rw [HilbertSchmidt.lpBasis_apply]
  apply lp.ext
  funext i
  exact hentry i j

theorem infiniteGlobalAgreement_forces_same_iterates
    (A B :
      lp (fun _ : ℕ => ℂ) 2 →L[ℂ]
        lp (fun _ : ℕ => ℂ) 2)
    (hentry : ∀ i j : ℕ,
      A (lp.single 2 j (1 : ℂ)) i =
        B (lp.single 2 j (1 : ℂ)) i)
    (m : ℕ) (x : lp (fun _ : ℕ => ℂ) 2) :
    (A ^ m) x = (B ^ m) x := by
  rw [infiniteBoundedOperator_eq_of_all_matrixEntries_eq A B hentry]

end RHTower.ParityForecast
