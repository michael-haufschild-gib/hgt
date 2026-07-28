import GaloisForLFunctions.RHTower.KrylovNearestNeighborRealization
import Mathlib.Analysis.InnerProductSpace.ProdL2

/-! # Closed-endpoint Krylov nearest-neighbour realization -/

open scoped BigOperators InnerProductSpace
open Complex

noncomputable section

namespace RHTower.ParityForecast

def paritySplitIndex (r : ℕ) : Fin r ⊕ Fin r → Fin (2 * r)
  | Sum.inl i => ⟨2 * (i : ℕ) + 1, by omega⟩
  | Sum.inr i => ⟨2 * (i : ℕ), by omega⟩

theorem paritySplitIndex_bijective (r : ℕ) :
    Function.Bijective (paritySplitIndex r) := by
  constructor
  · intro x y hxy
    cases x with
    | inl i =>
        cases y with
        | inl j =>
            congr
            apply Fin.ext
            simp only [paritySplitIndex, Fin.mk.injEq] at hxy
            omega
        | inr j =>
            change (⟨2 * (i : ℕ) + 1, by omega⟩ : Fin (2 * r)) =
              ⟨2 * (j : ℕ), by omega⟩ at hxy
            have := Fin.mk.inj hxy
            omega
    | inr i =>
        cases y with
        | inl j =>
            change (⟨2 * (i : ℕ), by omega⟩ : Fin (2 * r)) =
              ⟨2 * (j : ℕ) + 1, by omega⟩ at hxy
            have := Fin.mk.inj hxy
            omega
        | inr j =>
            congr
            apply Fin.ext
            simp only [paritySplitIndex, Fin.mk.injEq] at hxy
            omega
  · intro j
    rcases Nat.mod_two_eq_zero_or_one (j : ℕ) with hj | hj
    · have heven : Even (j : ℕ) := Nat.even_iff.mpr hj
      have hrepr : 2 * ((j : ℕ) / 2) = (j : ℕ) :=
        Nat.two_mul_div_two_of_even heven
      have hlt : (j : ℕ) / 2 < r := by omega
      refine ⟨Sum.inr ⟨(j : ℕ) / 2, hlt⟩, ?_⟩
      apply Fin.ext
      exact hrepr
    · have hrepr : 2 * ((j : ℕ) / 2) + 1 = (j : ℕ) := by
        have hdiv := Nat.mod_add_div (j : ℕ) 2
        omega
      have hlt : (j : ℕ) / 2 < r := by omega
      refine ⟨Sum.inl ⟨(j : ℕ) / 2, hlt⟩, ?_⟩
      apply Fin.ext
      exact hrepr

def paritySplitEquiv (r : ℕ) : Fin r ⊕ Fin r ≃ Fin (2 * r) :=
  Equiv.ofBijective (paritySplitIndex r) (paritySplitIndex_bijective r)

@[simp] theorem paritySplitEquiv_inl (r : ℕ) (i : Fin r) :
    paritySplitEquiv r (Sum.inl i) =
      ⟨2 * (i : ℕ) + 1, by omega⟩ := rfl

@[simp] theorem paritySplitEquiv_inr (r : ℕ) (i : Fin r) :
    paritySplitEquiv r (Sum.inr i) =
      ⟨2 * (i : ℕ), by omega⟩ := rfl

def parityProductUnitary (r : ℕ) :
    WithLp 2
        (FiniteIndexClockSpace (Fin r) ×
          FiniteIndexClockSpace (Fin r)) ≃ₗᵢ[ℂ]
      FiniteIndexClockSpace (Fin (2 * r)) :=
  (PiLp.sumPiLpEquivProdLpPiLp 2
      (fun _ : Fin r ⊕ Fin r => ℂ)).symm.trans
    (LinearIsometryEquiv.piLpCongrLeft
      2 ℂ ℂ (paritySplitEquiv r))

def endpointN (q : ℕ) : ℕ := 2 * q + 1

def endpointOddIndex (q : ℕ) (i : Fin (q + 1)) :
    Fin (endpointN q + 1) :=
  ⟨2 * (i : ℕ) + 1, by simp [endpointN]; omega⟩

def endpointEvenIndex (q : ℕ) (i : Fin (q + 1)) :
    Fin (endpointN q + 1) :=
  ⟨2 * (i : ℕ), by simp [endpointN]; omega⟩

def endpointActiveEnergy (T : ℝ) (q : ℕ) (i : Fin (q + 1)) : ℝ :=
  angularEnergy T (endpointN q) (endpointOddIndex q i)

def endpointActiveWeight (q : ℕ) (i : Fin (q + 1)) : ℝ :=
  parityWeight (endpointN q) (endpointOddIndex q i)

def endpointSpectatorEnergy (T : ℝ) (q : ℕ) (i : Fin (q + 1)) : ℝ :=
  angularEnergy T (endpointN q) (endpointEvenIndex q i)

theorem endpointActiveWeight_pos (q : ℕ) (i : Fin (q + 1)) :
    0 < endpointActiveWeight q i := by
  have hsub :
      endpointN q - (endpointOddIndex q i : ℕ) =
        2 * (q - (i : ℕ)) := by
    simp [endpointN, endpointOddIndex]
    omega
  have heven :
      Even (endpointN q - (endpointOddIndex q i : ℕ)) := by
    rw [hsub]
    exact ⟨q - (i : ℕ), by omega⟩
  rw [endpointActiveWeight, parityWeight, heven.neg_one_pow]
  norm_num
  exact fullWeight_pos (endpointN q) (endpointOddIndex q i)

theorem endpointEvenWeight_zero (q : ℕ) (i : Fin (q + 1)) :
    parityWeight (endpointN q) (endpointEvenIndex q i) = 0 := by
  have hsub :
      endpointN q - (endpointEvenIndex q i : ℕ) =
        2 * (q - (i : ℕ)) + 1 := by
    simp [endpointN, endpointEvenIndex]
    omega
  have hodd :
      Odd (endpointN q - (endpointEvenIndex q i : ℕ)) := by
    rw [hsub]
    exact ⟨q - (i : ℕ), by omega⟩
  rw [parityWeight, hodd.neg_one_pow]
  ring

theorem endpointActiveWeight_sum (q : ℕ) :
    ∑ i : Fin (q + 1), endpointActiveWeight q i = 1 := by
  have hsplit :
      (∑ x : Fin (q + 1) ⊕ Fin (q + 1),
          parityWeight (endpointN q)
            ((paritySplitEquiv (q + 1)).trans
              (finCongr (by simp [endpointN]; omega)) x)) =
        ∑ j : Fin (endpointN q + 1),
          parityWeight (endpointN q) j := by
    exact Equiv.sum_comp
      ((paritySplitEquiv (q + 1)).trans
        (finCongr (by simp [endpointN]; omega)))
      (parityWeight (endpointN q))
  rw [Fintype.sum_sum_type] at hsplit
  have hleft :
      (∑ i : Fin (q + 1),
          parityWeight (endpointN q)
            ((paritySplitEquiv (q + 1)).trans
              (finCongr (by simp [endpointN]; omega)) (Sum.inl i))) =
        ∑ i : Fin (q + 1), endpointActiveWeight q i := by
    apply Finset.sum_congr rfl
    intro i _hi
    rfl
  have hright :
      (∑ i : Fin (q + 1),
          parityWeight (endpointN q)
            ((paritySplitEquiv (q + 1)).trans
              (finCongr (by simp [endpointN]; omega)) (Sum.inr i))) = 0 := by
    apply Finset.sum_eq_zero
    intro i _hi
    exact endpointEvenWeight_zero q i
  rw [hleft, hright, add_zero, parityWeight_sum (by simp [endpointN])] at hsplit
  exact hsplit

theorem endpointActiveEnergy_injective {T : ℝ} (hT : 0 < T) (q : ℕ) :
    Function.Injective (endpointActiveEnergy T q) := by
  intro i j hij
  apply Fin.ext
  have hangular := angularEnergy_injective hT (endpointN q) hij
  simpa [endpointOddIndex] using congrArg Fin.val hangular

@[simp] theorem parityProductUnitary_apply_inl
    (r : ℕ) (x y : FiniteIndexClockSpace (Fin r)) (i : Fin r) :
    parityProductUnitary r (WithLp.toLp 2 (x, y))
        (paritySplitEquiv r (Sum.inl i)) = x i := by
  change
    ((LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
      (paritySplitEquiv r))
      ((PiLp.sumPiLpEquivProdLpPiLp 2
        (fun _ : Fin r ⊕ Fin r => ℂ)).symm
          (WithLp.toLp 2 (x, y))))
        (paritySplitEquiv r (Sum.inl i)) = x i
  rw [LinearIsometryEquiv.piLpCongrLeft_apply,
    Equiv.piCongrLeft'_apply, Equiv.symm_apply_apply]
  rfl

@[simp] theorem parityProductUnitary_apply_inr
    (r : ℕ) (x y : FiniteIndexClockSpace (Fin r)) (i : Fin r) :
    parityProductUnitary r (WithLp.toLp 2 (x, y))
        (paritySplitEquiv r (Sum.inr i)) = y i := by
  change
    ((LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
      (paritySplitEquiv r))
      ((PiLp.sumPiLpEquivProdLpPiLp 2
        (fun _ : Fin r ⊕ Fin r => ℂ)).symm
          (WithLp.toLp 2 (x, y))))
        (paritySplitEquiv r (Sum.inr i)) = y i
  rw [LinearIsometryEquiv.piLpCongrLeft_apply,
    Equiv.piCongrLeft'_apply, Equiv.symm_apply_apply]
  rfl

def endpointDimensionEquiv (q : ℕ) :
    Fin (2 * (q + 1)) ≃ Fin (endpointN q + 1) :=
  finCongr (by simp [endpointN]; omega)

def endpointProductUnitary (q : ℕ) :
    WithLp 2
        (FiniteIndexClockSpace (Fin (q + 1)) ×
          FiniteIndexClockSpace (Fin (q + 1))) ≃ₗᵢ[ℂ]
      ClockSpace (endpointN q) :=
  (parityProductUnitary (q + 1)).trans
    (LinearIsometryEquiv.piLpCongrLeft
      2 ℂ ℂ (endpointDimensionEquiv q))

def endpointParityIndexEquiv (q : ℕ) :
    Fin (q + 1) ⊕ Fin (q + 1) ≃ Fin (endpointN q + 1) :=
  (paritySplitEquiv (q + 1)).trans (endpointDimensionEquiv q)

@[simp] theorem endpointParityIndexEquiv_inl
    (q : ℕ) (i : Fin (q + 1)) :
    endpointParityIndexEquiv q (Sum.inl i) =
      endpointOddIndex q i := rfl

@[simp] theorem endpointParityIndexEquiv_inr
    (q : ℕ) (i : Fin (q + 1)) :
    endpointParityIndexEquiv q (Sum.inr i) =
      endpointEvenIndex q i := rfl

@[simp] theorem endpointProductUnitary_apply_inl
    (q : ℕ)
    (x y : FiniteIndexClockSpace (Fin (q + 1)))
    (i : Fin (q + 1)) :
    endpointProductUnitary q (WithLp.toLp 2 (x, y))
        (endpointOddIndex q i) = x i := by
  change
    ((LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
      (endpointDimensionEquiv q))
      (parityProductUnitary (q + 1)
        (WithLp.toLp 2 (x, y))))
        (endpointOddIndex q i) = x i
  rw [LinearIsometryEquiv.piLpCongrLeft_apply,
    Equiv.piCongrLeft'_apply]
  have hindex :
      (endpointDimensionEquiv q).symm (endpointOddIndex q i) =
        paritySplitEquiv (q + 1) (Sum.inl i) := by
    apply Fin.ext
    rfl
  rw [hindex, parityProductUnitary_apply_inl]

@[simp] theorem endpointProductUnitary_apply_inr
    (q : ℕ)
    (x y : FiniteIndexClockSpace (Fin (q + 1)))
    (i : Fin (q + 1)) :
    endpointProductUnitary q (WithLp.toLp 2 (x, y))
        (endpointEvenIndex q i) = y i := by
  change
    ((LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
      (endpointDimensionEquiv q))
      (parityProductUnitary (q + 1)
        (WithLp.toLp 2 (x, y))))
        (endpointEvenIndex q i) = y i
  rw [LinearIsometryEquiv.piLpCongrLeft_apply,
    Equiv.piCongrLeft'_apply]
  have hindex :
      (endpointDimensionEquiv q).symm (endpointEvenIndex q i) =
        paritySplitEquiv (q + 1) (Sum.inr i) := by
    apply Fin.ext
    rfl
  rw [hindex, parityProductUnitary_apply_inr]

theorem endpointProductUnitary_intertwines_diagonal
    (T : ℝ) (q : ℕ)
    (x y : FiniteIndexClockSpace (Fin (q + 1))) :
    finiteIndexDiagonalHamiltonian
        (angularEnergy T (endpointN q))
        (endpointProductUnitary q (WithLp.toLp 2 (x, y))) =
      endpointProductUnitary q
        (WithLp.toLp 2
          (finiteIndexDiagonalHamiltonian
              (endpointActiveEnergy T q) x,
            finiteIndexDiagonalHamiltonian
              (endpointSpectatorEnergy T q) y)) := by
  ext j
  obtain ⟨s, rfl⟩ := (endpointParityIndexEquiv q).surjective j
  cases s with
  | inl i =>
      simp [finiteIndexDiagonalHamiltonian_apply,
        endpointActiveEnergy]
  | inr i =>
      simp [finiteIndexDiagonalHamiltonian_apply,
        endpointSpectatorEnergy]

def endpointProductBasis (T : ℝ) (q : ℕ) :
    OrthonormalBasis
      (Fin (q + 1) ⊕ Fin (q + 1)) ℂ
      (WithLp 2
        (FiniteIndexClockSpace (Fin (q + 1)) ×
          FiniteIndexClockSpace (Fin (q + 1)))) :=
  (finiteKrylovBasis
      (endpointActiveEnergy T q) (endpointActiveWeight q)).prod
    (EuclideanSpace.basisFun (Fin (q + 1)) ℂ)

def endpointSpectralBasis (T : ℝ) (q : ℕ) :
    OrthonormalBasis
      (Fin (q + 1) ⊕ Fin (q + 1)) ℂ
      (ClockSpace (endpointN q)) :=
  (endpointProductBasis T q).map (endpointProductUnitary q)

def endpointBlockIndexEquiv (q : ℕ) :
    Fin (q + 1) ⊕ Fin (q + 1) ≃ Fin (endpointN q + 1) :=
  finSumFinEquiv.trans (finCongr (by simp [endpointN]; omega))

def endpointBlockBasis (T : ℝ) (q : ℕ) :
    OrthonormalBasis (Fin (endpointN q + 1)) ℂ
      (ClockSpace (endpointN q)) :=
  (endpointSpectralBasis T q).reindex (endpointBlockIndexEquiv q)

def endpointKrylovUnitary (T : ℝ) (q : ℕ) :
    ClockSpace (endpointN q) ≃ₗᵢ[ℂ] ClockSpace (endpointN q) :=
  (EuclideanSpace.basisFun (Fin (endpointN q + 1)) ℂ).equiv
    (endpointBlockBasis T q) (Equiv.refl _)

@[simp] theorem endpointKrylovUnitary_basis
    (T : ℝ) (q : ℕ) (i : Fin (endpointN q + 1)) :
    endpointKrylovUnitary T q
        (EuclideanSpace.basisFun (Fin (endpointN q + 1)) ℂ i) =
      endpointBlockBasis T q i := by
  exact OrthonormalBasis.equiv_apply_basis _ _ _ i

theorem endpointBlockBasis_active
    (T : ℝ) (q : ℕ) (i : Fin (q + 1)) :
    endpointBlockBasis T q
        (endpointBlockIndexEquiv q (Sum.inl i)) =
      endpointProductUnitary q
        (WithLp.toLp 2
          (finiteKrylovBasis
              (endpointActiveEnergy T q) (endpointActiveWeight q) i,
            0)) := by
  rw [endpointBlockBasis, OrthonormalBasis.reindex_apply,
    Equiv.symm_apply_apply, endpointSpectralBasis,
    OrthonormalBasis.map_apply, endpointProductBasis,
    OrthonormalBasis.prod_apply]
  rfl

theorem endpointBlockBasis_spectator
    (T : ℝ) (q : ℕ) (i : Fin (q + 1)) :
    endpointBlockBasis T q
        (endpointBlockIndexEquiv q (Sum.inr i)) =
      endpointProductUnitary q
        (WithLp.toLp 2
          (0, EuclideanSpace.basisFun (Fin (q + 1)) ℂ i)) := by
  rw [endpointBlockBasis, OrthonormalBasis.reindex_apply,
    Equiv.symm_apply_apply, endpointSpectralBasis,
    OrthonormalBasis.map_apply, endpointProductBasis,
    OrthonormalBasis.prod_apply]
  rfl

theorem endpointBlockBasis_active_matrix
    (T : ℝ) (q : ℕ) (i j : Fin (q + 1)) :
    inner ℂ
        (endpointBlockBasis T q
          (endpointBlockIndexEquiv q (Sum.inl i)))
        (finiteIndexDiagonalHamiltonian
          (angularEnergy T (endpointN q))
          (endpointBlockBasis T q
            (endpointBlockIndexEquiv q (Sum.inl j)))) =
      inner ℂ
        (finiteKrylovBasis
          (endpointActiveEnergy T q) (endpointActiveWeight q) i)
        (finiteIndexDiagonalHamiltonian
          (endpointActiveEnergy T q)
          (finiteKrylovBasis
            (endpointActiveEnergy T q)
            (endpointActiveWeight q) j)) := by
  rw [endpointBlockBasis_active, endpointBlockBasis_active,
    endpointProductUnitary_intertwines_diagonal,
    endpointProductUnitary q |>.inner_map_map]
  simp [WithLp.prod_inner_apply]

theorem endpointBlockBasis_cross_matrix
    (T : ℝ) (q : ℕ) (i j : Fin (q + 1)) :
    inner ℂ
        (endpointBlockBasis T q
          (endpointBlockIndexEquiv q (Sum.inl i)))
        (finiteIndexDiagonalHamiltonian
          (angularEnergy T (endpointN q))
          (endpointBlockBasis T q
            (endpointBlockIndexEquiv q (Sum.inr j)))) = 0 := by
  rw [endpointBlockBasis_active, endpointBlockBasis_spectator,
    endpointProductUnitary_intertwines_diagonal,
    endpointProductUnitary q |>.inner_map_map]
  simp [WithLp.prod_inner_apply]

theorem endpointBlockBasis_cross_matrix'
    (T : ℝ) (q : ℕ) (i j : Fin (q + 1)) :
    inner ℂ
        (endpointBlockBasis T q
          (endpointBlockIndexEquiv q (Sum.inr i)))
        (finiteIndexDiagonalHamiltonian
          (angularEnergy T (endpointN q))
          (endpointBlockBasis T q
            (endpointBlockIndexEquiv q (Sum.inl j)))) = 0 := by
  rw [endpointBlockBasis_spectator, endpointBlockBasis_active,
    endpointProductUnitary_intertwines_diagonal,
    endpointProductUnitary q |>.inner_map_map]
  simp [WithLp.prod_inner_apply]

theorem endpointBlockBasis_spectator_matrix
    (T : ℝ) (q : ℕ) (i j : Fin (q + 1)) (hij : i ≠ j) :
    inner ℂ
        (endpointBlockBasis T q
          (endpointBlockIndexEquiv q (Sum.inr i)))
        (finiteIndexDiagonalHamiltonian
          (angularEnergy T (endpointN q))
          (endpointBlockBasis T q
            (endpointBlockIndexEquiv q (Sum.inr j)))) = 0 := by
  rw [endpointBlockBasis_spectator, endpointBlockBasis_spectator,
    endpointProductUnitary_intertwines_diagonal,
    endpointProductUnitary q |>.inner_map_map]
  simp only [WithLp.prod_inner_apply, inner_zero_left, zero_add]
  have hdiag :
      finiteIndexDiagonalHamiltonian
          (endpointSpectatorEnergy T q)
          (EuclideanSpace.basisFun (Fin (q + 1)) ℂ j) =
        (endpointSpectatorEnergy T q j : ℂ) •
          EuclideanSpace.basisFun (Fin (q + 1)) ℂ j := by
    ext k
    by_cases hkj : k = j
    · subst k
      simp [finiteIndexDiagonalHamiltonian_apply,
        EuclideanSpace.basisFun_apply]
    · simp [finiteIndexDiagonalHamiltonian_apply,
        EuclideanSpace.basisFun_apply, hkj]
  rw [hdiag, inner_smul_right]
  have hinner :
      inner ℂ
          (EuclideanSpace.basisFun (Fin (q + 1)) ℂ i)
          (EuclideanSpace.basisFun (Fin (q + 1)) ℂ j) = 0 :=
    (EuclideanSpace.basisFun (Fin (q + 1)) ℂ).orthonormal.2 hij
  rw [hinner, mul_zero]

@[simp] theorem endpointBlockIndexEquiv_inl_val
    (q : ℕ) (i : Fin (q + 1)) :
    ((endpointBlockIndexEquiv q (Sum.inl i) :
      Fin (endpointN q + 1)) : ℕ) = (i : ℕ) := rfl

@[simp] theorem endpointBlockIndexEquiv_inr_val
    (q : ℕ) (i : Fin (q + 1)) :
    ((endpointBlockIndexEquiv q (Sum.inr i) :
      Fin (endpointN q + 1)) : ℕ) =
        q + 1 + (i : ℕ) := rfl

theorem endpointBlockBasis_nearestNeighbor
    {T : ℝ} (hT : 0 < T) (q : ℕ) :
    ∀ i j : Fin (endpointN q + 1),
      ((i : ℕ) + 1 < (j : ℕ) ∨
        (j : ℕ) + 1 < (i : ℕ)) →
      inner ℂ (endpointBlockBasis T q i)
        (finiteIndexDiagonalHamiltonian
          (angularEnergy T (endpointN q))
          (endpointBlockBasis T q j)) = 0 := by
  intro i j hij
  obtain ⟨si, rfl⟩ := (endpointBlockIndexEquiv q).surjective i
  obtain ⟨sj, rfl⟩ := (endpointBlockIndexEquiv q).surjective j
  cases si with
  | inl ai =>
      cases sj with
      | inl aj =>
          rw [endpointBlockBasis_active_matrix]
          apply finiteKrylovBasis_nearestNeighbor
            (endpointActiveEnergy_injective hT q)
            (endpointActiveWeight_pos q)
          simpa using hij
      | inr aj =>
          exact endpointBlockBasis_cross_matrix T q ai aj
  | inr ai =>
      cases sj with
      | inl aj =>
          exact endpointBlockBasis_cross_matrix' T q ai aj
      | inr aj =>
          apply endpointBlockBasis_spectator_matrix T q ai aj
          intro haij
          subst aj
          simp at hij

theorem endpointProductUnitary_activeKet_eq_parityClock
    (q : ℕ) :
    endpointProductUnitary q
        (WithLp.toLp 2
          (finiteIndexWeightKet (endpointActiveWeight q), 0)) =
      parityClock (endpointN q) := by
  ext j
  obtain ⟨s, rfl⟩ := (endpointParityIndexEquiv q).surjective j
  cases s with
  | inl i =>
      simp [parityClock, endpointActiveWeight]
  | inr i =>
      simp [parityClock, endpointEvenWeight_zero]

theorem endpointKrylovUnitary_fixedClock
    {T : ℝ} (hT : 0 < T) (q : ℕ) :
    endpointKrylovUnitary T q (fixedClock (endpointN q)) =
      parityClock (endpointN q) := by
  rw [fixedClock, endpointKrylovUnitary_basis]
  have hzero :
      (0 : Fin (endpointN q + 1)) =
        endpointBlockIndexEquiv q (Sum.inl 0) := by
    apply Fin.ext
    rfl
  rw [hzero, endpointBlockBasis_active,
    finiteKrylovBasis_zero
      (endpointActiveEnergy_injective hT q)
      (endpointActiveWeight_pos q)
      (endpointActiveWeight_sum q)]
  exact endpointProductUnitary_activeKet_eq_parityClock q

theorem fixedProtocolHamiltonian_endpoint_nearestNeighbor
    {T : ℝ} (hT : 0 < T) (q : ℕ) :
    NearestNeighborHamiltonian
      (fixedProtocolHamiltonian T (endpointN q)
        (endpointKrylovUnitary T q)) := by
  intro i j hij
  let U := endpointKrylovUnitary T q
  have hUi :
      U (EuclideanSpace.basisFun (Fin (endpointN q + 1)) ℂ i) =
        endpointBlockBasis T q i := by
    simpa [U] using endpointKrylovUnitary_basis T q i
  have hUj :
      U (EuclideanSpace.basisFun (Fin (endpointN q + 1)) ℂ j) =
        endpointBlockBasis T q j := by
    simpa [U] using endpointKrylovUnitary_basis T q j
  have htransport :
      U (((U.symm.toContinuousLinearEquiv.toContinuousLinearMap ∘L
          scaledClockHamiltonian T (endpointN q) ∘L
            U.toContinuousLinearEquiv.toContinuousLinearMap))
          (EuclideanSpace.basisFun
            (Fin (endpointN q + 1)) ℂ j)) =
        scaledClockHamiltonian T (endpointN q)
          (U (EuclideanSpace.basisFun
            (Fin (endpointN q + 1)) ℂ j)) := by
    simp
  calc
    inner ℂ
        (EuclideanSpace.basisFun
          (Fin (endpointN q + 1)) ℂ i)
        ((fixedProtocolHamiltonian T (endpointN q) U)
          (EuclideanSpace.basisFun
            (Fin (endpointN q + 1)) ℂ j)) =
      inner ℂ
        (U (EuclideanSpace.basisFun
          (Fin (endpointN q + 1)) ℂ i))
        (U ((fixedProtocolHamiltonian T (endpointN q) U)
          (EuclideanSpace.basisFun
            (Fin (endpointN q + 1)) ℂ j))) := by
              symm
              exact U.inner_map_map _ _
    _ = inner ℂ (endpointBlockBasis T q i)
        (finiteIndexDiagonalHamiltonian
          (angularEnergy T (endpointN q))
          (endpointBlockBasis T q j)) := by
            rw [fixedProtocolHamiltonian, htransport, hUi, hUj,
              scaledClockHamiltonian]
    _ = 0 := endpointBlockBasis_nearestNeighbor hT q i j hij

theorem exists_endpointN_every_future_probability_every_strict_window
    (m : ℕ) {ρ ε : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hε : 0 < ε) :
    ∃ q : ℕ,
      m < endpointN q ∧
      ∀ p : ℝ, p ∈ Set.Icc (0 : ℝ) 1 →
        (∀ k : ℕ, k ≤ m →
          ∑ j : Fin (endpointN q + 1),
              interpolatedWeight (endpointN q) (Real.sqrt p) j *
                halfLatticeEnergy (endpointN q) j ^ k =
            ∑ j : Fin (endpointN q + 1),
              fullWeight (endpointN q) j *
                halfLatticeEnergy (endpointN q) j ^ k) ∧
        (∀ t : ℝ, |t| ≤ ρ →
          |interpolatedProbability
              (endpointN q) (Real.sqrt p) t -
            fullProbability (endpointN q) t| < 2 * ε) ∧
        interpolatedProbability
            (endpointN q) (Real.sqrt p) 1 = p := by
  let s := Real.sin (Real.pi * ρ / 2)
  have hs0 : 0 ≤ s := by
    dsimp [s]
    apply Real.sin_nonneg_of_nonneg_of_le_pi
    · nlinarith [Real.pi_pos]
    · nlinarith [Real.pi_pos]
  have hs1 : s < 1 := by
    dsimp [s]
    rw [← Real.sin_pi_div_two]
    apply Real.sin_lt_sin_of_lt_of_le_pi_div_two
    · nlinarith [Real.pi_pos]
    · exact le_rfl
    · nlinarith [Real.pi_pos]
  obtain ⟨a, ha⟩ := exists_pow_lt_of_lt_one hε hs1
  let q := max m a
  have hmq : m ≤ q := le_max_left _ _
  have haq : a ≤ q := le_max_right _ _
  have hmn : m < endpointN q := by
    simp [endpointN]
    omega
  have han : a ≤ endpointN q := by
    simp [endpointN]
    omega
  have hn : 0 < endpointN q := by
    simp [endpointN]
  refine ⟨q, hmn, ?_⟩
  intro p hp
  have hθ0 : 0 ≤ Real.sqrt p := Real.sqrt_nonneg p
  have hθ1 : Real.sqrt p ≤ 1 := Real.sqrt_le_one.mpr hp.2
  refine ⟨?_, ?_, ?_⟩
  · intro k hk
    exact interpolated_energyMoment_eq_full
      (lt_of_le_of_lt hk hmn) _
  · intro t ht
    have hwindow :=
      amplitude_difference_window_bound (endpointN q) hρ1.le ht
    have hpow : s ^ endpointN q ≤ s ^ a :=
      pow_le_pow_of_le_one hs0 hs1.le han
    have hparity :
        ‖parityAmplitude (endpointN q) t -
          fullAmplitude (endpointN q) t‖ < ε :=
      lt_of_le_of_lt
        (hwindow.trans (by simpa [s] using hpow)) ha
    have hamp :
        ‖interpolatedAmplitude
            (endpointN q) (Real.sqrt p) t -
          fullAmplitude (endpointN q) t‖ < ε := by
      rw [interpolatedAmplitude_difference_norm
        (endpointN q) hθ0]
      have hmul :
          Real.sqrt p *
              ‖parityAmplitude (endpointN q) t -
                fullAmplitude (endpointN q) t‖ ≤
            ‖parityAmplitude (endpointN q) t -
              fullAmplitude (endpointN q) t‖ := by
        nlinarith
          [norm_nonneg
            (parityAmplitude (endpointN q) t -
              fullAmplitude (endpointN q) t)]
      exact lt_of_le_of_lt hmul hparity
    exact lt_of_le_of_lt
      (interpolated_probability_difference_le_amplitude
        hn hθ0 hθ1 t) (by linarith)
  · calc
      interpolatedProbability
          (endpointN q) (Real.sqrt p) 1 =
          (Real.sqrt p) ^ 2 :=
        interpolatedProbability_target hn hθ0
      _ = p := Real.sq_sqrt hp.1

theorem one_endpointN_record_compatible_with_every_future_probability
    (m : ℕ) (T H : ℝ) (hT : 0 < T) (hH0 : 0 ≤ H)
    (hHT : H < T) {δ : ℝ} (hδ : 0 < δ) :
    ∃ q : ℕ,
      m < endpointN q ∧
      ∀ p : ℝ, p ∈ Set.Icc (0 : ℝ) 1 →
        (∀ k : ℕ, k ≤ m →
          ∑ j : Fin (endpointN q + 1),
              interpolatedWeight (endpointN q) (Real.sqrt p) j *
                scaledEnergy T (endpointN q) j ^ k =
            ∑ j : Fin (endpointN q + 1),
              fullWeight (endpointN q) j *
                scaledEnergy T (endpointN q) j ^ k) ∧
        (∀ t : ℝ, |t| ≤ H →
          |scaledInterpolatedProbability
              T (endpointN q) (Real.sqrt p) t -
            scaledFullProbability T (endpointN q) t| < δ) ∧
        scaledInterpolatedProbability
            T (endpointN q) (Real.sqrt p) T = p := by
  have hρ0 : 0 ≤ H / T := div_nonneg hH0 hT.le
  have hρ1 : H / T < 1 := (div_lt_one hT).2 hHT
  have hhalf : 0 < δ / 2 := by linarith
  obtain ⟨q, hmn, hall⟩ :=
    exists_endpointN_every_future_probability_every_strict_window
      m hρ0 hρ1 hhalf
  have hn : 0 < endpointN q := by simp [endpointN]
  refine ⟨q, hmn, ?_⟩
  intro p hp
  obtain ⟨_hmom, hprob, _htarget⟩ := hall p hp
  refine ⟨?_, ?_, ?_⟩
  · intro k hk
    exact scaled_interpolated_energyMoment_eq
      (lt_of_le_of_lt hk hmn) _
  · intro t ht
    have hscaled := hprob (t / T) (by
      rw [abs_div, abs_of_pos hT]
      exact (div_le_div_iff_of_pos_right hT).2 ht)
    change
      |interpolatedProbability
          (endpointN q) (Real.sqrt p) (t / T) -
        fullProbability (endpointN q) (t / T)| < δ
    have heq : 2 * (δ / 2) = δ := by ring
    simpa only [heq] using hscaled
  · rw [scaledInterpolatedProbability_target
      hT hn (Real.sqrt_nonneg p), Real.sq_sqrt hp.1]

theorem interpolatedClock_one (n : ℕ) :
    interpolatedClock n 1 = parityClock n := by
  apply congrArg finiteIndexWeightKet
  funext j
  simp [interpolatedWeight]

/--
Closed-endpoint nearest-neighbour law. One fixed normalized state and
projector admit every terminal return probability in `[0,1]` under an
isospectral family of finite tridiagonal Hamiltonians, while any prescribed
finite collection of energy moments and the full strictly earlier survival
record remain common.
-/
theorem one_fixed_nearestNeighbor_chain_every_future_probability
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
              T n (Real.sqrt p) T U = p := by
  obtain ⟨q, hmn, hall⟩ :=
    one_endpointN_record_compatible_with_every_future_probability
      m T H hT hH0 hHT hδ
  let n := endpointN q
  have hn : 0 < n := by simp [n, endpointN]
  refine ⟨n, hmn, fixedClock_norm n, ?_⟩
  intro p hp
  obtain ⟨_hmom, hwindow, htarget⟩ := hall p hp
  have hθ0 : 0 ≤ Real.sqrt p := Real.sqrt_nonneg p
  have hθ1 : Real.sqrt p ≤ 1 := Real.sqrt_le_one.mpr hp.2
  obtain ⟨U, hU, hlocal⟩ :
      ∃ U : ClockSpace n ≃ₗᵢ[ℂ] ClockSpace n,
        U (fixedClock n) =
            interpolatedClock n (Real.sqrt p) ∧
        NearestNeighborHamiltonian
          (fixedProtocolHamiltonian T n U) := by
    by_cases hp1 : p = 1
    · subst p
      refine ⟨endpointKrylovUnitary T q, ?_, ?_⟩
      · simpa only [n, Real.sqrt_one, interpolatedClock_one]
          using endpointKrylovUnitary_fixedClock hT q
      · simpa only [n] using
          fixedProtocolHamiltonian_endpoint_nearestNeighbor hT q
    · have hp_lt_one : p < 1 := lt_of_le_of_ne hp.2 hp1
      have hθ_lt_one : Real.sqrt p < 1 := by
        rw [Real.sqrt_lt' zero_lt_one]
        simpa using hp_lt_one
      let U : ClockSpace n ≃ₗᵢ[ℂ] ClockSpace n :=
        finiteKrylovUnitary (angularEnergy T n)
          (interpolatedWeight n (Real.sqrt p))
      have hU :
          U (fixedClock n) =
            interpolatedClock n (Real.sqrt p) :=
        finiteKrylovUnitary_fixedClock
          hT hn hθ0 hθ_lt_one
      refine ⟨U, hU, ?_⟩
      exact fixedProtocolHamiltonian_krylov_nearestNeighbor
        hT hθ0 hθ_lt_one
  refine ⟨U, hU, hlocal, ?_,
    fixedProtocolHamiltonian_selfAdjoint T n U,
    fixedProtocolHamiltonian_intertwines T n U, ?_, ?_⟩
  · intro k hk
    exact fixedProtocol_energyMoment_eq_full
      (lt_of_le_of_lt hk hmn) hθ0 hθ1 hU
  · intro t ht
    rw [fixedProtocolProbability_eq
      hT n hθ0 hθ1 t hU]
    exact hwindow t ht
  · rw [fixedProtocolProbability_eq
      hT n hθ0 hθ1 T hU]
    exact htarget

end RHTower.ParityForecast
