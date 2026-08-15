import GaloisForLFunctions.HTGeometry.FiniteRankOneSelector
import GaloisForLFunctions.HTGeometry.SignedAtomicMomentInertia

/-!
# Exact signed `N₁` bulk threshold reversal

This leaf formalizes the literal three-atom rational counterexample from the
`n1-signed-bulk-exterior-monotonicity-fails` pipeline card.  It records the
Gram form, its explicit inverse, its exact inertia, two exterior energies, and
the resulting reverse order of rank-one threshold values.

All rational identities below are kernel-checked equalities; no approximation
or numerical search is used.
-/

namespace HTGeometry

open scoped BigOperators Matrix

noncomputable section

/-- Coefficient vectors for real polynomials of degree at most two. -/
abbrev N1SignedCoeff := Fin 3 → ℝ

/-- The three atomic support points. -/
def n1SignedNode : Fin 3 → ℝ := ![0, 1, 2]

/-- The signed atom weights: one negative, two positive. -/
def n1SignedWeight : Fin 3 → ℝ := ![-(1 / 36 : ℝ), 1 / 14, 15]

/-- The degree-two Gram/Hankel matrix of the signed atomic form. -/
def n1SignedGram : Matrix (Fin 3) (Fin 3) ℝ :=
  algebraicHankelMatrix (finiteModalSequence n1SignedWeight n1SignedNode) 3

/-- The monomial evaluation vector `(1, x, x²)`. -/
def n1SignedEvalVector (x : ℝ) : N1SignedCoeff := fun j => x ^ (j : ℕ)

/-- Explicit inverse of `n1SignedGram`. -/
def n1SignedGramInv : Matrix (Fin 3) (Fin 3) ℝ :=
  !![-36, 54, -18;
     54, -(1499 / 60 : ℝ), -(61 / 60 : ℝ);
     -18, -(61 / 60 : ℝ), 301 / 60]

/-- The displayed explicit inverse is a right inverse of the literal Gram matrix. -/
theorem n1SignedGram_mul_explicitInv : n1SignedGram * n1SignedGramInv = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [n1SignedGram, n1SignedGramInv, n1SignedWeight, n1SignedNode,
      algebraicHankelMatrix, finiteModalSequence, Fin.sum_univ_succ,
      Matrix.mul_apply]

/-- The literal Gram matrix is invertible. -/
theorem n1SignedGram_isUnit : IsUnit n1SignedGram :=
  IsUnit.of_mul_eq_one n1SignedGramInv n1SignedGram_mul_explicitInv

/-- The explicit inverse agrees with Mathlib's nonsingular inverse. -/
theorem n1SignedGram_inv_eq_explicit : n1SignedGram⁻¹ = n1SignedGramInv := by
  letI : Invertible n1SignedGram := n1SignedGram_isUnit.invertible
  apply (Matrix.mul_right_inj_of_invertible n1SignedGram).mp
  rw [Matrix.mul_inv_of_invertible, n1SignedGram_mul_explicitInv]

/-- The inverse energy `v_xᵀ H⁻¹ v_x` appearing in the rank-one threshold. -/
def n1SignedEnergy (x : ℝ) : ℝ :=
  n1SignedEvalVector x ⬝ᵥ n1SignedGram⁻¹ *ᵥ n1SignedEvalVector x

/-- Exact inverse energy at the farther exterior point. -/
theorem n1SignedEnergy_minus_four : n1SignedEnergy (-4) = -(88 / 3 : ℝ) := by
  norm_num [n1SignedEnergy, n1SignedEvalVector, n1SignedGram_inv_eq_explicit,
    n1SignedGramInv, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

/-- Exact inverse energy at the first-trivial-zero exterior point. -/
theorem n1SignedEnergy_minus_four_twentyFifth :
    n1SignedEnergy (-(4 / 25 : ℝ)) = -(321266936 / 5859375 : ℝ) := by
  norm_num [n1SignedEnergy, n1SignedEvalVector, n1SignedGram_inv_eq_explicit,
    n1SignedGramInv, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

/-- The three support nodes are distinct. -/
theorem n1SignedNode_injective : Function.Injective n1SignedNode := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [n1SignedNode]

/-- The signed Gram form has two positive squares. -/
theorem n1SignedGram_sigPos_eq_two :
    sigPos n1SignedGram.toQuadraticForm' = 2 := by
  have hset : {i | 0 < n1SignedWeight i} = ({(1 : Fin 3), 2} : Set (Fin 3)) := by
    ext i
    fin_cases i
    · norm_num [n1SignedWeight]; decide
    · norm_num [n1SignedWeight]
    · norm_num [n1SignedWeight]; decide
  simpa only [n1SignedGram, hset, Set.ncard_pair (by decide : (1 : Fin 3) ≠ 2)] using
    (sigPos_algebraicHankelMatrix_finiteModalSequence n1SignedNode_injective
      (weight := n1SignedWeight))

/-- The signed Gram form has exactly one negative square. -/
theorem n1SignedGram_sigNeg_eq_one :
    sigNeg n1SignedGram.toQuadraticForm' = 1 := by
  have hset : {i | n1SignedWeight i < 0} = ({(0 : Fin 3)} : Set (Fin 3)) := by
    ext i
    fin_cases i
    · norm_num [n1SignedWeight]
    · norm_num [n1SignedWeight]
    · norm_num [n1SignedWeight]
  simpa only [n1SignedGram, hset, Set.ncard_singleton] using
    (sigNeg_algebraicHankelMatrix_finiteModalSequence n1SignedNode_injective
      (weight := n1SignedWeight))

/-- There is no radical: the stated inertia is exactly `(2, 1, 0)`. -/
theorem n1SignedGram_radical_finrank_eq_zero :
    Module.finrank ℝ n1SignedGram.toQuadraticForm'.radical = 0 := by
  have hset : {i | n1SignedWeight i = 0} = (∅ : Set (Fin 3)) := by
    ext i
    fin_cases i <;> norm_num [n1SignedWeight]
  rw [show n1SignedGram =
    algebraicHankelMatrix (finiteModalSequence n1SignedWeight n1SignedNode) 3 from rfl]
  rw [finrank_radical_algebraicHankelMatrix_finiteModalSequence n1SignedNode_injective
    (weight := n1SignedWeight), hset]
  exact Set.ncard_empty (Fin 3)

/-- The literal form is congruent to the diagonal weighted sum of evaluation squares. -/
theorem n1SignedGram_equivalent_weightedSumSquares :
    QuadraticMap.Equivalent n1SignedGram.toQuadraticForm'
      (QuadraticMap.weightedSumSquares ℝ n1SignedWeight) := by
  simpa only [n1SignedGram] using
    (algebraicHankelMatrix_finiteModalSequence_equivalent_weightedSumSquares
      (weight := n1SignedWeight) n1SignedNode_injective)

/-- Every atomic support point lies to the right of both exterior boundary points. -/
theorem n1SignedSupport_right_of_boundaries (i : Fin 3) :
    (-4 : ℝ) < n1SignedNode i ∧ -(4 / 25 : ℝ) < n1SignedNode i := by
  fin_cases i <;> norm_num [n1SignedNode]

/-- The rank-one repair threshold `-1 / m(x)`. -/
def n1SignedThreshold (x : ℝ) : ℝ := -1 / n1SignedEnergy x

/-- Exact threshold at `-4`. -/
theorem n1SignedThreshold_minus_four :
    n1SignedThreshold (-4) = (3 / 88 : ℝ) := by
  rw [n1SignedThreshold, n1SignedEnergy_minus_four]
  norm_num

/-- Exact threshold at `-4/25`. -/
theorem n1SignedThreshold_minus_four_twentyFifth :
    n1SignedThreshold (-(4 / 25 : ℝ)) = (5859375 / 321266936 : ℝ) := by
  rw [n1SignedThreshold, n1SignedEnergy_minus_four_twentyFifth]
  norm_num

/-- The farther-left boundary has the larger repair threshold. -/
theorem n1SignedThreshold_order_reversed :
    n1SignedThreshold (-4) > n1SignedThreshold (-(4 / 25 : ℝ)) := by
  rw [n1SignedThreshold_minus_four, n1SignedThreshold_minus_four_twentyFifth]
  norm_num

/-- Complete finite signed-moment counterexample to exterior threshold monotonicity. -/
theorem n1SignedBulkExteriorMonotonicityFails :
    QuadraticMap.Equivalent n1SignedGram.toQuadraticForm'
        (QuadraticMap.weightedSumSquares ℝ n1SignedWeight) ∧
      sigPos n1SignedGram.toQuadraticForm' = 2 ∧
        sigNeg n1SignedGram.toQuadraticForm' = 1 ∧
          Module.finrank ℝ n1SignedGram.toQuadraticForm'.radical = 0 ∧
            (∀ i, (-4 : ℝ) < n1SignedNode i ∧ -(4 / 25 : ℝ) < n1SignedNode i) ∧
              n1SignedEnergy (-4) = -(88 / 3 : ℝ) ∧
                n1SignedEnergy (-(4 / 25 : ℝ)) = -(321266936 / 5859375 : ℝ) ∧
                  n1SignedThreshold (-4) = (3 / 88 : ℝ) ∧
                    n1SignedThreshold (-(4 / 25 : ℝ)) =
                      (5859375 / 321266936 : ℝ) ∧
                      n1SignedThreshold (-4) > n1SignedThreshold (-(4 / 25 : ℝ)) := by
  exact ⟨n1SignedGram_equivalent_weightedSumSquares, n1SignedGram_sigPos_eq_two,
    n1SignedGram_sigNeg_eq_one, n1SignedGram_radical_finrank_eq_zero,
    n1SignedSupport_right_of_boundaries, n1SignedEnergy_minus_four,
    n1SignedEnergy_minus_four_twentyFifth, n1SignedThreshold_minus_four,
    n1SignedThreshold_minus_four_twentyFifth, n1SignedThreshold_order_reversed⟩

end

end HTGeometry

namespace GaloisForLFunctions.HTGeometry

open Matrix Complex
open scoped ComplexOrder Matrix

noncomputable section

/-- Complex realization of the three real support nodes. -/
def n1SignedComplexNode : Fin 3 → ℂ := fun i => (HTGeometry.n1SignedNode i : ℂ)

/-- Complex realization of the signed real atom weights. -/
def n1SignedComplexWeight : Fin 3 → ℂ := fun i => (HTGeometry.n1SignedWeight i : ℂ)

/-- The same signed moment Gram matrix over `ℂ`, for the Hermitian rank-one API. -/
def n1SignedComplexGram : Matrix (Fin 3) (Fin 3) ℂ :=
  HTGeometry.algebraicHankelMatrix
    (HTGeometry.finiteModalSequence n1SignedComplexWeight n1SignedComplexNode) 3

/-- Node-evaluation Vandermonde matrix for the complex realization. -/
def n1SignedComplexV : Matrix (Fin 3) (Fin 3) ℂ :=
  Matrix.vandermonde n1SignedComplexNode

/-- Diagonal signed-mass matrix for the complex realization. -/
def n1SignedComplexD : Matrix (Fin 3) (Fin 3) ℂ :=
  Matrix.diagonal n1SignedComplexWeight

/-- Explicit inverse of the Vandermonde matrix at `0, 1, 2`. -/
def n1SignedComplexVInv : Matrix (Fin 3) (Fin 3) ℂ :=
  !![1, 0, 0;
     -(3 / 2 : ℂ), 2, -(1 / 2 : ℂ);
     1 / 2, -1, 1 / 2]

/-- Explicit inverse of the diagonal signed-mass matrix. -/
def n1SignedComplexDInv : Matrix (Fin 3) (Fin 3) ℂ :=
  Matrix.diagonal fun i => ![-36, 14, 1 / 15] i

theorem n1SignedComplexV_mul_inv : n1SignedComplexV * n1SignedComplexVInv = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [n1SignedComplexV, n1SignedComplexNode, HTGeometry.n1SignedNode,
      n1SignedComplexVInv, Matrix.vandermonde_apply, Matrix.mul_apply,
      Fin.sum_univ_succ]

theorem n1SignedComplexV_unit : IsUnit n1SignedComplexV :=
  IsUnit.of_mul_eq_one n1SignedComplexVInv n1SignedComplexV_mul_inv

theorem n1SignedComplexD_mul_inv : n1SignedComplexD * n1SignedComplexDInv = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [n1SignedComplexD, n1SignedComplexDInv, n1SignedComplexWeight,
      HTGeometry.n1SignedWeight, Matrix.mul_apply, Matrix.diagonal_apply,
      Fin.sum_univ_succ]

theorem n1SignedComplexD_unit : IsUnit n1SignedComplexD :=
  IsUnit.of_mul_eq_one n1SignedComplexDInv n1SignedComplexD_mul_inv

theorem n1SignedComplexV_conjTranspose : n1SignedComplexVᴴ = n1SignedComplexVᵀ := by
  ext i j
  simp [n1SignedComplexV, n1SignedComplexNode, Matrix.vandermonde_apply]

/-- The complex Gram matrix is an invertible Hermitian congruence of the signed diagonal mass. -/
theorem n1SignedComplexGram_factor :
    n1SignedComplexGram = n1SignedComplexVᴴ * n1SignedComplexD * n1SignedComplexV := by
  have hV : (Matrix.vandermonde n1SignedComplexNode)ᴴ =
      (Matrix.vandermonde n1SignedComplexNode)ᵀ := by
    simpa only [n1SignedComplexV] using n1SignedComplexV_conjTranspose
  rw [n1SignedComplexGram,
    HTGeometry.algebraicHankelMatrix_finiteModalSequence_eq_vandermonde,
    n1SignedComplexV, n1SignedComplexD, ← hV]

theorem n1SignedComplexD_hermitian : n1SignedComplexD.IsHermitian := by
  rw [n1SignedComplexD, Matrix.isHermitian_diagonal_iff]
  intro i
  rw [isSelfAdjoint_iff]
  simp [n1SignedComplexWeight]

theorem n1SignedComplexGram_hermitian : n1SignedComplexGram.IsHermitian := by
  rw [n1SignedComplexGram_factor]
  exact isHermitian_conjTranspose_mul_mul n1SignedComplexV n1SignedComplexD_hermitian

theorem n1SignedComplexGram_unit : IsUnit n1SignedComplexGram := by
  rw [n1SignedComplexGram_factor]
  exact ((isUnit_conjTranspose n1SignedComplexV_unit).mul n1SignedComplexD_unit).mul
    n1SignedComplexV_unit

/-- Explicit inverse of the complex Gram matrix. -/
def n1SignedComplexGramInv : Matrix (Fin 3) (Fin 3) ℂ :=
  !![-36, 54, -18;
     54, -(1499 / 60 : ℂ), -(61 / 60 : ℂ);
     -18, -(61 / 60 : ℂ), 301 / 60]

theorem n1SignedComplexGram_mul_inv :
    n1SignedComplexGram * n1SignedComplexGramInv = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [n1SignedComplexGram, n1SignedComplexWeight, HTGeometry.n1SignedWeight,
      n1SignedComplexNode, HTGeometry.n1SignedNode, n1SignedComplexGramInv,
      HTGeometry.algebraicHankelMatrix, HTGeometry.finiteModalSequence,
      Matrix.mul_apply, Fin.sum_univ_succ]

theorem n1SignedComplexGram_inv_eq : n1SignedComplexGram⁻¹ = n1SignedComplexGramInv := by
  letI : Invertible n1SignedComplexGram := n1SignedComplexGram_unit.invertible
  apply (Matrix.mul_right_inj_of_invertible n1SignedComplexGram).mp
  rw [Matrix.mul_inv_of_invertible, n1SignedComplexGram_mul_inv]

/-- Complex monomial evaluation vector at a real boundary point. -/
def n1SignedComplexEval (x : ℝ) : Fin 3 → ℂ := fun j => (x ^ (j : ℕ) : ℂ)

theorem n1SignedComplexEnergy_minus_four :
    rankOneEnergy n1SignedComplexGram (n1SignedComplexEval (-4)) = -(88 / 3 : ℝ) := by
  norm_num [rankOneEnergy, n1SignedComplexEval, n1SignedComplexGram_inv_eq,
    n1SignedComplexGramInv, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

theorem n1SignedComplexEnergy_minus_four_twentyFifth :
    rankOneEnergy n1SignedComplexGram (n1SignedComplexEval (-(4 / 25 : ℝ))) =
      -(321266936 / 5859375 : ℝ) := by
  norm_num [rankOneEnergy, n1SignedComplexEval, n1SignedComplexGram_inv_eq,
    n1SignedComplexGramInv, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

theorem n1SignedComplexD_posIndex : hermPosIndex n1SignedComplexD = 2 := by
  change hermPosIndex (Matrix.diagonal fun i => (HTGeometry.n1SignedWeight i : ℂ)) = 2
  rw [posIndex_diagonal]
  have hset : ({i | 0 < HTGeometry.n1SignedWeight i} : Finset (Fin 3)) =
      ({(1 : Fin 3), 2} : Finset (Fin 3)) := by
    ext i
    fin_cases i
    · norm_num [HTGeometry.n1SignedWeight]; decide
    · norm_num [HTGeometry.n1SignedWeight]
    · norm_num [HTGeometry.n1SignedWeight]; decide
  rw [hset]
  decide

theorem n1SignedComplexD_negIndex : hermNegIndex n1SignedComplexD = 1 := by
  change hermNegIndex (Matrix.diagonal fun i => (HTGeometry.n1SignedWeight i : ℂ)) = 1
  rw [negIndex_diagonal]
  have hset : ({i | HTGeometry.n1SignedWeight i < 0} : Finset (Fin 3)) =
      ({(0 : Fin 3)} : Finset (Fin 3)) := by
    ext i
    fin_cases i <;> norm_num [HTGeometry.n1SignedWeight]
  rw [hset]
  decide

theorem n1SignedComplexD_nullIndex : hermNullIndex n1SignedComplexD = 0 := by
  change hermNullIndex (Matrix.diagonal fun i => (HTGeometry.n1SignedWeight i : ℂ)) = 0
  rw [nullIndex_diagonal]
  have hset : ({i | HTGeometry.n1SignedWeight i = 0} : Finset (Fin 3)) = ∅ := by
    ext i
    fin_cases i <;> norm_num [HTGeometry.n1SignedWeight]
  rw [hset]
  exact Finset.card_empty

/-- The Hermitian complex Gram matrix has inertia `(2, 1, 0)`. -/
theorem n1SignedComplexGram_posIndex : hermPosIndex n1SignedComplexGram = 2 := by
  rw [n1SignedComplexGram_factor,
    posIndex_conjugate n1SignedComplexD n1SignedComplexV_unit]
  exact n1SignedComplexD_posIndex

theorem n1SignedComplexGram_negIndex : hermNegIndex n1SignedComplexGram = 1 := by
  rw [n1SignedComplexGram_factor,
    negIndex_conjugate n1SignedComplexD n1SignedComplexV_unit]
  exact n1SignedComplexD_negIndex

theorem n1SignedComplexGram_nullIndex : hermNullIndex n1SignedComplexGram = 0 := by
  rw [n1SignedComplexGram_factor,
    nullIndex_conjugate n1SignedComplexD n1SignedComplexV_unit]
  exact n1SignedComplexD_nullIndex

theorem n1SignedComplexThreshold_minus_four :
    rankOneThreshold n1SignedComplexGram (n1SignedComplexEval (-4)) = (3 / 88 : ℝ) := by
  rw [rankOneThreshold, n1SignedComplexEnergy_minus_four]
  norm_num

theorem n1SignedComplexThreshold_minus_four_twentyFifth :
    rankOneThreshold n1SignedComplexGram (n1SignedComplexEval (-(4 / 25 : ℝ))) =
      (5859375 / 321266936 : ℝ) := by
  rw [rankOneThreshold, n1SignedComplexEnergy_minus_four_twentyFifth]
  norm_num

/-- The actual rank-one repair at `-4` is positive definite exactly above its threshold. -/
theorem n1SignedComplexRepair_posDef_iff_above_minus_four (t : ℝ) (ht : 0 < t) :
    (rankOneRepair n1SignedComplexGram (n1SignedComplexEval (-4)) t).PosDef ↔
      (3 / 88 : ℝ) < t := by
  have hm : rankOneEnergy n1SignedComplexGram (n1SignedComplexEval (-4)) < 0 := by
    rw [n1SignedComplexEnergy_minus_four]
    norm_num
  simpa only [n1SignedComplexThreshold_minus_four] using
    (rankOneRepair_posDef_iff_above_threshold n1SignedComplexGram
      (n1SignedComplexEval (-4)) n1SignedComplexGram_hermitian n1SignedComplexGram_unit
      n1SignedComplexGram_negIndex n1SignedComplexGram_nullIndex ht hm)

/-- The actual rank-one repair at `-4/25` is positive definite exactly above its threshold. -/
theorem n1SignedComplexRepair_posDef_iff_above_minus_four_twentyFifth (t : ℝ) (ht : 0 < t) :
    (rankOneRepair n1SignedComplexGram (n1SignedComplexEval (-(4 / 25 : ℝ))) t).PosDef ↔
      (5859375 / 321266936 : ℝ) < t := by
  have hm : rankOneEnergy n1SignedComplexGram
      (n1SignedComplexEval (-(4 / 25 : ℝ))) < 0 := by
    rw [n1SignedComplexEnergy_minus_four_twentyFifth]
    norm_num
  simpa only [n1SignedComplexThreshold_minus_four_twentyFifth] using
    (rankOneRepair_posDef_iff_above_threshold n1SignedComplexGram
      (n1SignedComplexEval (-(4 / 25 : ℝ))) n1SignedComplexGram_hermitian
      n1SignedComplexGram_unit n1SignedComplexGram_negIndex n1SignedComplexGram_nullIndex ht hm)

/-- Complete Hermitian rank-one crossing certificate for the two exterior channels. -/
theorem n1SignedComplexRankOneThresholdCertificate :
    hermPosIndex n1SignedComplexGram = 2 ∧ hermNegIndex n1SignedComplexGram = 1 ∧
      hermNullIndex n1SignedComplexGram = 0 ∧
        rankOneEnergy n1SignedComplexGram (n1SignedComplexEval (-4)) = -(88 / 3 : ℝ) ∧
          rankOneEnergy n1SignedComplexGram (n1SignedComplexEval (-(4 / 25 : ℝ))) =
            -(321266936 / 5859375 : ℝ) ∧
            rankOneThreshold n1SignedComplexGram (n1SignedComplexEval (-4)) = (3 / 88 : ℝ) ∧
              rankOneThreshold n1SignedComplexGram
                  (n1SignedComplexEval (-(4 / 25 : ℝ))) =
                (5859375 / 321266936 : ℝ) ∧
                (3 / 88 : ℝ) > (5859375 / 321266936 : ℝ) ∧
                (∀ t, 0 < t →
                  ((rankOneRepair n1SignedComplexGram (n1SignedComplexEval (-4)) t).PosDef ↔
                    (3 / 88 : ℝ) < t)) ∧
                ∀ t, 0 < t →
                  ((rankOneRepair n1SignedComplexGram
                    (n1SignedComplexEval (-(4 / 25 : ℝ))) t).PosDef ↔
                    (5859375 / 321266936 : ℝ) < t) := by
  refine ⟨n1SignedComplexGram_posIndex, n1SignedComplexGram_negIndex,
    n1SignedComplexGram_nullIndex, n1SignedComplexEnergy_minus_four,
    n1SignedComplexEnergy_minus_four_twentyFifth, n1SignedComplexThreshold_minus_four,
    n1SignedComplexThreshold_minus_four_twentyFifth, ?_, ?_, ?_⟩
  · norm_num
  · exact fun t ht => n1SignedComplexRepair_posDef_iff_above_minus_four t ht
  · exact fun t ht => n1SignedComplexRepair_posDef_iff_above_minus_four_twentyFifth t ht

end

end GaloisForLFunctions.HTGeometry
