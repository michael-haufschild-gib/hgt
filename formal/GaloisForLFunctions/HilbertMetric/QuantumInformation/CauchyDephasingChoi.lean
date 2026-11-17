import GaloisForLFunctions.HilbertMetric.QuantumInformation.CauchyDephasingLimit
import Mathlib.Analysis.Matrix.Order

/-!
# Choi entanglement boundary of Cauchy dephasing

The actual channel action on matrix units gives a positive Choi matrix with
identity marginal. Every finite iterate in dimension at least two has a
strictly negative two-coordinate partial-transpose minor. The equal-rate
pinching limit admits a finite positive product-Gram decomposition exactly
when the rates are injective; coordinate projections give the decomposition.

This separates Choi positivity from partial-transpose positivity in the
states-over-time construction of Matt Hoogsteder-Riera.
-/

noncomputable section
open Matrix Filter
open scoped Topology ComplexOrder BigOperators Kronecker
namespace GaloisForLFunctions.HilbertMetric.CauchyDephasing

/-- The unnormalized maximally entangled vector as a one-row Gram factor. -/
def entangledRow (n : ℕ) : Matrix (Fin 1) (Fin n × Fin n) ℂ :=
  fun _ i => if i.1 = i.2 then 1 else 0

/-- Choi matrix of the finite Cauchy dephasing iterate. -/
def iterateChoi {n : ℕ} (k : ℕ) (r : Fin n → ℝ) :
    Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ :=
  fun i j => (coherence (r i.1) (r j.1) : ℂ) ^ k *
    ((entangledRow n)ᴴ * entangledRow n) i j

/-- Partial transpose on the first tensor factor. -/
def partialTransposeFirst {n m : ℕ}
    (A : Matrix (Fin n × Fin m) (Fin n × Fin m) ℂ) :
    Matrix (Fin n × Fin m) (Fin n × Fin m) ℂ :=
  fun i j => A (j.1, i.2) (i.1, j.2)

theorem iterateChoi_apply {n : ℕ} (k : ℕ) (r : Fin n → ℝ)
    (i j : Fin n × Fin n) :
    iterateChoi k r i j =
      if i.1 = i.2 ∧ j.1 = j.2 then (coherence (r i.1) (r j.1) : ℂ) ^ k else 0 := by
  by_cases hi : i.1 = i.2 <;> by_cases hj : j.1 = j.2 <;>
    simp [iterateChoi, entangledRow, Matrix.mul_apply, Matrix.conjTranspose_apply, hi, hj]

/-- The Choi matrix is the actual channel action on matrix units. -/
theorem iterateChoi_channelUnit {n : ℕ} (k : ℕ) (r : Fin n → ℝ)
    (i j a b : Fin n) :
    iterateChoi k r (i, a) (j, b) =
      channelPower k r (Matrix.single i j 1) a b := by
  rw [iterateChoi_apply]
  by_cases hi : i = a <;> by_cases hj : j = b
  · subst a; subst b
    simp [channelPower, Matrix.single]
  · simp [channelPower, Matrix.single, hi, hj]
  · simp [channelPower, Matrix.single, hi, hj]
  · simp [channelPower, Matrix.single, hi, hj]

/-- Every finite Choi matrix is positive, with no input positivity premise. -/
theorem iterateChoi_posSemidef {n : ℕ} (k : ℕ) (r : Fin n → ℝ) :
    (iterateChoi k r).PosSemidef := by
  induction k with
  | zero =>
    have he : iterateChoi 0 r = (entangledRow n)ᴴ * entangledRow n := by
      ext i j
      simp only [iterateChoi, pow_zero, one_mul]
    rw [he]
    exact posSemidef_conjTranspose_mul_self _
  | succ k ih =>
    have he : iterateChoi (k + 1) r =
        iterateChoi k r ⊙ (symbol r).submatrix Prod.fst Prod.fst := by
      ext i j
      simp only [iterateChoi, Matrix.hadamard_apply, Matrix.submatrix_apply, symbol, pow_succ]
      ring
    rw [he]
    exact ih.hadamard ((symbol_posSemidef r).submatrix Prod.fst)

/-- The Choi marginal is the identity, expressing exact trace preservation. -/
theorem iterateChoi_partialTrace {n : ℕ} (k : ℕ) (r : Fin n → ℝ) :
    (fun i j => ∑ a : Fin n, iterateChoi k r (i, a) (j, a)) =
      (1 : Matrix (Fin n) (Fin n) ℂ) := by
  ext i j
  simp_rw [iterateChoi_apply]
  by_cases h : i = j
  · subst j
    simp [coherence_self]
  · have hn (a : Fin n) : ¬ (i = a ∧ j = a) := fun ha => h (ha.1.trans ha.2.symm)
    simp only [hn, if_false, Finset.sum_const_zero, Matrix.one_apply_ne h]

private theorem partialTranspose_pair_det {n : ℕ} (k : ℕ) (r : Fin n → ℝ)
    (i j : Fin n) (hij : i ≠ j) :
    (((partialTransposeFirst (iterateChoi k r)).submatrix
      ![(i, j), (j, i)] ![(i, j), (j, i)]).det) =
        -((coherence (r i) (r j) : ℂ) ^ k) ^ 2 := by
  rw [Matrix.det_fin_two]
  simp only [Matrix.submatrix_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    partialTransposeFirst, iterateChoi_apply, hij, Ne.symm hij,
    and_self, if_true, if_false, coherence_symm (r j) (r i), zero_mul, zero_sub, pow_two]

/-- Every finite iterate in dimension at least two has a partial transpose that is not positive semidefinite. -/
theorem iterateChoi_not_positive_partialTranspose (n k : ℕ) (r : Fin (n + 2) → ℝ) :
    ¬ (partialTransposeFirst (iterateChoi k r)).PosSemidef := by
  intro h
  let i : Fin (n + 2) := ⟨0, by omega⟩
  let j : Fin (n + 2) := ⟨1, by omega⟩
  have hij : i ≠ j := by
    intro h
    have hv := congrArg Fin.val h
    change (0 : ℕ) = 1 at hv
    omega
  have hd := (h.submatrix ![(i, j), (j, i)]).det_nonneg
  rw [partialTranspose_pair_det k r i j hij] at hd
  have hr : 0 ≤ -(coherence (r i) (r j) ^ k) ^ 2 := by exact_mod_cast hd
  have hp := sq_pos_of_pos (pow_pos (coherence_pos (r i) (r j)) k)
  linarith only [hr, hp]

/-- Choi matrix of the limiting equal-rate projection. -/
def pinchingChoi {n : ℕ} (r : Fin n → ℝ) :
    Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ := by
  classical
  exact fun i j => if i.1 = i.2 ∧ j.1 = j.2 ∧ r i.1 = r j.1 then 1 else 0

/-- Choi matrices converge to the exact equal-rate block limit. -/
theorem iterateChoi_tendsto {n : ℕ} (r : Fin n → ℝ) :
    Tendsto (fun k => iterateChoi k r) atTop (𝓝 (pinchingChoi r)) := by
  classical
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_pi_nhds.mpr
  intro j
  have h := tendsto_pi_nhds.mp (tendsto_pi_nhds.mp
    (channelPower_tendsto_pinching r (fun _ _ => 1)) i.1) j.1
  by_cases hi : i.1 = i.2 <;> by_cases hj : j.1 = j.2
  · simpa only [iterateChoi_apply, hi, hj, true_and, if_true, pinchingChoi,
      channelPower, mul_one, pinching] using h
  · simp only [iterateChoi_apply, hi, hj, and_false, if_false, pinchingChoi,
      false_and, tendsto_const_nhds]
  · simp only [iterateChoi_apply, hi, hj, false_and, if_false, pinchingChoi,
      tendsto_const_nhds]
  · simp only [iterateChoi_apply, hi, hj, false_and, if_false, pinchingChoi,
      tendsto_const_nhds]

private theorem pinchingChoi_pair_det {n : ℕ} (r : Fin n → ℝ)
    (i j : Fin n) (hij : i ≠ j) :
    (((partialTransposeFirst (pinchingChoi r)).submatrix
      ![(i, j), (j, i)] ![(i, j), (j, i)]).det) =
        if r i = r j then -1 else 0 := by
  classical
  rw [Matrix.det_fin_two]
  by_cases h : r i = r j <;>
    simp [partialTransposeFirst, pinchingChoi, hij, Ne.symm hij, h, eq_comm]

/-- The limiting Choi partial transpose is positive exactly when no equal-rate coherence survives. -/
theorem pinchingChoi_positive_partialTranspose_iff {n : ℕ} (r : Fin n → ℝ) :
    (partialTransposeFirst (pinchingChoi r)).PosSemidef ↔ Function.Injective r := by
  classical
  constructor
  · intro h i j heq
    by_contra hij
    have hd := (h.submatrix ![(i, j), (j, i)]).det_nonneg
    rw [pinchingChoi_pair_det r i j hij, if_pos heq] at hd
    norm_num at hd
  · intro hinj
    have he : partialTransposeFirst (pinchingChoi r) =
        diagonal (fun i : Fin n × Fin n => if i.1 = i.2 then (1 : ℂ) else 0) := by
      ext i j
      simp only [partialTransposeFirst, pinchingChoi, Matrix.diagonal_apply]
      by_cases h : i = j
      · subst j
        simp only [and_true, and_self, if_true]
      · have hn : ¬ (j.1 = i.2 ∧ i.1 = j.2 ∧ r j.1 = r i.1) := by
          rintro ⟨h1, h2, h3⟩
          have hr := hinj h3
          exact h (Prod.ext hr.symm (h1.symm.trans (hr.trans h2)))
        simp only [if_neg h, if_neg hn]
    rw [he]
    apply Matrix.PosSemidef.diagonal
    intro i
    change (0 : ℂ) ≤ if i.1 = i.2 then 1 else 0
    split_ifs <;> norm_num

/-- An arbitrary finite sum of positive product Grams. -/
def finiteProductGram {n m : ℕ}
    (A B : Fin m → Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ :=
  ∑ i, ((A i)ᴴ * A i) ⊗ₖ ((B i)ᴴ * B i)

/-- Positive product decompositions remain positive under partial transpose. -/
theorem finiteProductGram_partialTranspose_posSemidef {n m : ℕ}
    (A B : Fin m → Matrix (Fin n) (Fin n) ℂ) :
    (partialTransposeFirst (finiteProductGram A B)).PosSemidef := by
  have he : partialTransposeFirst (finiteProductGram A B) =
      ∑ i, (((A i)ᴴ * A i)ᵀ) ⊗ₖ ((B i)ᴴ * B i) := by
    ext i j
    simp only [partialTransposeFirst, finiteProductGram, Matrix.sum_apply]
    apply Finset.sum_congr rfl
    intro k _
    rfl
  rw [he]
  apply Matrix.posSemidef_sum Finset.univ
  intro i _
  exact (posSemidef_conjTranspose_mul_self (A i)).transpose.kronecker
    (posSemidef_conjTranspose_mul_self (B i))

/-- No finite dephasing iterate admits a positive product-Gram decomposition. -/
theorem iterateChoi_ne_finiteProductGram (n k m : ℕ) (r : Fin (n + 2) → ℝ)
    (A B : Fin m → Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ) :
    iterateChoi k r ≠ finiteProductGram A B := by
  intro h
  apply iterateChoi_not_positive_partialTranspose n k r
  rw [h]
  exact finiteProductGram_partialTranspose_posSemidef A B

/-- Coordinate projections supply product factors for completely dephased Choi matrices. -/
def coordinateFactor {n : ℕ} (a : Fin n) : Matrix (Fin n) (Fin n) ℂ :=
  diagonal fun i => if a = i then 1 else 0

private theorem coordinateFactor_gram {n : ℕ} (a : Fin n) :
    (coordinateFactor a)ᴴ * coordinateFactor a = coordinateFactor a := by
  have hc : (coordinateFactor a)ᴴ = coordinateFactor a := by
    ext i j
    by_cases h : i = j
    · subst j
      simp [coordinateFactor, Matrix.conjTranspose_apply]
    · simp [coordinateFactor, Matrix.conjTranspose_apply, h, Ne.symm h]
  rw [hc, coordinateFactor, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  split_ifs <;> norm_num

private theorem coordinateProductGram_apply {n : ℕ} (i j : Fin n × Fin n) :
    finiteProductGram (@coordinateFactor n) (@coordinateFactor n) i j =
      if i.1 = i.2 ∧ i = j then 1 else 0 := by
  simp only [finiteProductGram, coordinateFactor_gram, Matrix.sum_apply]
  change (∑ a, coordinateFactor a i.1 j.1 * coordinateFactor a i.2 j.2) = _
  simp only [coordinateFactor, Matrix.diagonal_apply]
  by_cases h1 : i.1 = j.1 <;> by_cases h2 : i.2 = j.2
  · have hij : i = j := Prod.ext h1 h2
    subst j
    simp only [if_true, and_true]
    by_cases hi : i.1 = i.2
    · simp [hi]
    · have hz (a : Fin n) :
          (if a = i.1 then (1 : ℂ) else 0) * (if a = i.2 then 1 else 0) = 0 := by
        by_cases ha : a = i.1
        · subst a
          simp only [if_neg hi, mul_zero]
        · simp only [if_neg ha, zero_mul]
      simp only [hz, Finset.sum_const_zero, if_neg hi]
  · have hij : i ≠ j := fun h => h2 (congrArg Prod.snd h)
    simp only [if_pos h1, if_neg h2, mul_zero, Finset.sum_const_zero,
      hij, and_false, if_false]
  · have hij : i ≠ j := fun h => h1 (congrArg Prod.fst h)
    simp only [if_neg h1, zero_mul, Finset.sum_const_zero, hij, and_false, if_false]
  · have hij : i ≠ j := fun h => h1 (congrArg Prod.fst h)
    simp only [if_neg h1, zero_mul, Finset.sum_const_zero, hij, and_false, if_false]

/-- Exactly the injective-rate limit admits a finite positive product decomposition. -/
theorem pinchingChoi_finiteProductGram_iff {n : ℕ} (r : Fin n → ℝ) :
    (∃ (m : ℕ) (A B : Fin m → Matrix (Fin n) (Fin n) ℂ),
      pinchingChoi r = finiteProductGram A B) ↔ Function.Injective r := by
  classical
  constructor
  · rintro ⟨m, A, B, h⟩
    apply (pinchingChoi_positive_partialTranspose_iff r).mp
    rw [h]
    exact finiteProductGram_partialTranspose_posSemidef A B
  · intro hr
    refine ⟨n, coordinateFactor, coordinateFactor, ?_⟩
    ext i j
    rw [coordinateProductGram_apply]
    change (if i.1 = i.2 ∧ j.1 = j.2 ∧ r i.1 = r j.1 then (1 : ℂ) else 0) = _
    have he : (i.1 = i.2 ∧ j.1 = j.2 ∧ r i.1 = r j.1) ↔
        (i.1 = i.2 ∧ i = j) := by
      constructor
      · rintro ⟨hi, hj, hrate⟩
        exact ⟨hi, Prod.ext (hr hrate) (hi.symm.trans ((hr hrate).trans hj))⟩
      · rintro ⟨hi, rfl⟩
        exact ⟨hi, hi, rfl⟩
    simp only [he]

#print axioms iterateChoi_channelUnit
#print axioms iterateChoi_posSemidef
#print axioms iterateChoi_partialTrace
#print axioms iterateChoi_not_positive_partialTranspose
#print axioms iterateChoi_tendsto
#print axioms pinchingChoi_positive_partialTranspose_iff
#print axioms finiteProductGram_partialTranspose_posSemidef
#print axioms iterateChoi_ne_finiteProductGram
#print axioms pinchingChoi_finiteProductGram_iff
end GaloisForLFunctions.HilbertMetric.CauchyDephasing
