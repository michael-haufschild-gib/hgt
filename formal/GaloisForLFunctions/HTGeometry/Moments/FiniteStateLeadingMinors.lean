import GaloisForLFunctions.HTGeometry.Moments.LeadingMinorRecurrence
import GaloisForLFunctions.HTGeometry.LinearRecurrenceStateSpace

/-!
# Leading determinants detect finite state dimension

The finite Hankel leading-minor theorem turns eventual vanishing of the leading
determinants into a state-space realization, over any field. The largest nonzero
leading block equals the least realization dimension and the least recurrence order.
No positivity, diagonalizability, or nonzero initial observation is required.
-/

open scoped BigOperators Matrix

namespace HTGeometry.FiniteHankel

variable {K : Type*} [Field K]

/-- A relation between reachable states annihilates every shifted observation. -/
theorem observation_relation {d q : ℕ} (A : Matrix (Fin d) (Fin d) K)
    (input output : Fin d → K) (cols : Fin q → ℕ) (c : Fin q → K)
    (hc : (∑ j, c j • ((A ^ cols j) *ᵥ input)) = 0) (r : ℕ) :
    ∑ j, c j * algebraicStateSpaceResponse A input output (r + cols j) = 0 := by
  simp_rw [algebraicStateSpaceResponse_add]
  calc
    ∑ j, c j * (output ⬝ᵥ (A ^ r) *ᵥ ((A ^ cols j) *ᵥ input)) =
        output ⬝ᵥ (A ^ r) *ᵥ (∑ j, c j • ((A ^ cols j) *ᵥ input)) := by
      rw [Matrix.mulVec_sum, dotProduct_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [Matrix.mulVec_smul]
      simp only [dotProduct, Pi.smul_apply, smul_eq_mul]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      ring
    _ = 0 := by rw [hc, Matrix.mulVec_zero, dotProduct_zero]

/-- Every leading block larger than the state dimension is singular. -/
theorem leading_tail_zero_of_stateSpace {d : ℕ} {s : ℕ → K}
    (hs : AlgebraicStateSpaceDimensionAtMost d s) :
    ∀ n, d < n → leadingDet s n = 0 := by
  obtain ⟨A, input, output, rfl⟩ := hs
  intro n hn
  by_contra hdet
  have hli := ((independent_iff_exists_leading_det
    (algebraicStateSpaceResponse A input output) (d + 1) n).mpr
      ⟨n, by omega, le_rfl, hdet⟩).2
  obtain ⟨c, hc, j, hj⟩ := exists_algebraicStateSpace_controllability_relation A input
  apply hj
  apply Fintype.linearIndependent_iff.mp hli c _ j
  funext r
  simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, column, Pi.zero_apply]
    using observation_relation A input output Fin.val c hc r.val

/-- Arbitrary observation and shift indices also give singular oversized minors. -/
theorem arbitrary_minor_zero_of_stateSpace {d q : ℕ} {s : ℕ → K}
    (hs : AlgebraicStateSpaceDimensionAtMost d s) (hdq : d < q)
    (rows cols : Fin q → ℕ) : (Matrix.of fun i j => s (rows i + cols j)).det = 0 := by
  obtain ⟨A, input, output, rfl⟩ := hs
  have hdep : ¬ LinearIndependent K (fun j : Fin q => (A ^ cols j) *ᵥ input) := by
    intro hli
    have hb := hli.fintype_card_le_finrank
    simp only [Fintype.card_fin, Module.finrank_pi] at hb
    omega
  obtain ⟨c, hc, j, hj⟩ := Fintype.not_linearIndependent_iff.mp hdep
  apply Matrix.det_eq_zero_of_mulVec_eq_zero_of_mem_nonZeroDivisors (v := c) (i := j)
  · funext i
    simpa only [Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.zero_apply, mul_comm]
      using observation_relation A input output cols c hc (rows i)
  · simpa only [mem_nonZeroDivisors_iff_ne_zero] using hj

/-- The zero-order case of the recurrence realization is the zero-dimensional state. -/
theorem stateSpace_of_recurrence (E : LinearRecurrence K) {s : ℕ → K}
    (hE : E.IsSolution s) : AlgebraicStateSpaceDimensionAtMost E.order s := by
  by_cases h : E.order = 0
  · have hs : s = 0 := by
      funext n
      simpa [LinearRecurrence.IsSolution, h] using hE n
    rw [h, hs]
    refine ⟨0, 0, 0, ?_⟩
    funext n
    simp [algebraicStateSpaceResponse]
  · exact algebraicStateSpaceDimensionAtMost_of_linearRecurrence E hE h

/-- A bound on leading determinant sizes is exactly a bound on finite state dimension. -/
theorem leading_tail_zero_iff_stateSpace (s : ℕ → K) (B : ℕ) :
    (∀ n, B < n → leadingDet s n = 0) ↔
      ∃ d ≤ B, AlgebraicStateSpaceDimensionAtMost d s := by
  constructor
  · intro h
    obtain ⟨E, hEB, hE⟩ := (leading_tail_zero_iff_recurrence s B).mp h
    exact ⟨E.order, hEB, stateSpace_of_recurrence E hE⟩
  · rintro ⟨d, hd, hs⟩ n hn
    exact leading_tail_zero_of_stateSpace hs n (by omega)

/-- Finite state dimension and finite recurrence order have the same sharp bounds. -/
theorem stateSpace_iff_recurrence (s : ℕ → K) (B : ℕ) :
    (∃ d ≤ B, AlgebraicStateSpaceDimensionAtMost d s) ↔
      ∃ E : LinearRecurrence K, E.order ≤ B ∧ E.IsSolution s := by
  rw [← leading_tail_zero_iff_stateSpace, leading_tail_zero_iff_recurrence]

/-- A nonzero leading determinant lower-bounds every realization dimension. -/
theorem leading_nonzero_le_stateSpace {s : ℕ → K} {m d : ℕ}
    (hm : leadingDet s m ≠ 0) (hs : AlgebraicStateSpaceDimensionAtMost d s) : m ≤ d := by
  by_contra h
  exact hm (leading_tail_zero_of_stateSpace hs m (by omega))

/-- The last nonzero leading determinant gives a realization of the least possible dimension. -/
theorem last_nonzero_leading_det_minimal_stateSpace (s : ℕ → K) (m : ℕ)
    (hm : leadingDet s m ≠ 0) (htail : ∀ n, m < n → leadingDet s n = 0) :
    AlgebraicStateSpaceDimensionAtMost m s ∧
      ∀ d, AlgebraicStateSpaceDimensionAtMost d s → m ≤ d := by
  obtain ⟨c, hc⟩ := recurrence_of_last_nonzero_leading_det s m hm htail
  exact ⟨stateSpace_of_recurrence ⟨m, c⟩ hc,
    fun _ hs => leading_nonzero_le_stateSpace hm hs⟩

#print axioms leading_tail_zero_iff_stateSpace
#print axioms stateSpace_iff_recurrence
#print axioms last_nonzero_leading_det_minimal_stateSpace

end HTGeometry.FiniteHankel
