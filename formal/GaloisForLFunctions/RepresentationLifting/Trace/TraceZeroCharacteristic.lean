import GaloisForLFunctions.RepresentationLifting.Trace.ProjectiveTraceDuality

/-!
# The exact characteristic boundary for trace-zero self-duality

Over a field, the trace-zero radical is zero unless the matrix size vanishes
in the field; in that case it is exactly the scalar line. Trace-zero tests
still determine projective matrices in either case.
-/

namespace GaloisForLFunctions.RepresentationLifting

variable {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]

/-- A radical element is zero, or the dimension vanishes and the element is scalar. -/
theorem traceZero_field_radical_iff (p : ι) (A : Matrix ι ι K) :
    (A.trace = 0 ∧ ∀ B : traceZeroMatrices K ι, (A * B.val).trace = 0) ↔
      A = 0 ∨ ((Fintype.card ι : K) = 0 ∧ ∃ c : K, A = c • (1 : Matrix ι ι K)) := by
  rw [traceZero_radical_iff p]
  constructor
  · rintro ⟨c, hc, rfl⟩
    rcases mul_eq_zero.mp hc with hc | hn
    · exact Or.inl (by rw [hc, zero_smul])
    · exact Or.inr ⟨hn, c, rfl⟩
  · rintro (rfl | ⟨hn, c, rfl⟩)
    · exact ⟨0, zero_mul _, (zero_smul _ _).symm⟩
    · exact ⟨c, by rw [hn, mul_zero], rfl⟩

/-- The trace-zero self-pairing degenerates exactly when characteristic divides dimension. -/
theorem traceZero_nonzero_radical_iff (p : ι) :
    (∃ A : Matrix ι ι K, A ≠ 0 ∧ A.trace = 0 ∧
      ∀ B : traceZeroMatrices K ι, (A * B.val).trace = 0) ↔
      (Fintype.card ι : K) = 0 := by
  constructor
  · rintro ⟨A, hA, ht⟩
    rcases (traceZero_field_radical_iff p A).mp ht with hz | ⟨hn, _⟩
    · exact (hA hz).elim
    · exact hn
  · intro hn
    refine ⟨1, ?_, (traceZero_field_radical_iff p 1).mpr (Or.inr ⟨hn, 1, ?_⟩)⟩
    · intro hz
      have he := congrArg (fun M : Matrix ι ι K => M p p) hz
      exact (one_ne_zero : (1 : K) ≠ 0)
        (by simpa only [Matrix.one_apply_eq, Matrix.zero_apply] using he)
    · exact (one_smul _ _).symm

/-- Nondegeneracy is equivalent to the dimension being nonzero in the field. -/
theorem traceZero_self_pairing_nondegenerate_iff (p : ι) :
    (∀ A : traceZeroMatrices K ι,
      (∀ B : traceZeroMatrices K ι, (A.val * B.val).trace = 0) → A = 0) ↔
      (Fintype.card ι : K) ≠ 0 := by
  constructor
  · intro h hn
    obtain ⟨A, hA, ht, ho⟩ := (traceZero_nonzero_radical_iff p).mpr hn
    have hz := h ⟨A, ht⟩ ho
    exact hA (congrArg Subtype.val hz)
  · intro hn A hA
    rcases (traceZero_field_radical_iff p A.val).mp ⟨A.property, hA⟩ with hz | ⟨hd, _⟩
    · exact Subtype.ext hz
    · exact (hn hd).elim

#print axioms traceZero_nonzero_radical_iff
#print axioms traceZero_self_pairing_nondegenerate_iff

end GaloisForLFunctions.RepresentationLifting
