import GaloisForLFunctions.HTGeometry.PaperDegenerationDomain
import GaloisForLFunctions.HTGeometry.PaperStableCoordinate.SourcePresentation
import GaloisForLFunctions.HTGeometry.PaperOriginalInitialForms

/-!
# Exact multiplication in the original signed filtration

The explicit source presentation transports each filtration layer to the
literal four-variable polynomial ring. The proved associated-graded domain
prevents cancellation of a product's leading symbol. Consequently signed
degrees add, and multiplication by the source polynomial shifts every
filtration layer down by exactly one.
-/

namespace GaloisForLFunctions.HTGeometry

open StableCoordinate Obstruction AssociatedGradedPresentation

noncomputable section

/-- Exact layer transport through the proved source presentation. -/
theorem paperOriginalFiltration_source_iff (p : R 4) (d : ℤ) :
    p ∈ paperOriginalFiltration d ↔
      sourcePresentation.symm p ∈ Filtration.imagePiece (quotientMap ℂ) d := by
  unfold paperOriginalFiltration Filtration.imagePiece
  rw [Submodule.mem_map, Submodule.mem_map]
  constructor
  · rintro ⟨q, hq, heq⟩
    refine ⟨q, hq, ?_⟩
    apply sourcePresentation.injective
    change paperOriginalPresentation q = sourcePresentation (sourcePresentation.symm p)
    simpa only [AlgEquiv.apply_symm_apply, AlgHom.toLinearMap_apply] using heq
  · rintro ⟨q, hq, heq⟩
    refine ⟨q, hq, ?_⟩
    have h := congrArg sourcePresentation heq
    change sourcePresentation ((quotientMap ℂ) q) = p
    simpa only [AlgEquiv.apply_symm_apply, AlgHom.toLinearMap_apply] using h

private theorem degree_mul_of_nonzero {p q : R 4} (hp : p ≠ 0) (hq : q ≠ 0) :
    paperOriginalDegree (p * q) = paperOriginalDegree p + paperOriginalDegree q := by
  let F := Filtration.imagePiece (quotientMap ℂ)
  let mono := Filtration.imagePiece_mono (quotientMap ℂ)
  obtain ⟨hp_mem, hp_prev⟩ :=
    (paperOriginalInitialDegree_iff p (paperOriginalDegree p)).mpr ⟨hp, rfl⟩
  obtain ⟨hq_mem, hq_prev⟩ :=
    (paperOriginalInitialDegree_iff q (paperOriginalDegree q)).mpr ⟨hq, rfl⟩
  have hsp : sourcePresentation.symm p ∈ F (paperOriginalDegree p) :=
    (paperOriginalFiltration_source_iff p _).mp hp_mem
  have hsq : sourcePresentation.symm q ∈ F (paperOriginalDegree q) :=
    (paperOriginalFiltration_source_iff q _).mp hq_mem
  have hsp_ne : FilteredRees.initial F mono (paperOriginalDegree p)
      ⟨sourcePresentation.symm p, hsp⟩ ≠ 0 := by
    intro h
    exact hp_prev ((paperOriginalFiltration_source_iff p _).mpr
      ((FilteredRees.initial_eq_zero_iff F mono _ _).mp h))
  have hsq_ne : FilteredRees.initial F mono (paperOriginalDegree q)
      ⟨sourcePresentation.symm q, hsq⟩ ≠ 0 := by
    intro h
    exact hq_prev ((paperOriginalFiltration_source_iff q _).mpr
      ((FilteredRees.initial_eq_zero_iff F mono _ _).mp h))
  have hprod := mul_ne_zero hsp_ne hsq_ne
  rw [FilteredRees.initial_mul] at hprod
  have hpq : sourcePresentation.symm (p * q) ∈
      F (paperOriginalDegree p + paperOriginalDegree q) := by
    simpa only [map_mul] using SetLike.mul_mem_graded hsp hsq
  have hpq_ne : FilteredRees.initial F mono (paperOriginalDegree p + paperOriginalDegree q)
      ⟨sourcePresentation.symm (p * q), hpq⟩ ≠ 0 := by
    simpa only [map_mul] using hprod
  apply ((paperOriginalInitialDegree_iff (p * q) _).mp ⟨
    (paperOriginalFiltration_source_iff (p * q) _).mpr hpq, ?_⟩).2
  intro h
  apply hpq_ne
  exact (FilteredRees.initial_eq_zero_iff F mono _ _).mpr
    ((paperOriginalFiltration_source_iff (p * q) _).mp h)

/-- Adding a bottom value makes the multiplicative degree law valid also at zero. -/
def paperOriginalSignedDegree (p : R 4) : WithBot ℤ :=
  if p = 0 then ⊥ else (paperOriginalDegree p : WithBot ℤ)

@[simp] theorem paperOriginalSignedDegree_zero : paperOriginalSignedDegree 0 = ⊥ := by
  simp [paperOriginalSignedDegree]

@[simp] theorem paperOriginalSignedDegree_one : paperOriginalSignedDegree 1 = 0 := by
  have h : paperOriginalDegree 1 = 0 := by simpa using paperOriginalDegree_pow 0
  simp [paperOriginalSignedDegree, h]

/-- Unconditional degree addition, with zero represented by bottom. -/
theorem paperOriginalSignedDegree_mul (p q : R 4) :
    paperOriginalSignedDegree (p * q) =
      paperOriginalSignedDegree p + paperOriginalSignedDegree q := by
  by_cases hp : p = 0
  · simp [hp]
  by_cases hq : q = 0
  · simp [hq]
  simp [paperOriginalSignedDegree, hp, hq, mul_ne_zero hp hq,
    degree_mul_of_nonzero hp hq]

/-- Addition satisfies the nonarchimedean degree bound on the literal ring. -/
theorem paperOriginalSignedDegree_add_le (p q : R 4) :
    paperOriginalSignedDegree (p + q) ≤
      max (paperOriginalSignedDegree p) (paperOriginalSignedDegree q) := by
  by_cases hp : p = 0
  · simp [hp]
  by_cases hq : q = 0
  · simp [hq]
  by_cases hpq : p + q = 0
  · simp [hpq]
  have hmp : p ∈ paperOriginalFiltration (max (paperOriginalDegree p) (paperOriginalDegree q)) :=
    (paperOriginalFiltration_mem_iff p _).mpr (Or.inr (le_max_left _ _))
  have hmq : q ∈ paperOriginalFiltration (max (paperOriginalDegree p) (paperOriginalDegree q)) :=
    (paperOriginalFiltration_mem_iff q _).mpr (Or.inr (le_max_right _ _))
  have hdeg := ((paperOriginalFiltration_mem_iff (p + q) _).mp
    ((paperOriginalFiltration _).add_mem hmp hmq)).resolve_left hpq
  simpa only [paperOriginalSignedDegree, if_neg hp, if_neg hq, if_neg hpq,
    ← WithBot.coe_max, WithBot.coe_le_coe] using hdeg

/-- The source polynomial has exact signed degree minus one. -/
theorem paperOriginalSignedDegree_f : paperOriginalSignedDegree f = ((-1 : ℤ) : WithBot ℤ) := by
  have hf : paperOriginalDegree f = -1 := by
    simpa using paperOriginalDegree_pow 1
  simp [paperOriginalSignedDegree, paperOriginalPolynomial_ne_zero, hf]

/-- Every filtration layer shifts exactly, including its zero element. -/
theorem paperOriginalFiltration_mul_f_iff (p : R 4) (d : ℤ) :
    f * p ∈ paperOriginalFiltration d ↔ p ∈ paperOriginalFiltration (d + 1) := by
  by_cases hp : p = 0
  · simp [hp]
  have hf : paperOriginalDegree f = -1 := by
    simpa using paperOriginalDegree_pow 1
  rw [paperOriginalFiltration_mem_iff, paperOriginalFiltration_mem_iff]
  simp only [mul_ne_zero paperOriginalPolynomial_ne_zero hp, hp, false_or,
    degree_mul_of_nonzero paperOriginalPolynomial_ne_zero hp, hf]
  omega

/-- Arbitrary powers give the exact shift, not merely a divisibility bound. -/
theorem paperOriginalFiltration_mul_f_pow_iff (p : R 4) (n : ℕ) (d : ℤ) :
    f ^ n * p ∈ paperOriginalFiltration d ↔ p ∈ paperOriginalFiltration (d + n) := by
  induction n generalizing d with
  | zero => simp
  | succ n ih =>
      rw [pow_succ', mul_assoc, paperOriginalFiltration_mul_f_iff, ih]
      simp only [Nat.cast_add, Nat.cast_one, add_comm, add_left_comm]

end

end GaloisForLFunctions.HTGeometry
