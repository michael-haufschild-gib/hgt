import GaloisForLFunctions.HTGeometry.PaperOriginalFiltrationSeparation
import GaloisForLFunctions.HTGeometry.PaperStableCoordinate.Degree
import GaloisForLFunctions.HTGeometry.PaperStableCoordinate.FilteredRees
import GaloisForLFunctions.HTGeometry.PaperStableCoordinate.IntegerFiltrationDegree

/-!
The actual original polynomial algebra has a genuine least signed filtration
degree for every nonzero element and a nonzero Rees symbol at that degree.
The powers of the literal source polynomial have degree exactly `-n`, so the
negative layers contain nonzero elements at arbitrarily large negative depth.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open StableCoordinate

def paperOriginalDegree (p : R 4) : ℤ :=
  IntegerFiltration.degree (fun d => (paperOriginalFiltration d : Set (R 4))) p

instance paperOriginalFiltrationGradedMonoid : SetLike.GradedMonoid paperOriginalFiltration := by
  unfold paperOriginalFiltration
  infer_instance

private theorem original_separated (p : R 4)
    (h : ∀ d : ℤ, p ∈ paperOriginalFiltration d) : p = 0 :=
  (paperOriginalFiltration_residual_iff_zero p).mp h

/-- Layer membership is completely detected by zero or the least signed degree. -/
theorem paperOriginalFiltration_mem_iff (p : R 4) (d : ℤ) :
    p ∈ paperOriginalFiltration d ↔ p = 0 ∨ paperOriginalDegree p ≤ d := by
  by_cases hp : p = 0
  · simp [hp]
  · simpa [paperOriginalDegree, hp] using
      IntegerFiltration.mem_iff_degree_le
        (fun e => (paperOriginalFiltration e : Set (R 4)))
        (fun _ _ h => paperOriginalFiltration_mono h)
        paperOriginalFiltration_exhaustive original_separated hp d

/-- The first occupied layer is exactly the degree of a nonzero polynomial. -/
theorem paperOriginalInitialDegree_iff (p : R 4) (d : ℤ) :
    (p ∈ paperOriginalFiltration d ∧ p ∉ paperOriginalFiltration (d - 1)) ↔
      p ≠ 0 ∧ paperOriginalDegree p = d := by
  by_cases hp : p = 0
  · simp [hp]
  · simpa [paperOriginalDegree, hp] using
      (IntegerFiltration.degree_eq_iff_initial
        (fun e => (paperOriginalFiltration e : Set (R 4)))
        (fun _ _ h => paperOriginalFiltration_mono h)
        paperOriginalFiltration_exhaustive original_separated hp d).symm

theorem paperOriginalInitial_exists_unique (p : R 4) :
    p ≠ 0 ↔ ∃! d : ℤ,
      p ∈ paperOriginalFiltration d ∧ p ∉ paperOriginalFiltration (d - 1) := by
  constructor
  · intro hp
    refine ⟨paperOriginalDegree p, (paperOriginalInitialDegree_iff _ _).mpr ⟨hp, rfl⟩, ?_⟩
    intro e he
    exact ((paperOriginalInitialDegree_iff _ _).mp he).2.symm
  · rintro ⟨d, hd, _⟩
    exact ((paperOriginalInitialDegree_iff _ _).mp hd).1

/-- Every nonzero original polynomial is detected by an actual Rees symbol. -/
theorem paperOriginalNonzeroSymbol_iff (p : R 4) :
    p ≠ 0 ↔ ∃ (d : ℤ) (hp : p ∈ paperOriginalFiltration d),
      FilteredRees.initial paperOriginalFiltration paperOriginalFiltration_mono d ⟨p, hp⟩ ≠ 0 := by
  constructor
  · intro hp
    obtain ⟨d, hd, _⟩ := (paperOriginalInitial_exists_unique p).mp hp
    refine ⟨d, hd.1, ?_⟩
    intro hz
    exact hd.2 ((FilteredRees.initial_eq_zero_iff paperOriginalFiltration
      paperOriginalFiltration_mono d ⟨p, hd.1⟩).mp hz)
  · rintro ⟨d, hp, hsymbol⟩ rfl
    exact hsymbol ((FilteredRees.initial_eq_zero_iff paperOriginalFiltration
      paperOriginalFiltration_mono d ⟨0, hp⟩).mpr
      ((paperOriginalFiltration (d - 1)).zero_mem))

theorem paperOriginalPolynomial_ne_zero : f ≠ 0 := by
  intro hf
  have h := f_totalDegree
  rw [hf, MvPolynomial.totalDegree_zero] at h
  omega

theorem paperOriginalPolynomial_mem_negative_one : f ∈ paperOriginalFiltration (-1) := by
  simpa only [paperOriginalFiltration, paperOriginalPresentation_X_zero] using
    Filtration.image_X_zero_mem_neg_one paperOriginalPresentation

theorem paperOriginalPolynomial_pow_mem (n : ℕ) :
    f ^ n ∈ paperOriginalFiltration (-(n : ℤ)) := by
  induction n with
  | zero =>
      simpa only [paperOriginalFiltration, pow_zero, Nat.cast_zero, neg_zero] using
        SetLike.one_mem_graded (Filtration.imagePiece paperOriginalPresentation)
  | succ n ih =>
      simpa only [paperOriginalFiltration, pow_succ, Nat.cast_add, Nat.cast_one, neg_add] using
        Filtration.mul_mem_imagePiece paperOriginalPresentation ih
          paperOriginalPolynomial_mem_negative_one

/-- The powers cannot fall even one layer below their displayed negative degree. -/
theorem paperOriginalPolynomial_pow_not_mem_previous (n : ℕ) :
    f ^ n ∉ paperOriginalFiltration (-(n : ℤ) - 1) := by
  intro h
  have hlayer : f ^ n ∈ paperOriginalFiltration (-((n + 1 : ℕ) : ℤ)) := by
    simpa only [Nat.cast_add, Nat.cast_one, neg_add, sub_eq_add_neg] using h
  obtain ⟨q, hq⟩ := Ideal.mem_span_singleton.mp (paperOriginalFiltration_negative_le (n + 1) hlayer)
  have hcancel : f ^ n * 1 = f ^ n * (f * q) := by
    rw [mul_one, ← mul_assoc, ← pow_succ]
    exact hq
  have hinv : f * q = 1 :=
    (mul_left_cancel₀ (pow_ne_zero n paperOriginalPolynomial_ne_zero) hcancel).symm
  exact paperOriginalPolynomial_not_isUnit (isUnit_iff_exists_inv.mpr ⟨q, hinv⟩)

theorem paperOriginalDegree_pow (n : ℕ) : paperOriginalDegree (f ^ n) = -(n : ℤ) :=
  ((paperOriginalInitialDegree_iff _ _).mp
    ⟨paperOriginalPolynomial_pow_mem n, paperOriginalPolynomial_pow_not_mem_previous n⟩).2

/-- Signed filtration degree is unbounded below even on nonzero polynomials. -/
theorem paperOriginalDegree_unbounded_below (b : ℤ) :
    ∃ p : R 4, p ≠ 0 ∧ paperOriginalDegree p < b := by
  refine ⟨f ^ ((-b).toNat + 1), pow_ne_zero _ paperOriginalPolynomial_ne_zero, ?_⟩
  rw [paperOriginalDegree_pow]
  omega

end GaloisForLFunctions.HTGeometry
