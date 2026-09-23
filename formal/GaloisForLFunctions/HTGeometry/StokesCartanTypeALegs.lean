import GaloisForLFunctions.HTGeometry.StokesCartanLorentzCapacity

/-!
# Type-A leg conservation for the Stokes--Cartan law

Type-A legs are written in edge-increment coordinates.  Telescoping identifies the sum of the
increments with the attached core coordinate.  Exact completion around the constant increment
splits each leg into a strictly positive fluctuation energy and the Schur weight `1/(l+1)`.
Consequently arbitrary finite type-A legs add only positive squares and cannot create a second
Cartan defect.
-/

open scoped BigOperators

namespace GaloisForLFunctions
namespace IrregularStokes

namespace TypeALeg

theorem path_completion (l : ℕ) (x : ℝ) (d : Fin (l + 1) → ℝ)
    (hsum : ∑ k, d k = x) :
    (∑ k, d k ^ (2 : ℕ)) =
      (∑ k, (d k - x / (l + 1 : ℕ)) ^ (2 : ℕ)) + x ^ (2 : ℕ) / (l + 1 : ℕ) := by
  have hm : (l + 1 : ℝ) ≠ 0 := by positivity
  have hsquares :
      (∑ k, (d k - x / (l + 1 : ℕ)) ^ (2 : ℕ)) =
        (∑ k, d k ^ (2 : ℕ)) - 2 * (x / (l + 1 : ℕ)) * (∑ k, d k) +
          (l + 1 : ℕ) * (x / (l + 1 : ℕ)) ^ (2 : ℕ) := by
    calc
      (∑ k, (d k - x / (l + 1 : ℕ)) ^ (2 : ℕ)) =
          ∑ k, (d k ^ (2 : ℕ) - 2 * (x / (l + 1 : ℕ)) * d k +
            (x / (l + 1 : ℕ)) ^ (2 : ℕ)) := by
        apply Finset.sum_congr rfl
        intro k _
        ring
      _ = (∑ k, d k ^ (2 : ℕ)) - 2 * (x / (l + 1 : ℕ)) * (∑ k, d k) +
          (l + 1 : ℕ) * (x / (l + 1 : ℕ)) ^ (2 : ℕ) := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul, ← Finset.mul_sum]
  rw [hsquares, hsum]
  field_simp
  ring

theorem family_completion {n : ℕ} (legLength : Fin n → ℕ) (x : Fin n → ℝ)
    (d : (i : Fin n) → Fin (legLength i + 1) → ℝ)
    (hsum : ∀ i, ∑ k, d i k = x i) :
    (∑ i, ∑ k, d i k ^ (2 : ℕ)) =
      ∑ i, ((∑ k, (d i k - x i / (legLength i + 1 : ℕ)) ^ (2 : ℕ)) +
        x i ^ (2 : ℕ) / (legLength i + 1 : ℕ)) := by
  apply Finset.sum_congr rfl
  intro i _
  exact path_completion (legLength i) (x i) (d i) (hsum i)

end TypeALeg

namespace CertifiedFissionDatum

noncomputable def fullPositiveQuadratic {n : ℕ} (datum : CertifiedFissionDatum n)
    (legLength : Fin n → ℕ) (x : Fin n → ℝ)
    (d : (i : Fin n) → Fin (legLength i + 1) → ℝ) : ℝ :=
  (∑ i, ∑ k, d i k ^ (2 : ℕ)) +
    ∑ e, datum.rooted.tree.canonicalCuts.length e *
      (∑ i, x i * datum.cutVector e i) ^ (2 : ℕ)

noncomputable def fullCartanQuadratic {n : ℕ} (datum : CertifiedFissionDatum n)
    (legLength : Fin n → ℕ) (x : Fin n → ℝ)
    (d : (i : Fin n) → Fin (legLength i + 1) → ℝ) : ℝ :=
  datum.fullPositiveQuadratic legLength x d -
    datum.rootDefect * datum.totalRamification x ^ (2 : ℕ)

theorem fullPositiveQuadratic_eq_completed {n : ℕ} (datum : CertifiedFissionDatum n)
    (legLength : Fin n → ℕ) (x : Fin n → ℝ)
    (d : (i : Fin n) → Fin (legLength i + 1) → ℝ)
    (hsum : ∀ i, ∑ k, d i k = x i) :
    datum.fullPositiveQuadratic legLength x d =
      (∑ i, ((∑ k, (d i k - x i / (legLength i + 1 : ℕ)) ^ (2 : ℕ)) +
        x i ^ (2 : ℕ) / (legLength i + 1 : ℕ))) +
      ∑ e, datum.rooted.tree.canonicalCuts.length e *
        (∑ i, x i * datum.cutVector e i) ^ (2 : ℕ) := by
  rw [fullPositiveQuadratic, TypeALeg.family_completion legLength x d hsum]

theorem fullCartanQuadratic_eq_completed {n : ℕ} (datum : CertifiedFissionDatum n)
    (legLength : Fin n → ℕ) (x : Fin n → ℝ)
    (d : (i : Fin n) → Fin (legLength i + 1) → ℝ)
    (hsum : ∀ i, ∑ k, d i k = x i) :
    datum.fullCartanQuadratic legLength x d =
      (∑ i, ((∑ k, (d i k - x i / (legLength i + 1 : ℕ)) ^ (2 : ℕ)) +
        x i ^ (2 : ℕ) / (legLength i + 1 : ℕ))) +
      ∑ e, datum.rooted.tree.canonicalCuts.length e *
        (∑ i, x i * datum.cutVector e i) ^ (2 : ℕ) -
      datum.rootDefect * datum.totalRamification x ^ (2 : ℕ) := by
  rw [fullCartanQuadratic, datum.fullPositiveQuadratic_eq_completed legLength x d hsum]

theorem fullPositiveQuadratic_pos {n : ℕ} (datum : CertifiedFissionDatum n)
    (legLength : Fin n → ℕ) (x : Fin n → ℝ)
    (d : (i : Fin n) → Fin (legLength i + 1) → ℝ)
    (hsum : ∀ i, ∑ k, d i k = x i)
    (hstate : x ≠ 0 ∨ d ≠ 0) :
    0 < datum.fullPositiveQuadratic legLength x d := by
  have hd : d ≠ 0 := by
    intro hdZero
    rcases hstate with hx | hd
    · apply hx
      funext i
      rw [← hsum i, hdZero]
      simp
    · exact hd hdZero
  have hex : ∃ i k, d i k ≠ 0 := by
    by_contra h
    push Not at h
    apply hd
    funext i k
    exact h i k
  obtain ⟨i, k, hik⟩ := hex
  have hpaths : 0 < ∑ i, ∑ k, d i k ^ (2 : ℕ) := by
    apply Finset.sum_pos'
    · intro j _
      exact Finset.sum_nonneg fun k _ => sq_nonneg (d j k)
    · refine ⟨i, Finset.mem_univ _, ?_⟩
      apply Finset.sum_pos'
      · intro j _
        exact sq_nonneg (d i j)
      · exact ⟨k, Finset.mem_univ _, sq_pos_of_ne_zero hik⟩
  have hcuts : 0 ≤ ∑ e, datum.rooted.tree.canonicalCuts.length e *
      (∑ i, x i * datum.cutVector e i) ^ (2 : ℕ) := by
    apply Finset.sum_nonneg
    intro e _
    exact mul_nonneg (datum.rooted.tree.canonicalCuts.length_pos e).le (sq_nonneg _)
  rw [fullPositiveQuadratic]
  exact add_pos_of_pos_of_nonneg hpaths hcuts

/-- Arbitrary finite type-A legs preserve strict positivity on the ramification-zero hyperplane. -/
theorem fullCartanQuadratic_pos_of_totalRamification_eq_zero {n : ℕ}
    (datum : CertifiedFissionDatum n) (legLength : Fin n → ℕ) (x : Fin n → ℝ)
    (d : (i : Fin n) → Fin (legLength i + 1) → ℝ)
    (hsum : ∀ i, ∑ k, d i k = x i)
    (hmass : datum.totalRamification x = 0) (hstate : x ≠ 0 ∨ d ≠ 0) :
    0 < datum.fullCartanQuadratic legLength x d := by
  rw [fullCartanQuadratic, hmass]
  norm_num
  exact datum.fullPositiveQuadratic_pos legLength x d hsum hstate

noncomputable def wildDimension {n : ℕ} (datum : CertifiedFissionDatum n)
    (legLength : Fin n → ℕ) (x : Fin n → ℝ)
    (d : (i : Fin n) → Fin (legLength i + 1) → ℝ) : ℝ :=
  2 - datum.fullCartanQuadratic legLength x d

/-- Wild character-variety dimension is one global ramification gain minus positive leg and cut
energies. -/
theorem wildDimension_eq_conservation {n : ℕ} (datum : CertifiedFissionDatum n)
    (legLength : Fin n → ℕ) (x : Fin n → ℝ)
    (d : (i : Fin n) → Fin (legLength i + 1) → ℝ)
    (hsum : ∀ i, ∑ k, d i k = x i) :
    datum.wildDimension legLength x d =
      2 + datum.rootDefect * datum.totalRamification x ^ (2 : ℕ) -
        (∑ i, ((∑ k, (d i k - x i / (legLength i + 1 : ℕ)) ^ (2 : ℕ)) +
          x i ^ (2 : ℕ) / (legLength i + 1 : ℕ))) -
        ∑ e, datum.rooted.tree.canonicalCuts.length e *
          (∑ i, x i * datum.cutVector e i) ^ (2 : ℕ) := by
  rw [wildDimension, datum.fullCartanQuadratic_eq_completed legLength x d hsum]
  ring

end CertifiedFissionDatum

end IrregularStokes
end GaloisForLFunctions
