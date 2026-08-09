import GaloisForLFunctions.HTGeometry.EulerFactorUniformBound
import GaloisForLFunctions.HTGeometry.FiniteNomeSectionRestriction

/-!
# The logarithm tail of a finite section, and its counterterm split

The free energy of a finite section is a moment series whose coefficients are the finite Euler
products.  Those coefficients are bounded uniformly in the nome set and in the order, so the series
is dominated by a geometric one and may be split at any order into a finite head of counterterms and
a tail.

The head is what the counterterm jet subtracts; the tail is what the jet divides by a power of the
nome product.
-/

namespace HTGeometry

open Filter Topology
open scoped BigOperators

/-- The logarithm tail of a finite section: its regularized free energy, with a sign. -/
noncomputable def sectionLogTail {ι : Type*} (g : ℕ) (p : ι → ℂ) (S : Finset ι) (t : ℂ) : ℂ :=
  ∑' m : ℕ, t ^ (m + (g + 1)) / ((m + (g + 1) : ℕ) : ℂ) *
    ∏ a ∈ S, (1 - p a ^ (m + (g + 1)))⁻¹

theorem finiteNomeSection_eq_exp_neg_sectionLogTail {ι : Type*} (g : ℕ) (p : ι → ℂ)
    (hp_lt : ∀ a, ‖p a‖ < 1) (S : Finset ι) {t : ℂ} (ht : ‖t‖ < 1) :
    finiteNomeSection g p S t = Complex.exp (-sectionLogTail g p S t) :=
  finiteNomeSection_eq_exp_neg_moments g p hp_lt S ht

/-- Every term of the section's moment series is dominated by a geometric term, with a constant
independent of the nome set. -/
theorem norm_sectionLogTail_term_le {ι : Type*} (g : ℕ) (p : ι → ℂ)
    (hp_lt : ∀ a, ‖p a‖ < 1) (hsum : Summable (fun a => ‖p a‖ ^ (g + 1)))
    (S : Finset ι) (t : ℂ) (m : ℕ) :
    ‖t ^ (m + (g + 1)) / ((m + (g + 1) : ℕ) : ℂ) *
        ∏ a ∈ S, (1 - p a ^ (m + (g + 1)))⁻¹‖
      ≤ (‖t‖ ^ (g + 1) / ((g : ℝ) + 1) * ‖t‖ ^ m) * ∏' a, (1 - ‖p a‖ ^ (g + 1))⁻¹ := by
  have hterm : ‖t ^ (m + (g + 1)) / ((m + (g + 1) : ℕ) : ℂ)‖
      ≤ ‖t‖ ^ (g + 1) / ((g : ℝ) + 1) * ‖t‖ ^ m := by
    have h := norm_logTail_term_le g m (x := t) (q := 1) (by simp)
    simpa using h
  have heuler := norm_finiteEulerProduct_le g p hp_lt hsum S (k := m + (g + 1)) (by omega)
  rw [norm_mul]
  exact mul_le_mul hterm heuler (norm_nonneg _)
    (by positivity)

/-- The section's moment series is absolutely summable inside the unit disc. -/
theorem summable_sectionLogTail {ι : Type*} (g : ℕ) (p : ι → ℂ)
    (hp_lt : ∀ a, ‖p a‖ < 1) (hsum : Summable (fun a => ‖p a‖ ^ (g + 1)))
    (S : Finset ι) {t : ℂ} (ht : ‖t‖ < 1) :
    Summable (fun m : ℕ => t ^ (m + (g + 1)) / ((m + (g + 1) : ℕ) : ℂ) *
      ∏ a ∈ S, (1 - p a ^ (m + (g + 1)))⁻¹) := by
  have hgeom : Summable (fun m : ℕ =>
      (‖t‖ ^ (g + 1) / ((g : ℝ) + 1) * ‖t‖ ^ m) * ∏' a, (1 - ‖p a‖ ^ (g + 1))⁻¹) := by
    refine Summable.mul_right _ ?_
    exact (summable_geometric_of_lt_one (norm_nonneg t) ht).mul_left _
  exact Summable.of_norm_bounded hgeom (norm_sectionLogTail_term_le g p hp_lt hsum S t)

/-- **The counterterm split.**  At any order the section's free energy splits into the finite head
of counterterms and the tail the jet divides. -/
theorem sectionLogTail_split {ι : Type*} (g : ℕ) (p : ι → ℂ)
    (hp_lt : ∀ a, ‖p a‖ < 1) (hsum : Summable (fun a => ‖p a‖ ^ (g + 1)))
    (S : Finset ι) {t : ℂ} (ht : ‖t‖ < 1) (j : ℕ) :
    sectionLogTail g p S t
      = (∑ m ∈ Finset.range j, t ^ (m + (g + 1)) / ((m + (g + 1) : ℕ) : ℂ) *
            ∏ a ∈ S, (1 - p a ^ (m + (g + 1)))⁻¹)
        + ∑' k : ℕ, t ^ ((k + j) + (g + 1)) / (((k + j) + (g + 1) : ℕ) : ℂ) *
            ∏ a ∈ S, (1 - p a ^ ((k + j) + (g + 1)))⁻¹ :=
  ((summable_sectionLogTail g p hp_lt hsum S ht).sum_add_tsum_nat_add j).symm

end HTGeometry
