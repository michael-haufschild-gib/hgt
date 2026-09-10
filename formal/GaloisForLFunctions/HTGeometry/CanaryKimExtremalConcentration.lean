import GaloisForLFunctions.HTGeometry.FiniteNoiseMixingApplications
import GaloisForLFunctions.HTGeometry.ConservativeWeightedScaling

/-!
# Extremal concentration in finite observations

The support argument in Canary--Kim, arXiv:2609.10325, Theorem 3.2 compares
an extremal average with a strict rate gap away from the maximizing locus.
For the corpus's finite probability laws the argument has an exact deficit
identity and an explicit quantitative mass bound. Native unitary diagonal
observations and conservative geometry-weighted anchors inherit these results.
These are finite observation results, not assertions about Fuchsian entropy.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- The actual maximal rate in a finite source. -/
def canaryKimMaxRate (x : ι → ℝ) : ℝ := Finset.univ.sup' Finset.univ_nonempty x

theorem canaryKimRate_le_max (x : ι → ℝ) (i : ι) : x i ≤ canaryKimMaxRate x :=
  Finset.le_sup' x (Finset.mem_univ i)

/-- The average's deficit is exactly the mean pointwise deficit from the maximum. -/
theorem canaryKim_mean_defect (p : FiniteProbabilityLaw ι) (x : ι → ℝ) :
    canaryKimMaxRate x - (∑ i, p.prob i * x i) =
      ∑ i, p.prob i * (canaryKimMaxRate x-x i) := by
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, p.sum_prob, one_mul]

/-- Equality forces every occupied source coordinate into the maximizing locus. -/
theorem canaryKim_maximizing_support_iff (p : FiniteProbabilityLaw ι) (x : ι → ℝ) :
    (∑ i, p.prob i*x i) = canaryKimMaxRate x ↔
      ∀ i, p.prob i = 0 ∨ x i = canaryKimMaxRate x := by
  rw [eq_comm, ← sub_eq_zero, canaryKim_mean_defect,
    Finset.sum_eq_zero_iff_of_nonneg
      (fun i _ => mul_nonneg (p.nonneg i) (sub_nonneg.mpr (canaryKimRate_le_max x i)))]
  simp only [Finset.mem_univ, forall_const, mul_eq_zero, sub_eq_zero]
  exact forall_congr' fun i => or_congr Iff.rfl eq_comm

/-- Quantitative version: a fixed local rate gap limits the mass away from the extremal locus. -/
theorem canaryKim_near_maximizer_mass (p : FiniteProbabilityLaw ι) (x : ι → ℝ) (r : ℝ) :
    Real.exp r * (∑ i ∈ Finset.univ.filter (fun i => x i ≤ canaryKimMaxRate x-Real.exp r),
      p.prob i) ≤ canaryKimMaxRate x - ∑ i, p.prob i*x i := by
  rw [canaryKim_mean_defect, Finset.mul_sum]
  calc
    _ ≤ ∑ i ∈ Finset.univ.filter (fun i => x i ≤ canaryKimMaxRate x-Real.exp r),
        p.prob i * (canaryKimMaxRate x-x i) := by
      apply Finset.sum_le_sum
      intro i hi
      have hgap : Real.exp r ≤ canaryKimMaxRate x-x i := by
        have := (Finset.mem_filter.mp hi).2
        linarith
      simpa [mul_comm] using mul_le_mul_of_nonneg_left hgap (p.nonneg i)
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun i _ _ => mul_nonneg (p.nonneg i) (sub_nonneg.mpr (canaryKimRate_le_max x i)))

variable [DecidableEq ι]

/-- A unitary diagonal observer defines a probability law on the source eigenvalues. -/
def canaryKimUnitaryRow (U : Matrix.unitaryGroup ι ℂ) (i : ι) : FiniteProbabilityLaw ι where
  prob j := finiteUnitaryEntryWeight U j i
  nonneg _ := Complex.normSq_nonneg _
  sum_prob := sum_finiteUnitaryEntryWeight_column U i

/-- An extremal observed diagonal entry sees only the maximal source eigenspace. -/
theorem canaryKim_unitary_extremal_iff (U : Matrix.unitaryGroup ι ℂ) (x : ι → ℝ) (i : ι) :
    finiteUnitaryDiagonalCoordinate x U i = canaryKimMaxRate x ↔
      ∀ j, finiteUnitaryEntryWeight U j i = 0 ∨ x j = canaryKimMaxRate x := by
  simpa only [canaryKimUnitaryRow, finiteUnitaryDiagonalCoordinate, mul_comm] using
    canaryKim_maximizing_support_iff (canaryKimUnitaryRow U i) x

/-- Near-extremal unitary measurements quantitatively suppress low-rate eigenvectors. -/
theorem canaryKim_unitary_near_extremal (U : Matrix.unitaryGroup ι ℂ)
    (x : ι → ℝ) (i : ι) (r : ℝ) :
    Real.exp r *
      (∑ j ∈ Finset.univ.filter (fun j => x j ≤ canaryKimMaxRate x-Real.exp r),
        finiteUnitaryEntryWeight U j i) ≤
      canaryKimMaxRate x - finiteUnitaryDiagonalCoordinate x U i := by
  simpa only [canaryKimUnitaryRow, finiteUnitaryDiagonalCoordinate, mul_comm] using
    canaryKim_near_maximizer_mass (canaryKimUnitaryRow U i) x r

omit [DecidableEq ι] in
/-- Geometry reweighting cannot create an extremal anchor unless all occupied rates maximize. -/
theorem canaryKim_geometry_anchor_extremal_iff (p : FiniteProbabilityLaw ι)
    (g x : ι → ℝ) :
    conservativeWeightedAnchor p g x = canaryKimMaxRate x ↔
      ∀ i, p.prob i = 0 ∨ x i = canaryKimMaxRate x := by
  rw [conservativeWeightedAnchor, canaryKim_maximizing_support_iff]
  simp only [conservativeGeometryLaw, div_eq_zero_iff, mul_eq_zero,
    (conservativeGeometryMass_pos p g).ne', Real.exp_ne_zero, or_false]

end GaloisForLFunctions.HTGeometry
