import GaloisForLFunctions.HTGeometry.TopologicallyAdmittedFellerAdmission

/-!
# Conservative geometry-weighted scaling and entropy loss

Fu--Liu, arXiv:2608.29229v1, equations (115)--(117) and Theorem 4.4, scale
states toward a geometry-weighted anchor. On the corpus's finite probability
laws, arbitrary positive geometry is represented by exponential weights. The
anchor exists for every input, the weighted aggregate is conserved, and the
quadratic entropy drop is exactly the removed fraction of weighted variance.
-/

open scoped BigOperators
namespace GaloisForLFunctions.HTGeometry
noncomputable section
variable {ι : Type*} [Fintype ι]

/-- Positive geometry mass attached to a finite law. -/
def conservativeGeometryMass (p : FiniteProbabilityLaw ι) (g : ι → ℝ) : ℝ :=
  ∑ i, p.prob i * Real.exp (g i)

theorem conservativeGeometryMass_pos (p : FiniteProbabilityLaw ι) (g : ι → ℝ) :
    0 < conservativeGeometryMass p g := by
  classical
  have hex : ∃ i, 0 < p.prob i := by
    by_contra h
    push Not at h
    have hs : ∑ i, p.prob i ≤ 0 := Finset.sum_nonpos fun i _ => h i
    rw [p.sum_prob] at hs
    exact not_le_of_gt zero_lt_one hs
  obtain ⟨i, hi⟩ := hex
  apply Finset.sum_pos'
  · intro j _
    exact mul_nonneg (p.nonneg j) (Real.exp_pos _).le
  · exact ⟨i, Finset.mem_univ i, mul_pos hi (Real.exp_pos _)⟩

/-- The actual probability law induced by positive geometric densitization. -/
def conservativeGeometryLaw (p : FiniteProbabilityLaw ι) (g : ι → ℝ) :
    FiniteProbabilityLaw ι where
  prob i := p.prob i * Real.exp (g i) / conservativeGeometryMass p g
  nonneg i := div_nonneg (mul_nonneg (p.nonneg i) (Real.exp_pos _).le)
    (conservativeGeometryMass_pos p g).le
  sum_prob := by
    rw [← Finset.sum_div]
    exact div_self (conservativeGeometryMass_pos p g).ne'

/-- Geometry-compatible scalar anchor. -/
def conservativeWeightedAnchor (p : FiniteProbabilityLaw ι) (g x : ι → ℝ) : ℝ :=
  ∑ i, (conservativeGeometryLaw p g).prob i * x i

/-- A common contraction of every node toward the same weighted anchor. -/
def conservativeWeightedScale (p : FiniteProbabilityLaw ι) (g x : ι → ℝ)
    (θ : unitInterval) (i : ι) : ℝ :=
  (θ : ℝ) * x i + (1 - (θ : ℝ)) * conservativeWeightedAnchor p g x

/-- Exact conservation of the normalized geometric mean. -/
theorem conservativeWeightedScale_mean (p : FiniteProbabilityLaw ι)
    (g x : ι → ℝ) (θ : unitInterval) :
    (∑ i, (conservativeGeometryLaw p g).prob i * conservativeWeightedScale p g x θ i) =
      conservativeWeightedAnchor p g x := by
  simp only [conservativeWeightedScale, mul_add, Finset.sum_add_distrib]
  have h₁ : (∑ i, (conservativeGeometryLaw p g).prob i * ((θ : ℝ) * x i)) =
      (θ : ℝ) * conservativeWeightedAnchor p g x := by
    simp only [conservativeWeightedAnchor, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [h₁, ← Finset.sum_mul, (conservativeGeometryLaw p g).sum_prob]
  ring

/-- The original densitized aggregate is preserved, including nonconstant geometry. -/
theorem conservativeWeightedScale_conserves (p : FiniteProbabilityLaw ι)
    (g x : ι → ℝ) (θ : unitInterval) :
    (∑ i, p.prob i * Real.exp (g i) * conservativeWeightedScale p g x θ i) =
      ∑ i, p.prob i * Real.exp (g i) * x i := by
  have h := conservativeWeightedScale_mean p g x θ
  simp only [conservativeWeightedAnchor, conservativeGeometryLaw, div_mul_eq_mul_div,
    ← Finset.sum_div] at h
  exact (div_left_inj' (conservativeGeometryMass_pos p g).ne').mp h

/-- Every displacement from the anchor contracts by exactly the common factor. -/
theorem conservativeWeightedScale_centered (p : FiniteProbabilityLaw ι)
    (g x : ι → ℝ) (θ : unitInterval) (i : ι) :
    conservativeWeightedScale p g x θ i - conservativeWeightedAnchor p g x =
      (θ : ℝ) * (x i - conservativeWeightedAnchor p g x) := by
  simp only [conservativeWeightedScale]
  ring

/-- Quadratic dispersion contracts by the square of the scaling factor. -/
theorem conservativeWeightedScale_variance (p : FiniteProbabilityLaw ι)
    (g x : ι → ℝ) (θ : unitInterval) :
    (∑ i, (conservativeGeometryLaw p g).prob i *
      (conservativeWeightedScale p g x θ i - conservativeWeightedAnchor p g x) ^ (2 : ℕ)) =
      (θ : ℝ) ^ (2 : ℕ) * ∑ i, (conservativeGeometryLaw p g).prob i *
        (x i - conservativeWeightedAnchor p g x) ^ (2 : ℕ) := by
  simp_rw [conservativeWeightedScale_centered, mul_pow, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The exact quadratic-entropy change, stronger than monotonicity alone. -/
theorem conservativeWeightedScale_quadratic_drop (p : FiniteProbabilityLaw ι)
    (g x : ι → ℝ) (θ : unitInterval) :
    (∑ i, (conservativeGeometryLaw p g).prob i * x i ^ (2 : ℕ)) -
      (∑ i, (conservativeGeometryLaw p g).prob i * conservativeWeightedScale p g x θ i ^ (2 : ℕ)) =
      (1 - (θ : ℝ) ^ (2 : ℕ)) * ∑ i, (conservativeGeometryLaw p g).prob i *
        (x i - conservativeWeightedAnchor p g x) ^ (2 : ℕ) := by
  let w := conservativeGeometryLaw p g
  let a := conservativeWeightedAnchor p g x
  have hx : ∑ i, w.prob i * x i = a := rfl
  have hs := conservativeWeightedScale_mean p g x θ
  have expand (y : ι → ℝ) :
      (∑ i, w.prob i * (y i - a) ^ (2 : ℕ)) =
        (∑ i, w.prob i * y i ^ (2 : ℕ)) - 2 * a * (∑ i, w.prob i * y i) + a ^ (2 : ℕ) := by
    have he i : w.prob i * (y i - a) ^ (2 : ℕ) =
        w.prob i * y i ^ (2 : ℕ) - 2 * a * (w.prob i * y i) + w.prob i * a ^ (2 : ℕ) := by ring
    simp_rw [he, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, ← Finset.sum_mul, w.sum_prob, one_mul]
  have hv := conservativeWeightedScale_variance p g x θ
  change (∑ i, w.prob i * (conservativeWeightedScale p g x θ i - a) ^ (2 : ℕ)) =
    (θ : ℝ) ^ (2 : ℕ) * ∑ i, w.prob i * (x i - a) ^ (2 : ℕ) at hv
  rw [expand, expand, hx, hs] at hv
  change (∑ i, w.prob i * x i ^ (2 : ℕ)) - _ =
    (1 - (θ : ℝ) ^ (2 : ℕ)) * ∑ i, w.prob i * (x i - a) ^ (2 : ℕ)
  rw [expand, hx]
  nlinarith [hv]

/-- Conservative scaling never increases weighted quadratic entropy. -/
theorem conservativeWeightedScale_quadratic_le (p : FiniteProbabilityLaw ι)
    (g x : ι → ℝ) (θ : unitInterval) :
    (∑ i, (conservativeGeometryLaw p g).prob i * conservativeWeightedScale p g x θ i ^ (2 : ℕ)) ≤
      ∑ i, (conservativeGeometryLaw p g).prob i * x i ^ (2 : ℕ) := by
  apply sub_nonneg.mp
  rw [conservativeWeightedScale_quadratic_drop]
  apply mul_nonneg
  · nlinarith [θ.property.1, θ.property.2]
  · exact Finset.sum_nonneg fun i _ =>
      mul_nonneg ((conservativeGeometryLaw p g).nonneg i) (sq_nonneg _)

/-- Repeated scaling is independent of grouping and multiplies the contraction factors. -/
theorem conservativeWeightedScale_comp (p : FiniteProbabilityLaw ι)
    (g x : ι → ℝ) (θ η : unitInterval) :
    conservativeWeightedScale p g (conservativeWeightedScale p g x θ) η =
      conservativeWeightedScale p g x (η * θ) := by
  ext i
  have ha : conservativeWeightedAnchor p g (conservativeWeightedScale p g x θ) =
      conservativeWeightedAnchor p g x := conservativeWeightedScale_mean p g x θ
  simp only [conservativeWeightedScale, ha]
  change (η : ℝ) * ((θ : ℝ) * x i + (1 - (θ : ℝ)) * _) + (1 - (η : ℝ)) * _ =
    ((η : ℝ) * (θ : ℝ)) * x i + (1 - (η : ℝ) * (θ : ℝ)) * _
  ring

end
end GaloisForLFunctions.HTGeometry
