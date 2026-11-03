import GaloisForLFunctions.SelbergClass.OrdinaryCoefficientDecay
import GaloisForLFunctions.SelbergClass.PositiveDegreeAbscissa
import GaloisForLFunctions.SelbergClass.DegreeZeroClassification

/-!
# The Selberg degree gap

There is no extended Selberg function of degree strictly between zero and one.
For the full class, the lower side of this gap consists only of the Dirichlet unit.
-/

noncomputable section
open Complex Filter Topology Set
open GaloisForLFunctions.HTGeometry RHTower

namespace GaloisForLFunctions.SelbergClass

private theorem summable_zero_of_degree_gap (F : ExtendedSelbergClass)
    (hd0 : 0 < F.gammaData.degree) (hd1 : F.gammaData.degree < 1) :
    LSeriesSummable F.coeff 0 := by
  obtain ⟨C, _, hC⟩ := exists_exponential_coeff_bound_of_degree_lt_one F hd0 hd1 1
  have hsum : Summable (fun n : ℕ => C * Real.exp (-(n : ℝ))) := by
    simpa only [mul_one] using
      (summable_exp_neg_nat_mul (by norm_num : (0 : ℝ) < 1)).mul_left C
  have ha : Summable (fun n : ℕ => ‖F.coeff n‖) :=
    hsum.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => by simpa using hC n)
  apply Summable.of_norm
  apply ha.of_nonneg_of_le (fun n => norm_nonneg _)
  intro n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · simp [LSeries.term_of_ne_zero hn.ne']

/-- An extended Selberg function has degree zero or degree at least one. -/
theorem degree_eq_zero_or_one_le (F : ExtendedSelbergClass) :
    F.gammaData.degree = 0 ∨ 1 ≤ F.gammaData.degree := by
  by_cases h0 : F.gammaData.degree = 0
  · exact Or.inl h0
  right
  by_contra h1
  have hd0 : 0 < F.gammaData.degree :=
    lt_of_le_of_ne F.gammaData.degree_nonneg (Ne.symm h0)
  exact h0 (degree_eq_zero_of_summable_zero F
    (summable_zero_of_degree_gap F hd0 (lt_of_not_ge h1)))

/-- Below degree one, a full Selberg function is the Dirichlet unit, with unit
conductor parameter and root number. -/
theorem classification_of_degree_lt_one (F : RHTower.SelbergClass)
    (hF : F.gammaData.degree < 1) :
    F.gammaData.degree = 0 ∧ F.coeff = 1 ∧ F.gammaData.Q = 1 ∧ F.gammaData.rootNumber = 1 := by
  have h0 : F.gammaData.degree = 0 :=
    (degree_eq_zero_or_one_le F.toExtendedSelbergClass).resolve_right (not_le_of_gt hF)
  exact ⟨h0, degreeZero_classification F h0⟩

end GaloisForLFunctions.SelbergClass
