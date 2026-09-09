import GaloisForLFunctions.HTGeometry.GomesPolynomialExponentialIntegrability

/-!
# Integer tensor charges of arbitrary polynomial generators

The integer-charge construction of arXiv:2509.25276v7 section 5.2 now applies to every
polynomial log-density. Its finite charge sector is empty for constant or odd-degree
generators, and otherwise is precisely the half-lattice opposite the leading sign.
The existing Gaussian and quartic charge measures are literal specializations.
-/

noncomputable section
open Polynomial MeasureTheory
open scoped NNReal ENNReal

namespace GaloisForLFunctions.HTGeometry

/-- Integer tensor charge of any polynomial generating log-density. -/
def gomesPolynomialTensorLogWeight (P : ℝ[X]) (n : ℤ) : ℝ[X] := C (n : ℝ) * P

/-- Charges add at the level of the generating polynomial itself. -/
theorem gomesPolynomialTensorLogWeight_add (P : ℝ[X]) (n m : ℤ) :
    gomesPolynomialTensorLogWeight P (n + m) =
      gomesPolynomialTensorLogWeight P n + gomesPolynomialTensorLogWeight P m := by
  simp only [gomesPolynomialTensorLogWeight, Int.cast_add, map_add, add_mul]

/-- Dual charge is the exact negative polynomial profile. -/
theorem gomesPolynomialTensorLogWeight_neg (P : ℝ[X]) (n : ℤ) :
    gomesPolynomialTensorLogWeight P (-n) = -gomesPolynomialTensorLogWeight P n := by
  simp only [gomesPolynomialTensorLogWeight, Int.cast_neg, map_neg, neg_mul]

/-- Complete finite-charge criterion, including the neutral and degenerate generators. -/
theorem gomesPolynomialTensorLogWeight_finite_iff (P : ℝ[X]) (n : ℤ) :
    IsFiniteMeasure (gomesDilatonMeasure (gomesPolynomialTensorLogWeight P n)) ↔
      0 < P.natDegree ∧ Even P.natDegree ∧ (n : ℝ) * P.leadingCoeff < 0 := by
  rw [gomesDilatonMeasure_finite_polynomial_iff]
  by_cases hn : (n : ℝ) = 0
  · simp only [gomesPolynomialTensorLogWeight, hn, C_0, zero_mul, natDegree_zero,
      leadingCoeff_zero, lt_self_iff_false, and_false]
  · simp only [gomesPolynomialTensorLogWeight, natDegree_C_mul hn,
      leadingCoeff_mul, leadingCoeff_C]

/-- A polynomial admits at least one finite integer charge exactly when its degree is positive even. -/
theorem gomesPolynomialTensorLogWeight_exists_finite_iff (P : ℝ[X]) :
    (∃ n : ℤ, IsFiniteMeasure (gomesDilatonMeasure (gomesPolynomialTensorLogWeight P n))) ↔
      0 < P.natDegree ∧ Even P.natDegree := by
  simp only [gomesPolynomialTensorLogWeight_finite_iff]
  constructor
  · rintro ⟨n, hd, he, _⟩
    exact ⟨hd, he⟩
  · rintro ⟨hd, he⟩
    have hp : P ≠ 0 := ne_zero_of_degree_gt (natDegree_pos_iff_degree_pos.mp hd)
    have hl : P.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hp
    rcases lt_or_gt_of_ne hl with hn | hp
    · exact ⟨1, hd, he, by simpa only [Int.cast_one, one_mul] using hn⟩
    · exact ⟨-1, hd, he, by simpa only [Int.cast_neg, Int.cast_one, neg_mul, one_mul] using neg_neg_of_pos hp⟩

/-- No polynomial charge and its dual have finite mass simultaneously. -/
theorem gomesPolynomialTensorLogWeight_no_finite_dual (P : ℝ[X]) (n : ℤ) :
    ¬ (IsFiniteMeasure (gomesDilatonMeasure (gomesPolynomialTensorLogWeight P n)) ∧
      IsFiniteMeasure (gomesDilatonMeasure (gomesPolynomialTensorLogWeight P (-n)))) := by
  simp only [gomesPolynomialTensorLogWeight_finite_iff, Int.cast_neg, neg_mul]
  rintro ⟨⟨_, _, hn⟩, ⟨_, _, hm⟩⟩
  linarith

/-- Finiteness of two charges guarantees finiteness of their tensor sum for every generator. -/
theorem gomesPolynomialTensorLogWeight_no_tensor_failure (P : ℝ[X]) :
    ¬ ∃ n m : ℤ,
      IsFiniteMeasure (gomesDilatonMeasure (gomesPolynomialTensorLogWeight P n)) ∧
      IsFiniteMeasure (gomesDilatonMeasure (gomesPolynomialTensorLogWeight P m)) ∧
      ¬ IsFiniteMeasure (gomesDilatonMeasure (gomesPolynomialTensorLogWeight P (n + m))) := by
  simp only [gomesPolynomialTensorLogWeight_finite_iff, Int.cast_add, add_mul]
  rintro ⟨n, m, ⟨hd, he, hn⟩, ⟨_, _, hm⟩, hsum⟩
  exact hsum ⟨hd, he, add_neg hn hm⟩

/-- No generating polynomial makes the entire integer lattice finite. -/
theorem gomesPolynomialTensorLogWeight_not_all_finite (P : ℝ[X]) :
    ¬ ∀ n : ℤ, IsFiniteMeasure (gomesDilatonMeasure (gomesPolynomialTensorLogWeight P n)) := by
  intro h
  have hz := (gomesPolynomialTensorLogWeight_finite_iff P 0).mp (h 0)
  simp only [Int.cast_zero, zero_mul, lt_self_iff_false, and_false] at hz

/-- Probability normalization of every charged generator has the same exact coefficient test. -/
theorem gomesPolynomialTensorLogWeight_probability_iff (P : ℝ[X]) (n : ℤ) :
    IsProbabilityMeasure (gomesDilatonMassNormalized (gomesPolynomialTensorLogWeight P n)) ↔
      0 < P.natDegree ∧ Even P.natDegree ∧ (n : ℝ) * P.leadingCoeff < 0 := by
  rw [gomesDilatonMassNormalized_probability_iff, gomesPolynomialTensorLogWeight_finite_iff]

/-- Integer tensor addition is actual reweighting of the same full real-line measure. -/
theorem gomesPolynomialTensorLogWeight_measure_tensor (P : ℝ[X]) (n m : ℤ) :
    (gomesDilatonMeasure (gomesPolynomialTensorLogWeight P n)).withDensity
      (fun x => ENNReal.ofReal (dilatonWeight (gomesPolynomialTensorLogWeight P m) x)) =
        gomesDilatonMeasure (gomesPolynomialTensorLogWeight P (n + m)) := by
  rw [gomesDilatonMeasure_tensor, gomesPolynomialTensorLogWeight_add]

/-- The original Gaussian tensor family is an exact instance of the arbitrary-generator construction. -/
theorem gomesPolynomialTensorLogWeight_gaussian (b : ℝ) (n : ℤ) :
    gomesPolynomialTensorLogWeight (gomesGaussianLogWeight b) n = gomesGaussianTensorLogWeight b n := by
  simp only [gomesPolynomialTensorLogWeight, gomesGaussianLogWeight,
    gomesGaussianTensorLogWeight, map_mul]
  ring

/-- The original quartic tensor family is an exact instance as well. -/
theorem gomesPolynomialTensorLogWeight_quartic (b : ℝ) (n : ℤ) :
    gomesPolynomialTensorLogWeight (gomesQuarticLogWeight b) n = gomesQuarticTensorLogWeight b n := by
  simp only [gomesPolynomialTensorLogWeight, gomesQuarticLogWeight,
    gomesQuarticTensorLogWeight, map_neg, map_mul, neg_mul]
  ring

end GaloisForLFunctions.HTGeometry
