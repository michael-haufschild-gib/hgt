import GaloisForLFunctions.HTGeometry.GomesGaussianTensorDensity
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.FiniteMeasure

/-!
# Gaussian tensor-charge measures on the real line

Experimental application of the integer tensor charges of arXiv:2509.25276v7 section 5.2.
Here tensoring means multiplication of scalar densities on one base, not a product measure.
The entire charge lattice exists as measures, but its finite sector is a strict half-lattice:
it is closed under tensor addition, excludes the unit, and contains no dual pair.
-/

noncomputable section
open MeasureTheory
open scoped NNReal ENNReal

namespace GaloisForLFunctions.HTGeometry

/-- The actual Gaussian charge measure, allowing infinite mass. -/
def gomesGaussianChargeMeasure (b : ℝ) (n : ℤ) : Measure ℝ :=
  volume.withDensity (fun x => ENNReal.ofReal (gomesGaussianTensorDensity b n x))

/-- Exact finiteness boundary, including the infinite neutral charge. -/
theorem gomesGaussianChargeMeasure_finite_iff (b : ℝ) (n : ℤ) :
    IsFiniteMeasure (gomesGaussianChargeMeasure b n) ↔ 0 < (n : ℝ) * b := by
  have h : Integrable (fun _ : ℝ => (1 : ℝ)) (gomesGaussianChargeMeasure b n) ↔
      Integrable (gomesGaussianTensorDensity b n) := by
    change Integrable (fun _ : ℝ => (1 : ℝ))
      (volume.withDensity (fun x => ENNReal.ofReal (gomesGaussianTensorDensity b n x))) ↔ _
    rw [integrable_withDensity_iff_integrable_smul'
      (gomesGaussianTensorDensity_continuous b n).measurable.ennreal_ofReal
      (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
    simp only [ENNReal.toReal_ofReal (gomesGaussianTensorDensity_pos b n _).le,
      smul_eq_mul, mul_one]
  exact (integrable_const_iff_isFiniteMeasure (one_ne_zero : (1 : ℝ) ≠ 0)).symm.trans
    (h.trans (gomesGaussianTensorDensity_integrable_iff b n))

/-- The complementary closed half-lattice has infinite total mass. -/
theorem gomesGaussianChargeMeasure_infinite_iff (b : ℝ) (n : ℤ) :
    gomesGaussianChargeMeasure b n Set.univ = ∞ ↔ (n : ℝ) * b ≤ 0 := by
  rw [← not_isFiniteMeasure_iff, gomesGaussianChargeMeasure_finite_iff]
  exact not_lt

/-- The tensor unit is unrestricted Lebesgue volume. -/
theorem gomesGaussianChargeMeasure_zero (b : ℝ) :
    gomesGaussianChargeMeasure b 0 = volume := by
  have h : (fun x => ENNReal.ofReal (gomesGaussianTensorDensity b 0 x)) = 1 := by
    funext x
    simp [gomesGaussianTensorDensity_formula]
  rw [gomesGaussianChargeMeasure, h, withDensity_one]

/-- Tensor addition is literal reweighting of the same real base. -/
theorem gomesGaussianChargeMeasure_tensor (b : ℝ) (m n : ℤ) :
    (gomesGaussianChargeMeasure b m).withDensity
      (fun x => ENNReal.ofReal (gomesGaussianTensorDensity b n x)) =
        gomesGaussianChargeMeasure b (m + n) := by
  rw [gomesGaussianChargeMeasure, ← withDensity_mul _
    (gomesGaussianTensorDensity_continuous b m).measurable.ennreal_ofReal
    (gomesGaussianTensorDensity_continuous b n).measurable.ennreal_ofReal]
  apply withDensity_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    simp only [Pi.mul_apply, gomesGaussianTensorDensity_add,
      ENNReal.ofReal_mul (gomesGaussianTensorDensity_pos b m x).le]

/-- A charge and its dual always cancel back to infinite volume. -/
theorem gomesGaussianChargeMeasure_dual_cancel (b : ℝ) (n : ℤ) :
    (gomesGaussianChargeMeasure b n).withDensity
      (fun x => ENNReal.ofReal (gomesGaussianTensorDensity b (-n) x)) = volume := by
  rw [gomesGaussianChargeMeasure_tensor, add_neg_cancel, gomesGaussianChargeMeasure_zero]

/-- No charge and its dual are both finite. -/
theorem gomesGaussianChargeMeasure_no_finite_dual (b : ℝ) (n : ℤ) :
    ¬ (IsFiniteMeasure (gomesGaussianChargeMeasure b n) ∧
      IsFiniteMeasure (gomesGaussianChargeMeasure b (-n))) := by
  simp only [gomesGaussianChargeMeasure_finite_iff, Int.cast_neg, neg_mul]
  rintro ⟨h, h'⟩
  linarith

/-- Tensor reweighting of two finite charges cannot leave the finite sector. -/
theorem gomesGaussianChargeMeasure_no_tensor_failure (b : ℝ) :
    ¬ ∃ m n : ℤ, IsFiniteMeasure (gomesGaussianChargeMeasure b m) ∧
      IsFiniteMeasure (gomesGaussianChargeMeasure b n) ∧
      ¬ IsFiniteMeasure ((gomesGaussianChargeMeasure b m).withDensity
        (fun x => ENNReal.ofReal (gomesGaussianTensorDensity b n x))) := by
  simp only [gomesGaussianChargeMeasure_tensor, gomesGaussianChargeMeasure_finite_iff,
    Int.cast_add, add_mul]
  rintro ⟨m, n, hm, hn, hmn⟩
  exact hmn (add_pos hm hn)

/-- Every nontrivial generator has a finite charge; the trivial generator has none. -/
theorem gomesGaussianChargeMeasure_exists_finite_iff (b : ℝ) :
    (∃ n : ℤ, IsFiniteMeasure (gomesGaussianChargeMeasure b n)) ↔ b ≠ 0 := by
  simp only [gomesGaussianChargeMeasure_finite_iff]
  constructor
  · rintro ⟨n, hn⟩ rfl
    simp at hn
  · intro hb
    rcases lt_or_gt_of_ne hb with hn | hp
    · refine ⟨-1, ?_⟩
      simpa only [Int.cast_neg, Int.cast_one, neg_mul, one_mul] using neg_pos.mpr hn
    · exact ⟨1, by simpa using hp⟩

/-- No generator makes every charge finite, since the tensor unit already has infinite mass. -/
theorem gomesGaussianChargeMeasure_not_all_finite (b : ℝ) :
    ¬ ∀ n : ℤ, IsFiniteMeasure (gomesGaussianChargeMeasure b n) := by
  intro h
  have hz := (gomesGaussianChargeMeasure_finite_iff b 0).mp (h 0)
  simp at hz

/-- All charge measures have the same null sets as volume, independently of finiteness. -/
theorem gomesGaussianChargeMeasure_null_iff (b : ℝ) (n : ℤ) (s : Set ℝ) :
    gomesGaussianChargeMeasure b n s = 0 ↔ volume s = 0 := by
  have h := withDensity_absolutelyContinuous' (μ := (volume : Measure ℝ))
    (gomesGaussianTensorDensity_continuous b n).measurable.ennreal_ofReal.aemeasurable
    (Filter.Eventually.of_forall fun x =>
      ENNReal.ofReal_ne_zero_iff.mpr (gomesGaussianTensorDensity_pos b n x))
  exact ⟨fun hs => h hs, fun hs => withDensity_absolutelyContinuous _ _ hs⟩

/-- Every charge measure is atom-free, including the infinite ones. -/
theorem gomesGaussianChargeMeasure_singleton (b : ℝ) (n : ℤ) (x : ℝ) :
    gomesGaussianChargeMeasure b n {x} = 0 :=
  (gomesGaussianChargeMeasure_null_iff b n {x}).mpr (measure_singleton x)

/-- A finite charge packaged as data for the finite-measure constructor. -/
abbrev GomesGaussianFiniteCharge (b : ℝ) := {n : ℤ // 0 < (n : ℝ) * b}

/-- The exact finite measure of an admissible charge, without truncation or normalization. -/
def gomesGaussianChargeSource (b : ℝ) (n : GomesGaussianFiniteCharge b) : FiniteMeasure ℝ :=
  ⟨gomesGaussianChargeMeasure b n.val, (gomesGaussianChargeMeasure_finite_iff b n.val).mpr n.property⟩

/-- The bundled finite source is the original raw charge measure. -/
theorem gomesGaussianChargeSource_measure (b : ℝ) (n : GomesGaussianFiniteCharge b) :
    (gomesGaussianChargeSource b n : Measure ℝ) = gomesGaussianChargeMeasure b n.val := rfl

end GaloisForLFunctions.HTGeometry
