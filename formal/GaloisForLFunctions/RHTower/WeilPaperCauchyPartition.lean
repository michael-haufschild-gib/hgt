import GaloisForLFunctions.RHTower.WeilPaperCauchyDensity

/-!
# A Cauchy partition preserving total mass exactly

Normalizing the paper's Cauchy probes by their positive lattice sum produces
a countable partition of one. Its discrete density measurements preserve
positive mass exactly and contract L1 error, uniformly in the width.
-/

open MeasureTheory Set Filter
open scoped BigOperators

noncomputable section
namespace RHTower.WeilSpectral

/-- Total Cauchy weight at each real height. -/
def paperCauchyLatticeWeight (k : ℕ) (y : ℝ) : ℝ :=
  ∑' n : ℤ, paperCauchyKernel k ((n : ℝ) - y)

theorem paperCauchyLatticeWeight_pos (k : ℕ) (y : ℝ) :
    0 < paperCauchyLatticeWeight k y :=
  lt_of_lt_of_le (by unfold paperCauchyKernel; positivity)
    (paperCauchyKernel_half_le_lattice k y)

theorem measurable_paperCauchyLatticeWeight (k : ℕ) : Measurable (paperCauchyLatticeWeight k) :=
  Measurable.tsum fun _n : ℤ => ((continuous_paperCauchyKernel k).comp
    (continuous_const.sub continuous_id)).measurable

/-- A probability distribution on integer sites at each real height. -/
def paperCauchyPartition (k : ℕ) (n : ℤ) (y : ℝ) : ℝ :=
  paperCauchyKernel k ((n : ℝ) - y) / paperCauchyLatticeWeight k y

theorem paperCauchyPartition_nonneg (k : ℕ) (n : ℤ) (y : ℝ) :
    0 ≤ paperCauchyPartition k n y :=
  div_nonneg (paperCauchyKernel_nonneg _ _) (paperCauchyLatticeWeight_pos k y).le

theorem paperCauchyPartition_le_one (k : ℕ) (n : ℤ) (y : ℝ) :
    paperCauchyPartition k n y ≤ 1 := by
  apply (div_le_one (paperCauchyLatticeWeight_pos k y)).mpr
  exact (summable_paperCauchyKernel_lattice k y).le_tsum n
    (fun _ _ => paperCauchyKernel_nonneg _ _)

theorem summable_paperCauchyPartition (k : ℕ) (y : ℝ) :
    Summable (fun n : ℤ => paperCauchyPartition k n y) :=
  (summable_paperCauchyKernel_lattice k y).div_const _

theorem tsum_paperCauchyPartition (k : ℕ) (y : ℝ) :
    (∑' n : ℤ, paperCauchyPartition k n y) = 1 := by
  simp only [paperCauchyPartition, tsum_div_const]
  exact div_self (paperCauchyLatticeWeight_pos k y).ne'

private theorem integrable_div_lattice {f : ℝ → ℝ} (hf : Integrable f) (k : ℕ) :
    Integrable (fun y => f y / paperCauchyLatticeWeight k y) := by
  have hi : Integrable (fun y => (paperCauchyLatticeWeight k y)⁻¹ * f y) := by
    apply hf.bdd_mul (c := (paperCauchyKernel k (1 / 2))⁻¹)
      (measurable_paperCauchyLatticeWeight k).inv.aestronglyMeasurable
    exact Eventually.of_forall fun y => by
      change ‖(paperCauchyLatticeWeight k y)⁻¹‖ ≤ (paperCauchyKernel k (1 / 2))⁻¹
      rw [Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (paperCauchyLatticeWeight_pos k y).le)]
      simpa only [one_div, paperCauchyLatticeWeight] using one_div_le_one_div_of_le
        (by unfold paperCauchyKernel; positivity : 0 < paperCauchyKernel k (1 / 2))
        (paperCauchyKernel_half_le_lattice k y)
  simpa only [div_eq_mul_inv, mul_comm] using hi

/-- Cauchy measurements normalized to preserve density mass. -/
def paperCauchyPartitionSample (f : ℝ → ℝ) (k : ℕ) (n : ℤ) : ℝ :=
  paperCauchyDensitySample (fun y => f y / paperCauchyLatticeWeight k y) k n

theorem paperCauchyPartitionSample_eq_integral (f : ℝ → ℝ) (k : ℕ) (n : ℤ) :
    paperCauchyPartitionSample f k n = ∫ y, paperCauchyPartition k n y * f y := by
  unfold paperCauchyPartitionSample paperCauchyDensitySample paperCauchyPartition
  apply integral_congr_ae
  exact Eventually.of_forall fun _ => by ring

theorem paperCauchyPartitionSample_nonneg {f : ℝ → ℝ}
    (hf0 : ∀ y, 0 ≤ f y) (k : ℕ) (n : ℤ) : 0 ≤ paperCauchyPartitionSample f k n :=
  paperCauchyDensitySample_nonneg
    (fun y => div_nonneg (hf0 y) (paperCauchyLatticeWeight_pos k y).le) k n

theorem summable_paperCauchyPartitionSample {f : ℝ → ℝ} (hf : Integrable f)
    (hf0 : ∀ y, 0 ≤ f y) (k : ℕ) : Summable (paperCauchyPartitionSample f k) :=
  paperCauchyDensitySample_summable_nonneg (integrable_div_lattice hf k)
    (fun y => div_nonneg (hf0 y) (paperCauchyLatticeWeight_pos k y).le) k

/-- The infinite sample sum is exactly the positive density's total mass. -/
theorem tsum_paperCauchyPartitionSample {f : ℝ → ℝ} (hf : Integrable f)
    (hf0 : ∀ y, 0 ≤ f y) (k : ℕ) :
    (∑' n : ℤ, paperCauchyPartitionSample f k n) = ∫ y, f y := by
  unfold paperCauchyPartitionSample
  rw [tsum_paperCauchyDensitySample_eq (integrable_div_lattice hf k)
    (fun y => div_nonneg (hf0 y) (paperCauchyLatticeWeight_pos k y).le)]
  apply integral_congr_ae
  exact Eventually.of_forall fun y => by
    change paperCauchyLatticeWeight k y * (f y / paperCauchyLatticeWeight k y) = f y
    field_simp [(paperCauchyLatticeWeight_pos k y).ne']

theorem abs_paperCauchyPartitionSample_le (f : ℝ → ℝ) (k : ℕ) (n : ℤ) :
    |paperCauchyPartitionSample f k n| ≤ paperCauchyPartitionSample (fun y => |f y|) k n := by
  have h := abs_paperCauchyDensitySample_le
    (f := fun y => f y / paperCauchyLatticeWeight k y) k n
  simpa only [paperCauchyPartitionSample, abs_div,
    abs_of_pos (paperCauchyLatticeWeight_pos k _)] using h

/-- Normalized sampling contracts L1 error with constant one for every width. -/
theorem tsum_abs_paperCauchyPartitionSample_le {f : ℝ → ℝ} (hf : Integrable f) (k : ℕ) :
    (∑' n : ℤ, |paperCauchyPartitionSample f k n|) ≤ ∫ y, |f y| := by
  have hs := summable_abs_paperCauchyDensitySample (integrable_div_lattice hf k) k
  calc
    _ ≤ ∑' n : ℤ, paperCauchyPartitionSample (fun y => |f y|) k n :=
      Summable.tsum_le_tsum (abs_paperCauchyPartitionSample_le f k) hs
        (summable_paperCauchyPartitionSample hf.abs (fun _ => abs_nonneg _) k)
    _ = _ := tsum_paperCauchyPartitionSample hf.abs (fun _ => abs_nonneg _) k

theorem paperCauchyPartitionSample_sub {f g : ℝ → ℝ} (hf : Integrable f) (hg : Integrable g)
    (k : ℕ) (n : ℤ) :
    paperCauchyPartitionSample (fun y => f y - g y) k n =
      paperCauchyPartitionSample f k n - paperCauchyPartitionSample g k n := by
  unfold paperCauchyPartitionSample
  simp only [sub_div]
  exact paperCauchyDensitySample_sub (integrable_div_lattice hf k) (integrable_div_lattice hg k) k n

theorem tsum_abs_paperCauchyPartitionSample_sub_le {f g : ℝ → ℝ}
    (hf : Integrable f) (hg : Integrable g) (k : ℕ) :
    (∑' n : ℤ, |paperCauchyPartitionSample f k n - paperCauchyPartitionSample g k n|) ≤
      ∫ y, |f y - g y| := by
  simpa only [Pi.sub_def, paperCauchyPartitionSample_sub hf hg] using
    tsum_abs_paperCauchyPartitionSample_le (hf.sub hg) k

end RHTower.WeilSpectral
