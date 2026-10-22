import GaloisForLFunctions.RHTower.PMPowerDampedMobiusDyadicDeletion

/-!
# Gram matrix of dilated supported dyadic Haar functions

Let `h = 1_(0,1] − 2·1_(0,1/2]` be the dyadic Haar function supported on `(0,1]`
(`pmSupportedDyadicHaar`). This module computes the exact `L²(0,∞)` inner products of
its dilations `t ↦ h(a t)`: writing `h(a t)` through the cutoffs `1_(0,c]` reduces every
product to minima, giving `⟨h(a·), h(b·)⟩ = max 0 (2/max a b − 1/min a b)`. Consequences
are nonnegativity of the Gram matrix, `‖h(a·)‖² = 1/a`, orthogonality when `2a ≤ b`, and
the energy of a finite sum `∑ h(a_i t)` as the double Gram sum, bounded below by the
diagonal `∑ 1/a_i` and monotone in the index set.

## Main results

- `pmHaarDilationGram_eq_min`: the Gram entry as an explicit combination of `min (1/a) (1/b)`-type terms.
- `pmHaarDilationGram_eq_max`: for `a, b > 0`, Gram entry `= max 0 (2/max a b − 1/min a b)`.
- `pmHaarDilationGram_nonneg`, `pmHaarDilationGram_self`, `pmHaarDilationGram_eq_zero_of_two_mul_le`.
- `pmHaarDilationSum_energy`: `∫₀^∞ |∑_{i∈S} h(a_i t)|² dt = ∑_{i,j∈S} Gram(a_i, a_j)`.
- `pmHaarDilationSum_diagonal_le_energy`: `∑_{i∈S} 1/a_i ≤` that energy.
- `pmHaarDilationSum_energy_mono`: the energy increases with the finite index set.

## Hypotheses

All results are unconditional; the only hypotheses are positivity of the dilation
parameters (`0 < a`, `0 < b`, or `0 < a_i` on the index set) and order relations such as
`a ≤ b` or `2a ≤ b` where stated.
-/

open MeasureTheory Set Filter Topology Complex
noncomputable section
namespace RHTower

/-- The real cutoff `1_(0,c]`, the building block of dilated dyadic Haar functions. -/
def pmHaarCutoff (c : ℝ) : ℝ → ℝ := (Ioc (0 : ℝ) c).indicator (fun _ => 1)

theorem integrable_pmHaarCutoff (c : ℝ) :
    Integrable (pmHaarCutoff c) (volume.restrict (Ioi 0)) := by
  have h : Integrable (pmHaarCutoff c) volume :=
    (integrable_indicator_iff measurableSet_Ioc).mpr
      (integrableOn_const (C := (1 : ℝ)) measure_Ioc_lt_top.ne)
  exact h.mono_measure Measure.restrict_le_self

theorem pmHaarCutoff_integral {c : ℝ} (hc : 0 ≤ c) :
    (∫ t in Ioi (0 : ℝ), pmHaarCutoff c t) = c := by
  unfold pmHaarCutoff
  rw [setIntegral_indicator measurableSet_Ioc,
    Set.inter_eq_right.mpr (show Ioc (0 : ℝ) c ⊆ Ioi 0 from Ioc_subset_Ioi_self)]
  simp [hc]

theorem pmHaarCutoff_mul (a b t : ℝ) :
    pmHaarCutoff a t * pmHaarCutoff b t = pmHaarCutoff (min a b) t := by
  by_cases h0 : 0 < t <;> by_cases ha : t ≤ a <;> by_cases hb : t ≤ b <;>
    simp [pmHaarCutoff, Set.indicator, Set.mem_Ioc, h0, ha, hb]

theorem integrable_pmHaarCutoff_mul (a b : ℝ) :
    Integrable (fun t => pmHaarCutoff a t * pmHaarCutoff b t) (volume.restrict (Ioi 0)) := by
  simpa only [pmHaarCutoff_mul] using integrable_pmHaarCutoff (min a b)

/-- For `a, b ≥ 0`, `∫₀^∞ 1_(0,a] 1_(0,b] = min a b`. -/
theorem pmHaarCutoff_mul_integral {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (∫ t in Ioi (0 : ℝ), pmHaarCutoff a t * pmHaarCutoff b t) = min a b := by
  simp_rw [pmHaarCutoff_mul]
  exact pmHaarCutoff_integral (le_min ha hb)

/-- For `a > 0`, `Re h(a t) = 1_(0,1/a](t) − 2·1_(0,1/(2a)](t)`. -/
theorem pmSupportedDyadicHaar_dilation_re {a : ℝ} (ha : 0 < a) (t : ℝ) :
    (pmSupportedDyadicHaar (a * t)).re = pmHaarCutoff (1 / a) t - 2 * pmHaarCutoff (1 / (2 * a)) t := by
  by_cases ht : 0 < t
  · rw [pmSupportedDyadicHaar_eq_cutoffs (mul_pos ha ht)]
    have h1 : t ≤ 1 / a ↔ a * t ≤ 1 := by rw [le_div_iff₀ ha]; simp [mul_comm]
    have h2 : t ≤ 1 / (2 * a) ↔ a * t ≤ 1 / 2 := by
      rw [le_div_iff₀ (mul_pos (by norm_num) ha)]
      constructor <;> intro h <;> nlinarith
    simp only [pmHaarCutoff, Set.indicator, Set.mem_Ioc, ht, true_and, h1, h2]
    split_ifs <;> norm_num
  · have hat : ¬ 0 < a * t := not_lt.mpr (mul_nonpos_of_nonneg_of_nonpos ha.le (le_of_not_gt ht))
    simp [pmSupportedDyadicHaar, pmHaarCutoff, Set.indicator, Set.mem_Ioc, ht, hat]

/-- For `a, b > 0`, the product `Re h(a t)·Re h(b t)` expands into four cutoffs at the
pairwise minima of `1/a, 1/(2a)` and `1/b, 1/(2b)`. -/
theorem pmSupportedDyadicHaar_dilation_product {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (t : ℝ) :
    (pmSupportedDyadicHaar (a * t)).re * (pmSupportedDyadicHaar (b * t)).re =
      pmHaarCutoff (min (1 / a) (1 / b)) t -
      2 * pmHaarCutoff (min (1 / a) (1 / (2 * b))) t -
      2 * pmHaarCutoff (min (1 / (2 * a)) (1 / b)) t +
      4 * pmHaarCutoff (min (1 / (2 * a)) (1 / (2 * b))) t := by
  rw [pmSupportedDyadicHaar_dilation_re ha, pmSupportedDyadicHaar_dilation_re hb]
  simp only [← pmHaarCutoff_mul]
  ring

theorem integrable_pmSupportedDyadicHaar_dilation_product {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Integrable (fun t => (pmSupportedDyadicHaar (a * t)).re *
      (pmSupportedDyadicHaar (b * t)).re) (volume.restrict (Ioi 0)) := by
  simp_rw [pmSupportedDyadicHaar_dilation_product ha hb]
  exact (((integrable_pmHaarCutoff _).sub ((integrable_pmHaarCutoff _).const_mul 2)).sub
    ((integrable_pmHaarCutoff _).const_mul 2)).add ((integrable_pmHaarCutoff _).const_mul 4)

/-- The Gram entry `∫₀^∞ Re h(a t)·Re h(b t) dt` of two dilated supported dyadic Haar functions. -/
def pmHaarDilationGram (a b : ℝ) : ℝ :=
  ∫ t in Ioi (0 : ℝ), (pmSupportedDyadicHaar (a * t)).re * (pmSupportedDyadicHaar (b * t)).re

/-- For `a, b > 0`, the Gram entry equals
`min(1/a,1/b) − 2 min(1/a,1/(2b)) − 2 min(1/(2a),1/b) + 4 min(1/(2a),1/(2b))`. -/
theorem pmHaarDilationGram_eq_min {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    pmHaarDilationGram a b = min (1 / a) (1 / b) -
      2 * min (1 / a) (1 / (2 * b)) - 2 * min (1 / (2 * a)) (1 / b) +
      4 * min (1 / (2 * a)) (1 / (2 * b)) := by
  unfold pmHaarDilationGram
  simp_rw [pmSupportedDyadicHaar_dilation_product ha hb]
  erw [integral_add (((integrable_pmHaarCutoff _).sub ((integrable_pmHaarCutoff _).const_mul 2)).sub
    ((integrable_pmHaarCutoff _).const_mul 2)) ((integrable_pmHaarCutoff _).const_mul 4),
    integral_sub ((integrable_pmHaarCutoff _).sub ((integrable_pmHaarCutoff _).const_mul 2))
      ((integrable_pmHaarCutoff _).const_mul 2),
    integral_sub (integrable_pmHaarCutoff _) ((integrable_pmHaarCutoff _).const_mul 2)]
  simp only [integral_const_mul]
  rw [pmHaarCutoff_integral (by positivity), pmHaarCutoff_integral (by positivity),
    pmHaarCutoff_integral (by positivity), pmHaarCutoff_integral (by positivity)]

theorem pmHaarDilationGram_comm (a b : ℝ) : pmHaarDilationGram a b = pmHaarDilationGram b a := by
  unfold pmHaarDilationGram
  congr 1
  funext t
  ring

/-- For `0 < a ≤ b`, the Gram entry equals `2/b − 2 min(1/(2a), 1/b)`. -/
theorem pmHaarDilationGram_eq_of_le {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    pmHaarDilationGram a b = 2 / b - 2 * min (1 / (2 * a)) (1 / b) := by
  have hb := ha.trans_le hab
  have hba := one_div_le_one_div_of_le ha hab
  have hhalf : 1 / (2 * b) ≤ 1 / (2 * a) :=
    one_div_le_one_div_of_le (by positivity) (by linarith)
  have hba2 : 1 / (2 * b) ≤ 1 / a := one_div_le_one_div_of_le ha (by linarith)
  rw [pmHaarDilationGram_eq_min ha hb, min_eq_right hba, min_eq_right hba2, min_eq_right hhalf]
  ring

/-- Dilated supported Haar functions have nonnegative pairwise inner products for `a, b > 0`. -/
theorem pmHaarDilationGram_nonneg {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    0 ≤ pmHaarDilationGram a b := by
  wlog hab : a ≤ b generalizing a b
  · rw [pmHaarDilationGram_comm]
    exact this hb ha (le_of_not_ge hab)
  rw [pmHaarDilationGram_eq_of_le ha hab]
  have h := min_le_right (1 / (2 * a)) (1 / b)
  rw [show 2 / b = 2 * (1 / b) by ring]
  linarith

/-- The diagonal Gram entry: `‖h(a·)‖² = 1/a` for `a > 0`. -/
theorem pmHaarDilationGram_self {a : ℝ} (ha : 0 < a) : pmHaarDilationGram a a = 1 / a := by
  rw [pmHaarDilationGram_eq_of_le ha le_rfl,
    min_eq_left (one_div_le_one_div_of_le ha (by linarith : a ≤ 2 * a))]
  ring

/-- Closed form of the Gram entry for `a, b > 0`: `max 0 (2/max a b − 1/min a b)`. -/
theorem pmHaarDilationGram_eq_max {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    pmHaarDilationGram a b = max 0 (2 / max a b - 1 / min a b) := by
  wlog hab : a ≤ b generalizing a b
  · rw [pmHaarDilationGram_comm, max_comm a b, min_comm a b]
    exact this hb ha (le_of_not_ge hab)
  rw [max_eq_right hab, min_eq_left hab, pmHaarDilationGram_eq_of_le ha hab]
  have hhalf : 2 * (1 / (2 * a)) = 1 / a := by ring
  have hdouble : 2 * (1 / b) = 2 / b := by ring
  rcases le_total (1 / (2 * a)) (1 / b) with h | h
  · rw [min_eq_left h, max_eq_right (by nlinarith)]
    rw [hhalf]
  · rw [min_eq_right h, max_eq_left (by nlinarith)]
    linarith

/-- Dilations at least a factor two apart are orthogonal: `2a ≤ b` gives Gram entry `0`. -/
theorem pmHaarDilationGram_eq_zero_of_two_mul_le {a b : ℝ} (ha : 0 < a) (hab : 2 * a ≤ b) :
    pmHaarDilationGram a b = 0 := by
  rw [pmHaarDilationGram_eq_of_le ha (by linarith),
    min_eq_right (one_div_le_one_div_of_le (by positivity) hab)]
  ring

theorem pmSupportedDyadicHaar_im (t : ℝ) : (pmSupportedDyadicHaar t).im = 0 := by
  by_cases ht : t ∈ Ioc (0 : ℝ) 1
  · rw [pmSupportedDyadicHaar, Set.indicator_of_mem ht]
    unfold dyadicHaar
    split_ifs <;> simp
  · simp [pmSupportedDyadicHaar, Set.indicator_of_notMem ht]

/-- For `a > 0`, the dilation `t ↦ h(a t)` lies in `L²(0,∞)`. -/
theorem memLp_pmSupportedDyadicHaar_dilation {a : ℝ} (ha : 0 < a) :
    MemLp (fun t => pmSupportedDyadicHaar (a * t)) 2 (volume.restrict (Ioi 0)) := by
  apply (memLp_two_iff_integrable_sq_norm
    (measurable_pmSupportedDyadicHaar.comp (measurable_const.mul measurable_id)).aestronglyMeasurable).mpr
  apply (integrableOn_Ioi_comp_mul_left_iff
    (fun t => ‖pmSupportedDyadicHaar t‖ ^ (2 : ℕ)) 0 ha).mpr
  change Integrable (fun t => ‖pmSupportedDyadicHaar t‖ ^ (2 : ℕ)) (volume.restrict (Ioi (a * 0)))
  simpa only [mul_zero] using integrable_pmSupportedDyadicHaar_norm_sq

/-- For `a > 0`, `∫₀^∞ |h(a t)|² dt = 1/a`. -/
theorem pmSupportedDyadicHaar_dilation_energy {a : ℝ} (ha : 0 < a) :
    (∫ t in Ioi (0 : ℝ), ‖pmSupportedDyadicHaar (a * t)‖ ^ (2 : ℕ)) = 1 / a := by
  rw [integral_comp_mul_left_Ioi (fun t => ‖pmSupportedDyadicHaar t‖ ^ (2 : ℕ)) 0 ha,
    mul_zero, pmSupportedDyadicHaar_energy]
  simp

/-- The finite sum `∑_{i∈S} h(a_i t)` of dilated supported dyadic Haar functions. -/
def pmHaarDilationSum {ι : Type*} (S : Finset ι) (a : ι → ℝ) (t : ℝ) : ℂ :=
  ∑ i ∈ S, pmSupportedDyadicHaar (a i * t)

theorem memLp_pmHaarDilationSum {ι : Type*} (S : Finset ι) (a : ι → ℝ)
    (ha : ∀ i ∈ S, 0 < a i) :
    MemLp (pmHaarDilationSum S a) 2 (volume.restrict (Ioi 0)) := by
  unfold pmHaarDilationSum
  apply memLp_finsetSum
  exact fun i hi => memLp_pmSupportedDyadicHaar_dilation (ha i hi)

theorem pmHaarDilationSum_norm_sq {ι : Type*} (S : Finset ι) (a : ι → ℝ) (t : ℝ) :
    ‖pmHaarDilationSum S a t‖ ^ (2 : ℕ) =
      ∑ i ∈ S, ∑ j ∈ S, (pmSupportedDyadicHaar (a i * t)).re * (pmSupportedDyadicHaar (a j * t)).re := by
  rw [pmHaarDilationSum, Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.re_sum, Complex.im_sum, pmSupportedDyadicHaar_im,
    Finset.sum_const_zero, mul_zero, add_zero]
  exact Finset.sum_mul_sum _ _ _ _

/-- Assuming all `a_i > 0` on `S`, the `L²(0,∞)` energy of `∑_{i∈S} h(a_i t)` is the double
Gram sum `∑_{i,j∈S} Gram(a_i, a_j)`. -/
theorem pmHaarDilationSum_energy {ι : Type*} (S : Finset ι) (a : ι → ℝ)
    (ha : ∀ i ∈ S, 0 < a i) :
    (∫ t in Ioi (0 : ℝ), ‖pmHaarDilationSum S a t‖ ^ (2 : ℕ)) =
      ∑ i ∈ S, ∑ j ∈ S, pmHaarDilationGram (a i) (a j) := by
  simp_rw [pmHaarDilationSum_norm_sq]
  rw [integral_finsetSum S (fun i hi => integrable_finsetSum S
    (fun j hj => integrable_pmSupportedDyadicHaar_dilation_product (ha i hi) (ha j hj)))]
  apply Finset.sum_congr rfl
  intro i hi
  exact integral_finsetSum S (fun j hj =>
    integrable_pmSupportedDyadicHaar_dilation_product (ha i hi) (ha j hj))

/-- Assuming all `a_i > 0` on `S`, the energy of `∑_{i∈S} h(a_i t)` is at least the diagonal
sum `∑_{i∈S} 1/a_i`, by Gram nonnegativity. -/
theorem pmHaarDilationSum_diagonal_le_energy {ι : Type*} (S : Finset ι) (a : ι → ℝ)
    (ha : ∀ i ∈ S, 0 < a i) :
    (∑ i ∈ S, 1 / a i) ≤ (∫ t in Ioi (0 : ℝ), ‖pmHaarDilationSum S a t‖ ^ (2 : ℕ)) := by
  rw [pmHaarDilationSum_energy S a ha]
  apply Finset.sum_le_sum
  intro i hi
  rw [← pmHaarDilationGram_self (ha i hi)]
  exact Finset.single_le_sum (fun j hj => pmHaarDilationGram_nonneg (ha i hi) (ha j hj)) hi

/-- For `S ⊆ T` and all `a_i > 0` on `T`, the energy of the Haar dilation sum over `S` is at
most the energy over `T`. -/
theorem pmHaarDilationSum_energy_mono {ι : Type*} {S T : Finset ι} (hST : S ⊆ T) (a : ι → ℝ)
    (ha : ∀ i ∈ T, 0 < a i) :
    (∫ t in Ioi (0 : ℝ), ‖pmHaarDilationSum S a t‖ ^ (2 : ℕ)) ≤
      (∫ t in Ioi (0 : ℝ), ‖pmHaarDilationSum T a t‖ ^ (2 : ℕ)) := by
  rw [pmHaarDilationSum_energy S a (fun i hi => ha i (hST hi)), pmHaarDilationSum_energy T a ha]
  calc
    _ ≤ ∑ i ∈ S, ∑ j ∈ T, pmHaarDilationGram (a i) (a j) := by
      apply Finset.sum_le_sum
      intro i hi
      exact Finset.sum_le_sum_of_subset_of_nonneg hST
        (fun j hj _ => pmHaarDilationGram_nonneg (ha i (hST hi)) (ha j hj))
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hST (fun i hi _ =>
      Finset.sum_nonneg (fun j hj => pmHaarDilationGram_nonneg (ha i hi) (ha j hj)))

end RHTower
