import Mathlib

/-!
# Pairing finite complex measures with bounded functions

A finite complex measure `c` has the Jordan parts `c = re⁺ - re⁻ + i (im⁺ - im⁻)`, four finite
positive measures.  The pairing `⟨c, g⟩ = ∫ g dre⁺ - ∫ g dre⁻ + i (∫ g dim⁺ - ∫ g dim⁻)` of `c`
with a bounded measurable `g : X → ℂ` does not depend on the chosen splitting: whenever
`re c = μ₁ - ν₁` and `im c = μ₂ - ν₂` with finite positive `μ_j, ν_j`, the pairing equals
`∫ g dμ₁ - ∫ g dν₁ + i (∫ g dμ₂ - ∫ g dν₂)`.  Consequently the pairing is `ℂ`-linear in `c`, and
`⟨∑ w_a ν_a, g⟩ = ∑ w_a ∫ g dν_a` for every finite combination of finite positive measures.
-/

open MeasureTheory Complex
open scoped ENNReal NNReal

noncomputable section

namespace GaloisForLFunctions.HTGeometry.MeasureConvolution

variable {X : Type*} [MeasurableSpace X]

/-- A finite positive measure as a complex measure. -/
def ofMeasure (μ : Measure X) [IsFiniteMeasure μ] : ComplexMeasure X :=
  μ.toSignedMeasure.toComplexMeasure 0

/-- The Jordan parts `re⁺, re⁻, im⁺, im⁻` of a complex measure. -/
def jordanPart (c : ComplexMeasure X) : Fin 4 → Measure X
  | 0 => (ComplexMeasure.re c).toJordanDecomposition.posPart
  | 1 => (ComplexMeasure.re c).toJordanDecomposition.negPart
  | 2 => (ComplexMeasure.im c).toJordanDecomposition.posPart
  | 3 => (ComplexMeasure.im c).toJordanDecomposition.negPart

instance (c : ComplexMeasure X) (a : Fin 4) : IsFiniteMeasure (jordanPart c a) := by
  fin_cases a <;> simp only [jordanPart] <;> infer_instance

/-- The weights `1, -1, i, -i` of the Jordan parts. -/
def jordanWeight : Fin 4 → ℂ
  | 0 => 1
  | 1 => -1
  | 2 => I
  | 3 => -I

/-- The pairing `⟨c, g⟩ = ∑_a w_a ∫ g d(c_a)` over the Jordan parts. -/
def pair (c : ComplexMeasure X) (g : X → ℂ) : ℂ :=
  ∑ a, jordanWeight a * ∫ x, g x ∂(jordanPart c a)

/-- A bounded measurable test function. -/
structure IsTest (g : X → ℂ) : Prop where
  measurable : Measurable g
  bounded : ∃ C, ∀ x, ‖g x‖ ≤ C

theorem IsTest.integrable {g : X → ℂ} (hg : IsTest g) (μ : Measure X) [IsFiniteMeasure μ] :
    Integrable g μ := by
  obtain ⟨C, hC⟩ := hg.bounded
  exact (integrable_const C).mono' hg.measurable.aestronglyMeasurable (ae_of_all _ hC)

theorem pair_eq (c : ComplexMeasure X) (g : X → ℂ) :
    pair c g = (∫ x, g x ∂jordanPart c 0 - ∫ x, g x ∂jordanPart c 1) +
      I * (∫ x, g x ∂jordanPart c 2 - ∫ x, g x ∂jordanPart c 3) := by
  simp only [pair, Fin.sum_univ_four, jordanWeight]
  ring

theorem re_eq_jordan (c : ComplexMeasure X) :
    ComplexMeasure.re c = (jordanPart c 0).toSignedMeasure - (jordanPart c 1).toSignedMeasure :=
  (SignedMeasure.toSignedMeasure_toJordanDecomposition _).symm

theorem im_eq_jordan (c : ComplexMeasure X) :
    ComplexMeasure.im c = (jordanPart c 2).toSignedMeasure - (jordanPart c 3).toSignedMeasure :=
  (SignedMeasure.toSignedMeasure_toJordanDecomposition _).symm

/-- Two splittings of one signed measure give the same difference of integrals. -/
theorem integral_sub_eq_of_toSignedMeasure {μ₁ ν₁ μ₂ ν₂ : Measure X} [IsFiniteMeasure μ₁]
    [IsFiniteMeasure ν₁] [IsFiniteMeasure μ₂] [IsFiniteMeasure ν₂]
    (h : μ₁.toSignedMeasure - ν₁.toSignedMeasure = μ₂.toSignedMeasure - ν₂.toSignedMeasure)
    {g : X → ℂ} (hg : IsTest g) :
    ∫ x, g x ∂μ₁ - ∫ x, g x ∂ν₁ = ∫ x, g x ∂μ₂ - ∫ x, g x ∂ν₂ := by
  have hsum : μ₁ + ν₂ = μ₂ + ν₁ := by
    rw [← Measure.toSignedMeasure_eq_toSignedMeasure_iff, Measure.toSignedMeasure_add,
      Measure.toSignedMeasure_add]
    rwa [sub_eq_sub_iff_add_eq_add] at h
  have := congrArg (fun m => ∫ x, g x ∂m) hsum
  rw [integral_add_measure (hg.integrable μ₁) (hg.integrable ν₂),
    integral_add_measure (hg.integrable μ₂) (hg.integrable ν₁)] at this
  linear_combination this

/-- **Independence of the splitting.** -/
theorem pair_eq_of_split (c : ComplexMeasure X) {μ₁ ν₁ μ₂ ν₂ : Measure X} [IsFiniteMeasure μ₁]
    [IsFiniteMeasure ν₁] [IsFiniteMeasure μ₂] [IsFiniteMeasure ν₂]
    (hre : ComplexMeasure.re c = μ₁.toSignedMeasure - ν₁.toSignedMeasure)
    (him : ComplexMeasure.im c = μ₂.toSignedMeasure - ν₂.toSignedMeasure) {g : X → ℂ}
    (hg : IsTest g) :
    pair c g = (∫ x, g x ∂μ₁ - ∫ x, g x ∂ν₁) + I * (∫ x, g x ∂μ₂ - ∫ x, g x ∂ν₂) := by
  rw [pair_eq, integral_sub_eq_of_toSignedMeasure ((re_eq_jordan c).symm.trans hre) hg,
    integral_sub_eq_of_toSignedMeasure ((im_eq_jordan c).symm.trans him) hg]

/-! ### Linearity -/

theorem re_ofMeasure (μ : Measure X) [IsFiniteMeasure μ] :
    ComplexMeasure.re (ofMeasure μ) = μ.toSignedMeasure := by
  ext i hi
  simp [ofMeasure, ComplexMeasure.re_apply, SignedMeasure.toComplexMeasure_apply]

theorem im_ofMeasure (μ : Measure X) [IsFiniteMeasure μ] :
    ComplexMeasure.im (ofMeasure μ) = 0 := by
  ext i hi
  simp [ofMeasure, ComplexMeasure.im_apply, SignedMeasure.toComplexMeasure_apply]

theorem pair_ofMeasure (μ : Measure X) [IsFiniteMeasure μ] {g : X → ℂ} (hg : IsTest g) :
    pair (ofMeasure μ) g = ∫ x, g x ∂μ := by
  rw [pair_eq_of_split (ofMeasure μ) (μ₁ := μ) (ν₁ := 0) (μ₂ := 0) (ν₂ := 0)
    (by rw [re_ofMeasure]; simp) (by rw [im_ofMeasure]; simp) hg]
  simp

theorem pair_zero {g : X → ℂ} (hg : IsTest g) : pair (0 : ComplexMeasure X) g = 0 := by
  rw [pair_eq_of_split (0 : ComplexMeasure X) (μ₁ := 0) (ν₁ := 0) (μ₂ := 0) (ν₂ := 0)
    (by simp) (by simp) hg]
  simp

theorem pair_add (c d : ComplexMeasure X) {g : X → ℂ} (hg : IsTest g) :
    pair (c + d) g = pair c g + pair d g := by
  rw [pair_eq_of_split (c + d) (μ₁ := jordanPart c 0 + jordanPart d 0)
      (ν₁ := jordanPart c 1 + jordanPart d 1) (μ₂ := jordanPart c 2 + jordanPart d 2)
      (ν₂ := jordanPart c 3 + jordanPart d 3) ?_ ?_ hg, pair_eq c, pair_eq d,
    integral_add_measure (hg.integrable _) (hg.integrable _),
    integral_add_measure (hg.integrable _) (hg.integrable _),
    integral_add_measure (hg.integrable _) (hg.integrable _),
    integral_add_measure (hg.integrable _) (hg.integrable _)]
  · ring
  · rw [map_add, re_eq_jordan c, re_eq_jordan d, Measure.toSignedMeasure_add,
      Measure.toSignedMeasure_add]
    abel
  · rw [map_add, im_eq_jordan c, im_eq_jordan d, Measure.toSignedMeasure_add,
      Measure.toSignedMeasure_add]
    abel

theorem pair_neg (c : ComplexMeasure X) {g : X → ℂ} (hg : IsTest g) :
    pair (-c) g = -pair c g := by
  rw [pair_eq_of_split (-c) (μ₁ := jordanPart c 1) (ν₁ := jordanPart c 0)
      (μ₂ := jordanPart c 3) (ν₂ := jordanPart c 2) ?_ ?_ hg, pair_eq c]
  · ring
  · rw [map_neg, re_eq_jordan c]; abel
  · rw [map_neg, im_eq_jordan c]; abel

theorem pair_sub (c d : ComplexMeasure X) {g : X → ℂ} (hg : IsTest g) :
    pair (c - d) g = pair c g - pair d g := by
  rw [sub_eq_add_neg, pair_add _ _ hg, pair_neg _ hg, sub_eq_add_neg]

theorem pair_nsmul (n : ℕ) (c : ComplexMeasure X) {g : X → ℂ} (hg : IsTest g) :
    pair (n • c) g = n • pair c g := by
  induction n with
  | zero => rw [zero_nsmul, zero_nsmul, pair_zero hg]
  | succ n ih => rw [succ_nsmul, succ_nsmul, pair_add _ _ hg, ih]

theorem pair_zsmul (n : ℤ) (c : ComplexMeasure X) {g : X → ℂ} (hg : IsTest g) :
    pair (n • c) g = n • pair c g := by
  cases n with
  | ofNat n => rw [Int.ofNat_eq_natCast, natCast_zsmul, natCast_zsmul, pair_nsmul _ _ hg]
  | negSucc n => rw [negSucc_zsmul, negSucc_zsmul, pair_neg _ hg, pair_nsmul _ _ hg]

theorem re_smul_I (c : ComplexMeasure X) :
    ComplexMeasure.re (I • c) = -ComplexMeasure.im c := by
  ext i hi
  simp [ComplexMeasure.re_apply, ComplexMeasure.im_apply]

theorem im_smul_I (c : ComplexMeasure X) :
    ComplexMeasure.im (I • c) = ComplexMeasure.re c := by
  ext i hi
  simp [ComplexMeasure.re_apply, ComplexMeasure.im_apply]

theorem pair_smul_I (c : ComplexMeasure X) {g : X → ℂ} (hg : IsTest g) :
    pair (I • c) g = I * pair c g := by
  rw [pair_eq_of_split (I • c) (μ₁ := jordanPart c 3) (ν₁ := jordanPart c 2)
      (μ₂ := jordanPart c 0) (ν₂ := jordanPart c 1) ?_ ?_ hg, pair_eq c]
  · ring_nf
    rw [I_sq]
    ring
  · rw [re_smul_I, im_eq_jordan c]; abel
  · rw [im_smul_I, re_eq_jordan c]

theorem re_smul_real (r : ℝ) (c : ComplexMeasure X) :
    ComplexMeasure.re ((r : ℂ) • c) = r • ComplexMeasure.re c := by
  ext i hi
  simp [ComplexMeasure.re_apply]

theorem im_smul_real (r : ℝ) (c : ComplexMeasure X) :
    ComplexMeasure.im ((r : ℂ) • c) = r • ComplexMeasure.im c := by
  ext i hi
  simp [ComplexMeasure.im_apply]

theorem toSignedMeasure_smul_real_split (r : ℝ) (μ ν : Measure X) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] :
    r • (μ.toSignedMeasure - ν.toSignedMeasure) =
      ((Real.toNNReal r • μ) + (Real.toNNReal (-r) • ν)).toSignedMeasure -
        ((Real.toNNReal r • ν) + (Real.toNNReal (-r) • μ)).toSignedMeasure := by
  rw [Measure.toSignedMeasure_add, Measure.toSignedMeasure_add, Measure.toSignedMeasure_smul,
    Measure.toSignedMeasure_smul, Measure.toSignedMeasure_smul, Measure.toSignedMeasure_smul]
  have hr : r = (Real.toNNReal r : ℝ) - (Real.toNNReal (-r) : ℝ) := by
    rw [Real.coe_toNNReal', Real.coe_toNNReal']
    rcases le_total 0 r with h | h
    · rw [max_eq_left h, max_eq_right (by linarith)]; ring
    · rw [max_eq_right h, max_eq_left (by linarith)]; ring
  simp only [NNReal.smul_def]
  conv_lhs => rw [hr]
  module

theorem integral_nnreal_smul (r : ℝ≥0) (μ : Measure X) (g : X → ℂ) :
    ∫ x, g x ∂(r • μ) = (r : ℂ) * ∫ x, g x ∂μ := by
  rw [show r • μ = (r : ℝ≥0∞) • μ from rfl, integral_smul_measure, ENNReal.coe_toReal,
    Complex.real_smul]

theorem pair_smul_real (r : ℝ) (c : ComplexMeasure X) {g : X → ℂ} (hg : IsTest g) :
    pair ((r : ℂ) • c) g = r * pair c g := by
  rw [pair_eq_of_split ((r : ℂ) • c)
      (μ₁ := Real.toNNReal r • jordanPart c 0 + Real.toNNReal (-r) • jordanPart c 1)
      (ν₁ := Real.toNNReal r • jordanPart c 1 + Real.toNNReal (-r) • jordanPart c 0)
      (μ₂ := Real.toNNReal r • jordanPart c 2 + Real.toNNReal (-r) • jordanPart c 3)
      (ν₂ := Real.toNNReal r • jordanPart c 3 + Real.toNNReal (-r) • jordanPart c 2) ?_ ?_ hg,
    pair_eq c]
  · have hr : (r : ℂ) = ((Real.toNNReal r : ℝ) : ℂ) - ((Real.toNNReal (-r) : ℝ) : ℂ) := by
      rw [Real.coe_toNNReal', Real.coe_toNNReal']
      rcases le_total 0 r with h | h
      · rw [max_eq_left h, max_eq_right (by linarith)]; push_cast; ring
      · rw [max_eq_right h, max_eq_left (by linarith)]; push_cast; ring
    simp only [integral_add_measure (hg.integrable _) (hg.integrable _), integral_nnreal_smul]
    rw [hr]
    ring
  · rw [re_smul_real, re_eq_jordan c, toSignedMeasure_smul_real_split]
  · rw [im_smul_real, im_eq_jordan c, toSignedMeasure_smul_real_split]

/-- The pairing is `ℂ`-linear. -/
theorem pair_smul (w : ℂ) (c : ComplexMeasure X) {g : X → ℂ} (hg : IsTest g) :
    pair (w • c) g = w * pair c g := by
  have hw : w • c = (w.re : ℂ) • c + (w.im : ℂ) • (I • c) := by
    ext i hi
    simp only [FunLike.coe_add, Pi.add_apply, FunLike.coe_smul, Pi.smul_apply,
      smul_eq_mul]
    conv_lhs => rw [← Complex.re_add_im w]
    ring
  rw [hw, pair_add _ _ hg, pair_smul_real _ _ hg, pair_smul_real _ _ hg, pair_smul_I _ hg]
  conv_rhs => rw [← Complex.re_add_im w]
  ring

/-- `⟨∑ w_a ν_a, g⟩ = ∑ w_a ∫ g dν_a`. -/
theorem pair_sum_smul_ofMeasure {ι : Type*} (s : Finset ι) (w : ι → ℂ) (ν : ι → Measure X)
    [∀ i, IsFiniteMeasure (ν i)] {g : X → ℂ} (hg : IsTest g) :
    pair (∑ i ∈ s, w i • ofMeasure (ν i)) g = ∑ i ∈ s, w i * ∫ x, g x ∂ν i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [pair_zero hg]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, pair_add _ _ hg, ih, pair_smul _ _ hg,
      pair_ofMeasure _ hg]

end GaloisForLFunctions.HTGeometry.MeasureConvolution
