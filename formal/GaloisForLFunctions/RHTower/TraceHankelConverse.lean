import Mathlib

open Complex Polynomial Filter Topology
open scoped BigOperators

namespace RHTower

noncomputable section

/-- The real quadratic whose complex roots are `beta` and `conj beta`. -/
def realConjQuadratic (β : ℂ) : Polynomial ℝ :=
  X ^ 2 - C (2 * β.re) * X + C (Complex.normSq β)

/-- Evaluation of a real polynomial at a complex point. -/
def evalRealPolynomial (p : Polynomial ℝ) (z : ℂ) : ℂ :=
  (p.map (algebraMap ℝ ℂ)).eval z

@[simp] theorem evalRealPolynomial_zero (z : ℂ) : evalRealPolynomial 0 z = 0 := by
  simp [evalRealPolynomial]

@[simp] theorem evalRealPolynomial_one (z : ℂ) : evalRealPolynomial 1 z = 1 := by
  simp [evalRealPolynomial]

@[simp] theorem evalRealPolynomial_mul (p q : Polynomial ℝ) (z : ℂ) :
    evalRealPolynomial (p * q) z = evalRealPolynomial p z * evalRealPolynomial q z := by
  simp [evalRealPolynomial]

@[simp] theorem evalRealPolynomial_pow (p : Polynomial ℝ) (z : ℂ) (n : ℕ) :
    evalRealPolynomial (p ^ n) z = evalRealPolynomial p z ^ n := by
  simp [evalRealPolynomial]

theorem evalRealConjQuadratic (β z : ℂ) :
    evalRealPolynomial (realConjQuadratic β) z =
      (z - β) * (z - (starRingEnd ℂ) β) := by
  apply Complex.ext <;>
    simp [evalRealPolynomial, realConjQuadratic, Complex.normSq_apply, pow_two,
      mul_re, mul_im] <;> ring

theorem evalRealConjQuadratic_eq_zero_iff (β z : ℂ) :
    evalRealPolynomial (realConjQuadratic β) z = 0 ↔
      z = β ∨ z = (starRingEnd ℂ) β := by
  rw [evalRealConjQuadratic, mul_eq_zero, sub_eq_zero, sub_eq_zero]

/-- A real polynomial vanishing on every selected spectral orbit except the target conjugate pair. -/
def realOrbitSeparator (F : Finset ℂ) (α : ℂ) : Polynomial ℝ :=
  ∏ β ∈ F.filter (fun β => β ≠ α ∧ β ≠ (starRingEnd ℂ) α), realConjQuadratic β

theorem evalRealOrbitSeparator_eq_zero {F : Finset ℂ} {α γ : ℂ}
    (hγ : γ ∈ F) (hγα : γ ≠ α) (hγc : γ ≠ (starRingEnd ℂ) α) :
    evalRealPolynomial (realOrbitSeparator F α) γ = 0 := by
  rw [realOrbitSeparator]
  rw [evalRealPolynomial,
    Polynomial.map_prod (algebraMap ℝ ℂ) realConjQuadratic
      (F.filter (fun β => β ≠ α ∧ β ≠ (starRingEnd ℂ) α)),
    Polynomial.eval_prod]
  apply Finset.prod_eq_zero (Finset.mem_filter.mpr ⟨hγ, hγα, hγc⟩)
  rw [show ((realConjQuadratic γ).map (algebraMap ℝ ℂ)).eval γ =
      evalRealPolynomial (realConjQuadratic γ) γ by rfl,
    evalRealConjQuadratic]
  simp

theorem evalRealOrbitSeparator_ne_zero {F : Finset ℂ} {α : ℂ} :
    evalRealPolynomial (realOrbitSeparator F α) α ≠ 0 := by
  rw [realOrbitSeparator]
  rw [evalRealPolynomial,
    Polynomial.map_prod (algebraMap ℝ ℂ) realConjQuadratic
      (F.filter (fun β => β ≠ α ∧ β ≠ (starRingEnd ℂ) α)),
    Polynomial.eval_prod]
  apply Finset.prod_ne_zero_iff.mpr
  intro β hβ
  have hsel := (Finset.mem_filter.mp hβ).2
  change evalRealPolynomial (realConjQuadratic β) α ≠ 0
  intro hz
  rw [evalRealConjQuadratic_eq_zero_iff] at hz
  rcases hz with h | h
  · exact hsel.1 h.symm
  · have hc : (starRingEnd ℂ) α = β := by
      simpa using congrArg (starRingEnd ℂ) h
    exact hsel.2 hc.symm

/-- The real affine polynomial taking a prescribed complex value at a nonreal point. -/
def realLinearInterpolator (α c : ℂ) : Polynomial ℝ :=
  C (c.re - (c.im / α.im) * α.re) + C (c.im / α.im) * X

theorem evalRealLinearInterpolator {α c : ℂ} (him : α.im ≠ 0) :
    evalRealPolynomial (realLinearInterpolator α c) α = c := by
  apply Complex.ext
  · simp [evalRealPolynomial, realLinearInterpolator]
  · simp [evalRealPolynomial, realLinearInterpolator]
    field_simp

theorem norm_evalRealLinearInterpolator_le {α v z : ℂ} (him : α.im ≠ 0) :
    ‖evalRealPolynomial (realLinearInterpolator α v) z‖ ≤
      (1 + (|α.re| + ‖z‖) / |α.im|) * ‖v‖ := by
  have himabs : 0 < |α.im| := abs_pos.mpr him
  have heval : evalRealPolynomial (realLinearInterpolator α v) z =
      ((v.re - (v.im / α.im) * α.re : ℝ) : ℂ) +
        ((v.im / α.im : ℝ) : ℂ) * z := by
    simp [evalRealPolynomial, realLinearInterpolator]
  rw [heval]
  calc
    ‖((v.re - (v.im / α.im) * α.re : ℝ) : ℂ) +
        ((v.im / α.im : ℝ) : ℂ) * z‖
        ≤ ‖((v.re - (v.im / α.im) * α.re : ℝ) : ℂ)‖ +
          ‖((v.im / α.im : ℝ) : ℂ) * z‖ := norm_add_le _ _
    _ = |v.re - (v.im / α.im) * α.re| + |v.im / α.im| * ‖z‖ := by
      rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
        Real.norm_eq_abs]
    _ ≤ |v.re| + (|v.im| / |α.im|) * |α.re| +
        (|v.im| / |α.im|) * ‖z‖ := by
      rw [abs_div]
      gcongr
      calc
        |v.re - (v.im / α.im) * α.re| ≤ |v.re| + |(v.im / α.im) * α.re| :=
          abs_sub _ _
        _ = |v.re| + (|v.im| / |α.im|) * |α.re| := by
          rw [abs_mul, abs_div]
    _ ≤ ‖v‖ + (‖v‖ / |α.im|) * |α.re| +
        (‖v‖ / |α.im|) * ‖z‖ := by
      gcongr
      · exact Complex.abs_re_le_norm v
      · exact Complex.abs_im_le_norm v
      · exact Complex.abs_im_le_norm v
    _ = (1 + (|α.re| + ‖z‖) / |α.im|) * ‖v‖ := by
      field_simp
      ring

/-- Evaluation of a real polynomial commutes with complex conjugation. -/
theorem evalRealPolynomial_conj (p : Polynomial ℝ) (z : ℂ) :
    evalRealPolynomial p ((starRingEnd ℂ) z) =
      (starRingEnd ℂ) (evalRealPolynomial p z) := by
  simpa [evalRealPolynomial, Polynomial.aeval_def] using
    (Polynomial.aeval_conj p z)

/-- A coefficientwise norm majorant for a real polynomial on a complex disk. -/
def evalRealPolynomialNormBound (p : Polynomial ℝ) (R : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (p.natDegree + 1), ‖p.coeff k‖ * R ^ k

theorem evalRealPolynomialNormBound_nonneg (p : Polynomial ℝ) {R : ℝ} (hR : 0 ≤ R) :
    0 ≤ evalRealPolynomialNormBound p R := by
  apply Finset.sum_nonneg
  intro k _
  positivity

theorem norm_evalRealPolynomial_le (p : Polynomial ℝ) {z : ℂ} {R : ℝ}
    (hz : ‖z‖ ≤ R) :
    ‖evalRealPolynomial p z‖ ≤ evalRealPolynomialNormBound p R := by
  rw [evalRealPolynomial, Polynomial.eval_eq_sum_range]
  calc
    ‖∑ k ∈ Finset.range ((p.map (algebraMap ℝ ℂ)).natDegree + 1),
        (p.map (algebraMap ℝ ℂ)).coeff k * z ^ k‖
        ≤ ∑ k ∈ Finset.range ((p.map (algebraMap ℝ ℂ)).natDegree + 1),
            ‖(p.map (algebraMap ℝ ℂ)).coeff k * z ^ k‖ := norm_sum_le _ _
    _ = ∑ k ∈ Finset.range (p.natDegree + 1), ‖p.coeff k‖ * ‖z‖ ^ k := by
      simp only [Polynomial.natDegree_map_eq_of_injective
          (f := algebraMap ℝ ℂ) Complex.ofReal_injective,
        Polynomial.coeff_map, coe_algebraMap, norm_mul, norm_pow, Complex.norm_real]
    _ ≤ ∑ k ∈ Finset.range (p.natDegree + 1), ‖p.coeff k‖ * R ^ k := by
      apply Finset.sum_le_sum
      intro k _
      gcongr
    _ = evalRealPolynomialNormBound p R := rfl

@[simp] theorem evalRealPolynomial_scaleX (a : ℝ) (z : ℂ) :
    evalRealPolynomial (C a * X) z = (a : ℂ) * z := by
  simp [evalRealPolynomial]

/-- The outer-orbit separator with a bounded affine phase correction and radial monomial. -/
def phaseCorrectedSeparatorPolynomial (F : Finset ℂ) (α c : ℂ) (n : ℕ) : Polynomial ℝ :=
  let sep := realOrbitSeparator F α
  let d := c / evalRealPolynomial sep α
  let u := α / (‖α‖ : ℂ)
  sep * realLinearInterpolator α (d * u⁻¹ ^ n) * (C (‖α‖⁻¹) * X) ^ n

def phaseCorrectedSeparatorNormBound (F : Finset ℂ) (α c : ℂ) : ℝ :=
  let sep := realOrbitSeparator F α
  let d := c / evalRealPolynomial sep α
  evalRealPolynomialNormBound sep ‖α‖ *
    ((1 + (|α.re| + ‖α‖) / |α.im|) * ‖d‖)

theorem phaseCorrectedSeparatorNormBound_nonneg
    (F : Finset ℂ) {α c : ℂ} (him : α.im ≠ 0) :
    0 ≤ phaseCorrectedSeparatorNormBound F α c := by
  dsimp [phaseCorrectedSeparatorNormBound]
  have hpoly := evalRealPolynomialNormBound_nonneg
    (realOrbitSeparator F α) (norm_nonneg α)
  have himabs : 0 < |α.im| := abs_pos.mpr him
  positivity

theorem eval_phaseCorrectedSeparatorPolynomial_target
    {F : Finset ℂ} {α c : ℂ} (hα0 : α ≠ 0) (him : α.im ≠ 0) (n : ℕ) :
    evalRealPolynomial (phaseCorrectedSeparatorPolynomial F α c n) α = c := by
  let sep := realOrbitSeparator F α
  let d := c / evalRealPolynomial sep α
  let u := α / (‖α‖ : ℂ)
  have hsep : evalRealPolynomial sep α ≠ 0 := evalRealOrbitSeparator_ne_zero
  have hr : ‖α‖ ≠ 0 := norm_ne_zero_iff.mpr hα0
  have hu : u ≠ 0 := div_ne_zero hα0 (by exact_mod_cast hr)
  rw [phaseCorrectedSeparatorPolynomial]
  change evalRealPolynomial (sep * realLinearInterpolator α (d * u⁻¹ ^ n) *
    (C (‖α‖⁻¹) * X) ^ n) α = c
  rw [evalRealPolynomial_mul, evalRealPolynomial_mul,
    evalRealLinearInterpolator him]
  have hscale : evalRealPolynomial ((C (‖α‖⁻¹) * X) ^ n) α = u ^ n := by
    rw [evalRealPolynomial_pow, evalRealPolynomial_scaleX]
    congr 1
    dsimp [u]
    push_cast
    field_simp
  rw [hscale]
  dsimp [d]
  field_simp [hsep, hu]
  rw [mul_assoc, ← mul_pow, one_div, inv_mul_cancel₀ hu, one_pow, mul_one]

theorem eval_phaseCorrectedSeparatorPolynomial_conj_target
    {F : Finset ℂ} {α c : ℂ} (hα0 : α ≠ 0) (him : α.im ≠ 0) (n : ℕ) :
    evalRealPolynomial (phaseCorrectedSeparatorPolynomial F α c n)
      ((starRingEnd ℂ) α) = (starRingEnd ℂ) c := by
  rw [evalRealPolynomial_conj,
    eval_phaseCorrectedSeparatorPolynomial_target hα0 him]

theorem eval_phaseCorrectedSeparatorPolynomial_outer_zero
    {F : Finset ℂ} {α z c : ℂ} (hz : z ∈ F) (hzα : z ≠ α)
    (hzc : z ≠ (starRingEnd ℂ) α) (n : ℕ) :
    evalRealPolynomial (phaseCorrectedSeparatorPolynomial F α c n) z = 0 := by
  rw [phaseCorrectedSeparatorPolynomial]
  simp only [evalRealPolynomial_mul,
    evalRealOrbitSeparator_eq_zero hz hzα hzc, zero_mul]

theorem norm_eval_phaseCorrectedSeparatorPolynomial_le
    {F : Finset ℂ} {α z c : ℂ} (hα0 : α ≠ 0) (him : α.im ≠ 0)
    (hz : ‖z‖ ≤ ‖α‖) (n : ℕ) :
    ‖evalRealPolynomial (phaseCorrectedSeparatorPolynomial F α c n) z‖ ≤
      phaseCorrectedSeparatorNormBound F α c := by
  let sep := realOrbitSeparator F α
  let d := c / evalRealPolynomial sep α
  let u := α / (‖α‖ : ℂ)
  have hrpos : 0 < ‖α‖ := norm_pos_iff.mpr hα0
  have hr : ‖α‖ ≠ 0 := ne_of_gt hrpos
  have hu_norm : ‖u‖ = 1 := by
    dsimp [u]
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hrpos,
      div_self hr]
  have hv_norm : ‖d * u⁻¹ ^ n‖ = ‖d‖ := by
    rw [norm_mul, norm_pow, norm_inv, hu_norm, inv_one, one_pow, mul_one]
  have hscale : ‖evalRealPolynomial ((C (‖α‖⁻¹) * X) ^ n) z‖ ≤ 1 := by
    rw [evalRealPolynomial_pow, evalRealPolynomial_scaleX, norm_pow, norm_mul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (le_of_lt hrpos))]
    have hbase : ‖α‖⁻¹ * ‖z‖ ≤ 1 := by
      rw [inv_mul_le_one₀ hrpos]
      exact hz
    exact pow_le_one₀ (mul_nonneg (inv_nonneg.mpr (le_of_lt hrpos)) (norm_nonneg z)) hbase
  rw [phaseCorrectedSeparatorPolynomial]
  change ‖evalRealPolynomial
    (sep * realLinearInterpolator α (d * u⁻¹ ^ n) * (C (‖α‖⁻¹) * X) ^ n) z‖ ≤ _
  rw [evalRealPolynomial_mul, evalRealPolynomial_mul, norm_mul, norm_mul]
  dsimp [phaseCorrectedSeparatorNormBound]
  change _ ≤ evalRealPolynomialNormBound sep ‖α‖ *
    ((1 + (|α.re| + ‖α‖) / |α.im|) * ‖d‖)
  have hsepbound := norm_evalRealPolynomial_le sep hz
  have hinterp := norm_evalRealLinearInterpolator_le
    (α := α) (v := d * u⁻¹ ^ n) (z := z) him
  rw [hv_norm] at hinterp
  have himabs : 0 < |α.im| := abs_pos.mpr him
  have hfactor :
      1 + (|α.re| + ‖z‖) / |α.im| ≤
        1 + (|α.re| + ‖α‖) / |α.im| := by
    gcongr
  have hinterp' : ‖evalRealPolynomial (realLinearInterpolator α (d * u⁻¹ ^ n)) z‖ ≤
      (1 + (|α.re| + ‖α‖) / |α.im|) * ‖d‖ :=
    hinterp.trans (mul_le_mul_of_nonneg_right hfactor (norm_nonneg d))
  have hsepBoundNonneg : 0 ≤ evalRealPolynomialNormBound sep ‖α‖ :=
    evalRealPolynomialNormBound_nonneg sep (norm_nonneg α)
  have hinterpBoundNonneg :
      0 ≤ (1 + (|α.re| + ‖α‖) / |α.im|) * ‖d‖ := by positivity
  calc
    ‖evalRealPolynomial sep z‖ *
        ‖evalRealPolynomial (realLinearInterpolator α (d * u⁻¹ ^ n)) z‖ *
          ‖evalRealPolynomial ((C (‖α‖⁻¹) * X) ^ n) z‖
      ≤ evalRealPolynomialNormBound sep ‖α‖ *
          ((1 + (|α.re| + ‖α‖) / |α.im|) * ‖d‖) * 1 := by
        gcongr
    _ = evalRealPolynomialNormBound sep ‖α‖ *
          ((1 + (|α.re| + ‖α‖) / |α.im|) * ‖d‖) := by ring

theorem tendsto_eval_phaseCorrectedSeparatorPolynomial_zero
    {F : Finset ℂ} {α z c : ℂ} (hα0 : α ≠ 0) (him : α.im ≠ 0)
    (hz : ‖z‖ < ‖α‖) :
    Tendsto (fun n => evalRealPolynomial
      (phaseCorrectedSeparatorPolynomial F α c n) z) atTop (nhds 0) := by
  let sep := realOrbitSeparator F α
  let d := c / evalRealPolynomial sep α
  let u := α / (‖α‖ : ℂ)
  let ratio : ℝ := ‖z‖ / ‖α‖
  have hrpos : 0 < ‖α‖ := norm_pos_iff.mpr hα0
  have hu_norm : ‖u‖ = 1 := by
    dsimp [u]
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hrpos,
      div_self (ne_of_gt hrpos)]
  have hv_norm (n : ℕ) : ‖d * u⁻¹ ^ n‖ = ‖d‖ := by
    rw [norm_mul, norm_pow, norm_inv, hu_norm, inv_one, one_pow, mul_one]
  have hratio_nonneg : 0 ≤ ratio := div_nonneg (norm_nonneg z) (le_of_lt hrpos)
  have hratio_lt : ratio < 1 := (div_lt_one hrpos).mpr hz
  have hnormle (n : ℕ) :
      ‖evalRealPolynomial (phaseCorrectedSeparatorPolynomial F α c n) z‖ ≤
        phaseCorrectedSeparatorNormBound F α c * ratio ^ n := by
    have hzle : ‖z‖ ≤ ‖α‖ := le_of_lt hz
    have hsepbound := norm_evalRealPolynomial_le sep hzle
    have hinterp := norm_evalRealLinearInterpolator_le
      (α := α) (v := d * u⁻¹ ^ n) (z := z) him
    rw [hv_norm] at hinterp
    have himabs : 0 < |α.im| := abs_pos.mpr him
    have hfactor :
        1 + (|α.re| + ‖z‖) / |α.im| ≤
          1 + (|α.re| + ‖α‖) / |α.im| := by
      gcongr
    have hinterp' : ‖evalRealPolynomial
        (realLinearInterpolator α (d * u⁻¹ ^ n)) z‖ ≤
        (1 + (|α.re| + ‖α‖) / |α.im|) * ‖d‖ :=
      hinterp.trans (mul_le_mul_of_nonneg_right hfactor (norm_nonneg d))
    have hscale :
        ‖evalRealPolynomial ((C (‖α‖⁻¹) * X) ^ n) z‖ = ratio ^ n := by
      rw [evalRealPolynomial_pow, evalRealPolynomial_scaleX, norm_pow, norm_mul,
        Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (le_of_lt hrpos))]
      congr 1
      dsimp [ratio]
      rw [inv_mul_eq_div]
    rw [phaseCorrectedSeparatorPolynomial]
    change ‖evalRealPolynomial
      (sep * realLinearInterpolator α (d * u⁻¹ ^ n) * (C (‖α‖⁻¹) * X) ^ n) z‖ ≤ _
    rw [evalRealPolynomial_mul, evalRealPolynomial_mul, norm_mul, norm_mul, hscale]
    dsimp [phaseCorrectedSeparatorNormBound]
    change _ ≤ (evalRealPolynomialNormBound sep ‖α‖ *
      ((1 + (|α.re| + ‖α‖) / |α.im|) * ‖d‖)) * ratio ^ n
    have hsepBoundNonneg : 0 ≤ evalRealPolynomialNormBound sep ‖α‖ :=
      evalRealPolynomialNormBound_nonneg sep (norm_nonneg α)
    have hinterpBoundNonneg :
        0 ≤ (1 + (|α.re| + ‖α‖) / |α.im|) * ‖d‖ := by positivity
    gcongr
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
    (Eventually.of_forall hnormle)
  simpa using
    (tendsto_pow_atTop_nhds_zero_of_lt_one hratio_nonneg hratio_lt).const_mul
      (phaseCorrectedSeparatorNormBound F α c)

/-- Every nonreal complex number admits a complex phase whose squared weighted real part is
strictly negative. -/
theorem exists_phase_sq_re_neg {α : ℂ} (him : α.im ≠ 0) :
    ∃ c : ℂ, (α * c ^ 2).re < 0 := by
  by_cases hre : α.re < 0
  · exact ⟨1, by simpa using hre⟩
  by_cases hre0 : α.re = 0
  · by_cases himpos : 0 < α.im
    · refine ⟨1 + I, ?_⟩
      norm_num [pow_two, mul_re, mul_im]
      linarith
    · refine ⟨1 - I, ?_⟩
      norm_num [pow_two, mul_re, mul_im]
      have himneg : α.im < 0 := by
        rcases lt_or_eq_of_le (not_lt.mp himpos) with hlt | heq
        · exact hlt
        · exact (him heq).elim
      linarith
  · have hrepos : 0 < α.re := lt_of_le_of_ne (not_lt.mp hre) (Ne.symm hre0)
    refine ⟨I, ?_⟩
    simp only [pow_two, I_mul_I, mul_neg, mul_one, neg_re]
    linarith

theorem real_weight_conj_phase_re (w : ℝ) (α c : ℂ) :
    (((w : ℂ) * (starRingEnd ℂ) α * ((starRingEnd ℂ) c) ^ 2).re) =
      w * (α * c ^ 2).re := by
  calc
    _ = (((w : ℂ) * (starRingEnd ℂ) (α * c ^ 2))).re := by
      congr 1
      simp only [map_mul, map_pow]
      ring
    _ = w * (α * c ^ 2).re := by
      rw [mul_re]
      simp only [Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re,
        zero_mul, sub_zero]

theorem real_weight_phase_re (w : ℝ) (α c : ℂ) :
    (((w : ℂ) * α * c ^ 2).re) = w * (α * c ^ 2).re := by
  rw [show ((w : ℂ) * α * c ^ 2) = (w : ℂ) * (α * c ^ 2) by ring]
  simp

/-- A finite conjugation-closed trace spectrum whose real-polynomial Hankel trace is nonnegative
for every test polynomial is necessarily real. This is the finite converse missing from the
forward Gram theorem `secularHankel_posSemidef`. -/
theorem finite_traceHankel_nonneg_implies_real
    (F : Finset ℂ) (w : ℂ → ℝ)
    (hw : ∀ z ∈ F, 0 < w z)
    (hconj : ∀ z ∈ F, (starRingEnd ℂ) z ∈ F)
    (hpos : ∀ p : Polynomial ℝ,
      0 ≤ (∑ z ∈ F, ((w z : ℝ) : ℂ) * z * evalRealPolynomial p z ^ 2).re) :
    ∀ z ∈ F, z.im = 0 := by
  intro α hα
  by_contra him
  have hca : (starRingEnd ℂ) α ∈ F := hconj α hα
  have hca_ne : (starRingEnd ℂ) α ≠ α := Complex.conj_eq_iff_im.not.mpr him
  obtain ⟨c, hc⟩ := exists_phase_sq_re_neg him
  let sep := realOrbitSeparator F α
  have hsep : evalRealPolynomial sep α ≠ 0 := evalRealOrbitSeparator_ne_zero
  let d : ℂ := c / evalRealPolynomial sep α
  let p : Polynomial ℝ := sep * realLinearInterpolator α d
  have hpα : evalRealPolynomial p α = c := by
    simp only [p, evalRealPolynomial_mul, evalRealLinearInterpolator him]
    dsimp [d]
    field_simp
  have hpca : evalRealPolynomial p ((starRingEnd ℂ) α) = (starRingEnd ℂ) c := by
    rw [evalRealPolynomial_conj, hpα]
  let term : ℂ → ℂ := fun z => ((w z : ℝ) : ℂ) * z * evalRealPolynomial p z ^ 2
  have hsum : ∑ z ∈ F, term z = term α + term ((starRingEnd ℂ) α) := by
    rw [← Finset.sum_erase_add F term hα]
    have hcaErase : (starRingEnd ℂ) α ∈ F.erase α :=
      Finset.mem_erase.mpr ⟨hca_ne, hca⟩
    rw [← Finset.sum_erase_add (F.erase α) term hcaErase]
    have hrest : ∑ z ∈ (F.erase α).erase ((starRingEnd ℂ) α), term z = 0 := by
      apply Finset.sum_eq_zero
      intro z hz
      have hz1 := Finset.mem_erase.mp hz
      have hz2 := Finset.mem_erase.mp hz1.2
      have hpz : evalRealPolynomial p z = 0 := by
        have hsepz : evalRealPolynomial sep z = 0 := by
          dsimp [sep]
          exact evalRealOrbitSeparator_eq_zero hz2.2 hz2.1 hz1.1
        simp only [p, evalRealPolynomial_mul, hsepz, zero_mul]
      simp [term, hpz]
    rw [hrest]
    ring
  have hnonneg := hpos p
  change 0 ≤ (∑ z ∈ F, term z).re at hnonneg
  rw [hsum, add_re] at hnonneg
  simp only [term, hpα, hpca] at hnonneg
  have hfirst : (((w α : ℝ) : ℂ) * α * c ^ 2).re = w α * (α * c ^ 2).re := by
    exact real_weight_phase_re (w α) α c
  have hsecond :
      (((w ((starRingEnd ℂ) α) : ℝ) : ℂ) * (starRingEnd ℂ) α *
          ((starRingEnd ℂ) c) ^ 2).re =
        w ((starRingEnd ℂ) α) * (α * c ^ 2).re :=
    real_weight_conj_phase_re (w ((starRingEnd ℂ) α)) α c
  rw [hfirst, hsecond] at hnonneg
  have hwα := hw α hα
  have hwca := hw ((starRingEnd ℂ) α) hca
  nlinarith

end

end RHTower
