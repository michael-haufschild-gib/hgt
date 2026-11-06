import GaloisForLFunctions.ThetaCuspSections.ExplicitCurrentCore
import GaloisForLFunctions.ThetaCuspSections.QuarticLegendreKernel

/-!
# The tenth theta section

**Theorem** (`thetaCuspCenterMixedSignedHankel_ten_posDef`). For `0 < a ≤ ½` the signed section of
rank ten is positive definite.

The section is the moment form `∫ p(b)² current(a, b) db`, `deg p ≤ 9`. The current is even, so
`p = r(b²) + b r'(b²)` splits into two quartics in `t = b²`. RH through height `67` makes the current
nonnegative on `|b| ≤ 66`.

* On `[1, 5]` the current is at least `6·10⁻⁴ a`, so the form is at least `6·10⁻⁵ a E`, with
  `E = ∫₁²⁵ (r² + r'²)`.
* Past `66` the Legendre kernel bounds `p²` by `(87/12⁹) b¹⁸ E`, and the explicit tail of the current
  costs less than `10⁻⁵ a E` in total.

The aperture cancels, and `E > 0` unless `p = 0`.
-/

open Complex MeasureTheory Set Filter Topology Matrix

noncomputable section

namespace GaloisForLFunctions.ThetaCuspSections.ExplicitCollar

open _root_.RHTower CriticalCollar QuantitativeCollar LogarithmicCollar
open GaloisForLFunctions.VerifiedHeightRungs GaloisForLFunctions.VerifiedHeightRungs.HadamardBudget

/-! ## The parity of the current -/

theorem current_neg (a b : ℝ) : current a (-b) = current a b := by
  have hF : (fun a' : ℝ => Complex.normSq (XiC (((-b : ℝ) : ℂ) - (a' : ℂ) * I))) =
      fun a' : ℝ => Complex.normSq (XiC ((b : ℂ) - (a' : ℂ) * I)) := by
    funext a'
    have e : ((-b : ℝ) : ℂ) - (a' : ℂ) * I = -((starRingEnd ℂ) ((b : ℂ) - (a' : ℂ) * I)) := by
      simp only [map_sub, map_mul, Complex.conj_ofReal, Complex.conj_I]
      push_cast
      ring
    rw [e, XiC_even, XiC_conj, Complex.normSq_conj]
  have h1 := hasDerivAt_normSq_XiC a (-b)
  rw [hF] at h1
  exact h1.unique (hasDerivAt_normSq_XiC a b)

/-! ## The form -/

/-- The polynomial of a coefficient vector. -/
def poly10 (w : ℕ → ℝ) (b : ℝ) : ℝ := ∑ i ∈ Finset.range 10, w i * b ^ i

/-- The even quartic of a coefficient vector. -/
def evenQuartic (w : ℕ → ℝ) : ℝ → ℝ := quartic (w 0) (w 2) (w 4) (w 6) (w 8)

/-- The odd quartic of a coefficient vector. -/
def oddQuartic (w : ℕ → ℝ) : ℝ → ℝ := quartic (w 1) (w 3) (w 5) (w 7) (w 9)

theorem poly10_eq (w : ℕ → ℝ) (b : ℝ) :
    poly10 w b = evenQuartic w (b ^ 2) + b * oddQuartic w (b ^ 2) := by
  unfold poly10 evenQuartic oddQuartic quartic
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  ring

/-- The parity-reduced density. -/
def formW (w : ℕ → ℝ) (b : ℝ) : ℝ :=
  evenQuartic w (b ^ 2) ^ 2 + b ^ 2 * oddQuartic w (b ^ 2) ^ 2

theorem formW_nonneg (w : ℕ → ℝ) (b : ℝ) : 0 ≤ formW w b := by
  unfold formW
  positivity

theorem continuous_formW (w : ℕ → ℝ) : Continuous (formW w) := by
  unfold formW evenQuartic oddQuartic
  have h1 := continuous_quartic (w 0) (w 2) (w 4) (w 6) (w 8)
  have h2 := continuous_quartic (w 1) (w 3) (w 5) (w 7) (w 9)
  fun_prop

theorem poly10_sq_add (w : ℕ → ℝ) (b : ℝ) :
    poly10 w b ^ 2 + poly10 w (-b) ^ 2 = 2 * formW w b := by
  rw [poly10_eq, poly10_eq, neg_sq]
  unfold formW
  ring

private theorem integrable_poly10_sq_mul {a : ℝ} (ha : |a| < 1) (w : ℕ → ℝ) :
    Integrable fun b : ℝ => poly10 w b ^ 2 * current a b := by
  have e : ∀ b : ℝ, poly10 w b ^ 2 * current a b = ∑ i ∈ Finset.range 10, ∑ j ∈ Finset.range 10,
      w i * w j * (b ^ (i + j) * current a b) := by
    intro b
    unfold poly10
    rw [sq, Finset.sum_mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [pow_add]
    ring
  simp_rw [e]
  exact integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
    (raw_integrable a ha (i + j)).const_mul _

/-- The form on a polynomial. -/
theorem integral_poly10_sq_mul {a : ℝ} (ha : |a| < 1) (w : ℕ → ℝ) :
    ∫ b : ℝ, poly10 w b ^ 2 * current a b =
      ∑ i ∈ Finset.range 10, ∑ j ∈ Finset.range 10, w i * w j * rawMoment a (i + j) := by
  have e : ∀ b : ℝ, poly10 w b ^ 2 * current a b = ∑ i ∈ Finset.range 10, ∑ j ∈ Finset.range 10,
      w i * w j * (b ^ (i + j) * current a b) := by
    intro b
    unfold poly10
    rw [sq, Finset.sum_mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [pow_add]
    ring
  simp_rw [e]
  rw [integral_finset_sum _ fun i _ => integrable_finsetSum _ fun j _ =>
    (raw_integrable a ha (i + j)).const_mul _]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finset_sum _ fun j _ => (raw_integrable a ha (i + j)).const_mul _]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_const_mul]
  rfl

/-- The current is even, so the form depends only on the two quartics. -/
theorem integral_poly10_sq_eq {a : ℝ} (ha : |a| < 1) (w : ℕ → ℝ) :
    Integrable (fun b : ℝ => formW w b * current a b) ∧
      ∫ b : ℝ, poly10 w b ^ 2 * current a b = ∫ b : ℝ, formW w b * current a b := by
  have h1 := integrable_poly10_sq_mul ha w
  have h2 : Integrable fun b : ℝ => poly10 w (-b) ^ 2 * current a b := by
    refine h1.comp_neg.congr (ae_of_all _ fun b => ?_)
    simp only [current_neg]
  have hrefl : ∫ b : ℝ, poly10 w (-b) ^ 2 * current a b = ∫ b : ℝ, poly10 w b ^ 2 * current a b := by
    rw [← integral_neg_eq_self (fun b : ℝ => poly10 w b ^ 2 * current a b) volume]
    refine integral_congr_ae (ae_of_all _ fun b => ?_)
    simp only [current_neg]
  have e : ∀ b : ℝ, formW w b * current a b =
      1 / 2 * (poly10 w b ^ 2 * current a b + poly10 w (-b) ^ 2 * current a b) := by
    intro b
    have := poly10_sq_add w b
    have h : formW w b = 1 / 2 * (poly10 w b ^ 2 + poly10 w (-b) ^ 2) := by linarith only [this]
    rw [h]
    ring
  constructor
  · simp_rw [e]
    exact (h1.add h2).const_mul _
  · simp_rw [e]
    rw [integral_const_mul, integral_add h1 h2, hrefl]
    ring

/-! ## The energy -/

/-- The energy of the two quartics on `[1, 25]`. -/
def formE (w : ℕ → ℝ) : ℝ :=
  (∫ t in (1 : ℝ)..25, evenQuartic w t ^ 2) + ∫ t in (1 : ℝ)..25, oddQuartic w t ^ 2

private theorem interval_sq_nonneg (f : ℝ → ℝ) : 0 ≤ ∫ t in (1 : ℝ)..25, f t ^ 2 :=
  intervalIntegral.integral_nonneg (by norm_num) fun _ _ => sq_nonneg _

theorem formE_nonneg (w : ℕ → ℝ) : 0 ≤ formE w :=
  add_nonneg (interval_sq_nonneg _) (interval_sq_nonneg _)

theorem formE_pos {w : ℕ → ℝ} (hw : ∃ i, i < 10 ∧ w i ≠ 0) : 0 < formE w := by
  refine lt_of_le_of_ne (formE_nonneg w) fun h0 => ?_
  have h1 := interval_sq_nonneg (evenQuartic w)
  have h2 := interval_sq_nonneg (oddQuartic w)
  have hE : (∫ t in (1 : ℝ)..25, evenQuartic w t ^ 2) = 0 := by
    unfold formE at h0
    linarith only [h0, h1, h2]
  have hO : (∫ t in (1 : ℝ)..25, oddQuartic w t ^ 2) = 0 := by
    unfold formE at h0
    linarith only [h0, h1, h2]
  obtain ⟨e0, e2, e4, e6, e8⟩ := quartic_coeffs_zero hE
  obtain ⟨e1, e3, e5, e7, e9⟩ := quartic_coeffs_zero hO
  obtain ⟨i, hi, hne⟩ := hw
  interval_cases i <;> contradiction

/-- A change of variables: `∫₁⁵ g(b²) db ≥ (1/10) ∫₁²⁵ g` for `g ≥ 0`. -/
theorem integral_sq_comp_ge {g : ℝ → ℝ} (hg : Continuous g) (h0 : ∀ t, 0 ≤ g t) :
    1 / 10 * ∫ t in (1 : ℝ)..25, g t ≤ ∫ b in (1 : ℝ)..5, g (b ^ 2) := by
  have hcov := intervalIntegral.integral_comp_mul_deriv (a := 1) (b := 5)
    (f := fun b : ℝ => b ^ 2) (f' := fun b : ℝ => 2 * b) (g := g)
    (fun b _ => by simpa using hasDerivAt_pow 2 b) (by fun_prop) hg
  norm_num at hcov
  rw [← hcov]
  have hint1 : IntervalIntegrable (fun b : ℝ => g (b ^ 2) * (2 * b)) volume 1 5 :=
    (by fun_prop : Continuous fun b : ℝ => g (b ^ 2) * (2 * b)).intervalIntegrable _ _
  have hint2 : IntervalIntegrable (fun b : ℝ => g (b ^ 2)) volume 1 5 :=
    (by fun_prop : Continuous fun b : ℝ => g (b ^ 2)).intervalIntegrable _ _
  have hmono : ∫ b in (1 : ℝ)..5, g (b ^ 2) * (2 * b) ≤ ∫ b in (1 : ℝ)..5, 10 * g (b ^ 2) := by
    refine intervalIntegral.integral_mono_on (by norm_num) hint1 (hint2.const_mul _) fun b hb => ?_
    have := h0 (b ^ 2)
    nlinarith only [this, hb.2]
  rw [intervalIntegral.integral_const_mul] at hmono
  linarith only [hmono]

/-- The form on the window `[1, 5]`. -/
theorem formE_le_integral_formW (w : ℕ → ℝ) :
    1 / 10 * formE w ≤ ∫ b in (1 : ℝ)..5, formW w b := by
  have hc1 : Continuous fun t : ℝ => evenQuartic w t ^ 2 :=
    (continuous_quartic _ _ _ _ _).pow 2
  have hc2 : Continuous fun t : ℝ => oddQuartic w t ^ 2 :=
    (continuous_quartic _ _ _ _ _).pow 2
  have h1 := integral_sq_comp_ge hc1 fun _ => sq_nonneg _
  have h2 := integral_sq_comp_ge hc2 fun _ => sq_nonneg _
  have hcomp1 : Continuous fun b : ℝ => evenQuartic w (b ^ 2) ^ 2 := by
    have := continuous_quartic (w 0) (w 2) (w 4) (w 6) (w 8)
    unfold evenQuartic
    fun_prop
  have hcomp2 : Continuous fun b : ℝ => oddQuartic w (b ^ 2) ^ 2 := by
    have := continuous_quartic (w 1) (w 3) (w 5) (w 7) (w 9)
    unfold oddQuartic
    fun_prop
  have hmono : ∫ b in (1 : ℝ)..5, (evenQuartic w (b ^ 2) ^ 2 + oddQuartic w (b ^ 2) ^ 2) ≤
      ∫ b in (1 : ℝ)..5, formW w b := by
    refine intervalIntegral.integral_mono_on (by norm_num)
      ((hcomp1.add hcomp2).intervalIntegrable _ _)
      ((continuous_formW w).intervalIntegrable _ _) fun b hb => ?_
    unfold formW
    have h3 : 1 ≤ b ^ 2 := by nlinarith only [hb.1]
    nlinarith only [mul_le_mul_of_nonneg_right h3 (sq_nonneg (oddQuartic w (b ^ 2)))]
  rw [intervalIntegral.integral_add (hcomp1.intervalIntegrable _ _)
    (hcomp2.intervalIntegrable _ _)] at hmono
  unfold formE
  linarith only [h1, h2, hmono]

/-! ## The tail -/

/-- `x¹⁸ e^{−(7/5)x} ≤ 66¹⁸ e^{−26.4} e^{−x}` past `66`. -/
theorem pow_mul_exp_tail {x : ℝ} (hx : 66 ≤ x) :
    x ^ 18 * Real.exp (-(7 / 5 * x)) ≤ 66 ^ 18 * Real.exp (-(132 / 5)) * Real.exp (-x) := by
  obtain ⟨y, hy⟩ : ∃ y, y = x / 66 := ⟨_, rfl⟩
  have hy1 : 1 ≤ y := by rw [hy]; linarith only [hx]
  have h1 : y ≤ Real.exp (y - 1) := by
    have := Real.add_one_le_exp (y - 1)
    linarith only [this]
  have h2 : y ^ 18 ≤ Real.exp (2 / 5 * x - 132 / 5) := by
    have h3 := pow_le_pow_left₀ (by linarith only [hy1]) h1 18
    rw [← Real.exp_nat_mul] at h3
    refine h3.trans (Real.exp_le_exp.mpr ?_)
    rw [hy]
    push_cast
    linarith only [hx]
  have hxy : x = 66 * y := by rw [hy]; ring
  have e : Real.exp (2 / 5 * x - 132 / 5) * Real.exp (-(7 / 5 * x)) =
      Real.exp (-(132 / 5)) * Real.exp (-x) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have h4 := mul_le_mul_of_nonneg_right h2 (Real.exp_pos (-(7 / 5 * x))).le
  rw [e] at h4
  calc x ^ 18 * Real.exp (-(7 / 5 * x)) = 66 ^ 18 * (y ^ 18 * Real.exp (-(7 / 5 * x))) := by
        rw [hxy]
        ring_nf
    _ ≤ 66 ^ 18 * (Real.exp (-(132 / 5)) * Real.exp (-x)) :=
        mul_le_mul_of_nonneg_left h4 (by positivity)
    _ = _ := by ring

/-- The parity-reduced density past `66`. -/
theorem formW_le {w : ℕ → ℝ} {b : ℝ} (hb : 66 < |b|) :
    formW w b ≤ 87 / 12 ^ 9 * |b| ^ 18 * formE w := by
  obtain ⟨t, ht⟩ : ∃ t, t = b ^ 2 := ⟨_, rfl⟩
  have ht66 : 4356 < t := by
    rw [ht, ← sq_abs]
    nlinarith only [hb]
  have hs : 361 ≤ (t - 13) / 12 := by linarith only [ht66]
  have hsle : (t - 13) / 12 ≤ t / 12 := by linarith only [ht66]
  have hJ : legendreJ ((t - 13) / 12) ≤ 87 * (t / 12) ^ 8 :=
    (legendreJ_le hs).trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by linarith only [hs]) hsle 8) (by norm_num))
  have hbound (c0 c1 c2 c3 c4 : ℝ) : quartic c0 c1 c2 c3 c4 t ^ 2 ≤
      87 / 12 ^ 9 * t ^ 8 * ∫ u in (1 : ℝ)..25, quartic c0 c1 c2 c3 c4 u ^ 2 := by
    have h := sq_quartic_le_integral c0 c1 c2 c3 c4 t
    refine h.trans (mul_le_mul_of_nonneg_right ?_ (interval_sq_nonneg _))
    have e : 87 / 12 ^ 9 * t ^ 8 = 1 / 12 * (87 * (t / 12) ^ 8) := by
      field_simp
    rw [e]
    exact mul_le_mul_of_nonneg_left hJ (by norm_num)
  have h1 := hbound (w 0) (w 2) (w 4) (w 6) (w 8)
  have h2 := hbound (w 1) (w 3) (w 5) (w 7) (w 9)
  have hb18 : |b| ^ 18 = t * t ^ 8 := by
    rw [ht, show (18 : ℕ) = 2 * 9 by norm_num, pow_mul, sq_abs]
    ring
  unfold formW
  rw [← ht, hb18]
  unfold formE evenQuartic oddQuartic
  obtain ⟨E1, hE1⟩ : ∃ E1, E1 = ∫ u in (1 : ℝ)..25, quartic (w 0) (w 2) (w 4) (w 6) (w 8) u ^ 2 :=
    ⟨_, rfl⟩
  obtain ⟨E2, hE2⟩ : ∃ E2, E2 = ∫ u in (1 : ℝ)..25, quartic (w 1) (w 3) (w 5) (w 7) (w 9) u ^ 2 :=
    ⟨_, rfl⟩
  rw [← hE1] at h1
  rw [← hE2] at h2
  rw [← hE1, ← hE2]
  obtain ⟨R1, hR1⟩ : ∃ R1, R1 = quartic (w 0) (w 2) (w 4) (w 6) (w 8) t ^ 2 := ⟨_, rfl⟩
  obtain ⟨R2, hR2⟩ : ∃ R2, R2 = quartic (w 1) (w 3) (w 5) (w 7) (w 9) t ^ 2 := ⟨_, rfl⟩
  rw [← hR1] at h1 ⊢
  rw [← hR2] at h2 ⊢
  have hR10 : 0 ≤ R1 := by rw [hR1]; positivity
  have hP : 0 ≤ 87 / 12 ^ 9 * t ^ 8 := by positivity
  have ht1 : (1 : ℝ) ≤ t := by linarith only [ht66]
  have h3 : R1 ≤ t * R1 := by nlinarith only [hR10, ht1]
  have h4 : t * R1 ≤ t * (87 / 12 ^ 9 * t ^ 8 * E1) := mul_le_mul_of_nonneg_left h1 (by linarith only [ht1])
  have h5 : t * R2 ≤ t * (87 / 12 ^ 9 * t ^ 8 * E2) := mul_le_mul_of_nonneg_left h2 (by linarith only [ht1])
  calc R1 + t * R2 ≤ t * (87 / 12 ^ 9 * t ^ 8 * E1) + t * (87 / 12 ^ 9 * t ^ 8 * E2) := by
        linarith only [h3, h4, h5]
    _ = _ := by ring

/-- The exterior of a symmetric window. -/
def tailExp (b : ℝ) : ℝ := if 66 < |b| then Real.exp (-|b|) else 0

theorem tailExp_nonneg (b : ℝ) : 0 ≤ tailExp b := by
  unfold tailExp
  split_ifs
  · exact (Real.exp_pos _).le
  · exact le_rfl

theorem integrable_tailExp : Integrable tailExp := by
  have hm : Measurable tailExp := by
    unfold tailExp
    refine Measurable.ite ?_ (by fun_prop) measurable_const
    exact measurableSet_lt measurable_const (by fun_prop)
  have hmaj : Integrable fun b : ℝ => Real.exp (-(1 * |b|)) :=
    integrable_exp_neg_mul_abs' (by norm_num)
  refine hmaj.mono' hm.aestronglyMeasurable (ae_of_all _ fun b => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (tailExp_nonneg b), one_mul]
  unfold tailExp
  split_ifs
  · exact le_rfl
  · exact (Real.exp_pos _).le

theorem integral_tailExp : ∫ b, tailExp b = 2 * Real.exp (-66) := by
  have h := integral_comp_abs (f := fun u : ℝ => if 66 < u then Real.exp (-u) else 0)
  have e : (∫ u in Ioi (0 : ℝ), (if 66 < u then Real.exp (-u) else 0)) =
      ∫ u in Ioi (66 : ℝ), Real.exp (-1 * u) := by
    rw [← integral_indicator measurableSet_Ioi, ← integral_indicator measurableSet_Ioi]
    refine integral_congr_ae (ae_of_all _ fun u => ?_)
    by_cases hu : 66 < u
    · have h0 : (0 : ℝ) < u := by linarith only [hu]
      simp [indicator, hu, h0]
    · simp [indicator, hu]
  unfold tailExp
  rw [h, e, integral_exp_mul_Ioi (by norm_num) 66]
  norm_num

/-- The numerical value of the tail. -/
private theorem tail_numeric :
    (66 : ℝ) ^ 18 * Real.exp (-(132 / 5)) * Real.exp (-66) ≤ 4.5e-8 := by
  have h : Real.exp (-(132 / 5)) * Real.exp (-66) = Real.exp (-92) * Real.exp (-(2 / 5)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    norm_num
  rw [mul_assoc, h]
  have he : Real.exp (-92) = (Real.exp 1 ^ 92)⁻¹ := by
    rw [← Real.exp_nat_mul, ← Real.exp_neg]
    norm_num
  have h92 : Real.exp (-92) ≤ ((2.7182818283 : ℝ) ^ 92)⁻¹ := by
    rw [he]
    exact inv_anti₀ (by norm_num) (pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_d9.le 92)
  have h25 : Real.exp (-(2 / 5)) ≤ 5 / 7 := by
    have h1 := Real.add_one_le_exp (2 / 5 : ℝ)
    rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
    norm_num at h1 ⊢
    linarith only [h1]
  calc (66 : ℝ) ^ 18 * (Real.exp (-92) * Real.exp (-(2 / 5)))
      ≤ 66 ^ 18 * (((2.7182818283 : ℝ) ^ 92)⁻¹ * (5 / 7)) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul h92 h25 (Real.exp_pos _).le (by positivity))
          (by positivity)
    _ ≤ _ := by norm_num

/-! ## The section -/

/-- **The form is positive.** -/
theorem form_pos {a : ℝ} (ha0 : 0 < a) (ha : a ≤ 1 / 2) {w : ℕ → ℝ} (hw : ∃ i, i < 10 ∧ w i ≠ 0) :
    0 < ∫ b : ℝ, poly10 w b ^ 2 * current a b := by
  have habs : |a| ≤ 1 / 2 := by rw [abs_of_pos ha0]; exact ha
  have ha1 : |a| < 1 := habs.trans_lt (by norm_num)
  obtain ⟨hWint, hWeq⟩ := integral_poly10_sq_eq ha1 w
  rw [hWeq]
  obtain ⟨E, hE⟩ : ∃ E, E = formE w := ⟨_, rfl⟩
  have hEpos : 0 < E := by rw [hE]; exact formE_pos hw
  -- The tail constant.
  obtain ⟨Z, hZ⟩ : ∃ Z, Z = 6050000000 * a * (87 / 12 ^ 9 * E) *
      ((66 : ℝ) ^ 18 * Real.exp (-(132 / 5))) := ⟨_, rfl⟩
  have hZ0 : 0 ≤ Z := by rw [hZ]; positivity
  -- The minorant.
  let Lo : ℝ → ℝ := fun b => 0.0006 * a * Set.indicator (Icc (1 : ℝ) 5) (formW w) b - Z * tailExp b
  have hind : Integrable (Set.indicator (Icc (1 : ℝ) 5) (formW w)) :=
    ((continuous_formW w).integrableOn_Icc).integrable_indicator measurableSet_Icc
  have hLo : Integrable Lo := (hind.const_mul _).sub (integrable_tailExp.const_mul _)
  have hpoint : ∀ b, Lo b ≤ formW w b * current a b := by
    intro b
    have hW := formW_nonneg w b
    have hT := tailExp_nonneg b
    by_cases hb1 : b ∈ Icc (1 : ℝ) 5
    · have habs5 : |b| ≤ 5 := by
        rw [abs_of_pos (by linarith only [hb1.1])]
        exact hb1.2
      have hcore := current_ge_of_abs_le ha0 ha habs5
      have hT0 : tailExp b = 0 := by
        unfold tailExp
        rw [if_neg (by linarith only [habs5])]
      simp only [Lo]
      rw [Set.indicator_of_mem hb1, hT0, mul_zero, sub_zero]
      have := mul_le_mul_of_nonneg_left hcore hW
      nlinarith only [this]
    · simp only [Lo]
      rw [Set.indicator_of_notMem hb1, mul_zero, zero_sub]
      by_cases hb66 : |b| ≤ 66
      · have hc := current_nonneg_of_rhVerifiedThrough (T := 66) ha0
          (by
            have := rhVerifiedThrough_sixtySeven
            norm_num
            exact this) hb66
        have hT0 : tailExp b = 0 := by
          unfold tailExp
          rw [if_neg (not_lt.2 hb66)]
        rw [hT0, mul_zero, neg_zero]
        exact mul_nonneg hW hc
      · have hb66' : 66 < |b| := not_le.1 hb66
        have hc := abs_current_le_explicit habs b
        rw [abs_of_pos ha0] at hc
        have hW2 := formW_le (w := w) hb66'
        rw [← hE] at hW2
        have htl := pow_mul_exp_tail hb66'.le
        have hTv : tailExp b = Real.exp (-|b|) := by
          unfold tailExp
          rw [if_pos hb66']
        rw [hTv]
        have hlow : -(formW w b * (6050000000 * a * Real.exp (-(7 / 5 * |b|)))) ≤
            formW w b * current a b := by
          have := (abs_le.mp hc).1
          nlinarith only [mul_le_mul_of_nonneg_left this hW]
        refine le_trans ?_ hlow
        rw [neg_le_neg_iff]
        have hP : 0 ≤ 6050000000 * a * Real.exp (-(7 / 5 * |b|)) := by positivity
        have h1 := mul_le_mul_of_nonneg_right hW2 hP
        refine h1.trans ?_
        have hA : 0 ≤ 6050000000 * a * (87 / 12 ^ 9 * E) := by positivity
        have h2 := mul_le_mul_of_nonneg_left htl hA
        rw [hZ]
        calc 87 / 12 ^ 9 * |b| ^ 18 * E * (6050000000 * a * Real.exp (-(7 / 5 * |b|)))
            = 6050000000 * a * (87 / 12 ^ 9 * E) * (|b| ^ 18 * Real.exp (-(7 / 5 * |b|))) := by ring
          _ ≤ _ := h2
          _ = _ := by ring
  have hint := integral_mono hLo hWint hpoint
  have hval : ∫ b, Lo b = 0.0006 * a * (∫ b in (1 : ℝ)..5, formW w b) - Z * (2 * Real.exp (-66)) := by
    simp only [Lo]
    rw [integral_sub (hind.const_mul _) (integrable_tailExp.const_mul _), integral_const_mul,
      integral_const_mul, integral_tailExp, integral_indicator measurableSet_Icc,
      setIntegral_congr_set Ioc_ae_eq_Icc.symm, ← intervalIntegral.integral_of_le (by norm_num)]
  rw [hval] at hint
  have hcore := formE_le_integral_formW w
  rw [← hE] at hcore
  have hnum := tail_numeric
  have hZle : Z * (2 * Real.exp (-66)) ≤ a * E * 0.00001 := by
    rw [hZ]
    have hA : 0 ≤ a * E := by positivity
    have h1 := mul_le_mul_of_nonneg_left hnum hA
    calc 6050000000 * a * (87 / 12 ^ 9 * E) * ((66 : ℝ) ^ 18 * Real.exp (-(132 / 5))) *
          (2 * Real.exp (-66))
        = (a * E) * (66 ^ 18 * Real.exp (-(132 / 5)) * Real.exp (-66)) *
            (2 * 6050000000 * (87 / 12 ^ 9)) := by ring
      _ ≤ (a * E) * 4.5e-8 * (2 * 6050000000 * (87 / 12 ^ 9)) :=
          mul_le_mul_of_nonneg_right h1 (by norm_num)
      _ ≤ _ := by
          have : (4.5e-8 : ℝ) * (2 * 6050000000 * (87 / 12 ^ 9)) ≤ 0.00001 := by norm_num
          nlinarith only [mul_le_mul_of_nonneg_left this hA]
  have h6 : 0.0006 * a * (1 / 10 * E) ≤ 0.0006 * a * (∫ b in (1 : ℝ)..5, formW w b) :=
    mul_le_mul_of_nonneg_left hcore (by positivity)
  have hfinal : 0 < a * E := by positivity
  norm_num at h6 hZle hint hfinal ⊢
  nlinarith only [h6, hZle, hint, hfinal]

/-- **The tenth section.** For `0 < a ≤ ½` the signed section of rank ten is positive definite. -/
theorem thetaCuspCenterMixedSignedHankel_ten_posDef {a : ℝ} (ha0 : 0 < a) (ha : a ≤ 1 / 2) :
    (thetaCuspCenterMixedSignedHankel a 10).PosDef := by
  have habs : |a| < 1 := by
    rw [abs_of_pos ha0]
    linarith only [ha]
  apply signed_posDef_of_raw habs 10
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  refine ⟨raw_hermitian a 10, fun v hv => ?_⟩
  rw [star_trivial]
  obtain ⟨w, hw⟩ : ∃ w : ℕ → ℝ, w = fun i => if h : i < 10 then v ⟨i, h⟩ else 0 := ⟨_, rfl⟩
  have hwv : ∀ i : Fin 10, w i = v i := fun i => by
    rw [hw]
    simp only [i.isLt, dif_pos]
  have hne : ∃ i, i < 10 ∧ w i ≠ 0 := by
    by_contra hall
    push Not at hall
    apply hv
    funext i
    rw [← hwv i]
    exact hall i i.isLt
  have hpos := form_pos ha0 ha hne
  rw [integral_poly10_sq_mul habs] at hpos
  have heq : v ⬝ᵥ rawHankel a 10 *ᵥ v =
      ∑ i ∈ Finset.range 10, ∑ j ∈ Finset.range 10, w i * w j * rawMoment a (i + j) := by
    simp only [dotProduct, mulVec, rawHankel, Finset.mul_sum]
    rw [← Fin.sum_univ_eq_sum_range (fun i => ∑ j ∈ Finset.range 10, w i * w j * rawMoment a (i + j))]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Fin.sum_univ_eq_sum_range (fun j => w i * w j * rawMoment a (i + j))]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hwv i, hwv j]
    ring
  rwa [heq]

end GaloisForLFunctions.ThetaCuspSections.ExplicitCollar
