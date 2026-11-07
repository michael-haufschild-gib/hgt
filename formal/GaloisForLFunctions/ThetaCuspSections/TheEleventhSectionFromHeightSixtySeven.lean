import GaloisForLFunctions.ThetaCuspSections.TheTenthSectionFromHeightSixtySeven
import GaloisForLFunctions.ThetaCuspSections.QuinticLegendreKernel
import GaloisForLFunctions.ThetaCuspSections.TheSharpCurrentTail

/-!
# The eleventh theta section

**Theorem** (`thetaCuspCenterMixedSignedHankel_eleven_posDef`). For `0 < a ≤ ½` the signed section
of rank eleven is positive definite.

The form is `∫ p(b)² current(a, b) db`, `deg p ≤ 10`. Parity splits `p = r(b²) + b r'(b²)` into a
quintic `r` and a quartic `r'` in `t = b²`. RH through height `67` makes the current nonnegative on
`|b| ≤ 66`.

* On `[1, 5]` the current is at least `6·10⁻⁴ a`, so the form is at least `6·10⁻⁵ a E`,
  `E = ∫₁²⁵ (r² + r'²)`.
* Past `66` the quintic Legendre kernel bounds the parity-reduced density by `(342/12¹¹) b²⁰ E`, and
  the sharp tail `|current| ≤ 3.6·10⁷ a e^{−(7/5)|b|}` costs less than `10⁻⁵ a E`.
-/

open Complex MeasureTheory Set Filter Topology Matrix

noncomputable section

namespace GaloisForLFunctions.ThetaCuspSections.ExplicitCollar

open _root_.RHTower CriticalCollar QuantitativeCollar LogarithmicCollar
open GaloisForLFunctions.VerifiedHeightRungs GaloisForLFunctions.VerifiedHeightRungs.HadamardBudget

/-! ## The form -/

/-- The polynomial of degree ten of a coefficient vector. -/
def poly11 (w : ℕ → ℝ) (b : ℝ) : ℝ := ∑ i ∈ Finset.range 11, w i * b ^ i

/-- The even quintic of a coefficient vector. -/
def evenQuintic (w : ℕ → ℝ) : ℝ → ℝ := quintic (w 0) (w 2) (w 4) (w 6) (w 8) (w 10)

theorem poly11_eq (w : ℕ → ℝ) (b : ℝ) :
    poly11 w b = evenQuintic w (b ^ 2) + b * oddQuartic w (b ^ 2) := by
  unfold poly11 evenQuintic oddQuartic quintic quartic
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  ring

/-- The parity-reduced density of rank eleven. -/
def formW11 (w : ℕ → ℝ) (b : ℝ) : ℝ :=
  evenQuintic w (b ^ 2) ^ 2 + b ^ 2 * oddQuartic w (b ^ 2) ^ 2

theorem formW11_nonneg (w : ℕ → ℝ) (b : ℝ) : 0 ≤ formW11 w b := by
  unfold formW11
  positivity

theorem continuous_formW11 (w : ℕ → ℝ) : Continuous (formW11 w) := by
  unfold formW11 evenQuintic oddQuartic
  have h1 := continuous_quintic (w 0) (w 2) (w 4) (w 6) (w 8) (w 10)
  have h2 := continuous_quartic (w 1) (w 3) (w 5) (w 7) (w 9)
  fun_prop

theorem poly11_sq_add (w : ℕ → ℝ) (b : ℝ) :
    poly11 w b ^ 2 + poly11 w (-b) ^ 2 = 2 * formW11 w b := by
  rw [poly11_eq, poly11_eq, neg_sq]
  unfold formW11
  ring

private theorem poly11_sq_mul_eq (w : ℕ → ℝ) (a b : ℝ) :
    poly11 w b ^ 2 * current a b = ∑ i ∈ Finset.range 11, ∑ j ∈ Finset.range 11,
      w i * w j * (b ^ (i + j) * current a b) := by
  unfold poly11
  rw [sq, Finset.sum_mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [pow_add]
  ring

private theorem integrable_poly11_sq_mul {a : ℝ} (ha : |a| < 1) (w : ℕ → ℝ) :
    Integrable fun b : ℝ => poly11 w b ^ 2 * current a b := by
  simp_rw [poly11_sq_mul_eq w a]
  exact integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
    (raw_integrable a ha (i + j)).const_mul _

/-- The form on a polynomial. -/
theorem integral_poly11_sq_mul {a : ℝ} (ha : |a| < 1) (w : ℕ → ℝ) :
    ∫ b : ℝ, poly11 w b ^ 2 * current a b =
      ∑ i ∈ Finset.range 11, ∑ j ∈ Finset.range 11, w i * w j * rawMoment a (i + j) := by
  simp_rw [poly11_sq_mul_eq w a]
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
    (raw_integrable a ha (i + j)).const_mul _]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ fun j _ => (raw_integrable a ha (i + j)).const_mul _]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_const_mul]
  rfl

/-- The current is even, so the form depends only on the quintic and the quartic. -/
theorem integral_poly11_sq_eq {a : ℝ} (ha : |a| < 1) (w : ℕ → ℝ) :
    Integrable (fun b : ℝ => formW11 w b * current a b) ∧
      ∫ b : ℝ, poly11 w b ^ 2 * current a b = ∫ b : ℝ, formW11 w b * current a b := by
  have h1 := integrable_poly11_sq_mul ha w
  have h2 : Integrable fun b : ℝ => poly11 w (-b) ^ 2 * current a b := by
    refine h1.comp_neg.congr (ae_of_all _ fun b => ?_)
    simp only [current_neg]
  have hrefl : ∫ b : ℝ, poly11 w (-b) ^ 2 * current a b =
      ∫ b : ℝ, poly11 w b ^ 2 * current a b := by
    rw [← integral_neg_eq_self (fun b : ℝ => poly11 w b ^ 2 * current a b) volume]
    refine integral_congr_ae (ae_of_all _ fun b => ?_)
    simp only [current_neg]
  have e : ∀ b : ℝ, formW11 w b * current a b =
      1 / 2 * (poly11 w b ^ 2 * current a b + poly11 w (-b) ^ 2 * current a b) := by
    intro b
    have := poly11_sq_add w b
    have h : formW11 w b = 1 / 2 * (poly11 w b ^ 2 + poly11 w (-b) ^ 2) := by
      linarith only [this]
    rw [h]
    ring
  constructor
  · simp_rw [e]
    exact (h1.add h2).const_mul _
  · simp_rw [e]
    rw [integral_const_mul, integral_add h1 h2, hrefl]
    ring

/-! ## The energy -/

/-- The energy of the quintic and the quartic on `[1, 25]`. -/
def formE11 (w : ℕ → ℝ) : ℝ :=
  (∫ t in (1 : ℝ)..25, evenQuintic w t ^ 2) + ∫ t in (1 : ℝ)..25, oddQuartic w t ^ 2

private theorem interval_sq_nonneg' (f : ℝ → ℝ) : 0 ≤ ∫ t in (1 : ℝ)..25, f t ^ 2 :=
  intervalIntegral.integral_nonneg (by norm_num) fun _ _ => sq_nonneg _

theorem formE11_pos {w : ℕ → ℝ} (hw : ∃ i, i < 11 ∧ w i ≠ 0) : 0 < formE11 w := by
  have h1 := interval_sq_nonneg' (evenQuintic w)
  have h2 := interval_sq_nonneg' (oddQuartic w)
  refine lt_of_le_of_ne (add_nonneg h1 h2) fun h0 => ?_
  have hE : (∫ t in (1 : ℝ)..25, evenQuintic w t ^ 2) = 0 := by
    unfold formE11 at h0
    linarith only [h0, h1, h2]
  have hO : (∫ t in (1 : ℝ)..25, oddQuartic w t ^ 2) = 0 := by
    unfold formE11 at h0
    linarith only [h0, h1, h2]
  obtain ⟨e0, e2, e4, e6, e8, e10⟩ := quintic_coeffs_zero hE
  obtain ⟨e1, e3, e5, e7, e9⟩ := quartic_coeffs_zero hO
  obtain ⟨i, hi, hne⟩ := hw
  interval_cases i <;> contradiction

/-- The form on the window `[1, 5]`. -/
theorem formE11_le_integral_formW11 (w : ℕ → ℝ) :
    1 / 10 * formE11 w ≤ ∫ b in (1 : ℝ)..5, formW11 w b := by
  have hc1 : Continuous fun t : ℝ => evenQuintic w t ^ 2 :=
    (continuous_quintic _ _ _ _ _ _).pow 2
  have hc2 : Continuous fun t : ℝ => oddQuartic w t ^ 2 :=
    (continuous_quartic _ _ _ _ _).pow 2
  have h1 := integral_sq_comp_ge hc1 fun _ => sq_nonneg _
  have h2 := integral_sq_comp_ge hc2 fun _ => sq_nonneg _
  have hcomp1 : Continuous fun b : ℝ => evenQuintic w (b ^ 2) ^ 2 := by
    have := continuous_quintic (w 0) (w 2) (w 4) (w 6) (w 8) (w 10)
    unfold evenQuintic
    fun_prop
  have hcomp2 : Continuous fun b : ℝ => oddQuartic w (b ^ 2) ^ 2 := by
    have := continuous_quartic (w 1) (w 3) (w 5) (w 7) (w 9)
    unfold oddQuartic
    fun_prop
  have hmono : ∫ b in (1 : ℝ)..5, (evenQuintic w (b ^ 2) ^ 2 + oddQuartic w (b ^ 2) ^ 2) ≤
      ∫ b in (1 : ℝ)..5, formW11 w b := by
    refine intervalIntegral.integral_mono_on (by norm_num)
      ((hcomp1.add hcomp2).intervalIntegrable _ _)
      ((continuous_formW11 w).intervalIntegrable _ _) fun b hb => ?_
    unfold formW11
    have h3 : 1 ≤ b ^ 2 := by nlinarith only [hb.1]
    nlinarith only [mul_le_mul_of_nonneg_right h3 (sq_nonneg (oddQuartic w (b ^ 2)))]
  rw [intervalIntegral.integral_add (hcomp1.intervalIntegrable _ _)
    (hcomp2.intervalIntegrable _ _)] at hmono
  unfold formE11
  linarith only [h1, h2, hmono]

/-! ## The tail -/

/-- `x²⁰ e^{−(7/5)x} ≤ 66²⁰ e^{−26.4} e^{−x}` past `66`. -/
theorem pow_twenty_mul_exp_tail {x : ℝ} (hx : 66 ≤ x) :
    x ^ 20 * Real.exp (-(7 / 5 * x)) ≤ 66 ^ 20 * Real.exp (-(132 / 5)) * Real.exp (-x) := by
  obtain ⟨y, hy⟩ : ∃ y, y = x / 66 := ⟨_, rfl⟩
  have hy1 : 1 ≤ y := by rw [hy]; linarith only [hx]
  have h1 : y ≤ Real.exp (y - 1) := by
    have := Real.add_one_le_exp (y - 1)
    linarith only [this]
  have h2 : y ^ 20 ≤ Real.exp (2 / 5 * x - 132 / 5) := by
    have h3 := pow_le_pow_left₀ (by linarith only [hy1]) h1 20
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
  calc x ^ 20 * Real.exp (-(7 / 5 * x)) = 66 ^ 20 * (y ^ 20 * Real.exp (-(7 / 5 * x))) := by
        rw [hxy]
        ring_nf
    _ ≤ 66 ^ 20 * (Real.exp (-(132 / 5)) * Real.exp (-x)) :=
        mul_le_mul_of_nonneg_left h4 (by positivity)
    _ = _ := by ring

/-- The parity-reduced density past `66`. -/
theorem formW11_le {w : ℕ → ℝ} {b : ℝ} (hb : 66 < |b|) :
    formW11 w b ≤ 342 / 12 ^ 11 * |b| ^ 20 * formE11 w := by
  obtain ⟨t, ht⟩ : ∃ t, t = b ^ 2 := ⟨_, rfl⟩
  have ht66 : 4356 < t := by
    rw [ht, ← sq_abs]
    nlinarith only [hb]
  have ht0 : 0 ≤ t := by linarith only [ht66]
  have hs : 361 ≤ (t - 13) / 12 := by linarith only [ht66]
  have hsle : (t - 13) / 12 ≤ t / 12 := by linarith only [ht66]
  -- The quintic.
  have hJ5 : legendreJ5 ((t - 13) / 12) ≤ 342 * (t / 12) ^ 10 :=
    (legendreJ5_le hs).trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by linarith only [hs]) hsle 10) (by norm_num))
  have hq5 (c0 c1 c2 c3 c4 c5 : ℝ) : quintic c0 c1 c2 c3 c4 c5 t ^ 2 ≤
      342 / 12 ^ 11 * t ^ 10 * ∫ u in (1 : ℝ)..25, quintic c0 c1 c2 c3 c4 c5 u ^ 2 := by
    refine (sq_quintic_le_integral c0 c1 c2 c3 c4 c5 t).trans
      (mul_le_mul_of_nonneg_right ?_ (interval_sq_nonneg' _))
    have e : 342 / 12 ^ 11 * t ^ 10 = 1 / 12 * (342 * (t / 12) ^ 10) := by
      field_simp
    rw [e]
    exact mul_le_mul_of_nonneg_left hJ5 (by norm_num)
  -- The quartic.
  have hJ4 : legendreJ ((t - 13) / 12) ≤ 87 * (t / 12) ^ 8 :=
    (legendreJ_le hs).trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by linarith only [hs]) hsle 8) (by norm_num))
  have hq4 (c0 c1 c2 c3 c4 : ℝ) : t * quartic c0 c1 c2 c3 c4 t ^ 2 ≤
      342 / 12 ^ 11 * t ^ 10 * ∫ u in (1 : ℝ)..25, quartic c0 c1 c2 c3 c4 u ^ 2 := by
    have h := sq_quartic_le_integral c0 c1 c2 c3 c4 t
    have hI := interval_sq_nonneg' (quartic c0 c1 c2 c3 c4)
    have hk : 1 / 12 * legendreJ ((t - 13) / 12) * t ≤ 342 / 12 ^ 11 * t ^ 10 := by
      have h1 : 1 / 12 * legendreJ ((t - 13) / 12) * t ≤ 1 / 12 * (87 * (t / 12) ^ 8) * t :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hJ4 (by norm_num)) ht0
      refine h1.trans ?_
      have e : 342 / 12 ^ 11 * t ^ 10 - 1 / 12 * (87 * (t / 12) ^ 8) * t =
          t ^ 9 / 12 ^ 11 * (342 * t - 12528) := by
        field_simp
        ring
      have : 0 ≤ t ^ 9 / 12 ^ 11 * (342 * t - 12528) :=
        mul_nonneg (by positivity) (by linarith only [ht66])
      linarith only [e, this]
    calc t * quartic c0 c1 c2 c3 c4 t ^ 2
        ≤ t * (1 / 12 * legendreJ ((t - 13) / 12) * ∫ u in (1 : ℝ)..25, quartic c0 c1 c2 c3 c4 u ^ 2) :=
          mul_le_mul_of_nonneg_left h ht0
      _ = (1 / 12 * legendreJ ((t - 13) / 12) * t) *
            ∫ u in (1 : ℝ)..25, quartic c0 c1 c2 c3 c4 u ^ 2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hk hI
  have h1 := hq5 (w 0) (w 2) (w 4) (w 6) (w 8) (w 10)
  have h2 := hq4 (w 1) (w 3) (w 5) (w 7) (w 9)
  have hb20 : |b| ^ 20 = t ^ 10 := by
    rw [ht, show (20 : ℕ) = 2 * 10 by norm_num, pow_mul, sq_abs]
  unfold formW11 formE11 evenQuintic oddQuartic
  rw [← ht, hb20]
  linarith only [h1, h2]

/-- The numerical value of the tail. -/
private theorem tail20_numeric :
    (66 : ℝ) ^ 20 * Real.exp (-(132 / 5)) * Real.exp (-66) ≤ 1.85e-4 := by
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
  have h25 : Real.exp (-(2 / 5)) ≤ 0.6757 := by
    have h1 := Real.quadratic_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 2 / 5)
    rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
    norm_num at h1 ⊢
    linarith only [h1]
  calc (66 : ℝ) ^ 20 * (Real.exp (-92) * Real.exp (-(2 / 5)))
      ≤ 66 ^ 20 * (((2.7182818283 : ℝ) ^ 92)⁻¹ * 0.6757) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul h92 h25 (Real.exp_pos _).le (by positivity))
          (by positivity)
    _ ≤ _ := by norm_num

/-! ## The section -/

/-- **The form is positive.** -/
theorem form11_pos {a : ℝ} (ha0 : 0 < a) (ha : a ≤ 1 / 2) {w : ℕ → ℝ}
    (hw : ∃ i, i < 11 ∧ w i ≠ 0) :
    0 < ∫ b : ℝ, poly11 w b ^ 2 * current a b := by
  have habs : |a| ≤ 1 / 2 := by rw [abs_of_pos ha0]; exact ha
  have ha1 : |a| < 1 := habs.trans_lt (by norm_num)
  obtain ⟨hWint, hWeq⟩ := integral_poly11_sq_eq ha1 w
  rw [hWeq]
  obtain ⟨E, hE⟩ : ∃ E, E = formE11 w := ⟨_, rfl⟩
  have hEpos : 0 < E := by rw [hE]; exact formE11_pos hw
  -- The tail constant.
  obtain ⟨Z, hZ⟩ : ∃ Z, Z = 36000000 * a * (342 / 12 ^ 11 * E) *
      ((66 : ℝ) ^ 20 * Real.exp (-(132 / 5))) := ⟨_, rfl⟩
  -- The minorant.
  let Lo : ℝ → ℝ := fun b =>
    0.0006 * a * Set.indicator (Icc (1 : ℝ) 5) (formW11 w) b - Z * tailExp b
  have hind : Integrable (Set.indicator (Icc (1 : ℝ) 5) (formW11 w)) :=
    ((continuous_formW11 w).integrableOn_Icc).integrable_indicator measurableSet_Icc
  have hLo : Integrable Lo := (hind.const_mul _).sub (integrable_tailExp.const_mul _)
  have hpoint : ∀ b, Lo b ≤ formW11 w b * current a b := by
    intro b
    have hW := formW11_nonneg w b
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
        have hc := abs_current_le_sharp habs b
        rw [abs_of_pos ha0] at hc
        have hW2 := formW11_le (w := w) hb66'
        rw [← hE] at hW2
        have htl := pow_twenty_mul_exp_tail hb66'.le
        have hTv : tailExp b = Real.exp (-|b|) := by
          unfold tailExp
          rw [if_pos hb66']
        rw [hTv]
        have hlow : -(formW11 w b * (36000000 * a * Real.exp (-(7 / 5 * |b|)))) ≤
            formW11 w b * current a b := by
          have := (abs_le.mp hc).1
          nlinarith only [mul_le_mul_of_nonneg_left this hW]
        refine le_trans ?_ hlow
        rw [neg_le_neg_iff]
        have hP : 0 ≤ 36000000 * a * Real.exp (-(7 / 5 * |b|)) := by positivity
        have h1 := mul_le_mul_of_nonneg_right hW2 hP
        refine h1.trans ?_
        have hA : 0 ≤ 36000000 * a * (342 / 12 ^ 11 * E) := by positivity
        have h2 := mul_le_mul_of_nonneg_left htl hA
        rw [hZ]
        calc 342 / 12 ^ 11 * |b| ^ 20 * E * (36000000 * a * Real.exp (-(7 / 5 * |b|)))
            = 36000000 * a * (342 / 12 ^ 11 * E) * (|b| ^ 20 * Real.exp (-(7 / 5 * |b|))) := by
              ring
          _ ≤ _ := h2
          _ = _ := by ring
  have hint := integral_mono hLo hWint hpoint
  have hval : ∫ b, Lo b =
      0.0006 * a * (∫ b in (1 : ℝ)..5, formW11 w b) - Z * (2 * Real.exp (-66)) := by
    simp only [Lo]
    rw [integral_sub (hind.const_mul _) (integrable_tailExp.const_mul _), integral_const_mul,
      integral_const_mul, integral_tailExp, integral_indicator measurableSet_Icc,
      setIntegral_congr_set Ioc_ae_eq_Icc.symm, ← intervalIntegral.integral_of_le (by norm_num)]
  rw [hval] at hint
  have hcore := formE11_le_integral_formW11 w
  rw [← hE] at hcore
  have hnum := tail20_numeric
  have hZle : Z * (2 * Real.exp (-66)) ≤ a * E * 0.00001 := by
    rw [hZ]
    have hA : 0 ≤ a * E := by positivity
    have h1 := mul_le_mul_of_nonneg_left hnum hA
    calc 36000000 * a * (342 / 12 ^ 11 * E) * ((66 : ℝ) ^ 20 * Real.exp (-(132 / 5))) *
          (2 * Real.exp (-66))
        = (a * E) * (66 ^ 20 * Real.exp (-(132 / 5)) * Real.exp (-66)) *
            (2 * 36000000 * (342 / 12 ^ 11)) := by ring
      _ ≤ (a * E) * 1.85e-4 * (2 * 36000000 * (342 / 12 ^ 11)) :=
          mul_le_mul_of_nonneg_right h1 (by norm_num)
      _ ≤ _ := by
          have : (1.85e-4 : ℝ) * (2 * 36000000 * (342 / 12 ^ 11)) ≤ 0.00001 := by norm_num
          nlinarith only [mul_le_mul_of_nonneg_left this hA]
  have h6 : 0.0006 * a * (1 / 10 * E) ≤ 0.0006 * a * (∫ b in (1 : ℝ)..5, formW11 w b) :=
    mul_le_mul_of_nonneg_left hcore (by positivity)
  have hfinal : 0 < a * E := by positivity
  norm_num at h6 hZle hint hfinal ⊢
  nlinarith only [h6, hZle, hint, hfinal]

/-- **The eleventh section.** For `0 < a ≤ ½` the signed section of rank eleven is positive
definite. -/
theorem thetaCuspCenterMixedSignedHankel_eleven_posDef {a : ℝ} (ha0 : 0 < a) (ha : a ≤ 1 / 2) :
    (thetaCuspCenterMixedSignedHankel a 11).PosDef := by
  have habs : |a| < 1 := by
    rw [abs_of_pos ha0]
    linarith only [ha]
  apply signed_posDef_of_raw habs 11
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  refine ⟨raw_hermitian a 11, fun v hv => ?_⟩
  rw [star_trivial]
  obtain ⟨w, hw⟩ : ∃ w : ℕ → ℝ, w = fun i => if h : i < 11 then v ⟨i, h⟩ else 0 := ⟨_, rfl⟩
  have hwv : ∀ i : Fin 11, w i = v i := fun i => by
    rw [hw]
    simp only [i.isLt, dif_pos]
  have hne : ∃ i, i < 11 ∧ w i ≠ 0 := by
    by_contra hall
    push Not at hall
    apply hv
    funext i
    rw [← hwv i]
    exact hall i i.isLt
  have hpos := form11_pos ha0 ha hne
  rw [integral_poly11_sq_mul habs] at hpos
  have heq : v ⬝ᵥ rawHankel a 11 *ᵥ v =
      ∑ i ∈ Finset.range 11, ∑ j ∈ Finset.range 11, w i * w j * rawMoment a (i + j) := by
    simp only [dotProduct, mulVec, rawHankel, Finset.mul_sum]
    rw [← Fin.sum_univ_eq_sum_range
      (fun i => ∑ j ∈ Finset.range 11, w i * w j * rawMoment a (i + j))]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Fin.sum_univ_eq_sum_range (fun j => w i * w j * rawMoment a (i + j))]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hwv i, hwv j]
    ring
  rwa [heq]

end GaloisForLFunctions.ThetaCuspSections.ExplicitCollar
