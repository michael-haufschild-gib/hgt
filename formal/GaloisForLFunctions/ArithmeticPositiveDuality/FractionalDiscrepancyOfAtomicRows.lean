import Mathlib.Probability.Distributions.Beta
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Fractional discrepancy of signed atomic rows

The one-dimensional right-sided kernel in Meiners and Gnewuch, §3.5
(arXiv:2611.20739), acts on arbitrary signed point masses. Pairing with a
left-sided power convolves their orders. At complementary orders the
pairing recovers each strict tail, including its sign and endpoint convention.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Finset Filter Set
open scoped Topology

namespace GaloisForLFunctions.ArithmeticPositiveDuality.FractionalDiscrepancy

/-- Right-hand power with the open endpoint convention, including at order zero. -/
def cutPower (e x : ℝ) : ℝ := if 0 < x then x ^ e else 0

/-- Fractional discrepancy field of an atomic row. Repeated locations add algebraically. -/
def field {ι : Type*} (S : Finset ι) (p w : ι → ℝ) (e x : ℝ) : ℝ :=
  ∑ i ∈ S, w i * cutPower e (p i - x)

private lemma cutPower_scale (e x : ℝ) {d : ℝ} (hd : 0 < d) :
    cutPower e (d*x) = d^e * cutPower e x := by
  by_cases hx : 0 < x
  · simp only [cutPower, if_pos hx, if_pos (mul_pos hd hx), Real.mul_rpow hd.le hx.le]
  · simp only [cutPower, if_neg hx, if_neg (not_lt.mpr (mul_nonpos_of_nonneg_of_nonpos hd.le
      (le_of_not_gt hx))), mul_zero]

private lemma beta_pdf_integral {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∫ x, betaPDFReal a b x = 1 := by
  have hn (x : ℝ) : 0 ≤ betaPDFReal a b x := by
    by_cases h : 0 < x ∧ x < 1
    · exact (betaPDFReal_pos h.1 h.2 ha hb).le
    · simp [betaPDFReal, h]
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hn)
    (stronglyMeasurable_betaPDFReal a b).aestronglyMeasurable]
  change (∫⁻ x, betaPDF a b x).toReal = 1
  simp [lintegral_betaPDF_eq_one ha hb]

private lemma unit_convolution {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∫ x, cutPower (a-1) x * cutPower (b-1) (1-x) = beta a b := by
  have h (x : ℝ) : cutPower (a-1) x * cutPower (b-1) (1-x) =
      beta a b * betaPDFReal a b x := by
    by_cases h₁ : 0 < x <;> by_cases h₂ : x < 1 <;>
      simp [cutPower, betaPDFReal, h₁, h₂, sub_pos, (beta_pos ha hb).ne', ← mul_assoc]
  simp_rw [h, integral_const_mul, beta_pdf_integral ha hb, mul_one]

private lemma disjoint_powers (e f : ℝ) {x y : ℝ} (h : y ≤ x) (t : ℝ) :
    cutPower e (t-x) * cutPower f (y-t) = 0 := by
  by_cases ht : x < t
  · simp [cutPower, sub_pos, not_lt.mpr (h.trans ht.le)]
  · simp [cutPower, sub_pos, ht]

/-- Beta convolution of two one-sided powers on arbitrary translated supports. -/
theorem integral_cutPower_mul {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (x y : ℝ) :
    ∫ t, cutPower (a-1) (t-x) * cutPower (b-1) (y-t) =
      beta a b * cutPower (a+b-1) (y-x) := by
  by_cases h : x < y
  · let d := y-x
    have hd : 0 < d := sub_pos.mpr h
    let F := fun t => cutPower (a-1) t * cutPower (b-1) (d-t)
    have htrans := integral_sub_right_eq_self (μ := volume) F x
    have heq (t : ℝ) : d-(t-x) = y-t := by dsimp only [d]; ring
    have hscale := Measure.integral_comp_mul_left F d
    have hscaled (u : ℝ) : F (d*u) =
        (d^(a-1)*d^(b-1)) * (cutPower (a-1) u * cutPower (b-1) (1-u)) := by
      dsimp only [F]
      rw [show d-d*u=d*(1-u) by ring, cutPower_scale _ _ hd, cutPower_scale _ _ hd]
      ring
    simp_rw [hscaled] at hscale
    rw [integral_const_mul, unit_convolution ha hb, abs_of_pos (inv_pos.mpr hd),
      smul_eq_mul] at hscale
    have hp : d*(d^(a-1)*d^(b-1)) = d^(a+b-1) := by
      rw [show a+b-1=1+((a-1)+(b-1)) by ring, Real.rpow_add hd, Real.rpow_one, Real.rpow_add hd]
    change (∫ t, cutPower (a-1) (t-x) * cutPower (b-1) (y-t)) =
      beta a b * cutPower (a+b-1) d
    simpa only [F, heq] using htrans.trans (show (∫ t, F t) = beta a b * cutPower (a+b-1) d by
      rw [cutPower, if_pos hd, ← hp]
      have hc := congrArg (d * ·) hscale
      rw [← mul_assoc d d⁻¹, mul_inv_cancel₀ hd.ne', one_mul] at hc
      rw [← hc]; ring)
  · simp_rw [disjoint_powers _ _ (le_of_not_gt h), integral_zero, cutPower, sub_pos, if_neg h, mul_zero]

private lemma kernel_integrable {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (x y : ℝ) :
    Integrable (fun t => cutPower (a-1) (t-x) * cutPower (b-1) (y-t)) := by
  by_cases h : x < y
  · by_contra hbad
    have he := integral_cutPower_mul ha hb x y
    rw [integral_undef hbad, cutPower, if_pos (sub_pos.mpr h)] at he
    exact (mul_pos (beta_pos ha hb) (Real.rpow_pos_of_pos (sub_pos.mpr h) _)).ne he
  · simp_rw [disjoint_powers _ _ (le_of_not_gt h)]
    exact integrable_zero _ _ _

/-- Pairing with a power of complementary orientation adds the two orders.
Finite signed sums commute with the integral, including at coincident endpoints. -/
theorem integral_field {ι : Type*} (S : Finset ι) (p w : ι → ℝ) {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (x : ℝ) :
    ∫ t, cutPower (a-1) (t-x) * field S p w (b-1) t =
      beta a b * field S p w (a+b-1) x := by
  simp only [field, mul_sum, mul_left_comm (cutPower _ _) (w _)]
  rw [integral_finsetSum S (fun i _ => (kernel_integrable ha hb x (p i)).const_mul (w i))]
  simp_rw [integral_const_mul, integral_cutPower_mul ha hb, mul_left_comm (w _) (beta a b)]

/-- Every power pairing is absolutely integrable, even for signed weights. -/
theorem integrable_pairing {ι : Type*} (S : Finset ι) (p w : ι → ℝ) {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (x : ℝ) :
    Integrable (fun t => cutPower (a-1) (t-x) * field S p w (b-1) t) := by
  simp only [field, mul_sum, mul_left_comm (cutPower _ _) (w _)]
  exact integrable_finsetSum S fun i _ => (kernel_integrable ha hb x (p i)).const_mul (w i)

/-- Fractional inversion at any order strictly between zero and one. -/
theorem complementary_tail {ι : Type*} (S : Finset ι) (p w : ι → ℝ)
    {b : ℝ} (hb : b ∈ Set.Ioo 0 1) (x : ℝ) :
    (∫ t, cutPower (-b) (t-x) * field S p w (b-1) t) =
      beta (1-b) b * ∑ i ∈ S, if x < p i then w i else 0 := by
  have h := integral_field S p w (sub_pos.mpr hb.2) hb.1 x
  simpa [show 1-b-1 = -b by ring, show 1-b+b-1=0 by ring, field, cutPower,
    sub_pos, mul_ite] using h

/-- At half order the inverse has the same power kernel, with constant π. -/
theorem half_order_tail {ι : Type*} (S : Finset ι) (p w : ι → ℝ) (x : ℝ) :
    (∫ t, cutPower (-(1/2)) (t-x) * field S p w (-(1/2)) t) =
      Real.pi * ∑ i ∈ S, if x < p i then w i else 0 := by
  have h := complementary_tail S p w (b := 1/2) (by constructor <;> norm_num) x
  norm_num [beta, Real.Gamma_one_half_eq, Real.mul_self_sqrt Real.pi_pos.le] at h ⊢
  exact h

/-- Duality for two signed atomic rows. On the right only ordered pairs survive.
At coincident atoms the strict tail convention discards the pair. -/
theorem paired_rows {ι κ : Type*} (S : Finset ι) (T : Finset κ) (p w : ι → ℝ)
    (q v : κ → ℝ) {b : ℝ} (hb : b ∈ Set.Ioo 0 1) :
    (∫ t, (∑ j ∈ T, v j * cutPower (-b) (t-q j)) * field S p w (b-1) t) =
      beta (1-b) b * ∑ j ∈ T, v j * ∑ i ∈ S, if q j < p i then w i else 0 := by
  have hi (j : κ) : Integrable (fun t => cutPower (-b) (t-q j) * field S p w (b-1) t) := by
    simpa only [show 1-b-1 = -b by ring] using
      integrable_pairing S p w (sub_pos.mpr hb.2) hb.1 (q j)
  simp only [sum_mul, mul_assoc]
  rw [integral_finsetSum T (fun j _ => (hi j).const_mul (v j))]
  simp_rw [integral_const_mul, complementary_tail S p w hb]
  rw [mul_sum]
  exact sum_congr rfl fun j _ => mul_left_comm ..

#print axioms integral_field
#print axioms half_order_tail
#print axioms paired_rows

end GaloisForLFunctions.ArithmeticPositiveDuality.FractionalDiscrepancy
