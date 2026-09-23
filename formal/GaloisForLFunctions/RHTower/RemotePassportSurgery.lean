import GaloisForLFunctions.RHTower.LiRemoteQuartetGaugedCarrier
import GaloisForLFunctions.RHTower.ImaginaryAxisPositiveRepair
import GaloisForLFunctions.RHTower.FiniteOrderSymmetryHTRationalGaugeBlindness
import GaloisForLFunctions.HTGeometry.DigammaFieldValuationRational
import GaloisForLFunctions.HTGeometry.PolynomialWeightedValuationBoundary
import GaloisForLFunctions.HTGeometry.IteratedDerivTranslate
import GaloisForLFunctions.HTGeometry.RemotePairEscapeGauge
import GaloisForLFunctions.RHTower.DeningerArithmeticCompactOpen

/-!
# Symmetry-complete remote passport surgery

Real-even polynomial surgery inserts a prescribed remote quartet while preserving arbitrary finite
Hermite passports.  Coefficient decay gives compact-open convergence with every derivative; the
reflected-Gamma carrier then supplies exact order one, hypertranscendence, and literal equality of
the complete translated differential fields.  The final section proves a general finite-root Li
escape theorem and applies it to every finite Li prefix.
-/

open Complex Set Polynomial Filter Topology

namespace RHTower

open GaloisForLFunctions
open GaloisForLFunctions.HTGeometry

noncomputable section

def remotePassportPolynomial {ι : Type*} [Fintype ι]
    (M : ι → ℕ) (α : ι → ℂ) : Polynomial ℂ :=
  X ^ (2 : ℕ) * simultaneousFlatPolynomial M α

theorem remotePassportPolynomial_eval {ι : Type*} [Fintype ι]
    (M : ι → ℕ) (α : ι → ℂ) (w : ℂ) :
    (remotePassportPolynomial M α).eval w =
      w ^ (2 : ℕ) * simultaneousFlatProduct M α w := by
  rw [remotePassportPolynomial, eval_mul, eval_pow, eval_X,
    simultaneousFlatPolynomial_eval]

theorem remotePassportPolynomial_monic {ι : Type*} [Fintype ι]
    (M : ι → ℕ) (α : ι → ℂ) :
    (remotePassportPolynomial M α).Monic := by
  apply Polynomial.Monic.mul
  · exact monic_X.pow _
  · exact simultaneousFlatPolynomial_monic M α

theorem remotePassportPolynomial_ne_zero {ι : Type*} [Fintype ι]
    (M : ι → ℕ) (α : ι → ℂ) :
    remotePassportPolynomial M α ≠ 0 :=
  (remotePassportPolynomial_monic M α).ne_zero

theorem remotePassportPolynomial_natDegree_ge_two {ι : Type*} [Fintype ι]
    (M : ι → ℕ) (α : ι → ℂ) :
    2 ≤ (remotePassportPolynomial M α).natDegree := by
  rw [remotePassportPolynomial, Polynomial.Monic.natDegree_mul
    (monic_X.pow 2) (simultaneousFlatPolynomial_monic M α)]
  simp

theorem tendsto_pow_div_polynomial_eval_vertical_of_lt
    (p : Polynomial ℂ) (hp : p ≠ 0) (σ : ℝ) {k : ℕ}
    (hk : k < p.natDegree) :
    Tendsto (fun t : ℝ =>
      (((σ : ℂ) + I * (t : ℂ)) ^ k) /
        p.eval ((σ : ℂ) + I * (t : ℂ))) atTop (nhds 0) := by
  let z : ℝ → ℂ := fun t => (σ : ℂ) + (t : ℂ) * I
  have hlead : p.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hp
  have hnorm := tendsto_eval_div_pow_natDegree_vertical σ p
  have hinv := hnorm.inv₀ hlead
  have hneg := tendsto_one_div_vertical_pow σ (Nat.sub_pos_of_lt hk)
  have hmul := hinv.mul hneg
  have heq : ∀ᶠ t : ℝ in atTop,
      (p.eval (z t) / (z t) ^ p.natDegree)⁻¹ *
          (1 / (z t) ^ (p.natDegree - k)) =
        (z t) ^ k / p.eval (z t) := by
    filter_upwards [eventually_vertical_ne_zero σ,
      hnorm.eventually_ne hlead] with t hzt hratio
    have hpzt : p.eval (z t) ≠ 0 := by
      intro hzero
      apply hratio
      rw [hzero, zero_div]
    rw [inv_div]
    field_simp
    rw [div_eq_iff (pow_ne_zero _ hzt)]
    rw [← pow_add]
    congr 1
    omega
  have hzero : (p.leadingCoeff)⁻¹ * 0 = (0 : ℂ) := mul_zero _
  rw [hzero] at hmul
  exact hmul.congr' (heq.mono fun t ht => by
    simpa [z, mul_comm] using ht)

def remotePassportPoint (a T : ℝ) : ℂ :=
  (a : ℂ) + I * (T : ℂ)

def remotePassportTarget (a T : ℝ) : ℂ :=
  (1 / 2 : ℂ) + remotePassportPoint a T

def remotePassportInverseValue {ι : Type*} [Fintype ι]
    (M : ι → ℕ) (α : ι → ℂ) (a T : ℝ) : ℂ :=
  -((remotePassportPolynomial M α).eval (remotePassportPoint a T))⁻¹

def remotePassportD {ι : Type*} [Fintype ι]
    (M : ι → ℕ) (α : ι → ℂ) (a T : ℝ) : ℝ :=
  (remotePassportInverseValue M α a T).im /
    ((remotePassportPoint a T) ^ (2 : ℕ)).im

def remotePassportC {ι : Type*} [Fintype ι]
    (M : ι → ℕ) (α : ι → ℂ) (a T : ℝ) : ℝ :=
  (remotePassportInverseValue M α a T).re -
    remotePassportD M α a T * ((remotePassportPoint a T) ^ (2 : ℕ)).re

theorem remotePassportPoint_sq_im (a T : ℝ) :
    ((remotePassportPoint a T) ^ (2 : ℕ)).im = 2 * a * T := by
  simp [remotePassportPoint, pow_two]
  ring

theorem remotePassportPoint_sq_re (a T : ℝ) :
    ((remotePassportPoint a T) ^ (2 : ℕ)).re = a ^ (2 : ℕ) - T ^ (2 : ℕ) := by
  simp [remotePassportPoint, pow_two]

theorem tendsto_remotePassportInverseValue {ι : Type*} [Fintype ι]
    (M : ι → ℕ) (α : ι → ℂ) (a : ℝ) :
    Tendsto (remotePassportInverseValue M α a) atTop (nhds 0) := by
  have h := tendsto_pow_div_polynomial_eval_vertical_of_lt
    (remotePassportPolynomial M α) (remotePassportPolynomial_ne_zero M α) a
    (k := 0) (lt_of_lt_of_le (by norm_num) (remotePassportPolynomial_natDegree_ge_two M α))
  have hneg : Tendsto (fun T : ℝ =>
      -(((a : ℂ) + I * (T : ℂ)) ^ (0 : ℕ) /
        (remotePassportPolynomial M α).eval ((a : ℂ) + I * (T : ℂ))))
      atTop (nhds 0) := by simpa using h.neg
  refine hneg.congr' (Eventually.of_forall fun T => ?_)
  simp [remotePassportInverseValue, remotePassportPoint]

theorem tendsto_height_mul_remotePassportInverseValue {ι : Type*} [Fintype ι]
    (M : ι → ℕ) (α : ι → ℂ) (a : ℝ) :
    Tendsto (fun T : ℝ => (T : ℂ) * remotePassportInverseValue M α a T)
      atTop (nhds 0) := by
  let p := remotePassportPolynomial M α
  have hp : p ≠ 0 := remotePassportPolynomial_ne_zero M α
  have hdeg : 2 ≤ p.natDegree := remotePassportPolynomial_natDegree_ge_two M α
  have h0 := tendsto_pow_div_polynomial_eval_vertical_of_lt p hp a
    (k := 0) (lt_of_lt_of_le (by norm_num) hdeg)
  have h1 := tendsto_pow_div_polynomial_eval_vertical_of_lt p hp a
    (k := 1) (lt_of_lt_of_le (by norm_num) hdeg)
  have hconst : Tendsto (fun _ : ℝ => (a : ℂ)) atTop (nhds (a : ℂ)) :=
    tendsto_const_nhds
  have hdiff := h1.sub (hconst.mul h0)
  have hdiff0 : Tendsto (fun T : ℝ =>
      (((a : ℂ) + I * (T : ℂ)) ^ (1 : ℕ) / p.eval ((a : ℂ) + I * (T : ℂ))) -
        (a : ℂ) * (((a : ℂ) + I * (T : ℂ)) ^ (0 : ℕ) /
          p.eval ((a : ℂ) + I * (T : ℂ)))) atTop (nhds 0) := by
    simpa using hdiff
  have hI : Tendsto (fun T : ℝ => I *
      ((((a : ℂ) + I * (T : ℂ)) ^ (1 : ℕ) / p.eval ((a : ℂ) + I * (T : ℂ))) -
        (a : ℂ) * (((a : ℂ) + I * (T : ℂ)) ^ (0 : ℕ) /
          p.eval ((a : ℂ) + I * (T : ℂ))))) atTop (nhds 0) := by
    simpa using (tendsto_const_nhds.mul hdiff0 :
      Tendsto (fun T : ℝ => I *
        ((((a : ℂ) + I * (T : ℂ)) ^ (1 : ℕ) / p.eval ((a : ℂ) + I * (T : ℂ))) -
          (a : ℂ) * (((a : ℂ) + I * (T : ℂ)) ^ (0 : ℕ) /
            p.eval ((a : ℂ) + I * (T : ℂ))))) atTop (nhds (I * 0)))
  exact hI.congr' (Eventually.of_forall fun T => by
    simp only [pow_one, pow_zero]
    simp [remotePassportInverseValue, remotePassportPoint, p, div_eq_mul_inv]
    calc
      I * (((a : ℂ) + I * (T : ℂ)) *
          ((remotePassportPolynomial M α).eval ((a : ℂ) + I * (T : ℂ)))⁻¹ -
        (a : ℂ) *
          ((remotePassportPolynomial M α).eval ((a : ℂ) + I * (T : ℂ)))⁻¹) =
          (I * I) * (T : ℂ) *
            ((remotePassportPolynomial M α).eval ((a : ℂ) + I * (T : ℂ)))⁻¹ := by ring
      _ = -((T : ℂ) *
            ((remotePassportPolynomial M α).eval ((a : ℂ) + I * (T : ℂ)))⁻¹) := by
        rw [I_mul_I]
        ring)

theorem tendsto_remotePassportD {ι : Type*} [Fintype ι]
    (M : ι → ℕ) (α : ι → ℂ) {a : ℝ} (ha : a ≠ 0) :
    Tendsto (remotePassportD M α a) atTop (nhds 0) := by
  have hb := tendsto_remotePassportInverseValue M α a
  have hbim : Tendsto (fun T => (remotePassportInverseValue M α a T).im)
      atTop (nhds 0) := by
    exact ((Complex.continuous_im.tendsto 0).comp hb).congr'
      (Eventually.of_forall fun _ => rfl)
  have hinv : Tendsto (fun T : ℝ => T⁻¹) atTop (nhds 0) := tendsto_inv_atTop_zero
  have hconst : Tendsto (fun _ : ℝ => (2 * a)⁻¹) atTop (nhds (2 * a)⁻¹) :=
    tendsto_const_nhds
  have hprod := hbim.mul (hconst.mul hinv)
  have hprod0 : Tendsto (fun T =>
      (remotePassportInverseValue M α a T).im * ((2 * a)⁻¹ * T⁻¹))
      atTop (nhds 0) := by simpa using hprod
  refine hprod0.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
  rw [remotePassportD, remotePassportPoint_sq_im]
  field_simp [ha, ne_of_gt hT]

theorem tendsto_remotePassportD_mul_point_sq_re {ι : Type*} [Fintype ι]
    (M : ι → ℕ) (α : ι → ℂ) {a : ℝ} (ha : a ≠ 0) :
    Tendsto (fun T => remotePassportD M α a T *
      ((remotePassportPoint a T) ^ (2 : ℕ)).re) atTop (nhds 0) := by
  have hb := tendsto_remotePassportInverseValue M α a
  have hbim : Tendsto (fun T => (remotePassportInverseValue M α a T).im)
      atTop (nhds 0) := by
    exact ((Complex.continuous_im.tendsto 0).comp hb).congr'
      (Eventually.of_forall fun _ => rfl)
  have hbT := tendsto_height_mul_remotePassportInverseValue M α a
  have hbTim : Tendsto (fun T : ℝ =>
      ((T : ℂ) * remotePassportInverseValue M α a T).im) atTop (nhds 0) := by
    exact ((Complex.continuous_im.tendsto 0).comp hbT).congr'
      (Eventually.of_forall fun _ => rfl)
  have hinv : Tendsto (fun T : ℝ => T⁻¹) atTop (nhds 0) := tendsto_inv_atTop_zero
  have hsmall : Tendsto (fun T =>
      (remotePassportInverseValue M α a T).im * a / (2 * T)) atTop (nhds 0) := by
    have h := (hbim.mul hinv).const_mul (a / 2)
    have h0 : Tendsto (fun T =>
        a / 2 * ((remotePassportInverseValue M α a T).im * T⁻¹))
        atTop (nhds 0) := by simpa using h
    refine h0.congr' (Eventually.of_forall fun T => ?_)
    ring
  have hlarge : Tendsto (fun T : ℝ =>
      ((T : ℂ) * remotePassportInverseValue M α a T).im / (2 * a))
      atTop (nhds 0) := by
    have h := hbTim.const_mul ((2 * a)⁻¹)
    have h0 : Tendsto (fun T : ℝ => (2 * a)⁻¹ *
        ((T : ℂ) * remotePassportInverseValue M α a T).im) atTop (nhds 0) := by
      simpa using h
    exact h0.congr' (Eventually.of_forall fun T => by ring)
  have hdiff := hsmall.sub hlarge
  have hdiff0 : Tendsto (fun T =>
      (remotePassportInverseValue M α a T).im * a / (2 * T) -
        ((T : ℂ) * remotePassportInverseValue M α a T).im / (2 * a))
      atTop (nhds 0) := by simpa using hdiff
  refine hdiff0.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
  rw [remotePassportD, remotePassportPoint_sq_im, remotePassportPoint_sq_re]
  have him : ((T : ℂ) * remotePassportInverseValue M α a T).im =
      T * (remotePassportInverseValue M α a T).im := by simp
  rw [him]
  field_simp [ha, ne_of_gt hT]

theorem tendsto_remotePassportC {ι : Type*} [Fintype ι]
    (M : ι → ℕ) (α : ι → ℂ) {a : ℝ} (ha : a ≠ 0) :
    Tendsto (remotePassportC M α a) atTop (nhds 0) := by
  have hb := tendsto_remotePassportInverseValue M α a
  have hbre : Tendsto (fun T => (remotePassportInverseValue M α a T).re)
      atTop (nhds 0) := by
    exact ((Complex.continuous_re.tendsto 0).comp hb).congr'
      (Eventually.of_forall fun _ => rfl)
  have hsub := hbre.sub (tendsto_remotePassportD_mul_point_sq_re M α ha)
  have hsub0 : Tendsto (fun T =>
      (remotePassportInverseValue M α a T).re -
        remotePassportD M α a T * ((remotePassportPoint a T) ^ (2 : ℕ)).re)
      atTop (nhds 0) := by simpa using hsub
  exact hsub0.congr' (Eventually.of_forall fun _ => rfl)

theorem remotePassport_coefficients_solve {ι : Type*} [Fintype ι]
    (M : ι → ℕ) (α : ι → ℂ) {a T : ℝ} (ha : a ≠ 0) (hT : T ≠ 0) :
    (remotePassportC M α a T : ℂ) +
        (remotePassportD M α a T : ℂ) * (remotePassportPoint a T) ^ (2 : ℕ) =
      remotePassportInverseValue M α a T := by
  apply Complex.ext
  · simp [remotePassportC]
  · simp only [add_im, ofReal_im, mul_im, ofReal_re, zero_mul, add_zero]
    rw [remotePassportD, remotePassportPoint_sq_im]
    field_simp [ha, hT]
    simp

def remotePassportGauge {ι : Type*} [Fintype ι]
    (M : ι → ℕ) (α : ι → ℂ) (a T : ℝ) (s : ℂ) : ℂ :=
  1 + (remotePassportPolynomial M α).eval (s - (1 / 2 : ℂ)) *
    ((remotePassportC M α a T : ℂ) +
      (remotePassportD M α a T : ℂ) * (s - (1 / 2 : ℂ)) ^ (2 : ℕ))

theorem remotePassportGauge_target_zero {ι : Type*} [Fintype ι]
    (M : ι → ℕ) (α : ι → ℂ) {a T : ℝ} (ha : a ≠ 0) (hT : T ≠ 0)
    (hpoly : (remotePassportPolynomial M α).eval (remotePassportPoint a T) ≠ 0) :
    remotePassportGauge M α a T (remotePassportTarget a T) = 0 := by
  rw [remotePassportGauge]
  have hcenter : remotePassportTarget a T - (1 / 2 : ℂ) = remotePassportPoint a T := by
    simp [remotePassportTarget]
  rw [hcenter, remotePassport_coefficients_solve M α ha hT,
    remotePassportInverseValue]
  rw [mul_neg, mul_inv_cancel₀ hpoly]
  ring

theorem remotePassportPolynomial_eval_neg {ι : Type*} [Fintype ι]
    (M : ι → ℕ) (α : ι → ℂ) (w : ℂ) :
    (remotePassportPolynomial M α).eval (-w) =
      (remotePassportPolynomial M α).eval w := by
  rw [remotePassportPolynomial_eval, remotePassportPolynomial_eval]
  have hprod : simultaneousFlatProduct M α (-w) = simultaneousFlatProduct M α w := by
    rw [simultaneousFlatProduct, simultaneousFlatProduct]
    apply Finset.prod_congr rfl
    intro i _
    unfold quartetFlatAtom
    ring
  rw [hprod]
  ring

theorem remotePassportPolynomial_eval_conj {ι : Type*} [Fintype ι]
    (M : ι → ℕ) (α : ι → ℂ) (w : ℂ) :
    (remotePassportPolynomial M α).eval ((starRingEnd ℂ) w) =
      (starRingEnd ℂ) ((remotePassportPolynomial M α).eval w) := by
  rw [remotePassportPolynomial_eval, remotePassportPolynomial_eval]
  simp only [map_mul, map_pow]
  congr 1
  rw [simultaneousFlatProduct, simultaneousFlatProduct, map_prod]
  apply Finset.prod_congr rfl
  intro i _
  simp only [map_pow]
  congr 1
  unfold quartetFlatAtom
  simp only [map_mul, map_sub, map_pow, Complex.conj_conj]
  ring

theorem remotePassportGauge_one_sub {ι : Type*} [Fintype ι]
    (M : ι → ℕ) (α : ι → ℂ) (a T : ℝ) (s : ℂ) :
    remotePassportGauge M α a T (1 - s) = remotePassportGauge M α a T s := by
  rw [remotePassportGauge, remotePassportGauge]
  have hcenter : 1 - s - (1 / 2 : ℂ) = -(s - (1 / 2 : ℂ)) := by ring
  rw [hcenter, remotePassportPolynomial_eval_neg]
  ring

theorem remotePassportGauge_conj {ι : Type*} [Fintype ι]
    (M : ι → ℕ) (α : ι → ℂ) (a T : ℝ) (s : ℂ) :
    remotePassportGauge M α a T ((starRingEnd ℂ) s) =
      (starRingEnd ℂ) (remotePassportGauge M α a T s) := by
  rw [remotePassportGauge, remotePassportGauge]
  have hcenter : (starRingEnd ℂ) s - (1 / 2 : ℂ) =
      (starRingEnd ℂ) (s - (1 / 2 : ℂ)) := by
    apply Complex.ext <;> simp
  rw [hcenter, remotePassportPolynomial_eval_conj]
  simp only [map_add, map_one, map_mul, map_pow, Complex.conj_ofReal]

theorem remotePassportGauge_half {ι : Type*} [Fintype ι]
    (M : ι → ℕ) (α : ι → ℂ) (a T : ℝ) :
    remotePassportGauge M α a T (1 / 2 : ℂ) = 1 := by
  simp [remotePassportGauge, remotePassportPolynomial_eval]

theorem remotePassportGauge_quartet_zero {ι : Type*} [Fintype ι]
    (M : ι → ℕ) (α : ι → ℂ) {a T : ℝ} (ha : a ≠ 0) (hT : T ≠ 0)
    (hpoly : (remotePassportPolynomial M α).eval (remotePassportPoint a T) ≠ 0) :
    remotePassportGauge M α a T (remotePassportTarget a T) = 0 ∧
      remotePassportGauge M α a T (1 - remotePassportTarget a T) = 0 ∧
      remotePassportGauge M α a T ((starRingEnd ℂ) (remotePassportTarget a T)) = 0 ∧
      remotePassportGauge M α a T
        (1 - (starRingEnd ℂ) (remotePassportTarget a T)) = 0 := by
  have hzero := remotePassportGauge_target_zero M α ha hT hpoly
  refine ⟨hzero, ?_, ?_, ?_⟩
  · rw [remotePassportGauge_one_sub, hzero]
  · rw [remotePassportGauge_conj, hzero, map_zero]
  · rw [remotePassportGauge_one_sub, remotePassportGauge_conj, hzero, map_zero]

theorem remotePassportTarget_quartet_mem_criticalStrip
    {a T : ℝ} (ha : |a| < 1 / 2) :
    (0 < (remotePassportTarget a T).re ∧ (remotePassportTarget a T).re < 1) ∧
      (0 < (1 - remotePassportTarget a T).re ∧
        (1 - remotePassportTarget a T).re < 1) ∧
      (0 < ((starRingEnd ℂ) (remotePassportTarget a T)).re ∧
        ((starRingEnd ℂ) (remotePassportTarget a T)).re < 1) ∧
      (0 < (1 - (starRingEnd ℂ) (remotePassportTarget a T)).re ∧
        (1 - (starRingEnd ℂ) (remotePassportTarget a T)).re < 1) := by
  have ha' := abs_lt.mp ha
  have hplus : (remotePassportTarget a T).re = 1 / 2 + a := by
    simp [remotePassportTarget, remotePassportPoint]
  have hminus : (1 - remotePassportTarget a T).re = 1 / 2 - a := by
    rw [sub_re, one_re, hplus]
    ring
  have hconjplus : ((starRingEnd ℂ) (remotePassportTarget a T)).re = 1 / 2 + a := by
    simp [remotePassportTarget, remotePassportPoint]
  have hconjminus : (1 - (starRingEnd ℂ) (remotePassportTarget a T)).re =
      1 / 2 - a := by
    rw [sub_re, one_re, hconjplus]
    ring
  rw [hplus, hminus, hconjplus, hconjminus]
  norm_num at ha' ⊢
  constructor
  · constructor <;> linarith
  constructor
  · constructor <;> linarith
  constructor <;> constructor <;> linarith

def remotePassportCorrectionPolynomial {ι : Type*} [Fintype ι]
    (M : ι → ℕ) (α : ι → ℂ) (a T : ℝ) : Polynomial ℂ :=
  remotePassportPolynomial M α *
    (Polynomial.C (remotePassportC M α a T : ℂ) +
      Polynomial.C (remotePassportD M α a T : ℂ) * X ^ (2 : ℕ))

theorem remotePassportCorrectionPolynomial_eval {ι : Type*} [Fintype ι]
    (M : ι → ℕ) (α : ι → ℂ) (a T : ℝ) (w : ℂ) :
    (remotePassportCorrectionPolynomial M α a T).eval w =
      remotePassportGauge M α a T ((1 / 2 : ℂ) + w) - 1 := by
  simp [remotePassportCorrectionPolynomial, remotePassportGauge]

theorem X_sub_C_pow_dvd_remotePassportCorrectionPolynomial
    {ι : Type*} [Fintype ι]
    (M : ι → ℕ) (α : ι → ℂ) (a T : ℝ) (i : ι) :
    (X - Polynomial.C (α i)) ^ (M i) ∣
      remotePassportCorrectionPolynomial M α a T := by
  obtain ⟨Q, hQ⟩ :=
    quartetFlatPolynomial_pow_dvd_simultaneousFlatPolynomial M α i
  have hlinear : X - Polynomial.C (α i) ∣ quartetFlatPolynomial (α i) := by
    rw [Polynomial.dvd_iff_isRoot]
    simp [Polynomial.IsRoot, quartetFlatPolynomial]
  obtain ⟨R, hR⟩ := hlinear
  refine ⟨R ^ M i * Q * X ^ (2 : ℕ) *
      (Polynomial.C (remotePassportC M α a T : ℂ) +
        Polynomial.C (remotePassportD M α a T : ℂ) * X ^ (2 : ℕ)), ?_⟩
  rw [remotePassportCorrectionPolynomial, remotePassportPolynomial, hQ, hR, mul_pow]
  ring

theorem remotePassportCorrectionPolynomial_iterate_derivative_eval_eq_zero_of_lt
    {ι : Type*} [Fintype ι]
    (M : ι → ℕ) (α : ι → ℂ) (a T : ℝ) (i : ι) {n : ℕ} (hn : n < M i) :
    (Polynomial.derivative^[n] (remotePassportCorrectionPolynomial M α a T)).eval (α i) = 0 := by
  by_cases hzero : remotePassportCorrectionPolynomial M α a T = 0
  · simp [hzero]
  · have hmult : M i ≤ Polynomial.rootMultiplicity (α i)
        (remotePassportCorrectionPolynomial M α a T) :=
      (Polynomial.le_rootMultiplicity_iff hzero).mpr
        (X_sub_C_pow_dvd_remotePassportCorrectionPolynomial M α a T i)
    exact Polynomial.isRoot_iterate_derivative_of_lt_rootMultiplicity
      (lt_of_lt_of_le hn hmult)

theorem remotePassportGauge_iteratedDeriv_sub_one_eq_zero_of_lt
    {ι : Type*} [Fintype ι]
    (M : ι → ℕ) (α : ι → ℂ) (a T : ℝ) (i : ι) {n : ℕ} (hn : n < M i) :
    iteratedDeriv n (fun s => remotePassportGauge M α a T s - 1)
        ((1 / 2 : ℂ) + α i) = 0 := by
  let Q := remotePassportCorrectionPolynomial M α a T
  have hfun : (fun s => remotePassportGauge M α a T s - 1) =
      fun s => Q.eval (s - (1 / 2 : ℂ)) := by
    funext s
    rw [remotePassportCorrectionPolynomial_eval]
    congr 2
    ring
  rw [hfun]
  simp only [sub_eq_add_neg]
  have htranslate := iteratedDeriv_comp_add_right (fun w => Q.eval w) (-(1 / 2 : ℂ)) n
      ((1 / 2 : ℂ) + α i)
  rw [htranslate]
  convert remotePassportCorrectionPolynomial_iterate_derivative_eval_eq_zero_of_lt
    M α a T i hn using 1
  · simp [Q, GaloisForLFunctions.iteratedDeriv_polynomial_eval]

def remotePassportGaugePolynomial {ι : Type*} [Fintype ι]
    (M : ι → ℕ) (α : ι → ℂ) (a T : ℝ) : Polynomial ℂ :=
  1 + (remotePassportCorrectionPolynomial M α a T).comp
    (X - Polynomial.C (1 / 2 : ℂ))

theorem remotePassportGaugePolynomial_eval {ι : Type*} [Fintype ι]
    (M : ι → ℕ) (α : ι → ℂ) (a T : ℝ) (s : ℂ) :
    (remotePassportGaugePolynomial M α a T).eval s =
      remotePassportGauge M α a T s := by
  rw [remotePassportGaugePolynomial, eval_add, eval_one, eval_comp, eval_sub, eval_X, eval_C,
    remotePassportCorrectionPolynomial_eval]
  unfold remotePassportGauge
  ring

theorem remotePassportGaugePolynomial_ne_zero {ι : Type*} [Fintype ι]
    (M : ι → ℕ) (α : ι → ℂ) (a T : ℝ) :
    remotePassportGaugePolynomial M α a T ≠ 0 := by
  intro hzero
  have heval := congrArg (fun P : Polynomial ℂ => P.eval (1 / 2 : ℂ)) hzero
  rw [remotePassportGaugePolynomial_eval, remotePassportGauge_half] at heval
  simp at heval

theorem remotePassportGaugePolynomial_natDegree_le {ι : Type*} [Fintype ι]
    (M : ι → ℕ) (α : ι → ℂ) (a T : ℝ) :
    (remotePassportGaugePolynomial M α a T).natDegree ≤
      (remotePassportPolynomial M α).natDegree + 2 := by
  have hquad :
      (Polynomial.C (remotePassportC M α a T : ℂ) +
        Polynomial.C (remotePassportD M α a T : ℂ) * X ^ (2 : ℕ)).natDegree ≤ 2 := by
    calc
      _ ≤ max (Polynomial.C (remotePassportC M α a T : ℂ)).natDegree
          (Polynomial.C (remotePassportD M α a T : ℂ) * X ^ (2 : ℕ)).natDegree :=
        Polynomial.natDegree_add_le _ _
      _ ≤ 2 := by
        have hmul := Polynomial.natDegree_mul_le (R := ℂ)
          (p := Polynomial.C (remotePassportD M α a T : ℂ)) (q := X ^ (2 : ℕ))
        rw [Polynomial.natDegree_C, Polynomial.natDegree_pow,
          Polynomial.natDegree_X] at hmul
        norm_num at hmul
        rw [Polynomial.natDegree_C]
        exact max_le (by omega) hmul
  have hcorrection :
      (remotePassportCorrectionPolynomial M α a T).natDegree ≤
        (remotePassportPolynomial M α).natDegree + 2 := by
    rw [remotePassportCorrectionPolynomial]
    exact (Polynomial.natDegree_mul_le.trans (Nat.add_le_add_left hquad _))
  rw [remotePassportGaugePolynomial]
  refine (Polynomial.natDegree_add_le _ _).trans ?_
  have hcomp := Polynomial.natDegree_comp_le (R := ℂ)
    (p := remotePassportCorrectionPolynomial M α a T)
    (q := X - Polynomial.C (1 / 2 : ℂ))
  rw [Polynomial.natDegree_X_sub_C, mul_one] at hcomp
  simp only [natDegree_one, zero_le, max_eq_right]
  exact hcomp.trans hcorrection

theorem remotePassportGauge_iteratedDeriv_eq_one_of_lt
    {ι : Type*} [Fintype ι]
    (M : ι → ℕ) (α : ι → ℂ) (a T : ℝ) (i : ι) {n : ℕ} (hn : n < M i) :
    iteratedDeriv n (remotePassportGauge M α a T)
        ((1 / 2 : ℂ) + α i) =
      iteratedDeriv n (fun _ : ℂ => (1 : ℂ)) ((1 / 2 : ℂ) + α i) := by
  have hflat := remotePassportGauge_iteratedDeriv_sub_one_eq_zero_of_lt
    M α a T i hn
  have hshape : (fun s => remotePassportGauge M α a T s - 1) =
      remotePassportGauge M α a T - (fun _ : ℂ => (1 : ℂ)) := rfl
  rw [hshape, iteratedDeriv_sub] at hflat
  · exact sub_eq_zero.mp hflat
  · rw [show remotePassportGauge M α a T =
        fun s => (remotePassportGaugePolynomial M α a T).eval s by
      funext s
      exact (remotePassportGaugePolynomial_eval M α a T s).symm]
    have hsmooth : ContDiff ℂ (n : ℕ∞)
        (fun s => (remotePassportGaugePolynomial M α a T).eval s) := by
      simpa only [Polynomial.coe_aeval_eq_eval] using
        (Polynomial.contDiff_aeval (𝕜 := ℂ)
          (remotePassportGaugePolynomial M α a T) (n : ℕ∞))
    exact hsmooth.contDiffAt
  · fun_prop

theorem remotePassportGaugePolynomial_iterate_derivative_eval_eq_one_of_lt
    {ι : Type*} [Fintype ι]
    (M : ι → ℕ) (α : ι → ℂ) (a T : ℝ) (i : ι) {n : ℕ} (hn : n < M i) :
    (Polynomial.derivative^[n] (remotePassportGaugePolynomial M α a T)).eval
        ((1 / 2 : ℂ) + α i) =
      (Polynomial.derivative^[n] (1 : Polynomial ℂ)).eval
        ((1 / 2 : ℂ) + α i) := by
  rw [← GaloisForLFunctions.iteratedDeriv_polynomial_eval,
    ← GaloisForLFunctions.iteratedDeriv_polynomial_eval]
  rw [show (fun x => (remotePassportGaugePolynomial M α a T).eval x) =
      remotePassportGauge M α a T by
        funext x
        exact remotePassportGaugePolynomial_eval M α a T x]
  simpa using remotePassportGauge_iteratedDeriv_eq_one_of_lt M α a T i hn

theorem remotePassportGauge_tendstoLocallyUniformly {ι : Type*} [Fintype ι]
    (M : ι → ℕ) (α : ι → ℂ) {a : ℝ} (ha : a ≠ 0) :
    TendstoLocallyUniformly (remotePassportGauge M α a)
      (fun _ : ℂ => (1 : ℂ)) atTop := by
  let gC : ℂ → ℂ := fun s =>
    (remotePassportPolynomial M α).eval (s - (1 / 2 : ℂ))
  let gD : ℂ → ℂ := fun s =>
    (remotePassportPolynomial M α).eval (s - (1 / 2 : ℂ)) *
      (s - (1 / 2 : ℂ)) ^ (2 : ℕ)
  have hgC : Continuous gC := by
    dsimp [gC]
    fun_prop
  have hgD : Continuous gD := by
    dsimp [gD]
    fun_prop
  have hCℂ : Tendsto (fun T => (remotePassportC M α a T : ℂ)) atTop (nhds 0) := by
    exact ((Complex.continuous_ofReal.tendsto 0).comp
      (tendsto_remotePassportC M α ha)).congr' (Eventually.of_forall fun _ => rfl)
  have hDℂ : Tendsto (fun T => (remotePassportD M α a T : ℂ)) atTop (nhds 0) := by
    exact ((Complex.continuous_ofReal.tendsto 0).comp
      (tendsto_remotePassportD M α ha)).congr' (Eventually.of_forall fun _ => rfl)
  have hC := tendstoLocallyUniformly_one_add_mul
    (fun T => (remotePassportC M α a T : ℂ)) gC hgC hCℂ
  have hD := tendstoLocallyUniformly_one_add_mul
    (fun T => (remotePassportD M α a T : ℂ)) gD hgD hDℂ
  have hneg : TendstoLocallyUniformly
      (fun (_ : ℝ) (_ : ℂ) => (-1 : ℂ)) (fun _ : ℂ => (-1 : ℂ)) atTop :=
    tendstoLocallyUniformly_const_seq _
  have htotal := (hC.add hD).add hneg
  convert htotal using 1
  · funext T s
    simp [remotePassportGauge, gC, gD]
    ring
  · funext s
    simp

theorem eventually_remotePassportGauge_ne_zero_on_compact
    {ι : Type*} [Fintype ι]
    (M : ι → ℕ) (α : ι → ℂ) {a : ℝ} (ha : a ≠ 0)
    (K : Set ℂ) (hK : IsCompact K) :
    ∀ᶠ T : ℝ in atTop, ∀ s ∈ K, remotePassportGauge M α a T s ≠ 0 := by
  have hconv := remotePassportGauge_tendstoLocallyUniformly M α ha
  have huniform : TendstoUniformlyOn (remotePassportGauge M α a)
      (fun _ : ℂ => (1 : ℂ)) atTop K :=
    (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hK).mp
      hconv.tendstoLocallyUniformlyOn
  have hclose : ∀ᶠ T : ℝ in atTop, ∀ s ∈ K,
      dist (remotePassportGauge M α a T s) (1 : ℂ) < 1 / 2 :=
    by
      simpa only [dist_comm] using
        (Metric.tendstoUniformlyOn_iff.mp huniform) (1 / 2) (by norm_num)
  filter_upwards [hclose] with T hT
  intro s hs hzero
  have h := hT s hs
  rw [hzero] at h
  norm_num at h

theorem remotePassportGauge_differentiable {ι : Type*} [Fintype ι]
    (M : ι → ℕ) (α : ι → ℂ) (a T : ℝ) :
    Differentiable ℂ (remotePassportGauge M α a T) := by
  unfold remotePassportGauge
  fun_prop

def remotePassportGaugedCarrier {ι : Type*} [Fintype ι]
    (alpha : ℝ) (M : ι → ℕ) (α : ι → ℂ) (a T : ℝ) (s : ℂ) : ℂ :=
  remotePassportGauge M α a T s * liReflectedGammaCarrier alpha s

theorem remotePassportGaugedCarrier_eq_polynomialGaugedLiCarrier
    {ι : Type*} [Fintype ι]
    (alpha : ℝ) (M : ι → ℕ) (α : ι → ℂ) (a T : ℝ) :
    remotePassportGaugedCarrier alpha M α a T =
      polynomialGaugedLiCarrier alpha (remotePassportGaugePolynomial M α a T) := by
  funext s
  rw [remotePassportGaugedCarrier, polynomialGaugedLiCarrier,
    remotePassportGaugePolynomial_eval]

theorem remotePassportGaugedCarrier_analyticOnNhd
    {ι : Type*} [Fintype ι]
    (alpha : ℝ) (M : ι → ℕ) (α : ι → ℂ) (a T : ℝ) :
    AnalyticOnNhd ℂ (remotePassportGaugedCarrier alpha M α a T) Set.univ := by
  rw [remotePassportGaugedCarrier_eq_polynomialGaugedLiCarrier]
  exact polynomialGaugedLiCarrier_analyticOnNhd alpha _

theorem remotePassportGaugedCarrier_one_sub
    {ι : Type*} [Fintype ι]
    (alpha : ℝ) (M : ι → ℕ) (α : ι → ℂ) (a T : ℝ) (s : ℂ) :
    remotePassportGaugedCarrier alpha M α a T (1 - s) =
      remotePassportGaugedCarrier alpha M α a T s := by
  rw [remotePassportGaugedCarrier, remotePassportGaugedCarrier,
    remotePassportGauge_one_sub, liReflectedGammaCarrier_one_sub]

theorem remotePassportGaugedCarrier_conj
    {ι : Type*} [Fintype ι]
    (alpha : ℝ) (M : ι → ℕ) (α : ι → ℂ) (a T : ℝ) (s : ℂ) :
    remotePassportGaugedCarrier alpha M α a T ((starRingEnd ℂ) s) =
      (starRingEnd ℂ) (remotePassportGaugedCarrier alpha M α a T s) := by
  rw [remotePassportGaugedCarrier, remotePassportGaugedCarrier,
    remotePassportGauge_conj, liReflectedGammaCarrier_conj, map_mul]

theorem remotePassportGaugedCarrier_hypertranscendental_of_two_mul_sub_one
    {ι : Type*} [Fintype ι]
    {alpha : ℝ} (M : ι → ℕ) (α : ι → ℂ) (a T : ℝ)
    (hsep : ∀ k : ℤ, (2 * alpha - 1 : ℂ) ≠ (k : ℂ)) :
    Hypertranscendental (remotePassportGaugedCarrier alpha M α a T) := by
  rw [remotePassportGaugedCarrier_eq_polynomialGaugedLiCarrier]
  exact polynomialGaugedLiCarrier_hypertranscendental_of_two_mul_sub_one
    (remotePassportGaugePolynomial_ne_zero M α a T) hsep

theorem remotePassportGaugedCarrier_hasExactEntireOrderOne
    {ι : Type*} [Fintype ι]
    {alpha : ℝ} (halpha : 0 < alpha) (M : ι → ℕ) (α : ι → ℂ) (a T : ℝ) :
    HasExactEntireOrderOne (remotePassportGaugedCarrier alpha M α a T) := by
  rw [remotePassportGaugedCarrier_eq_polynomialGaugedLiCarrier]
  apply polynomialGaugedLiCarrier_hasExactEntireOrderOne halpha
  rw [remotePassportGaugePolynomial_eval, remotePassportGauge_half]

theorem remotePassportGaugedCarrier_iteratedDeriv_eq_of_lt
    {ι : Type*} [Fintype ι]
    (alpha : ℝ) (M : ι → ℕ) (α : ι → ℂ) (a T : ℝ) (i : ι)
    {n : ℕ} (hn : n < M i) :
    iteratedDeriv n (remotePassportGaugedCarrier alpha M α a T)
        ((1 / 2 : ℂ) + α i) =
      iteratedDeriv n (liReflectedGammaCarrier alpha) ((1 / 2 : ℂ) + α i) := by
  rw [remotePassportGaugedCarrier_eq_polynomialGaugedLiCarrier]
  exact polynomialGaugedLiCarrier_iteratedDeriv_eq alpha _
    (fun j hj => remotePassportGaugePolynomial_iterate_derivative_eval_eq_one_of_lt
      M α a T i hj) hn

theorem remotePassportGaugedCarrier_target_zero
    {ι : Type*} [Fintype ι]
    (alpha : ℝ) (M : ι → ℕ) (α : ι → ℂ) {a T : ℝ}
    (ha : a ≠ 0) (hT : T ≠ 0)
    (hpoly : (remotePassportPolynomial M α).eval (remotePassportPoint a T) ≠ 0) :
    remotePassportGaugedCarrier alpha M α a T (remotePassportTarget a T) = 0 := by
  rw [remotePassportGaugedCarrier, remotePassportGauge_target_zero M α ha hT hpoly,
    zero_mul]

theorem remotePassportGaugedCarrier_quartet_zero
    {ι : Type*} [Fintype ι]
    (alpha : ℝ) (M : ι → ℕ) (α : ι → ℂ) {a T : ℝ}
    (ha : a ≠ 0) (hT : T ≠ 0)
    (hpoly : (remotePassportPolynomial M α).eval (remotePassportPoint a T) ≠ 0) :
    remotePassportGaugedCarrier alpha M α a T (remotePassportTarget a T) = 0 ∧
      remotePassportGaugedCarrier alpha M α a T (1 - remotePassportTarget a T) = 0 ∧
      remotePassportGaugedCarrier alpha M α a T
        ((starRingEnd ℂ) (remotePassportTarget a T)) = 0 ∧
      remotePassportGaugedCarrier alpha M α a T
        (1 - (starRingEnd ℂ) (remotePassportTarget a T)) = 0 := by
  obtain ⟨h1, h2, h3, h4⟩ := remotePassportGauge_quartet_zero M α ha hT hpoly
  simp only [remotePassportGaugedCarrier, h1, h2, h3, h4, zero_mul, and_self]

theorem eventually_remotePassportGaugedCarrier_quartet_zero
    {ι : Type*} [Fintype ι]
    (alpha : ℝ) (M : ι → ℕ) (α : ι → ℂ) {a : ℝ} (ha : a ≠ 0) :
    ∀ᶠ T : ℝ in atTop,
      0 < T ∧
      remotePassportGaugedCarrier alpha M α a T (remotePassportTarget a T) = 0 ∧
      remotePassportGaugedCarrier alpha M α a T (1 - remotePassportTarget a T) = 0 ∧
      remotePassportGaugedCarrier alpha M α a T
        ((starRingEnd ℂ) (remotePassportTarget a T)) = 0 ∧
      remotePassportGaugedCarrier alpha M α a T
        (1 - (starRingEnd ℂ) (remotePassportTarget a T)) = 0 := by
  have hpoly := polynomial_eval_eventually_ne_zero
    (remotePassportPolynomial_ne_zero M α) a
  filter_upwards [eventually_gt_atTop (0 : ℝ), hpoly] with T hT hpolyT
  have hpolyT' : (remotePassportPolynomial M α).eval
      (remotePassportPoint a T) ≠ 0 := by
    simpa [remotePassportPoint, mul_comm] using hpolyT
  exact ⟨hT, remotePassportGaugedCarrier_quartet_zero alpha M α ha hT.ne' hpolyT'⟩

def remotePassportGaugedCarrierTranslateFamily
    {ι : Type*} [Fintype ι]
    (alpha : ℝ) (M : ι → ℕ) (α : ι → ℂ) (a T : ℝ) (h : ℂ) : upperEndMeroField :=
  polynomialGaugedLiCarrierTranslateFamily alpha
    (remotePassportGaugePolynomial M α a T) h

theorem remotePassportGaugedCarrierTranslateFamily_allJets_adjoin_eq
    {ι : Type*} [Fintype ι]
    (alpha : ℝ) (M : ι → ℕ) (α : ι → ℂ) (a T : ℝ) :
    letI := isDomain_upperEndAnalyticSubring
    letI : Algebra (RatFunc ℂ) upperEndMeroField := upperEndRatfuncToMero.toAlgebra
    letI := ratFuncCoordinateDifferential
    letI := upperEndMeroFieldDifferential
    letI : DifferentialAlgebra (RatFunc ℂ) upperEndMeroField :=
      upperEndRatfuncDifferentialAlgebra
    IntermediateField.adjoin (RatFunc ℂ)
        (Set.range fun p : ℂ × ℕ => differentialJet p.2
          (remotePassportGaugedCarrierTranslateFamily alpha M α a T p.1)) =
      IntermediateField.adjoin (RatFunc ℂ)
        (Set.range fun p : ℂ × ℕ => differentialJet p.2
          (liReflectedGammaCarrierTranslateFamily alpha p.1)) := by
  simpa [remotePassportGaugedCarrierTranslateFamily] using
    polynomialGaugedLiCarrierTranslateFamily_allJets_adjoin_eq alpha
      (remotePassportGaugePolynomial_ne_zero M α a T)

theorem remotePassportGaugedCarrier_tendstoLocallyUniformly
    {ι : Type*} [Fintype ι]
    (alpha : ℝ) (M : ι → ℕ) (α : ι → ℂ) {a : ℝ} (ha : a ≠ 0) :
    TendstoLocallyUniformly (remotePassportGaugedCarrier alpha M α a)
      (liReflectedGammaCarrier alpha) atTop := by
  have hgauge := remotePassportGauge_tendstoLocallyUniformly M α ha
  have hcarrier : Continuous (liReflectedGammaCarrier alpha) := by
    rw [continuous_iff_continuousAt]
    intro s
    exact (liReflectedGammaCarrier_analyticOnNhd alpha s (Set.mem_univ s)).continuousAt
  have hconstant : TendstoLocallyUniformly
      (fun (_ : ℝ) => liReflectedGammaCarrier alpha)
      (liReflectedGammaCarrier alpha) atTop := tendstoLocallyUniformly_const_seq _
  have hmul := hgauge.mul₀ hconstant continuous_const hcarrier
  convert hmul using 1
  · funext T s
    rfl
  · funext s
    simp

theorem remotePassportGaugedCarrier_iteratedDeriv_tendstoLocallyUniformly
    {ι : Type*} [Fintype ι]
    (alpha : ℝ) (M : ι → ℕ) (α : ι → ℂ) {a : ℝ} (ha : a ≠ 0) (j : ℕ) :
    TendstoLocallyUniformly
      (fun T => iteratedDeriv j (remotePassportGaugedCarrier alpha M α a T))
      (iteratedDeriv j (liReflectedGammaCarrier alpha)) atTop := by
  have hconvOn : TendstoLocallyUniformlyOn
      (remotePassportGaugedCarrier alpha M α a)
      (liReflectedGammaCarrier alpha) atTop Set.univ := by
    simpa [tendstoLocallyUniformlyOn_univ] using
      remotePassportGaugedCarrier_tendstoLocallyUniformly alpha M α ha
  have hcarrierDiff : Differentiable ℂ (liReflectedGammaCarrier alpha) := by
    intro s
    exact (liReflectedGammaCarrier_analyticOnNhd alpha s (Set.mem_univ s)).differentiableAt
  have hdiff : ∀ᶠ T : ℝ in atTop,
      DifferentiableOn ℂ (remotePassportGaugedCarrier alpha M α a T) Set.univ :=
    Eventually.of_forall fun T =>
      ((remotePassportGauge_differentiable M α a T).mul hcarrierDiff).differentiableOn
  have hj := iteratedDeriv_tendstoLocallyUniformlyOn_of_locallyUniform
    isOpen_univ hconvOn hdiff j
  simpa [tendstoLocallyUniformlyOn_univ] using hj

def remotePassportGaugedCarrierCompactOpen
    {ι : Type*} [Fintype ι]
    (alpha : ℝ) (M : ι → ℕ) (α : ι → ℂ) (a T : ℝ) :
    DeningerCompactOpenEntire := by
  have hdiff : Differentiable ℂ (remotePassportGaugedCarrier alpha M α a T) :=
    Complex.analyticOnNhd_univ_iff_differentiable.mp
      (remotePassportGaugedCarrier_analyticOnNhd alpha M α a T)
  exact ⟨⟨remotePassportGaugedCarrier alpha M α a T, hdiff.continuous⟩, hdiff⟩

def liReflectedGammaCarrierCompactOpen (alpha : ℝ) :
    DeningerCompactOpenEntire := by
  have hdiff : Differentiable ℂ (liReflectedGammaCarrier alpha) :=
    Complex.analyticOnNhd_univ_iff_differentiable.mp
      (liReflectedGammaCarrier_analyticOnNhd alpha)
  exact ⟨⟨liReflectedGammaCarrier alpha, hdiff.continuous⟩, hdiff⟩

theorem remotePassportGaugedCarrierCompactOpen_tendsto
    {ι : Type*} [Fintype ι]
    (alpha : ℝ) (M : ι → ℕ) (α : ι → ℂ) {a : ℝ} (ha : a ≠ 0) :
    Tendsto (remotePassportGaugedCarrierCompactOpen alpha M α a) atTop
      (nhds (liReflectedGammaCarrierCompactOpen alpha)) := by
  rw [tendsto_subtype_rng]
  apply ContinuousMap.tendsto_iff_tendstoLocallyUniformly.mpr
  simpa [remotePassportGaugedCarrierCompactOpen,
    liReflectedGammaCarrierCompactOpen] using
      remotePassportGaugedCarrier_tendstoLocallyUniformly alpha M α ha

theorem eventually_remotePassportGaugedCarrier_finite_continuous_probes_pos
    {ι κ : Type*} [Fintype ι] [Finite κ]
    (alpha : ℝ) (M : ι → ℕ) (α : ι → ℂ) {a : ℝ} (ha : a ≠ 0)
    (Phi : κ → DeningerCompactOpenEntire → ℝ)
    (hPhi : ∀ k, Continuous (Phi k))
    (hpos : ∀ k, 0 < Phi k (liReflectedGammaCarrierCompactOpen alpha)) :
    ∀ᶠ T : ℝ in atTop, ∀ k,
      0 < Phi k (remotePassportGaugedCarrierCompactOpen alpha M α a T) := by
  rw [Filter.eventually_all]
  intro k
  have htendsto : Tendsto
      (fun T => Phi k (remotePassportGaugedCarrierCompactOpen alpha M α a T))
      atTop (nhds (Phi k (liReflectedGammaCarrierCompactOpen alpha))) :=
    ((hPhi k).tendsto _).comp
      (remotePassportGaugedCarrierCompactOpen_tendsto alpha M α ha)
  exact htendsto.eventually (isOpen_Ioi.mem_nhds (hpos k))

def liInverseKernel (n : ℕ) (u : ℂ) : ℂ :=
  1 - (1 - u) ^ n

def polynomialInverseRootSum (g : ℂ → ℂ) (P : Polynomial ℂ) : ℂ :=
  (P.roots.map fun rho => g rho⁻¹).sum

def polynomialLiContribution (n : ℕ) (P : Polynomial ℂ) : ℂ :=
  polynomialInverseRootSum (liInverseKernel n) P

theorem norm_multiset_sum_map_le_card_mul
    {β : Type*} (s : Multiset β) (f : β → ℂ) (C : ℝ)
    (hf : ∀ x ∈ s, ‖f x‖ ≤ C) :
    ‖(s.map f).sum‖ ≤ (s.card : ℝ) * C := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons x s ih =>
      rw [Multiset.map_cons, Multiset.sum_cons, Multiset.card_cons, Nat.cast_add, Nat.cast_one]
      calc
        ‖f x + (s.map f).sum‖ ≤ ‖f x‖ + ‖(s.map f).sum‖ := norm_add_le _ _
        _ ≤ C + (s.card : ℝ) * C := add_le_add (hf x (by simp))
          (ih fun y hy => hf y (by simp [hy]))
        _ = ((s.card : ℝ) + 1) * C := by ring

theorem polynomialInverseRootSum_tendsto_zero_of_escape
    {P : ℝ → Polynomial ℂ} (hP : ∀ T, P T ≠ 0) (D : ℕ)
    (hdegree : ∀ T, (P T).natDegree ≤ D)
    (hescape : ∀ R : ℝ, 0 < R →
      ∀ᶠ T : ℝ in atTop, ∀ rho ∈ Metric.closedBall (0 : ℂ) R,
        (P T).eval rho ≠ 0)
    (g : ℂ → ℂ) (hg : ContinuousAt g 0) (hg0 : g 0 = 0) :
    Tendsto (fun T => polynomialInverseRootSum g (P T)) atTop (nhds 0) := by
  rw [Metric.tendsto_nhds]
  intro epsilon hepsilon
  let C : ℝ := epsilon / (D + 1)
  have hC : 0 < C := by
    dsimp [C]
    positivity
  obtain ⟨delta, hdelta, hdeltaKernel⟩ :=
    (Metric.continuousAt_iff.mp hg) C hC
  let R : ℝ := delta⁻¹
  have hR : 0 < R := inv_pos.mpr hdelta
  filter_upwards [hescape R hR] with T hT
  let Q := P T
  have hrootBound : ∀ rho ∈ Q.roots,
      ‖g rho⁻¹‖ ≤ C := by
    intro rho hrho
    have hQ : Q ≠ 0 := hP T
    have hroot : Q.eval rho = 0 := (Polynomial.mem_roots hQ).mp hrho
    have hnotmem : rho ∉ Metric.closedBall (0 : ℂ) R := by
      intro hrhoBall
      exact (hT rho hrhoBall) hroot
    have hnormgt : R < ‖rho‖ := by
      have hnotle : ¬ ‖rho‖ ≤ R := by
        intro hle
        apply hnotmem
        simpa only [Metric.mem_closedBall, dist_zero_right] using hle
      exact lt_of_not_ge hnotle
    have hnormpos : 0 < ‖rho‖ := hR.trans hnormgt
    have hinvnorm : ‖rho⁻¹‖ < delta := by
      rw [norm_inv, inv_lt_comm₀ hnormpos hdelta]
      exact hnormgt
    have hnear : dist rho⁻¹ 0 < delta := by
      simpa only [dist_zero_right] using hinvnorm
    have hk := hdeltaKernel hnear
    rw [hg0, dist_zero_right] at hk
    exact hk.le
  have hsum := norm_multiset_sum_map_le_card_mul Q.roots
    (fun rho => g rho⁻¹) C hrootBound
  have hcardNat : Q.roots.card ≤ D :=
    (Polynomial.card_roots' Q).trans (hdegree T)
  have hcardReal : (Q.roots.card : ℝ) ≤ D := by exact_mod_cast hcardNat
  have hsumD : ‖polynomialInverseRootSum g Q‖ ≤ (D : ℝ) * C :=
    hsum.trans (mul_le_mul_of_nonneg_right hcardReal hC.le)
  have hratio : (D : ℝ) / (D + 1) < 1 := by
    rw [div_lt_one (by positivity)]
    norm_num
  have hD : (D : ℝ) * C < epsilon := by
    rw [show (D : ℝ) * C = epsilon * ((D : ℝ) / (D + 1)) by
      dsimp [C]
      ring]
    nlinarith
  simpa only [dist_zero_right, Q] using hsumD.trans_lt hD

theorem polynomialLiContribution_tendsto_zero_of_escape
    {P : ℝ → Polynomial ℂ} (hP : ∀ T, P T ≠ 0) (D : ℕ)
    (hdegree : ∀ T, (P T).natDegree ≤ D)
    (hescape : ∀ R : ℝ, 0 < R →
      ∀ᶠ T : ℝ in atTop, ∀ rho ∈ Metric.closedBall (0 : ℂ) R,
        (P T).eval rho ≠ 0)
    (n : ℕ) :
    Tendsto (fun T => polynomialLiContribution n (P T)) atTop (nhds 0) := by
  apply polynomialInverseRootSum_tendsto_zero_of_escape hP D hdegree hescape
    (liInverseKernel n)
  · unfold liInverseKernel
    fun_prop
  · simp [liInverseKernel]

theorem remotePassportPolynomialInverseRootSum_tendsto_zero
    {ι : Type*} [Fintype ι]
    (M : ι → ℕ) (α : ι → ℂ) {a : ℝ} (ha : a ≠ 0)
    (g : ℂ → ℂ) (hg : ContinuousAt g 0) (hg0 : g 0 = 0) :
    Tendsto (fun T => polynomialInverseRootSum g
      (remotePassportGaugePolynomial M α a T)) atTop (nhds 0) := by
  apply polynomialInverseRootSum_tendsto_zero_of_escape
    (fun T => remotePassportGaugePolynomial_ne_zero M α a T)
    ((remotePassportPolynomial M α).natDegree + 2)
    (fun T => remotePassportGaugePolynomial_natDegree_le M α a T)
  · intro R hR
    have hzeroFree := eventually_remotePassportGauge_ne_zero_on_compact
      M α ha (Metric.closedBall (0 : ℂ) R) (isCompact_closedBall (0 : ℂ) R)
    filter_upwards [hzeroFree] with T hT
    intro rho hrho
    rw [remotePassportGaugePolynomial_eval]
    exact hT rho hrho
  · exact hg
  · exact hg0

theorem remotePassportPolynomialLiContribution_tendsto_zero
    {ι : Type*} [Fintype ι]
    (M : ι → ℕ) (α : ι → ℂ) {a : ℝ} (ha : a ≠ 0) (n : ℕ) :
    Tendsto (fun T => polynomialLiContribution n
      (remotePassportGaugePolynomial M α a T)) atTop (nhds 0) := by
  change Tendsto (fun T => polynomialInverseRootSum (liInverseKernel n)
    (remotePassportGaugePolynomial M α a T)) atTop (nhds 0)
  apply remotePassportPolynomialInverseRootSum_tendsto_zero M α ha
  · unfold liInverseKernel
    fun_prop
  · simp [liInverseKernel]

def remotePassportGaugedCarrierLiCoefficient
    {ι : Type*} [Fintype ι]
    (alpha : ℝ) (n : ℕ) (M : ι → ℕ) (α : ι → ℂ) (a T : ℝ) : ℝ :=
  liReflectedGammaCarrierCoefficient alpha n +
    (polynomialLiContribution n (remotePassportGaugePolynomial M α a T)).re

theorem remotePassportGaugedCarrierLiCoefficient_tendsto
    {ι : Type*} [Fintype ι]
    (alpha : ℝ) (n : ℕ) (M : ι → ℕ) (α : ι → ℂ) {a : ℝ} (ha : a ≠ 0) :
    Tendsto (remotePassportGaugedCarrierLiCoefficient alpha n M α a) atTop
      (nhds (liReflectedGammaCarrierCoefficient alpha n)) := by
  have hli := remotePassportPolynomialLiContribution_tendsto_zero M α ha n
  have hre : Tendsto (fun T =>
      (polynomialLiContribution n (remotePassportGaugePolynomial M α a T)).re)
      atTop (nhds 0) :=
    ((Complex.continuous_re.tendsto 0).comp hli).congr'
      (Eventually.of_forall fun _ => rfl)
  change Tendsto (fun T => liReflectedGammaCarrierCoefficient alpha n +
    (polynomialLiContribution n (remotePassportGaugePolynomial M α a T)).re)
    atTop (nhds (liReflectedGammaCarrierCoefficient alpha n))
  simpa using tendsto_const_nhds.add hre

theorem eventually_remotePassportGaugedCarrierLiCoefficient_pos_prefix
    {ι : Type*} [Fintype ι]
    {alpha : ℝ} (halpha : 0 < alpha) (N : ℕ)
    (M : ι → ℕ) (α : ι → ℂ) {a : ℝ} (ha : a ≠ 0) :
    ∀ᶠ T : ℝ in atTop, ∀ n : Fin N,
      0 < remotePassportGaugedCarrierLiCoefficient alpha (n + 1) M α a T := by
  rw [Filter.eventually_all]
  intro n
  have hlim := remotePassportGaugedCarrierLiCoefficient_tendsto
    alpha (n + 1) M α ha
  exact hlim.eventually (isOpen_Ioi.mem_nhds
    (liReflectedGammaCarrierCoefficient_pos halpha (by omega)))

end
end RHTower
