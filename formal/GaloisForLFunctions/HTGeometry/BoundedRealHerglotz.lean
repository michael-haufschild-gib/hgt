import GaloisForLFunctions.HTGeometry.HardyDiskRadialPointwise
import GaloisForLFunctions.HTGeometry.PrimePoissonProductState
import GaloisForLFunctions.HTGeometry.CircleRieszFischerFourier

/-!
# Herglotz transforms of bounded real circle data

This file constructs the analytic Herglotz transform of arbitrary bounded measurable real data
as an actual `HardyDisk` vector.  Its Taylor coefficients are the nonnegative Fourier coefficients,
with the standard doubled normalization away from the constant mode.
-/

open MeasureTheory Filter Topology Complex
open scoped ENNReal NNReal lp

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- A bounded measurable real function on the circle, regarded as a circle `L²` vector. -/
def boundedRealCircleLp (b : Circle → ℝ) (hb : Measurable b) (M : ℝ)
    (hM : ∀ z, |b z| ≤ M) : Lp ℂ 2 circleLebesgue :=
  (MemLp.of_bound
    ((Complex.continuous_ofReal.measurable.comp hb).aestronglyMeasurable) M
    (Filter.Eventually.of_forall fun z => by simpa using hM z)).toLp
      (fun z => (b z : ℂ))

theorem boundedRealCircleLp_coeFn_ae (b : Circle → ℝ) (hb : Measurable b) (M : ℝ)
    (hM : ∀ z, |b z| ≤ M) :
    ⇑(boundedRealCircleLp b hb M hM) =ᵐ[circleLebesgue] fun z => (b z : ℂ) :=
  (MemLp.of_bound
    ((Complex.continuous_ofReal.measurable.comp hb).aestronglyMeasurable) M
    (Filter.Eventually.of_forall fun z => by simpa using hM z)).coeFn_toLp

/-- Full Fourier coordinate sequence of bounded real data. -/
def boundedRealCircleFourier (b : Circle → ℝ) (hb : Measurable b) (M : ℝ)
    (hM : ∀ z, |b z| ≤ M) : lp (fun _ : ℤ => ℂ) 2 :=
  fourierBasis.repr
    (circleLpAddCircleLinearIsometryEquiv (boundedRealCircleLp b hb M hM))

theorem boundedRealCircleFourier_eq_inner
    (b : Circle → ℝ) (hb : Measurable b) (M : ℝ)
    (hM : ∀ z, |b z| ≤ M) (k : ℤ) :
    boundedRealCircleFourier b hb M hM k =
      inner ℂ (circleZMonomialLp circleLebesgue k)
        (boundedRealCircleLp b hb M hM) := by
  rw [boundedRealCircleFourier, HilbertBasis.repr_apply_apply]
  let U := circleLpAddCircleLinearIsometryEquiv
  calc
    inner ℂ (fourierBasis k)
        (U (boundedRealCircleLp b hb M hM)) =
      inner ℂ (U (circleZMonomialLp circleLebesgue k))
        (U (boundedRealCircleLp b hb M hM)) := by
          congr 1
          simpa [U, circleLpAddCircleLinearIsometryEquiv] using
            (circleLpToAddCircleLinearIsometry_circleZMonomial k).symm
    _ = inner ℂ (circleZMonomialLp circleLebesgue k)
        (boundedRealCircleLp b hb M hM) := U.inner_map_map _ _

theorem boundedRealCircleFourier_eq_integral
    (b : Circle → ℝ) (hb : Measurable b) (M : ℝ)
    (hM : ∀ z, |b z| ≤ M) (k : ℤ) :
    boundedRealCircleFourier b hb M hM k =
      ∫ z : Circle, (b z : ℂ) * (starRingEnd ℂ) ((z : ℂ) ^ k)
        ∂circleLebesgue := by
  rw [boundedRealCircleFourier_eq_inner,
    circleZMonomialLp_inner]
  apply integral_congr_ae
  filter_upwards [boundedRealCircleLp_coeFn_ae b hb M hM] with z hz
  rw [hz]

/-- Taylor coefficients of the analytic Herglotz transform: constant Fourier mode at zero and
twice the positive Fourier mode thereafter. -/
def boundedRealHerglotzCoeff (b : Circle → ℝ) (hb : Measurable b) (M : ℝ)
    (hM : ∀ z, |b z| ≤ M) (n : ℕ) : ℂ :=
  if n = 0 then boundedRealCircleFourier b hb M hM 0
  else 2 * boundedRealCircleFourier b hb M hM (n : ℤ)

theorem memℓp_boundedRealHerglotzCoeff
    (b : Circle → ℝ) (hb : Measurable b) (M : ℝ)
    (hM : ∀ z, |b z| ≤ M) :
    Memℓp (boundedRealHerglotzCoeff b hb M hM) 2 := by
  let a := boundedRealCircleFourier b hb M hM
  have hbase : Memℓp (fun n : ℕ => a (n : ℤ)) 2 := by
    rw [memℓp_gen_iff (by norm_num)]
    have hall := lp.memℓp a
    rw [memℓp_gen_iff (by norm_num)] at hall
    simpa [Function.comp_def] using hall.comp_injective Int.ofNat_injective
  have hdouble : Memℓp (fun n : ℕ => (2 : ℂ) * a (n : ℤ)) 2 :=
    hbase.const_mul 2
  exact hdouble.mono' fun n => by
    rw [boundedRealHerglotzCoeff]
    by_cases hn : n = 0
    · subst n
      simp only [if_pos]
      change ‖a 0‖ ≤ ‖(2 : ℂ) * a 0‖
      rw [norm_mul]
      norm_num
      have ha0 : 0 ≤ ‖a 0‖ := norm_nonneg (a 0)
      linarith
    · simp only [if_neg hn]
      rfl

/-- Hardy-disk Herglotz transform of bounded measurable real circle data. -/
def boundedRealHerglotzHardy (b : Circle → ℝ) (hb : Measurable b) (M : ℝ)
    (hM : ∀ z, |b z| ≤ M) : HardyDisk :=
  ⟨boundedRealHerglotzCoeff b hb M hM,
    memℓp_boundedRealHerglotzCoeff b hb M hM⟩

@[simp] theorem boundedRealHerglotzHardy_apply
    (b : Circle → ℝ) (hb : Measurable b) (M : ℝ)
    (hM : ∀ z, |b z| ≤ M) (n : ℕ) :
    boundedRealHerglotzHardy b hb M hM n =
      boundedRealHerglotzCoeff b hb M hM n := rfl

/-! ## The analytic Herglotz kernel -/

/-- Standard analytic Herglotz kernel on the unit circle. -/
def circleHerglotzKernel (w : ℂ) (z : Circle) : ℂ :=
  ((z : ℂ) + w) / ((z : ℂ) - w)

/-- Taylor terms of the Herglotz kernel. -/
def circleHerglotzSeriesTerm (w : ℂ) (n : ℕ) (z : Circle) : ℂ :=
  if n = 0 then 1
  else 2 * w ^ n * (starRingEnd ℂ) ((z : ℂ) ^ n)

theorem summable_circleHerglotzSeriesTerm {w : ℂ} (hw : ‖w‖ < 1) (z : Circle) :
    Summable fun n => circleHerglotzSeriesTerm w n z := by
  apply Summable.of_norm_bounded
    ((summable_geometric_of_lt_one (norm_nonneg w) hw).mul_left 2)
  intro n
  rw [circleHerglotzSeriesTerm]
  by_cases hn : n = 0
  · subst n
    norm_num
  · rw [if_neg hn, norm_mul, norm_mul, norm_pow, map_pow, norm_pow,
      Complex.norm_conj, Circle.norm_coe]
    simp

theorem tsum_circleHerglotzSeriesTerm_eq {w : ℂ} (hw : ‖w‖ < 1) (z : Circle) :
    (∑' n, circleHerglotzSeriesTerm w n z) = circleHerglotzKernel w z := by
  let x : ℂ := w * (starRingEnd ℂ) (z : ℂ)
  have hxnorm : ‖x‖ < 1 := by
    change ‖w * (starRingEnd ℂ) (z : ℂ)‖ < 1
    rw [norm_mul, Complex.norm_conj, Circle.norm_coe, mul_one]
    exact hw
  have htail : (∑' n : ℕ, circleHerglotzSeriesTerm w (n + 1) z) =
      2 * x * (1 - x)⁻¹ := by
    have hgeom := (hasSum_geometric_of_norm_lt_one hxnorm).mul_left (2 * x)
    calc
      (∑' n : ℕ, circleHerglotzSeriesTerm w (n + 1) z) =
          ∑' n : ℕ, 2 * x * x ^ n := by
            apply tsum_congr
            intro n
            rw [circleHerglotzSeriesTerm, if_neg (Nat.succ_ne_zero n)]
            simp only [map_pow]
            change 2 * w ^ (n + 1) * ((starRingEnd ℂ) (z : ℂ)) ^ (n + 1) =
              2 * (w * (starRingEnd ℂ) (z : ℂ)) *
                (w * (starRingEnd ℂ) (z : ℂ)) ^ n
            rw [mul_pow, pow_succ', pow_succ']
            ring
      _ = 2 * x * (1 - x)⁻¹ := hgeom.tsum_eq
  have hsplit := (summable_circleHerglotzSeriesTerm hw z).sum_add_tsum_nat_add 1
  have hhead : ∑ i ∈ Finset.range 1, circleHerglotzSeriesTerm w i z = 1 := by
    simp [circleHerglotzSeriesTerm]
  rw [hhead, htail] at hsplit
  rw [← hsplit]
  rw [circleHerglotzKernel]
  have hz : (z : ℂ) ≠ 0 := by simp
  have hzw : (z : ℂ) - w ≠ 0 := by
    intro hzero
    have heq : (z : ℂ) = w := sub_eq_zero.mp hzero
    have := hw
    rw [← heq, Circle.norm_coe] at this
    exact (lt_irrefl 1) this
  dsimp [x]
  rw [← Complex.inv_eq_conj (Circle.norm_coe z)]
  field_simp [hz, hzw]
  ring

theorem circleHerglotzKernel_re {w : ℂ} (hw : ‖w‖ < 1) (z : Circle) :
    (circleHerglotzKernel w z).re = poissonKernel 0 w (z : ℂ) := by
  rw [circleHerglotzKernel, Complex.div_re, poissonKernel_def]
  have hnormz : Complex.normSq (z : ℂ) = 1 := by
    rw [← Complex.sq_norm, Circle.norm_coe]
    norm_num
  simp only [sub_zero]
  rw [show ‖(z : ℂ)‖ ^ 2 = Complex.normSq (z : ℂ) by
      exact Complex.sq_norm (z : ℂ),
    show ‖w‖ ^ 2 = Complex.normSq w by exact Complex.sq_norm w,
    show ‖(z : ℂ) - w‖ ^ 2 = Complex.normSq ((z : ℂ) - w) by
      exact Complex.sq_norm ((z : ℂ) - w)]
  rw [← add_div]
  congr 1
  simp only [Complex.normSq_apply] at hnormz ⊢
  simp only [Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im]
  nlinarith

theorem integral_boundedReal_mul_circleHerglotzSeriesTerm
    (b : Circle → ℝ) (hb : Measurable b) (M : ℝ)
    (hM : ∀ z, |b z| ≤ M) (w : ℂ) (n : ℕ) :
    (∫ z : Circle, (b z : ℂ) * circleHerglotzSeriesTerm w n z
        ∂circleLebesgue) =
      boundedRealHerglotzCoeff b hb M hM n * w ^ n := by
  by_cases hn : n = 0
  · subst n
    rw [boundedRealHerglotzCoeff, if_pos rfl,
      boundedRealCircleFourier_eq_integral]
    simp [circleHerglotzSeriesTerm]
  · rw [boundedRealHerglotzCoeff, if_neg hn,
      boundedRealCircleFourier_eq_integral]
    simp only [circleHerglotzSeriesTerm, if_neg hn]
    simp only [map_pow]
    calc
      (∫ z : Circle,
          (b z : ℂ) * (2 * w ^ n * ((starRingEnd ℂ) (z : ℂ)) ^ n)
            ∂circleLebesgue) =
          ∫ z : Circle, (2 * w ^ n) *
            ((b z : ℂ) * (starRingEnd ℂ) ((z : ℂ) ^ (n : ℤ)))
              ∂circleLebesgue := by
                apply integral_congr_ae
                filter_upwards with z
                norm_num
                ring
      _ = (2 * w ^ n) *
          ∫ z : Circle, (b z : ℂ) *
            (starRingEnd ℂ) ((z : ℂ) ^ (n : ℤ)) ∂circleLebesgue := by
              rw [integral_const_mul]
      _ = (2 *
          ∫ z : Circle, (b z : ℂ) *
            (starRingEnd ℂ) ((z : ℂ) ^ (n : ℤ)) ∂circleLebesgue) * w ^ n := by
              ring

theorem norm_circleHerglotzSeriesTerm_le {w : ℂ} (hw : ‖w‖ < 1)
    (n : ℕ) (z : Circle) :
    ‖circleHerglotzSeriesTerm w n z‖ ≤ 2 * ‖w‖ ^ n := by
  rw [circleHerglotzSeriesTerm]
  by_cases hn : n = 0
  · subst n
    norm_num
  · rw [if_neg hn, norm_mul, norm_mul, norm_pow, map_pow, norm_pow,
      Complex.norm_conj, Circle.norm_coe]
    simp

/-- The coefficient-defined Hardy function is the literal Herglotz integral. -/
theorem hardyFun_boundedRealHerglotzHardy_eq_integral
    (b : Circle → ℝ) (hb : Measurable b) (M : ℝ)
    (hM : ∀ z, |b z| ≤ M) {w : ℂ} (hw : ‖w‖ < 1) :
    hardyFun (boundedRealHerglotzHardy b hb M hM) w =
      ∫ z : Circle, (b z : ℂ) * circleHerglotzKernel w z
        ∂circleLebesgue := by
  let F : ℕ → Circle → ℂ := fun n z =>
    (b z : ℂ) * circleHerglotzSeriesTerm w n z
  have hMnonneg : 0 ≤ M := by
    exact le_trans (abs_nonneg (b (1 : Circle))) (hM 1)
  have hFmeas : ∀ n, AEStronglyMeasurable (F n) circleLebesgue := by
    intro n
    have hterm : Measurable fun z : Circle => circleHerglotzSeriesTerm w n z := by
      simp only [circleHerglotzSeriesTerm]
      split_ifs <;> fun_prop
    exact ((Complex.continuous_ofReal.measurable.comp hb).mul hterm).aestronglyMeasurable
  have hFbound : ∀ n, ∀ z, ‖F n z‖ ≤ 2 * M * ‖w‖ ^ n := by
    intro n z
    change ‖(b z : ℂ) * circleHerglotzSeriesTerm w n z‖ ≤ _
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc
      |b z| * ‖circleHerglotzSeriesTerm w n z‖ ≤
          M * (2 * ‖w‖ ^ n) :=
        mul_le_mul (hM z) (norm_circleHerglotzSeriesTerm_le hw n z)
          (norm_nonneg _) hMnonneg
      _ = 2 * M * ‖w‖ ^ n := by ring
  have hFint : ∀ n, Integrable (F n) circleLebesgue := by
    intro n
    exact Integrable.of_bound (hFmeas n) (2 * M * ‖w‖ ^ n)
      (Filter.Eventually.of_forall (hFbound n))
  have hnormIntLe : ∀ n,
      (∫ z : Circle, ‖F n z‖ ∂circleLebesgue) ≤ 2 * M * ‖w‖ ^ n := by
    intro n
    calc
      (∫ z : Circle, ‖F n z‖ ∂circleLebesgue) ≤
          ∫ _z : Circle, 2 * M * ‖w‖ ^ n ∂circleLebesgue := by
            exact integral_mono (hFint n).norm (integrable_const _)
              (hFbound n)
      _ = 2 * M * ‖w‖ ^ n := by simp
  have hnormIntSum : Summable fun n =>
      ∫ z : Circle, ‖F n z‖ ∂circleLebesgue := by
    apply Summable.of_nonneg_of_le
    · intro n
      exact integral_nonneg fun _ => norm_nonneg _
    · exact hnormIntLe
    · exact (summable_geometric_of_lt_one (norm_nonneg w) hw).mul_left (2 * M)
  have hinterchange := integral_tsum_of_summable_integral_norm hFint hnormIntSum
  have hpoint : ∀ z : Circle, (∑' n, F n z) =
      (b z : ℂ) * circleHerglotzKernel w z := by
    intro z
    have hs := (summable_circleHerglotzSeriesTerm hw z).hasSum.mul_left (b z : ℂ)
    rw [tsum_circleHerglotzSeriesTerm_eq hw z] at hs
    exact hs.tsum_eq
  rw [hardyFun]
  calc
    (∑' n, (boundedRealHerglotzHardy b hb M hM : ℕ → ℂ) n * w ^ n) =
        ∑' n, ∫ z : Circle, F n z ∂circleLebesgue := by
          apply tsum_congr
          intro n
          exact (integral_boundedReal_mul_circleHerglotzSeriesTerm
            b hb M hM w n).symm
    _ = ∫ z : Circle, ∑' n, F n z ∂circleLebesgue := hinterchange
    _ = ∫ z : Circle, (b z : ℂ) * circleHerglotzKernel w z
          ∂circleLebesgue := by
            apply integral_congr_ae
            exact Filter.Eventually.of_forall hpoint

/-! ## Pointwise conjugation and real part in circle `L²` -/

/-- Pointwise complex conjugation of a circle `L²` vector. -/
def circleLpConj (f : Lp ℂ 2 circleLebesgue) : Lp ℂ 2 circleLebesgue :=
  ((Lp.memLp f).mono
    (Complex.continuous_conj.comp_aestronglyMeasurable
      (Lp.aestronglyMeasurable f))
    (Filter.Eventually.of_forall fun z => by simp)).toLp
      (fun z => (starRingEnd ℂ) ((f : Circle → ℂ) z))

theorem circleLpConj_coeFn_ae (f : Lp ℂ 2 circleLebesgue) :
    ⇑(circleLpConj f) =ᵐ[circleLebesgue]
      fun z => (starRingEnd ℂ) ((f : Circle → ℂ) z) :=
  ((Lp.memLp f).mono
    (Complex.continuous_conj.comp_aestronglyMeasurable
      (Lp.aestronglyMeasurable f))
    (Filter.Eventually.of_forall fun z => by simp)).coeFn_toLp

/-- Pointwise complexified real part of a circle `L²` vector. -/
def circleLpRealPart (f : Lp ℂ 2 circleLebesgue) : Lp ℂ 2 circleLebesgue :=
  (2 : ℂ)⁻¹ • (f + circleLpConj f)

theorem circleLpRealPart_coeFn_ae (f : Lp ℂ 2 circleLebesgue) :
    ⇑(circleLpRealPart f) =ᵐ[circleLebesgue]
      fun z => (((f : Circle → ℂ) z).re : ℂ) := by
  filter_upwards [Lp.coeFn_smul (2 : ℂ)⁻¹ (f + circleLpConj f),
    Lp.coeFn_add f (circleLpConj f), circleLpConj_coeFn_ae f]
      with z hsmul hadd hconj
  rw [circleLpRealPart]
  calc
    ⇑((2 : ℂ)⁻¹ • (f + circleLpConj f)) z =
        (2 : ℂ)⁻¹ * ⇑(f + circleLpConj f) z := by
          simpa [Pi.smul_apply, smul_eq_mul] using hsmul
    _ = (2 : ℂ)⁻¹ *
        (((f : Circle → ℂ) z) + (starRingEnd ℂ) ((f : Circle → ℂ) z)) := by
          rw [hadd]
          simp only [Pi.add_apply]
          rw [hconj]
    _ = (((f : Circle → ℂ) z).re : ℂ) := by
          apply Complex.ext <;> norm_num <;> ring

theorem circle_conj_zpow (z : Circle) (k : ℤ) :
    (starRingEnd ℂ) ((z : ℂ) ^ k) = (z : ℂ) ^ (-k) := by
  rw [map_zpow₀, ← Complex.inv_eq_conj (Circle.norm_coe z),
    inv_zpow, ← zpow_neg]

theorem circleZMonomialLp_inner_circleLpConj
    (f : Lp ℂ 2 circleLebesgue) (k : ℤ) :
    inner ℂ (circleZMonomialLp circleLebesgue k) (circleLpConj f) =
      (starRingEnd ℂ)
        (inner ℂ (circleZMonomialLp circleLebesgue (-k)) f) := by
  rw [circleZMonomialLp_inner, circleZMonomialLp_inner, ← integral_conj]
  apply integral_congr_ae
  filter_upwards [circleLpConj_coeFn_ae f] with z hz
  rw [hz]
  simp only [map_mul, starRingEnd_self_apply]
  rw [circle_conj_zpow]

theorem circleZMonomialLp_inner_circleLpRealPart
    (f : Lp ℂ 2 circleLebesgue) (k : ℤ) :
    inner ℂ (circleZMonomialLp circleLebesgue k) (circleLpRealPart f) =
      (2 : ℂ)⁻¹ *
        (inner ℂ (circleZMonomialLp circleLebesgue k) f +
          (starRingEnd ℂ)
            (inner ℂ (circleZMonomialLp circleLebesgue (-k)) f)) := by
  rw [circleLpRealPart, inner_smul_right, inner_add_right,
    circleZMonomialLp_inner_circleLpConj]

theorem boundedRealCircleFourier_neg
    (b : Circle → ℝ) (hb : Measurable b) (M : ℝ)
    (hM : ∀ z, |b z| ≤ M) (k : ℤ) :
    boundedRealCircleFourier b hb M hM (-k) =
      (starRingEnd ℂ) (boundedRealCircleFourier b hb M hM k) := by
  rw [boundedRealCircleFourier_eq_integral,
    boundedRealCircleFourier_eq_integral, ← integral_conj]
  apply integral_congr_ae
  filter_upwards with z
  rw [circle_conj_zpow]
  simp only [map_mul, starRingEnd_self_apply, map_ofNat]
  simp

/-- Laurent monomials are total in circle `L²`. -/
theorem circleLp_ext_of_circleZMonomial_inner_eq
    {f g : Lp ℂ 2 circleLebesgue}
    (h : ∀ k : ℤ,
      inner ℂ (circleZMonomialLp circleLebesgue k) f =
        inner ℂ (circleZMonomialLp circleLebesgue k) g) :
    f = g := by
  let U := circleLpAddCircleLinearIsometryEquiv
  apply U.injective
  apply fourierBasis.repr.injective
  apply lp.ext
  funext k
  rw [HilbertBasis.repr_apply_apply, HilbertBasis.repr_apply_apply]
  rw [show fourierBasis k = U (circleZMonomialLp circleLebesgue k) by
    simpa [U, circleLpAddCircleLinearIsometryEquiv] using
      (circleLpToAddCircleLinearIsometry_circleZMonomial k).symm]
  rw [U.inner_map_map, U.inner_map_map]
  exact h k

@[simp] theorem nonnegativeIntExtension_boundedRealHerglotzHardy_ofNat
    (b : Circle → ℝ) (hb : Measurable b) (M : ℝ)
    (hM : ∀ z, |b z| ≤ M) (n : ℕ) :
    nonnegativeIntExtension
        (↑(boundedRealHerglotzHardy b hb M hM) : ℕ → ℂ) (n : ℤ) =
      boundedRealHerglotzCoeff b hb M hM n := by
  change nonnegativeIntExtension (boundedRealHerglotzCoeff b hb M hM) (n : ℤ) = _
  rw [nonnegativeIntExtension_ofNat]

@[simp] theorem nonnegativeIntExtension_boundedRealHerglotzHardy_negSucc
    (b : Circle → ℝ) (hb : Measurable b) (M : ℝ)
    (hM : ∀ z, |b z| ≤ M) (n : ℕ) :
    nonnegativeIntExtension
        (↑(boundedRealHerglotzHardy b hb M hM) : ℕ → ℂ) (Int.negSucc n) = 0 := by
  change nonnegativeIntExtension (boundedRealHerglotzCoeff b hb M hM) (Int.negSucc n) = 0
  rw [nonnegativeIntExtension_negSucc]

/-- The `L²` boundary real part of the Herglotz transform is exactly its prescribed real
circle datum. -/
theorem circleLpRealPart_hardyDiskBoundary_boundedRealHerglotz
    (b : Circle → ℝ) (hb : Measurable b) (M : ℝ)
    (hM : ∀ z, |b z| ≤ M) :
    circleLpRealPart (hardyDiskBoundary (boundedRealHerglotzHardy b hb M hM)) =
      boundedRealCircleLp b hb M hM := by
  let a : ℤ → ℂ := fun k => boundedRealCircleFourier b hb M hM k
  let c : ℕ → ℂ := fun n => if n = 0 then a 0 else 2 * a (n : ℤ)
  have ha_neg (j : ℤ) : a (-j) = (starRingEnd ℂ) (a j) := by
    exact boundedRealCircleFourier_neg b hb M hM j
  apply circleLp_ext_of_circleZMonomial_inner_eq
  intro k
  rw [circleZMonomialLp_inner_circleLpRealPart,
    hardyDiskBoundary_apply,
    circleZMonomialLp_inner_circleRieszFischerOfNat,
    circleZMonomialLp_inner_circleRieszFischerOfNat,
    ← boundedRealCircleFourier_eq_inner]
  change (2 : ℂ)⁻¹ *
      (nonnegativeIntExtension c k +
        (starRingEnd ℂ)
          (nonnegativeIntExtension c (-k))) = a k
  cases k with
  | ofNat n =>
      cases n with
      | zero =>
          have hzero := ha_neg 0
          simp only [neg_zero] at hzero
          have hzero_nonneg : (0 : ℤ) ≤ Int.ofNat 0 := Int.ofNat_zero_le 0
          simp [nonnegativeIntExtension, hzero_nonneg, c]
          rw [← hzero]
          ring
      | succ n =>
          have hn : (0 : ℤ) ≤ (n : ℤ) := Int.ofNat_zero_le n
          have hleft : (0 : ℤ) ≤ 1 + (n : ℤ) := by omega
          have hright : ¬ (n : ℤ) ≤ -1 := by omega
          simp [nonnegativeIntExtension, c, hleft, hright]
          intro hbad
          omega
  | negSucc n =>
      have hneg : a (Int.negSucc n) =
          (starRingEnd ℂ) (a ((n : ℤ) + 1)) := by
        have hind : Int.negSucc n = -((n + 1 : ℕ) : ℤ) := by omega
        rw [hind]
        simpa only [Nat.cast_add, Nat.cast_one] using ha_neg (n + 1 : ℕ)
      have hkneg : ¬ (0 : ℤ) ≤ Int.negSucc n :=
        not_le_of_gt (Int.negSucc_lt_zero n)
      have hkpos : (0 : ℤ) ≤ -Int.negSucc n :=
        neg_nonneg.mpr (le_of_lt (Int.negSucc_lt_zero n))
      have hn : (0 : ℤ) ≤ (n : ℤ) := Int.ofNat_zero_le n
      have hleft : (0 : ℤ) ≤ (n : ℤ) + 1 := by omega
      simp [nonnegativeIntExtension, hkneg, hkpos, c]
      rw [if_pos hleft]
      rw [hneg]
      rw [map_mul]
      rw [map_ofNat]
      norm_num
      ring

/-- Pointwise almost-everywhere boundary version of the exact Herglotz real-part identity. -/
theorem hardyDiskBoundary_boundedRealHerglotz_re_ae
    (b : Circle → ℝ) (hb : Measurable b) (M : ℝ)
    (hM : ∀ z, |b z| ≤ M) :
    ∀ᵐ z ∂circleLebesgue,
      ((hardyDiskBoundary (boundedRealHerglotzHardy b hb M hM) :
        Circle → ℂ) z).re = b z := by
  have hlp := circleLpRealPart_hardyDiskBoundary_boundedRealHerglotz b hb M hM
  filter_upwards [circleLpRealPart_coeFn_ae
      (hardyDiskBoundary (boundedRealHerglotzHardy b hb M hM)),
    boundedRealCircleLp_coeFn_ae b hb M hM] with z hreal hbval
  rw [hlp] at hreal
  calc
    ((hardyDiskBoundary (boundedRealHerglotzHardy b hb M hM) :
        Circle → ℂ) z).re =
        (((((hardyDiskBoundary (boundedRealHerglotzHardy b hb M hM) :
          Circle → ℂ) z).re : ℂ)).re) := by simp
    _ = ((boundedRealCircleLp b hb M hM : Circle → ℂ) z).re := by
      exact congrArg Complex.re hreal.symm
    _ = ((b z : ℂ)).re := by exact congrArg Complex.re hbval
    _ = b z := by simp

private theorem continuous_circleHerglotzKernel {w : ℂ} (hw : ‖w‖ < 1) :
    Continuous fun z : Circle => circleHerglotzKernel w z := by
  change Continuous fun z : Circle => ((z : ℂ) + w) / ((z : ℂ) - w)
  refine Continuous.div ?_ ?_ ?_
  · fun_prop
  · fun_prop
  · intro z
    apply sub_ne_zero.mpr
    intro hzw
    have hnorm := congrArg norm hzw
    rw [Circle.norm_coe] at hnorm
    linarith

private theorem integrable_boundedReal_mul_circleHerglotzKernel
    (b : Circle → ℝ) (hb : Measurable b) (M : ℝ)
    (hM : ∀ z, |b z| ≤ M) {w : ℂ} (hw : ‖w‖ < 1) :
    Integrable (fun z : Circle =>
      (b z : ℂ) * circleHerglotzKernel w z) circleLebesgue := by
  let K : C(Circle, ℂ) :=
    ⟨fun z => circleHerglotzKernel w z, continuous_circleHerglotzKernel hw⟩
  have hbint : Integrable (fun z : Circle => (b z : ℂ)) circleLebesgue := by
    have hbmeas := Complex.continuous_ofReal.measurable.comp hb
    change Measurable (fun z : Circle => (b z : ℂ)) at hbmeas
    exact Integrable.of_bound
      hbmeas.aestronglyMeasurable M
      (Filter.Eventually.of_forall fun z => by simpa using hM z)
  exact hbint.mul_bdd (continuous_circleHerglotzKernel hw).aestronglyMeasurable
    (Filter.Eventually.of_forall fun z => by
      simpa [K] using ContinuousMap.norm_coe_le_norm K z)

private theorem integral_circlePoissonMeasure_real_eq_local
    (a : CirclePoissonParameter) (f : Circle → ℝ) :
    ∫ z, f z ∂circlePoissonMeasure a =
      ∫ z, f z * poissonKernel 0 (a : ℂ) (z : ℂ) ∂circleLebesgue := by
  have hdens : AEMeasurable (circlePoissonDensity a) circleLebesgue :=
    (ENNReal.continuous_ofReal.comp
      (continuous_circlePoissonDensity_real a)).measurable.aemeasurable
  have hdensTop : ∀ᵐ z ∂circleLebesgue, circlePoissonDensity a z < ∞ :=
    Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
  rw [circlePoissonMeasure,
    integral_withDensity_eq_integral_toReal_smul₀ hdens hdensTop]
  apply integral_congr_ae
  filter_upwards with z
  rw [circlePoissonDensity,
    ENNReal.toReal_ofReal (circlePoissonDensity_nonneg a z)]
  simp only [smul_eq_mul]
  ring

/-- Interior real part of the coefficient-defined transform is the Poisson integral of the
prescribed datum. -/
theorem hardyFun_boundedRealHerglotzHardy_re_eq_circlePoissonIntegral
    (b : Circle → ℝ) (hb : Measurable b) (M : ℝ)
    (hM : ∀ z, |b z| ≤ M) {w : ℂ} (hw : ‖w‖ < 1) :
    (hardyFun (boundedRealHerglotzHardy b hb M hM) w).re =
      ∫ z : Circle, b z ∂(circlePoissonMeasure
        ⟨w, by simpa [Metric.mem_ball, dist_zero_right] using hw⟩) := by
  rw [hardyFun_boundedRealHerglotzHardy_eq_integral b hb M hM hw]
  have hint := integrable_boundedReal_mul_circleHerglotzKernel b hb M hM hw
  calc
    (∫ z : Circle, (b z : ℂ) * circleHerglotzKernel w z
        ∂circleLebesgue).re =
        ∫ z : Circle,
          ((b z : ℂ) * circleHerglotzKernel w z).re ∂circleLebesgue := by
            simpa only [Complex.reCLM_apply] using
              (ContinuousLinearMap.integral_comp_comm Complex.reCLM hint).symm
    _ = ∫ z : Circle,
        b z * poissonKernel 0 w (z : ℂ) ∂circleLebesgue := by
          apply integral_congr_ae
          filter_upwards with z
          rw [Complex.mul_re, circleHerglotzKernel_re hw z]
          simp
    _ = ∫ z : Circle, b z ∂(circlePoissonMeasure
        ⟨w, by simpa [Metric.mem_ball, dist_zero_right] using hw⟩) := by
          exact (integral_circlePoissonMeasure_real_eq_local
            ⟨w, by simpa [Metric.mem_ball, dist_zero_right] using hw⟩ b).symm

/-- Sharp maximum-principle strip bound inherited from bounded real boundary data. -/
theorem abs_re_hardyFun_boundedRealHerglotzHardy_le
    (b : Circle → ℝ) (hb : Measurable b) (M : ℝ)
    (hM : ∀ z, |b z| ≤ M) {w : ℂ} (hw : ‖w‖ < 1) :
    |(hardyFun (boundedRealHerglotzHardy b hb M hM) w).re| ≤ M := by
  rw [hardyFun_boundedRealHerglotzHardy_re_eq_circlePoissonIntegral b hb M hM hw]
  have hwball : w ∈ Metric.ball (0 : ℂ) 1 := by
    simpa [Metric.mem_ball, dist_zero_right] using hw
  have hbound := MeasureTheory.norm_integral_le_of_norm_le_const
    (μ := circlePoissonMeasure ⟨w, hwball⟩) (f := b)
    (Filter.Eventually.of_forall fun z => by
      simpa [Real.norm_eq_abs] using hM z)
  simpa [Real.norm_eq_abs] using hbound

end

end GaloisForLFunctions.HTGeometry
