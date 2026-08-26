import GaloisForLFunctions.HTGeometry.HardyProductConvolution
import GaloisForLFunctions.HTGeometry.L1PeriodizationFourier
import GaloisForLFunctions.HTGeometry.HardyArcGluing
import Mathlib.Analysis.Normed.Ring.InfiniteSum

open Complex Filter MeasureTheory Metric Set Topology Finset
open scoped ENNReal NNReal lp

namespace GaloisForLFunctions.HTGeometry

noncomputable section

def circleL1CauchyTransform (f : Circle → ℂ) (z : ℂ) : ℂ :=
  ∫ ζ : Circle, f ζ * ((ζ : ℂ) / ((ζ : ℂ) - z)) ∂circleLebesgue

private theorem integral_tsum_of_summable_integral_norm
    {α E ι : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [Countable ι] {μ : Measure α} {F : ι → α → E}
    (hF_int : ∀ i, Integrable (F i) μ)
    (hF_sum : Summable fun i => ∫ x, ‖F i x‖ ∂μ) :
    ∫ x, ∑' i, F i x ∂μ = ∑' i, ∫ x, F i x ∂μ := by
  apply MeasureTheory.integral_tsum
  · exact fun i => (hF_int i).aestronglyMeasurable
  · have hi (i : ι) :
        (∫⁻ x, ‖F i x‖ₑ ∂μ) = ‖∫ x, ‖F i x‖ ∂μ‖ₑ := by
      dsimp only [enorm]
      rw [lintegral_coe_eq_integral _ (hF_int i).norm, ENNReal.coe_nnreal_eq,
        coe_nnnorm, Real.norm_of_nonneg (integral_nonneg fun x => norm_nonneg (F i x))]
      simp only [coe_nnnorm]
    rw [funext hi]
    exact ENNReal.tsum_coe_ne_top_iff_summable.2
      (NNReal.summable_coe.1 hF_sum.abs)

private theorem circle_geometric_kernel_tsum (z : ℂ) (hz : ‖z‖ < 1)
    (ζ : Circle) :
    (∑' n : ℕ, z ^ n * (starRingEnd ℂ) ((ζ : ℂ) ^ n)) =
      (ζ : ℂ) / ((ζ : ℂ) - z) := by
  have hunit : (starRingEnd ℂ) (ζ : ℂ) = ((ζ : ℂ))⁻¹ :=
    (Complex.inv_eq_conj (Circle.norm_coe ζ)).symm
  have hw : ‖z * (starRingEnd ℂ) (ζ : ℂ)‖ < 1 := by
    rw [norm_mul, RCLike.norm_conj, Circle.norm_coe, mul_one]
    exact hz
  calc
    (∑' n : ℕ, z ^ n * (starRingEnd ℂ) ((ζ : ℂ) ^ n)) =
        ∑' n : ℕ, (z * (starRingEnd ℂ) (ζ : ℂ)) ^ n := by
          apply tsum_congr
          intro n
          rw [map_pow]
          exact (mul_pow z ((starRingEnd ℂ) (ζ : ℂ)) n).symm
    _ = (1 - z * (starRingEnd ℂ) (ζ : ℂ))⁻¹ :=
      tsum_geometric_of_norm_lt_one hw
    _ = (ζ : ℂ) / ((ζ : ℂ) - z) := by
      rw [hunit]
      have hζ0 : (ζ : ℂ) ≠ 0 := by simp
      have hden : (ζ : ℂ) - z ≠ 0 := by
        intro hzero
        have heq := sub_eq_zero.mp hzero
        have := congrArg norm heq
        rw [Circle.norm_coe] at this
        linarith
      field_simp

theorem circleL1CauchyTransform_hardyProduct
    (u v : HardyDisk) {z : ℂ} (hz : ‖z‖ < 1) :
    circleL1CauchyTransform
      (fun ζ => (hardyDiskBoundary u : Circle → ℂ) ζ *
        (hardyDiskBoundary v : Circle → ℂ) ζ) z =
      hardyFun u z * hardyFun v z := by
  let q : Circle → ℂ := fun ζ =>
    (hardyDiskBoundary u : Circle → ℂ) ζ *
      (hardyDiskBoundary v : Circle → ℂ) ζ
  have hq : Integrable q circleLebesgue := by
    exact (Lp.memLp (hardyDiskBoundary u)).integrable_mul
      (Lp.memLp (hardyDiskBoundary v))
  let T : ℕ → Circle → ℂ := fun n ζ =>
    q ζ * (z ^ n * (starRingEnd ℂ) ((ζ : ℂ) ^ n))
  have hTint (n : ℕ) : Integrable (T n) circleLebesgue := by
    apply hq.mul_bdd (c := ‖z‖ ^ n)
    · fun_prop
    · filter_upwards with ζ
      change ‖z ^ n * (starRingEnd ℂ) ((ζ : ℂ) ^ n)‖ ≤ ‖z‖ ^ n
      simp only [norm_mul, norm_pow, norm_conj, Circle.norm_coe,
        one_pow, mul_one, le_refl]
  have hTnorm (n : ℕ) :
      (∫ ζ, ‖T n ζ‖ ∂circleLebesgue) =
        ‖z‖ ^ n * ∫ ζ, ‖q ζ‖ ∂circleLebesgue := by
    change (∫ ζ, ‖q ζ *
      (z ^ n * (starRingEnd ℂ) ((ζ : ℂ) ^ n))‖ ∂circleLebesgue) = _
    calc
      (∫ ζ, ‖q ζ * (z ^ n * (starRingEnd ℂ) ((ζ : ℂ) ^ n))‖
          ∂circleLebesgue) =
          ∫ ζ, ‖z‖ ^ n * ‖q ζ‖ ∂circleLebesgue := by
        apply integral_congr_ae
        filter_upwards with ζ
        simp only [norm_mul, norm_pow, norm_conj,
          Circle.norm_coe, one_pow, mul_one]
        ring
      _ = _ := integral_const_mul _ _
  have hTsum : Summable fun n => ∫ ζ, ‖T n ζ‖ ∂circleLebesgue := by
    rw [funext hTnorm]
    exact (summable_geometric_of_lt_one (norm_nonneg z) hz).mul_right _
  have hseries := integral_tsum_of_summable_integral_norm hTint hTsum
  have hpoint : (∫ ζ, ∑' n, T n ζ ∂circleLebesgue) =
      circleL1CauchyTransform q z := by
    rw [circleL1CauchyTransform]
    apply integral_congr_ae
    filter_upwards with ζ
    dsimp [T]
    rw [tsum_mul_left, circle_geometric_kernel_tsum z hz ζ]
  have hterm (n : ℕ) :
      (∫ ζ, T n ζ ∂circleLebesgue) =
        z ^ n * ∑ i ∈ Finset.range (n + 1), u i * v (n - i) := by
    dsimp [T, q]
    calc
      (∫ ζ,
          ((hardyDiskBoundary u : Circle → ℂ) ζ *
            (hardyDiskBoundary v : Circle → ℂ) ζ) *
              (z ^ n * (starRingEnd ℂ) ((ζ : ℂ) ^ n))
          ∂circleLebesgue) =
          z ^ n * ∫ ζ,
            (hardyDiskBoundary u : Circle → ℂ) ζ *
              (hardyDiskBoundary v : Circle → ℂ) ζ *
                (starRingEnd ℂ) ((ζ : ℂ) ^ n)
            ∂circleLebesgue := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards with ζ
        ring
      _ = _ := by
        rw [hardyDiskBoundary_apply, hardyDiskBoundary_apply,
          hardyProduct_moment_convolution]
  have hprod : HasSum
      (fun n => z ^ n * ∑ i ∈ Finset.range (n + 1), u i * v (n - i))
      (hardyFun u z * hardyFun v z) := by
    have huNorm : Summable fun n => ‖(u n : ℂ) * z ^ n‖ :=
      summable_norm_iff.mpr (summable_hardyDisk_terms u hz)
    have hvNorm : Summable fun n => ‖(v n : ℂ) * z ^ n‖ :=
      summable_norm_iff.mpr (summable_hardyDisk_terms v hz)
    have h := hasSum_sum_range_mul_of_summable_norm huNorm hvNorm
    have hfun :
        (fun n => ∑ k ∈ Finset.range (n + 1),
          (u k * z ^ k) * (v (n - k) * z ^ (n - k))) =
        fun n => z ^ n * ∑ i ∈ Finset.range (n + 1), u i * v (n - i) := by
      funext n
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mem_range] at hi
      rw [show z ^ n = z ^ i * z ^ (n - i) by
        rw [← pow_add, Nat.add_sub_of_le (by omega : i ≤ n)]]
      ring
    rw [← hfun]
    simpa only [hardyFun] using h
  calc
    circleL1CauchyTransform q z =
        ∫ ζ, ∑' n, T n ζ ∂circleLebesgue := hpoint.symm
    _ = ∑' n, ∫ ζ, T n ζ ∂circleLebesgue := hseries
    _ = ∑' n, z ^ n * ∑ i ∈ Finset.range (n + 1), u i * v (n - i) := by
      apply tsum_congr hterm
    _ = hardyFun u z * hardyFun v z := hprod.tsum_eq

private theorem circle_conj_zpow_neg_nat (ζ : Circle) (m : ℕ) :
    (starRingEnd ℂ) ((ζ : ℂ) ^ (-(m : ℤ))) = (ζ : ℂ) ^ m := by
  have hζ0 : (ζ : ℂ) ≠ 0 := by simp
  rw [zpow_neg, zpow_natCast, map_inv₀, map_pow,
    ← Complex.inv_eq_conj (Circle.norm_coe ζ), inv_pow, inv_inv]

private theorem circle_geometric_kernel_tsum_exterior (z : ℂ) (hz : 1 < ‖z‖)
    (ζ : Circle) :
    (∑' n : ℕ, -(z⁻¹) ^ (n + 1) * (ζ : ℂ) ^ (n + 1)) =
      (ζ : ℂ) / ((ζ : ℂ) - z) := by
  have hz0 : z ≠ 0 := by
    intro hz0
    rw [hz0, norm_zero] at hz
    linarith
  have hw : ‖z⁻¹ * (ζ : ℂ)‖ < 1 := by
    rw [norm_mul, norm_inv, Circle.norm_coe, mul_one]
    exact inv_lt_one_of_one_lt₀ hz
  calc
    (∑' n : ℕ, -(z⁻¹) ^ (n + 1) * (ζ : ℂ) ^ (n + 1)) =
        ∑' n : ℕ, -(z⁻¹ * (ζ : ℂ)) * (z⁻¹ * (ζ : ℂ)) ^ n := by
          apply tsum_congr
          intro n
          rw [pow_succ', pow_succ', mul_pow]
          ring
    _ = -(z⁻¹ * (ζ : ℂ)) * (1 - z⁻¹ * (ζ : ℂ))⁻¹ := by
      rw [tsum_mul_left, tsum_geometric_of_norm_lt_one hw]
    _ = (ζ : ℂ) / ((ζ : ℂ) - z) := by
      field_simp
      rw [show (ζ : ℂ) - z = -(z - (ζ : ℂ)) by ring]
      simp only [one_div, inv_neg]

theorem circleL1CauchyTransform_hardyProduct_exterior
    (u v : HardyDisk) {z : ℂ} (hz : 1 < ‖z‖) :
    circleL1CauchyTransform
      (fun ζ => (hardyDiskBoundary u : Circle → ℂ) ζ *
        (hardyDiskBoundary v : Circle → ℂ) ζ) z = 0 := by
  let q : Circle → ℂ := fun ζ =>
    (hardyDiskBoundary u : Circle → ℂ) ζ *
      (hardyDiskBoundary v : Circle → ℂ) ζ
  have hq : Integrable q circleLebesgue := by
    exact (Lp.memLp (hardyDiskBoundary u)).integrable_mul
      (Lp.memLp (hardyDiskBoundary v))
  let T : ℕ → Circle → ℂ := fun n ζ =>
    q ζ * (-(z⁻¹) ^ (n + 1) * (ζ : ℂ) ^ (n + 1))
  have hTint (n : ℕ) : Integrable (T n) circleLebesgue := by
    apply hq.mul_bdd (c := ‖z⁻¹‖ ^ (n + 1))
    · fun_prop
    · filter_upwards with ζ
      change ‖-(z⁻¹) ^ (n + 1) * (ζ : ℂ) ^ (n + 1)‖ ≤
        ‖z⁻¹‖ ^ (n + 1)
      simp only [norm_mul, norm_neg, norm_pow, Circle.norm_coe,
        one_pow, mul_one, le_refl]
  have hTnorm (n : ℕ) :
      (∫ ζ, ‖T n ζ‖ ∂circleLebesgue) =
        ‖z⁻¹‖ ^ (n + 1) * ∫ ζ, ‖q ζ‖ ∂circleLebesgue := by
    change (∫ ζ, ‖q ζ *
      (-(z⁻¹) ^ (n + 1) * (ζ : ℂ) ^ (n + 1))‖ ∂circleLebesgue) = _
    calc
      (∫ ζ, ‖q ζ * (-(z⁻¹) ^ (n + 1) * (ζ : ℂ) ^ (n + 1))‖
          ∂circleLebesgue) =
          ∫ ζ, ‖z⁻¹‖ ^ (n + 1) * ‖q ζ‖ ∂circleLebesgue := by
        apply integral_congr_ae
        filter_upwards with ζ
        simp only [norm_mul, norm_neg, norm_pow, Circle.norm_coe,
          one_pow, mul_one]
        ring
      _ = _ := integral_const_mul _ _
  have hTsum : Summable fun n => ∫ ζ, ‖T n ζ‖ ∂circleLebesgue := by
    rw [funext hTnorm]
    have hg : Summable fun n : ℕ => ‖z⁻¹‖ ^ n :=
      summable_geometric_of_lt_one (norm_nonneg z⁻¹)
        (by simpa [norm_inv] using inv_lt_one_of_one_lt₀ hz)
    simpa only [pow_succ'] using
      (hg.mul_left ‖z⁻¹‖).mul_right (∫ ζ, ‖q ζ‖ ∂circleLebesgue)
  have hseries := integral_tsum_of_summable_integral_norm hTint hTsum
  have hpoint : (∫ ζ, ∑' n, T n ζ ∂circleLebesgue) =
      circleL1CauchyTransform q z := by
    rw [circleL1CauchyTransform]
    apply integral_congr_ae
    filter_upwards with ζ
    dsimp [T]
    rw [tsum_mul_left, circle_geometric_kernel_tsum_exterior z hz ζ]
  have hterm (n : ℕ) : (∫ ζ, T n ζ ∂circleLebesgue) = 0 := by
    have hm := hardyProduct_moment_eq_zero_of_neg
      (u : ℕ → ℂ) (v : ℕ → ℂ) (lp.memℓp u) (lp.memℓp v)
      (-((n + 1 : ℕ) : ℤ)) (by omega)
    have hmoment : (∫ ζ : Circle, q ζ * (ζ : ℂ) ^ (n + 1)
        ∂circleLebesgue) = 0 := by
      dsimp [q]
      rw [hardyDiskBoundary_apply, hardyDiskBoundary_apply]
      calc
        (∫ ζ : Circle,
            (circleRieszFischerOfNat (u : ℕ → ℂ) (lp.memℓp u)) ζ *
              (circleRieszFischerOfNat (v : ℕ → ℂ) (lp.memℓp v)) ζ *
                (ζ : ℂ) ^ (n + 1) ∂circleLebesgue) =
            ∫ ζ : Circle,
              (circleRieszFischerOfNat (u : ℕ → ℂ) (lp.memℓp u)) ζ *
                (circleRieszFischerOfNat (v : ℕ → ℂ) (lp.memℓp v)) ζ *
                  (starRingEnd ℂ) ((ζ : ℂ) ^ (-((n + 1 : ℕ) : ℤ)))
              ∂circleLebesgue := by
          apply integral_congr_ae
          filter_upwards with ζ
          rw [circle_conj_zpow_neg_nat ζ (n + 1)]
        _ = 0 := hm
    dsimp [T]
    calc
      (∫ ζ, q ζ * (-(z⁻¹) ^ (n + 1) * (ζ : ℂ) ^ (n + 1))
          ∂circleLebesgue) =
          (-(z⁻¹) ^ (n + 1)) *
            ∫ ζ, q ζ * (ζ : ℂ) ^ (n + 1) ∂circleLebesgue := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards with ζ
        ring
      _ = 0 := by rw [hmoment, mul_zero]
  calc
    circleL1CauchyTransform q z =
        ∫ ζ, ∑' n, T n ζ ∂circleLebesgue := hpoint.symm
    _ = ∑' n, ∫ ζ, T n ζ ∂circleLebesgue := hseries
    _ = 0 := by simp only [hterm, tsum_zero]

/-- An integrable circle density vanishing near a circle point has a Cauchy transform analytic
through that point. -/
theorem differentiableAt_circleL1CauchyTransform_of_ae_zero_near
    (f : Circle → ℂ) (hf : Integrable f circleLebesgue)
    (z₀ : ℂ) {r : ℝ} (hr : 0 < r)
    (hzero : ∀ᵐ ζ : Circle ∂circleLebesgue,
      dist (ζ : ℂ) z₀ < r → f ζ = 0) :
    DifferentiableAt ℂ (circleL1CauchyTransform f) z₀ := by
  let F : ℂ → Circle → ℂ := fun z ζ =>
    if dist (ζ : ℂ) z₀ < r then 0
    else f ζ * ((ζ : ℂ) / ((ζ : ℂ) - z))
  let bound : Circle → ℝ := fun ζ => (2 / r) * ‖f ζ‖
  have hmeas : ∀ z ∈ ball z₀ (r / 2),
      AEStronglyMeasurable (F z) circleLebesgue := by
    intro z hz
    have hset : MeasurableSet {ζ : Circle | dist (ζ : ℂ) z₀ < r} := by
      change @MeasurableSet Circle (borel Circle)
        {ζ : Circle | dist (ζ : ℂ) z₀ < r}
      letI : MeasurableSpace Circle := borel Circle
      rw [show {ζ : Circle | dist (ζ : ℂ) z₀ < r} =
          (fun ζ : Circle => (ζ : ℂ)) ⁻¹' ball z₀ r by
        ext ζ
        simp [mem_ball]]
      exact @IsOpen.measurableSet Circle _ _ (borel Circle) ⟨le_rfl⟩
        (isOpen_ball.preimage continuous_subtype_val)
    have hkernelMeas : Measurable
        (fun ζ : Circle => (ζ : ℂ) / ((ζ : ℂ) - z)) := by
      fun_prop
    have hprod : AEStronglyMeasurable
        (fun ζ : Circle => f ζ * ((ζ : ℂ) / ((ζ : ℂ) - z)))
        circleLebesgue :=
      hf.aestronglyMeasurable.mul hkernelMeas.aestronglyMeasurable
    convert hprod.indicator hset.compl using 1
    funext ζ
    by_cases hnear : dist (ζ : ℂ) z₀ < r <;>
      simp [F, Set.indicator, hnear]
  have hdiff : ∀ ζ : Circle,
      DifferentiableOn ℂ (fun z : ℂ => F z ζ) (ball z₀ (r / 2)) := by
    intro ζ
    by_cases hnear : dist (ζ : ℂ) z₀ < r
    · simp only [F, if_pos hnear]
      fun_prop
    · simp only [F, if_neg hnear]
      intro z hz
      apply DifferentiableAt.differentiableWithinAt
      have hconstF : DifferentiableAt ℂ (fun _ : ℂ => f ζ) z :=
        differentiableAt_const (c := f ζ)
      have hconstZeta : DifferentiableAt ℂ (fun _ : ℂ => (ζ : ℂ)) z :=
        differentiableAt_const (c := (ζ : ℂ))
      have hden : (ζ : ℂ) - z ≠ 0 := by
        intro hzero
        have heq : (ζ : ℂ) = z := sub_eq_zero.mp hzero
        have hzdist : dist (ζ : ℂ) z₀ < r / 2 := by
          simpa [heq] using hz
        exact hnear (by linarith)
      exact hconstF.mul
        (hconstZeta.div (hconstZeta.sub differentiableAt_id) hden)
  have hbound : ∀ ζ : Circle, ∀ z ∈ ball z₀ (r / 2),
      ‖F z ζ‖ ≤ bound ζ := by
    intro ζ z hz
    by_cases hnear : dist (ζ : ℂ) z₀ < r
    · simp only [F, if_pos hnear, norm_zero]
      change 0 ≤ (2 / r) * ‖f ζ‖
      exact mul_nonneg (div_nonneg (by norm_num) hr.le) (norm_nonneg _)
    · simp only [F, if_neg hnear, bound]
      have hfar : r ≤ dist (ζ : ℂ) z₀ := le_of_not_gt hnear
      have htriangle : dist (ζ : ℂ) z₀ ≤
          dist (ζ : ℂ) z + dist z z₀ := dist_triangle _ _ _
      have hzdist : dist z z₀ < r / 2 := by
        simpa [mem_ball] using hz
      have hsep : r / 2 < ‖(ζ : ℂ) - z‖ := by
        rw [← dist_eq]
        linarith
      have hkernel : ‖(ζ : ℂ) / ((ζ : ℂ) - z)‖ ≤ 2 / r := by
        rw [norm_div, Circle.norm_coe, one_div]
        have hhalf : 0 < r / 2 := by positivity
        have hnormpos : 0 < ‖(ζ : ℂ) - z‖ := lt_trans hhalf hsep
        calc
          ‖(ζ : ℂ) - z‖⁻¹ ≤ (r / 2)⁻¹ :=
            (inv_le_inv₀ hnormpos hhalf).2 hsep.le
          _ = 2 / r := by field_simp
      rw [norm_mul]
      calc
        ‖f ζ‖ * ‖(ζ : ℂ) / ((ζ : ℂ) - z)‖ ≤
            ‖f ζ‖ * (2 / r) :=
          mul_le_mul_of_nonneg_left hkernel (norm_nonneg _)
        _ = (2 / r) * ‖f ζ‖ := by ring
  have hboundInt : Integrable bound circleLebesgue :=
    hf.norm.const_mul (2 / r)
  have hdiffInt : DifferentiableAt ℂ
      (fun z : ℂ => ∫ ζ : Circle, F z ζ ∂circleLebesgue) z₀ :=
    differentiableAt_integral_of_cauchy_dominated
      (by positivity : 0 < r / 2) hmeas hdiff hbound hboundInt
  have heq : circleL1CauchyTransform f =
      fun z : ℂ => ∫ ζ : Circle, F z ζ ∂circleLebesgue := by
    funext z
    rw [circleL1CauchyTransform]
    apply integral_congr_ae
    filter_upwards [hzero] with ζ hζ
    by_cases hnear : dist (ζ : ℂ) z₀ < r
    · simp [F, hnear, hζ hnear]
    · simp [F, hnear]
  rw [heq]
  exact hdiffInt

private theorem integrable_circleL1_mul_continuous
    (f : Circle → ℂ) (hf : Integrable f circleLebesgue)
    (K : Circle → ℂ) (hK : Continuous K) :
    Integrable (fun ζ : Circle => f ζ * K ζ) circleLebesgue := by
  let Kc : C(Circle, ℂ) := ⟨K, hK⟩
  exact hf.mul_bdd hK.aestronglyMeasurable
    (Filter.Eventually.of_forall fun ζ => by
      simpa [Kc] using ContinuousMap.norm_coe_le_norm Kc ζ)

private theorem integrable_circleL1_conj
    (f : Circle → ℂ) (hf : Integrable f circleLebesgue) :
    Integrable (fun ζ => (starRingEnd ℂ) (f ζ)) circleLebesgue := by
  exact hf.norm.mono'
    (Complex.continuous_conj.comp_aestronglyMeasurable hf.aestronglyMeasurable)
    (Filter.Eventually.of_forall fun ζ => by rw [RCLike.norm_conj])

theorem circleL1CauchyTransform_exterior_relation
    (f : Circle → ℂ) (hf : Integrable f circleLebesgue)
    {z : ℂ} (hz : 1 < ‖z‖) :
    circleL1CauchyTransform f z =
      (∫ ζ : Circle, f ζ ∂circleLebesgue) -
        (starRingEnd ℂ)
          (circleL1CauchyTransform (fun ζ => (starRingEnd ℂ) (f ζ))
            ((starRingEnd ℂ z)⁻¹)) := by
  have hw : ‖(starRingEnd ℂ z)⁻¹‖ < 1 := by
    rw [norm_inv, RCLike.norm_conj]
    exact inv_lt_one_of_one_lt₀ hz
  have hkernel : Continuous fun ζ : Circle =>
      (ζ : ℂ) / ((ζ : ℂ) - (starRingEnd ℂ z)⁻¹) := by
    apply Continuous.div continuous_subtype_val
      (continuous_subtype_val.sub continuous_const)
    intro ζ
    apply sub_ne_zero.mpr
    intro heq
    have hnorm := congrArg norm heq
    rw [Circle.norm_coe] at hnorm
    linarith
  have hfconj := integrable_circleL1_conj f hf
  have hB : Integrable (fun ζ : Circle =>
      (starRingEnd ℂ) (f ζ) *
        ((ζ : ℂ) / ((ζ : ℂ) - (starRingEnd ℂ z)⁻¹))) circleLebesgue :=
    integrable_circleL1_mul_continuous _ hfconj _ hkernel
  rw [circleL1CauchyTransform, circleL1CauchyTransform]
  calc
    (∫ ζ : Circle, f ζ * ((ζ : ℂ) / ((ζ : ℂ) - z)) ∂circleLebesgue) =
        ∫ ζ : Circle, f ζ - (starRingEnd ℂ)
          ((starRingEnd ℂ) (f ζ) *
            ((ζ : ℂ) / ((ζ : ℂ) - (starRingEnd ℂ z)⁻¹)))
          ∂circleLebesgue := by
      apply integral_congr_ae
      filter_upwards with ζ
      have hζ0 : (ζ : ℂ) ≠ 0 := by simp
      have hz0 : z ≠ 0 := by
        intro hz0
        rw [hz0, norm_zero] at hz
        linarith
      have hden1 : (ζ : ℂ) - z ≠ 0 := by
        intro hzero
        have heq := sub_eq_zero.mp hzero
        have hnorm := congrArg norm heq
        rw [Circle.norm_coe] at hnorm
        linarith
      have hden2 : (ζ : ℂ) - (starRingEnd ℂ z)⁻¹ ≠ 0 := by
        intro hzero
        have heq := sub_eq_zero.mp hzero
        have hnorm := congrArg norm heq
        rw [Circle.norm_coe, norm_inv, RCLike.norm_conj] at hnorm
        have := inv_lt_one_of_one_lt₀ hz
        linarith
      have hden1' : -(ζ : ℂ) + z ≠ 0 := by
        intro hzero
        apply hden1
        linear_combination -hzero
      simp only [map_mul, map_div₀, map_sub, map_inv₀,
        starRingEnd_self_apply]
      have hcircle : (starRingEnd ℂ) (ζ : ℂ) = ((ζ : ℂ))⁻¹ :=
        (Complex.inv_eq_conj (Circle.norm_coe ζ)).symm
      rw [hcircle]
      field_simp [hz0, hζ0, hden1, hden1', hden2]
      have hinv := mul_inv_cancel₀ hden1'
      linear_combination -(f ζ * z) * hinv
    _ = (∫ ζ : Circle, f ζ ∂circleLebesgue) -
        ∫ ζ : Circle, (starRingEnd ℂ)
          ((starRingEnd ℂ) (f ζ) *
            ((ζ : ℂ) / ((ζ : ℂ) - (starRingEnd ℂ z)⁻¹)))
          ∂circleLebesgue := by
      have hBconj : Integrable (fun ζ : Circle => (starRingEnd ℂ)
          ((starRingEnd ℂ) (f ζ) *
            ((ζ : ℂ) / ((ζ : ℂ) - (starRingEnd ℂ z)⁻¹)))) circleLebesgue :=
        integrable_circleL1_conj _ hB
      rw [integral_sub hf hBconj]
    _ = (∫ ζ : Circle, f ζ ∂circleLebesgue) -
        (starRingEnd ℂ)
          (∫ ζ : Circle, (starRingEnd ℂ) (f ζ) *
            ((ζ : ℂ) / ((ζ : ℂ) - (starRingEnd ℂ z)⁻¹))
            ∂circleLebesgue) := by
      rw [integral_conj]

theorem integral_hardyProduct (u v : HardyDisk) :
    (∫ ζ : Circle,
      (hardyDiskBoundary u : Circle → ℂ) ζ *
        (hardyDiskBoundary v : Circle → ℂ) ζ ∂circleLebesgue) =
      u 0 * v 0 := by
  have h := hardyProduct_moment_convolution
    (u : ℕ → ℂ) (v : ℕ → ℂ) (lp.memℓp u) (lp.memℓp v) 0
  simpa only [hardyDiskBoundary_apply, pow_zero, map_one, mul_one,
    Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.zero_sub] using h

theorem circleL1CauchyTransform_conj_hardyProduct_exterior
    (u v : HardyDisk) {z : ℂ} (hz : 1 < ‖z‖) :
    circleL1CauchyTransform
      (fun ζ => (starRingEnd ℂ)
        ((hardyDiskBoundary u : Circle → ℂ) ζ *
          (hardyDiskBoundary v : Circle → ℂ) ζ)) z =
      (starRingEnd ℂ) (u 0 * v 0) -
        (starRingEnd ℂ)
          (hardyFun u ((starRingEnd ℂ z)⁻¹) *
            hardyFun v ((starRingEnd ℂ z)⁻¹)) := by
  let q : Circle → ℂ := fun ζ =>
    (hardyDiskBoundary u : Circle → ℂ) ζ *
      (hardyDiskBoundary v : Circle → ℂ) ζ
  have hq : Integrable q circleLebesgue := by
    exact (Lp.memLp (hardyDiskBoundary u)).integrable_mul
      (Lp.memLp (hardyDiskBoundary v))
  have hw : ‖(starRingEnd ℂ z)⁻¹‖ < 1 := by
    rw [norm_inv, RCLike.norm_conj]
    exact inv_lt_one_of_one_lt₀ hz
  have hrel := circleL1CauchyTransform_exterior_relation
    (fun ζ => (starRingEnd ℂ) (q ζ)) (integrable_circleL1_conj q hq) hz
  rw [show (fun ζ => (starRingEnd ℂ) ((starRingEnd ℂ) (q ζ))) = q by
      funext ζ; simp] at hrel
  rw [integral_conj, integral_hardyProduct u v,
    circleL1CauchyTransform_hardyProduct u v hw] at hrel
  exact hrel

theorem circleL1CauchyTransform_conj_hardyProduct
    (u v : HardyDisk) {z : ℂ} (hz : ‖z‖ < 1) :
    circleL1CauchyTransform
      (fun ζ => (starRingEnd ℂ)
        ((hardyDiskBoundary u : Circle → ℂ) ζ *
          (hardyDiskBoundary v : Circle → ℂ) ζ)) z =
      (starRingEnd ℂ) (u 0 * v 0) := by
  by_cases hz0 : z = 0
  · subst z
    rw [circleL1CauchyTransform]
    calc
      (∫ ζ : Circle,
          (starRingEnd ℂ)
              ((hardyDiskBoundary u : Circle → ℂ) ζ *
                (hardyDiskBoundary v : Circle → ℂ) ζ) *
            ((ζ : ℂ) / ((ζ : ℂ) - 0)) ∂circleLebesgue) =
          ∫ ζ : Circle, (starRingEnd ℂ)
            ((hardyDiskBoundary u : Circle → ℂ) ζ *
              (hardyDiskBoundary v : Circle → ℂ) ζ) ∂circleLebesgue := by
        apply integral_congr_ae
        filter_upwards with ζ
        have hζ0 : (ζ : ℂ) ≠ 0 := by simp
        simp [hζ0]
      _ = _ := by rw [integral_conj, integral_hardyProduct]
  · let w : ℂ := (starRingEnd ℂ z)⁻¹
    have hw : 1 < ‖w‖ := by
      dsimp [w]
      rw [norm_inv, RCLike.norm_conj]
      exact (one_lt_inv₀ (norm_pos_iff.mpr hz0)).2 hz
    have harg : ((starRingEnd ℂ w)⁻¹) = z := by
      dsimp [w]
      rw [map_inv₀, starRingEnd_self_apply, inv_inv]
    have hext := circleL1CauchyTransform_hardyProduct_exterior u v hw
    have hrel := circleL1CauchyTransform_exterior_relation
      (fun ζ => (hardyDiskBoundary u : Circle → ℂ) ζ *
        (hardyDiskBoundary v : Circle → ℂ) ζ)
      ((Lp.memLp (hardyDiskBoundary u)).integrable_mul
        (Lp.memLp (hardyDiskBoundary v))) hw
    rw [hext, integral_hardyProduct, harg] at hrel
    have hc := congrArg (starRingEnd ℂ) hrel
    have hc' : 0 =
        (starRingEnd ℂ) (u 0 * v 0) -
          circleL1CauchyTransform
            (fun ζ => (starRingEnd ℂ)
              ((hardyDiskBoundary u : Circle → ℂ) ζ *
                (hardyDiskBoundary v : Circle → ℂ) ζ)) z := by
      simpa using hc
    exact (sub_eq_zero.mp hc'.symm).symm

theorem circleL1CauchyTransform_sub
    (f g : Circle → ℂ)
    (hf : Integrable f circleLebesgue) (hg : Integrable g circleLebesgue)
    {z : ℂ} (hz : ‖z‖ ≠ 1) :
    circleL1CauchyTransform (fun ζ => f ζ - g ζ) z =
      circleL1CauchyTransform f z - circleL1CauchyTransform g z := by
  have hkernel : Continuous fun ζ : Circle =>
      (ζ : ℂ) / ((ζ : ℂ) - z) := by
    apply Continuous.div continuous_subtype_val
      (continuous_subtype_val.sub continuous_const)
    intro ζ hden
    apply hz
    have heq : (ζ : ℂ) = z := sub_eq_zero.mp hden
    rw [← heq, Circle.norm_coe]
  have hfint := integrable_circleL1_mul_continuous f hf _ hkernel
  have hgint := integrable_circleL1_mul_continuous g hg _ hkernel
  rw [circleL1CauchyTransform, circleL1CauchyTransform,
    circleL1CauchyTransform]
  calc
    (∫ ζ : Circle, (f ζ - g ζ) * ((ζ : ℂ) / ((ζ : ℂ) - z))
        ∂circleLebesgue) =
        ∫ ζ : Circle,
          (f ζ * ((ζ : ℂ) / ((ζ : ℂ) - z)) -
            g ζ * ((ζ : ℂ) / ((ζ : ℂ) - z))) ∂circleLebesgue := by
      apply integral_congr_ae
      filter_upwards with ζ
      ring
    _ = (∫ ζ : Circle, f ζ * ((ζ : ℂ) / ((ζ : ℂ) - z))
          ∂circleLebesgue) -
        ∫ ζ : Circle, g ζ * ((ζ : ℂ) / ((ζ : ℂ) - z))
          ∂circleLebesgue := integral_sub hfint hgint

/-- Reciprocal-conjugate exterior reflection of a product of two Hardy functions. -/
def hardyProductExteriorReflection (u v : HardyDisk) (z : ℂ) : ℂ :=
  (starRingEnd ℂ)
    (hardyFun u ((starRingEnd ℂ z)⁻¹) *
      hardyFun v ((starRingEnd ℂ z)⁻¹))

/-- Exact local gluing of two `H¹` Hardy products whose traces agree on a circle arc. -/
theorem exists_differentiableAt_hardyProduct_arc_glue
    (u₁ u₂ v₁ v₂ : HardyDisk) (z₀ : ℂ) {r : ℝ} (hr : 0 < r)
    (hseam : ∀ᵐ ζ : Circle ∂circleLebesgue,
      dist (ζ : ℂ) z₀ < r →
        (hardyDiskBoundary u₁ : Circle → ℂ) ζ *
            (hardyDiskBoundary u₂ : Circle → ℂ) ζ =
          (starRingEnd ℂ)
            ((hardyDiskBoundary v₁ : Circle → ℂ) ζ *
              (hardyDiskBoundary v₂ : Circle → ℂ) ζ)) :
    ∃ G : ℂ → ℂ,
      DifferentiableAt ℂ G z₀ ∧
      (∀ z : ℂ, ‖z‖ < 1 →
        G z = hardyFun u₁ z * hardyFun u₂ z) ∧
      (∀ z : ℂ, 1 < ‖z‖ →
        G z = hardyProductExteriorReflection v₁ v₂ z) := by
  let q : Circle → ℂ := fun ζ =>
    (hardyDiskBoundary u₁ : Circle → ℂ) ζ *
      (hardyDiskBoundary u₂ : Circle → ℂ) ζ
  let s : Circle → ℂ := fun ζ =>
    (hardyDiskBoundary v₁ : Circle → ℂ) ζ *
      (hardyDiskBoundary v₂ : Circle → ℂ) ζ
  let sc : Circle → ℂ := fun ζ => (starRingEnd ℂ) (s ζ)
  let d : Circle → ℂ := fun ζ => q ζ - sc ζ
  have hq : Integrable q circleLebesgue := by
    exact (Lp.memLp (hardyDiskBoundary u₁)).integrable_mul
      (Lp.memLp (hardyDiskBoundary u₂))
  have hs : Integrable s circleLebesgue := by
    exact (Lp.memLp (hardyDiskBoundary v₁)).integrable_mul
      (Lp.memLp (hardyDiskBoundary v₂))
  have hsc : Integrable sc circleLebesgue := integrable_circleL1_conj s hs
  have hd : Integrable d circleLebesgue := hq.sub hsc
  have hzeroD : ∀ᵐ ζ : Circle ∂circleLebesgue,
      dist (ζ : ℂ) z₀ < r → d ζ = 0 := by
    filter_upwards [hseam] with ζ hmatch
    intro hnear
    dsimp [d, q, sc, s]
    rw [hmatch hnear, sub_self]
  let c : ℂ := (starRingEnd ℂ) (v₁ 0 * v₂ 0)
  refine ⟨fun z => circleL1CauchyTransform d z + c,
    (differentiableAt_circleL1CauchyTransform_of_ae_zero_near
      d hd z₀ hr hzeroD).add (differentiableAt_const (c := c)), ?_, ?_⟩
  · intro z hz
    have hzne : ‖z‖ ≠ 1 := ne_of_lt hz
    change circleL1CauchyTransform (fun ζ => q ζ - sc ζ) z + c = _
    rw [circleL1CauchyTransform_sub q sc hq hsc hzne]
    change circleL1CauchyTransform q z -
      circleL1CauchyTransform (fun ζ => (starRingEnd ℂ) (s ζ)) z + c = _
    rw [show q = fun ζ =>
          (hardyDiskBoundary u₁ : Circle → ℂ) ζ *
            (hardyDiskBoundary u₂ : Circle → ℂ) ζ by rfl,
      circleL1CauchyTransform_hardyProduct u₁ u₂ hz]
    rw [show s = fun ζ =>
          (hardyDiskBoundary v₁ : Circle → ℂ) ζ *
            (hardyDiskBoundary v₂ : Circle → ℂ) ζ by rfl,
      circleL1CauchyTransform_conj_hardyProduct v₁ v₂ hz]
    dsimp [c]
    ring
  · intro z hz
    have hzne : ‖z‖ ≠ 1 := ne_of_gt hz
    change circleL1CauchyTransform (fun ζ => q ζ - sc ζ) z + c = _
    rw [circleL1CauchyTransform_sub q sc hq hsc hzne]
    change circleL1CauchyTransform q z -
      circleL1CauchyTransform (fun ζ => (starRingEnd ℂ) (s ζ)) z + c = _
    rw [show q = fun ζ =>
          (hardyDiskBoundary u₁ : Circle → ℂ) ζ *
            (hardyDiskBoundary u₂ : Circle → ℂ) ζ by rfl,
      circleL1CauchyTransform_hardyProduct_exterior u₁ u₂ hz]
    rw [show s = fun ζ =>
          (hardyDiskBoundary v₁ : Circle → ℂ) ζ *
            (hardyDiskBoundary v₂ : Circle → ℂ) ζ by rfl,
      circleL1CauchyTransform_conj_hardyProduct_exterior v₁ v₂ hz]
    simp only [zero_sub, hardyProductExteriorReflection]
    dsimp [c]
    ring

end

end GaloisForLFunctions.HTGeometry
