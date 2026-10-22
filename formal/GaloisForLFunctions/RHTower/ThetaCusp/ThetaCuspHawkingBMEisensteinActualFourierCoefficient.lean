import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMEisensteinPrimitiveCuspReindexing
import GaloisForLFunctions.RHTower.Sieve.CircleOrthogonality

/-!
# Genuine Fourier coefficients of the actual Eisenstein Poincare series

Corpus research isolated the remaining analytic weld after exact primitive-cusp reindexing: the
Fourier coefficient had to be taken from the actual Poincare function, not defined by the
already-summed Ramanujan--Bessel expression.  This module proves a quantitative Tonelli theorem,
the unit-cell `L1` contraction of integer periodization, and the sharp denominator majorant

`integral_(0,1] ||slice_Q|| <= C(z,s) Q^(1-2 Re(s))`.

Thus genuine unit-cell Fourier integration commutes with the denominator `tsum`.  Combining that
exchange with the corpus fixed-slice Ramanujan theorem, exact Ramanujan Dirichlet series, and
Cauchy-power Fourier--Bessel transform proves that every positive Fourier coefficient of the
actual completed Poincare series is exactly

`2 a_(s-1/2)(n) sqrt(y) K_(s-1/2)(2 pi n y)`.

No coefficient is defined by the target formula, and no pointwise Poisson, uniform convergence,
or conditional rearrangement premise is used.  This is the positive-mode half of Fourier
uniqueness in the fixed route

`actual Poincare coefficient -> Fourier uniqueness -> modular Green/Stokes defects -> balanced
polarized BM coefficient -> negative BM leg -> conserved left-QNM projection -> HC94 -> RH`.

`[NEW] [PAPER-PROVED] [LEAN-PROVED] [HB] [FZZ-P] [RBH] [PW-B]`
-/

open Real MeasureTheory Set intervalIntegral Filter Topology Function
open scoped ENNReal FourierTransform

noncomputable section

namespace GaloisForLFunctions.HTGeometry

theorem integral_norm_tsum_le_tsum_integral_norm
    {α E ι : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [Countable ι] {μ : Measure α} {F : ι → α → E}
    (hF_int : ∀ i, Integrable (F i) μ)
    (hF_sum : Summable fun i => ∫ x, ‖F i x‖ ∂μ) :
    (∫ x, ‖∑' i, F i x‖ ∂μ) ≤ ∑' i, ∫ x, ‖F i x‖ ∂μ := by
  let B : α → ℝ≥0∞ := fun x => ∑' i, ‖F i x‖ₑ
  have hFiMeas : ∀ i, AEMeasurable (fun x => ‖F i x‖ₑ) μ := by
    intro i
    exact (hF_int i).aestronglyMeasurable.enorm
  have hBMeas : AEMeasurable B μ := AEMeasurable.tsum hFiMeas
  have hBfinite : (∫⁻ x, B x ∂μ) ≠ ∞ := by
    dsimp only [B]
    rw [lintegral_tsum hFiMeas]
    have hi (i : ι) :
        (∫⁻ x, ‖F i x‖ₑ ∂μ) = ‖∫ x, ‖F i x‖ ∂μ‖ₑ := by
      dsimp only [enorm]
      rw [lintegral_coe_eq_integral _ (hF_int i).norm, ENNReal.coe_nnreal_eq,
        coe_nnnorm, Real.norm_of_nonneg (integral_nonneg (fun x => norm_nonneg (F i x)))]
      simp only [coe_nnnorm]
    rw [funext hi]
    exact ENNReal.tsum_coe_ne_top_iff_summable.2 <|
      NNReal.summable_coe.1 hF_sum.abs
  have hBne : ∀ᵐ x ∂μ, B x ≠ ∞ :=
    (ae_lt_top' hBMeas hBfinite).mono fun x hx => hx.ne
  have hBint : Integrable (fun x => (B x).toReal) μ :=
    integrable_toReal_of_lintegral_ne_top hBMeas hBfinite
  have hsumInt : Integrable (fun x => ∑' i, F i x) μ :=
    integrable_tsum_of_summable_integral_norm hF_int hF_sum
  have hpoint : ∀ᵐ x ∂μ, ‖∑' i, F i x‖ ≤ (B x).toReal := by
    filter_upwards [hBne] with x hx
    have hnormSummable : Summable fun i => ‖F i x‖ := by
      have hnn : Summable fun i => ‖F i x‖₊ := by
        apply ENNReal.tsum_coe_ne_top_iff_summable.1
        simpa only [B, enorm_eq_nnnorm] using hx
      exact NNReal.summable_coe.2 hnn
    calc
      ‖∑' i, F i x‖ ≤ ∑' i, ‖F i x‖ := norm_tsum_le_tsum_norm hnormSummable
      _ = (B x).toReal := by
        dsimp only [B]
        rw [ENNReal.tsum_toReal_eq (fun i => enorm_ne_top)]
        simp only [enorm_eq_nnnorm, ENNReal.coe_toReal, coe_nnnorm]
  calc
    (∫ x, ‖∑' i, F i x‖ ∂μ) ≤ ∫ x, (B x).toReal ∂μ :=
      integral_mono_ae hsumInt.norm hBint hpoint
    _ = (∫⁻ x, B x ∂μ).toReal :=
      integral_toReal hBMeas (hBne.mono fun _ h => lt_top_iff_ne_top.mpr h)
    _ = (∑' i, ∫⁻ x, ‖F i x‖ₑ ∂μ).toReal := by
      rw [lintegral_tsum hFiMeas]
    _ = ∑' i, (∫⁻ x, ‖F i x‖ₑ ∂μ).toReal := by
      rw [ENNReal.tsum_toReal_eq]
      intro i
      exact ((hF_int i).hasFiniteIntegral).ne
    _ = ∑' i, ∫ x, ‖F i x‖ ∂μ := by
      apply tsum_congr
      intro i
      exact (integral_norm_eq_lintegral_enorm (hF_int i).aestronglyMeasurable).symm

theorem integral_tsum_eq_tsum_integral_of_summable_integral_norm
    {α E ι : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
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

theorem integral_unit_norm_l1Periodization_le_integral_norm
    {f : ℝ → ℂ} (hf : Integrable f) :
    (∫ x in Set.Ioc (0 : ℝ) 1, ‖l1Periodization f x‖) ≤
      ∫ x : ℝ, ‖f x‖ := by
  let F : ℤ → ℝ → ℂ := fun k x => f (x + k)
  let μ : Measure ℝ := volume.restrict (Set.Ioc (0 : ℝ) 1)
  have hFint : ∀ k : ℤ, Integrable (F k) μ := by
    intro k
    exact (hf.comp_add_right k).restrict
  have hnormInt (k : ℤ) :
      ∫ x, ‖F k x‖ ∂μ = ∫ x in (0 : ℝ)..1, ‖f (x + k)‖ := by
    rw [intervalIntegral.integral_of_le zero_le_one]
  have hbase := hf.norm.hasSum_intervalIntegral_comp_add_int
  have hFsum : Summable fun k : ℤ => ∫ x, ‖F k x‖ ∂μ :=
    hbase.summable.congr (fun k => (hnormInt k).symm)
  have hbound := integral_norm_tsum_le_tsum_integral_norm hFint hFsum
  change (∫ x, ‖∑' k : ℤ, f (x + k)‖ ∂μ) ≤ _
  calc
    (∫ x, ‖∑' k : ℤ, f (x + k)‖ ∂μ) ≤
        ∑' k : ℤ, ∫ x, ‖F k x‖ ∂μ := hbound
    _ = ∑' k : ℤ, ∫ x in (0 : ℝ)..1, ‖f (x + k)‖ := by
      apply tsum_congr
      exact hnormInt
    _ = ∫ x : ℝ, ‖f x‖ := hbase.tsum_eq

end GaloisForLFunctions.HTGeometry

namespace RHTower

theorem d4BM_integrable_shiftedCauchyPeriodization
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter)
    (a : ℝ) :
    Integrable
      (fun x : ℝ => GaloisForLFunctions.HTGeometry.l1Periodization
        (d4BMCauchyPowerKernel z P.s) (x + a))
      (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
  let g : ℝ → ℂ := fun t => d4BMCauchyPowerKernel z P.s (t + a)
  have hg : Integrable g := (integrable_d4BMCauchyPowerKernel z P).comp_add_right a
  have hp := GaloisForLFunctions.HTGeometry.integrableOn_Ioc_l1Periodization hg
  apply hp.congr
  filter_upwards with x
  exact (d4BM_l1Periodization_add_eq_translated _ _ _).symm

theorem d4BM_integral_unit_norm_shiftedCauchyPeriodization_le
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter)
    (a : ℝ) :
    (∫ x in Set.Ioc (0 : ℝ) 1,
      ‖GaloisForLFunctions.HTGeometry.l1Periodization
        (d4BMCauchyPowerKernel z P.s) (x + a)‖) ≤
      ∫ t : ℝ, ‖d4BMCauchyPowerKernel z P.s t‖ := by
  let g : ℝ → ℂ := fun t => d4BMCauchyPowerKernel z P.s (t + a)
  have hg : Integrable g := (integrable_d4BMCauchyPowerKernel z P).comp_add_right a
  have hp :=
    GaloisForLFunctions.HTGeometry.integral_unit_norm_l1Periodization_le_integral_norm hg
  have hperiod : ∀ x : ℝ,
      GaloisForLFunctions.HTGeometry.l1Periodization
          (d4BMCauchyPowerKernel z P.s) (x + a) =
        GaloisForLFunctions.HTGeometry.l1Periodization g x := by
    intro x
    exact d4BM_l1Periodization_add_eq_translated _ _ _
  have htranslate : (∫ t : ℝ, ‖g t‖) =
      ∫ t : ℝ, ‖d4BMCauchyPowerKernel z P.s t‖ := by
    exact (MeasureTheory.measurePreserving_add_right volume a).integral_comp
      (MeasurableEquiv.addRight a).measurableEmbedding
      (fun t : ℝ => ‖d4BMCauchyPowerKernel z P.s t‖)
  rw [show (fun x : ℝ =>
      ‖GaloisForLFunctions.HTGeometry.l1Periodization
        (d4BMCauchyPowerKernel z P.s) (x + a)‖) =
      fun x : ℝ => ‖GaloisForLFunctions.HTGeometry.l1Periodization g x‖ by
        funext x
        rw [hperiod]]
  exact hp.trans_eq htranslate

theorem d4BM_integrable_reducedResidueCauchyPeriodization
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter)
    (Q : CGLPositiveModulus) :
    Integrable (d4BMReducedResidueCauchyPeriodization z P Q)
      (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
  let A := {a : ZMod Q.value // IsUnit a}
  let F : A → ℝ → ℂ := fun a x =>
    GaloisForLFunctions.HTGeometry.l1Periodization
      (d4BMCauchyPowerKernel z P.s) (x + (a.1.val : ℝ) / Q.value)
  let μ : Measure ℝ := volume.restrict (Set.Ioc (0 : ℝ) 1)
  have hFint : ∀ a : A, Integrable (F a) μ := by
    intro a
    exact d4BM_integrable_shiftedCauchyPeriodization z P _
  have hseries : Integrable (fun x => ∑' a : A, F a x) μ :=
    GaloisForLFunctions.HTGeometry.integrable_tsum_of_summable_integral_norm
      hFint Summable.of_finite
  have hsum (x : ℝ) :
      d4BMReducedResidueCauchyPeriodization z P Q x = ∑' a : A, F a x := by
    unfold d4BMReducedResidueCauchyPeriodization
    rw [Finset.sum_subtype (p := fun a : ZMod Q.value => IsUnit a)
      ((Finset.univ : Finset (ZMod Q.value)).filter IsUnit)
      (by intro a; simp) (fun a : ZMod Q.value =>
        GaloisForLFunctions.HTGeometry.l1Periodization
          (d4BMCauchyPowerKernel z P.s) (x + (a.val : ℝ) / Q.value))]
    rw [tsum_fintype]
  apply hseries.congr
  filter_upwards with x
  exact (hsum x).symm

theorem d4BM_integral_unit_norm_reducedResiduePeriodization_le
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter)
    (Q : CGLPositiveModulus) :
    (∫ x in Set.Ioc (0 : ℝ) 1,
      ‖d4BMReducedResidueCauchyPeriodization z P Q x‖) ≤
      Q.value * ∫ t : ℝ, ‖d4BMCauchyPowerKernel z P.s t‖ := by
  let A := {a : ZMod Q.value // IsUnit a}
  let F : A → ℝ → ℂ := fun a x =>
    GaloisForLFunctions.HTGeometry.l1Periodization
      (d4BMCauchyPowerKernel z P.s) (x + (a.1.val : ℝ) / Q.value)
  let μ : Measure ℝ := volume.restrict (Set.Ioc (0 : ℝ) 1)
  have hFint : ∀ a : A, Integrable (F a) μ := by
    intro a
    exact d4BM_integrable_shiftedCauchyPeriodization z P _
  have hFsum : Summable fun a : A => ∫ x, ‖F a x‖ ∂μ := Summable.of_finite
  have hbound :=
    GaloisForLFunctions.HTGeometry.integral_norm_tsum_le_tsum_integral_norm
      hFint hFsum
  have hterm (a : A) :
      (∫ x, ‖F a x‖ ∂μ) ≤ ∫ t : ℝ, ‖d4BMCauchyPowerKernel z P.s t‖ := by
    exact d4BM_integral_unit_norm_shiftedCauchyPeriodization_le z P _
  have hsum (x : ℝ) :
      d4BMReducedResidueCauchyPeriodization z P Q x = ∑' a : A, F a x := by
    unfold d4BMReducedResidueCauchyPeriodization
    rw [Finset.sum_subtype (p := fun a : ZMod Q.value => IsUnit a)
      ((Finset.univ : Finset (ZMod Q.value)).filter IsUnit)
      (by intro a; simp) (fun a : ZMod Q.value =>
        GaloisForLFunctions.HTGeometry.l1Periodization
          (d4BMCauchyPowerKernel z P.s) (x + (a.val : ℝ) / Q.value))]
    rw [tsum_fintype]
  have hcard : Fintype.card A ≤ Q.value := by
    calc
      Fintype.card A ≤ Fintype.card (ZMod Q.value) :=
        Fintype.card_le_of_injective (fun a : A => a.1) Subtype.val_injective
      _ = Q.value := by simp
  calc
    (∫ x in Set.Ioc (0 : ℝ) 1,
        ‖d4BMReducedResidueCauchyPeriodization z P Q x‖) =
        ∫ x, ‖∑' a : A, F a x‖ ∂μ := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards with x
          rw [hsum]
    _ ≤ ∑' a : A, ∫ x, ‖F a x‖ ∂μ := hbound
    _ ≤ ∑' _a : A, ∫ t : ℝ, ‖d4BMCauchyPowerKernel z P.s t‖ := by
      rw [tsum_fintype, tsum_fintype]
      exact Finset.sum_le_sum fun a _ => hterm a
    _ = (Fintype.card A : ℝ) *
        ∫ t : ℝ, ‖d4BMCauchyPowerKernel z P.s t‖ := by simp
    _ ≤ Q.value * ∫ t : ℝ, ‖d4BMCauchyPowerKernel z P.s t‖ := by
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard)
        (integral_nonneg fun _ => norm_nonneg _)

theorem d4BM_norm_positiveCuspScale
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter)
    (Q : CGLPositiveModulus) :
    ‖(z.y : ℂ) ^ P.s * ((Q.value : ℝ) : ℂ) ^ (-(2 * P.s))‖ =
      z.y ^ P.s.re * (Q.value : ℝ) ^ (-(2 * P.s.re)) := by
  rw [norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos z.y_pos,
    Complex.norm_cpow_eq_rpow_re_of_pos (by exact_mod_cast Q.positive : (0 : ℝ) < Q.value)]
  congr 1
  simp

theorem d4BM_integrable_positivePrimitiveCuspSlice
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter)
    (Q : CGLPositiveModulus) :
    Integrable (d4BMPositivePrimitiveCuspSlice z P Q)
      (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
  unfold d4BMPositivePrimitiveCuspSlice
  exact (d4BM_integrable_reducedResidueCauchyPeriodization z P Q).const_mul _

theorem d4BM_integral_unit_norm_positivePrimitiveCuspSlice_le
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter)
    (Q : CGLPositiveModulus) :
    (∫ x in Set.Ioc (0 : ℝ) 1,
      ‖d4BMPositivePrimitiveCuspSlice z P Q x‖) ≤
      (z.y ^ P.s.re * (Q.value : ℝ) ^ (-(2 * P.s.re - 1))) *
        ∫ t : ℝ, ‖d4BMCauchyPowerKernel z P.s t‖ := by
  let C : ℂ := (z.y : ℂ) ^ P.s * ((Q.value : ℝ) : ℂ) ^ (-(2 * P.s))
  let I : ℝ := ∫ t : ℝ, ‖d4BMCauchyPowerKernel z P.s t‖
  have hred := d4BM_integral_unit_norm_reducedResiduePeriodization_le z P Q
  have hI : 0 ≤ I := integral_nonneg fun _ => norm_nonneg _
  have hC : 0 ≤ ‖C‖ := norm_nonneg _
  have hQ : (0 : ℝ) < Q.value := by exact_mod_cast Q.positive
  have hscale : ‖C‖ * (Q.value : ℝ) =
      z.y ^ P.s.re * (Q.value : ℝ) ^ (-(2 * P.s.re - 1)) := by
    rw [show ‖C‖ = z.y ^ P.s.re * (Q.value : ℝ) ^ (-(2 * P.s.re)) by
      exact d4BM_norm_positiveCuspScale z P Q]
    have hqscale : (Q.value : ℝ) ^ (-(2 * P.s.re)) * (Q.value : ℝ) =
        (Q.value : ℝ) ^ (-(2 * P.s.re - 1)) := by
      calc
        (Q.value : ℝ) ^ (-(2 * P.s.re)) * (Q.value : ℝ) =
            (Q.value : ℝ) ^ (-(2 * P.s.re)) * (Q.value : ℝ) ^ (1 : ℝ) := by
              rw [Real.rpow_one]
        _ = (Q.value : ℝ) ^ (-(2 * P.s.re) + 1) :=
          (Real.rpow_add hQ _ _).symm
        _ = (Q.value : ℝ) ^ (-(2 * P.s.re - 1)) := by
          congr 1
          ring
    rw [mul_assoc, hqscale]
  change (∫ x in Set.Ioc (0 : ℝ) 1,
      ‖C * d4BMReducedResidueCauchyPeriodization z P Q x‖) ≤ _
  rw [show (fun x : ℝ =>
      ‖C * d4BMReducedResidueCauchyPeriodization z P Q x‖) =
      fun x : ℝ => ‖C‖ * ‖d4BMReducedResidueCauchyPeriodization z P Q x‖ by
        funext x
        rw [norm_mul]]
  rw [MeasureTheory.integral_const_mul]
  calc
    ‖C‖ * (∫ x in Set.Ioc (0 : ℝ) 1,
        ‖d4BMReducedResidueCauchyPeriodization z P Q x‖) ≤
        ‖C‖ * ((Q.value : ℝ) * I) := mul_le_mul_of_nonneg_left hred hC
    _ = (‖C‖ * (Q.value : ℝ)) * I := by ring
    _ = (z.y ^ P.s.re * (Q.value : ℝ) ^ (-(2 * P.s.re - 1))) * I := by
      rw [hscale]

theorem d4BM_summable_integral_unit_norm_positivePrimitiveCuspSlice
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) :
    Summable fun Q : ℕ+ =>
      ∫ x in Set.Ioc (0 : ℝ) 1,
        ‖d4BMPositivePrimitiveCuspSlice z P (d4BMPositiveModulusOfPNat Q) x‖ := by
  let sigma : ℝ := 2 * P.s.re - 1
  let C : ℝ := z.y ^ P.s.re *
    ∫ t : ℝ, ‖d4BMCauchyPowerKernel z P.s t‖
  have hsigma : 1 < sigma := by
    dsimp only [sigma]
    linarith [P.re_gt_one]
  have hnat : Summable fun n : ℕ => ((n : ℝ) ^ sigma)⁻¹ :=
    Real.summable_nat_rpow_inv.mpr hsigma
  have hnat' : Summable fun n : ℕ => (n : ℝ) ^ (-sigma) := by
    refine hnat.congr fun n => ?_
    rw [Real.rpow_neg (by positivity)]
  have hbase : Summable fun Q : ℕ+ => (Q : ℝ) ^ (-sigma) :=
    hnat'.comp_injective (fun _ _ hab => PNat.coe_injective hab)
  have hmaj : Summable fun Q : ℕ+ => C * (Q : ℝ) ^ (-sigma) :=
    hbase.mul_left C
  refine Summable.of_nonneg_of_le
    (fun Q => integral_nonneg fun _ => norm_nonneg _) (fun Q => ?_) hmaj
  have h := d4BM_integral_unit_norm_positivePrimitiveCuspSlice_le z P
    (d4BMPositiveModulusOfPNat Q)
  change (∫ x in Set.Ioc (0 : ℝ) 1,
      ‖d4BMPositivePrimitiveCuspSlice z P (d4BMPositiveModulusOfPNat Q) x‖) ≤
      (z.y ^ P.s.re * (Q : ℝ) ^ (-(2 * P.s.re - 1))) *
        ∫ t : ℝ, ‖d4BMCauchyPowerKernel z P.s t‖ at h
  calc
    (∫ x in Set.Ioc (0 : ℝ) 1,
        ‖d4BMPositivePrimitiveCuspSlice z P (d4BMPositiveModulusOfPNat Q) x‖) ≤
        (z.y ^ P.s.re * (Q : ℝ) ^ (-sigma)) *
          ∫ t : ℝ, ‖d4BMCauchyPowerKernel z P.s t‖ := by
            simpa only [sigma] using h
    _ = C * (Q : ℝ) ^ (-sigma) := by
      dsimp only [C]
      ring

def d4BMHorizontalCoordinate
    (z : D4BMUpperHalfPlaneCoordinate) (x : ℝ) : D4BMUpperHalfPlaneCoordinate where
  x := x
  y := z.y
  y_pos := z.y_pos

@[simp] theorem d4BMHorizontalCoordinate_x
    (z : D4BMUpperHalfPlaneCoordinate) (x : ℝ) :
    (d4BMHorizontalCoordinate z x).x = x := rfl

@[simp] theorem d4BMHorizontalCoordinate_y
    (z : D4BMUpperHalfPlaneCoordinate) (x : ℝ) :
    (d4BMHorizontalCoordinate z x).y = z.y := rfl

theorem d4BM_positivePrimitiveCuspSlice_horizontalCoordinate
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter)
    (Q : CGLPositiveModulus) (x : ℝ) :
    d4BMPositivePrimitiveCuspSlice (d4BMHorizontalCoordinate z x) P Q x =
      d4BMPositivePrimitiveCuspSlice z P Q x := rfl

def d4BMRawEisensteinHorizontalFunction
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) (x : ℝ) : ℂ :=
  d4BMRawEisensteinPoincareSeries (d4BMHorizontalCoordinate z x) P

theorem d4BM_rawEisensteinHorizontalFunction_eq_constant_add_positiveSlices
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) (x : ℝ) :
    d4BMRawEisensteinHorizontalFunction z P x =
      (z.y : ℂ) ^ P.s +
        ∑' Q : ℕ+,
          d4BMPositivePrimitiveCuspSlice z P (d4BMPositiveModulusOfPNat Q) x := by
  have h := d4BM_rawEisensteinPoincareSeries_eq_constant_add_positiveSlices
    (d4BMHorizontalCoordinate z x) P
  simpa only [d4BMRawEisensteinHorizontalFunction, d4BMHorizontalCoordinate_y,
    d4BMHorizontalCoordinate_x,
    d4BM_positivePrimitiveCuspSlice_horizontalCoordinate] using h

theorem d4BM_actualRawPoincare_fourier_integral_tsum_exchange
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) (m : ℤ) :
    (∫ x in Set.Ioc (0 : ℝ) 1,
      fourier (-m) (x : UnitAddCircle) * d4BMRawEisensteinHorizontalFunction z P x) =
      (∫ x in Set.Ioc (0 : ℝ) 1,
        fourier (-m) (x : UnitAddCircle) * (z.y : ℂ) ^ P.s) +
        ∑' Q : ℕ+,
          ∫ x in Set.Ioc (0 : ℝ) 1,
            fourier (-m) (x : UnitAddCircle) *
              d4BMPositivePrimitiveCuspSlice z P (d4BMPositiveModulusOfPNat Q) x := by
  let e : ℝ → ℂ := fun x => fourier (-m) (x : UnitAddCircle)
  let S : ℕ+ → ℝ → ℂ := fun Q x =>
    d4BMPositivePrimitiveCuspSlice z P (d4BMPositiveModulusOfPNat Q) x
  let F : ℕ+ → ℝ → ℂ := fun Q x => e x * S Q x
  let μ : Measure ℝ := volume.restrict (Set.Ioc (0 : ℝ) 1)
  have hecont : Continuous e := by
    dsimp only [e]
    fun_prop
  have henorm : ∀ x : ℝ, ‖e x‖ = 1 := by
    intro x
    simp [e, Complex.norm_exp]
  have hSint : ∀ Q : ℕ+, Integrable (S Q) μ := by
    intro Q
    exact d4BM_integrable_positivePrimitiveCuspSlice z P
      (d4BMPositiveModulusOfPNat Q)
  have hFint : ∀ Q : ℕ+, Integrable (F Q) μ := by
    intro Q
    have h := (hSint Q).bdd_mul hecont.aestronglyMeasurable.restrict
      (Eventually.of_forall fun x => (henorm x).le)
    apply h.congr
    filter_upwards with x
    simp only [F, S]
  have hnormEq (Q : ℕ+) :
      (∫ x, ‖F Q x‖ ∂μ) = ∫ x, ‖S Q x‖ ∂μ := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards with x
    rw [norm_mul, henorm, one_mul]
  have hSsum : Summable fun Q : ℕ+ => ∫ x, ‖S Q x‖ ∂μ := by
    exact d4BM_summable_integral_unit_norm_positivePrimitiveCuspSlice z P
  have hFsum : Summable fun Q : ℕ+ => ∫ x, ‖F Q x‖ ∂μ :=
    hSsum.congr fun Q => (hnormEq Q).symm
  have htsumInt : Integrable (fun x => ∑' Q : ℕ+, F Q x) μ :=
    GaloisForLFunctions.HTGeometry.integrable_tsum_of_summable_integral_norm
      hFint hFsum
  have hexchange :=
    GaloisForLFunctions.HTGeometry.integral_tsum_eq_tsum_integral_of_summable_integral_norm
      hFint hFsum
  have hconst : Integrable (fun x => e x * (z.y : ℂ) ^ P.s) μ := by
    have hc : Integrable (fun _ : ℝ => ((z.y : ℂ) ^ P.s : ℂ)) μ :=
      integrable_const _
    have h := hc.bdd_mul
      hecont.aestronglyMeasurable.restrict
      (Eventually.of_forall fun x => (henorm x).le)
    apply h.congr
    filter_upwards with x
    ring
  have hfun : (fun x : ℝ =>
      fourier (-m) (x : UnitAddCircle) * d4BMRawEisensteinHorizontalFunction z P x) =
      fun x : ℝ => e x * (z.y : ℂ) ^ P.s + ∑' Q : ℕ+, F Q x := by
    funext x
    rw [d4BM_rawEisensteinHorizontalFunction_eq_constant_add_positiveSlices]
    change e x * ((z.y : ℂ) ^ P.s + ∑' Q : ℕ+, S Q x) =
      e x * (z.y : ℂ) ^ P.s + ∑' Q : ℕ+, e x * S Q x
    rw [mul_add, tsum_mul_left]
  rw [hfun]
  change (∫ x, (e x * (z.y : ℂ) ^ P.s + ∑' Q : ℕ+, F Q x) ∂μ) = _
  rw [MeasureTheory.integral_add hconst htsumInt, hexchange]

theorem d4BM_actualRawPoincare_fourierCoefficient_eq_sliceFormula
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) (m : ℤ) :
    (∫ x in Set.Ioc (0 : ℝ) 1,
      fourier (-m) (x : UnitAddCircle) * d4BMRawEisensteinHorizontalFunction z P x) =
      (∫ x in Set.Ioc (0 : ℝ) 1,
        fourier (-m) (x : UnitAddCircle) * (z.y : ℂ) ^ P.s) +
        ∑' Q : ℕ+,
          (((z.y : ℂ) ^ P.s *
              ((((d4BMPositiveModulusOfPNat Q).value : ℝ) : ℂ)) ^ (-(2 * P.s))) *
            cglRamanujanAdditiveSum (d4BMPositiveModulusOfPNat Q)
              (m : ZMod (d4BMPositiveModulusOfPNat Q).value) *
            𝓕 (d4BMCauchyPowerKernel z P.s) (m : ℝ)) := by
  rw [d4BM_actualRawPoincare_fourier_integral_tsum_exchange]
  congr 1
  apply tsum_congr
  intro Q
  exact d4BM_positivePrimitiveCuspSlice_fourierCoefficient z P
    (d4BMPositiveModulusOfPNat Q) m

theorem d4BM_integral_unit_fourier_character (m : ℤ) :
    (∫ x in Set.Ioc (0 : ℝ) 1, fourier (-m) (x : UnitAddCircle)) =
      if m = 0 then 1 else 0 := by
  rw [← intervalIntegral.integral_of_le zero_le_one]
  have hfun : (fun x : ℝ => fourier (-m) (x : UnitAddCircle)) =
      fun x : ℝ => RHTower.Sieve.circleFreq (((-m : ℤ) : ℝ) * x) := by
    funext x
    rw [fourier_coe_apply]
    unfold RHTower.Sieve.circleFreq
    congr 1
    push_cast
    ring
  rw [hfun, RHTower.Sieve.integral_circleFreq_intCast]
  simp

theorem d4BM_integral_unit_fourier_character_mul_constant
    (m : ℤ) (C : ℂ) :
    (∫ x in Set.Ioc (0 : ℝ) 1, fourier (-m) (x : UnitAddCircle) * C) =
      if m = 0 then C else 0 := by
  rw [MeasureTheory.integral_mul_const, d4BM_integral_unit_fourier_character]
  split_ifs <;> simp_all

theorem d4BM_actualRawPoincare_positiveFourierCoefficient_eq_divisorZeta
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter)
    (F : D4BMPositiveFourierFrequency) :
    (∫ x in Set.Ioc (0 : ℝ) 1,
      fourier (-(F.value : ℤ)) (x : UnitAddCircle) *
        d4BMRawEisensteinHorizontalFunction z P x) =
      ((z.y : ℂ) ^ P.s *
        𝓕 (d4BMCauchyPowerKernel z P.s) (F.value : ℝ)) *
        (d4BMRamanujanDivisorPolynomial F.value (2 * P.s) /
          riemannZeta (2 * P.s)) := by
  rw [d4BM_actualRawPoincare_fourierCoefficient_eq_sliceFormula]
  rw [d4BM_integral_unit_fourier_character_mul_constant]
  have hm : (F.value : ℤ) ≠ 0 := by exact_mod_cast F.positive.ne'
  rw [if_neg hm, zero_add]
  let A : ℂ := (z.y : ℂ) ^ P.s *
    𝓕 (d4BMCauchyPowerKernel z P.s) (F.value : ℝ)
  calc
    (∑' Q : ℕ+,
        (((z.y : ℂ) ^ P.s *
            ((((d4BMPositiveModulusOfPNat Q).value : ℝ) : ℂ)) ^ (-(2 * P.s))) *
          cglRamanujanAdditiveSum (d4BMPositiveModulusOfPNat Q)
            ((F.value : ℤ) : ZMod (d4BMPositiveModulusOfPNat Q).value) *
          𝓕 (d4BMCauchyPowerKernel z P.s) ((F.value : ℤ) : ℝ))) =
        ∑' Q : ℕ+, A * d4BMRamanujanPNatTerm F P Q := by
          apply tsum_congr
          intro Q
          have hram : d4BMRamanujanPNatTerm F P Q =
              cglRamanujanAdditiveSum (d4BMPositiveModulusOfPNat Q)
                  (F.value : ZMod (d4BMPositiveModulusOfPNat Q).value) *
                ((((d4BMPositiveModulusOfPNat Q).value : ℝ) : ℂ)) ^
                  (-(2 * P.s)) := by
            unfold d4BMRamanujanPNatTerm d4BMRamanujanNaturalCoefficient
            split
            · congr
            · rename_i hq
              exact (hq Q.2).elim
          dsimp only [A]
          rw [hram]
          push_cast
          ring
    _ = A * ∑' Q : ℕ+, d4BMRamanujanPNatTerm F P Q := tsum_mul_left
    _ = A * (d4BMRamanujanDivisorPolynomial F.value (2 * P.s) /
        riemannZeta (2 * P.s)) := by
      rw [tsum_d4BMRamanujanPNatTerm_eq_div_riemannZeta]
    _ = ((z.y : ℂ) ^ P.s *
        𝓕 (d4BMCauchyPowerKernel z P.s) (F.value : ℝ)) *
        (d4BMRamanujanDivisorPolynomial F.value (2 * P.s) /
          riemannZeta (2 * P.s)) := rfl

def d4BMCompletedEisensteinHorizontalFunction
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) (x : ℝ) : ℂ :=
  d4BMCompletedEisensteinPoincareSeries (d4BMHorizontalCoordinate z x) P

theorem d4BM_completedEisensteinHorizontalFunction_eq_lambda_mul_raw
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) (x : ℝ) :
    d4BMCompletedEisensteinHorizontalFunction z P x =
      reflectedCompletedLambda (2 * P.s) *
        d4BMRawEisensteinHorizontalFunction z P x := rfl

theorem d4BM_actualCompletedPoincare_positiveFourierCoefficient_eq_completedDivisorZeta
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter)
    (F : D4BMPositiveFourierFrequency) :
    (∫ x in Set.Ioc (0 : ℝ) 1,
      fourier (-(F.value : ℤ)) (x : UnitAddCircle) *
        d4BMCompletedEisensteinHorizontalFunction z P x) =
      reflectedCompletedLambda (2 * P.s) *
        (((z.y : ℂ) ^ P.s *
          𝓕 (d4BMCauchyPowerKernel z P.s) (F.value : ℝ)) *
          (d4BMRamanujanDivisorPolynomial F.value (2 * P.s) /
            riemannZeta (2 * P.s))) := by
  rw [show (fun x : ℝ =>
      fourier (-(F.value : ℤ)) (x : UnitAddCircle) *
        d4BMCompletedEisensteinHorizontalFunction z P x) =
      fun x : ℝ => reflectedCompletedLambda (2 * P.s) *
        (fourier (-(F.value : ℤ)) (x : UnitAddCircle) *
          d4BMRawEisensteinHorizontalFunction z P x) by
    funext x
    rw [d4BM_completedEisensteinHorizontalFunction_eq_lambda_mul_raw]
    ring]
  rw [MeasureTheory.integral_const_mul]
  rw [d4BM_actualRawPoincare_positiveFourierCoefficient_eq_divisorZeta]

theorem d4BM_completedDivisorZeta_bessel_simplification
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter)
    (F : D4BMPositiveFourierFrequency) :
    reflectedCompletedLambda (2 * P.s) *
        (((z.y : ℂ) ^ P.s *
          𝓕 (d4BMCauchyPowerKernel z P.s) (F.value : ℝ)) *
          (d4BMRamanujanDivisorPolynomial F.value (2 * P.s) /
            riemannZeta (2 * P.s))) =
      2 * (z.y : ℂ) ^ P.s *
        ((((F.value : ℝ) / z.y : ℝ) : ℂ)) ^ (P.s - 1 / 2) *
        d4BMRamanujanDivisorPolynomial F.value (2 * P.s) *
        GaloisForLFunctions.HTGeometry.modifiedBesselKOrder
          (2 * Real.pi * z.y * F.value) (P.s - 1 / 2) := by
  have hn : (0 : ℝ) < F.value := by exact_mod_cast F.positive
  have hfourier := fourier_d4BMCauchyPowerKernel_ne_zero z P hn.ne'
  rw [hfourier, abs_of_pos hn]
  rw [reflectedCompletedLambda_eq]
  have hhalf : (2 * P.s) / 2 = P.s := by ring
  have hnegHalf : -(2 * P.s) / 2 = -P.s := by ring
  rw [hhalf, hnegHalf]
  have hGamma : Complex.Gamma P.s ≠ 0 := by
    apply Complex.Gamma_ne_zero
    intro k hk
    have hre := congrArg Complex.re hk
    simp only [Complex.neg_re, Complex.natCast_re] at hre
    nlinarith [P.re_gt_one, Nat.cast_nonneg (α := ℝ) k]
  have hpiPow : (Real.pi : ℂ) ^ P.s ≠ 0 := by
    apply Complex.cpow_ne_zero_iff.2
    exact Or.inl (by exact_mod_cast Real.pi_ne_zero)
  have hw : 1 < (2 * P.s).re := by
    norm_num [Complex.mul_re]
    linarith [P.re_gt_one]
  have hinv := LSeries_moebiusCoeff_mul_riemannZeta hw
  have hzeta : riemannZeta (2 * P.s) ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at hinv
    exact zero_ne_one hinv
  rw [Complex.cpow_neg]
  field_simp [hGamma, hpiPow, hzeta]

theorem d4BM_cuspScale_divisorPolynomial_eq_sqrt_whittakerCoefficient
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter)
    (F : D4BMPositiveFourierFrequency) :
    (z.y : ℂ) ^ P.s *
        ((((F.value : ℝ) / z.y : ℝ) : ℂ)) ^ (P.s - 1 / 2) *
        d4BMRamanujanDivisorPolynomial F.value (2 * P.s) =
      (Real.sqrt z.y : ℂ) *
        d4BMCompletedEisensteinWhittakerCoefficient (P.s - 1 / 2)
          ⟨F.value, F.positive⟩ := by
  let u : ℂ := P.s - 1 / 2
  have hn : (0 : ℝ) < F.value := by exact_mod_cast F.positive
  have hy : (0 : ℝ) < z.y := z.y_pos
  have hdiv : d4BMRamanujanDivisorPolynomial F.value (2 * P.s) =
      ∑ d ∈ F.value.divisors, (d : ℂ) ^ (-2 * u) := by
    unfold d4BMRamanujanDivisorPolynomial
    apply Finset.sum_congr rfl
    intro d hd
    have hdpos : 0 < d := Nat.pos_of_mem_divisors hd
    have hdne : (d : ℂ) ≠ 0 := by exact_mod_cast hdpos.ne'
    calc
      (d : ℂ) * (d : ℂ) ^ (-(2 * P.s)) =
          (d : ℂ) ^ (1 : ℂ) * (d : ℂ) ^ (-(2 * P.s)) := by
            rw [Complex.cpow_one]
      _ = (d : ℂ) ^ ((1 : ℂ) + (-(2 * P.s))) :=
        (Complex.cpow_add _ _ hdne).symm
      _ = (d : ℂ) ^ (-2 * u) := by
        congr 1
        dsimp only [u]
        ring
  have hratio := RHTower.Sieve.ofReal_div_cpow_eq_mul_cpow_neg
    hn hy u
  have hyne : (z.y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  have hsqrt : ((Real.sqrt z.y : ℝ) : ℂ) =
      (z.y : ℂ) ^ ((1 : ℂ) / 2) := by
    rw [show ((1 : ℂ) / 2) = (((1 / 2 : ℝ)) : ℂ) by norm_num,
      ← Complex.ofReal_cpow hy.le]
    norm_cast
    exact Real.sqrt_eq_rpow z.y
  have hypow : (z.y : ℂ) ^ P.s * (z.y : ℂ) ^ (-u) =
      (Real.sqrt z.y : ℂ) := by
    rw [← Complex.cpow_add _ _ hyne]
    rw [show P.s + -u = (1 : ℂ) / 2 by dsimp only [u]; ring]
    exact hsqrt.symm
  rw [show P.s - 1 / 2 = u by rfl, hratio, hdiv]
  unfold d4BMCompletedEisensteinWhittakerCoefficient
  push_cast
  calc
    (z.y : ℂ) ^ P.s *
          ((F.value : ℂ) ^ u * (z.y : ℂ) ^ (-u)) *
          ∑ d ∈ F.value.divisors, (d : ℂ) ^ (-2 * u) =
        ((z.y : ℂ) ^ P.s * (z.y : ℂ) ^ (-u)) *
          ((F.value : ℂ) ^ u *
            ∑ d ∈ F.value.divisors, (d : ℂ) ^ (-2 * u)) := by ring
    _ = (Real.sqrt z.y : ℂ) *
          ((F.value : ℂ) ^ u *
            ∑ d ∈ F.value.divisors, (d : ℂ) ^ (-2 * u)) := by rw [hypow]

theorem d4BM_actualCompletedPoincare_positiveFourierCoefficient_eq_canonicalWhittaker
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter)
    (F : D4BMPositiveFourierFrequency) :
    (∫ x in Set.Ioc (0 : ℝ) 1,
      fourier (-(F.value : ℤ)) (x : UnitAddCircle) *
        d4BMCompletedEisensteinHorizontalFunction z P x) =
      2 * d4BMCompletedEisensteinWhittakerCoefficient (P.s - 1 / 2)
          ⟨F.value, F.positive⟩ *
        (Real.sqrt z.y : ℂ) *
        GaloisForLFunctions.HTGeometry.modifiedBesselKOrder
          (2 * Real.pi * z.y * F.value) (P.s - 1 / 2) := by
  rw [d4BM_actualCompletedPoincare_positiveFourierCoefficient_eq_completedDivisorZeta]
  rw [d4BM_completedDivisorZeta_bessel_simplification]
  let K : ℂ := GaloisForLFunctions.HTGeometry.modifiedBesselKOrder
    (2 * Real.pi * z.y * F.value) (P.s - 1 / 2)
  have hscale := d4BM_cuspScale_divisorPolynomial_eq_sqrt_whittakerCoefficient
    z P F
  change 2 * (z.y : ℂ) ^ P.s *
      ((((F.value : ℝ) / z.y : ℝ) : ℂ)) ^ (P.s - 1 / 2) *
      d4BMRamanujanDivisorPolynomial F.value (2 * P.s) * K = _
  calc
    2 * (z.y : ℂ) ^ P.s *
          ((((F.value : ℝ) / z.y : ℝ) : ℂ)) ^ (P.s - 1 / 2) *
          d4BMRamanujanDivisorPolynomial F.value (2 * P.s) * K =
        2 * (((z.y : ℂ) ^ P.s *
          ((((F.value : ℝ) / z.y : ℝ) : ℂ)) ^ (P.s - 1 / 2) *
          d4BMRamanujanDivisorPolynomial F.value (2 * P.s))) * K := by ring
    _ = 2 * ((Real.sqrt z.y : ℂ) *
        d4BMCompletedEisensteinWhittakerCoefficient (P.s - 1 / 2)
          ⟨F.value, F.positive⟩) * K := by rw [hscale]
    _ = 2 * d4BMCompletedEisensteinWhittakerCoefficient (P.s - 1 / 2)
          ⟨F.value, F.positive⟩ *
        (Real.sqrt z.y : ℂ) * K := by ring

end RHTower
