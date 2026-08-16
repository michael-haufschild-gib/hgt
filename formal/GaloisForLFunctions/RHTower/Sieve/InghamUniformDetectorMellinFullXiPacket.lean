import GaloisForLFunctions.RHTower.Sieve.InghamUniformDetectorMellinBufferedTail
import GaloisForLFunctions.RHTower.XiGuinandWeilSpectralRectangle
import GaloisForLFunctions.RHTower.XiMassCriticalDiagonalPrimeCoronaZeroDensity

/-!
# Complete low-real and shifted-high Xi Mellin packets for Route T

The density packet controls zeros with real part at least `7/10` only through ordinate
`X - 2`.  This module closes both complementary regions for the buffered physical Mellin kernel:

* every copy with `Re rho < 7/10` and `|Im rho| ≤ X - 2` has total mass `o(1)`, using only the
  unconditional global `O(X log X)` Xi count and the exact residual power `X^(-1/299)`;
* every copy with `|Im rho| ≥ X - 2` has total mass `o(1)`, using order-`2001` Mellin decay and the
  buffered-frequency residual power `X^(-1/500)`.

Thus the two-unit top band omitted by the common detector rectangle is no longer an obstruction.
-/

open Complex Filter Metric Set Finset Topology

namespace RHTower.Sieve

noncomputable section

/-- Multiplicity copies with ordinate in the common detector height range. -/
def inghamRouteTXiLowOrdinatePacket (X : ℕ) : Finset RHTower.XiZeroCopy :=
  RHTower.xiZeroCopyClosedRectangle
    (((2 - (X : ℝ) : ℝ) : ℂ) + ((-(1 / 2 : ℝ) : ℝ) : ℂ) * I)
    ((((X : ℝ) - 2 : ℝ) : ℂ) + (((1 / 2 : ℝ) : ℝ) : ℂ) * I)

/-- The spectral rectangle is exactly the copied Xi divisor below ordinate `X - 2`. -/
theorem mem_inghamRouteTXiLowOrdinatePacket_iff
    {X : ℕ} (hX : 4 ≤ X) (q : RHTower.XiZeroCopy) :
    q ∈ inghamRouteTXiLowOrdinatePacket X ↔
      |((q.1 : RHTower.XiDivisorSupport) : ℂ).im| ≤ (X : ℝ) - 2 := by
  have horder : (2 : ℝ) - X ≤ (X : ℝ) - 2 := by
    have hXR : (4 : ℝ) ≤ X := by exact_mod_cast hX
    linarith
  have hspectralRe : (RHTower.xiSpectralPoint q).re =
      ((q.1 : RHTower.XiDivisorSupport) : ℂ).im := by
    simp [RHTower.xiSpectralPoint, Complex.mul_re]
  have hspectralIm : (RHTower.xiSpectralPoint q).im =
      1 / 2 - ((q.1 : RHTower.XiDivisorSupport) : ℂ).re := by
    simp [RHTower.xiSpectralPoint, Complex.mul_im]
  have hstrip := RHTower.xi_divisor_support_re_mem_open_unit q.1
  rw [inghamRouteTXiLowOrdinatePacket, RHTower.mem_xiZeroCopyClosedRectangle]
  constructor
  · intro hq
    have hcoords := Complex.mem_reProdIm.mp hq
    have hrecoords : (RHTower.xiSpectralPoint q).re ∈
        Set.Icc ((2 : ℝ) - X) ((X : ℝ) - 2) := by
      simpa [uIcc_of_le horder] using hcoords.1
    rw [← hspectralRe]
    exact abs_le.mpr ⟨by linarith [hrecoords.1], hrecoords.2⟩
  · intro hq
    apply Complex.mem_reProdIm.mpr
    constructor
    · simpa [uIcc_of_le horder, hspectralRe] using (abs_le.mp hq)
    · have hy : (RHTower.xiSpectralPoint q).im ∈
          Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ) := by
        rw [hspectralIm]
        constructor <;> linarith
      simpa [uIcc_of_le (by norm_num : (-(1 / 2 : ℝ)) ≤ 1 / 2)] using hy

/-- The bounded-height Xi packet strictly left of the density threshold `7/10`. -/
def inghamRouteTXiLowRealPacket (X : ℕ) : Finset RHTower.XiZeroCopy :=
  (inghamRouteTXiLowOrdinatePacket X).filter fun q =>
    ((q.1 : RHTower.XiDivisorSupport) : ℂ).re < 7 / 10

/-- Buffered normalized Mellin value of the low-real packet. -/
def inghamRouteTBufferedXiMellinLowRealPacket (X : ℕ) : ℂ :=
  ∑ q ∈ inghamRouteTXiLowRealPacket X,
    routeTNormalizedSmoothWindowMellin
      (inghamRouteTMellinPhysicalCenter X)
      (inghamRouteTMellinBufferedPhysicalWidth X)
      (q.1 : ℂ)

private theorem inghamRouteTXiLowRealPacket_support_mem_closedBall
    {X : ℕ} (hX : 4 ≤ X) {q : RHTower.XiZeroCopy}
    (hq : q ∈ inghamRouteTXiLowRealPacket X) :
    ((q.1 : RHTower.XiDivisorSupport) : ℂ) ∈ closedBall (2 : ℂ) (X : ℝ) := by
  have hrect := (RHTower.mem_xiZeroCopyClosedRectangle.mp
    (Finset.mem_filter.mp hq).1)
  have hcoords := Complex.mem_reProdIm.mp hrect
  have horder : (2 : ℝ) - X ≤ (X : ℝ) - 2 := by
    have hXR : (4 : ℝ) ≤ X := by exact_mod_cast hX
    linarith
  have hrecoords : (RHTower.xiSpectralPoint q).re ∈
      Set.Icc ((2 : ℝ) - X) ((X : ℝ) - 2) := by
    simpa [inghamRouteTXiLowOrdinatePacket, uIcc_of_le horder] using hcoords.1
  have hspectralRe : (RHTower.xiSpectralPoint q).re =
      ((q.1 : RHTower.XiDivisorSupport) : ℂ).im := by
    simp [RHTower.xiSpectralPoint, Complex.mul_re]
  have him : |((q.1 : RHTower.XiDivisorSupport) : ℂ).im| ≤ (X : ℝ) - 2 := by
    rw [← hspectralRe]
    exact abs_le.mpr ⟨by linarith [hrecoords.1], hrecoords.2⟩
  have hstrip := RHTower.xi_divisor_support_re_mem_open_unit q.1
  have hre : |(((q.1 : RHTower.XiDivisorSupport) : ℂ) - 2).re| ≤ 2 := by
    rw [Complex.sub_re]
    norm_num
    rw [abs_le]
    constructor <;> linarith
  have himsub : |(((q.1 : RHTower.XiDivisorSupport) : ℂ) - 2).im| ≤
      (X : ℝ) - 2 := by
    simpa using him
  rw [mem_closedBall, dist_eq_norm]
  calc
    ‖((q.1 : RHTower.XiDivisorSupport) : ℂ) - 2‖ ≤
        |(((q.1 : RHTower.XiDivisorSupport) : ℂ) - 2).re| +
          |(((q.1 : RHTower.XiDivisorSupport) : ℂ) - 2).im| :=
      Complex.norm_le_abs_re_add_abs_im _
    _ ≤ 2 + ((X : ℝ) - 2) := add_le_add hre himsub
    _ = (X : ℝ) := by ring

/-- Global Xi counting bounds the exact multiplicity-copy packet. -/
theorem card_inghamRouteTXiLowRealPacket_le_global
    {X : ℕ} (hX : 4 ≤ X) :
    ((inghamRouteTXiLowRealPacket X).card : ℝ) ≤
      RHTower.xiZeroCountEnvelopeConstant * (1 + (X : ℝ)) *
        Real.log (2 + (X : ℝ)) := by
  have hdisc := RHTower.card_le_xiBallOrderSum_of_support_mem
    (inghamRouteTXiLowRealPacket X)
    (fun q hq => inghamRouteTXiLowRealPacket_support_mem_closedBall hX hq)
  exact hdisc.trans (RHTower.xiBallOrderSum_le_zeroCountEnvelope (X : ℝ) (by
    exact_mod_cast (show 1 ≤ X by omega)))

/-- The low-real packet has the exact pre-counting weight `X^(-300/299)`. -/
theorem norm_inghamRouteTBufferedXiMellinLowRealPacket_le
    {X : ℕ} (hX : 4 ≤ X) :
    ‖inghamRouteTBufferedXiMellinLowRealPacket X‖ ≤
      RHTower.xiZeroCountEnvelopeConstant * (1 + (X : ℝ)) *
        Real.log (2 + (X : ℝ)) * (X : ℝ) ^ (-(300 / 299 : ℝ)) := by
  have hX1 : 1 ≤ X := by omega
  have hXR1 : (1 : ℝ) ≤ X := by exact_mod_cast hX1
  have hNpos := inghamRouteTMellinPhysicalCenter_pos hX1
  have hNone := inghamRouteTMellinPhysicalCenter_one_le hX1
  have hHpos := inghamRouteTMellinBufferedPhysicalWidth_pos hX1
  let E : ℝ := (X : ℝ) ^ (-(300 / 299 : ℝ))
  have hpoint : ∀ q ∈ inghamRouteTXiLowRealPacket X,
      ‖routeTNormalizedSmoothWindowMellin
        (inghamRouteTMellinPhysicalCenter X)
        (inghamRouteTMellinBufferedPhysicalWidth X) (q.1 : ℂ)‖ ≤ E := by
    intro q hq
    have hrelt : ((q.1 : RHTower.XiDivisorSupport) : ℂ).re < 7 / 10 :=
      (Finset.mem_filter.mp hq).2
    have hstrip := RHTower.xi_divisor_support_re_mem_open_unit q.1
    have hkernel := norm_routeTNormalizedSmoothWindowMellin_le_left_rpow
      hNpos hHpos hstrip.2.le
    have hmono : inghamRouteTMellinPhysicalCenter X ^
          (((q.1 : RHTower.XiDivisorSupport) : ℂ).re - 1) ≤
        inghamRouteTMellinPhysicalCenter X ^ ((7 / 10 : ℝ) - 1) :=
      Real.rpow_le_rpow_of_exponent_le hNone (by linarith)
    have hexact : inghamRouteTMellinPhysicalCenter X ^ ((7 / 10 : ℝ) - 1) = E := by
      rw [inghamRouteTMellinPhysicalCenter_rpow_sub_one hX1]
      dsimp only [E]
      congr 1
      unfold inghamRouteTPhysicalScaleExponent
      norm_num
    exact hkernel.trans (hmono.trans_eq hexact)
  have hcard := card_inghamRouteTXiLowRealPacket_le_global hX
  have hE0 : 0 ≤ E := Real.rpow_nonneg (zero_le_one.trans hXR1) _
  unfold inghamRouteTBufferedXiMellinLowRealPacket
  calc
    ‖∑ q ∈ inghamRouteTXiLowRealPacket X,
        routeTNormalizedSmoothWindowMellin
          (inghamRouteTMellinPhysicalCenter X)
          (inghamRouteTMellinBufferedPhysicalWidth X) (q.1 : ℂ)‖ ≤
      ∑ q ∈ inghamRouteTXiLowRealPacket X,
        ‖routeTNormalizedSmoothWindowMellin
          (inghamRouteTMellinPhysicalCenter X)
          (inghamRouteTMellinBufferedPhysicalWidth X) (q.1 : ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ _q ∈ inghamRouteTXiLowRealPacket X, E :=
      Finset.sum_le_sum fun q hq => hpoint q hq
    _ = ((inghamRouteTXiLowRealPacket X).card : ℝ) * E := by
      simp [nsmul_eq_mul]
    _ ≤ (RHTower.xiZeroCountEnvelopeConstant * (1 + (X : ℝ)) *
          Real.log (2 + (X : ℝ))) * E :=
      mul_le_mul_of_nonneg_right hcard hE0
    _ = _ := by rfl

/-- The full bounded-height low-real Xi packet tends to zero. -/
theorem tendsto_norm_inghamRouteTBufferedXiMellinLowRealPacket_zero :
    Tendsto (fun X : ℕ => ‖inghamRouteTBufferedXiMellinLowRealPacket X‖)
      atTop (𝓝 0) := by
  let C : ℝ := RHTower.xiZeroCountEnvelopeConstant
  have hC : 0 < C := RHTower.xiZeroCountEnvelopeConstant_pos
  have hcore := tendsto_nat_log_mul_rpow_neg_one_div_299_zero
  have hupper : Tendsto (fun X : ℕ =>
      (4 * C) * (Real.log (X : ℝ) * (X : ℝ) ^ (-(1 / 299 : ℝ))))
      atTop (𝓝 0) := by
    simpa using hcore.const_mul (4 * C)
  refine squeeze_zero' (by filter_upwards with X; exact norm_nonneg _) ?_ hupper
  filter_upwards [eventually_ge_atTop (4 : ℕ)] with X hX
  have hb := norm_inghamRouteTBufferedXiMellinLowRealPacket_le hX
  have hXR : (4 : ℝ) ≤ X := by exact_mod_cast hX
  have hXpos : (0 : ℝ) < X := by linarith
  have hlog0 : 0 ≤ Real.log (X : ℝ) := Real.log_nonneg (by linarith)
  have hadd : 1 + (X : ℝ) ≤ 2 * X := by linarith
  have hquad : 2 + (X : ℝ) ≤ (X : ℝ) ^ (2 : ℕ) := by nlinarith
  have hlog := Real.log_le_log (by positivity : (0 : ℝ) < 2 + (X : ℝ)) hquad
  rw [Real.log_pow] at hlog
  norm_num at hlog
  have hfac : (1 + (X : ℝ)) * Real.log (2 + (X : ℝ)) ≤
      4 * (X : ℝ) * Real.log (X : ℝ) := by
    calc
      (1 + (X : ℝ)) * Real.log (2 + (X : ℝ)) ≤
          (2 * (X : ℝ)) * (2 * Real.log (X : ℝ)) :=
        mul_le_mul hadd hlog (Real.log_nonneg (by linarith : (1 : ℝ) ≤ 2 + X))
          (by positivity)
      _ = 4 * (X : ℝ) * Real.log (X : ℝ) := by ring
  have hweight0 : 0 ≤ (X : ℝ) ^ (-(300 / 299 : ℝ)) :=
    Real.rpow_nonneg hXpos.le _
  have hfacC : C * ((1 + (X : ℝ)) * Real.log (2 + (X : ℝ))) ≤
      C * (4 * (X : ℝ) * Real.log (X : ℝ)) :=
    mul_le_mul_of_nonneg_left hfac hC.le
  have hcollapse : (X : ℝ) * (X : ℝ) ^ (-(300 / 299 : ℝ)) =
      (X : ℝ) ^ (-(1 / 299 : ℝ)) := by
    calc
      (X : ℝ) * (X : ℝ) ^ (-(300 / 299 : ℝ)) =
          (X : ℝ) ^ (1 : ℝ) * (X : ℝ) ^ (-(300 / 299 : ℝ)) := by
        rw [Real.rpow_one]
      _ = (X : ℝ) ^ ((1 : ℝ) + -(300 / 299 : ℝ)) :=
        (Real.rpow_add hXpos _ _).symm
      _ = (X : ℝ) ^ (-(1 / 299 : ℝ)) := by
        congr 1
        norm_num
  calc
    ‖inghamRouteTBufferedXiMellinLowRealPacket X‖ ≤
        C * (1 + (X : ℝ)) * Real.log (2 + (X : ℝ)) *
          (X : ℝ) ^ (-(300 / 299 : ℝ)) := by simpa only [C] using hb
    _ = C * ((1 + (X : ℝ)) * Real.log (2 + (X : ℝ))) *
          (X : ℝ) ^ (-(300 / 299 : ℝ)) := by ring
    _ ≤ C * (4 * (X : ℝ) * Real.log (X : ℝ)) *
          (X : ℝ) ^ (-(300 / 299 : ℝ)) :=
      mul_le_mul_of_nonneg_right hfacC hweight0
    _ = (4 * C) * (Real.log (X : ℝ) * (X : ℝ) ^ (-(1 / 299 : ℝ))) := by
      rw [← hcollapse]
      ring

/-- Full exact-multiplicity Xi tail strictly beyond the finite detector top `X - 2`. -/
def inghamRouteTBufferedXiMellinShiftedHighTail (X : ℕ) : ℂ :=
  ∑' q : {q : RHTower.XiZeroCopy //
      q ∈ (↑(inghamRouteTXiLowOrdinatePacket X) : Set RHTower.XiZeroCopy)ᶜ},
    routeTNormalizedSmoothWindowMellin
      (inghamRouteTMellinPhysicalCenter X)
      (inghamRouteTMellinBufferedPhysicalWidth X)
      (q.1.1 : ℂ)

/- Arbitrary Mellin order bounds the shifted tail by inverse-square Xi ordinate mass. -/
set_option maxRecDepth 10000 in
theorem exists_norm_inghamRouteTBufferedXiMellinShiftedHighTail_le :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ {X : ℕ}, 4 ≤ X →
      ‖inghamRouteTBufferedXiMellinShiftedHighTail X‖ ≤
        (D * inghamRouteTMellinBufferedFrequency X ^ 2002 /
          ((X : ℝ) / 2) ^ 2000) *
            ∑' q : RHTower.XiZeroCopy,
              1 / |((q.1 : RHTower.XiDivisorSupport) : ℂ).im| ^ 2 := by
  obtain ⟨D, hD, hfrequency⟩ :=
    exists_routeTBufferedMellin_natOrder_frequency_bound 2001
  refine ⟨D, hD, ?_⟩
  intro X hX
  have hX1 : 1 ≤ X := by omega
  have hXR : (0 : ℝ) < X := by positivity
  have hhalf : (0 : ℝ) < (X : ℝ) / 2 := by positivity
  have hhalfcut : (X : ℝ) / 2 ≤ (X : ℝ) - 2 := by
    have hXR4 : (4 : ℝ) ≤ X := by exact_mod_cast hX
    linarith
  let Q := {q : RHTower.XiZeroCopy // q ∉ inghamRouteTXiLowOrdinatePacket X}
  let B : Q → ℝ := fun q =>
    1 / |((q.1.1 : RHTower.XiDivisorSupport) : ℂ).im| ^ 2
  let A : ℝ := D * inghamRouteTMellinBufferedFrequency X ^ 2002 /
    ((X : ℝ) / 2) ^ 2000
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hB : Summable B := by
    exact summable_xiZeroCopy_one_div_abs_im_sq.subtype _
  have hmajor : Summable (fun q : Q => A * B q) := hB.mul_left A
  have hpoint : ∀ q : Q,
      ‖routeTNormalizedSmoothWindowMellin
        (inghamRouteTMellinPhysicalCenter X)
        (inghamRouteTMellinBufferedPhysicalWidth X) (q.1.1 : ℂ)‖ ≤ A * B q := by
    intro q
    let rho : ℂ := (q.1.1 : RHTower.XiDivisorSupport)
    let gamma : ℝ := |rho.im|
    have hcut : (X : ℝ) - 2 < gamma := by
      apply lt_of_not_ge
      intro hgamma
      have qnot : q.1 ∉ inghamRouteTXiLowOrdinatePacket X := by simpa using q.2
      exact qnot ((mem_inghamRouteTXiLowOrdinatePacket_iff hX q.1).2
        (by simpa only [rho, gamma] using hgamma))
    have hgammaHalf : (X : ℝ) / 2 ≤ gamma := hhalfcut.trans hcut.le
    have hgamma : 0 < gamma := hhalf.trans_le hgammaHalf
    have hstrip := RHTower.xi_divisor_support_re_mem_open_unit q.1.1
    have hweighted := hfrequency (X := X) (w := rho) (by omega) hstrip.1 hstrip.2.le
    norm_num at hweighted
    have hkernel :
        ‖routeTNormalizedSmoothWindowMellin
          (inghamRouteTMellinPhysicalCenter X)
          (inghamRouteTMellinBufferedPhysicalWidth X) rho‖ ≤
          D * inghamRouteTMellinBufferedFrequency X ^ 2002 / gamma ^ 2002 := by
      apply (le_div_iff₀ (pow_pos hgamma 2002)).2
      simpa only [mul_comm] using hweighted
    have hpow : ((X : ℝ) / 2) ^ 2000 ≤ gamma ^ 2000 :=
      pow_le_pow_left₀ hhalf.le hgammaHalf 2000
    have htail :
        D * inghamRouteTMellinBufferedFrequency X ^ 2002 / gamma ^ 2002 ≤
          A * (1 / gamma ^ 2) := by
      dsimp only [A]
      have hF : 0 ≤ D * inghamRouteTMellinBufferedFrequency X ^ 2002 :=
        mul_nonneg hD (pow_nonneg (inghamRouteTMellinBufferedFrequency_pos hX1).le _)
      have hgammaPow : gamma ^ 2002 = gamma ^ 2000 * gamma ^ 2 := by
        rw [show 2002 = 2000 + 2 by omega, pow_add]
      rw [hgammaPow, div_mul_eq_div_mul_one_div]
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact div_le_div_of_nonneg_left hF (pow_pos hhalf 2000) hpow
    exact hkernel.trans (by simpa only [A, B, rho, gamma] using htail)
  have hsum : Summable (fun q : Q =>
      routeTNormalizedSmoothWindowMellin
        (inghamRouteTMellinPhysicalCenter X)
        (inghamRouteTMellinBufferedPhysicalWidth X) (q.1.1 : ℂ)) :=
    Summable.of_norm_bounded hmajor hpoint
  unfold inghamRouteTBufferedXiMellinShiftedHighTail
  change ‖∑' q : Q, routeTNormalizedSmoothWindowMellin
      (inghamRouteTMellinPhysicalCenter X)
      (inghamRouteTMellinBufferedPhysicalWidth X) (q.1.1 : ℂ)‖ ≤ _
  calc
    _ ≤ ∑' q : Q, ‖routeTNormalizedSmoothWindowMellin
        (inghamRouteTMellinPhysicalCenter X)
        (inghamRouteTMellinBufferedPhysicalWidth X) (q.1.1 : ℂ)‖ :=
      norm_tsum_le_tsum_norm hsum.norm
    _ ≤ ∑' q : Q, A * B q := hsum.norm.tsum_le_tsum hpoint hmajor
    _ = A * ∑' q : Q, B q := tsum_mul_left
    _ ≤ A * ∑' q : RHTower.XiZeroCopy,
        1 / |((q.1 : RHTower.XiDivisorSupport) : ℂ).im| ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ hA
      exact Summable.tsum_subtype_le _ _ (fun _ => by positivity)
        summable_xiZeroCopy_one_div_abs_im_sq
    _ = _ := rfl

/-- Exact buffered residual after replacing `X - 2` by the smaller cutoff `X/2`. -/
theorem inghamRouteTMellinBufferedFrequency_pow_2002_div_halfHeight_pow_2000
    {X : ℕ} (hX : 1 ≤ X) :
    inghamRouteTMellinBufferedFrequency X ^ 2002 / ((X : ℝ) / 2) ^ 2000 =
      (2 : ℝ) ^ 2000 * (X : ℝ) ^ (-(1 / 500 : ℝ)) := by
  have hXR : (0 : ℝ) < X := by positivity
  rw [div_pow]
  calc
    inghamRouteTMellinBufferedFrequency X ^ 2002 /
          ((X : ℝ) ^ 2000 / (2 : ℝ) ^ 2000) =
        (2 : ℝ) ^ 2000 *
          (inghamRouteTMellinBufferedFrequency X ^ 2002 / (X : ℝ) ^ 2000) := by
      field_simp [hXR.ne']
    _ = _ := by
      rw [inghamRouteTMellinBufferedFrequency_pow_2002_div_height_pow_2000 hX]

/-- The complete Xi tail above `X - 2`, including the former top band, tends to zero. -/
theorem tendsto_norm_inghamRouteTBufferedXiMellinShiftedHighTail_zero :
    Tendsto (fun X : ℕ => ‖inghamRouteTBufferedXiMellinShiftedHighTail X‖)
      atTop (𝓝 0) := by
  obtain ⟨D, hD, hbound⟩ :=
    exists_norm_inghamRouteTBufferedXiMellinShiftedHighTail_le
  let S : ℝ := ∑' q : RHTower.XiZeroCopy,
    1 / |((q.1 : RHTower.XiDivisorSupport) : ℂ).im| ^ 2
  have hcore : Tendsto (fun X : ℕ => (X : ℝ) ^ (-(1 / 500 : ℝ)))
      atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 500)).comp
      tendsto_natCast_atTop_atTop
  have hupper : Tendsto (fun X : ℕ =>
      (D * inghamRouteTMellinBufferedFrequency X ^ 2002 /
        ((X : ℝ) / 2) ^ 2000) * S) atTop (𝓝 0) := by
    have hscaled : Tendsto (fun X : ℕ =>
        (D * (2 : ℝ) ^ 2000 * S) * (X : ℝ) ^ (-(1 / 500 : ℝ)))
        atTop (𝓝 0) := by
      simpa using hcore.const_mul (D * (2 : ℝ) ^ 2000 * S)
    refine hscaled.congr' ?_
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with X hX
    have hratio := inghamRouteTMellinBufferedFrequency_pow_2002_div_halfHeight_pow_2000 hX
    calc
      (D * (2 : ℝ) ^ 2000 * S) * (X : ℝ) ^ (-(1 / 500 : ℝ)) =
          D * ((2 : ℝ) ^ 2000 * (X : ℝ) ^ (-(1 / 500 : ℝ))) * S := by ring
      _ = D * (inghamRouteTMellinBufferedFrequency X ^ 2002 /
          ((X : ℝ) / 2) ^ 2000) * S := by rw [← hratio]
      _ = _ := by ring
  refine squeeze_zero' (by filter_upwards with X; exact norm_nonneg _) ?_ hupper
  filter_upwards [eventually_ge_atTop (4 : ℕ)] with X hX
  simpa only [S] using hbound hX

end

end RHTower.Sieve
