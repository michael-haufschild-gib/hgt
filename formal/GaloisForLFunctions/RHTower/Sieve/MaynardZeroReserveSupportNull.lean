import GaloisForLFunctions.RHTower.Sieve.MaynardZeroReserveLogRigidity
import GaloisForLFunctions.RHTower.Sieve.MaynardNormalizedReferenceTargetPerron

noncomputable section
namespace RHTower.Sieve

open Finset ArithmeticFunction Complex MeasureTheory Set Filter
open GaloisForLFunctions.HTGeometry

/-- Saturation of the total logarithmic length places the box's exact lower support edge at the
physical truncation edge. -/
theorem groupedDyadicLower_eq_cutoff_of_totalExponent_eq
    {L X k : ℕ} {T mu N : ℝ} (box : HeathBrownBoxChoice L X k)
    (hT : 1 < T) (hXscale : (X : ℝ) ≤ T ^ mu)
    (hbox : IsHeathBrownBoxWindowRelevant N X k box)
    (htotal : heathBrownBoxTotalExponent L X k T box = mu) :
    groupedDyadicLower
      (heathBrownBoxFactorExponent box.a box.b box.q) = X := by
  let D : ℕ := groupedDyadicLower
    (heathBrownBoxFactorExponent box.a box.b box.q)
  have hDpow : (D : ℝ) = T ^ heathBrownBoxTotalExponent L X k T box := by
    dsimp [D]
    simpa [heathBrownBoxTotalExponent, groupedDyadicLower] using
      (cast_prod_twoPow_eq_rpow_sum_dyadicLogExponent hT
        (heathBrownBoxFactorExponent box.a box.b box.q)
        (Finset.univ : Finset (HeathBrownBoxFactorIndex k box.m)))
  have hDX : D ≤ X := hbox.1
  have hXDreal : (X : ℝ) ≤ D := by
    rw [hDpow, htotal]
    exact hXscale
  have hXD : X ≤ D := by exact_mod_cast hXDreal
  exact Nat.le_antisymm hDX hXD

/-- At zero erase-complement mass, saturation identifies the unique logarithm block's lower edge
with the physical cutoff itself. -/
theorem pow_logIndex_eq_cutoff_of_zero_complement_mass
    {L X k : ℕ} {T mu N : ℝ} (box : HeathBrownBoxChoice L X k)
    (j : HeathBrownBoxFactorIndex k box.m)
    (hlog : 1 ≤ box.q) (hT : 1 < T)
    (hXscale : (X : ℝ) ≤ T ^ mu)
    (hbox : IsHeathBrownBoxWindowRelevant N X k box)
    (htotal : heathBrownBoxTotalExponent L X k T box = mu)
    (hzero : (∑ i ∈ (Finset.univ.erase j),
      dyadicLogExponent T
        (heathBrownBoxFactorExponent box.a box.b box.q i)) = 0) :
    2 ^ box.q = X := by
  have hD := groupedDyadicLower_eq_cutoff_of_totalExponent_eq
    box hT hXscale hbox htotal
  have hj := distinguished_eq_logIndex_of_complement_mass_zero
    box j hlog hT hzero
  have hsplit := heathBrownBox_totalExponent_eq_factor_add_complement
    (T := T) box j
  rw [hzero, add_zero, hj] at hsplit
  change heathBrownBoxTotalExponent L X k T box =
    dyadicLogExponent T box.q at hsplit
  have hpow : (T ^ mu : ℝ) = (2 ^ box.q : ℕ) := by
    rw [← htotal, hsplit]
    exact rpow_dyadicLogExponent hT box.q
  have hDpow :
      ((groupedDyadicLower
        (heathBrownBoxFactorExponent box.a box.b box.q) : ℕ) : ℝ) =
        T ^ heathBrownBoxTotalExponent L X k T box := by
    simpa [heathBrownBoxTotalExponent, groupedDyadicLower] using
      (cast_prod_twoPow_eq_rpow_sum_dyadicLogExponent hT
        (heathBrownBoxFactorExponent box.a box.b box.q)
        (Finset.univ : Finset (HeathBrownBoxFactorIndex k box.m)))
  have hreal : ((2 ^ box.q : ℕ) : ℝ) = X := by
    calc
      ((2 ^ box.q : ℕ) : ℝ) = T ^ mu := hpow.symm
      _ = ((groupedDyadicLower
          (heathBrownBoxFactorExponent box.a box.b box.q) : ℕ) : ℝ) := by
        rw [hDpow, htotal]
      _ = X := by exact_mod_cast hD
  exact_mod_cast hreal

/-- Every coefficient of a logarithm block whose lower edge is the cutoff is invisible to an
adjacent physical window ending at that cutoff. -/
theorem complexCoeff_logDyadicBlock_mul_routeTSmoothWindowWeight_eq_zero
    {X q : ℕ} {N H : ℝ} (hedge : 2 ^ q = X)
    (hH : 0 < H) (hsupport : N + 2 * H ≤ X) (n : ℕ) :
    complexCoeff
        (arithmeticDyadicBlock (coeffTrunc ArithmeticFunction.log X) q) n *
      ((routeTSmoothWindowWeight N H (n : ℝ) : ℝ) : ℂ) = 0 := by
  by_cases hn : complexCoeff
      (arithmeticDyadicBlock (coeffTrunc ArithmeticFunction.log X) q) n = 0
  · rw [hn, zero_mul]
  · have hnlow := (Finset.mem_Ico.mp
      (complexCoeff_logDyadicBlock_support_Ico X q n hn)).1
    rw [hedge] at hnlow
    have hXn : (X : ℝ) ≤ n := by exact_mod_cast hnlow
    have hplus := smoothWeight_eq_zero hH
      (show N + H + H ≤ (n : ℝ) by linarith)
    have hbase := smoothWeight_eq_zero hH
      (show N + H ≤ (n : ℝ) by linarith)
    rw [routeTSmoothWindowWeight, hplus, hbase, sub_self, Complex.ofReal_zero,
      mul_zero]

theorem tsum_complexCoeff_logDyadicBlock_routeTSmoothWindowWeight_eq_zero
    {X q : ℕ} {N H : ℝ} (hedge : 2 ^ q = X)
    (hH : 0 < H) (hsupport : N + 2 * H ≤ X) :
    (∑' n : ℕ,
      complexCoeff
          (arithmeticDyadicBlock (coeffTrunc ArithmeticFunction.log X) q) n *
        ((routeTSmoothWindowWeight N H (n : ℝ) : ℝ) : ℂ)) = 0 := by
  calc
    (∑' n : ℕ,
      complexCoeff
          (arithmeticDyadicBlock (coeffTrunc ArithmeticFunction.log X) q) n *
        ((routeTSmoothWindowWeight N H (n : ℝ) : ℝ) : ℂ)) =
        ∑' _n : ℕ, (0 : ℂ) := by
      apply tsum_congr
      intro n
      exact complexCoeff_logDyadicBlock_mul_routeTSmoothWindowWeight_eq_zero
        hedge hH hsupport n
    _ = 0 := tsum_zero

/-- Finite-support Perron inversion for the adjacent Route-T window, with no special assumption on
the arithmetic function. -/
theorem smul_tsum_mul_routeTSmoothWindowWeight_eq_integral_of_upperSupported
    {F : ArithmeticFunction ℝ} {M : ℕ} (hF : UpperSupported F M)
    {N H sigma : ℝ} (hN : 0 < N) (hH : 0 < H) (hsigma : 0 < sigma) :
    (2 * Real.pi : ℝ) • (∑' n : ℕ, complexCoeff F n *
        ((routeTSmoothWindowWeight N H (n : ℝ) : ℝ) : ℂ)) =
      ∫ y : ℝ,
        LSeries (complexCoeff F) ((sigma : ℂ) + (y : ℝ) * I) *
          mellin (fun x : ℝ => ((routeTSmoothWindowWeight N H x : ℝ) : ℂ))
            ((sigma : ℂ) + (y : ℝ) * I) := by
  have hplusP := smul_tsum_mul_smoothWeight_eq_integral_of_upperSupported hF
    (N := N + H) (H := H) (sigma := sigma) (by linarith) hH hsigma
  have hbaseP := smul_tsum_mul_smoothWeight_eq_integral_of_upperSupported hF
    (N := N) (H := H) (sigma := sigma) hN hH hsigma
  have hplus := integrable_LSeries_mul_mellin_smoothWeight_of_upperSupported hF
    (N := N + H) (H := H) (sigma := sigma) (by linarith) hH hsigma
  have hbase := integrable_LSeries_mul_mellin_smoothWeight_of_upperSupported hF
    (N := N) (H := H) (sigma := sigma) hN hH hsigma
  have hplusSum : Summable fun n : ℕ => complexCoeff F n *
      ((GaloisForLFunctions.HTGeometry.smoothWeight (N + H) H (n : ℝ) : ℝ) : ℂ) := by
    refine summable_of_ne_finset_zero (s := Finset.Icc 1 M) fun n hn => ?_
    have hzero : complexCoeff F n = 0 := by
      by_contra hne
      exact hn (hF n (Complex.ofReal_injective.ne_iff.mp hne))
    rw [hzero, zero_mul]
  have hbaseSum : Summable fun n : ℕ => complexCoeff F n *
      ((GaloisForLFunctions.HTGeometry.smoothWeight N H (n : ℝ) : ℝ) : ℂ) := by
    refine summable_of_ne_finset_zero (s := Finset.Icc 1 M) fun n hn => ?_
    have hzero : complexCoeff F n = 0 := by
      by_contra hne
      exact hn (hF n (Complex.ofReal_injective.ne_iff.mp hne))
    rw [hzero, zero_mul]
  have hadjacent :
      (∑' n : ℕ, complexCoeff F n *
        ((routeTSmoothWindowWeight N H (n : ℝ) : ℝ) : ℂ)) =
      (∑' n : ℕ, complexCoeff F n *
        ((GaloisForLFunctions.HTGeometry.smoothWeight (N + H) H (n : ℝ) : ℝ) : ℂ)) -
      ∑' n : ℕ, complexCoeff F n *
        ((GaloisForLFunctions.HTGeometry.smoothWeight N H (n : ℝ) : ℝ) : ℂ) := by
    rw [← hplusSum.tsum_sub hbaseSum]
    apply tsum_congr
    intro n
    rw [routeTSmoothWindowWeight, ofReal_sub, mul_sub]
  have hperron : (2 * Real.pi : ℝ) •
      (∑' n : ℕ, complexCoeff F n *
        ((routeTSmoothWindowWeight N H (n : ℝ) : ℝ) : ℂ)) =
      (∫ y : ℝ,
        LSeries (complexCoeff F) ((sigma : ℂ) + (y : ℝ) * I) *
          mellin (fun x : ℝ => ((GaloisForLFunctions.HTGeometry.smoothWeight (N + H) H x : ℝ) : ℂ))
            ((sigma : ℂ) + (y : ℝ) * I)) -
      ∫ y : ℝ,
        LSeries (complexCoeff F) ((sigma : ℂ) + (y : ℝ) * I) *
          mellin (fun x : ℝ => ((GaloisForLFunctions.HTGeometry.smoothWeight N H x : ℝ) : ℂ))
            ((sigma : ℂ) + (y : ℝ) * I) := by
    rw [hadjacent, smul_sub, hplusP, hbaseP]
  rw [← integral_sub hplus hbase] at hperron
  calc
    (2 * Real.pi : ℝ) • (∑' n : ℕ, complexCoeff F n *
        ((routeTSmoothWindowWeight N H (n : ℝ) : ℝ) : ℂ)) =
        ∫ y : ℝ,
          LSeries (complexCoeff F) ((sigma : ℂ) + (y : ℝ) * I) *
              mellin (fun x : ℝ => ((GaloisForLFunctions.HTGeometry.smoothWeight (N + H) H x : ℝ) : ℂ))
                ((sigma : ℂ) + (y : ℝ) * I) -
            LSeries (complexCoeff F) ((sigma : ℂ) + (y : ℝ) * I) *
              mellin (fun x : ℝ => ((GaloisForLFunctions.HTGeometry.smoothWeight N H x : ℝ) : ℂ))
                ((sigma : ℂ) + (y : ℝ) * I) := hperron
    _ = ∫ y : ℝ,
        LSeries (complexCoeff F) ((sigma : ℂ) + (y : ℝ) * I) *
          mellin (fun x : ℝ => ((routeTSmoothWindowWeight N H x : ℝ) : ℂ))
            ((sigma : ℂ) + (y : ℝ) * I) := by
      apply integral_congr_ae
      filter_upwards with y
      rw [mellin_routeTSmoothWindowWeight_eq_sub hN.le hH (by
        simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im]
        linarith)]
      ring

/-- A cutoff-saturated logarithm block has identically zero adjacent Perron integral. -/
theorem integral_LSeries_logDyadicBlock_mul_routeTMellin_eq_zero
    {X q : ℕ} {N H sigma : ℝ} (hedge : 2 ^ q = X)
    (hN : 0 < N) (hH : 0 < H) (hsupport : N + 2 * H ≤ X)
    (hsigma : 0 < sigma) :
    (∫ y : ℝ,
      LSeries (complexCoeff
          (arithmeticDyadicBlock (coeffTrunc ArithmeticFunction.log X) q))
          ((sigma : ℂ) + (y : ℝ) * I) *
        mellin (fun x : ℝ => ((routeTSmoothWindowWeight N H x : ℝ) : ℂ))
          ((sigma : ℂ) + (y : ℝ) * I)) = 0 := by
  have hperron := smul_tsum_mul_routeTSmoothWindowWeight_eq_integral_of_upperSupported
    (upperSupported_arithmeticDyadicBlock (coeffTrunc ArithmeticFunction.log X) q)
    hN hH hsigma
  rw [tsum_complexCoeff_logDyadicBlock_routeTSmoothWindowWeight_eq_zero
    hedge hH hsupport] at hperron
  simpa using hperron.symm

/-- **Zero-reserve support-null rigidity.** A saturated zero-complement Heath--Brown box is exactly
the logarithm block beginning at `X`, so its entire adjacent Perron transform vanishes. -/
theorem integral_heathBrownDyadicCoreProduct_mul_routeTMellin_eq_zero_of_zero_reserve
    {L X k : ℕ} {T mu N H sigma : ℝ} (box : HeathBrownBoxChoice L X k)
    (j : HeathBrownBoxFactorIndex k box.m)
    (hL : 1 ≤ L) (hX : 1 ≤ X) (hlog : 1 ≤ box.q)
    (hT : 1 < T) (hXscale : (X : ℝ) ≤ T ^ mu)
    (hbox : IsHeathBrownBoxWindowRelevant N X k box)
    (htotal : heathBrownBoxTotalExponent L X k T box = mu)
    (hzero : (∑ i ∈ (Finset.univ.erase j),
      dyadicLogExponent T
        (heathBrownBoxFactorExponent box.a box.b box.q i)) = 0)
    (hN : 0 < N) (hH : 0 < H) (hsupport : N + 2 * H ≤ X)
    (hsigma : 0 < sigma) :
    (∫ y : ℝ,
      heathBrownDyadicCoreProduct L X k box.m box.a box.b box.q
          ((sigma : ℂ) + (y : ℝ) * I) *
        mellin (fun x : ℝ => ((routeTSmoothWindowWeight N H x : ℝ) : ℂ))
          ((sigma : ℂ) + (y : ℝ) * I)) = 0 := by
  have hedge := pow_logIndex_eq_cutoff_of_zero_complement_mass
    box j hlog hT hXscale hbox htotal hzero
  calc
    (∫ y : ℝ,
      heathBrownDyadicCoreProduct L X k box.m box.a box.b box.q
          ((sigma : ℂ) + (y : ℝ) * I) *
        mellin (fun x : ℝ => ((routeTSmoothWindowWeight N H x : ℝ) : ℂ))
          ((sigma : ℂ) + (y : ℝ) * I)) =
      ∫ y : ℝ,
        LSeries (complexCoeff
            (arithmeticDyadicBlock (coeffTrunc ArithmeticFunction.log X) box.q))
            ((sigma : ℂ) + (y : ℝ) * I) *
          mellin (fun x : ℝ => ((routeTSmoothWindowWeight N H x : ℝ) : ℂ))
            ((sigma : ℂ) + (y : ℝ) * I) := by
        apply integral_congr_ae
        filter_upwards with y
        rw [heathBrownDyadicCoreProduct_eq_logFactor_of_complement_mass_zero
          box j hL hX hlog hT hzero]
    _ = 0 := integral_LSeries_logDyadicBlock_mul_routeTMellin_eq_zero
      hedge hN hH hsupport hsigma

/-- Finite-support integrability for one Route-T adjacent Mellin kernel. -/
theorem integrable_LSeries_mul_mellin_routeTSmoothWindowWeight_of_upperSupported
    {F : ArithmeticFunction ℝ} {M : ℕ} (hF : UpperSupported F M)
    {N H sigma : ℝ} (hN : 0 < N) (hH : 0 < H) (hsigma : 0 < sigma) :
    Integrable (fun y : ℝ =>
      LSeries (complexCoeff F) ((sigma : ℂ) + (y : ℝ) * I) *
        mellin (fun x : ℝ => ((routeTSmoothWindowWeight N H x : ℝ) : ℂ))
          ((sigma : ℂ) + (y : ℝ) * I)) := by
  have hplus := integrable_LSeries_mul_mellin_smoothWeight_of_upperSupported hF
    (N := N + H) (H := H) (sigma := sigma) (by linarith) hH hsigma
  have hbase := integrable_LSeries_mul_mellin_smoothWeight_of_upperSupported hF
    (N := N) (H := H) (sigma := sigma) hN hH hsigma
  refine (hplus.sub hbase).congr (Filter.Eventually.of_forall fun y => ?_)
  simp only [Pi.sub_apply]
  rw [mellin_routeTSmoothWindowWeight_eq_sub hN.le hH (by
    simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im]
    linarith)]
  ring

/-- Width normalization preserves finite-support integrability. -/
theorem integrable_LSeries_mul_routeTNormalizedSmoothWindowMellin_of_upperSupported
    {F : ArithmeticFunction ℝ} {M : ℕ} (hF : UpperSupported F M)
    {N H sigma : ℝ} (hN : 0 < N) (hH : 0 < H) (hsigma : 0 < sigma) :
    Integrable (fun y : ℝ =>
      LSeries (complexCoeff F) ((sigma : ℂ) + (y : ℝ) * I) *
        routeTNormalizedSmoothWindowMellin N H
          ((sigma : ℂ) + (y : ℝ) * I)) := by
  have hraw :=
    integrable_LSeries_mul_mellin_routeTSmoothWindowWeight_of_upperSupported
      hF hN hH hsigma
  have hscaled := hraw.const_mul (H : ℂ)⁻¹
  refine hscaled.congr (Filter.Eventually.of_forall fun y => ?_)
  change (H : ℂ)⁻¹ *
      (LSeries (complexCoeff F) ((sigma : ℂ) + (y : ℝ) * I) *
        mellin (fun x : ℝ => ((routeTSmoothWindowWeight N H x : ℝ) : ℂ))
          ((sigma : ℂ) + (y : ℝ) * I)) =
    LSeries (complexCoeff F) ((sigma : ℂ) + (y : ℝ) * I) *
      routeTNormalizedSmoothWindowMellin N H
        ((sigma : ℂ) + (y : ℝ) * I)
  rw [routeTNormalizedSmoothWindowMellin]
  ring

/-- Cutoff-saturated logarithm block is also null after width normalization. -/
theorem integral_LSeries_logDyadicBlock_mul_routeTNormalizedMellin_eq_zero
    {X q : ℕ} {N H sigma : ℝ} (hedge : 2 ^ q = X)
    (hN : 0 < N) (hH : 0 < H) (hsupport : N + 2 * H ≤ X)
    (hsigma : 0 < sigma) :
    (∫ y : ℝ,
      LSeries (complexCoeff
          (arithmeticDyadicBlock (coeffTrunc ArithmeticFunction.log X) q))
          ((sigma : ℂ) + (y : ℝ) * I) *
        routeTNormalizedSmoothWindowMellin N H
          ((sigma : ℂ) + (y : ℝ) * I)) = 0 := by
  have hraw := integral_LSeries_logDyadicBlock_mul_routeTMellin_eq_zero
    hedge hN hH hsupport hsigma
  calc
    (∫ y : ℝ,
      LSeries (complexCoeff
          (arithmeticDyadicBlock (coeffTrunc ArithmeticFunction.log X) q))
          ((sigma : ℂ) + (y : ℝ) * I) *
        routeTNormalizedSmoothWindowMellin N H
          ((sigma : ℂ) + (y : ℝ) * I)) =
      ∫ y : ℝ, (H : ℂ)⁻¹ *
        (LSeries (complexCoeff
            (arithmeticDyadicBlock (coeffTrunc ArithmeticFunction.log X) q))
            ((sigma : ℂ) + (y : ℝ) * I) *
          mellin (fun x : ℝ => ((routeTSmoothWindowWeight N H x : ℝ) : ℂ))
            ((sigma : ℂ) + (y : ℝ) * I)) := by
        apply integral_congr_ae
        filter_upwards with y
        rw [routeTNormalizedSmoothWindowMellin]
        ring
    _ = (H : ℂ)⁻¹ * ∫ y : ℝ,
        LSeries (complexCoeff
            (arithmeticDyadicBlock (coeffTrunc ArithmeticFunction.log X) q))
            ((sigma : ℂ) + (y : ℝ) * I) *
          mellin (fun x : ℝ => ((routeTSmoothWindowWeight N H x : ℝ) : ℂ))
            ((sigma : ℂ) + (y : ℝ) * I) := by rw [integral_const_mul]
    _ = 0 := by rw [hraw, mul_zero]

/-- Saturated logarithm block is null under the exact target--reference adjacent kernel. -/
theorem integral_LSeries_logDyadicBlock_mul_routeTAdjacentNormalizedMellin_eq_zero
    {X q : ℕ} {N R H sigma : ℝ} (hedge : 2 ^ q = X)
    (hN : 0 < N) (hR : 0 < R) (hH : 0 < H)
    (hsupportR : N + 2 * R ≤ X) (hsupportH : N + 2 * H ≤ X)
    (hsigma : 0 < sigma) :
    (∫ y : ℝ,
      LSeries (complexCoeff
          (arithmeticDyadicBlock (coeffTrunc ArithmeticFunction.log X) q))
          ((sigma : ℂ) + (y : ℝ) * I) *
        (routeTNormalizedSmoothWindowMellin N R
            ((sigma : ℂ) + (y : ℝ) * I) -
          routeTNormalizedSmoothWindowMellin N H
            ((sigma : ℂ) + (y : ℝ) * I))) = 0 := by
  let F := arithmeticDyadicBlock (coeffTrunc ArithmeticFunction.log X) q
  have hF := upperSupported_arithmeticDyadicBlock
    (coeffTrunc ArithmeticFunction.log X) q
  have hIR :=
    integrable_LSeries_mul_routeTNormalizedSmoothWindowMellin_of_upperSupported
      hF hN hR hsigma
  have hIH :=
    integrable_LSeries_mul_routeTNormalizedSmoothWindowMellin_of_upperSupported
      hF hN hH hsigma
  simp_rw [mul_sub]
  rw [integral_sub hIR hIH,
    integral_LSeries_logDyadicBlock_mul_routeTNormalizedMellin_eq_zero
      hedge hN hR hsupportR hsigma,
    integral_LSeries_logDyadicBlock_mul_routeTNormalizedMellin_eq_zero
      hedge hN hH hsupportH hsigma,
    sub_self]

/-- **Target--reference zero-reserve elimination.** Under exact scale saturation, every
zero-complement box contributes zero to the normalized adjacent defect used by Route T. -/
theorem integral_heathBrownDyadicCoreProduct_mul_routeTAdjacentNormalizedMellin_eq_zero_of_zero_reserve
    {L X k : ℕ} {T mu N R H sigma : ℝ} (box : HeathBrownBoxChoice L X k)
    (j : HeathBrownBoxFactorIndex k box.m)
    (hL : 1 ≤ L) (hX : 1 ≤ X) (hlog : 1 ≤ box.q)
    (hT : 1 < T) (hXscale : (X : ℝ) ≤ T ^ mu)
    (hbox : IsHeathBrownBoxWindowRelevant N X k box)
    (htotal : heathBrownBoxTotalExponent L X k T box = mu)
    (hzero : (∑ i ∈ (Finset.univ.erase j),
      dyadicLogExponent T
        (heathBrownBoxFactorExponent box.a box.b box.q i)) = 0)
    (hN : 0 < N) (hR : 0 < R) (hH : 0 < H)
    (hsupportR : N + 2 * R ≤ X) (hsupportH : N + 2 * H ≤ X)
    (hsigma : 0 < sigma) :
    (∫ y : ℝ,
      heathBrownDyadicCoreProduct L X k box.m box.a box.b box.q
          ((sigma : ℂ) + (y : ℝ) * I) *
        (routeTNormalizedSmoothWindowMellin N R
            ((sigma : ℂ) + (y : ℝ) * I) -
          routeTNormalizedSmoothWindowMellin N H
            ((sigma : ℂ) + (y : ℝ) * I))) = 0 := by
  have hedge := pow_logIndex_eq_cutoff_of_zero_complement_mass
    box j hlog hT hXscale hbox htotal hzero
  calc
    (∫ y : ℝ,
      heathBrownDyadicCoreProduct L X k box.m box.a box.b box.q
          ((sigma : ℂ) + (y : ℝ) * I) *
        (routeTNormalizedSmoothWindowMellin N R
            ((sigma : ℂ) + (y : ℝ) * I) -
          routeTNormalizedSmoothWindowMellin N H
            ((sigma : ℂ) + (y : ℝ) * I))) =
      ∫ y : ℝ,
        LSeries (complexCoeff
            (arithmeticDyadicBlock (coeffTrunc ArithmeticFunction.log X) box.q))
            ((sigma : ℂ) + (y : ℝ) * I) *
          (routeTNormalizedSmoothWindowMellin N R
              ((sigma : ℂ) + (y : ℝ) * I) -
            routeTNormalizedSmoothWindowMellin N H
              ((sigma : ℂ) + (y : ℝ) * I)) := by
        apply integral_congr_ae
        filter_upwards with y
        rw [heathBrownDyadicCoreProduct_eq_logFactor_of_complement_mass_zero
          box j hL hX hlog hT hzero]
    _ = 0 :=
      integral_LSeries_logDyadicBlock_mul_routeTAdjacentNormalizedMellin_eq_zero
        hedge hN hR hH hsupportR hsupportH hsigma

end RHTower.Sieve
