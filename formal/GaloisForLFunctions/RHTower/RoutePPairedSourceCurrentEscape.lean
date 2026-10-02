import GaloisForLFunctions.RHTower.RoutePActivePairedDisplacementEscape
import GaloisForLFunctions.RHTower.RoutePMovingDepthBoundary
import GaloisForLFunctions.RHTower.CCMActualHeadMatchedQuantileLorentzEdgeProducer

/-!
# A complete paired current at arbitrarily small Xi norm

Mass-normalized primitive jets are uniformly dominated by the base-prime jet.
The actual matched-minus-quantile cross current, after division by the positive
pair mass, escapes every absolute bound on active tails. Two signed primitive
atoms therefore give complete paired current exactly minus one at arbitrarily
small Xi norm. Both physical moment sides and their literal source coefficients
are retained. No lower bound by Xi norm squared exists for this source family.

This is a statement about finite signed source packets. It neither estimates nor
falsifies the linear floor of the native positive prime-head history.
-/

open Complex Set Filter Topology
open scoped BigOperators
namespace RHTower
noncomputable section


private theorem primitive_point_eq (p : Nat.Primes) (e : ℕ) :
    (routePPrimitiveDeningerUpperPoint (p, e) 0 : ℂ) =
      (xiGammaEulerPrimitiveLogFrequency (p, e) : ℂ) * I := by
  simp [routePPrimitiveDeningerUpperPoint_coe, routePPrimitiveBurnolCenteredMode]

theorem routeP_massNormalizedXiJet_norm_le_base (p : Nat.Primes) (e : ℕ) :
    ‖routePDepthMassNormalizedXiJet p e‖ ≤
      ‖routePDepthMassNormalizedXiJet ⟨2, Nat.prime_two⟩ 0‖ := by
  let p₂ : Nat.Primes := ⟨2, Nat.prime_two⟩
  have hp : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast p.property.one_lt)
  have hp₂ : 0 < Real.log (p₂ : ℝ) := Real.log_pos (by norm_num [p₂])
  have hlog : Real.log (p₂ : ℝ) ≤ Real.log (p : ℝ) :=
    Real.log_le_log (by norm_num [p₂]) (by exact_mod_cast p.property.two_le)
  have hfreq : xiGammaEulerPrimitiveLogFrequency (p₂, 0) ≤
      xiGammaEulerPrimitiveLogFrequency (p, e) := by
    simp only [routeP_depth_frequency, Nat.cast_zero, zero_add, one_mul]
    nlinarith [Nat.cast_nonneg (α := ℝ) e]
  have hamp : ‖-(Real.sqrt (Real.log (p : ℝ)) : ℂ)⁻¹‖ ≤
      ‖-(Real.sqrt (Real.log (p₂ : ℝ)) : ℂ)⁻¹‖ := by
    simp only [norm_neg, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _)]
    exact inv_anti₀ (Real.sqrt_pos.mpr hp₂) (Real.sqrt_le_sqrt hlog)
  apply lp.norm_mono (by norm_num)
  intro q
  have hq := (xiSpectralPoint_im_mem_openHalf q).2
  have hb := half_lt_xiGammaEulerPrimitiveLogFrequency (p₂, 0)
  have hsq (p : Nat.Primes) (j : ℕ) : ‖xiSpectralPoint q -
      (routePPrimitiveDeningerUpperPoint (p, j) 0 : ℂ)‖ ^ 2 =
      (xiSpectralPoint q).re ^ 2 +
        ((xiSpectralPoint q).im - xiGammaEulerPrimitiveLogFrequency (p, j)) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, primitive_point_eq]
    simp only [sub_re, sub_im, mul_re, mul_im, ofReal_re, ofReal_im, I_re, I_im,
      mul_zero, sub_zero, mul_one, add_zero]
    ring
  have hnorm : ‖xiSpectralPoint q - (routePPrimitiveDeningerUpperPoint (p₂, 0) 0 : ℂ)‖ ≤
      ‖xiSpectralPoint q - (routePPrimitiveDeningerUpperPoint (p, e) 0 : ℂ)‖ := by
    have h0 := hsq p₂ 0
    have he := hsq p e
    nlinarith [norm_nonneg (xiSpectralPoint q -
      (routePPrimitiveDeningerUpperPoint (p₂, 0) 0 : ℂ)),
      norm_nonneg (xiSpectralPoint q -
      (routePPrimitiveDeningerUpperPoint (p, e) 0 : ℂ))]
  have hpos : 0 < ‖xiSpectralPoint q - (routePPrimitiveDeningerUpperPoint (p₂, 0) 0 : ℂ)‖ :=
    (routePDeningerUpperSpectralGap_pos _).trans (routePDeningerUpperSpectralGap_lt_norm_sub _ _)
  have hc : ‖xiWeilCauchyTest (routePPrimitiveDeningerUpperPoint (p, e) 0 : ℂ) (xiSpectralPoint q)‖ ≤
      ‖xiWeilCauchyTest (routePPrimitiveDeningerUpperPoint (p₂, 0) 0 : ℂ) (xiSpectralPoint q)‖ := by
    simp only [xiWeilCauchyTest, norm_inv]
    exact inv_anti₀ hpos hnorm
  change ‖(-(Real.sqrt (Real.log (p : ℝ)) : ℂ)⁻¹) *
    xiWeilCauchyTest (routePPrimitiveDeningerUpperPoint (p, e) 0 : ℂ) (xiSpectralPoint q) ^ 2‖ ≤
      ‖(-(Real.sqrt (Real.log (p₂ : ℝ)) : ℂ)⁻¹) *
    xiWeilCauchyTest (routePPrimitiveDeningerUpperPoint (p₂, 0) 0 : ℂ) (xiSpectralPoint q) ^ 2‖
  rw [norm_mul, norm_mul, norm_pow, norm_pow]
  exact mul_le_mul hamp (pow_le_pow_left₀ (norm_nonneg _) hc 2) (by positivity) (norm_nonneg _)

def routePPairedUnitCross (a n : ℕ) : ℝ :=
  ccmActualHeadMatchedQuantileParabolicCrossKernelValue a n /
    (criticalMellinAtomWeight a * criticalMellinAtomWeight n)

theorem routePPairedUnitCross_factor {a n : ℕ} (ha : IsPrimePow a) (hn : IsPrimePow n) :
    routePPairedUnitCross a n =
      -(ccmActualHeadMatchedQuantilePolarDisplacement n -
        ccmActualHeadMatchedQuantilePolarDisplacement a) *
      (ccmActualHeadMatchedPolarCentroid n - ccmActualHeadMatchedPolarCentroid a +
        (ccmActualHeadQuantilePolarCentroid n - ccmActualHeadQuantilePolarCentroid a)) / 2 := by
  have hwa := (criticalMellinAtomWeight_pos ha).ne'
  have hwn := (criticalMellinAtomWeight_pos hn).ne'
  rw [routePPairedUnitCross, ccmActualHeadMatchedQuantileParabolicCrossKernelValue_eq_lorentzEdge]
  simp only [ccmActualHeadMatchedQuantileLorentzSquare, ccmActualHeadMatchedQuantileLorentzEdge,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [ccmActualHeadQuantilePolarCentroid_eq_matched_add_displacement,
    ccmActualHeadQuantilePolarCentroid_eq_matched_add_displacement]
  field_simp
  ring

theorem routePPairedUnitCross_absolute_escape (a : ℕ) (ha : IsPrimePow a) (B : ℝ) (L : ℕ) :
    ∃ n : ℕ, L ≤ n ∧ IsPrimePow n ∧ B < |routePPairedUnitCross a n| := by
  have hsqrt : Tendsto (fun n : ℕ => Real.sqrt (n : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hsqrt.eventually_ge_atTop
    (|ccmActualHeadMatchedPolarCentroid a| + 2))
  obtain ⟨n, hnL, hn, hdisp⟩ := routeP_activeDisplacement_absolute_escape
    (|B| + |ccmActualHeadMatchedQuantilePolarDisplacement a| + 1) (max L (max a N))
  have han : a ≤ n := (le_max_left _ _).trans ((le_max_right _ _).trans hnL)
  have hNn : N ≤ n := (le_max_right _ _).trans ((le_max_right _ _).trans hnL)
  have hc : 2 * Real.sqrt (n : ℝ) ≤ ccmActualHeadMatchedPolarCentroid n := by
    have hs := ccmActualHeadMatchedPolarCentroid_sq n hn.pos
    have hr := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) n)
    nlinarith [ccmActualHeadMatchedPolarCentroid_pos n, Real.sqrt_nonneg (n : ℝ),
      sq_nonneg (criticalMellinAtomWeight n)]
  have hq := ccmActualHeadQuantilePolarCentroid_le_of_le han
  have hsum : 2 ≤ ccmActualHeadMatchedPolarCentroid n - ccmActualHeadMatchedPolarCentroid a +
      (ccmActualHeadQuantilePolarCentroid n - ccmActualHeadQuantilePolarCentroid a) := by
    linarith [hN n hNn, le_abs_self (ccmActualHeadMatchedPolarCentroid a),
      abs_nonneg (ccmActualHeadMatchedPolarCentroid a)]
  have hd : |B| < |ccmActualHeadMatchedQuantilePolarDisplacement n -
      ccmActualHeadMatchedQuantilePolarDisplacement a| := by
    have ht := abs_add_le (ccmActualHeadMatchedQuantilePolarDisplacement n -
      ccmActualHeadMatchedQuantilePolarDisplacement a) (ccmActualHeadMatchedQuantilePolarDisplacement a)
    rw [sub_add_cancel] at ht
    linarith
  refine ⟨n, (le_max_left _ _).trans hnL, hn, ?_⟩
  rw [routePPairedUnitCross_factor ha hn, abs_div, abs_mul, abs_neg,
    abs_of_nonneg (by linarith : 0 ≤ ccmActualHeadMatchedPolarCentroid n -
      ccmActualHeadMatchedPolarCentroid a +
      (ccmActualHeadQuantilePolarCentroid n - ccmActualHeadQuantilePolarCentroid a)),
    abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hm := mul_le_mul_of_nonneg_left hsum (abs_nonneg
    (ccmActualHeadMatchedQuantilePolarDisplacement n - ccmActualHeadMatchedQuantilePolarDisplacement a))
  linarith [le_abs_self B]

def routePPairedXiPacket (p : Nat.Primes) (e : ℕ) (a b : ℝ) : DeningerArithmeticJetHilbert :=
  (a : ℂ) • routePDepthMassNormalizedXiJet ⟨2, Nat.prime_two⟩ 0 +
    (b : ℂ) • routePDepthMassNormalizedXiJet p e

def routePPairedPhysicalPacketForm (p : Nat.Primes) (e : ℕ) (a b : ℝ) : ℝ :=
  let n := xiGammaEulerValuationNat (p, e)
  ccmParabolicForm
      ((a / criticalMellinAtomWeight 2) • ccmActualHeadMatchedParabolicMoment 2 +
        (b / criticalMellinAtomWeight n) • ccmActualHeadMatchedParabolicMoment n) -
    ccmParabolicForm
      ((a / criticalMellinAtomWeight 2) • ccmActualHeadQuantileParabolicMoment 2 +
        (b / criticalMellinAtomWeight n) • ccmActualHeadQuantileParabolicMoment n)

theorem routePPairedPhysicalPacketForm_eq (p : Nat.Primes) (e : ℕ) (a b : ℝ) :
    routePPairedPhysicalPacketForm p e a b =
      2 * a * b * routePPairedUnitCross 2 (xiGammaEulerValuationNat (p, e)) := by
  have hquad (u v : Fin 3 → ℝ) (s t : ℝ) :
      ccmParabolicForm (s • u + t • v) = s ^ 2 * ccmParabolicForm u +
        2 * s * t * ccmParabolicPairing u v + t ^ 2 * ccmParabolicForm v := by
    simp only [ccmParabolicForm, ccmParabolicPairing, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [routePPairedPhysicalPacketForm, hquad, hquad,
    ccmActualHeadQuantileParabolicForm_eq_matched, ccmActualHeadQuantileParabolicForm_eq_matched]
  simp only [routePPairedUnitCross, ccmActualHeadMatchedQuantileParabolicCrossKernelValue]
  ring

theorem routePPairedXiPacket_norm_le (p : Nat.Primes) (e : ℕ) (a b : ℝ) :
    ‖routePPairedXiPacket p e a b‖ ≤ (|a| + |b|) *
      ‖routePDepthMassNormalizedXiJet ⟨2, Nat.prime_two⟩ 0‖ := by
  have h := norm_add_le
    ((a : ℂ) • routePDepthMassNormalizedXiJet ⟨2, Nat.prime_two⟩ 0)
    ((b : ℂ) • routePDepthMassNormalizedXiJet p e)
  simp only [norm_smul, Complex.norm_real, Real.norm_eq_abs] at h
  have hmono := mul_le_mul_of_nonneg_left (routeP_massNormalizedXiJet_norm_le_base p e)
    (abs_nonneg b)
  change ‖routePPairedXiPacket p e a b‖ ≤ _ at h
  nlinarith

/-- The complete paired current can equal minus one at arbitrarily small Xi norm,
using two literal signed primitive sources, with the moving source arbitrarily late. -/
theorem routeP_paired_negative_unit_at_small_Xi {ε : ℝ} (hε : 0 < ε) (L : ℕ) :
    ∃ (p : Nat.Primes) (e : ℕ) (a b : ℝ),
      L ≤ xiGammaEulerValuationNat (p, e) ∧
      ‖routePPairedXiPacket p e a b‖ < ε ∧ routePPairedPhysicalPacketForm p e a b = -1 := by
  let D : ℝ := ‖routePDepthMassNormalizedXiJet ⟨2, Nat.prime_two⟩ 0‖
  have hD : 0 ≤ D := norm_nonneg _
  let t : ℝ := ε / (4 * (D + 1))
  have ht : 0 < t := div_pos hε (by positivity)
  have htε : t * (4 * (D + 1)) = ε := by
    dsimp [t]
    field_simp
  obtain ⟨n, hnL, hn, hc⟩ := routePPairedUnitCross_absolute_escape 2 Nat.prime_two.isPrimePow
    (1 / t ^ 2) L
  obtain ⟨p, e, hp, hpn⟩ := (isPrimePow_iff_pow_succ n).mp hn
  let P : Nat.Primes := ⟨p, Nat.prime_iff.mpr hp⟩
  have hnP : xiGammaEulerValuationNat (P, e) = n := hpn
  let c : ℝ := routePPairedUnitCross 2 n
  have hcpos : 0 < |c| := lt_trans (by positivity : 0 < 1 / t ^ 2) hc
  have hcne : c ≠ 0 := abs_pos.mp hcpos
  have hprod : 1 < t ^ 2 * |c| := by
    have h := (div_lt_iff₀ (sq_pos_of_pos ht)).mp hc
    dsimp [c]
    nlinarith
  let b : ℝ := -1 / (2 * t * c)
  have hbabs : |b| = 1 / (2 * t * |c|) := by
    dsimp [b]
    rw [abs_div, abs_neg, abs_one, abs_mul, abs_mul,
      abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_of_pos ht]
  have hb : |b| ≤ t := by
    rw [hbabs]
    apply (div_le_iff₀ (by positivity : 0 < 2 * t * |c|)).mpr
    nlinarith
  refine ⟨P, e, t, b, by rwa [hnP], ?_, ?_⟩
  · have hnorm := routePPairedXiPacket_norm_le P e t b
    rw [abs_of_pos ht] at hnorm
    change ‖routePPairedXiPacket P e t b‖ ≤ (t + |b|) * D at hnorm
    have hm := mul_le_mul_of_nonneg_right hb hD
    nlinarith
  · rw [routePPairedPhysicalPacketForm_eq, hnP]
    change 2 * t * (-1 / (2 * t * c)) * c = -1
    field_simp

/-- The Hilbert packet uses exactly the same signed physical-source coefficients
as the two moment sums defining its complete paired current. -/
theorem routePPairedXiPacket_eq_literal_sources (p : Nat.Primes) (e : ℕ) (a b : ℝ) :
    routePPairedXiPacket p e a b =
      (((a / criticalMellinAtomWeight 2 : ℝ) : ℂ)) •
        routePDeningerUpperSquaredCauchyJet (-finiteVonMangoldtDepthOneAmplitude 2)
          (routePPrimitiveDeningerUpperPoint (⟨2, Nat.prime_two⟩, 0) 0) +
      (((b / criticalMellinAtomWeight (xiGammaEulerValuationNat (p, e)) : ℝ) : ℂ)) •
        routePDeningerUpperSquaredCauchyJet
          (-finiteVonMangoldtDepthOneAmplitude (xiGammaEulerValuationNat (p, e)))
          (routePPrimitiveDeningerUpperPoint (p, e) 0) := by
  rw [routePPairedXiPacket, routePDepthMassNormalizedXiJet_eq,
    routePDepthMassNormalizedXiJet_eq]
  simp only [xiGammaEulerValuationNat, Nat.zero_add, pow_one,
    smul_smul, div_eq_mul_inv, Complex.ofReal_mul, Complex.ofReal_inv]

theorem not_routeP_paired_current_lower_bounded_by_Xi :
    ¬ ∃ C : ℝ, ∀ (p : Nat.Primes) (e : ℕ) (a b : ℝ),
      -C * ‖routePPairedXiPacket p e a b‖ ^ 2 ≤ routePPairedPhysicalPacketForm p e a b := by
  rintro ⟨C, hC⟩
  let ε : ℝ := 1 / (|C| + 2)
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hεone : ε ≤ 1 := by
    dsimp [ε]
    apply (div_le_iff₀ (by positivity : 0 < |C| + 2)).mpr
    linarith [abs_nonneg C]
  have hεeq : (|C| + 2) * ε = 1 := by dsimp [ε]; field_simp
  obtain ⟨p, e, a, b, _, hn, hf⟩ := routeP_paired_negative_unit_at_small_Xi hε 0
  have hlow := hC p e a b
  rw [hf] at hlow
  have hnorm0 := norm_nonneg (routePPairedXiPacket p e a b)
  have hnorm1 := hn.trans_le hεone
  have hsq : ‖routePPairedXiPacket p e a b‖ ^ 2 ≤ ‖routePPairedXiPacket p e a b‖ := by
    nlinarith
  have hm := mul_lt_mul_of_pos_left hn (by positivity : 0 < |C| + 2)
  rw [hεeq] at hm
  have hm2 := mul_le_mul_of_nonneg_left hsq (by positivity : 0 ≤ |C| + 2)
  have hCabs := mul_le_mul_of_nonneg_right (le_abs_self C)
    (sq_nonneg ‖routePPairedXiPacket p e a b‖)
  nlinarith [sq_nonneg ‖routePPairedXiPacket p e a b‖]

end
end RHTower
