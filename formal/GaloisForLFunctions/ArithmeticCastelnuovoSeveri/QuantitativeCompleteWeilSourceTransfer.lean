import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.QuantitativeCompleteCellMoments
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.QuantitativeCompletePrimeSource
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.CompleteWeilSourceTransfer

/-! # A square-root rate for the literal complete-cell Weil form

The discontinuous sampling error has jump energy of order `1/N`. Its jump
vector gives the only square-root loss; mass, both poles, and the full prime
series retain their `1/N` estimates.
-/

noncomputable section
open MeasureTheory Set RHTower

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri.LogCells

open HTGeometry SpacingScaleHarmonicAnalysis

/-- Coefficient of the jump energy of the actual sampling error. -/
def completeCellJumpRate (f : ℝ → ℝ) (K : ℝ) : ℝ :=
  8 * K * (eVariationOn f univ).toReal * ∫ t in Ioi (0 : ℝ), t * archLevyDensity t

theorem completeCellJumpRate_nonneg (f : ℝ → ℝ) {K : ℝ} (hK : 0 ≤ K) :
    0 ≤ completeCellJumpRate f K := by
  have hJ : 0 ≤ ∫ t in Ioi (0 : ℝ), t * archLevyDensity t := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact mul_nonneg ht.le (archLevyDensity_pos ht).le
  unfold completeCellJumpRate
  positivity

/-- Explicit coefficient of the square-root rate for the Gamma energy. -/
def completeCellGammaRate (f : ℝ → ℝ) (K : ℝ) : ℝ :=
  2 * Real.sqrt (levyEnergy f) * Real.sqrt (completeCellJumpRate f K) + completeCellJumpRate f K

theorem completeCellGammaRate_nonneg (f : ℝ → ℝ) {K : ℝ} (hK : 0 ≤ K) :
    0 ≤ completeCellGammaRate f K := by
  unfold completeCellGammaRate
  exact add_nonneg (by positivity) (completeCellJumpRate_nonneg f hK)

/-- The norm-square difference of the complete jump vectors has a quantitative rate. -/
theorem abs_logStep_levyEnergy_sub_le {f : ℝ → ℝ}
    (hf : BoundedVariationOn f univ) (hc : HasCompactSupport f) {K : NNReal}
    (hK : LipschitzWith K f) (R : ℝ) {N B : ℕ} (hN : 1 ≤ N) (hB : 1 ≤ B)
    (hs : ∀ u, u ≤ -R ∨ Real.log B - R ≤ u → f u = 0) :
    |levyEnergy (logStep f R N) - levyEnergy f| ≤
      completeCellGammaRate f K / Real.sqrt N := by
  let v := levyVector f hf hc
  let w := levyVector (logStep f R N) (boundedVariationOn_logStep hf R hN)
    (hasCompactSupport_logStep R hN hB hs)
  let D := completeCellJumpRate f K
  have hD : 0 ≤ D := completeCellJumpRate_nonneg f K.coe_nonneg
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNs : 1 ≤ Real.sqrt N := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hN1
  have he : ‖w - v‖ ^ 2 ≤ D / N := by
    dsimp only [w, v]
    rw [norm_levyVector_sub_sq]
    exact levyEnergy_logStep_sub_le hf hc hK R hN hB hs
  have hd2 : (Real.sqrt D / Real.sqrt N) ^ 2 = D / N := by
    rw [div_pow, Real.sq_sqrt hD, Real.sq_sqrt (Nat.cast_nonneg N)]
  have hd0 : 0 ≤ Real.sqrt D / Real.sqrt N := by positivity
  have hd : ‖w - v‖ ≤ Real.sqrt D / Real.sqrt N := by
    exact (sq_le_sq₀ (norm_nonneg (w - v)) hd0).mp (he.trans_eq hd2.symm)
  have hnorm : ‖w‖ ≤ ‖v‖ + Real.sqrt D / Real.sqrt N := by
    calc ‖w‖ = ‖v + (w - v)‖ := by congr 1; abel
      _ ≤ ‖v‖ + ‖w - v‖ := norm_add_le _ _
      _ ≤ _ := add_le_add le_rfl hd
  have hdn : Real.sqrt D / Real.sqrt N ≤ Real.sqrt D :=
    div_le_self (Real.sqrt_nonneg D) hNs
  have hsq : |‖w‖ ^ 2 - ‖v‖ ^ 2| ≤
      (2 * ‖v‖ * Real.sqrt D + D) / Real.sqrt N := by
    calc |‖w‖ ^ 2 - ‖v‖ ^ 2| = |‖w‖ - ‖v‖| * (‖w‖ + ‖v‖) := by
          rw [← abs_of_nonneg (add_nonneg (norm_nonneg w) (norm_nonneg v)), ← abs_mul]
          congr 1; ring
      _ ≤ (Real.sqrt D / Real.sqrt N) * (2 * ‖v‖ + Real.sqrt D) :=
        mul_le_mul ((abs_norm_sub_norm_le w v).trans hd)
          (by linarith only [hnorm, hdn])
          (add_nonneg (norm_nonneg w) (norm_nonneg v)) hd0
      _ = (2 * ‖v‖ * Real.sqrt D + D) / Real.sqrt N := by
        rw [div_mul_eq_mul_div]
        congr 1
        calc Real.sqrt D * (2 * ‖v‖ + Real.sqrt D) =
            2 * ‖v‖ * Real.sqrt D + Real.sqrt D ^ 2 := by ring
          _ = _ := by rw [Real.sq_sqrt hD]
  have hv : ‖v‖ ^ 2 = levyEnergy f := norm_levyVector_sq f hf hc
  have hw : ‖w‖ ^ 2 = levyEnergy (logStep f R N) := norm_levyVector_sq _ _ _
  have hvroot : ‖v‖ = Real.sqrt (levyEnergy f) := by
    rw [← hv, Real.sqrt_sq_eq_abs, abs_norm]
  rw [hv, hw, hvroot] at hsq
  exact hsq

/-- Every term of the complete form, with one explicit coefficient. -/
def completeCellWeilRate (f : ℝ → ℝ) (R : ℝ) (B : ℕ) (C K : ℝ) : ℝ :=
  completeCellGammaRate f K + completeCellPrimeRate B C K +
    4 * |gammaHardyPhaseRate 0| * C * K * Real.log B +
    4 * C * K *
      (cellWindowWeight R B (fun u => Real.cosh (u / 2)) ^ 2 +
        cellWindowWeight R B (fun u => Real.sinh (u / 2)) ^ 2)

theorem completeCellWeilRate_nonneg (f : ℝ → ℝ) (R : ℝ) {B : ℕ}
    (hB : 1 ≤ B) {C K : ℝ} (hC : 0 ≤ C) (hK : 0 ≤ K) :
    0 ≤ completeCellWeilRate f R B C K := by
  have hlog : 0 ≤ Real.log B := Real.log_nonneg (by exact_mod_cast hB)
  have hgamma := completeCellGammaRate_nonneg f hK
  have hprime := completeCellPrimeRate_nonneg B hC hK
  unfold completeCellWeilRate
  positivity

private theorem div_nat_le_div_sqrt {C : ℝ} (hC : 0 ≤ C) {N : ℕ} (hN : 1 ≤ N) :
    C / N ≤ C / Real.sqrt N := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hs1 : 1 ≤ Real.sqrt N := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hN1
  have hs : Real.sqrt N ≤ N := by
    nlinarith only [hs1, Real.sq_sqrt (Nat.cast_nonneg N)]
  exact div_le_div_of_nonneg_left hC (lt_of_lt_of_le zero_lt_one hs1) hs

private theorem abs_full_form_sub_le (a m m' g g' p p' c c' s s' : ℝ) :
    |(2 * a * m + g - p + (2 * c ^ 2 - 2 * s ^ 2)) -
      (2 * a * m' + g' - p' + (2 * c' ^ 2 - 2 * s' ^ 2))| ≤
      2 * |a| * |m - m'| + |g - g'| + |p - p'| +
        2 * |c ^ 2 - c' ^ 2| + 2 * |s ^ 2 - s' ^ 2| := by
  have hsub (x y : ℝ) : |x - y| ≤ |x| + |y| := by
    simpa only [sub_zero, zero_sub, abs_neg] using abs_sub_le x 0 y
  calc _ = |(2 * a * (m - m') + (g - g') - (p - p')) +
        (2 * (c ^ 2 - c' ^ 2) - 2 * (s ^ 2 - s' ^ 2))| := by congr 1; ring
    _ ≤ |2 * a * (m - m') + (g - g') - (p - p')| +
        |2 * (c ^ 2 - c' ^ 2) - 2 * (s ^ 2 - s' ^ 2)| := abs_add_le _ _
    _ ≤ (|2 * a * (m - m') + (g - g')| + |p - p'|) +
        (|2 * (c ^ 2 - c' ^ 2)| + |2 * (s ^ 2 - s' ^ 2)|) :=
      add_le_add (hsub _ _) (hsub _ _)
    _ ≤ ((|2 * a * (m - m')| + |g - g'|) + |p - p'|) +
        (|2 * (c ^ 2 - c' ^ 2)| + |2 * (s ^ 2 - s' ^ 2)|) :=
      add_le_add (add_le_add (abs_add_le _ _) le_rfl) le_rfl
    _ = _ := by norm_num only [abs_mul]; ring

/-- The entire arithmetic cell form converges with an explicit square-root error. -/
theorem abs_completeCellWeil_sub_le {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hc : HasCompactSupport f) {K : NNReal} (hK : LipschitzWith K f)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ u, |f u| ≤ C) (R : ℝ) {N B : ℕ}
    (hN : 1 ≤ N) (hB : 1 ≤ B)
    (hs : ∀ u, u ≤ -R ∨ Real.log B - R ≤ u → f u = 0) :
    |completeCellWeil f R N B - weilQuad f| ≤ completeCellWeilRate f R B C K / Real.sqrt N := by
  have hlog : 0 ≤ Real.log B := Real.log_nonneg (by exact_mod_cast hB)
  have hv := boundedVariationOn_of_contDiff_compact (hf.of_le (by norm_num)) hc
  have hm := (abs_logStep_mass_sub_le hK hb R hN hB hs).trans
    (div_nat_le_div_sqrt (by positivity) hN)
  have hg := abs_logStep_levyEnergy_sub_le hv hc hK R hN hB hs
  have hp := (abs_cellPrimeEnergy_sub_primeSum_le hK hC hb R hN hB hs).trans
    (div_nat_le_div_sqrt (completeCellPrimeRate_nonneg B hC K.coe_nonneg) hN)
  have hcosh := (abs_logStep_weightedMoment_sq_sub_le hK
    (w := fun u => Real.cosh (u / 2)) (by fun_prop) hb R hN hB hs).trans
    (div_nat_le_div_sqrt (by positivity) hN)
  have hsinh := (abs_logStep_weightedMoment_sq_sub_le hK
    (w := fun u => Real.sinh (u / 2)) (by fun_prop) hb R hN hB hs).trans
    (div_nat_le_div_sqrt (by positivity) hN)
  change |coshHalfMoment (logStep f R N) ^ 2 - coshHalfMoment f ^ 2| ≤ _ at hcosh
  change |sinhHalfMoment (logStep f R N) ^ 2 - sinhHalfMoment f ^ 2| ≤ _ at hsinh
  rw [completeCellWeil_eq R hN hB hs, weilQuad_eq hf hc]
  refine (abs_full_form_sub_le _ _ _ _ _ _ _ _ _ _ _).trans ?_
  calc
    _ ≤ 2 * |gammaHardyPhaseRate 0| *
          (2 * C * (K : ℝ) * Real.log B / Real.sqrt N) +
        completeCellGammaRate f K / Real.sqrt N +
        completeCellPrimeRate B C K / Real.sqrt N +
        2 * (2 * C * (K : ℝ) * cellWindowWeight R B (fun u => Real.cosh (u / 2)) ^ 2 /
          Real.sqrt N) +
        2 * (2 * C * (K : ℝ) * cellWindowWeight R B (fun u => Real.sinh (u / 2)) ^ 2 /
          Real.sqrt N) := by
      exact add_le_add
        (add_le_add (add_le_add
          (add_le_add (mul_le_mul_of_nonneg_left hm (by positivity)) hg) hp)
          (mul_le_mul_of_nonneg_left hcosh (by norm_num)))
        (mul_le_mul_of_nonneg_left hsinh (by norm_num))
    _ = completeCellWeilRate f R B C K / Real.sqrt N := by
      unfold completeCellWeilRate
      ring

/-- Point value plus total variation is a canonical global supremum bound. -/
def completeCellSourceBound (f : ℝ → ℝ) : ℝ := ‖f 0‖ + (eVariationOn f univ).toReal

theorem completeCellSourceBound_nonneg (f : ℝ → ℝ) : 0 ≤ completeCellSourceBound f :=
  add_nonneg (norm_nonneg _) ENNReal.toReal_nonneg

/-- The derivative's canonical supremum bound supplies the sampling Lipschitz constant. -/
def completeCellSourceLip (f : ℝ → ℝ) : NNReal :=
  ⟨completeCellSourceBound (deriv f), completeCellSourceBound_nonneg _⟩

theorem abs_le_completeCellSourceBound {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f) (u : ℝ) :
    |f u| ≤ completeCellSourceBound f := by
  have hv := boundedVariationOn_of_contDiff_compact (hf.of_le (by norm_num)) hc
  simpa only [Real.norm_eq_abs, completeCellSourceBound] using norm_le_of_boundedVariation_univ hv u

theorem lipschitzWith_completeCellSourceLip {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f) : LipschitzWith (completeCellSourceLip f) f := by
  have hd : ContDiff ℝ 1 (deriv f) := hf.deriv'
  have hv := boundedVariationOn_of_contDiff_compact hd hc.deriv
  apply lipschitzWith_of_nnnorm_deriv_le (hf.differentiable (by norm_num))
  intro u
  exact norm_le_of_boundedVariation_univ hv u

/-- The rate constant uses only the source itself and its support window. -/
def canonicalCompleteCellRate (f : ℝ → ℝ) (R : ℝ) (B : ℕ) : ℝ :=
  completeCellWeilRate f R B (completeCellSourceBound f) (completeCellSourceLip f)

theorem canonicalCompleteCellRate_nonneg (f : ℝ → ℝ) (R : ℝ) {B : ℕ} (hB : 1 ≤ B) :
    0 ≤ canonicalCompleteCellRate f R B :=
  completeCellWeilRate_nonneg f R hB (completeCellSourceBound_nonneg f)
    (completeCellSourceLip f).coe_nonneg

/-- Compact `C²` regularity discharges every analytic bound in the explicit rate. -/
theorem abs_completeCellWeil_sub_le_canonical {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hc : HasCompactSupport f) (R : ℝ) {N B : ℕ} (hN : 1 ≤ N) (hB : 1 ≤ B)
    (hs : ∀ u, u ≤ -R ∨ Real.log B - R ≤ u → f u = 0) :
    |completeCellWeil f R N B - weilQuad f| ≤ canonicalCompleteCellRate f R B / Real.sqrt N :=
  abs_completeCellWeil_sub_le hf hc (lipschitzWith_completeCellSourceLip hf hc)
    (completeCellSourceBound_nonneg f) (abs_le_completeCellSourceBound hf hc) R hN hB hs

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri.LogCells

#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.LogCells.abs_logStep_levyEnergy_sub_le
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.LogCells.abs_completeCellWeil_sub_le
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.LogCells.abs_completeCellWeil_sub_le_canonical
