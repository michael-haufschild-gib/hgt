import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMEisensteinActualFourierCoefficient

/-!
# Actual zero Fourier coefficient of the completed Poincare series

Corpus research isolated the missing constant-frequency weld after the genuine Poincare
sum/integral exchange: the zero Ramanujan sum is the Dirichlet convolution `id * mu`, hence its
Dirichlet series is `zeta(2s - 1) / zeta(2s)`.  Combining this arithmetic identity with the
corpus Cauchy-power zero transform cancels the completion and yields both Weyl terms exactly.

The headline theorem identifies the zero Fourier coefficient of the actual completed Poincare
function with `d4BMCompletedEisensteinCuspConstantPart`.  Its downstream RH chain is

`actual zero/nonzero coefficients -> Fourier uniqueness -> truncated modular Green/Stokes ->
 polarized BM source -> negative BM leg -> conserved left-QNM projection -> HC94 clock defect -> RH`.

All statements are unconditional in the existing absolute-convergence parameter and introduce
no axioms.
-/

open Complex Finset
open scoped BigOperators ArithmeticFunction.Moebius FourierTransform

namespace RHTower
noncomputable section

def d4BMIdentityArithmeticC : ArithmeticFunction ℂ where
  toFun n := (n : ℂ)
  map_zero' := by simp

theorem d4BM_identity_LSeries_term_eq_shiftedOne
    (w : ℂ) (n : ℕ) :
    LSeries.term d4BMIdentityArithmeticC w n =
      LSeries.term (1 : ℕ → ℂ) (w - 1) n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [LSeries.term_zero]
  · rw [LSeries.term_of_ne_zero hn.ne', LSeries.term_of_ne_zero hn.ne']
    change (n : ℂ) / (n : ℂ) ^ w = 1 / (n : ℂ) ^ (w - 1)
    have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
    calc
      (n : ℂ) / (n : ℂ) ^ w =
          (n : ℂ) * (n : ℂ) ^ (-w) := by
            rw [div_eq_mul_inv, Complex.cpow_neg]
      _ = (n : ℂ) ^ (1 : ℂ) * (n : ℂ) ^ (-w) := by
        rw [Complex.cpow_one]
      _ = (n : ℂ) ^ ((1 : ℂ) + (-w)) :=
        (Complex.cpow_add _ _ hnC).symm
      _ = (n : ℂ) ^ (-(w - 1)) := by
        congr 1
        ring
      _ = 1 / (n : ℂ) ^ (w - 1) := by
        rw [one_div, Complex.cpow_neg]

theorem d4BMIdentityArithmeticC_LSeriesSummable
    {w : ℂ} (hw : 2 < w.re) :
    LSeriesSummable d4BMIdentityArithmeticC w := by
  unfold LSeriesSummable
  have hshift : 1 < (w - 1).re := by
    norm_num [Complex.sub_re]
    linarith
  have hbase : Summable (LSeries.term (1 : ℕ → ℂ) (w - 1)) :=
    LSeriesSummable_one_iff.mpr hshift
  exact hbase.congr fun n => (d4BM_identity_LSeries_term_eq_shiftedOne w n).symm

theorem LSeries_d4BMIdentityArithmeticC_eq_shiftedZeta
    {w : ℂ} (hw : 2 < w.re) :
    LSeries d4BMIdentityArithmeticC w = riemannZeta (w - 1) := by
  unfold LSeries
  rw [show (fun n => LSeries.term d4BMIdentityArithmeticC w n) =
      LSeries.term (1 : ℕ → ℂ) (w - 1) by
    funext n
    exact d4BM_identity_LSeries_term_eq_shiftedOne w n]
  exact LSeries_one_eq_riemannZeta (by
    norm_num [Complex.sub_re]
    linarith)

def d4BMZeroRamanujanArithmeticC : ArithmeticFunction ℂ :=
  d4BMIdentityArithmeticC * d4BMMoebiusArithmeticC

theorem d4BM_zeroRamanujanArithmeticC_eq_cgl
    (Q : CGLPositiveModulus) :
    d4BMZeroRamanujanArithmeticC Q.value =
      cglRamanujanAdditiveSum Q (0 : ZMod Q.value) := by
  rw [show cglRamanujanAdditiveSum Q (0 : ZMod Q.value) =
      ∑ d ∈ ((0 : ℕ).gcd Q.value).divisors,
        ((d : ℕ) : ℂ) *
          ((ArithmeticFunction.moebius (Q.value / d) : ℤ) : ℂ) by
    simpa using cglRamanujanAdditiveSum_natCast_eq_gcd_mobiusDivisorSum Q 0]
  simp only [Nat.gcd_zero_left]
  unfold d4BMZeroRamanujanArithmeticC
  rw [ArithmeticFunction.mul_apply]
  rw [Nat.sum_divisorsAntidiagonal
    (fun a b => d4BMIdentityArithmeticC a * d4BMMoebiusArithmeticC b)]
  apply Finset.sum_congr rfl
  intro d hd
  rfl

theorem LSeries_d4BMZeroRamanujanArithmeticC_eq_zetaRatio
    {w : ℂ} (hw : 2 < w.re) :
    LSeries d4BMZeroRamanujanArithmeticC w =
      riemannZeta (w - 1) / riemannZeta w := by
  have hid := (d4BMIdentityArithmeticC_LSeriesSummable hw).LSeriesHasSum
  rw [LSeries_d4BMIdentityArithmeticC_eq_shiftedZeta hw] at hid
  have hw1 : 1 < w.re := lt_trans one_lt_two hw
  have hmob := (d4BMMoebiusArithmeticC_LSeriesSummable hw1).LSeriesHasSum
  have hmul := ArithmeticFunction.LSeriesHasSum_mul hid hmob
  have hinv := LSeries_moebiusCoeff_mul_riemannZeta hw1
  have hzeta : riemannZeta w ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at hinv
    exact zero_ne_one hinv
  have hM : LSeries d4BMMoebiusArithmeticC w = (riemannZeta w)⁻¹ := by
    have hseq : d4BMMoebiusArithmeticC = moebiusCoeffC := by
      funext q
      rfl
    rw [hseq]
    rw [show (riemannZeta w)⁻¹ = 1 / riemannZeta w by rw [one_div]]
    exact (eq_div_iff hzeta).2 hinv
  have hvalue : LSeries d4BMZeroRamanujanArithmeticC w =
      riemannZeta (w - 1) * LSeries d4BMMoebiusArithmeticC w :=
    hmul.LSeries_eq
  rw [hvalue, hM, div_eq_mul_inv]

def d4BMZeroRamanujanPNatTerm
    (P : D4BMEisensteinAbsoluteConvergenceParameter) (q : ℕ+) : ℂ :=
  cglRamanujanAdditiveSum (d4BMPositiveModulusOfPNat q)
      (0 : ZMod (d4BMPositiveModulusOfPNat q).value) *
    ((((q : ℕ) : ℝ) : ℂ)) ^ (-(2 * P.s))

theorem tsum_d4BMZeroRamanujanPNatTerm_eq_zetaRatio
    (P : D4BMEisensteinAbsoluteConvergenceParameter) :
    (∑' q : ℕ+, d4BMZeroRamanujanPNatTerm P q) =
      riemannZeta (2 * P.s - 1) / riemannZeta (2 * P.s) := by
  have hw : 2 < (2 * P.s).re := by
    norm_num [Complex.mul_re]
    nlinarith [P.re_gt_one]
  rw [← LSeries_d4BMZeroRamanujanArithmeticC_eq_zetaRatio hw]
  unfold LSeries
  calc
    (∑' q : ℕ+, d4BMZeroRamanujanPNatTerm P q) =
        ∑' q : ℕ+,
          LSeries.term d4BMZeroRamanujanArithmeticC (2 * P.s) q := by
      apply tsum_congr
      intro q
      rw [LSeries.term_of_ne_zero q.ne_zero]
      have hzero := d4BM_zeroRamanujanArithmeticC_eq_cgl
        (d4BMPositiveModulusOfPNat q)
      change d4BMZeroRamanujanArithmeticC (q : ℕ) =
        cglRamanujanAdditiveSum (d4BMPositiveModulusOfPNat q)
          (0 : ZMod (d4BMPositiveModulusOfPNat q).value) at hzero
      rw [hzero]
      unfold d4BMZeroRamanujanPNatTerm
      rw [div_eq_mul_inv, ← Complex.cpow_neg]
      rfl
    _ = ∑' q : ℕ,
        {q : ℕ | 0 < q}.indicator
          (LSeries.term d4BMZeroRamanujanArithmeticC (2 * P.s)) q :=
      tsum_subtype {q : ℕ | 0 < q}
        (LSeries.term d4BMZeroRamanujanArithmeticC (2 * P.s))
    _ = ∑' q : ℕ,
        LSeries.term d4BMZeroRamanujanArithmeticC (2 * P.s) q := by
      apply tsum_congr
      intro q
      rcases Nat.eq_zero_or_pos q with rfl | hq
      · simp only [Set.indicator_apply, Set.mem_setOf_eq, lt_self_iff_false,
          if_false, LSeries.term_zero]
      · simp only [Set.indicator_apply, Set.mem_setOf_eq, if_pos hq]

theorem d4BM_actualRawPoincare_zeroFourierCoefficient_eq_zetaRatio
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) :
    (∫ x in Set.Ioc (0 : ℝ) 1,
      fourier (0 : ℤ) (x : UnitAddCircle) *
        d4BMRawEisensteinHorizontalFunction z P x) =
      (z.y : ℂ) ^ P.s +
        ((z.y : ℂ) ^ P.s *
          𝓕 (d4BMCauchyPowerKernel z P.s) 0) *
          (riemannZeta (2 * P.s - 1) / riemannZeta (2 * P.s)) := by
  have hformula := d4BM_actualRawPoincare_fourierCoefficient_eq_sliceFormula z P 0
  simp only [neg_zero, Int.cast_zero] at hformula
  rw [hformula]
  have hconst := d4BM_integral_unit_fourier_character_mul_constant 0 ((z.y : ℂ) ^ P.s)
  simp only [neg_zero] at hconst
  rw [hconst]
  let A : ℂ := (z.y : ℂ) ^ P.s *
    𝓕 (d4BMCauchyPowerKernel z P.s) 0
  congr 1
  calc
    (∑' Q : ℕ+,
        (((z.y : ℂ) ^ P.s *
            ((((d4BMPositiveModulusOfPNat Q).value : ℝ) : ℂ)) ^ (-(2 * P.s))) *
          cglRamanujanAdditiveSum (d4BMPositiveModulusOfPNat Q)
            (0 : ZMod (d4BMPositiveModulusOfPNat Q).value) *
          𝓕 (d4BMCauchyPowerKernel z P.s) 0)) =
        ∑' Q : ℕ+, A * d4BMZeroRamanujanPNatTerm P Q := by
      apply tsum_congr
      intro Q
      dsimp only [A]
      unfold d4BMZeroRamanujanPNatTerm
      have hbase :
          ((((d4BMPositiveModulusOfPNat Q).value : ℝ) : ℂ)) ^ (-(2 * P.s)) =
            ((((Q : ℕ) : ℝ) : ℂ)) ^ (-(2 * P.s)) := by
        rfl
      rw [hbase]
      ring
    _ = A * ∑' Q : ℕ+, d4BMZeroRamanujanPNatTerm P Q := tsum_mul_left
    _ = A * (riemannZeta (2 * P.s - 1) / riemannZeta (2 * P.s)) := by
      rw [tsum_d4BMZeroRamanujanPNatTerm_eq_zetaRatio]
    _ = ((z.y : ℂ) ^ P.s *
          𝓕 (d4BMCauchyPowerKernel z P.s) 0) *
          (riemannZeta (2 * P.s - 1) / riemannZeta (2 * P.s)) := rfl

theorem d4BM_actualCompletedPoincare_zeroFourierCoefficient_eq_completedZetaRatio
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) :
    (∫ x in Set.Ioc (0 : ℝ) 1,
      fourier (0 : ℤ) (x : UnitAddCircle) *
        d4BMCompletedEisensteinHorizontalFunction z P x) =
      reflectedCompletedLambda (2 * P.s) *
        ((z.y : ℂ) ^ P.s +
          ((z.y : ℂ) ^ P.s *
            𝓕 (d4BMCauchyPowerKernel z P.s) 0) *
            (riemannZeta (2 * P.s - 1) / riemannZeta (2 * P.s))) := by
  rw [show (fun x : ℝ =>
      fourier (0 : ℤ) (x : UnitAddCircle) *
        d4BMCompletedEisensteinHorizontalFunction z P x) =
      fun x : ℝ => reflectedCompletedLambda (2 * P.s) *
        (fourier (0 : ℤ) (x : UnitAddCircle) *
          d4BMRawEisensteinHorizontalFunction z P x) by
    funext x
    rw [d4BM_completedEisensteinHorizontalFunction_eq_lambda_mul_raw]
    ring]
  rw [MeasureTheory.integral_const_mul]
  rw [d4BM_actualRawPoincare_zeroFourierCoefficient_eq_zetaRatio]

theorem d4BM_completedZeroWeylFactor_eq_reflectedConstantTerm
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) :
    reflectedCompletedLambda (2 * P.s) *
        (((z.y : ℂ) ^ P.s *
          𝓕 (d4BMCauchyPowerKernel z P.s) 0) *
          (riemannZeta (2 * P.s - 1) / riemannZeta (2 * P.s))) =
      reflectedCompletedLambda (2 * P.s - 1) *
        (z.y : ℂ) ^ (1 - P.s) := by
  let u : ℂ := P.s - 1 / 2
  have huRe : 0 < u.re := by
    dsimp only [u]
    norm_num [Complex.sub_re, Complex.div_re]
    linarith [P.re_gt_one]
  have hy : (0 : ℝ) < z.y := z.y_pos
  have hyne : (z.y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hGammaS : Complex.Gamma P.s ≠ 0 := by
    apply Complex.Gamma_ne_zero
    intro k hk
    have hre := congrArg Complex.re hk
    simp only [Complex.neg_re, Complex.natCast_re] at hre
    nlinarith [P.re_gt_one, Nat.cast_nonneg (α := ℝ) k]
  have hGammaU : Complex.Gamma u ≠ 0 := by
    apply Complex.Gamma_ne_zero
    intro k hk
    have hre := congrArg Complex.re hk
    simp only [Complex.neg_re, Complex.natCast_re] at hre
    nlinarith [huRe, Nat.cast_nonneg (α := ℝ) k]
  have hw : 1 < (2 * P.s).re := by
    norm_num [Complex.mul_re]
    linarith [P.re_gt_one]
  have hinv := LSeries_moebiusCoeff_mul_riemannZeta hw
  have hzeta : riemannZeta (2 * P.s) ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at hinv
    exact zero_ne_one hinv
  have hkernelScale :
      (((Real.pi * z.y ^ 2 : ℝ) : ℂ)) ^ (-u) =
        (Real.pi : ℂ) ^ (-u) * (z.y : ℂ) ^ (-2 * u) := by
    rw [show (((Real.pi * z.y ^ 2 : ℝ) : ℂ)) =
        (Real.pi : ℂ) * (((z.y ^ 2 : ℝ) : ℂ)) by push_cast; ring,
      Complex.mul_cpow_ofReal_nonneg Real.pi_pos.le (sq_nonneg z.y)]
    rw [cpow_sq_ofReal hy]
    congr 2
    ring
  have hyScale :
      (z.y : ℂ) ^ P.s * (z.y : ℂ) ^ (-2 * u) =
        (z.y : ℂ) ^ (1 - P.s) := by
    rw [← Complex.cpow_add _ _ hyne]
    congr 1
    dsimp only [u]
    ring
  rw [fourier_d4BMCauchyPowerKernel_zero]
  rw [reflectedCompletedLambda_eq, reflectedCompletedLambda_eq]
  rw [show (2 * P.s) / 2 = P.s by ring,
    show -(2 * P.s) / 2 = -P.s by ring,
    show (2 * P.s - 1) / 2 = u by dsimp only [u]; ring,
    show -(2 * P.s - 1) / 2 = -u by dsimp only [u]; ring]
  rw [show -(P.s - 1 / 2) = -u by rfl]
  rw [hkernelScale]
  rw [show (z.y : ℂ) ^ P.s *
      ((Real.pi : ℂ) ^ P.s / Complex.Gamma P.s *
        (Complex.Gamma u *
          ((Real.pi : ℂ) ^ (-u) * (z.y : ℂ) ^ (-2 * u)))) =
      ((Real.pi : ℂ) ^ P.s / Complex.Gamma P.s *
        Complex.Gamma u * (Real.pi : ℂ) ^ (-u)) *
        ((z.y : ℂ) ^ P.s * (z.y : ℂ) ^ (-2 * u)) by ring]
  rw [hyScale]
  rw [Complex.cpow_neg, Complex.cpow_neg]
  field_simp [hGammaS, hGammaU, hpi, hzeta]

theorem d4BM_actualCompletedPoincare_zeroFourierCoefficient_eq_canonicalConstantPart
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) :
    (∫ x in Set.Ioc (0 : ℝ) 1,
      fourier (0 : ℤ) (x : UnitAddCircle) *
        d4BMCompletedEisensteinHorizontalFunction z P x) =
      d4BMCompletedEisensteinCuspConstantPart .scalar
        (P.s - 1 / 2) z.y := by
  rw [d4BM_actualCompletedPoincare_zeroFourierCoefficient_eq_completedZetaRatio]
  calc
    reflectedCompletedLambda (2 * P.s) *
          ((z.y : ℂ) ^ P.s +
            (z.y : ℂ) ^ P.s *
                𝓕 (d4BMCauchyPowerKernel z P.s) 0 *
              (riemannZeta (2 * P.s - 1) / riemannZeta (2 * P.s))) =
        reflectedCompletedLambda (2 * P.s) * (z.y : ℂ) ^ P.s +
          reflectedCompletedLambda (2 * P.s) *
            (((z.y : ℂ) ^ P.s *
              𝓕 (d4BMCauchyPowerKernel z P.s) 0) *
              (riemannZeta (2 * P.s - 1) / riemannZeta (2 * P.s))) := by ring
    _ = reflectedCompletedLambda (2 * P.s) * (z.y : ℂ) ^ P.s +
          reflectedCompletedLambda (2 * P.s - 1) *
            (z.y : ℂ) ^ (1 - P.s) := by
      rw [d4BM_completedZeroWeylFactor_eq_reflectedConstantTerm]
    _ = d4BMCompletedEisensteinCuspConstantPart .scalar
          (P.s - 1 / 2) z.y := by
      simp [d4BMCompletedEisensteinCuspConstantPart,
        d4BMCompletedEisensteinCuspConstantTerm,
        d4BMCompletedEisensteinCuspConstantCoefficient,
        d4BMCompletedEisensteinCuspConstantMaassFactor,
        d4BMCompletedEisensteinCuspWeylExponent,
        d4BMCuspSign]
      ring_nf

end
end RHTower
