import GaloisForLFunctions.RHTower.RoutePPrimitiveBurnolWindowGramSquare

/-!
# Frankenstein primitive--Xi mixed Burnol Schur gap

P-G186 constructs the complete primitive Euler Burnol-window Gram, while the completed-Xi
conormal modules construct the target Gram.  This module computes their missing mixed entry
without scalarizing either family.  The entry is the same coefficient-faithful Cauchy cube with
one Euler rate and one actual Xi rate.

The mixed block does not supply the desired boundary restriction.  Every primitive Euler rate is
at least `log 2`, whereas every strict-right centered Xi rate is below `1/2`.  Their normalized
coherence is therefore strictly below one, and the two-node Gram determinant is strictly positive
at every ordinate.  Ordinary Hilbert projection leaves a nonzero Schur residual in the Xi column;
block positivity gives the opposite direction from Route P's required domination.

This is the exact positive survivor of the failed pure-Gram landing.  Any successful completed
boundary theorem must change the geometry before positive compression: the polar--Gamma channel
must be shorted in a signed/relative colligation, not appended as another positive Gram column.
-/

open Complex Set MeasureTheory
open scoped ComplexOrder

namespace RHTower

noncomputable section

/-- Exact mixed primitive-Euler/actual-conormal Burnol overlap.  Prime-depth amplitude, Euler
frequency, target horizontal rate, and ordinate difference all remain visible. -/
theorem integral_star_routePPrimitiveBurnolWindowFeature_mul_xiConormal
    (pe : Nat.Primes × ℕ) (kappa : ℝ) {rho : ℂ}
    (hrho : 1 / 2 < rho.re) :
    (∫ L : ℝ in Ioi 0,
      star (routePPrimitiveBurnolWindowFeature pe kappa L) *
        xiWardCubicBurnolWindowConormalFeature L rho) =
      finiteVonMangoldtDepthOneAmplitude (xiGammaEulerValuationNat pe) *
        routePBaseCauchyCubicKernel 1
          (xiGammaEulerPrimitiveLogFrequency pe)
          (rho - 1 / 2).re ((rho - 1 / 2).im - kappa) := by
  let A : ℂ := finiteVonMangoldtDepthOneAmplitude (xiGammaEulerValuationNat pe)
  let sigma : ℂ := routePPrimitiveBurnolSpectralPoint pe kappa
  have hsigma : 1 / 2 < sigma.re := routePPrimitiveBurnolSpectralPoint_right pe kappa
  rw [show (fun L : ℝ =>
      star (routePPrimitiveBurnolWindowFeature pe kappa L) *
        xiWardCubicBurnolWindowConormalFeature L rho) =
      fun L : ℝ => star A *
        (star (routePXiBaseConormalResidueFeature sigma L) *
          routePXiBaseConormalResidueFeature rho L) by
    funext L
    simp only [routePPrimitiveBurnolWindowFeature,
      xiWardCubicBurnolWindowConormalFeature_eq]
    dsimp [A, sigma]
    rw [map_mul]
    ring]
  rw [MeasureTheory.integral_const_mul,
    integral_star_routePXiBaseConormalResidueFeature_mul hsigma hrho]
  dsimp [A, sigma]
  rw [routePPrimitiveBurnolSpectralPoint_re,
    routePPrimitiveBurnolSpectralPoint_im]
  simp [finiteVonMangoldtDepthOneAmplitude]

/-- Squared norm of one unweighted mixed Cauchy-cube entry. -/
theorem normSq_routePBaseCauchyCubicKernel
    {a b kappa : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Complex.normSq (routePBaseCauchyCubicKernel 1 a b kappa) =
      4 / (((a + b) ^ 2 + kappa ^ 2) ^ 3) := by
  rw [routePBaseCauchyCubicKernel, Complex.normSq_div,
    Complex.normSq_mul]
  rw [show routePCollisionPairFrequency 1 a b kappa ^ 3 =
      routePCollisionPairFrequency 1 a b kappa *
        routePCollisionPairFrequency 1 a b kappa *
          routePCollisionPairFrequency 1 a b kappa by ring,
    Complex.normSq_mul, Complex.normSq_mul]
  norm_num
  rw [Complex.normSq_apply]
  simp [routePCollisionPairFrequency]
  field_simp

/-- Squared normalized coherence of two unweighted cubic radial conormals. -/
def routePBaseCauchyCubicNormalizedCoherenceSq
    (a b kappa : ℝ) : ℝ :=
  64 * a ^ 3 * b ^ 3 / (((a + b) ^ 2 + kappa ^ 2) ^ 3)

/-- Normalized coherence is strict unless both radial rates and ordinates coincide. -/
theorem routePBaseCauchyCubicNormalizedCoherenceSq_lt_one
    {a b kappa : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hne : a ≠ b ∨ kappa ≠ 0) :
    routePBaseCauchyCubicNormalizedCoherenceSq a b kappa < 1 := by
  have hgap : 0 < (a - b) ^ 2 + kappa ^ 2 := by
    rcases hne with hab | hk
    · have hs : 0 < (a - b) ^ 2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hab)
      nlinarith [sq_nonneg kappa]
    · have hs : 0 < kappa ^ 2 := sq_pos_of_ne_zero hk
      nlinarith [sq_nonneg (a - b)]
  have hleft : 0 < 4 * a * b := by positivity
  have hlt : 4 * a * b < (a + b) ^ 2 + kappa ^ 2 := by
    nlinarith
  have hright : 0 < (a + b) ^ 2 + kappa ^ 2 := hleft.trans hlt
  have hcubes : (4 * a * b) ^ 3 <
      ((a + b) ^ 2 + kappa ^ 2) ^ 3 :=
    pow_lt_pow_left₀ hlt hleft.le (by norm_num)
  rw [show (4 * a * b) ^ 3 = 64 * a ^ 3 * b ^ 3 by ring] at hcubes
  rw [routePBaseCauchyCubicNormalizedCoherenceSq,
    div_lt_one (pow_pos hright 3)]
  exact hcubes

/-- Strict spectral separation: every primitive Euler Burnol rate lies above every strict-right
centered Xi rate. -/
theorem xiRightCenteredZero_re_lt_primitiveBurnolLogFrequency
    (pe : Nat.Primes × ℕ) (q : XiRightZeroCopy) :
    (xiRightCenteredZero q).re < xiGammaEulerPrimitiveLogFrequency pe := by
  have hpow : (pe.1 : ℕ) ≤ (pe.1 : ℕ) ^ (pe.2 + 1) := by
    rw [pow_succ]
    exact Nat.le_mul_of_pos_left _ (pow_pos pe.1.prop.pos pe.2)
  have hval : (2 : ℕ) ≤ xiGammaEulerValuationNat pe := by
    rw [xiGammaEulerValuationNat]
    exact pe.1.prop.two_le.trans hpow
  have hlog : Real.log 2 ≤ xiGammaEulerPrimitiveLogFrequency pe := by
    rw [xiGammaEulerPrimitiveLogFrequency]
    exact Real.log_le_log (by norm_num) (by exact_mod_cast hval)
  have hhalf : (xiRightCenteredZero q).re < 1 / 2 :=
    (abs_lt.mp (abs_xiRightCenteredZero_re_lt_half q)).2
  nlinarith [Real.log_two_gt_d9]

/-- Actual primitive/Xi normalized mixed coherence. -/
def routePPrimitiveXiBurnolNormalizedCoherenceSq
    (pe : Nat.Primes × ℕ) (kappa : ℝ) (q : XiRightZeroCopy) : ℝ :=
  routePBaseCauchyCubicNormalizedCoherenceSq
    (xiGammaEulerPrimitiveLogFrequency pe)
    (xiRightCenteredZero q).re
    ((xiRightCenteredZero q).im - kappa)

/-- No primitive Euler Burnol column is collinear with an actual strict-right Xi conormal column,
even when their ordinate clocks agree. -/
theorem routePPrimitiveXiBurnolNormalizedCoherenceSq_lt_one
    (pe : Nat.Primes × ℕ) (kappa : ℝ) (q : XiRightZeroCopy) :
    routePPrimitiveXiBurnolNormalizedCoherenceSq pe kappa q < 1 := by
  apply routePBaseCauchyCubicNormalizedCoherenceSq_lt_one
    (xiGammaEulerPrimitiveLogFrequency_pos pe)
    (xiRightCenteredZero_re_pos q)
  exact Or.inl (ne_of_gt
    (xiRightCenteredZero_re_lt_primitiveBurnolLogFrequency pe q))

/-- Real determinant of the unweighted two-node cubic conormal Gram. -/
def routePBaseCauchyCubicTwoNodeGramDet
    (a b kappa : ℝ) : ℝ :=
  (1 / (4 * a ^ 3)) * (1 / (4 * b ^ 3)) -
    Complex.normSq (routePBaseCauchyCubicKernel 1 a b kappa)

/-- The two-node Gram has a strict Schur residual whenever rate or ordinate differs. -/
theorem routePBaseCauchyCubicTwoNodeGramDet_pos
    {a b kappa : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hne : a ≠ b ∨ kappa ≠ 0) :
    0 < routePBaseCauchyCubicTwoNodeGramDet a b kappa := by
  have hcoh := routePBaseCauchyCubicNormalizedCoherenceSq_lt_one ha hb hne
  have hscale : 0 < (1 / (16 * a ^ 3 * b ^ 3) : ℝ) := by positivity
  rw [routePBaseCauchyCubicTwoNodeGramDet,
    normSq_routePBaseCauchyCubicKernel ha hb]
  have hid :
      (1 / (4 * a ^ 3)) * (1 / (4 * b ^ 3)) -
          4 / (((a + b) ^ 2 + kappa ^ 2) ^ 3) =
        (1 / (16 * a ^ 3 * b ^ 3)) *
          (1 - routePBaseCauchyCubicNormalizedCoherenceSq a b kappa) := by
    unfold routePBaseCauchyCubicNormalizedCoherenceSq
    field_simp [ha.ne', hb.ne']
    ring
  rw [hid]
  exact mul_pos hscale (sub_pos.mpr hcoh)

/-- **Strict mixed Schur gap.** Every canonical Euler source node and every actual strict-right Xi
node span a positive-definite two-column cubic Burnol Gram.  The target column retains nonzero
energy after projection onto that source atom. -/
theorem routePPrimitiveXiBurnolTwoNodeGramDet_pos
    (pe : Nat.Primes × ℕ) (kappa : ℝ) (q : XiRightZeroCopy) :
    0 < routePBaseCauchyCubicTwoNodeGramDet
      (xiGammaEulerPrimitiveLogFrequency pe)
      (xiRightCenteredZero q).re
      ((xiRightCenteredZero q).im - kappa) := by
  apply routePBaseCauchyCubicTwoNodeGramDet_pos
    (xiGammaEulerPrimitiveLogFrequency_pos pe)
    (xiRightCenteredZero_re_pos q)
  exact Or.inl (ne_of_gt
    (xiRightCenteredZero_re_lt_primitiveBurnolLogFrequency pe q))

end


end RHTower
