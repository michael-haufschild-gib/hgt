import GaloisForLFunctions.RHTower.CesaroSignRecurrence
import GaloisForLFunctions.RHTower.XiResolventHankelEquivalence
import GaloisForLFunctions.RHTower.XiShiftedHardEdgeCayleyDivisorLift
import GaloisForLFunctions.RHTower.XiOrdinateEndpointObstruction
import GaloisForLFunctions.RHTower.XiReciprocalTranslationSeamNormLaw
import GaloisForLFunctions.RHTower.HedenmalmThetaCayleyTools
import GaloisForLFunctions.RHTower.XiWeilTwoChannelResolvent
import GaloisForLFunctions.RHTower.XiSquaredCompleteMonotonicityFarRay
import GaloisForLFunctions.RHTower.CayleyChebyshevSource
import GaloisForLFunctions.RHTower.CayleyLaguerreFourier

open Complex Filter Topology Polynomial
open scoped BigOperators

namespace RHTower

noncomputable section

def xiCayleyChebyshevPhase (q : XiZeroCopy) : ℂ :=
  xiHardEdgeCayleyPhase 1 (xiSpectralPoint q)

def xiCayleyChebyshevMode (q : XiZeroCopy) : ℂ :=
  xiCayleyChebyshevPhase q ^ 2

def xiCayleyChebyshevPolynomial (n : ℕ) : Polynomial ℝ :=
  xiHardEdgeReciprocalPolynomial 1 (Polynomial.Chebyshev.T ℝ (n : ℤ))

def xiCayleyChebyshevCoefficient (n : ℕ) : ℂ :=
  xiResolventTrace 1 (xiCayleyChebyshevPolynomial n)

theorem xiCayleyChebyshevPhase_ne_zero (q : XiZeroCopy) :
    xiCayleyChebyshevPhase q ≠ 0 := by
  exact div_ne_zero (add_I_mul_spectral_ne_zero (by norm_num) q)
    (sub_I_mul_spectral_ne_zero (by norm_num) q)

theorem xiCayleyChebyshevPhase_reflect (q : XiZeroCopy) :
    xiCayleyChebyshevPhase (xiZeroCopyReflectEquiv q) =
      (xiCayleyChebyshevPhase q)⁻¹ := by
  rw [xiCayleyChebyshevPhase, xiCayleyChebyshevPhase,
    xiHardEdgeCayleyPhase, xiHardEdgeCayleyPhase, xiSpectralPoint_reflect]
  simpa [sub_eq_add_neg, add_comm] using
    (inv_div ((1 : ℂ) + Complex.I * xiSpectralPoint q)
      ((1 : ℂ) - Complex.I * xiSpectralPoint q)).symm

theorem xiCayleyChebyshevPhase_copyConj (q : XiZeroCopy) :
    xiCayleyChebyshevPhase (xiZeroCopyConjEquiv q) =
      star (xiCayleyChebyshevPhase q) := by
  rw [xiCayleyChebyshevPhase, xiCayleyChebyshevPhase,
    xiHardEdgeCayleyPhase, xiHardEdgeCayleyPhase, xiSpectralPoint_copyConj]
  change ((1 : ℂ) + Complex.I * (-star (xiSpectralPoint q))) /
      ((1 : ℂ) - Complex.I * (-star (xiSpectralPoint q))) =
    star (((1 : ℂ) + Complex.I * xiSpectralPoint q) /
      ((1 : ℂ) - Complex.I * xiSpectralPoint q))
  conv_rhs =>
    rw [← starRingEnd_apply, map_div₀, map_add, map_mul, map_one,
      map_sub, Complex.conj_I]
  simp

theorem xiCayleyChebyshevMode_reflect (q : XiZeroCopy) :
    xiCayleyChebyshevMode (xiZeroCopyReflectEquiv q) =
      (xiCayleyChebyshevMode q)⁻¹ := by
  rw [xiCayleyChebyshevMode, xiCayleyChebyshevMode,
    xiCayleyChebyshevPhase_reflect, inv_pow]

theorem xiCayleyChebyshevMode_copyConj (q : XiZeroCopy) :
    xiCayleyChebyshevMode (xiZeroCopyConjEquiv q) =
      star (xiCayleyChebyshevMode q) := by
  rw [xiCayleyChebyshevMode, xiCayleyChebyshevMode,
    xiCayleyChebyshevPhase_copyConj]
  exact (map_pow (starRingEnd ℂ) (xiCayleyChebyshevPhase q) 2).symm

theorem xiResolventPoint_one_reflect (q : XiZeroCopy) :
    xiResolventPoint 1 (xiZeroCopyReflectEquiv q) = xiResolventPoint 1 q := by
  rw [xiResolventPoint, xiResolventPoint, xiSpectralPoint_reflect, neg_sq]

theorem xiResolventPoint_one_copyConj (q : XiZeroCopy) :
    xiResolventPoint 1 (xiZeroCopyConjEquiv q) = star (xiResolventPoint 1 q) := by
  rw [xiResolventPoint, xiResolventPoint, xiSpectralPoint_copyConj,
    neg_sq]
  change (star (xiSpectralPoint q) ^ 2 + 1)⁻¹ =
    star ((xiSpectralPoint q ^ 2 + 1)⁻¹)
  simp

theorem one_lt_norm_xiCayleyChebyshevPhase_of_im_neg
    {q : XiZeroCopy} (hq : (xiSpectralPoint q).im < 0) :
    1 < ‖xiCayleyChebyshevPhase q‖ := by
  apply HedenmalmThetaSource.one_lt_norm_cayley_of_re_pos
  · simp [Complex.mul_re]
    linarith
  · exact sub_I_mul_spectral_ne_zero (by norm_num) q

theorem exists_one_lt_norm_xiCayleyChebyshevMode_of_not_rh
    (hRH : ¬ RiemannHypothesis) :
    ∃ q : XiZeroCopy, 1 < ‖xiCayleyChebyshevMode q‖ := by
  have hnot : ¬ ∀ q : XiZeroCopy, (xiSpectralPoint q).im = 0 := by
    intro h
    exact hRH (xiSpectralPoint_im_eq_zero_iff_rh.mpr h)
  push Not at hnot
  obtain ⟨q, hq⟩ := hnot
  rcases lt_or_gt_of_ne hq with hneg | hpos
  · refine ⟨q, ?_⟩
    rw [xiCayleyChebyshevMode, norm_pow]
    nlinarith [one_lt_norm_xiCayleyChebyshevPhase_of_im_neg hneg]
  · refine ⟨xiZeroCopyLineConjEquiv q, ?_⟩
    have hline : (xiSpectralPoint (xiZeroCopyLineConjEquiv q)).im < 0 := by
      rw [xiSpectralPoint_lineConj, Complex.conj_im]
      linarith
    rw [xiCayleyChebyshevMode, norm_pow]
    nlinarith [one_lt_norm_xiCayleyChebyshevPhase_of_im_neg hline]


theorem tendsto_xiSpectralPoint_inv_cofinite_zero :
    Tendsto (fun q : XiZeroCopy => (xiSpectralPoint q)⁻¹)
      cofinite (nhds 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  convert tendsto_inv_atTop_zero.comp tendsto_norm_xiSpectralPoint_cofinite using 1
  funext q
  simp only [Function.comp_apply, norm_inv]

theorem tendsto_xiCayleyChebyshevPhase_cofinite_neg_one :
    Tendsto xiCayleyChebyshevPhase cofinite (nhds (-1)) := by
  have hinv := tendsto_xiSpectralPoint_inv_cofinite_zero
  have hI : Tendsto (fun _ : XiZeroCopy => Complex.I) cofinite (nhds Complex.I) :=
    tendsto_const_nhds
  have hquot := (hinv.add hI).div
    (hinv.sub hI) (by norm_num : (0 : ℂ) - Complex.I ≠ 0)
  convert hquot using 1
  · funext q
    rw [xiCayleyChebyshevPhase, xiHardEdgeCayleyPhase]
    have hα := xiSpectralPoint_ne_zero q
    change ((1 : ℂ) + Complex.I * xiSpectralPoint q) /
        ((1 : ℂ) - Complex.I * xiSpectralPoint q) =
      ((xiSpectralPoint q)⁻¹ + Complex.I) /
        ((xiSpectralPoint q)⁻¹ - Complex.I)
    field_simp [hα]
  · norm_num

theorem tendsto_xiCayleyChebyshevMode_cofinite_one :
    Tendsto xiCayleyChebyshevMode cofinite (nhds 1) := by
  have h := tendsto_xiCayleyChebyshevPhase_cofinite_neg_one.pow 2
  change Tendsto (fun q : XiZeroCopy => xiCayleyChebyshevPhase q ^ 2)
    cofinite (nhds 1)
  simpa using h

theorem norm_xiCayleyChebyshevPhase_le_three (q : XiZeroCopy) :
    ‖xiCayleyChebyshevPhase q‖ ≤ 3 := by
  let α := xiSpectralPoint q
  have hstrip := abs_im_xiSpectralPoint_lt_half q
  obtain ⟨hbneg, hbpos⟩ := abs_lt.mp hstrip
  have hden := sub_I_mul_spectral_ne_zero (by norm_num : (1 / 2 : ℝ) < (1 : ℂ).re) q
  have hsq :
      ‖(1 : ℂ) + Complex.I * α‖ ^ 2 ≤
        9 * ‖(1 : ℂ) - Complex.I * α‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.sq_norm]
    simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im,
      Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im,
      Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
      zero_mul, one_mul, zero_sub, add_zero, sub_zero]
    nlinarith [sq_nonneg α.re, sq_nonneg (α.im + 1 / 2),
      sq_nonneg (1 / 2 - α.im)]
  have hnorm :
      ‖(1 : ℂ) + Complex.I * α‖ ≤ 3 * ‖(1 : ℂ) - Complex.I * α‖ := by
    nlinarith [norm_nonneg ((1 : ℂ) + Complex.I * α),
      norm_nonneg ((1 : ℂ) - Complex.I * α)]
  rw [xiCayleyChebyshevPhase, xiHardEdgeCayleyPhase, norm_div]
  exact (div_le_iff₀ (norm_pos_iff.mpr hden)).2 (by simpa only [α] using hnorm)

theorem norm_xiCayleyChebyshevMode_le_nine (q : XiZeroCopy) :
    ‖xiCayleyChebyshevMode q‖ ≤ 9 := by
  rw [xiCayleyChebyshevMode, norm_pow]
  nlinarith [norm_xiCayleyChebyshevPhase_le_three q,
    norm_nonneg (xiCayleyChebyshevPhase q)]

theorem xiCayleyChebyshevPhase_im (q : XiZeroCopy) :
    (xiCayleyChebyshevPhase q).im =
      2 * (xiSpectralPoint q).re /
        Complex.normSq ((1 : ℂ) - Complex.I * xiSpectralPoint q) := by
  rw [xiCayleyChebyshevPhase, xiHardEdgeCayleyPhase, Complex.div_im]
  simp only [one_pow, Complex.ofReal_one, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im,
    Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
    zero_mul, one_mul, zero_sub, add_zero, sub_zero]
  ring

theorem xiCayleyChebyshevPhase_im_ne_zero (q : XiZeroCopy) :
    (xiCayleyChebyshevPhase q).im ≠ 0 := by
  rw [xiCayleyChebyshevPhase_im]
  have hre : (xiSpectralPoint q).re ≠ 0 := by
    rw [xiSpectralPoint_re_eq]
    intro hzero
    have hheight := xiZeroCopy_two_lt_im_sq q
    rw [hzero] at hheight
    norm_num at hheight
  exact div_ne_zero (mul_ne_zero two_ne_zero hre)
    (ne_of_gt (Complex.normSq_pos.mpr
      (sub_I_mul_spectral_ne_zero (by norm_num) q)))

theorem xiCayleyChebyshevMode_div_ne_one_of_one_lt
    {r : ℝ} (hr : 1 < r) {q : XiZeroCopy}
    (hq : ‖xiCayleyChebyshevMode q‖ = r) :
    xiCayleyChebyshevMode q / (r : ℂ) ≠ 1 := by
  intro heq
  have hr0 : (r : ℂ) ≠ 0 := ofReal_ne_zero.mpr (ne_of_gt (lt_trans zero_lt_one hr))
  have hmode : xiCayleyChebyshevMode q = (r : ℂ) :=
    (div_eq_one_iff_eq hr0).mp heq
  have himsq : (xiCayleyChebyshevPhase q ^ 2).im = 0 := by
    rw [← xiCayleyChebyshevMode, hmode]
    simp
  have hresq : (xiCayleyChebyshevPhase q ^ 2).re = r := by
    rw [← xiCayleyChebyshevMode, hmode]
    simp
  rw [pow_two, Complex.mul_im] at himsq
  rw [pow_two, Complex.mul_re] at hresq
  have himne := xiCayleyChebyshevPhase_im_ne_zero q
  have hre0 : (xiCayleyChebyshevPhase q).re = 0 := by
    have hprod : (xiCayleyChebyshevPhase q).re *
        (xiCayleyChebyshevPhase q).im = 0 := by linarith
    exact (mul_eq_zero.mp hprod).resolve_right himne
  rw [hre0] at hresq
  nlinarith [sq_nonneg (xiCayleyChebyshevPhase q).im]



theorem eval_xiCayleyChebyshevPolynomial_xiResolventPoint
    (n : ℕ) (q : XiZeroCopy) :
    evalRealPolynomial (xiCayleyChebyshevPolynomial n) (xiResolventPoint 1 q) =
      xiCayleyChebyshevPhase q ^ n / 2 +
        (xiCayleyChebyshevPhase q ^ n)⁻¹ / 2 := by
  rw [xiCayleyChebyshevPolynomial,
    evalRealPolynomial_xiHardEdgeReciprocalPolynomial]
  have hcoord := xiHardEdgeCayleyCoordinate_xiSpectralPoint 1 q
  rw [xiShiftedReciprocalSquare_eq_xiResolventPoint (by norm_num)] at hcoord
  norm_num at hcoord
  norm_num
  rw [← hcoord]
  rw [evalRealPolynomial, Polynomial.Chebyshev.map_T]
  have h := chebyshevT_eval_xiHardEdgeCayleyCoordinate
      (add_I_mul_spectral_ne_zero (W := (1 : ℂ)) (by norm_num) q)
      (sub_I_mul_spectral_ne_zero (W := (1 : ℂ)) (by norm_num) q) n
  have hinv :
      (((1 : ℂ) - Complex.I * xiSpectralPoint q) /
          ((1 : ℂ) + Complex.I * xiSpectralPoint q)) ^ n =
        ((((1 : ℂ) + Complex.I * xiSpectralPoint q) /
          ((1 : ℂ) - Complex.I * xiSpectralPoint q)) ^ n)⁻¹ := by
    rw [← inv_pow, inv_div]
  simpa [xiCayleyChebyshevPhase, xiHardEdgeCayleyPhase, hinv] using h

theorem summable_xiResolventPoint_one_mul_xiCayleyChebyshevMode_pow (n : ℕ) :
    Summable (fun q : XiZeroCopy =>
      xiResolventPoint 1 q * xiCayleyChebyshevMode q ^ n) := by
  apply Summable.of_norm_bounded
    ((summable_norm_xiResolventPoint (by norm_num : (0 : ℝ) ≤ 1)).mul_left (9 ^ n))
  intro q
  rw [norm_mul, norm_pow]
  calc
    ‖xiResolventPoint 1 q‖ * ‖xiCayleyChebyshevMode q‖ ^ n ≤
        ‖xiResolventPoint 1 q‖ * 9 ^ n :=
      mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (norm_nonneg _) (norm_xiCayleyChebyshevMode_le_nine q) n)
        (norm_nonneg _)
    _ = 9 ^ n * ‖xiResolventPoint 1 q‖ := by ring

theorem summable_xiResolventPoint_one_mul_xiCayleyChebyshevMode_inv_pow (n : ℕ) :
    Summable (fun q : XiZeroCopy =>
      xiResolventPoint 1 q * (xiCayleyChebyshevMode q)⁻¹ ^ n) := by
  apply Summable.of_norm_bounded
    ((summable_norm_xiResolventPoint (by norm_num : (0 : ℝ) ≤ 1)).mul_left (9 ^ n))
  intro q
  rw [norm_mul, norm_pow]
  have hbound : ‖(xiCayleyChebyshevMode q)⁻¹‖ ≤ 9 := by
    calc
      ‖(xiCayleyChebyshevMode q)⁻¹‖ =
          ‖xiCayleyChebyshevMode (xiZeroCopyReflectEquiv q)‖ := by
            rw [xiCayleyChebyshevMode_reflect]
      _ ≤ 9 := norm_xiCayleyChebyshevMode_le_nine _
  calc
    ‖xiResolventPoint 1 q‖ * ‖(xiCayleyChebyshevMode q)⁻¹‖ ^ n ≤
        ‖xiResolventPoint 1 q‖ * 9 ^ n :=
      mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (norm_nonneg _) hbound n) (norm_nonneg _)
    _ = 9 ^ n * ‖xiResolventPoint 1 q‖ := by ring

theorem tsum_xiResolventPoint_one_mul_xiCayleyChebyshevMode_inv_pow
    (n : ℕ) :
    (∑' q : XiZeroCopy,
      xiResolventPoint 1 q * (xiCayleyChebyshevMode q)⁻¹ ^ n) =
    ∑' q : XiZeroCopy,
      xiResolventPoint 1 q * xiCayleyChebyshevMode q ^ n := by
  let f : XiZeroCopy → ℂ := fun q =>
    xiResolventPoint 1 q * (xiCayleyChebyshevMode q)⁻¹ ^ n
  calc
    (∑' q : XiZeroCopy,
        xiResolventPoint 1 q * (xiCayleyChebyshevMode q)⁻¹ ^ n) =
      ∑' q : XiZeroCopy, f (xiZeroCopyReflectEquiv q) := by
        symm
        exact xiZeroCopyReflectEquiv.tsum_eq f
    _ = ∑' q : XiZeroCopy,
        xiResolventPoint 1 q * xiCayleyChebyshevMode q ^ n := by
      apply tsum_congr
      intro q
      dsimp only [f]
      rw [xiResolventPoint_one_reflect, xiCayleyChebyshevMode_reflect,
        inv_inv]

theorem xiCayleyChebyshevCoefficient_eq_pencil (n : ℕ) :
    xiCayleyChebyshevCoefficient n =
      ((∑' q : XiZeroCopy,
          xiResolventPoint 1 q * xiCayleyChebyshevMode q ^ n) +
        ∑' q : XiZeroCopy, xiResolventPoint 1 q) / 2 := by
  rw [xiCayleyChebyshevCoefficient, xiResolventTrace]
  have hmain :=
    summable_xiResolventPoint_one_mul_xiCayleyChebyshevMode_pow n
  have hinv :=
    summable_xiResolventPoint_one_mul_xiCayleyChebyshevMode_inv_pow n
  have hconst := summable_xiResolventPoint (by norm_num : (0 : ℝ) ≤ 1)
  have hsplit :
      (∑' q : XiZeroCopy,
        (xiResolventPoint 1 q * xiCayleyChebyshevMode q ^ n +
          2 * xiResolventPoint 1 q +
          xiResolventPoint 1 q * (xiCayleyChebyshevMode q)⁻¹ ^ n)) =
        (∑' q : XiZeroCopy,
          xiResolventPoint 1 q * xiCayleyChebyshevMode q ^ n) +
          2 * (∑' q : XiZeroCopy, xiResolventPoint 1 q) +
          ∑' q : XiZeroCopy,
            (xiResolventPoint 1 q * (xiCayleyChebyshevMode q)⁻¹ ^ n) := by
    rw [(hmain.add (hconst.mul_left 2)).tsum_add hinv,
      hmain.tsum_add (hconst.mul_left 2), tsum_mul_left]
  calc
    (∑' q : XiZeroCopy, xiResolventPoint 1 q *
        evalRealPolynomial (xiCayleyChebyshevPolynomial n)
          (xiResolventPoint 1 q) ^ 2) =
      ∑' q : XiZeroCopy,
        (xiResolventPoint 1 q * xiCayleyChebyshevMode q ^ n +
          2 * xiResolventPoint 1 q +
          xiResolventPoint 1 q * (xiCayleyChebyshevMode q)⁻¹ ^ n) / 4 := by
        apply tsum_congr
        intro q
        rw [eval_xiCayleyChebyshevPolynomial_xiResolventPoint]
        have hphase := xiCayleyChebyshevPhase_ne_zero q
        have hmodepow : xiCayleyChebyshevMode q ^ n =
            (xiCayleyChebyshevPhase q ^ n) ^ 2 := by
          rw [xiCayleyChebyshevMode, ← pow_mul, ← pow_mul, Nat.mul_comm 2 n]
        have hinvpow : (xiCayleyChebyshevMode q)⁻¹ ^ n =
            (xiCayleyChebyshevPhase q ^ n)⁻¹ ^ 2 := by
          rw [inv_pow, hmodepow, ← inv_pow]
        rw [hmodepow, hinvpow]
        let x := xiCayleyChebyshevPhase q ^ n
        have hx : x ≠ 0 := pow_ne_zero n hphase
        change xiResolventPoint 1 q * (x / 2 + x⁻¹ / 2) ^ 2 =
          (xiResolventPoint 1 q * x ^ 2 + 2 * xiResolventPoint 1 q +
            xiResolventPoint 1 q * x⁻¹ ^ 2) / 4
        field_simp [hx]
        ring
    _ = ((∑' q : XiZeroCopy,
          xiResolventPoint 1 q * xiCayleyChebyshevMode q ^ n) +
        ∑' q : XiZeroCopy, xiResolventPoint 1 q) / 2 := by
      rw [show (fun q : XiZeroCopy =>
          (xiResolventPoint 1 q * xiCayleyChebyshevMode q ^ n +
            2 * xiResolventPoint 1 q +
            xiResolventPoint 1 q * (xiCayleyChebyshevMode q)⁻¹ ^ n) / 4) =
          fun q => (4 : ℂ)⁻¹ *
            (xiResolventPoint 1 q * xiCayleyChebyshevMode q ^ n +
              2 * xiResolventPoint 1 q +
              xiResolventPoint 1 q * (xiCayleyChebyshevMode q)⁻¹ ^ n) by
            funext q; ring]
      rw [tsum_mul_left, hsplit,
        tsum_xiResolventPoint_one_mul_xiCayleyChebyshevMode_inv_pow]
      ring

theorem finiteExponentialPencil_xiCayleyChebyshevMode_div_im_eq_zero
    (D : Finset XiZeroCopy) {r : ℝ} (hr : 0 < r)
    (hdom : ∀ q ∈ D, ‖xiCayleyChebyshevMode q‖ = r)
    (hsub : ∀ q ∉ D, ‖xiCayleyChebyshevMode q‖ < r)
    (n : ℕ) :
    (finiteExponentialPencil D (xiResolventPoint 1)
      (fun q => xiCayleyChebyshevMode q / (r : ℂ)) n).im = 0 := by
  let term : XiZeroCopy → ℂ := fun q =>
    xiResolventPoint 1 q *
      (xiCayleyChebyshevMode q / (r : ℂ)) ^ n
  have hmem (q : XiZeroCopy) :
      q ∈ D ↔ xiZeroCopyConjEquiv q ∈ D := by
    constructor
    · intro hq
      by_contra hc
      have hlt := hsub (xiZeroCopyConjEquiv q) hc
      have heq := hdom q hq
      rw [xiCayleyChebyshevMode_copyConj, norm_star, heq] at hlt
      exact (lt_irrefl r) hlt
    · intro hq
      by_contra hc
      have hlt := hsub q hc
      have heq := hdom (xiZeroCopyConjEquiv q) hq
      rw [xiCayleyChebyshevMode_copyConj, norm_star] at heq
      rw [heq] at hlt
      exact (lt_irrefl r) hlt
  have hterm (q : XiZeroCopy) :
      term (xiZeroCopyConjEquiv q) = star (term q) := by
    dsimp only [term]
    rw [xiResolventPoint_one_copyConj, xiCayleyChebyshevMode_copyConj]
    conv_rhs =>
      rw [← starRingEnd_apply, map_mul, map_pow, map_div₀]
    simp
  have hreindex :
      (∑ q ∈ D, term (xiZeroCopyConjEquiv q)) = ∑ q ∈ D, term q :=
    Finset.sum_equiv xiZeroCopyConjEquiv (fun q => hmem q) (fun _ _ => rfl)
  have hstar : star (∑ q ∈ D, term q) = ∑ q ∈ D, term q := by
    rw [star_sum]
    calc
      (∑ q ∈ D, star (term q)) =
          ∑ q ∈ D, term (xiZeroCopyConjEquiv q) := by
            apply Finset.sum_congr rfl
            intro q hq
            exact (hterm q).symm
      _ = ∑ q ∈ D, term q := hreindex
  have him := congrArg Complex.im hstar
  have him' : -(∑ q ∈ D, term q).im = (∑ q ∈ D, term q).im := by
    simpa only [← starRingEnd_apply, Complex.conj_im] using him
  rw [finiteExponentialPencil]
  change (∑ q ∈ D, term q).im = 0
  linarith

theorem exists_nonzero_xiCayleyChebyshevMode_fiberCoefficient
    (D : Finset XiZeroCopy) (hD : D.Nonempty) {r : ℝ} :
    ∃ u ∈ D.image (fun q => xiCayleyChebyshevMode q / (r : ℂ)),
      finiteExponentialFiberCoefficient D (xiResolventPoint 1)
        (fun q => xiCayleyChebyshevMode q / (r : ℂ)) u ≠ 0 := by
  classical
  let z : XiZeroCopy → ℂ := fun q => xiCayleyChebyshevMode q / (r : ℂ)
  by_contra hnone
  push Not at hnone
  have hleft :
      (∑ u ∈ D.image z,
        finiteExponentialFiberCoefficient D (xiResolventPoint 1) z u) = 0 := by
    apply Finset.sum_eq_zero
    intro u hu
    exact hnone u hu
  have himage := finiteExponentialPencil_image_eq D (xiResolventPoint 1) z 0
  rw [finiteExponentialPencil, finiteExponentialPencil] at himage
  simp only [id_eq, pow_zero, mul_one] at himage
  rw [hleft] at himage
  have hsumzero : (∑ q ∈ D, xiResolventPoint 1 q) = 0 := himage.symm
  have hpos : 0 < (∑ q ∈ D, xiResolventPoint 1 q).re := by
    rw [← Complex.reCLM_apply, map_sum]
    exact Finset.sum_pos
      (fun q hq => xiResolventPoint_re_pos (by norm_num) q) hD
  rw [hsumzero] at hpos
  simp at hpos
theorem tsum_normalized_xiCayleyChebyshevMode_eq
    {r : ℝ} (hr : 0 < r) (n : ℕ) :
    (∑' q : XiZeroCopy,
      xiResolventPoint 1 q *
        (xiCayleyChebyshevMode q / (r : ℂ)) ^ n) =
      (∑' q : XiZeroCopy,
        xiResolventPoint 1 q * xiCayleyChebyshevMode q ^ n) /
        ((r : ℂ) ^ n) := by
  rw [← tsum_div_const]
  apply tsum_congr
  intro q
  rw [div_pow]
  ring

theorem riemannHypothesis_of_forall_xiCayleyChebyshevCoefficient_re_nonneg
    (h : ∀ n : ℕ, 0 ≤ (xiCayleyChebyshevCoefficient n).re) :
    RiemannHypothesis := by
  by_contra hRH
  obtain ⟨q0, hq0⟩ :=
    exists_one_lt_norm_xiCayleyChebyshevMode_of_not_rh hRH
  obtain ⟨D, r, hr, hD, hdom, hsub⟩ :=
    exists_finite_maximal_norm_packet_of_tendsto_cofinite_one
      xiCayleyChebyshevMode tendsto_xiCayleyChebyshevMode_cofinite_one hq0
  have hr0 : 0 < r := lt_trans zero_lt_one hr
  have hsum := summable_xiResolventPoint (by norm_num : (0 : ℝ) ≤ 1)
  have hnoOne : ∀ q ∈ D,
      xiCayleyChebyshevMode q / (r : ℂ) ≠ 1 := by
    intro q hq
    exact xiCayleyChebyshevMode_div_ne_one_of_one_lt hr (hdom q hq)
  have hfiber :=
    exists_nonzero_xiCayleyChebyshevMode_fiberCoefficient D hD (r := r)
  have hreal : ∀ n,
      (finiteExponentialPencil D (xiResolventPoint 1)
        (fun q => xiCayleyChebyshevMode q / (r : ℂ)) n).im = 0 :=
    fun n => finiteExponentialPencil_xiCayleyChebyshevMode_div_im_eq_zero
      D hr0 hdom hsub n
  obtain ⟨δ, hδ, hlate⟩ :=
    exists_arbitrarily_late_re_tsum_normalizedExponentialPencil_lt_neg_of_dominantFinset
      (xiResolventPoint 1) xiCayleyChebyshevMode hsum D hr0 hdom hsub
      hnoOne hfiber hreal
  let A : ℂ := ∑' q : XiZeroCopy, xiResolventPoint 1 q
  have hrInvNorm : ‖((r : ℂ)⁻¹)‖ < 1 := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0,
      inv_lt_one₀ hr0]
    exact hr
  have hAzero : Tendsto
      (fun n : ℕ => A * ((r : ℂ)⁻¹) ^ n) atTop (nhds 0) := by
    simpa using tendsto_const_nhds.mul
      (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hrInvNorm)
  have hsmall : ∀ᶠ n : ℕ in atTop,
      ‖A * ((r : ℂ)⁻¹) ^ n‖ < δ := by
    have hev := hAzero.eventually (Metric.ball_mem_nhds (0 : ℂ) hδ)
    simpa only [Metric.mem_ball, dist_zero_right] using hev
  obtain ⟨N, hN⟩ := eventually_atTop.1 hsmall
  obtain ⟨n, hnN, hnneg⟩ := hlate N
  let P : ℂ := ∑' q : XiZeroCopy,
    xiResolventPoint 1 q * xiCayleyChebyshevMode q ^ n
  have hrpow : (0 : ℝ) < r ^ n := pow_pos hr0 n
  have hreDiv (z : ℂ) :
      (z / ((r : ℂ) ^ n)).re = z.re / r ^ n := by
    have hcast : ((r : ℂ) ^ n) = ((r ^ n : ℝ) : ℂ) := by norm_cast
    rw [hcast]
    rw [Complex.div_re]
    simp only [Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_mul,
      add_zero, Complex.normSq_apply]
    field_simp [ne_of_gt hrpow]
    ring
  have hPscaled : (P / ((r : ℂ) ^ n)).re < -δ := by
    rw [← tsum_normalized_xiCayleyChebyshevMode_eq hr0 n]
    exact hnneg
  rw [hreDiv] at hPscaled
  have hP : P.re < -δ * r ^ n := (div_lt_iff₀ hrpow).mp hPscaled
  have hAscaled : (A / ((r : ℂ) ^ n)).re < δ := by
    rw [show A / ((r : ℂ) ^ n) = A * ((r : ℂ)⁻¹) ^ n by
      rw [div_eq_mul_inv, inv_pow]]
    exact lt_of_le_of_lt (Complex.re_le_norm _) (hN n hnN)
  rw [hreDiv] at hAscaled
  have hA : A.re < δ * r ^ n := (div_lt_iff₀ hrpow).mp hAscaled
  have hcoeffEq := xiCayleyChebyshevCoefficient_eq_pencil n
  change xiCayleyChebyshevCoefficient n = (P + A) / 2 at hcoeffEq
  have hcoeffRe := congrArg Complex.re hcoeffEq
  norm_num [Complex.div_re, Complex.normSq_apply] at hcoeffRe
  have hneg : (xiCayleyChebyshevCoefficient n).re < 0 := by
    rw [hcoeffRe]
    nlinarith
  exact (not_lt_of_ge (h n)) hneg

theorem xiCayleyChebyshevCoefficient_re_nonneg_of_riemannHypothesis
    (hRH : RiemannHypothesis) (n : ℕ) :
    0 ≤ (xiCayleyChebyshevCoefficient n).re := by
  exact xiResolventTrace_re_nonneg_of_riemannHypothesis hRH
    (by norm_num : (0 : ℝ) ≤ 1) (xiCayleyChebyshevPolynomial n)

theorem riemannHypothesis_iff_forall_xiCayleyChebyshevCoefficient_re_nonneg :
    RiemannHypothesis ↔
      ∀ n : ℕ, 0 ≤ (xiCayleyChebyshevCoefficient n).re :=
  ⟨xiCayleyChebyshevCoefficient_re_nonneg_of_riemannHypothesis,
    riemannHypothesis_of_forall_xiCayleyChebyshevCoefficient_re_nonneg⟩

/-! ### Exact generalized-Li collision -/

/-- Polynomial defect whose division by `X` makes the reflection-paired Li atom summable. -/
def xiGeneralizedLiDefectPolynomial (m : ℕ) : Polynomial ℝ :=
  1 - Polynomial.C ((-1 : ℝ) ^ m) * xiCayleyChebyshevPolynomial m

/-- Quotient left after removing the exact zero at the reciprocal origin. -/
def xiGeneralizedLiQuotientPolynomial (m : ℕ) : Polynomial ℝ :=
  (xiGeneralizedLiDefectPolynomial m).divX

theorem xiGeneralizedLiDefectPolynomial_coeff_zero (m : ℕ) :
    (xiGeneralizedLiDefectPolynomial m).coeff 0 = 0 := by
  rw [Polynomial.coeff_zero_eq_eval_zero]
  simp [xiGeneralizedLiDefectPolynomial, xiCayleyChebyshevPolynomial,
    xiHardEdgeReciprocalPolynomial, Polynomial.Chebyshev.T_eval_neg_one]
  rw [← mul_pow]
  norm_num

theorem X_mul_xiGeneralizedLiQuotientPolynomial (m : ℕ) :
    Polynomial.X * xiGeneralizedLiQuotientPolynomial m =
      xiGeneralizedLiDefectPolynomial m := by
  have h := Polynomial.X_mul_divX_add (xiGeneralizedLiDefectPolynomial m)
  rw [xiGeneralizedLiDefectPolynomial_coeff_zero, Polynomial.C_0, add_zero] at h
  exact h

/-- Absolutely convergent reflection-paired generalized Li coefficient. -/
def xiGeneralizedLiCoefficient (m : ℕ) : ℂ :=
  ∑' q : XiZeroCopy, xiResolventPoint 1 q *
    evalRealPolynomial (xiGeneralizedLiQuotientPolynomial m)
      (xiResolventPoint 1 q)

theorem summable_xiGeneralizedLiQuotientAtom (m : ℕ) :
    Summable (fun q : XiZeroCopy => xiResolventPoint 1 q *
      evalRealPolynomial (xiGeneralizedLiQuotientPolynomial m)
        (xiResolventPoint 1 q)) := by
  refine Summable.of_norm_bounded
    ((summable_norm_xiResolventPoint (by norm_num : (0 : ℝ) ≤ 1)).mul_right
      (evalRealPolynomialNormBound (xiGeneralizedLiQuotientPolynomial m) 1)) ?_
  intro q
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left
    (norm_evalRealPolynomial_le (xiGeneralizedLiQuotientPolynomial m)
      (norm_xiResolventPoint_le_one (by norm_num) q)) (norm_nonneg _)

/-- One multiplicity-exact paired Li atom in the Cayley coordinate. -/
def xiGeneralizedLiPairedAtom (m : ℕ) (q : XiZeroCopy) : ℂ :=
  1 - (((-xiCayleyChebyshevPhase q) ^ m +
    ((-xiCayleyChebyshevPhase q)⁻¹) ^ m) / 2)

theorem xiGeneralizedLiPairedAtom_eq (m : ℕ) (q : XiZeroCopy) :
    xiGeneralizedLiPairedAtom m q =
      xiResolventPoint 1 q *
        evalRealPolynomial (xiGeneralizedLiQuotientPolynomial m)
          (xiResolventPoint 1 q) := by
  have hpoly := congrArg
    (fun P : Polynomial ℝ => evalRealPolynomial P (xiResolventPoint 1 q))
    (X_mul_xiGeneralizedLiQuotientPolynomial m)
  rw [evalRealPolynomial_mul] at hpoly
  have hX : evalRealPolynomial (Polynomial.X : Polynomial ℝ)
      (xiResolventPoint 1 q) = xiResolventPoint 1 q := by
    simp [evalRealPolynomial]
  rw [hX] at hpoly
  have hdefect :
      evalRealPolynomial (xiGeneralizedLiDefectPolynomial m)
          (xiResolventPoint 1 q) =
        1 - (((-1 : ℝ) ^ m : ℝ) : ℂ) *
          evalRealPolynomial (xiCayleyChebyshevPolynomial m)
            (xiResolventPoint 1 q) := by
    simp [xiGeneralizedLiDefectPolynomial, evalRealPolynomial]
  rw [hdefect] at hpoly
  rw [eval_xiCayleyChebyshevPolynomial_xiResolventPoint] at hpoly
  rw [hpoly]
  rw [xiGeneralizedLiPairedAtom]
  have hy := xiCayleyChebyshevPhase_ne_zero q
  let y := xiCayleyChebyshevPhase q
  have hneg : (-y) ^ m = (-1 : ℂ) ^ m * y ^ m := by
    rw [show -y = (-1 : ℂ) * y by ring, mul_pow]
  have hinvneg : ((-y)⁻¹) ^ m = (-1 : ℂ) ^ m * (y ^ m)⁻¹ := by
    rw [inv_neg]
    rw [show -(y⁻¹) = (-1 : ℂ) * y⁻¹ by ring, mul_pow, ← inv_pow]
  rw [hneg, hinvneg]
  push_cast
  ring

theorem summable_xiGeneralizedLiPairedAtom (m : ℕ) :
    Summable (xiGeneralizedLiPairedAtom m) := by
  convert summable_xiGeneralizedLiQuotientAtom m using 1
  funext q
  exact xiGeneralizedLiPairedAtom_eq m q

theorem xiGeneralizedLiCoefficient_eq_tsum_pairedAtom (m : ℕ) :
    xiGeneralizedLiCoefficient m =
      ∑' q : XiZeroCopy, xiGeneralizedLiPairedAtom m q := by
  rw [xiGeneralizedLiCoefficient]
  exact tsum_congr fun q => (xiGeneralizedLiPairedAtom_eq m q).symm

theorem xiGeneralizedLiPairedAtom_one (q : XiZeroCopy) :
    xiGeneralizedLiPairedAtom 1 q = 2 * xiResolventPoint 1 q := by
  have h := eval_xiCayleyChebyshevPolynomial_xiResolventPoint 1 q
  have hp : evalRealPolynomial (xiCayleyChebyshevPolynomial 1)
      (xiResolventPoint 1 q) = 2 * xiResolventPoint 1 q - 1 := by
    simp [xiCayleyChebyshevPolynomial, xiHardEdgeReciprocalPolynomial,
      evalRealPolynomial]
  rw [hp] at h
  rw [xiGeneralizedLiPairedAtom]
  norm_num at h ⊢
  calc
    1 - (-xiCayleyChebyshevPhase q +
        -(xiCayleyChebyshevPhase q)⁻¹) / 2 =
      1 + (xiCayleyChebyshevPhase q / 2 +
        (xiCayleyChebyshevPhase q)⁻¹ / 2) := by ring
    _ = 2 * xiResolventPoint 1 q := by rw [← h]; ring

theorem xiCayleyChebyshevCoefficient_zero_eq_generalizedLi_one :
    xiCayleyChebyshevCoefficient 0 = xiGeneralizedLiCoefficient 1 / 2 := by
  rw [xiCayleyChebyshevCoefficient_eq_pencil,
    xiGeneralizedLiCoefficient_eq_tsum_pairedAtom]
  simp only [pow_zero, mul_one]
  rw [show (∑' q : XiZeroCopy, xiGeneralizedLiPairedAtom 1 q) =
      2 * ∑' q : XiZeroCopy, xiResolventPoint 1 q by
    rw [← tsum_mul_left]
    exact tsum_congr fun q => xiGeneralizedLiPairedAtom_one q]
  ring

theorem xiCayleyChebyshevTraceAtom_eq_generalizedLi_stencil
    {n : ℕ} (hn : 0 < n) (q : XiZeroCopy) :
    xiResolventPoint 1 q *
        evalRealPolynomial (xiCayleyChebyshevPolynomial n)
          (xiResolventPoint 1 q) ^ 2 =
      (xiGeneralizedLiPairedAtom (2 * n + 1) q -
          2 * xiGeneralizedLiPairedAtom (2 * n) q +
          xiGeneralizedLiPairedAtom (2 * n - 1) q +
          2 * xiGeneralizedLiPairedAtom 1 q) / 8 := by
  cases n with
  | zero => omega
  | succ k =>
      let y := xiCayleyChebyshevPhase q
      let u := xiResolventPoint 1 q
      have hy : y ≠ 0 := xiCayleyChebyshevPhase_ne_zero q
      have hp := eval_xiCayleyChebyshevPolynomial_xiResolventPoint (k + 1) q
      change evalRealPolynomial (xiCayleyChebyshevPolynomial (k + 1)) u =
        y ^ (k + 1) / 2 + (y ^ (k + 1))⁻¹ / 2 at hp
      have hu : u = (2 + y + y⁻¹) / 4 := by
        have h1 := eval_xiCayleyChebyshevPolynomial_xiResolventPoint 1 q
        have hp1 : evalRealPolynomial (xiCayleyChebyshevPolynomial 1) u = 2 * u - 1 := by
          simp [u, xiCayleyChebyshevPolynomial, xiHardEdgeReciprocalPolynomial,
            evalRealPolynomial]
        change evalRealPolynomial (xiCayleyChebyshevPolynomial 1) u =
          y ^ 1 / 2 + (y ^ 1)⁻¹ / 2 at h1
        rw [hp1] at h1
        norm_num at h1
        calc
          u = ((2 * u - 1) + 1) / 2 := by ring
          _ = ((y / 2 + y⁻¹ / 2) + 1) / 2 := by rw [h1]
          _ = (2 + y + y⁻¹) / 4 := by ring
      have heven : (-y) ^ (2 * (k + 1)) = (y ^ (k + 1)) ^ 2 := by
        rw [show -y = (-1 : ℂ) * y by ring, mul_pow]
        have hs : (-1 : ℂ) ^ (2 * (k + 1)) = 1 := by
          rw [pow_mul]
          norm_num
        rw [hs, one_mul]
        rw [show 2 * (k + 1) = (k + 1) * 2 by omega, pow_mul]
      have hoddPlus : (-y) ^ (2 * (k + 1) + 1) =
          -(y * (y ^ (k + 1)) ^ 2) := by
        rw [pow_succ, heven]
        ring
      have hoddMinus : (-y) ^ (2 * (k + 1) - 1) =
          -(y⁻¹ * (y ^ (k + 1)) ^ 2) := by
        rw [show 2 * (k + 1) - 1 = 2 * k + 1 by omega, pow_succ]
        have hevenk : (-y) ^ (2 * k) = (y ^ k) ^ 2 := by
          rw [show -y = (-1 : ℂ) * y by ring, mul_pow]
          have hs : (-1 : ℂ) ^ (2 * k) = 1 := by
            rw [pow_mul]
            norm_num
          rw [hs, one_mul]
          rw [show 2 * k = k * 2 by omega, pow_mul]
        rw [hevenk, pow_succ]
        field_simp [hy]
        ring
      have hevenInv : ((-y)⁻¹) ^ (2 * (k + 1)) =
          ((y ^ (k + 1))⁻¹) ^ 2 := by
        rw [inv_pow, heven, inv_pow]
      have hoddPlusInv : ((-y)⁻¹) ^ (2 * (k + 1) + 1) =
          -(y⁻¹ * ((y ^ (k + 1))⁻¹) ^ 2) := by
        rw [inv_pow, hoddPlus]
        field_simp [hy]
      have hoddMinusInv : ((-y)⁻¹) ^ (2 * (k + 1) - 1) =
          -(y * ((y ^ (k + 1))⁻¹) ^ 2) := by
        rw [inv_pow, hoddMinus]
        field_simp [hy]
      change u * evalRealPolynomial (xiCayleyChebyshevPolynomial (k + 1)) u ^ 2 = _
      rw [hp, xiGeneralizedLiPairedAtom, xiGeneralizedLiPairedAtom,
        xiGeneralizedLiPairedAtom, xiGeneralizedLiPairedAtom]
      change u * (y ^ (k + 1) / 2 + (y ^ (k + 1))⁻¹ / 2) ^ 2 =
        ((1 - (((-y) ^ (2 * (k + 1) + 1) +
              ((-y)⁻¹) ^ (2 * (k + 1) + 1)) / 2)) -
            2 * (1 - (((-y) ^ (2 * (k + 1)) +
              ((-y)⁻¹) ^ (2 * (k + 1))) / 2)) +
            (1 - (((-y) ^ (2 * (k + 1) - 1) +
              ((-y)⁻¹) ^ (2 * (k + 1) - 1)) / 2)) +
            2 * (1 - (((-y) ^ 1 + ((-y)⁻¹) ^ 1) / 2))) / 8
      rw [heven, hoddPlus, hoddMinus, hevenInv, hoddPlusInv, hoddMinusInv]
      norm_num
      rw [hu]
      field_simp [hy]
      ring

theorem xiCayleyChebyshevCoefficient_eq_generalizedLi_stencil
    {n : ℕ} (hn : 0 < n) :
    xiCayleyChebyshevCoefficient n =
      (xiGeneralizedLiCoefficient (2 * n + 1) -
          2 * xiGeneralizedLiCoefficient (2 * n) +
          xiGeneralizedLiCoefficient (2 * n - 1) +
          2 * xiGeneralizedLiCoefficient 1) / 8 := by
  rw [xiCayleyChebyshevCoefficient, xiResolventTrace,
    xiGeneralizedLiCoefficient_eq_tsum_pairedAtom,
    xiGeneralizedLiCoefficient_eq_tsum_pairedAtom,
    xiGeneralizedLiCoefficient_eq_tsum_pairedAtom,
    xiGeneralizedLiCoefficient_eq_tsum_pairedAtom]
  let A : XiZeroCopy → ℂ := xiGeneralizedLiPairedAtom (2 * n + 1)
  let B : XiZeroCopy → ℂ := xiGeneralizedLiPairedAtom (2 * n)
  let C : XiZeroCopy → ℂ := xiGeneralizedLiPairedAtom (2 * n - 1)
  let D : XiZeroCopy → ℂ := xiGeneralizedLiPairedAtom 1
  have hA : Summable A := summable_xiGeneralizedLiPairedAtom _
  have hB : Summable B := summable_xiGeneralizedLiPairedAtom _
  have hC : Summable C := summable_xiGeneralizedLiPairedAtom _
  have hD : Summable D := summable_xiGeneralizedLiPairedAtom _
  let N : XiZeroCopy → ℂ := fun q => A q - 2 * B q + C q + 2 * D q
  have hN : Summable N :=
    ((hA.sub (hB.mul_left 2)).add hC).add (hD.mul_left 2)
  calc
    (∑' q : XiZeroCopy,
        xiResolventPoint 1 q *
          evalRealPolynomial (xiCayleyChebyshevPolynomial n)
            (xiResolventPoint 1 q) ^ 2) =
      ∑' q : XiZeroCopy, N q / 8 := by
        exact tsum_congr fun q =>
          xiCayleyChebyshevTraceAtom_eq_generalizedLi_stencil hn q
    _ = (∑' q : XiZeroCopy, N q) / 8 := by
      have hscale : (fun q : XiZeroCopy => N q / 8) =
          fun q => (8 : ℂ)⁻¹ * N q := by
        funext q
        ring
      rw [hscale, tsum_mul_left]
      ring
    _ = _ := by
      rw [show (∑' q : XiZeroCopy, N q) =
          ((∑' q : XiZeroCopy, A q) - 2 * (∑' q : XiZeroCopy, B q) +
            (∑' q : XiZeroCopy, C q) + 2 * (∑' q : XiZeroCopy, D q)) by
        rw [show N = fun q => (A q - 2 * B q) + C q + 2 * D q by
          funext q
          rfl]
        rw [((hA.sub (hB.mul_left 2)).add hC).tsum_add (hD.mul_left 2),
          (hA.sub (hB.mul_left 2)).tsum_add hC,
          hA.tsum_sub (hB.mul_left 2), tsum_mul_left, tsum_mul_left]]

theorem xiCayleyChebyshevPolynomial_eq_sourcePolynomial (n : ℕ) :
    xiCayleyChebyshevPolynomial n = cayleyChebyshevPolynomial n := rfl

theorem xiCayleyChebyshevCoefficient_re_eq_normalizedFilteredGamma
    (n : ℕ) :
    (xiCayleyChebyshevCoefficient n).re =
      (1 / ((2 * n).factorial : ℝ)) *
        ∫ t in Set.Ioi (0 : ℝ),
          xiShiftedFilteredGammaKernelReal 1 0 n
            (cayleyChebyshevSourceCoefficients n) t := by
  rw [xiCayleyChebyshevCoefficient,
    xiCayleyChebyshevPolynomial_eq_sourcePolynomial,
    xiResolventTrace_cayleyChebyshevPolynomial_re_eq_normalizedFilteredGamma]

/-- The explicit positive-root Gamma packets carry RH with no source-side premise. -/
theorem riemannHypothesis_iff_forall_cayleyChebyshev_normalizedFilteredGamma_nonneg :
    RiemannHypothesis ↔
      ∀ n : ℕ, 0 ≤
        (1 / ((2 * n).factorial : ℝ)) *
          ∫ t in Set.Ioi (0 : ℝ),
            xiShiftedFilteredGammaKernelReal 1 0 n
              (cayleyChebyshevSourceCoefficients n) t := by
  rw [riemannHypothesis_iff_forall_xiCayleyChebyshevCoefficient_re_nonneg]
  exact forall_congr' fun n => by
    rw [xiCayleyChebyshevCoefficient_re_eq_normalizedFilteredGamma]

/-! ## Exact Abel--resolvent row

The paper draft claimed the following generating function on the whole unit disk.  Off RH that
radius is too large: an exterior Cayley phase makes the Chebyshev atoms grow exponentially.  The
uniform strip bound above gives the unconditional disk `‖r‖ < 1/3`; the two pointwise phase bounds
below give the exact atom-dependent domain.
-/

private theorem cayleyChebyshevPhaseGenerating_algebra
    {u r y x : ℂ} (hy : y ≠ 0)
    (hx : (y + y⁻¹) / 2 = x)
    (hry : 1 - r * y ≠ 0) (hryi : 1 - r * y⁻¹ ≠ 0)
    (hD : 1 - 2 * r * x + r ^ 2 ≠ 0) :
    u / 2 * ((1 - r * y)⁻¹ + (1 - r * y⁻¹)⁻¹) =
      u * (1 - r * x) / (1 - 2 * r * x + r ^ 2) := by
  let A : ℂ := 1 - r * y
  let B : ℂ := 1 - r * y⁻¹
  let D : ℂ := 1 - 2 * r * x + r ^ 2
  have hAB : A * B = D := by
    dsimp only [A, B, D]
    have hx' : y ^ 2 + 1 = 2 * x * y := by
      field_simp [hy] at hx
      linear_combination hx
    field_simp [hy]
    linear_combination hx' * (-r)
  have hAaddB : A + B = 2 * (1 - r * x) := by
    dsimp only [A, B]
    have hphase : y + y⁻¹ = 2 * x := by
      calc
        y + y⁻¹ = 2 * ((y + y⁻¹) / 2) := by ring
        _ = 2 * x := by rw [hx]
    calc
      1 - r * y + (1 - r * y⁻¹) = 2 - r * (y + y⁻¹) := by ring
      _ = 2 - r * (2 * x) := by rw [hphase]
      _ = 2 * (1 - r * x) := by ring
  have hsum : A⁻¹ + B⁻¹ = (A + B) / (A * B) := by
    have hA : A ≠ 0 := by simpa only [A] using hry
    have hB : B ≠ 0 := by simpa only [B] using hryi
    field_simp [hA, hB]
    ring
  rw [show 1 - r * y = A by rfl, show 1 - r * y⁻¹ = B by rfl,
    hsum, hAB, hAaddB]
  dsimp only [D]
  field_simp [hD]

private theorem cayleyChebyshevResolvent_algebra
    {w r : ℂ} (hw : 1 + w ≠ 0) (hr1 : 1 + r ≠ 0)
    (hres : w + ((1 - r) / (1 + r)) ^ 2 ≠ 0) :
    (w + 1)⁻¹ * (1 - r * ((1 - w) / (1 + w))) /
          (1 - 2 * r * ((1 - w) / (1 + w)) + r ^ 2) =
      (1 / 2) * ((w + 1)⁻¹ +
        ((1 - r) / (1 + r)) *
          (w + ((1 - r) / (1 + r)) ^ 2)⁻¹) := by
  have hw' : w + 1 ≠ 0 := by simpa [add_comm] using hw
  have hresnum : w * (1 + r) ^ 2 + (1 - r) ^ 2 ≠ 0 := by
    intro hzero
    apply hres
    field_simp [hr1]
    linear_combination hzero
  let H : ℂ := w * (1 + r) ^ 2 + (1 - r) ^ 2
  have hH : H ≠ 0 := by simpa only [H] using hresnum
  have hDform :
      1 - 2 * r * ((1 - w) / (1 + w)) + r ^ 2 = H / (1 + w) := by
    dsimp only [H]
    field_simp [hw]
    ring
  have hNform :
      1 - r * ((1 - w) / (1 + w)) =
        ((1 - r) + w * (1 + r)) / (1 + w) := by
    field_simp [hw]
    ring
  have hresform :
      w + ((1 - r) / (1 + r)) ^ 2 = H / (1 + r) ^ 2 := by
    dsimp only [H]
    field_simp [hr1]
  rw [hNform, hDform, hresform]
  dsimp only [H]
  field_simp [hw, hw', hr1, hH]
  ring

private theorem cayleyChebyshev_resolvent_denominator_ne_zero
    {w r : ℂ} (hw : 1 + w ≠ 0) (hr1 : 1 + r ≠ 0)
    (hD : 1 - 2 * r * ((1 - w) / (1 + w)) + r ^ 2 ≠ 0) :
    w + ((1 - r) / (1 + r)) ^ 2 ≠ 0 := by
  intro hzero
  apply hD
  field_simp [hw, hr1] at hzero ⊢
  linear_combination hzero

theorem norm_xiCayleyChebyshevPhase_inv_le_three (q : XiZeroCopy) :
    ‖(xiCayleyChebyshevPhase q)⁻¹‖ ≤ 3 := by
  rw [← xiCayleyChebyshevPhase_reflect]
  exact norm_xiCayleyChebyshevPhase_le_three _

/-- Cayley parameter used by the exact two-resolvent transfer row. -/
def xiCayleyAbelParameter (r : ℂ) : ℂ :=
  (1 - r) / (1 + r)

/-- Squared-spectral resolvent at an arbitrary complex shift. -/
def xiCayleySpectralResolvent (y : ℂ) : ℂ :=
  ∑' q : XiZeroCopy, (xiSpectralPoint q ^ 2 + y)⁻¹

/-- Linear Cayley--Chebyshev moment `a_k` from the Route U paper proof. -/
def xiCayleyChebyshevMoment (k : ℕ) : ℂ :=
  ∑' q : XiZeroCopy,
    xiResolventPoint 1 q *
      evalRealPolynomial (xiCayleyChebyshevPolynomial k)
        (xiResolventPoint 1 q)

/-- Exact pointwise generating row on its unconditional uniform disk. -/
theorem hasSum_xiCayleyChebyshevAtom_generating
    (q : XiZeroCopy) {r : ℂ} (hr : ‖r‖ < 1 / 3) :
    HasSum (fun k : ℕ =>
      xiResolventPoint 1 q *
        evalRealPolynomial (xiCayleyChebyshevPolynomial k)
          (xiResolventPoint 1 q) * r ^ k)
      ((1 / 2) *
        (xiResolventPoint 1 q + xiCayleyAbelParameter r *
          (xiSpectralPoint q ^ 2 + xiCayleyAbelParameter r ^ 2)⁻¹)) := by
  let y := xiCayleyChebyshevPhase q
  let u := xiResolventPoint 1 q
  let w := xiSpectralPoint q ^ 2
  let x := 2 * u - 1
  have hy : y ≠ 0 := xiCayleyChebyshevPhase_ne_zero q
  have hynorm : ‖y‖ ≤ 3 := norm_xiCayleyChebyshevPhase_le_three q
  have hyinvnorm : ‖y⁻¹‖ ≤ 3 := norm_xiCayleyChebyshevPhase_inv_le_three q
  have hrynorm : ‖r * y‖ < 1 := by
    rw [norm_mul]
    nlinarith [norm_nonneg r]
  have hryinorm : ‖r * y⁻¹‖ < 1 := by
    rw [norm_mul]
    nlinarith [norm_nonneg r]
  have hry : 1 - r * y ≠ 0 := by
    intro hzero
    have : r * y = 1 := (sub_eq_zero.mp hzero).symm
    rw [this] at hrynorm
    norm_num at hrynorm
  have hryi : 1 - r * y⁻¹ ≠ 0 := by
    intro hzero
    have : r * y⁻¹ = 1 := (sub_eq_zero.mp hzero).symm
    rw [this] at hryinorm
    norm_num at hryinorm
  have hxphase : (y + y⁻¹) / 2 = x := by
    have h := eval_xiCayleyChebyshevPolynomial_xiResolventPoint 1 q
    have hp :
        evalRealPolynomial (xiCayleyChebyshevPolynomial 1) u = x := by
      simp [u, x, xiCayleyChebyshevPolynomial,
        xiHardEdgeReciprocalPolynomial, evalRealPolynomial]
    change evalRealPolynomial (xiCayleyChebyshevPolynomial 1) u =
      y ^ 1 / 2 + (y ^ 1)⁻¹ / 2 at h
    rw [hp] at h
    norm_num at h
    rw [show (y + y⁻¹) / 2 = y / 2 + y⁻¹ / 2 by ring]
    exact h.symm
  have hAB :
      (1 - r * y) * (1 - r * y⁻¹) =
        1 - 2 * r * x + r ^ 2 := by
    have hx' : y ^ 2 + 1 = 2 * x * y := by
      field_simp [hy] at hxphase
      linear_combination hxphase
    field_simp [hy]
    linear_combination hx' * (-r)
  have hD : 1 - 2 * r * x + r ^ 2 ≠ 0 := by
    rw [← hAB]
    exact mul_ne_zero hry hryi
  have hgeomY := hasSum_geometric_of_norm_lt_one hrynorm
  have hgeomYi := hasSum_geometric_of_norm_lt_one hryinorm
  have hphaseSum : HasSum (fun k : ℕ =>
      u / 2 * (r * y) ^ k + u / 2 * (r * y⁻¹) ^ k)
      (u / 2 * (1 - r * y)⁻¹ + u / 2 * (1 - r * y⁻¹)⁻¹) :=
    (hgeomY.mul_left (u / 2)).add (hgeomYi.mul_left (u / 2))
  have hterm (k : ℕ) :
      xiResolventPoint 1 q *
          evalRealPolynomial (xiCayleyChebyshevPolynomial k)
            (xiResolventPoint 1 q) * r ^ k =
        u / 2 * (r * y) ^ k + u / 2 * (r * y⁻¹) ^ k := by
    rw [eval_xiCayleyChebyshevPolynomial_xiResolventPoint]
    change u * (y ^ k / 2 + (y ^ k)⁻¹ / 2) * r ^ k = _
    rw [mul_pow, mul_pow, inv_pow]
    ring
  have hsum : HasSum (fun k : ℕ =>
      xiResolventPoint 1 q *
        evalRealPolynomial (xiCayleyChebyshevPolynomial k)
          (xiResolventPoint 1 q) * r ^ k)
      (u / 2 * ((1 - r * y)⁻¹ + (1 - r * y⁻¹)⁻¹)) := by
    have hs := HasSum.congr_fun hphaseSum fun k => hterm k
    convert hs using 1 <;> ring
  have hphaseAlg := cayleyChebyshevPhaseGenerating_algebra
    (u := u) hy hxphase hry hryi hD
  have hw : 1 + w ≠ 0 := by
    simpa [w, add_comm] using
      xiSpectralSq_add_ofReal_ne_zero (X := (1 : ℝ)) (by norm_num) q
  have hu : u = (w + 1)⁻¹ := by
    simp [u, w, xiResolventPoint, add_comm]
  have hxw : x = (1 - w) / (1 + w) := by
    dsimp only [x]
    rw [hu]
    rw [show w + 1 = 1 + w by ring]
    field_simp [hw]
    ring
  have hr1 : 1 + r ≠ 0 := by
    intro hzero
    have : r = -1 := by linear_combination hzero
    rw [this] at hr
    norm_num at hr
  have hDw : 1 - 2 * r * ((1 - w) / (1 + w)) + r ^ 2 ≠ 0 := by
    simpa only [hxw] using hD
  have hres := cayleyChebyshev_resolvent_denominator_ne_zero hw hr1 hDw
  have hresAlg := cayleyChebyshevResolvent_algebra hw hr1 hres
  rw [hphaseAlg, hxw, hu, hresAlg] at hsum
  simpa [u, w, xiCayleyAbelParameter, xiResolventPoint, add_comm] using hsum

theorem norm_eval_xiCayleyChebyshevPolynomial_le_three_pow
    (k : ℕ) (q : XiZeroCopy) :
    ‖evalRealPolynomial (xiCayleyChebyshevPolynomial k)
        (xiResolventPoint 1 q)‖ ≤ 3 ^ k := by
  rw [eval_xiCayleyChebyshevPolynomial_xiResolventPoint]
  let y := xiCayleyChebyshevPhase q
  have hpow : ‖y ^ k‖ ≤ 3 ^ k := by
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg y)
      (norm_xiCayleyChebyshevPhase_le_three q) k
  have hinvpow : ‖(y ^ k)⁻¹‖ ≤ 3 ^ k := by
    have h : ‖(y⁻¹) ^ k‖ ≤ 3 ^ k := by
      rw [norm_pow]
      exact pow_le_pow_left₀ (norm_nonneg y⁻¹)
        (norm_xiCayleyChebyshevPhase_inv_le_three q) k
    simpa only [inv_pow] using h
  calc
    ‖y ^ k / 2 + (y ^ k)⁻¹ / 2‖ ≤
        ‖y ^ k / 2‖ + ‖(y ^ k)⁻¹ / 2‖ := norm_add_le _ _
    _ = ‖y ^ k‖ / 2 + ‖(y ^ k)⁻¹‖ / 2 := by
      simp only [norm_div]
      norm_num
    _ ≤ 3 ^ k / 2 + 3 ^ k / 2 := by gcongr
    _ = 3 ^ k := by ring

theorem summable_xiCayleyChebyshevGeneratingAtom_prod
    {r : ℂ} (hr : ‖r‖ < 1 / 3) :
    Summable (fun p : XiZeroCopy × ℕ =>
      xiResolventPoint 1 p.1 *
        evalRealPolynomial (xiCayleyChebyshevPolynomial p.2)
          (xiResolventPoint 1 p.1) * r ^ p.2) := by
  have hratio0 : 0 ≤ 3 * ‖r‖ := mul_nonneg (by norm_num) (norm_nonneg r)
  have hratio1 : 3 * ‖r‖ < 1 := by nlinarith
  have hgeom : Summable (fun k : ℕ => (3 * ‖r‖) ^ k) :=
    summable_geometric_of_lt_one hratio0 hratio1
  have hbase : Summable (fun q : XiZeroCopy => ‖xiResolventPoint 1 q‖) :=
    summable_norm_xiResolventPoint (by norm_num)
  refine Summable.of_norm_bounded
      (g := fun p : XiZeroCopy × ℕ =>
        ‖xiResolventPoint 1 p.1‖ * (3 * ‖r‖) ^ p.2) ?_ ?_
  · exact hbase.mul_of_nonneg hgeom (fun q => norm_nonneg _)
      (fun k => pow_nonneg hratio0 k)
  · intro p
    rw [norm_mul, norm_mul, norm_pow]
    calc
      ‖xiResolventPoint 1 p.1‖ *
          ‖evalRealPolynomial (xiCayleyChebyshevPolynomial p.2)
            (xiResolventPoint 1 p.1)‖ * ‖r‖ ^ p.2 ≤
        ‖xiResolventPoint 1 p.1‖ * 3 ^ p.2 * ‖r‖ ^ p.2 := by
          gcongr
          exact norm_eval_xiCayleyChebyshevPolynomial_le_three_pow p.2 p.1
      _ = ‖xiResolventPoint 1 p.1‖ * (3 * ‖r‖) ^ p.2 := by
        rw [mul_pow]
        ring

/-- Correct unconditional form of Route U's global generating identity.  The paper's asserted
unit disk is replaced by the uniform disk forced by the proved Cayley strip bound. -/
theorem xiCayleyChebyshevMoment_generating_eq_resolvent
    {r : ℂ} (hr : ‖r‖ < 1 / 3) :
    (∑' k : ℕ, xiCayleyChebyshevMoment k * r ^ k) =
      (1 / 2) *
        (xiCayleySpectralResolvent 1 +
          xiCayleyAbelParameter r *
            xiCayleySpectralResolvent (xiCayleyAbelParameter r ^ 2)) := by
  let F : XiZeroCopy → ℕ → ℂ := fun q k =>
    xiResolventPoint 1 q *
      evalRealPolynomial (xiCayleyChebyshevPolynomial k)
        (xiResolventPoint 1 q) * r ^ k
  let A : XiZeroCopy → ℂ := fun q => xiResolventPoint 1 q
  let B : XiZeroCopy → ℂ := fun q =>
    xiCayleyAbelParameter r *
      (xiSpectralPoint q ^ 2 + xiCayleyAbelParameter r ^ 2)⁻¹
  have hprod : Summable (fun p : XiZeroCopy × ℕ => F p.1 p.2) := by
    simpa only [F] using summable_xiCayleyChebyshevGeneratingAtom_prod hr
  have hinner (q : XiZeroCopy) :
      (∑' k : ℕ, F q k) = (1 / 2) * (A q + B q) := by
    exact (hasSum_xiCayleyChebyshevAtom_generating q hr).tsum_eq
  have hinnerSummable : Summable (fun q : XiZeroCopy => ∑' k : ℕ, F q k) :=
    hprod.prod
  have hRhs : Summable (fun q : XiZeroCopy => (1 / 2) * (A q + B q)) :=
    hinnerSummable.congr hinner
  have hAB : Summable (fun q : XiZeroCopy => A q + B q) :=
    (summable_mul_left_iff (by norm_num : (1 / 2 : ℂ) ≠ 0)).mp hRhs
  have hA : Summable A := by
    simpa only [A] using
      summable_xiResolventPoint (X := (1 : ℝ)) (by norm_num)
  have hBraw : Summable (fun q : XiZeroCopy => (A q + B q) - A q) := hAB.sub hA
  have hB : Summable B := hBraw.congr fun q => by ring
  calc
    (∑' k : ℕ, xiCayleyChebyshevMoment k * r ^ k) =
        ∑' k : ℕ, ∑' q : XiZeroCopy, F q k := by
      apply tsum_congr
      intro k
      rw [xiCayleyChebyshevMoment, tsum_mul_right]
    _ = ∑' q : XiZeroCopy, ∑' k : ℕ, F q k := hprod.tsum_comm
    _ = ∑' q : XiZeroCopy, (1 / 2) * (A q + B q) :=
      tsum_congr hinner
    _ = (1 / 2) * ((∑' q : XiZeroCopy, A q) + ∑' q : XiZeroCopy, B q) := by
      rw [show (fun q : XiZeroCopy => (1 / 2 : ℂ) * (A q + B q)) =
          fun q => (1 / 2 : ℂ) * A q + (1 / 2 : ℂ) * B q by
        funext q
        ring]
      rw [(hA.mul_left (1 / 2)).tsum_add (hB.mul_left (1 / 2)),
        tsum_mul_left, tsum_mul_left]
      ring
    _ = (1 / 2) *
        (xiCayleySpectralResolvent 1 +
          xiCayleyAbelParameter r *
            xiCayleySpectralResolvent (xiCayleyAbelParameter r ^ 2)) := by
      rw [xiCayleySpectralResolvent, xiCayleySpectralResolvent]
      rw [show (∑' q : XiZeroCopy, A q) =
          ∑' q : XiZeroCopy, (xiSpectralPoint q ^ 2 + (1 : ℂ))⁻¹ by
        apply tsum_congr
        intro q
        simp [A, xiResolventPoint, add_comm]]
      rw [show (∑' q : XiZeroCopy, B q) =
          xiCayleyAbelParameter r *
            ∑' q : XiZeroCopy,
              (xiSpectralPoint q ^ 2 + xiCayleyAbelParameter r ^ 2)⁻¹ by
        change (∑' q : XiZeroCopy,
            xiCayleyAbelParameter r *
              (xiSpectralPoint q ^ 2 + xiCayleyAbelParameter r ^ 2)⁻¹) = _
        rw [tsum_mul_left]]

/-! ## The exact fourth hostile Laguerre packet -/

theorem routeUAssociatedLaguerreMinusOne_four (x : ℝ) :
    routeUAssociatedLaguerreMinusOne 4 x =
      -x + (3 / 2 : ℝ) * x ^ 2 - (1 / 2 : ℝ) * x ^ 3 +
        (1 / 24 : ℝ) * x ^ 4 := by
  norm_num [routeUAssociatedLaguerreMinusOne, Finset.sum_range_succ]
  ring

/-- Exact hostile value in the paper: `2 + L_4^(-1)(6) = -4`. -/
theorem two_add_routeUAssociatedLaguerreMinusOne_four_six :
    2 + routeUAssociatedLaguerreMinusOne 4 6 = -4 := by
  rw [routeUAssociatedLaguerreMinusOne_four]
  norm_num

/-- Polynomial kernel occurring in the full prime-valuation tower. -/
def routeUValuationKernel (t : ℝ) : ℝ :=
  2 + routeUAssociatedLaguerreMinusOne 4 (2 * t)

theorem routeUValuationKernel_eq (t : ℝ) :
    routeUValuationKernel t =
      2 - 2 * t + 6 * t ^ 2 - 4 * t ^ 3 + (2 / 3 : ℝ) * t ^ 4 := by
  rw [routeUValuationKernel, routeUAssociatedLaguerreMinusOne_four]
  ring

theorem routeUValuationKernel_eq_square (t : ℝ) :
    routeUValuationKernel t =
      (2 / 3 : ℝ) * t ^ 2 * (t - 3) ^ 2 - 2 * t + 2 := by
  rw [routeUValuationKernel_eq]
  ring

/-! ### Closed logarithmic windows used by the two exact prime towers -/

private theorem routeU_exp_one_lt_eleven_fourths :
    Real.exp 1 < (11 / 4 : ℝ) := by
  exact lt_trans Real.exp_one_lt_d9 (by norm_num)

private theorem routeU_eleven_tenths_lt_exp_one_tenth :
    (11 / 10 : ℝ) < Real.exp (1 / 10) := by
  convert (Real.add_one_lt_exp (by norm_num : (1 / 10 : ℝ) ≠ 0)) using 1 <;>
    norm_num

private theorem routeU_exp_nineteen_tenths_lt_seven :
    Real.exp (19 / 10) < 7 := by
  have hprod : Real.exp (19 / 10) * Real.exp (1 / 10) = Real.exp 1 ^ 2 := by
    calc
      Real.exp (19 / 10) * Real.exp (1 / 10) =
          Real.exp ((19 / 10 : ℝ) + 1 / 10) := (Real.exp_add _ _).symm
      _ = Real.exp 2 := by norm_num
      _ = Real.exp 1 ^ 2 := by
        rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add, pow_two]
  have hpow : Real.exp 1 ^ 2 < (11 / 4 : ℝ) ^ 2 :=
    pow_lt_pow_left₀ routeU_exp_one_lt_eleven_fourths
      (Real.exp_pos 1).le (by norm_num)
  have hmul : Real.exp (19 / 10) * (11 / 10 : ℝ) < Real.exp 1 ^ 2 := by
    calc
      Real.exp (19 / 10) * (11 / 10 : ℝ) <
          Real.exp (19 / 10) * Real.exp (1 / 10) :=
        mul_lt_mul_of_pos_left routeU_eleven_tenths_lt_exp_one_tenth
          (Real.exp_pos _)
      _ = Real.exp 1 ^ 2 := hprod
  nlinarith

private theorem routeU_exp_twenty_nine_tenths_lt_nineteen :
    Real.exp (29 / 10) < 19 := by
  have hprod : Real.exp (29 / 10) * Real.exp (1 / 10) = Real.exp 1 ^ 3 := by
    calc
      Real.exp (29 / 10) * Real.exp (1 / 10) =
          Real.exp ((29 / 10 : ℝ) + 1 / 10) := (Real.exp_add _ _).symm
      _ = Real.exp 3 := by norm_num
      _ = Real.exp 1 ^ 3 := by
        rw [show (3 : ℝ) = 1 + (1 + 1) by norm_num,
          Real.exp_add, Real.exp_add]
        ring
  have hpow : Real.exp 1 ^ 3 < (11 / 4 : ℝ) ^ 3 :=
    pow_lt_pow_left₀ routeU_exp_one_lt_eleven_fourths
      (Real.exp_pos 1).le (by norm_num)
  have hmul : Real.exp (29 / 10) * (11 / 10 : ℝ) < Real.exp 1 ^ 3 := by
    calc
      Real.exp (29 / 10) * (11 / 10 : ℝ) <
          Real.exp (29 / 10) * Real.exp (1 / 10) :=
        mul_lt_mul_of_pos_left routeU_eleven_tenths_lt_exp_one_tenth
          (Real.exp_pos _)
      _ = Real.exp 1 ^ 3 := hprod
  nlinarith

private theorem routeU_seven_lt_exp_two : (7 : ℝ) < Real.exp 2 := by
  have he : (27 / 10 : ℝ) < Real.exp 1 :=
    lt_trans (by norm_num) Real.exp_one_gt_d9
  have hpow : (27 / 10 : ℝ) ^ 2 < Real.exp 1 ^ 2 :=
    pow_lt_pow_left₀ he (by norm_num) (by norm_num)
  calc
    (7 : ℝ) < (27 / 10 : ℝ) ^ 2 := by norm_num
    _ < Real.exp 1 ^ 2 := hpow
    _ = Real.exp 2 := by
      rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add, pow_two]

private theorem routeU_nineteen_lt_exp_three : (19 : ℝ) < Real.exp 3 := by
  have he : (27 / 10 : ℝ) < Real.exp 1 :=
    lt_trans (by norm_num) Real.exp_one_gt_d9
  have hpow : (27 / 10 : ℝ) ^ 3 < Real.exp 1 ^ 3 :=
    pow_lt_pow_left₀ he (by norm_num) (by norm_num)
  calc
    (19 : ℝ) < (27 / 10 : ℝ) ^ 3 := by norm_num
    _ < Real.exp 1 ^ 3 := hpow
    _ = Real.exp 3 := by
      rw [show (3 : ℝ) = 1 + (1 + 1) by norm_num,
        Real.exp_add, Real.exp_add]
      ring

theorem routeU_log_seven_mem :
    (19 / 10 : ℝ) < Real.log 7 ∧ Real.log 7 < 2 := by
  constructor
  · exact (Real.lt_log_iff_exp_lt (by norm_num)).2
      routeU_exp_nineteen_tenths_lt_seven
  · exact (Real.log_lt_iff_lt_exp (by norm_num)).2 routeU_seven_lt_exp_two

theorem routeU_log_nineteen_mem :
    (29 / 10 : ℝ) < Real.log 19 ∧ Real.log 19 < 3 := by
  constructor
  · exact (Real.lt_log_iff_exp_lt (by norm_num)).2
      routeU_exp_twenty_nine_tenths_lt_nineteen
  · exact (Real.log_lt_iff_lt_exp (by norm_num)).2 routeU_nineteen_lt_exp_three

private theorem routeUValuationKernel_translate (x : ℝ) :
    routeUValuationKernel ((19 / 5 : ℝ) + x) =
      (1052 / 1875 : ℝ) + (6242 / 375 : ℝ) * x +
        (454 / 25 : ℝ) * x ^ 2 + (92 / 15 : ℝ) * x ^ 3 +
          (2 / 3 : ℝ) * x ^ 4 := by
  rw [routeUValuationKernel_eq]
  ring

theorem routeUValuationKernel_pos_of_far {t : ℝ}
    (ht : (19 / 5 : ℝ) ≤ t) : 0 < routeUValuationKernel t := by
  let x := t - (19 / 5 : ℝ)
  have hx : 0 ≤ x := by dsimp only [x]; linarith
  have ht' : t = (19 / 5 : ℝ) + x := by dsimp only [x]; ring
  rw [ht', routeUValuationKernel_translate]
  positivity

theorem routeUValuationKernel_strictMono_far
    {s t : ℝ} (hs : (19 / 5 : ℝ) ≤ s) (hst : s < t) :
    routeUValuationKernel s < routeUValuationKernel t := by
  let x := s - (19 / 5 : ℝ)
  let y := t - (19 / 5 : ℝ)
  have hx : 0 ≤ x := by dsimp only [x]; linarith
  have hxy : x < y := by dsimp only [x, y]; linarith
  have h2 : x ^ 2 < y ^ 2 :=
    pow_lt_pow_left₀ hxy hx (by norm_num)
  have h3 : x ^ 3 < y ^ 3 :=
    pow_lt_pow_left₀ hxy hx (by norm_num)
  have h4 : x ^ 4 < y ^ 4 :=
    pow_lt_pow_left₀ hxy hx (by norm_num)
  have hs' : s = (19 / 5 : ℝ) + x := by dsimp only [x]; ring
  have ht' : t = (19 / 5 : ℝ) + y := by dsimp only [y]; ring
  rw [hs', ht', routeUValuationKernel_translate,
    routeUValuationKernel_translate]
  nlinarith

theorem routeUValuationKernel_log_seven_pos :
    0 < routeUValuationKernel (Real.log 7) := by
  obtain ⟨hlow, hupp⟩ := routeU_log_seven_mem
  let d := 2 - Real.log 7
  have hd0 : 0 < d := by dsimp only [d]; linarith
  have hd1 : d < (1 / 10 : ℝ) := by dsimp only [d]; linarith
  have hd2 : d ^ 2 < (1 / 100 : ℝ) := by nlinarith [sq_nonneg d]
  have hd3 : 0 ≤ d ^ 3 := pow_nonneg hd0.le 3
  have hid :
      routeUValuationKernel (Real.log 7) =
        (2 / 3 : ℝ) + d *
          ((14 / 3 : ℝ) - 2 * d - (4 / 3 : ℝ) * d ^ 2 +
            (2 / 3 : ℝ) * d ^ 3) := by
    rw [routeUValuationKernel_eq]
    dsimp only [d]
    ring
  rw [hid]
  have hbracket :
      0 < (14 / 3 : ℝ) - 2 * d - (4 / 3 : ℝ) * d ^ 2 +
        (2 / 3 : ℝ) * d ^ 3 := by
    nlinarith
  positivity

/-! ### Complete prime-valuation towers -/

/-- Exact ratio `p^(-3/2)` written in the square-root chart used by the rational bounds. -/
def routeUPrimeValuationRatio (p : ℝ) : ℝ :=
  (p * Real.sqrt p)⁻¹

theorem routeUPrimeValuationRatio_eq_rpow {p : ℝ} (hp : 0 < p) :
    routeUPrimeValuationRatio p = p ^ (-3 / 2 : ℝ) := by
  rw [routeUPrimeValuationRatio, Real.sqrt_eq_rpow]
  calc
    (p * p ^ (1 / 2 : ℝ))⁻¹ =
        (p ^ (1 : ℝ) * p ^ (1 / 2 : ℝ))⁻¹ := by rw [Real.rpow_one]
    _ = (p ^ ((1 : ℝ) + 1 / 2))⁻¹ := by rw [Real.rpow_add hp]
    _ = p ^ (-3 / 2 : ℝ) := by
      norm_num
      exact (Real.rpow_neg hp.le (3 / 2 : ℝ)).symm

theorem routeUPrimeValuationRatio_pow_eq_rpow
    {p : ℝ} (hp : 0 < p) (e : ℕ) :
    routeUPrimeValuationRatio p ^ e = p ^ ((-3 / 2 : ℝ) * e) := by
  rw [routeUPrimeValuationRatio_eq_rpow hp]
  exact (Real.rpow_mul_natCast hp.le (-3 / 2 : ℝ) e).symm

/-- Depth-`e+1` summand in the full Route U local prime tower. -/
def routeUPrimeValuationTerm (p : ℝ) (e : ℕ) : ℝ :=
  routeUPrimeValuationRatio p ^ (e + 1) *
    routeUValuationKernel ((e + 1 : ℕ) * Real.log p)

/-- Full local tower `S₂(p)`, including every prime-power depth. -/
def routeUPrimeValuationTower (p : ℝ) : ℝ :=
  ∑' e : ℕ, routeUPrimeValuationTerm p e

theorem routeUPrimeValuationTerm_eq_paper_rpow
    {p : ℝ} (hp : 0 < p) (e : ℕ) :
    routeUPrimeValuationTerm p e =
      p ^ ((-3 / 2 : ℝ) * (e + 1 : ℕ)) *
        (2 + routeUAssociatedLaguerreMinusOne 4
          (2 * ((e + 1 : ℕ) * Real.log p))) := by
  rw [routeUPrimeValuationTerm, routeUPrimeValuationRatio_pow_eq_rpow hp,
    routeUValuationKernel]

private theorem routeUValuationKernel_norm_le
    {N t : ℝ} (hN : 1 ≤ N) (ht0 : 0 ≤ t) (ht : t ≤ 3 * N) :
    ‖routeUValuationKernel t‖ ≤ 224 * N ^ 4 := by
  have hN0 : 0 ≤ N := le_trans (by norm_num) hN
  have hN1 : N ≤ N ^ 4 := by
    simpa using (pow_le_pow_right₀ hN (by norm_num : 1 ≤ 4))
  have hN2 : N ^ 2 ≤ N ^ 4 :=
    pow_le_pow_right₀ hN (by norm_num)
  have hN3 : N ^ 3 ≤ N ^ 4 :=
    pow_le_pow_right₀ hN (by norm_num)
  have ht1 : t ≤ 3 * N ^ 4 := le_trans ht (by gcongr)
  have ht2 : t ^ 2 ≤ 9 * N ^ 4 := by
    calc
      t ^ 2 ≤ (3 * N) ^ 2 := pow_le_pow_left₀ ht0 ht 2
      _ = 9 * N ^ 2 := by ring
      _ ≤ 9 * N ^ 4 := by gcongr
  have ht3 : t ^ 3 ≤ 27 * N ^ 4 := by
    calc
      t ^ 3 ≤ (3 * N) ^ 3 := pow_le_pow_left₀ ht0 ht 3
      _ = 27 * N ^ 3 := by ring
      _ ≤ 27 * N ^ 4 := by gcongr
  have ht4 : t ^ 4 ≤ 81 * N ^ 4 := by
    calc
      t ^ 4 ≤ (3 * N) ^ 4 := pow_le_pow_left₀ ht0 ht 4
      _ = 81 * N ^ 4 := by ring
  rw [Real.norm_eq_abs, abs_le, routeUValuationKernel_eq]
  constructor <;>
    nlinarith [pow_nonneg ht0 2, pow_nonneg ht0 3, pow_nonneg ht0 4,
      pow_nonneg hN0 4]

theorem summable_routeUPrimeValuationTerm
    {p : ℝ} (hlog0 : 0 ≤ Real.log p) (hlog3 : Real.log p ≤ 3)
    (hq : ‖routeUPrimeValuationRatio p‖ < 1) :
    Summable (routeUPrimeValuationTerm p) := by
  let q := routeUPrimeValuationRatio p
  have hgeom : Summable (fun n : ℕ =>
      (n : ℝ) ^ 4 * ‖q‖ ^ n) := by
    simpa using
      (summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 4
        (r := ‖q‖) (by simpa using hq))
  have hshift : Summable (fun e : ℕ =>
      ((e + 1 : ℕ) : ℝ) ^ 4 * ‖q‖ ^ (e + 1)) := by
    simpa [Function.comp_def, Nat.succ_eq_add_one] using
      hgeom.comp_injective Nat.succ_injective
  apply Summable.of_norm_bounded (hshift.mul_left 224)
  intro e
  let N : ℝ := ((e + 1 : ℕ) : ℝ)
  have hN : 1 ≤ N := by dsimp only [N]; norm_num
  have hN0 : 0 ≤ N := le_trans (by norm_num) hN
  have ht0 : 0 ≤ N * Real.log p := mul_nonneg hN0 hlog0
  have ht3 : N * Real.log p ≤ 3 * N := by nlinarith
  have hk := routeUValuationKernel_norm_le hN ht0 ht3
  rw [routeUPrimeValuationTerm, norm_mul, norm_pow]
  change ‖q‖ ^ (e + 1) *
      ‖routeUValuationKernel (N * Real.log p)‖ ≤
    224 * (N ^ 4 * ‖q‖ ^ (e + 1))
  calc
    ‖q‖ ^ (e + 1) * ‖routeUValuationKernel (N * Real.log p)‖ ≤
        ‖q‖ ^ (e + 1) * (224 * N ^ 4) :=
      mul_le_mul_of_nonneg_left hk (pow_nonneg (norm_nonneg q) _)
    _ = 224 * (N ^ 4 * ‖q‖ ^ (e + 1)) := by ring

theorem routeUPrimeValuationRatio_pos {p : ℝ} (hp : 0 < p) :
    0 < routeUPrimeValuationRatio p := by
  rw [routeUPrimeValuationRatio]
  exact inv_pos.mpr (mul_pos hp (Real.sqrt_pos.2 hp))

theorem norm_routeUPrimeValuationRatio_seven_lt_one :
    ‖routeUPrimeValuationRatio 7‖ < 1 := by
  have hsqrt : (1 : ℝ) < Real.sqrt 7 :=
    (Real.lt_sqrt (by norm_num)).2 (by norm_num)
  have hden : (1 : ℝ) < 7 * Real.sqrt 7 := by nlinarith
  have hpos := routeUPrimeValuationRatio_pos (by norm_num : (0 : ℝ) < 7)
  rw [Real.norm_eq_abs, abs_of_pos hpos, routeUPrimeValuationRatio]
  exact (inv_lt_one₀ (by positivity)).2 hden

theorem summable_routeUPrimeValuationTerm_seven :
    Summable (routeUPrimeValuationTerm 7) := by
  exact summable_routeUPrimeValuationTerm
    (Real.log_nonneg (by norm_num))
    (le_trans routeU_log_seven_mem.2.le (by norm_num))
    norm_routeUPrimeValuationRatio_seven_lt_one

theorem routeUPrimeValuationTerm_seven_pos (e : ℕ) :
    0 < routeUPrimeValuationTerm 7 e := by
  have hq : 0 < routeUPrimeValuationRatio 7 :=
    routeUPrimeValuationRatio_pos (by norm_num)
  have hk : 0 < routeUValuationKernel ((e + 1 : ℕ) * Real.log 7) := by
    cases e with
    | zero => simpa using routeUValuationKernel_log_seven_pos
    | succ e =>
        apply routeUValuationKernel_pos_of_far
        have hdepth : (2 : ℝ) ≤ ((e + 1 + 1 : ℕ) : ℝ) := by
          exact_mod_cast (by omega : 2 ≤ e + 1 + 1)
        have hlog0 : 0 < Real.log 7 := Real.log_pos (by norm_num)
        have hmul : 2 * Real.log 7 ≤
            ((e + 1 + 1 : ℕ) : ℝ) * Real.log 7 :=
          mul_le_mul_of_nonneg_right hdepth hlog0.le
        nlinarith [routeU_log_seven_mem.1]
  rw [routeUPrimeValuationTerm]
  exact mul_pos (pow_pos hq _) hk

/-- Exact first sign in the paper, with every valuation depth retained. -/
theorem routeUPrimeValuationTower_seven_pos :
    0 < routeUPrimeValuationTower 7 := by
  rw [routeUPrimeValuationTower]
  exact summable_routeUPrimeValuationTerm_seven.tsum_pos
    (fun e => (routeUPrimeValuationTerm_seven_pos e).le) 0
    (routeUPrimeValuationTerm_seven_pos 0)

theorem routeU_sqrt_nineteen_mem :
    (87 / 20 : ℝ) < Real.sqrt 19 ∧ Real.sqrt 19 < (22 / 5 : ℝ) := by
  constructor
  · exact (Real.lt_sqrt (by norm_num)).2 (by norm_num)
  · exact (Real.sqrt_lt' (by norm_num)).2 (by norm_num)

theorem routeUPrimeValuationRatio_nineteen_bounds :
    (5 / 418 : ℝ) < routeUPrimeValuationRatio 19 ∧
      routeUPrimeValuationRatio 19 < (20 / 1653 : ℝ) := by
  have hdenpos : 0 < (19 : ℝ) * Real.sqrt 19 := by positivity
  have hdenUpper : (19 : ℝ) * Real.sqrt 19 < 418 / 5 := by
    nlinarith [routeU_sqrt_nineteen_mem.2]
  have hdenLower : (1653 / 20 : ℝ) < 19 * Real.sqrt 19 := by
    nlinarith [routeU_sqrt_nineteen_mem.1]
  rw [routeUPrimeValuationRatio]
  constructor
  · have h := one_div_lt_one_div_of_lt hdenpos hdenUpper
    norm_num at h ⊢
    exact h
  · have h := one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < 1653 / 20)
      hdenLower
    norm_num at h ⊢
    exact h

theorem norm_routeUPrimeValuationRatio_nineteen_lt_one :
    ‖routeUPrimeValuationRatio 19‖ < 1 := by
  have hqpos := routeUPrimeValuationRatio_pos (by norm_num : (0 : ℝ) < 19)
  rw [Real.norm_eq_abs, abs_of_pos hqpos]
  exact lt_trans routeUPrimeValuationRatio_nineteen_bounds.2 (by norm_num)

theorem summable_routeUPrimeValuationTerm_nineteen :
    Summable (routeUPrimeValuationTerm 19) := by
  exact summable_routeUPrimeValuationTerm
    (Real.log_nonneg (by norm_num)) routeU_log_nineteen_mem.2.le
    norm_routeUPrimeValuationRatio_nineteen_lt_one

theorem routeUValuationKernel_log_nineteen_lt :
    routeUValuationKernel (Real.log 19) < (-187 / 50 : ℝ) := by
  obtain ⟨hlow, hupp⟩ := routeU_log_nineteen_mem
  have hlpos : 0 < Real.log 19 := Real.log_pos (by norm_num)
  have hlsq : Real.log 19 ^ 2 < (9 : ℝ) := by
    have h := pow_lt_pow_left₀ (n := 2) hupp hlpos.le (by norm_num)
    norm_num at h ⊢
    exact h
  let d := 3 - Real.log 19
  have hd0 : 0 < d := by dsimp only [d]; linarith
  have hd1 : d < (1 / 10 : ℝ) := by dsimp only [d]; linarith
  have hd2 : d ^ 2 < (1 / 100 : ℝ) := by nlinarith [sq_nonneg d]
  have hprod : Real.log 19 ^ 2 * (Real.log 19 - 3) ^ 2 < (9 / 100 : ℝ) := by
    have hmul : Real.log 19 ^ 2 * d ^ 2 < Real.log 19 ^ 2 * (1 / 100 : ℝ) :=
      mul_lt_mul_of_pos_left hd2 (sq_pos_of_pos hlpos)
    have hdEq : (Real.log 19 - 3) ^ 2 = d ^ 2 := by
      dsimp only [d]
      ring
    rw [hdEq]
    nlinarith
  rw [routeUValuationKernel_eq_square]
  nlinarith

theorem routeUPrimeValuationTerm_nineteen_zero_lt_neg_one_div_twenty_three :
    routeUPrimeValuationTerm 19 0 < (-1 / 23 : ℝ) := by
  let q := routeUPrimeValuationRatio 19
  let f := routeUValuationKernel (Real.log 19)
  have hq : (5 / 418 : ℝ) < q :=
    routeUPrimeValuationRatio_nineteen_bounds.1
  have hf : f < (-187 / 50 : ℝ) :=
    routeUValuationKernel_log_nineteen_lt
  have hf0 : f < 0 := lt_trans hf (by norm_num)
  have hfirst : q * f < (5 / 418 : ℝ) * (-187 / 50 : ℝ) := by
    calc
      q * f < (5 / 418 : ℝ) * f := mul_lt_mul_of_neg_right hq hf0
      _ < (5 / 418 : ℝ) * (-187 / 50 : ℝ) :=
        mul_lt_mul_of_pos_left hf (by norm_num)
  rw [routeUPrimeValuationTerm]
  simp only [zero_add, Nat.cast_one, one_mul, pow_one]
  change q * f < (-1 / 23 : ℝ)
  exact lt_trans hfirst (by norm_num)

private theorem routeUPrimeValuationRatio_nineteen_lt_one_div_eighty_two :
    routeUPrimeValuationRatio 19 < (1 / 82 : ℝ) :=
  lt_trans routeUPrimeValuationRatio_nineteen_bounds.2 (by norm_num)

theorem routeUValuationKernel_nineteen_depth_pos
    {e : ℕ} (he : 2 ≤ e) :
    0 < routeUValuationKernel ((e : ℝ) * Real.log 19) := by
  apply routeUValuationKernel_pos_of_far
  have heR : (2 : ℝ) ≤ e := by exact_mod_cast he
  have hlpos : 0 < Real.log 19 := Real.log_pos (by norm_num)
  have hmul : 2 * Real.log 19 ≤ (e : ℝ) * Real.log 19 :=
    mul_le_mul_of_nonneg_right heR hlpos.le
  nlinarith [routeU_log_nineteen_mem.1]

theorem routeUValuationKernel_nineteen_depth_lt_three_mul
    {e : ℕ} (he : 2 ≤ e) :
    routeUValuationKernel ((e : ℝ) * Real.log 19) <
      routeUValuationKernel (3 * (e : ℝ)) := by
  apply routeUValuationKernel_strictMono_far
  · have heR : (2 : ℝ) ≤ e := by exact_mod_cast he
    have hlpos : 0 < Real.log 19 := Real.log_pos (by norm_num)
    have hmul : 2 * Real.log 19 ≤ (e : ℝ) * Real.log 19 :=
      mul_le_mul_of_nonneg_right heR hlpos.le
    nlinarith [routeU_log_nineteen_mem.1]
  · have hepos : (0 : ℝ) < e := by exact_mod_cast (lt_of_lt_of_le (by omega) he)
    simpa [mul_comm] using
      (mul_lt_mul_of_pos_right routeU_log_nineteen_mem.2 hepos)

theorem routeUValuationKernel_six :
    routeUValuationKernel 6 = 206 := by
  rw [routeUValuationKernel_eq]
  norm_num

theorem routeUValuationKernel_three_mul_depth_lt
    {e : ℕ} (he : 3 ≤ e) :
    routeUValuationKernel (3 * (e : ℝ)) < 54 * (e : ℝ) ^ 4 := by
  let E : ℝ := e
  let x : ℝ := E - 3
  have hx : 0 ≤ x := by
    have heR : (3 : ℝ) ≤ E := by
      dsimp only [E]
      exact_mod_cast he
    dsimp only [x]
    linarith
  have hid : routeUValuationKernel (3 * E) - 54 * E ^ 4 =
      -2446 - 2598 * x - 918 * x ^ 2 - 108 * x ^ 3 := by
    rw [routeUValuationKernel_eq]
    dsimp only [x]
    ring
  change routeUValuationKernel (3 * E) < 54 * E ^ 4
  have hx2 : 0 ≤ x ^ 2 := pow_nonneg hx 2
  have hx3 : 0 ≤ x ^ 3 := pow_nonneg hx 3
  nlinarith [hid]

theorem routeUPrimeValuationTerm_nineteen_one_lt :
    routeUPrimeValuationTerm 19 1 < (206 / 82 ^ 2 : ℝ) := by
  let q := routeUPrimeValuationRatio 19
  have hq0 : 0 < q := routeUPrimeValuationRatio_pos (by norm_num)
  have hq : q < (1 / 82 : ℝ) :=
    routeUPrimeValuationRatio_nineteen_lt_one_div_eighty_two
  have hq2 : q ^ 2 < (1 / 82 : ℝ) ^ 2 :=
    pow_lt_pow_left₀ hq hq0.le (by norm_num)
  have hk0 : 0 < routeUValuationKernel (2 * Real.log 19) :=
    routeUValuationKernel_nineteen_depth_pos (e := 2) (by norm_num)
  have hk : routeUValuationKernel (2 * Real.log 19) < 206 := by
    calc
      routeUValuationKernel (2 * Real.log 19) <
          routeUValuationKernel (3 * (2 : ℝ)) :=
        routeUValuationKernel_nineteen_depth_lt_three_mul (e := 2) (by norm_num)
      _ = 206 := by rw [show (3 : ℝ) * 2 = 6 by norm_num,
        routeUValuationKernel_six]
  rw [routeUPrimeValuationTerm]
  norm_num only [Nat.cast_ofNat]
  change q ^ 2 * routeUValuationKernel (2 * Real.log 19) < _
  have hmain : q ^ 2 * routeUValuationKernel (2 * Real.log 19) <
      (1 / 82 : ℝ) ^ 2 * 206 := by
    calc
    q ^ 2 * routeUValuationKernel (2 * Real.log 19) <
        (1 / 82 : ℝ) ^ 2 * routeUValuationKernel (2 * Real.log 19) :=
      mul_lt_mul_of_pos_right hq2 hk0
    _ <
        (1 / 82 : ℝ) ^ 2 * 206 :=
      mul_lt_mul_of_pos_left hk (pow_pos (by norm_num) 2)
  norm_num at hmain ⊢
  exact hmain

theorem routeUPrimeValuationTerm_nineteen_depth_le_majorant
    {e : ℕ} (he : 3 ≤ e) :
    routeUPrimeValuationRatio 19 ^ e *
        routeUValuationKernel ((e : ℝ) * Real.log 19) ≤
      54 * (e : ℝ) ^ 4 * (1 / 82 : ℝ) ^ e := by
  let q := routeUPrimeValuationRatio 19
  have hq0 : 0 < q := routeUPrimeValuationRatio_pos (by norm_num)
  have hq : q < (1 / 82 : ℝ) :=
    routeUPrimeValuationRatio_nineteen_lt_one_div_eighty_two
  have hqpow : q ^ e ≤ (1 / 82 : ℝ) ^ e :=
    (pow_le_pow_left₀ hq0.le hq.le e)
  have hk0 : 0 < routeUValuationKernel ((e : ℝ) * Real.log 19) :=
    routeUValuationKernel_nineteen_depth_pos (le_trans (by norm_num) he)
  have hk : routeUValuationKernel ((e : ℝ) * Real.log 19) <
      54 * (e : ℝ) ^ 4 :=
    lt_trans (routeUValuationKernel_nineteen_depth_lt_three_mul
      (le_trans (by norm_num) he))
      (routeUValuationKernel_three_mul_depth_lt he)
  change q ^ e * routeUValuationKernel ((e : ℝ) * Real.log 19) ≤ _
  calc
    q ^ e * routeUValuationKernel ((e : ℝ) * Real.log 19) ≤
        (1 / 82 : ℝ) ^ e * routeUValuationKernel ((e : ℝ) * Real.log 19) :=
      mul_le_mul_of_nonneg_right hqpow hk0.le
    _ ≤ (1 / 82 : ℝ) ^ e * (54 * (e : ℝ) ^ 4) :=
      mul_le_mul_of_nonneg_left hk.le (pow_nonneg (by norm_num) e)
    _ = 54 * (e : ℝ) ^ 4 * (1 / 82 : ℝ) ^ e := by ring

/-- Polynomial-geometric envelope for depths `e = n+3`. -/
def routeUFourthGeometricTail (n : ℕ) : ℝ :=
  ((n + 3 : ℕ) : ℝ) ^ 4 * (1 / 82 : ℝ) ^ (n + 3)

theorem routeUFourthGeometricTail_ratio (n : ℕ) :
    routeUFourthGeometricTail (n + 1) ≤
      (1 / 25 : ℝ) * routeUFourthGeometricTail n := by
  let N : ℝ := n
  have hN : 0 ≤ N := by positivity
  have hid :
      82 * (N + 3) ^ 4 - 25 * (N + 4) ^ 4 =
        57 * N ^ 4 + 584 * N ^ 3 + 2028 * N ^ 2 + 2456 * N + 242 := by
    ring
  have hpoly : 25 * (N + 4) ^ 4 ≤ 82 * (N + 3) ^ 4 := by
    have h2 : 0 ≤ N ^ 2 := pow_nonneg hN 2
    have h3 : 0 ≤ N ^ 3 := pow_nonneg hN 3
    have h4 : 0 ≤ N ^ 4 := pow_nonneg hN 4
    nlinarith [hid]
  have hsmall : (N + 4) ^ 4 * (1 / 82 : ℝ) ≤
      (1 / 25 : ℝ) * (N + 3) ^ 4 := by
    nlinarith
  rw [routeUFourthGeometricTail, routeUFourthGeometricTail]
  have hindex : n + 1 + 3 = (n + 3) + 1 := by omega
  have hgeomPow : (1 / 82 : ℝ) ^ (n + 1 + 3) =
      (1 / 82 : ℝ) ^ (n + 3) * (1 / 82 : ℝ) := by
    rw [hindex, pow_succ]
  rw [hgeomPow]
  push_cast
  have hn4 : (n : ℝ) + 1 + 3 = N + 4 := by dsimp only [N]; ring
  have hn3 : (n : ℝ) + 3 = N + 3 := by rfl
  rw [hn4, hn3]
  calc
    (N + 4) ^ 4 *
        ((1 / 82 : ℝ) ^ (n + 3) * (1 / 82 : ℝ)) =
      ((N + 4) ^ 4 * (1 / 82 : ℝ)) * (1 / 82 : ℝ) ^ (n + 3) := by ring
    _ ≤ ((1 / 25 : ℝ) * (N + 3) ^ 4) *
        (1 / 82 : ℝ) ^ (n + 3) :=
      mul_le_mul_of_nonneg_right hsmall (pow_nonneg (by norm_num) _)
    _ = (1 / 25 : ℝ) *
        ((N + 3) ^ 4 * (1 / 82 : ℝ) ^ (n + 3)) := by ring

theorem routeUFourthGeometricTail_le_geometric (n : ℕ) :
    routeUFourthGeometricTail n ≤
      routeUFourthGeometricTail 0 * (1 / 25 : ℝ) ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      calc
        routeUFourthGeometricTail (n + 1) ≤
            (1 / 25 : ℝ) * routeUFourthGeometricTail n :=
          routeUFourthGeometricTail_ratio n
        _ ≤ (1 / 25 : ℝ) *
            (routeUFourthGeometricTail 0 * (1 / 25 : ℝ) ^ n) := by
          gcongr
        _ = routeUFourthGeometricTail 0 * (1 / 25 : ℝ) ^ (n + 1) := by
          rw [pow_succ]
          ring

theorem summable_routeUFourthGeometricTail :
    Summable routeUFourthGeometricTail := by
  have hbase : Summable (fun n : ℕ =>
      (n : ℝ) ^ 4 * (1 / 82 : ℝ) ^ n) :=
    summable_pow_mul_geometric_of_norm_lt_one 4 (by norm_num)
  have hshift := (summable_nat_add_iff 3).2 hbase
  change Summable (fun n : ℕ =>
    ((n + 3 : ℕ) : ℝ) ^ 4 * (1 / 82 : ℝ) ^ (n + 3))
  exact hshift

theorem tsum_routeUFourthGeometricTail_le :
    (∑' n : ℕ, routeUFourthGeometricTail n) ≤
      routeUFourthGeometricTail 0 * (25 / 24 : ℝ) := by
  have hgeom : Summable (fun n : ℕ =>
      routeUFourthGeometricTail 0 * (1 / 25 : ℝ) ^ n) := by
    have hg : Summable (fun n : ℕ => (1 / 25 : ℝ) ^ n) :=
      summable_geometric_of_norm_lt_one (by norm_num)
    exact hg.mul_left _
  have hle := summable_routeUFourthGeometricTail.tsum_le_tsum
    routeUFourthGeometricTail_le_geometric hgeom
  rw [tsum_mul_left] at hle
  have hsum : (∑' n : ℕ, (1 / 25 : ℝ) ^ n) = 25 / 24 := by
    have hg : HasSum (fun n : ℕ => (1 / 25 : ℝ) ^ n)
        ((1 - (1 / 25 : ℝ))⁻¹) :=
      hasSum_geometric_of_norm_lt_one (by norm_num)
    have heq := hg.tsum_eq
    norm_num at heq ⊢
    exact heq
  rw [hsum] at hle
  exact hle

theorem routeUPrimeValuationTerm_nineteen_add_two_le_majorant (n : ℕ) :
    routeUPrimeValuationTerm 19 (n + 2) ≤
      54 * routeUFourthGeometricTail n := by
  have hdepth := routeUPrimeValuationTerm_nineteen_depth_le_majorant
    (e := n + 3) (by omega : 3 ≤ n + 3)
  simpa [routeUPrimeValuationTerm, routeUFourthGeometricTail,
    Nat.add_assoc, mul_assoc] using hdepth

theorem tsum_routeUPrimeValuationTerm_nineteen_from_depth_three_lt :
    (∑' n : ℕ, routeUPrimeValuationTerm 19 (n + 2)) < (9 / 1000 : ℝ) := by
  have hterms : Summable (fun n : ℕ => routeUPrimeValuationTerm 19 (n + 2)) :=
    (summable_nat_add_iff 2).2 summable_routeUPrimeValuationTerm_nineteen
  have hmajor : Summable (fun n : ℕ => 54 * routeUFourthGeometricTail n) :=
    summable_routeUFourthGeometricTail.mul_left 54
  have hle := hterms.tsum_le_tsum
    routeUPrimeValuationTerm_nineteen_add_two_le_majorant hmajor
  rw [tsum_mul_left] at hle
  have henv := tsum_routeUFourthGeometricTail_le
  have hscaled : 54 * (∑' n : ℕ, routeUFourthGeometricTail n) ≤
      54 * (routeUFourthGeometricTail 0 * (25 / 24 : ℝ)) := by
    gcongr
  have hrat :
      54 * (routeUFourthGeometricTail 0 * (25 / 24 : ℝ)) <
        (9 / 1000 : ℝ) := by
    norm_num [routeUFourthGeometricTail]
  exact lt_of_le_of_lt (le_trans hle hscaled) hrat

theorem tsum_routeUPrimeValuationTerm_nineteen_tail_lt :
    (∑' n : ℕ, routeUPrimeValuationTerm 19 (n + 1)) < (1 / 25 : ℝ) := by
  let F : ℕ → ℝ := fun n => routeUPrimeValuationTerm 19 (n + 1)
  have hF : Summable F := by
    dsimp only [F]
    exact (summable_nat_add_iff 1).2 summable_routeUPrimeValuationTerm_nineteen
  have hsplit := hF.sum_add_tsum_nat_add 1
  have hsplit' :
      routeUPrimeValuationTerm 19 1 +
          (∑' n : ℕ, routeUPrimeValuationTerm 19 (n + 2)) =
        ∑' n : ℕ, routeUPrimeValuationTerm 19 (n + 1) := by
    simpa [F, Nat.add_assoc] using hsplit
  rw [← hsplit']
  have hdepthTwo : routeUPrimeValuationTerm 19 1 < (31 / 1000 : ℝ) :=
    lt_trans routeUPrimeValuationTerm_nineteen_one_lt (by norm_num)
  have hrest := tsum_routeUPrimeValuationTerm_nineteen_from_depth_three_lt
  nlinarith

/-- Exact second sign in the paper, with no prime-power cutoff. -/
theorem routeUPrimeValuationTower_nineteen_neg :
    routeUPrimeValuationTower 19 < 0 := by
  have hsplit := summable_routeUPrimeValuationTerm_nineteen.sum_add_tsum_nat_add 1
  have hsplit' :
      routeUPrimeValuationTerm 19 0 +
          (∑' n : ℕ, routeUPrimeValuationTerm 19 (n + 1)) =
        routeUPrimeValuationTower 19 := by
    rw [routeUPrimeValuationTower]
    simpa using hsplit
  rw [← hsplit']
  have hfirst :=
    routeUPrimeValuationTerm_nineteen_zero_lt_neg_one_div_twenty_three
  have htail := tsum_routeUPrimeValuationTerm_nineteen_tail_lt
  nlinarith


end

end RHTower

