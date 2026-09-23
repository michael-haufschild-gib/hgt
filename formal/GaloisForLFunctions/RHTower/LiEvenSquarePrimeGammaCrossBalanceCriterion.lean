import GaloisForLFunctions.RHTower.LiEvenSquareReflectionBlindnessNoGo
import GaloisForLFunctions.RHTower.XiShiftedHardEdgePrimeGammaKelvinCrossCurrent
import GaloisForLFunctions.RHTower.HeatMomentDerivativeLadder

/-!
# Even Li squares as a fixed completed prime--Gamma cross balance

At quarter shift, the even Li weighted square is exactly the polarized Route-U cross term between
`U_n` and `(1-X)U_n`.  The factor is exactly two at the reciprocal-Hankel level.  On RH the
common-degree shifted reversals have pointwise nonnegative product on every real squared spectral
coordinate, so every literal completed prime--Gamma cross balance is nonnegative.  Conversely,
pointwise nonnegativity integrates to the fixed cross capital, hence to every even Li source and
therefore to RH.
-/

open scoped BigOperators
open Complex Matrix Polynomial

namespace RHTower

noncomputable section






/-- Left hard-edge Chebyshev channel for the even Li family. -/
def liEvenCrossLeftPolynomial (n : ℕ) : Polynomial ℝ :=
  Polynomial.Chebyshev.U ℝ (n : ℤ)

/-- Right channel: the hard-edge distance weight times the same Chebyshev mode. -/
def liEvenCrossRightPolynomial (n : ℕ) : Polynomial ℝ :=
  (1 - X) * liEvenCrossLeftPolynomial n

/-- Reciprocal-coordinate cross polynomial whose moment value is one even Li source. -/
def liEvenCrossMomentPolynomial (n : ℕ) : Polynomial ℝ :=
  2 * xiHardEdgeReciprocalPolynomial (1 / 2) (liEvenCrossLeftPolynomial n) *
    xiHardEdgeReciprocalPolynomial (1 / 2) (liEvenCrossRightPolynomial n)

/-- The shifted reciprocal Hankel bilinear form is the moment inner product of its coefficient polynomials. -/
theorem xiShiftedReciprocalHankelBilinear_eq_momentInner_ofFn
    (y : ℝ) {N : ℕ} (c e : Fin N → ℝ) :
    xiShiftedReciprocalHankelBilinear y c e =
      HTGeometry.momentInner
        (fun k => (xiShiftedReciprocalMoment y k).re)
        (Polynomial.ofFn N c) (Polynomial.ofFn N e) := by
  rw [HTGeometry.momentInner_ofFn_ofFn]
  simp only [xiShiftedReciprocalHankelBilinear, dotProduct, mulVec,
    HTGeometry.momentHankelMatrix, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Exact hard-edge factorization before coefficient extension. -/
theorem two_mul_X_mul_liEvenCrossPullbacks (n : ℕ) :
    (2 : Polynomial ℝ) * X *
        xiHardEdgeReciprocalPolynomial (1 / 2) (liEvenCrossLeftPolynomial n) *
        xiHardEdgeReciprocalPolynomial (1 / 2) (liEvenCrossRightPolynomial n) =
      X * (C 4 - X) *
        ((Polynomial.Chebyshev.U ℝ (n : ℤ)).comp
          (C 1 - C (1 / 2) * X)) ^ (2 : ℕ) := by
  apply Polynomial.funext
  intro u
  simp only [Polynomial.eval_ofNat, Polynomial.eval_X, Polynomial.eval_sub,
    Polynomial.eval_C, Polynomial.eval_comp, Polynomial.eval_mul,
    Polynomial.eval_pow, liEvenCrossLeftPolynomial,
    liEvenCrossRightPolynomial, xiHardEdgeReciprocalPolynomial]
  norm_num
  rw [show (1 / 2 : ℝ) * u - 1 = -(1 - (1 / 2 : ℝ) * u) by ring]
  rw [Polynomial.Chebyshev.U_eval_neg ℝ n (1 - (1 / 2 : ℝ) * u)]
  have hsign : (((n : ℤ).negOnePow : ℤ) : ℝ) ^ (2 : ℕ) = 1 := by
    have hsignInt : (n : ℤ).negOnePow * (n : ℤ).negOnePow = 1 := by
      rw [← Int.negOnePow_add]
      rw [show (n : ℤ) + (n : ℤ) = 2 * (n : ℤ) by ring,
        Int.negOnePow_two_mul]
    rw [pow_two, ← Int.cast_mul]
    simpa using congrArg (fun z : ℤ => (z : ℝ)) hsignInt
  linear_combination (norm := ring_nf)
    u * (4 - u) *
      (Polynomial.eval (1 - (1 / 2 : ℝ) * u)
        (Polynomial.Chebyshev.U ℝ (n : ℤ))) ^ (2 : ℕ) * hsign

/-- The real even-Li square equals `X` times the reciprocal cross polynomial. -/
theorem X_mul_liEvenCrossMomentPolynomial (n : ℕ) :
    X * liEvenCrossMomentPolynomial n =
      X * (C 4 - X) *
        ((Polynomial.Chebyshev.U ℝ (n : ℤ)).comp
          (C 1 - C (1 / 2) * X)) ^ (2 : ℕ) := by
  rw [liEvenCrossMomentPolynomial]
  simpa only [mul_assoc, mul_left_comm, mul_comm] using two_mul_X_mul_liEvenCrossPullbacks n

/-- Coefficient extension recovers the existing complex even-Li source polynomial. -/
theorem map_X_mul_liEvenCrossMomentPolynomial (n : ℕ) :
    (X * liEvenCrossMomentPolynomial n).map Complex.ofRealHom =
      liEvenShiftedSquarePolynomial n := by
  rw [X_mul_liEvenCrossMomentPolynomial]
  simp only [Polynomial.map_mul, Polynomial.map_X, Polynomial.map_sub,
    Polynomial.map_C, map_ofNat, Polynomial.map_pow, Polynomial.map_comp,
    Polynomial.Chebyshev.map_U, liEvenShiftedSquarePolynomial]
  norm_num

/-- Every positive even paired Li coefficient is the shifted moment value of the cross polynomial. -/
theorem re_xiLiPaired_two_mul_eq_momentFunctional_liEvenCross (n : ℕ) :
    (xiLiPaired (2 * (n + 1))).re =
      HTGeometry.momentFunctional
        (fun k => (xiShiftedReciprocalMoment (1 / 4) k).re)
        (liEvenCrossMomentPolynomial n) := by
  have hs : Summable (fun q : XiZeroCopy =>
      liTerm (xiRootW ((q.1 : XiDivisorSupport) : ℂ)) (2 * (n + 1))) :=
    (hasSum_liTerm_xiZeroCopy (2 * (n + 1))).summable
  rw [show xiLiPaired (2 * (n + 1)) =
      ∑' q : XiZeroCopy,
        liTerm (xiRootW ((q.1 : XiDivisorSupport) : ℂ)) (2 * (n + 1)) from
      (hasSum_liTerm_xiZeroCopy (2 * (n + 1))).tsum_eq.symm]
  rw [Complex.re_tsum hs]
  rw [momentFunctional_xiShifted_eq_polynomialAtomSum (by norm_num)
    (liEvenCrossMomentPolynomial n)]
  rw [xiShiftedPolynomialAtomSum]
  apply tsum_congr
  intro q
  rw [liTerm_xiRootW_eq_liShiftedMomentPolynomial,
    liShiftedMomentPolynomial_two_mul_eq_weighted_chebyshevU_square,
    ← map_X_mul_liEvenCrossMomentPolynomial]
  rw [Polynomial.eval_map]
  simp

/-- Exact LI-XP1 landing: the literal even Li source is twice the fixed reciprocal-Hankel cross term. -/
theorem re_liPrimeArchEvenSquareSource_eq_two_mul_crossBilinear (n : ℕ) :
    (liPrimeArchEvenSquareSource n).re =
      2 * xiShiftedReciprocalHankelBilinear (1 / 4)
        (routeUHardEdgeCommonLeftCoefficients (1 / 2)
          (liEvenCrossLeftPolynomial n) (liEvenCrossRightPolynomial n))
        (routeUHardEdgeCommonRightCoefficients (1 / 2)
          (liEvenCrossLeftPolynomial n) (liEvenCrossRightPolynomial n)) := by
  rw [← xiLiPaired_two_mul_eq_liPrimeArchEvenSquareSource,
    re_xiLiPaired_two_mul_eq_momentFunctional_liEvenCross, liEvenCrossMomentPolynomial]
  rw [xiShiftedReciprocalHankelBilinear_eq_momentInner_ofFn]
  rw [ofFn_routeUHardEdgeCommonLeftCoefficients,
    ofFn_routeUHardEdgeCommonRightCoefficients, HTGeometry.momentInner_def]
  rw [show (2 : Polynomial ℝ) = C 2 by rw [← C_ofNat], mul_assoc]
  rw [HTGeometry.momentFunctional_C_mul]

/-- Under RH, a pair with nonnegative product on the real squared spectrum has nonnegative polarized heat trace. -/
theorem xiPolynomialGaussianHeatTraceReal_cross_nonneg_of_rh
    (hRH : RiemannHypothesis) (P Q : Polynomial ℝ)
    {t : ℝ} (ht : 0 < t)
    (hPQ : ∀ x : ℝ, 0 ≤ P.eval (x ^ (2 : ℕ)) * Q.eval (x ^ (2 : ℕ))) :
    0 ≤ (xiPolynomialGaussianHeatTraceReal (P + Q) t -
      xiPolynomialGaussianHeatTraceReal (P - Q) t) / 4 := by
  have hsplus := summable_xiPolynomialGaussianHeatTerm ht (P + Q)
  have hsminus := summable_xiPolynomialGaussianHeatTerm ht (P - Q)
  have hrplus : Summable (fun q : XiZeroCopy =>
      (xiPolynomialGaussianHeatTerm (P + Q) t q).re) := by
    convert hsplus.map Complex.reCLM Complex.reCLM.continuous using 1
    ext q
    rfl
  have hrminus : Summable (fun q : XiZeroCopy =>
      (xiPolynomialGaussianHeatTerm (P - Q) t q).re) := by
    convert hsminus.map Complex.reCLM Complex.reCLM.continuous using 1
    ext q
    rfl
  rw [xiPolynomialGaussianHeatTraceReal, xiPolynomialGaussianHeatTrace,
    Complex.re_tsum hsplus, xiPolynomialGaussianHeatTraceReal,
    xiPolynomialGaussianHeatTrace, Complex.re_tsum hsminus]
  rw [← Summable.tsum_sub hrplus hrminus, ← tsum_div_const]
  apply tsum_nonneg
  intro q
  obtain ⟨x, hcoord⟩ := xiSpectralPoint_real_of_rh hRH q
  rw [xiPolynomialGaussianHeatTerm, xiPolynomialGaussianHeatTerm,
    xiGaussianHeatTerm, hcoord]
  have hsq : (x : ℂ) ^ (2 : ℕ) = ((x ^ (2 : ℕ) : ℝ) : ℂ) := by push_cast; rfl
  rw [hsq, evalRealPolynomial_ofReal, evalRealPolynomial_ofReal]
  have hexpC : Complex.exp (-(t : ℂ) * ((x ^ (2 : ℕ) : ℝ) : ℂ)) =
      ((Real.exp (-(t * x ^ (2 : ℕ))) : ℝ) : ℂ) := by
    rw [show -(t : ℂ) * ((x ^ (2 : ℕ) : ℝ) : ℂ) =
      ((-(t * x ^ (2 : ℕ)) : ℝ) : ℂ) by push_cast; ring]
    exact (Complex.ofReal_exp _).symm
  rw [hexpC]
  simp only [Polynomial.eval_add, Polynomial.eval_sub, pow_two,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, add_zero]
  have hprod : 0 ≤ P.eval (x * x) * Q.eval (x * x) := by
    simpa only [pow_two] using hPQ x
  have hexp : 0 ≤ Real.exp (-(t * (x * x))) := Real.exp_nonneg _
  nlinarith [mul_nonneg hprod hexp]

/-- RH makes every fixed Chebyshev completed prime--Gamma cross balance nonnegative pointwise in heat time. -/
theorem liEvenPrimeGammaCrossBalance_nonneg_of_rh
    (hRH : RiemannHypothesis) (n : ℕ)
    (t : {τ : ℝ // 0 < τ}) :
    0 ≤ routeUShiftedCompletedPrimeGammaCrossBalance (1 / 4)
      (routeUHardEdgeCommonLiftDegree (1 / 2)
        (liEvenCrossLeftPolynomial n) (liEvenCrossRightPolynomial n))
      (routeUHardEdgeCommonLeftCoefficients (1 / 2)
        (liEvenCrossLeftPolynomial n) (liEvenCrossRightPolynomial n))
      (routeUHardEdgeCommonRightCoefficients (1 / 2)
        (liEvenCrossLeftPolynomial n) (liEvenCrossRightPolynomial n)) t := by
  let P := liEvenCrossLeftPolynomial n
  let Q := liEvenCrossRightPolynomial n
  let d := routeUHardEdgeCommonLiftDegree (1 / 2) P Q
  let c := routeUHardEdgeCommonLeftCoefficients (1 / 2) P Q
  let e := routeUHardEdgeCommonRightCoefficients (1 / 2) P Q
  let L := routeUHardEdgeCommonLeftReversedPolynomial (1 / 2) P Q
  let R := routeUHardEdgeCommonRightReversedPolynomial (1 / 2) P Q
  have hLR : ∀ x : ℝ, 0 ≤ L.eval (x ^ (2 : ℕ)) * R.eval (x ^ (2 : ℕ)) := by
    intro x
    have hden : 0 < (1 / 2 : ℝ) ^ (2 : ℕ) + x ^ (2 : ℕ) := by positivity
    have hcoord : 0 ≤ 1 -
        (((1 / 2 : ℝ) ^ (2 : ℕ) - x ^ (2 : ℕ)) / ((1 / 2 : ℝ) ^ (2 : ℕ) + x ^ (2 : ℕ))) := by
      rw [show 1 -
          (((1 / 2 : ℝ) ^ (2 : ℕ) - x ^ (2 : ℕ)) / ((1 / 2 : ℝ) ^ (2 : ℕ) + x ^ (2 : ℕ))) =
        2 * x ^ (2 : ℕ) / ((1 / 2 : ℝ) ^ (2 : ℕ) + x ^ (2 : ℕ)) by
          field_simp [hden.ne']; ring]
      positivity
    rw [show L.eval (x ^ (2 : ℕ)) =
        ((1 / 2 : ℝ) ^ (2 : ℕ) + x ^ (2 : ℕ)) ^ d *
          P.eval (((1 / 2 : ℝ) ^ (2 : ℕ) - x ^ (2 : ℕ)) /
            ((1 / 2 : ℝ) ^ (2 : ℕ) + x ^ (2 : ℕ))) by
          simpa only [L, d] using
            eval_routeUHardEdgeCommonLeftReversedPolynomial
              (1 / 2) P Q hden.ne',
      show R.eval (x ^ (2 : ℕ)) =
        ((1 / 2 : ℝ) ^ (2 : ℕ) + x ^ (2 : ℕ)) ^ d *
          Q.eval (((1 / 2 : ℝ) ^ (2 : ℕ) - x ^ (2 : ℕ)) /
            ((1 / 2 : ℝ) ^ (2 : ℕ) + x ^ (2 : ℕ))) by
          simpa only [R, d] using
            eval_routeUHardEdgeCommonRightReversedPolynomial
              (1 / 2) P Q hden.ne']
    simp only [Q, liEvenCrossRightPolynomial, Polynomial.eval_mul,
      Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_X]
    have hnon : 0 ≤
        (((1 / 2 : ℝ) ^ (2 : ℕ) + x ^ (2 : ℕ)) ^ d) ^ (2 : ℕ) *
          (1 - (((1 / 2 : ℝ) ^ (2 : ℕ) - x ^ (2 : ℕ)) /
            ((1 / 2 : ℝ) ^ (2 : ℕ) + x ^ (2 : ℕ)))) *
          (P.eval (((1 / 2 : ℝ) ^ (2 : ℕ) - x ^ (2 : ℕ)) /
            ((1 / 2 : ℝ) ^ (2 : ℕ) + x ^ (2 : ℕ)))) ^ (2 : ℕ) :=
      mul_nonneg (mul_nonneg (sq_nonneg _) hcoord) (sq_nonneg _)
    convert hnon using 1
    ring
  have htrace := xiPolynomialGaussianHeatTraceReal_cross_nonneg_of_rh hRH L R t.2 hLR
  rw [routeUShiftedCompletedPrimeGammaCrossBalance,
    routeUShiftedCompletedPrimeGammaBalance_eq_pi_mul_trace,
    routeUShiftedCompletedPrimeGammaBalance_eq_pi_mul_trace]
  have hadd : xiShiftedReversedPolynomial (1 / 4) d (c + e) = L + R := by
    norm_num [L, R, c, e, d, routeUHardEdgeCommonLeftReversedPolynomial,
      routeUHardEdgeCommonRightReversedPolynomial]
    exact xiShiftedReversedPolynomial_add (1 / 4) d c e
  have hsub : xiShiftedReversedPolynomial (1 / 4) d (c - e) = L - R := by
    norm_num [L, R, c, e, d, routeUHardEdgeCommonLeftReversedPolynomial,
      routeUHardEdgeCommonRightReversedPolynomial]
    exact xiShiftedReversedPolynomial_sub (1 / 4) d c e
  change 0 ≤
    (Real.pi * xiPolynomialGaussianHeatTraceReal
        (xiShiftedReversedPolynomial (1 / 4) d (c + e)) t.1 -
      Real.pi * xiPolynomialGaussianHeatTraceReal
        (xiShiftedReversedPolynomial (1 / 4) d (c - e)) t.1) / 4
  rw [hadd, hsub]
  nlinarith [Real.pi_pos]

/-- Source-only pointwise positivity of the fixed completed prime--Gamma cross family. -/
def LiEvenPrimeGammaCrossBalanceNonnegative : Prop :=
  ∀ (n : ℕ) (t : {τ : ℝ // 0 < τ}),
    0 ≤ routeUShiftedCompletedPrimeGammaCrossBalance (1 / 4)
      (routeUHardEdgeCommonLiftDegree (1 / 2)
        (liEvenCrossLeftPolynomial n) (liEvenCrossRightPolynomial n))
      (routeUHardEdgeCommonLeftCoefficients (1 / 2)
        (liEvenCrossLeftPolynomial n) (liEvenCrossRightPolynomial n))
      (routeUHardEdgeCommonRightCoefficients (1 / 2)
        (liEvenCrossLeftPolynomial n) (liEvenCrossRightPolynomial n)) t

/-- LI-XP1: RH is exactly pointwise nonnegativity of the fixed Chebyshev prime--Gamma cross balances. -/
theorem riemannHypothesis_iff_liEvenPrimeGammaCrossBalanceNonnegative :
    RiemannHypothesis ↔ LiEvenPrimeGammaCrossBalanceNonnegative := by
  constructor
  · intro hRH n t
    exact liEvenPrimeGammaCrossBalance_nonneg_of_rh hRH n t
  · intro hcross
    rw [riemannHypothesis_iff_forall_re_liPrimeArchEvenSquareSource_nonneg]
    intro n
    let P := liEvenCrossLeftPolynomial n
    let Q := liEvenCrossRightPolynomial n
    let d := routeUHardEdgeCommonLiftDegree (1 / 2) P Q
    let c := routeUHardEdgeCommonLeftCoefficients (1 / 2) P Q
    let e := routeUHardEdgeCommonRightCoefficients (1 / 2) P Q
    have hcap : 0 ≤
        routeUShiftedFilteredCompletedSourceCrossCapital (1 / 4) d c e := by
      by_contra hneg
      push Not at hneg
      obtain ⟨t, ht⟩ :=
        exists_routeUShiftedCompletedPrimeGammaCrossBalance_neg_of_crossCapital_neg
          (1 / 4) d c e hneg
      exact (not_lt_of_ge (hcross n t)) ht
    rw [routeUShiftedFilteredCompletedSourceCrossCapital_eq
      (by norm_num : (0 : ℝ) < 1 / 4)] at hcap
    have hfactor : 0 < Real.pi * ((2 * d).factorial : ℝ) := by positivity
    have hbil : 0 ≤ xiShiftedReciprocalHankelBilinear (1 / 4) c e := by
      nlinarith
    rw [re_liPrimeArchEvenSquareSource_eq_two_mul_crossBilinear]
    exact mul_nonneg (by norm_num) (by simpa only [P, Q, c, e] using hbil)

/-- A positive-time polynomial Xi heat trace is exactly its Gaussian moment square. -/
theorem xiPolynomialGaussianHeatTraceReal_eq_momentFunctional_sq
    (P : Polynomial ℝ) {t : ℝ} (ht : 0 < t) :
    xiPolynomialGaussianHeatTraceReal P t =
      HTGeometry.momentFunctional (fun k ↦ xiGaussianHeatMomentReal k t) (P ^ (2 : ℕ)) := by
  let N := P.natDegree + 1
  let c : Fin N → ℝ := fun i ↦ P.coeff i
  have hof : Polynomial.ofFn N c = P := by
    dsimp only [N, c]
    exact Polynomial.ofFn_comp_toFn_eq_id_of_natDegree_lt (Nat.lt_succ_self _)
  calc
    xiPolynomialGaussianHeatTraceReal P t = xiHeatHankelForm N P.coeff t := by
      rw [← xiPolynomialGaussianHeatTraceReal_rangeSum ht N P.coeff]
      congr 1
      exact routeUPolynomial_eq_coeff_rangeSum P
    _ = HTGeometry.momentFunctional
          (fun k ↦ xiGaussianHeatMomentReal k t) ((Polynomial.ofFn N c) ^ (2 : ℕ)) := by
      rw [← HTGeometry.dotProduct_mulVec_momentHankelMatrix]
      simp only [xiHeatHankelForm, dotProduct, mulVec,
        HTGeometry.momentHankelMatrix, c, Finset.mul_sum]
      rw [← Fin.sum_univ_eq_sum_range
        (fun j : ℕ ↦ ∑ k ∈ Finset.range N,
          P.coeff j * P.coeff k * xiGaussianHeatMomentReal (j + k) t) N]
      apply Finset.sum_congr rfl
      intro j _
      rw [← Fin.sum_univ_eq_sum_range
        (fun k : ℕ ↦ P.coeff j * P.coeff k *
          xiGaussianHeatMomentReal (j + k) t) N]
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ = HTGeometry.momentFunctional
          (fun k ↦ xiGaussianHeatMomentReal k t) (P ^ (2 : ℕ)) := by rw [hof]

/-- Polarized real polynomial Xi heat trace. -/
def xiPolynomialGaussianHeatCrossTraceReal
    (P Q : Polynomial ℝ) (t : ℝ) : ℝ :=
  (xiPolynomialGaussianHeatTraceReal (P + Q) t -
    xiPolynomialGaussianHeatTraceReal (P - Q) t) / 4

/-- Polarization lands exactly on the Gaussian moment functional of the polynomial product. -/
theorem xiPolynomialGaussianHeatCrossTraceReal_eq_momentFunctional_mul
    (P Q : Polynomial ℝ) {t : ℝ} (ht : 0 < t) :
    xiPolynomialGaussianHeatCrossTraceReal P Q t =
      HTGeometry.momentFunctional (fun k ↦ xiGaussianHeatMomentReal k t) (P * Q) := by
  rw [xiPolynomialGaussianHeatCrossTraceReal,
    xiPolynomialGaussianHeatTraceReal_eq_momentFunctional_sq _ ht,
    xiPolynomialGaussianHeatTraceReal_eq_momentFunctional_sq _ ht]
  rw [← HTGeometry.momentFunctional_sub]
  rw [show (P + Q) ^ (2 : ℕ) - (P - Q) ^ (2 : ℕ) = C 4 * (P * Q) by
    change (P + Q) ^ (2 : ℕ) - (P - Q) ^ (2 : ℕ) = (4 : Polynomial ℝ) * (P * Q)
    ring]
  rw [HTGeometry.momentFunctional_C_mul]
  ring

/-- Real part of the unconditional Xi Gaussian moment derivative ladder. -/
theorem hasDerivAt_xiGaussianHeatMomentReal {t : ℝ} (ht : 0 < t) (n : ℕ) :
    HasDerivAt (fun s : ℝ ↦ xiGaussianHeatMomentReal n s)
      (-xiGaussianHeatMomentReal (n + 1) t) t := by
  have hc : HasDerivAt (fun _ : ℝ ↦ Complex.reCLM)
      (0 : ℂ →L[ℝ] ℝ) t := hasDerivAt_const t Complex.reCLM
  have h := hc.clm_apply (hasDerivAt_xiGaussianHeatMoment ht n)
  simpa [xiGaussianHeatMomentReal] using h

/-- Any fixed polynomial Gaussian moment functional differentiates by multiplication by `-X`. -/
theorem hasDerivAt_xiGaussianMomentFunctional
    (A : Polynomial ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt
      (fun s : ℝ ↦ HTGeometry.momentFunctional
        (fun k ↦ xiGaussianHeatMomentReal k s) A)
      (-HTGeometry.momentFunctional
        (fun k ↦ xiGaussianHeatMomentReal k t) (X * A)) t := by
  induction A using Polynomial.induction_on' with
  | add P Q hP hQ =>
      rw [show
        (fun s : ℝ ↦ HTGeometry.momentFunctional
          (fun k ↦ xiGaussianHeatMomentReal k s) (P + Q)) =
          (fun s : ℝ ↦ HTGeometry.momentFunctional
            (fun k ↦ xiGaussianHeatMomentReal k s) P) +
          (fun s : ℝ ↦ HTGeometry.momentFunctional
            (fun k ↦ xiGaussianHeatMomentReal k s) Q) by
        funext s
        rw [Pi.add_apply, HTGeometry.momentFunctional_add]]
      rw [mul_add, HTGeometry.momentFunctional_add]
      simpa only [Pi.add_apply, neg_add_rev, add_comm] using hP.add hQ
  | monomial n a =>
      have h := (hasDerivAt_xiGaussianHeatMomentReal ht n).const_mul a
      rw [show
        (fun s : ℝ ↦ HTGeometry.momentFunctional
          (fun k ↦ xiGaussianHeatMomentReal k s) (monomial n a)) =
          fun s : ℝ ↦ a * xiGaussianHeatMomentReal n s by
        funext s
        rw [HTGeometry.momentFunctional_monomial]]
      rw [Polynomial.X_mul_monomial, HTGeometry.momentFunctional_monomial]
      simpa only [mul_neg] using h

/-! ## LI-XP2: the Stieltjes-localized common reversal -/

/-- Exact degree of the left Chebyshev channel. -/
theorem natDegree_liEvenCrossLeftPolynomial (n : ℕ) :
    (liEvenCrossLeftPolynomial n).natDegree = n := by
  rw [liEvenCrossLeftPolynomial, Polynomial.Chebyshev.natDegree_U]
  omega

/-- The distance-weighted right channel raises the degree by exactly one. -/
theorem natDegree_liEvenCrossRightPolynomial (n : ℕ) :
    (liEvenCrossRightPolynomial n).natDegree = n + 1 := by
  have hdeg : (1 - X : Polynomial ℝ).natDegree = 1 := by
    rw [show (1 - X : Polynomial ℝ) = C (-1) * X + C 1 by
      norm_num; ring]
    rw [Polynomial.natDegree_linear (by norm_num : (-1 : ℝ) ≠ 0)]
  rw [liEvenCrossRightPolynomial, Polynomial.natDegree_mul, hdeg,
    natDegree_liEvenCrossLeftPolynomial]
  · omega
  · intro h
    have := congrArg Polynomial.natDegree h
    rw [hdeg] at this
    simp at this
  · simpa only [liEvenCrossLeftPolynomial] using
      Polynomial.Chebyshev.U_ne_zero ℝ (n : ℤ) (by omega)

/-- At quarter shift the reciprocal affine pullback preserves every polynomial degree. -/
theorem natDegree_xiHardEdgeReciprocalPolynomial_half (S : Polynomial ℝ) :
    (xiHardEdgeReciprocalPolynomial (1 / 2) S).natDegree = S.natDegree := by
  rw [xiHardEdgeReciprocalPolynomial, Polynomial.natDegree_comp]
  norm_num [Polynomial.natDegree_sub_eq_left_of_natDegree_lt]

/-- The common reversal degree of the LI pair is exactly `n+1`. -/
theorem liEvenCross_commonLiftDegree (n : ℕ) :
    routeUHardEdgeCommonLiftDegree (1 / 2)
        (liEvenCrossLeftPolynomial n) (liEvenCrossRightPolynomial n) = n + 1 := by
  rw [routeUHardEdgeCommonLiftDegree,
    natDegree_xiHardEdgeReciprocalPolynomial_half,
    natDegree_xiHardEdgeReciprocalPolynomial_half,
    natDegree_liEvenCrossLeftPolynomial, natDegree_liEvenCrossRightPolynomial]
  omega

/-- The common unweighted base left after reversal at its intrinsic degree. -/
def liEvenCrossBaseReversedPolynomial (n : ℕ) : Polynomial ℝ :=
  routeUHardEdgeDegreePaddedReversedPolynomial
    (1 / 2) n (liEvenCrossLeftPolynomial n)

/-- The common-degree left reversal has exactly one `(X+1/4)` factor. -/
theorem liEvenCross_leftReversedPolynomial_factor (n : ℕ) :
    routeUHardEdgeCommonLeftReversedPolynomial (1 / 2)
        (liEvenCrossLeftPolynomial n) (liEvenCrossRightPolynomial n) =
      (C (1 / 4) + X) * liEvenCrossBaseReversedPolynomial n := by
  apply Polynomial.eq_of_infinite_eval_eq
  apply (Set.Ioi_infinite (0 : ℝ)).mono
  intro W hW
  simp only [Set.mem_setOf_eq, Set.mem_Ioi] at hW ⊢
  have hden : (1 / 2 : ℝ) ^ (2 : ℕ) + W ≠ 0 := by positivity
  rw [eval_routeUHardEdgeCommonLeftReversedPolynomial _ _ _ hden,
    liEvenCross_commonLiftDegree, Polynomial.eval_mul,
    liEvenCrossBaseReversedPolynomial,
    eval_routeUHardEdgeDegreePaddedReversedPolynomial]
  · simp only [Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_X]
    norm_num
    ring
  · rw [natDegree_xiHardEdgeReciprocalPolynomial_half,
      natDegree_liEvenCrossLeftPolynomial]
  · exact hden

/-- The common-degree right reversal has exactly the complementary `2X` factor. -/
theorem liEvenCross_rightReversedPolynomial_factor (n : ℕ) :
    routeUHardEdgeCommonRightReversedPolynomial (1 / 2)
        (liEvenCrossLeftPolynomial n) (liEvenCrossRightPolynomial n) =
      2 * X * liEvenCrossBaseReversedPolynomial n := by
  apply Polynomial.eq_of_infinite_eval_eq
  apply (Set.Ioi_infinite (0 : ℝ)).mono
  intro W hW
  simp only [Set.mem_setOf_eq, Set.mem_Ioi] at hW ⊢
  have hden : (1 / 2 : ℝ) ^ (2 : ℕ) + W ≠ 0 := by positivity
  rw [eval_routeUHardEdgeCommonRightReversedPolynomial _ _ _ hden,
    liEvenCross_commonLiftDegree, liEvenCrossRightPolynomial,
    Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_one,
    Polynomial.eval_X, Polynomial.eval_mul,
    liEvenCrossBaseReversedPolynomial,
    eval_routeUHardEdgeDegreePaddedReversedPolynomial]
  · norm_num
    field_simp [hden]
    ring
  · rw [natDegree_xiHardEdgeReciprocalPolynomial_half,
      natDegree_liEvenCrossLeftPolynomial]
  · exact hden

/-- Completed Gaussian moment of the exact Stieltjes-localized LI-XP2 square. -/
def liEvenStieltjesLocalizedHeatSource (n : ℕ) (t : ℝ) : ℝ :=
  HTGeometry.momentFunctional (fun k ↦ xiGaussianHeatMomentReal k t)
    (X * (C (1 / 4) + X) * (liEvenCrossBaseReversedPolynomial n) ^ (2 : ℕ))

/-- Unlocalized base-square heat energy whose first two derivatives generate the LI-XP2 source. -/
def liEvenBaseHeatEnergy (n : ℕ) (t : ℝ) : ℝ :=
  HTGeometry.momentFunctional (fun k ↦ xiGaussianHeatMomentReal k t)
    ((liEvenCrossBaseReversedPolynomial n) ^ (2 : ℕ))

/-- First heat derivative of the base square is the negative once-shifted square moment. -/
theorem hasDerivAt_liEvenBaseHeatEnergy (n : ℕ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (liEvenBaseHeatEnergy n)
      (-HTGeometry.momentFunctional (fun k ↦ xiGaussianHeatMomentReal k t)
        (X * (liEvenCrossBaseReversedPolynomial n) ^ (2 : ℕ))) t := by
  change HasDerivAt
    (fun s : ℝ ↦ HTGeometry.momentFunctional
      (fun k ↦ xiGaussianHeatMomentReal k s)
      ((liEvenCrossBaseReversedPolynomial n) ^ (2 : ℕ)))
    (-HTGeometry.momentFunctional (fun k ↦ xiGaussianHeatMomentReal k t)
      (X * (liEvenCrossBaseReversedPolynomial n) ^ (2 : ℕ))) t
  exact hasDerivAt_xiGaussianMomentFunctional
    ((liEvenCrossBaseReversedPolynomial n) ^ (2 : ℕ)) ht

/-- Pointwise first-derivative form of the LI-XP2 base energy. -/
theorem deriv_liEvenBaseHeatEnergy (n : ℕ) {t : ℝ} (ht : 0 < t) :
    deriv (liEvenBaseHeatEnergy n) t =
      -HTGeometry.momentFunctional (fun k ↦ xiGaussianHeatMomentReal k t)
        (X * (liEvenCrossBaseReversedPolynomial n) ^ (2 : ℕ)) :=
  (hasDerivAt_liEvenBaseHeatEnergy n ht).deriv

/-- The second derivative is the twice-shifted square moment, unconditionally on positive time. -/
theorem secondDeriv_liEvenBaseHeatEnergy (n : ℕ) {t : ℝ} (ht : 0 < t) :
    deriv (fun s : ℝ ↦ deriv (liEvenBaseHeatEnergy n) s) t =
      HTGeometry.momentFunctional (fun k ↦ xiGaussianHeatMomentReal k t)
        (X ^ (2 : ℕ) * (liEvenCrossBaseReversedPolynomial n) ^ (2 : ℕ)) := by
  have hev :
      (fun s : ℝ ↦ deriv (liEvenBaseHeatEnergy n) s) =ᶠ[nhds t]
        fun s : ℝ ↦ -HTGeometry.momentFunctional
          (fun k ↦ xiGaussianHeatMomentReal k s)
          (X * (liEvenCrossBaseReversedPolynomial n) ^ (2 : ℕ)) := by
    filter_upwards [eventually_gt_nhds ht] with s hs
    exact deriv_liEvenBaseHeatEnergy n hs
  rw [hev.deriv_eq]
  have hneg := (hasDerivAt_xiGaussianMomentFunctional
    (X * (liEvenCrossBaseReversedPolynomial n) ^ (2 : ℕ)) ht).neg
  have hderiv :
      deriv (fun s : ℝ ↦ -HTGeometry.momentFunctional
        (fun k ↦ xiGaussianHeatMomentReal k s)
        (X * (liEvenCrossBaseReversedPolynomial n) ^ (2 : ℕ))) t =
        -(-HTGeometry.momentFunctional
          (fun k ↦ xiGaussianHeatMomentReal k t)
          (X * (X * (liEvenCrossBaseReversedPolynomial n) ^ (2 : ℕ)))) := by
    rw [show
      (fun s : ℝ ↦ -HTGeometry.momentFunctional
        (fun k ↦ xiGaussianHeatMomentReal k s)
        (X * (liEvenCrossBaseReversedPolynomial n) ^ (2 : ℕ))) =
      -(fun s : ℝ ↦ HTGeometry.momentFunctional
        (fun k ↦ xiGaussianHeatMomentReal k s)
        (X * (liEvenCrossBaseReversedPolynomial n) ^ (2 : ℕ))) by
        funext s
        rfl]
    exact hneg.deriv
  rw [hderiv]
  rw [neg_neg]
  congr 1
  ring

/-- Exact differential form of the localized source:
`Lₜ(X(X+1/4)Bₙ²) = Fₙ''(t) - (1/4)Fₙ'(t)`. -/
theorem liEvenStieltjesLocalizedHeatSource_eq_secondDeriv_sub_quarter_deriv
    (n : ℕ) {t : ℝ} (ht : 0 < t) :
    liEvenStieltjesLocalizedHeatSource n t =
      deriv (fun s : ℝ ↦ deriv (liEvenBaseHeatEnergy n) s) t -
        (1 / 4 : ℝ) * deriv (liEvenBaseHeatEnergy n) t := by
  rw [secondDeriv_liEvenBaseHeatEnergy n ht,
    deriv_liEvenBaseHeatEnergy n ht, liEvenStieltjesLocalizedHeatSource]
  rw [show
      X * (C (1 / 4) + X) * (liEvenCrossBaseReversedPolynomial n) ^ (2 : ℕ) =
        X ^ (2 : ℕ) * (liEvenCrossBaseReversedPolynomial n) ^ (2 : ℕ) +
          (1 / 4 : ℝ) •
            (X * (liEvenCrossBaseReversedPolynomial n) ^ (2 : ℕ)) by
      rw [Polynomial.smul_eq_C_mul]
      ring]
  rw [HTGeometry.momentFunctional_add, HTGeometry.momentFunctional_smul]
  ring

/-- LI-XP2 exact landing: the fixed completed cross balance is `2π` times one
Stieltjes-localized square moment. -/
theorem liEvenPrimeGammaCrossBalance_eq_two_pi_mul_localizedHeatSource
    (n : ℕ) (t : {τ : ℝ // 0 < τ}) :
    routeUShiftedCompletedPrimeGammaCrossBalance (1 / 4)
        (routeUHardEdgeCommonLiftDegree (1 / 2)
          (liEvenCrossLeftPolynomial n) (liEvenCrossRightPolynomial n))
        (routeUHardEdgeCommonLeftCoefficients (1 / 2)
          (liEvenCrossLeftPolynomial n) (liEvenCrossRightPolynomial n))
        (routeUHardEdgeCommonRightCoefficients (1 / 2)
          (liEvenCrossLeftPolynomial n) (liEvenCrossRightPolynomial n)) t =
      2 * Real.pi * liEvenStieltjesLocalizedHeatSource n t.1 := by
  let P := liEvenCrossLeftPolynomial n
  let Q := liEvenCrossRightPolynomial n
  let d := routeUHardEdgeCommonLiftDegree (1 / 2) P Q
  let c := routeUHardEdgeCommonLeftCoefficients (1 / 2) P Q
  let e := routeUHardEdgeCommonRightCoefficients (1 / 2) P Q
  let L := routeUHardEdgeCommonLeftReversedPolynomial (1 / 2) P Q
  let R := routeUHardEdgeCommonRightReversedPolynomial (1 / 2) P Q
  have hadd : xiShiftedReversedPolynomial (1 / 4) d (c + e) = L + R := by
    norm_num [L, R, c, e, d, routeUHardEdgeCommonLeftReversedPolynomial,
      routeUHardEdgeCommonRightReversedPolynomial]
    exact xiShiftedReversedPolynomial_add (1 / 4) d c e
  have hsub : xiShiftedReversedPolynomial (1 / 4) d (c - e) = L - R := by
    norm_num [L, R, c, e, d, routeUHardEdgeCommonLeftReversedPolynomial,
      routeUHardEdgeCommonRightReversedPolynomial]
    exact xiShiftedReversedPolynomial_sub (1 / 4) d c e
  rw [routeUShiftedCompletedPrimeGammaCrossBalance,
    routeUShiftedCompletedPrimeGammaBalance_eq_pi_mul_trace,
    routeUShiftedCompletedPrimeGammaBalance_eq_pi_mul_trace]
  change
    (Real.pi * xiPolynomialGaussianHeatTraceReal
        (xiShiftedReversedPolynomial (1 / 4) d (c + e)) t.1 -
      Real.pi * xiPolynomialGaussianHeatTraceReal
        (xiShiftedReversedPolynomial (1 / 4) d (c - e)) t.1) / 4 =
      2 * Real.pi * liEvenStieltjesLocalizedHeatSource n t.1
  rw [hadd, hsub]
  rw [show
      (Real.pi * xiPolynomialGaussianHeatTraceReal (L + R) t.1 -
        Real.pi * xiPolynomialGaussianHeatTraceReal (L - R) t.1) / 4 =
        Real.pi * xiPolynomialGaussianHeatCrossTraceReal L R t.1 by
      rw [xiPolynomialGaussianHeatCrossTraceReal]
      ring]
  rw [xiPolynomialGaussianHeatCrossTraceReal_eq_momentFunctional_mul L R t.2]
  rw [show L = (C (1 / 4) + X) * liEvenCrossBaseReversedPolynomial n by
      simpa only [L, P, Q] using liEvenCross_leftReversedPolynomial_factor n,
    show R = 2 * X * liEvenCrossBaseReversedPolynomial n by
      simpa only [R, P, Q] using liEvenCross_rightReversedPolynomial_factor n]
  rw [show
      ((C (1 / 4) + X) * liEvenCrossBaseReversedPolynomial n) *
          (2 * X * liEvenCrossBaseReversedPolynomial n) =
        C 2 * (X * (C (1 / 4) + X) *
          (liEvenCrossBaseReversedPolynomial n) ^ (2 : ℕ)) by
      change
        ((C (1 / 4) + X) * liEvenCrossBaseReversedPolynomial n) *
            ((2 : Polynomial ℝ) * X * liEvenCrossBaseReversedPolynomial n) =
          (2 : Polynomial ℝ) * (X * (C (1 / 4) + X) *
            (liEvenCrossBaseReversedPolynomial n) ^ (2 : ℕ))
      ring]
  rw [HTGeometry.momentFunctional_C_mul, liEvenStieltjesLocalizedHeatSource]
  ring

/-- Source-only positivity of every LI-XP2 Stieltjes-localized square moment. -/
def LiEvenStieltjesLocalizedHeatSourceNonnegative : Prop :=
  ∀ (n : ℕ) (t : {τ : ℝ // 0 < τ}),
    0 ≤ liEvenStieltjesLocalizedHeatSource n t.1

/-- LI-XP2: RH is exactly positivity of the completed moment functional on the explicit
localized family `X (X+1/4) Bₙ²`. -/
theorem riemannHypothesis_iff_liEvenStieltjesLocalizedHeatSourceNonnegative :
    RiemannHypothesis ↔ LiEvenStieltjesLocalizedHeatSourceNonnegative := by
  rw [riemannHypothesis_iff_liEvenPrimeGammaCrossBalanceNonnegative]
  constructor
  · intro hcross n t
    have h := hcross n t
    rw [liEvenPrimeGammaCrossBalance_eq_two_pi_mul_localizedHeatSource] at h
    nlinarith [Real.pi_pos]
  · intro hsource n t
    rw [liEvenPrimeGammaCrossBalance_eq_two_pi_mul_localizedHeatSource]
    exact mul_nonneg (mul_nonneg (by norm_num) Real.pi_nonneg) (hsource n t)

/-- Differential producer exposed by LI-XP2: every base square satisfies
`Fₙ'' - (1/4)Fₙ' ≥ 0` throughout positive heat time. -/
def LiEvenBaseHeatDifferentialNonnegative : Prop :=
  ∀ (n : ℕ) (t : {τ : ℝ // 0 < τ}),
    0 ≤ deriv (fun s : ℝ ↦ deriv (liEvenBaseHeatEnergy n) s) t.1 -
      (1 / 4 : ℝ) * deriv (liEvenBaseHeatEnergy n) t.1

/-- LI-XP2 differential criterion: RH is exactly the explicit family
`Fₙ'' - (1/4)Fₙ' ≥ 0`; no auxiliary positivity premise remains. -/
theorem riemannHypothesis_iff_liEvenBaseHeatDifferentialNonnegative :
    RiemannHypothesis ↔ LiEvenBaseHeatDifferentialNonnegative := by
  rw [riemannHypothesis_iff_liEvenStieltjesLocalizedHeatSourceNonnegative]
  constructor
  · intro hsource n t
    rw [← liEvenStieltjesLocalizedHeatSource_eq_secondDeriv_sub_quarter_deriv n t.2]
    exact hsource n t
  · intro hdiff n t
    rw [liEvenStieltjesLocalizedHeatSource_eq_secondDeriv_sub_quarter_deriv n t.2]
    exact hdiff n t

end

end RHTower
