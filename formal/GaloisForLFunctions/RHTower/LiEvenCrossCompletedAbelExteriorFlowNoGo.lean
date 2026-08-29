import GaloisForLFunctions.RHTower.LiEvenCrossCompletedAbelMassFlow
import GaloisForLFunctions.RHTower.XiShiftedHankelFarRightPositiveDefinite
import GaloisForLFunctions.RHTower.XiShiftedCanonicalAdmissionAdaptiveArithmeticSourceFlow
import GaloisForLFunctions.HTGeometry.HorizonScalingSymmetry

/-!
# Exterior-flow no-go for the even Li completed-Abel current

LI-CAB4 leaves the sign of one adjacent Chebyshev current.  A tempting source-side route is to
start at the critical mass and propagate outward through the absolutely convergent
prime--Gamma window.  This module kills that route at every mode.

Writing `t = v * lambda_q(v)`, the atom is a fixed unit-interval defect `P_n(t)` and its velocity
is `lambda_q(v) * (1-t) * P_n'(t)`.  Thus the full current is exactly one moving polynomial
moment and, for `v=w^2`, one literal rational--Gamma-minus-von-Mangoldt source whenever
`w>1/2`.

The corpus far-right moment asymptotic turns the normalized current into the arcsine functional
of `(1-X)P_n'`.  An exact arcsine integration-by-parts identity makes this half the functional of
`P_n/X`; the latter is the nonzero weighted Chebyshev square

`2 * (1-X) * U_n(2X-1)^2`.

Consequently the exterior current is eventually strictly positive for every mode.  Hence the
nonpositive exterior-flow conjecture that would propagate a zero far-right anchor back to the
critical endpoint is impossible.  The surviving LI chain is the interior positive-current
problem on `0 < v <= 1/4` from LI-CAB5.
-/

open Polynomial Real Filter Topology Set MeasureTheory
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Unit-interval affine coordinate underlying the square-mass Cayley flow. -/
def liEvenCrossUnitAffine : Polynomial ℝ := 2 * X - 1

/-- Half-mode Chebyshev amplitude in the unit mass coordinate. -/
def liEvenCrossUnitAmplitude (n : ℕ) : Polynomial ℝ :=
  (Polynomial.Chebyshev.T ℝ ((n : ℤ) + 1)).comp liEvenCrossUnitAffine

/-- Fixed unit-coordinate form of one completed-Abel atom. -/
def liEvenCrossUnitDefect (n : ℕ) : Polynomial ℝ :=
  C (1 / 2) * (1 - liEvenCrossUnitAmplitude n ^ 2)

/-- Quotient current left after the summable reciprocal factor is removed. -/
def liEvenCrossUnitFluxQuotient (n : ℕ) : Polynomial ℝ :=
  (1 - X) * (liEvenCrossUnitDefect n).derivative

theorem two_mul_liEvenCrossUnitDefect (n : ℕ) :
    2 * liEvenCrossUnitDefect n = 1 - liEvenCrossUnitAmplitude n ^ 2 := by
  rw [liEvenCrossUnitDefect]
  change C 2 * (C (1 / 2) * (1 - liEvenCrossUnitAmplitude n ^ 2)) = _
  rw [← mul_assoc, ← C_mul]
  norm_num

theorem liEvenCrossUnitDefect_eq_weightedSquare (n : ℕ) :
    liEvenCrossUnitDefect n =
      2 * X * (1 - X) *
        ((Polynomial.Chebyshev.U ℝ (n : ℤ)).comp liEvenCrossUnitAffine) ^ 2 := by
  have h := congrArg (fun P : Polynomial ℝ => P.comp liEvenCrossUnitAffine)
    (chebyshevT_sq_add_one_sub_X_sq_mul_chebyshevU_sq_real n)
  simp only [add_comp, sub_comp, mul_comp, pow_comp, one_comp,
    Polynomial.X_comp] at h
  simp only [liEvenCrossUnitAffine] at h
  have htwo :
      2 * liEvenCrossUnitDefect n =
        2 * (2 * X * (1 - X) *
          ((Polynomial.Chebyshev.U ℝ (n : ℤ)).comp liEvenCrossUnitAffine) ^ 2) := by
    rw [two_mul_liEvenCrossUnitDefect, liEvenCrossUnitAmplitude]
    simp only [liEvenCrossUnitAffine]
    ring_nf at h ⊢
    linear_combination -1 * h
  exact mul_left_cancel₀ (by norm_num : (2 : Polynomial ℝ) ≠ 0) htwo

theorem liEvenCrossUnitDefect_coeff_zero (n : ℕ) :
    (liEvenCrossUnitDefect n).coeff 0 = 0 := by
  rw [liEvenCrossUnitDefect_eq_weightedSquare]
  simp

theorem X_mul_liEvenCrossUnitDefect_divX (n : ℕ) :
    X * (liEvenCrossUnitDefect n).divX = liEvenCrossUnitDefect n := by
  have h := Polynomial.X_mul_divX_add (liEvenCrossUnitDefect n)
  rw [liEvenCrossUnitDefect_coeff_zero, Polynomial.C_0, add_zero] at h
  exact h

theorem liEvenCrossUnitDefect_divX_eq_weightedSquare (n : ℕ) :
    (liEvenCrossUnitDefect n).divX =
      2 * (1 - X) *
        ((Polynomial.Chebyshev.U ℝ (n : ℤ)).comp liEvenCrossUnitAffine) ^ 2 := by
  apply mul_left_cancel₀ Polynomial.X_ne_zero
  rw [X_mul_liEvenCrossUnitDefect_divX,
    liEvenCrossUnitDefect_eq_weightedSquare]
  ring

/-- Arcsine integration by parts in finite moment coordinates. -/
theorem two_mul_momentFunctional_normalizedCentralBinom_one_sub_X_derivative_X_mul
    (P : Polynomial ℝ) :
    2 * HTGeometry.momentFunctional
          GaloisForLFunctions.HTGeometry.normalizedCentralBinom
          ((1 - X) * (X * P).derivative) =
      HTGeometry.momentFunctional
        GaloisForLFunctions.HTGeometry.normalizedCentralBinom P := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [mul_add, Polynomial.derivative_add, mul_add,
        HTGeometry.momentFunctional_add, HTGeometry.momentFunctional_add,
        mul_add, hp, hq]
  | monomial n a =>
      rw [HTGeometry.momentFunctional_monomial]
      have hpoly :
          (1 - X) * (X * Polynomial.monomial n a).derivative =
            Polynomial.monomial n ((n + 1 : ℝ) * a) -
              Polynomial.monomial (n + 1) ((n + 1 : ℝ) * a) := by
        rw [Polynomial.X_mul_monomial, Polynomial.derivative_monomial]
        simp only [Nat.add_sub_cancel]
        rw [sub_mul, one_mul, Polynomial.X_mul_monomial]
        congr 2 <;> push_cast <;> ring
      rw [hpoly, HTGeometry.momentFunctional_sub,
        HTGeometry.momentFunctional_monomial,
        HTGeometry.momentFunctional_monomial]
      rw [GaloisForLFunctions.HTGeometry.normalizedCentralBinom_succ]
      push_cast
      field_simp
      ring

theorem two_mul_momentFunctional_liEvenCrossUnitFluxQuotient (n : ℕ) :
    2 * HTGeometry.momentFunctional
          GaloisForLFunctions.HTGeometry.normalizedCentralBinom
          (liEvenCrossUnitFluxQuotient n) =
      HTGeometry.momentFunctional
        GaloisForLFunctions.HTGeometry.normalizedCentralBinom
        (liEvenCrossUnitDefect n).divX := by
  have h :=
    two_mul_momentFunctional_normalizedCentralBinom_one_sub_X_derivative_X_mul
      ((liEvenCrossUnitDefect n).divX)
  rw [X_mul_liEvenCrossUnitDefect_divX] at h
  simpa only [liEvenCrossUnitFluxQuotient] using h

/-- Strict arcsine positivity for a nonzero polynomial nonnegative on the unit interval. -/
theorem momentFunctional_normalizedCentralBinom_pos_of_nonnegativeOn_Icc
    {P : Polynomial ℝ} (hP0 : P ≠ 0)
    (hP : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 ≤ P.eval x) :
    0 < HTGeometry.momentFunctional
      GaloisForLFunctions.HTGeometry.normalizedCentralBinom P := by
  rw [GaloisForLFunctions.HTGeometry.momentFunctional_normalizedCentralBinom_eq_quarterIntegral]
  apply mul_pos (div_pos (by norm_num) Real.pi_pos)
  let f : ℝ → ℝ := fun x => P.eval (Real.cos x ^ 2)
  have hfcont : Continuous f := by
    dsimp only [f]
    fun_prop
  have hfint : IntervalIntegrable f volume (0 : ℝ) (Real.pi / 2) :=
    hfcont.intervalIntegrable _ _
  have hfnn : ∀ x, 0 ≤ f x := by
    intro x
    apply hP
    constructor
    · positivity
    · have hlow := neg_one_le_cos x
      have hupp := cos_le_one x
      nlinarith
  rw [intervalIntegral.integral_pos_iff_support_of_nonneg_ae
    (Filter.Eventually.of_forall hfnn) hfint]
  refine ⟨by positivity, ?_⟩
  let W : Set ℝ := Set.Ioo (0 : ℝ) (Real.pi / 2) ∩
    {x : ℝ | P.eval (Real.cos x ^ 2) ≠ 0}
  have hWopen : IsOpen W := by
    exact isOpen_Ioo.inter (isOpen_ne.preimage (P.continuous.comp
      (Real.continuous_cos.pow 2)))
  have hWne : W.Nonempty := by
    obtain ⟨x, hx, hpx⟩ :=
      GaloisForLFunctions.HTGeometry.exists_quarter_eval_cos_sq_ne_zero hP0
    exact ⟨x, hx, hpx⟩
  have hWsub : W ⊆ Function.support f ∩ Set.Ioc (0 : ℝ) (Real.pi / 2) := by
    intro x hx
    exact ⟨Function.mem_support.mpr hx.2, ⟨hx.1.1, hx.1.2.le⟩⟩
  exact (hWopen.measure_pos volume hWne).trans_le (measure_mono hWsub)

theorem momentFunctional_liEvenCrossUnitDefect_divX_pos (n : ℕ) :
    0 < HTGeometry.momentFunctional
      GaloisForLFunctions.HTGeometry.normalizedCentralBinom
      (liEvenCrossUnitDefect n).divX := by
  rw [liEvenCrossUnitDefect_divX_eq_weightedSquare]
  apply momentFunctional_normalizedCentralBinom_pos_of_nonnegativeOn_Icc
  · intro hzero
    have heval := congrArg (fun P : Polynomial ℝ => P.eval 0) hzero
    simp [liEvenCrossUnitAffine, Polynomial.Chebyshev.U_eval_neg_one] at heval
  · intro x hx
    simp only [Polynomial.eval_mul, Polynomial.eval_ofNat,
      Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_X,
      Polynomial.eval_pow]
    nlinarith [hx.2, sq_nonneg
      (((Polynomial.Chebyshev.U ℝ (n : ℤ)).comp liEvenCrossUnitAffine).eval x)]

/-- Every mode has a strictly positive universal arcsine flux energy. -/
theorem momentFunctional_liEvenCrossUnitFluxQuotient_pos (n : ℕ) :
    0 < HTGeometry.momentFunctional
      GaloisForLFunctions.HTGeometry.normalizedCentralBinom
      (liEvenCrossUnitFluxQuotient n) := by
  have h := momentFunctional_liEvenCrossUnitDefect_divX_pos n
  have heq := two_mul_momentFunctional_liEvenCrossUnitFluxQuotient n
  nlinarith

theorem eval_liEvenCrossUnitDefect (v : ℝ) (n : ℕ) (q : XiZeroCopy) :
    evalRealPolynomial (liEvenCrossUnitDefect n)
        (((v : ℝ) : ℂ) * xiShiftedReciprocalSquare v q) =
      liEvenCrossSquareMassAtom v n q := by
  let z : ℂ := ((v : ℝ) : ℂ) * xiShiftedReciprocalSquare v q
  have hc : liEvenCrossCayleyAtSquareMass v q = 2 * z - 1 := by
    simp [liEvenCrossCayleyAtSquareMass, z]
    ring
  have hdouble := congrArg
    (fun P : Polynomial ℝ => evalRealPolynomial P (2 * z - 1))
    (chebyshevT_two_mul_eq_two_mul_sq_sub_one (n + 1))
  have hdouble' :
      evalRealPolynomial (Polynomial.Chebyshev.T ℝ (2 * ((n + 1 : ℕ) : ℤ)))
          (2 * z - 1) =
        2 * evalRealPolynomial (Polynomial.Chebyshev.T ℝ ((n + 1 : ℕ) : ℤ))
          (2 * z - 1) ^ 2 - 1 := by
    simpa [evalRealPolynomial] using hdouble
  have hdef : evalRealPolynomial (liEvenCrossUnitDefect n) z =
      (1 - evalRealPolynomial (liEvenCrossUnitAmplitude n) z ^ 2) / 2 := by
    have h := congrArg (fun P : Polynomial ℝ => evalRealPolynomial P z)
      (two_mul_liEvenCrossUnitDefect n)
    simp only [evalRealPolynomial_mul] at h
    have htwo : evalRealPolynomial (2 : Polynomial ℝ) z = 2 := by
      simp [evalRealPolynomial]
    have hright : evalRealPolynomial (1 - liEvenCrossUnitAmplitude n ^ 2) z =
        1 - evalRealPolynomial (liEvenCrossUnitAmplitude n) z ^ 2 := by
      simp [evalRealPolynomial]
    rw [htwo, hright] at h
    linear_combination h / 2
  rw [hdef]
  rw [liEvenCrossUnitAmplitude, evalRealPolynomial, evalRealPolynomial,
    Polynomial.map_comp, Polynomial.eval_comp]
  change (1 - evalRealPolynomial (Polynomial.Chebyshev.T ℝ ((n : ℤ) + 1))
      (evalRealPolynomial liEvenCrossUnitAffine z) ^ 2) / 2 = _
  have haff : evalRealPolynomial liEvenCrossUnitAffine z = 2 * z - 1 := by
    simp [liEvenCrossUnitAffine, evalRealPolynomial]
  rw [haff, liEvenCrossSquareMassAtom, hc]
  rw [show (2 * ((n : ℤ) + 1)) = 2 * ((n + 1 : ℕ) : ℤ) by omega]
  rw [hdouble']
  push_cast
  ring

theorem hasDerivAt_liEvenCrossUnitMassCoordinate
    {v : ℝ} (hv : 0 < v) (q : XiZeroCopy) :
    HasDerivAt
      (fun t : ℝ => ((t : ℝ) : ℂ) * xiShiftedReciprocalSquare t q)
      (xiShiftedReciprocalSquare v q *
        (1 - (v : ℂ) * xiShiftedReciprocalSquare v q)) v := by
  have ht : HasDerivAt (fun t : ℝ => ((t : ℝ) : ℂ)) (1 : ℂ) v := by
    simpa using (hasDerivAt_id v).ofReal_comp
  have hlam := hasDerivAt_xiShiftedReciprocalSquare_pow hv q 0
  have h := ht.mul hlam
  convert h using 1
  norm_num
  ring

/-- One adjacent Chebyshev flux atom is exactly one reciprocal times the unit flux quotient. -/
theorem liEvenCrossSquareMassAdjacentFlux_eq_unitFluxQuotient
    {v : ℝ} (hv : 0 < v) (n : ℕ) (q : XiZeroCopy) :
    liEvenCrossSquareMassAdjacentFlux v n q =
      xiShiftedReciprocalSquare v q *
        evalRealPolynomial (liEvenCrossUnitFluxQuotient n)
          (((v : ℝ) : ℂ) * xiShiftedReciprocalSquare v q) := by
  have hcoord := hasDerivAt_liEvenCrossUnitMassCoordinate hv q
  have hpoly := hasDerivAt_evalRealPolynomial_comp
    (p := liEvenCrossUnitDefect n) hcoord
  have hfun :
      (fun t : ℝ => evalRealPolynomial (liEvenCrossUnitDefect n)
        (((t : ℝ) : ℂ) * xiShiftedReciprocalSquare t q)) =
      (fun t : ℝ => liEvenCrossSquareMassAtom t n q) := by
    funext t
    exact eval_liEvenCrossUnitDefect t n q
  rw [hfun] at hpoly
  have htarget :
      evalRealPolynomial (liEvenCrossUnitDefect n).derivative
          (((v : ℝ) : ℂ) * xiShiftedReciprocalSquare v q) *
          (xiShiftedReciprocalSquare v q *
            (1 - (v : ℂ) * xiShiftedReciprocalSquare v q)) =
        xiShiftedReciprocalSquare v q *
          evalRealPolynomial (liEvenCrossUnitFluxQuotient n)
            (((v : ℝ) : ℂ) * xiShiftedReciprocalSquare v q) := by
    have hX : evalRealPolynomial X
        (((v : ℝ) : ℂ) * xiShiftedReciprocalSquare v q) =
        ((v : ℝ) : ℂ) * xiShiftedReciprocalSquare v q := by
      simp [evalRealPolynomial]
    have hsub : evalRealPolynomial (1 - X)
        (((v : ℝ) : ℂ) * xiShiftedReciprocalSquare v q) =
        1 - ((v : ℝ) : ℂ) * xiShiftedReciprocalSquare v q := by
      simp [evalRealPolynomial]
    rw [liEvenCrossUnitFluxQuotient, evalRealPolynomial_mul, hsub]
    ring
  rw [htarget] at hpoly
  exact (hasDerivAt_liEvenCrossSquareMassAtom_adjacentFlux hv n q).unique hpoly

theorem summable_liEvenCrossSquareMassAdjacentFlux
    {v : ℝ} (hv : 0 < v) (n : ℕ) :
    Summable (liEvenCrossSquareMassAdjacentFlux v n) := by
  exact (summable_liEvenCrossSquareMassAtomVelocity hv n).congr
    (fun q => (liEvenCrossSquareMassAtomVelocity_eq_adjacentFlux hv n q))

/-- The complete adjacent current is one finite polynomial moment of the actual Xi tower. -/
theorem re_tsum_liEvenCrossSquareMassAdjacentFlux_eq_momentFunctional
    {v : ℝ} (hv : 0 < v) (n : ℕ) :
    (∑' q : XiZeroCopy, liEvenCrossSquareMassAdjacentFlux v n q).re =
      HTGeometry.momentFunctional
        (fun k => (xiShiftedReciprocalMoment v k).re)
        ((liEvenCrossUnitFluxQuotient n).comp
          (Polynomial.C v * X)) := by
  rw [momentFunctional_xiShifted_eq_polynomialAtomSum hv.le,
    xiShiftedPolynomialAtomSum]
  rw [Complex.re_tsum (summable_liEvenCrossSquareMassAdjacentFlux hv n)]
  apply tsum_congr
  intro q
  rw [liEvenCrossSquareMassAdjacentFlux_eq_unitFluxQuotient hv]
  simp only [evalRealPolynomial, Polynomial.map_comp, Polynomial.map_mul,
    Polynomial.map_C, Polynomial.map_X, Polynomial.eval_comp,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]

theorem momentFunctional_scaledSequence_eq_comp_scale
    (s : ℕ → ℝ) (c r : ℝ) (P : Polynomial ℝ) :
    HTGeometry.momentFunctional (fun k => c * r ^ k * s k) P =
      c * HTGeometry.momentFunctional s (P.comp (Polynomial.C r * X)) := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [HTGeometry.momentFunctional_add, hp, hq, Polynomial.add_comp,
        HTGeometry.momentFunctional_add, mul_add]
  | monomial n a =>
      rw [HTGeometry.momentFunctional_monomial,
        Polynomial.monomial_comp, HTGeometry.momentFunctional_mul]
      simp [mul_pow, mul_assoc, mul_left_comm, mul_comm]

theorem normalized_liEvenCrossSquareMassAdjacentFlux_eq_momentFunctional
    {w : ℝ} (hw : 1 < w) (n : ℕ) :
    2 * w / Real.log w *
        (∑' q : XiZeroCopy,
          liEvenCrossSquareMassAdjacentFlux (w ^ 2) n q).re =
      HTGeometry.momentFunctional
        (xiShiftedFarRightNormalizedMoment w)
        (liEvenCrossUnitFluxQuotient n) := by
  rw [re_tsum_liEvenCrossSquareMassAdjacentFlux_eq_momentFunctional
    (sq_pos_of_pos (lt_trans zero_lt_one hw))]
  rw [xiShiftedFarRightNormalizedMoment,
    momentFunctional_scaledSequence_eq_comp_scale
      (fun k => (xiShiftedReciprocalMoment (w ^ 2) k).re)
      (2 * w / Real.log w) (w ^ 2)]
  congr 2

theorem tendsto_momentFunctional_xiShiftedFarRightNormalizedMoment
    (P : Polynomial ℝ) :
    Tendsto
      (fun w : ℝ => HTGeometry.momentFunctional
        (xiShiftedFarRightNormalizedMoment w) P)
      atTop
      (nhds (HTGeometry.momentFunctional
        GaloisForLFunctions.HTGeometry.normalizedCentralBinom P)) := by
  have hterms : ∀ k ∈ P.support,
      Tendsto
        (fun w : ℝ => P.coeff k * xiShiftedFarRightNormalizedMoment w k)
        atTop
        (nhds (P.coeff k *
          GaloisForLFunctions.HTGeometry.normalizedCentralBinom k)) := by
    intro k hk
    exact (tendsto_scaled_re_xiShiftedReciprocalMoment_squareParam k).const_mul _
  simpa [HTGeometry.momentFunctional_eq_support_sum,
    xiShiftedFarRightNormalizedMoment, mul_assoc, mul_left_comm, mul_comm] using
    tendsto_finsetSum P.support hterms

/-- Exact all-mode far-right current asymptotic. -/
theorem tendsto_normalized_liEvenCrossSquareMassAdjacentFlux (n : ℕ) :
    Tendsto
      (fun w : ℝ => 2 * w / Real.log w *
        (∑' q : XiZeroCopy,
          liEvenCrossSquareMassAdjacentFlux (w ^ 2) n q).re)
      atTop
      (nhds (HTGeometry.momentFunctional
        GaloisForLFunctions.HTGeometry.normalizedCentralBinom
        (liEvenCrossUnitFluxQuotient n))) := by
  apply (tendsto_momentFunctional_xiShiftedFarRightNormalizedMoment
    (liEvenCrossUnitFluxQuotient n)).congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with w hw
  exact (normalized_liEvenCrossSquareMassAdjacentFlux_eq_momentFunctional hw n).symm

/-- The exterior completed-Abel current is eventually strictly positive at every mode. -/
theorem eventually_re_tsum_liEvenCrossSquareMassAdjacentFlux_square_pos (n : ℕ) :
    ∀ᶠ w : ℝ in atTop,
      0 < (∑' q : XiZeroCopy,
        liEvenCrossSquareMassAdjacentFlux (w ^ 2) n q).re := by
  have hlimitPos := momentFunctional_liEvenCrossUnitFluxQuotient_pos n
  have hnormalized : ∀ᶠ w : ℝ in atTop,
      0 < 2 * w / Real.log w *
        (∑' q : XiZeroCopy,
          liEvenCrossSquareMassAdjacentFlux (w ^ 2) n q).re :=
    (tendsto_normalized_liEvenCrossSquareMassAdjacentFlux n).eventually
      (Ioi_mem_nhds hlimitPos)
  filter_upwards [hnormalized, eventually_gt_atTop (1 : ℝ)] with w hpos hw
  have hscale : 0 < 2 * w / Real.log w :=
    div_pos (mul_pos (by norm_num) (lt_trans zero_lt_one hw)) (Real.log_pos hw)
  exact (mul_pos_iff.mp hpos).resolve_left (not_lt.mpr hscale.le)

/-- In the convergence window the exact current is one literal completed arithmetic source. -/
theorem re_tsum_liEvenCrossSquareMassAdjacentFlux_sq_eq_arithmeticSource
    {w : ℝ} (hw : 1 / 2 < w) (n : ℕ) :
    (∑' q : XiZeroCopy,
      liEvenCrossSquareMassAdjacentFlux (w ^ 2) n q).re =
      xiShiftedPolynomialCompletedArithmeticSource w
        ((liEvenCrossUnitFluxQuotient n).comp
          (Polynomial.C (w ^ 2) * X)) := by
  rw [re_tsum_liEvenCrossSquareMassAdjacentFlux_eq_momentFunctional
    (sq_pos_of_pos (by linarith : 0 < w))]
  rw [xiShiftedPolynomialCompletedArithmeticSource_eq_momentFunctional hw]
  rfl

/-- No all-exterior nonpositive current law can hold, even at one fixed mode. -/
theorem not_forall_re_tsum_liEvenCrossSquareMassAdjacentFlux_square_nonpos
    (n : ℕ) :
    ¬ ∀ w : ℝ, 1 / 2 < w →
      (∑' q : XiZeroCopy,
        liEvenCrossSquareMassAdjacentFlux (w ^ 2) n q).re ≤ 0 := by
  intro hnonpos
  have hevent :=
    (eventually_re_tsum_liEvenCrossSquareMassAdjacentFlux_square_pos n).and
      (eventually_gt_atTop (1 : ℝ))
  obtain ⟨w, hpos, hw⟩ := Filter.Eventually.exists hevent
  exact (not_lt_of_ge (hnonpos w (by linarith))) hpos

/-- Source-side statement of the same all-mode exterior-flow no-go. -/
theorem not_forall_liEvenCrossFluxArithmeticSource_nonpos (n : ℕ) :
    ¬ ∀ w : ℝ, 1 / 2 < w →
      xiShiftedPolynomialCompletedArithmeticSource w
        ((liEvenCrossUnitFluxQuotient n).comp
          (Polynomial.C (w ^ 2) * X)) ≤ 0 := by
  intro hnonpos
  apply not_forall_re_tsum_liEvenCrossSquareMassAdjacentFlux_square_nonpos n
  intro w hw
  rw [re_tsum_liEvenCrossSquareMassAdjacentFlux_sq_eq_arithmeticSource hw]
  exact hnonpos w hw

end

end RHTower
