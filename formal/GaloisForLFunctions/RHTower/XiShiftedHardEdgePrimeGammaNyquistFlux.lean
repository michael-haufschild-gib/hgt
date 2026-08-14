import GaloisForLFunctions.RHTower.XiShiftedHardEdgePrimeGammaSourceDisintegration
import GaloisForLFunctions.RHTower.XiShiftedHardEdgeGlobalNyquistCurrentExchange

open scoped BigOperators SchwartzMap FourierTransform
open Complex Filter MeasureTheory Polynomial Set

noncomputable section

namespace RHTower

/-- Positive hard-edge mass, packaging the only positivity required by source transmutation. -/
def RouteUPositiveHardEdgeMass := {a : ℝ // 0 < a}

/-- One common source degree for two oriented hard-edge polynomial channels. -/
def routeUHardEdgeCommonLiftDegree
    (a : ℝ) (P Q : Polynomial ℝ) : ℕ :=
  max (xiHardEdgeReciprocalPolynomial a P).natDegree
    (xiHardEdgeReciprocalPolynomial a Q).natDegree

def routeUHardEdgeCommonLeftCoefficients
    (a : ℝ) (P Q : Polynomial ℝ) :
    Fin (routeUHardEdgeCommonLiftDegree a P Q + 1) → ℝ :=
  Polynomial.toFn (routeUHardEdgeCommonLiftDegree a P Q + 1)
    (xiHardEdgeReciprocalPolynomial a P)

def routeUHardEdgeCommonRightCoefficients
    (a : ℝ) (P Q : Polynomial ℝ) :
    Fin (routeUHardEdgeCommonLiftDegree a P Q + 1) → ℝ :=
  Polynomial.toFn (routeUHardEdgeCommonLiftDegree a P Q + 1)
    (xiHardEdgeReciprocalPolynomial a Q)

theorem ofFn_routeUHardEdgeCommonLeftCoefficients
    (a : ℝ) (P Q : Polynomial ℝ) :
    Polynomial.ofFn (routeUHardEdgeCommonLiftDegree a P Q + 1)
        (routeUHardEdgeCommonLeftCoefficients a P Q) =
      xiHardEdgeReciprocalPolynomial a P := by
  apply Polynomial.ofFn_comp_toFn_eq_id_of_natDegree_lt
  exact lt_of_le_of_lt (le_max_left _ _)
    (Nat.lt_succ_self (routeUHardEdgeCommonLiftDegree a P Q))

theorem ofFn_routeUHardEdgeCommonRightCoefficients
    (a : ℝ) (P Q : Polynomial ℝ) :
    Polynomial.ofFn (routeUHardEdgeCommonLiftDegree a P Q + 1)
        (routeUHardEdgeCommonRightCoefficients a P Q) =
      xiHardEdgeReciprocalPolynomial a Q := by
  apply Polynomial.ofFn_comp_toFn_eq_id_of_natDegree_lt
  exact lt_of_le_of_lt (le_max_right _ _)
    (Nat.lt_succ_self (routeUHardEdgeCommonLiftDegree a P Q))

theorem routeUHardEdgeCommonLeftQuadratic_eq_trace_re
    (a : ℝ) (P Q : Polynomial ℝ) :
    xiShiftedReciprocalHankelQuadratic (a ^ 2)
        (routeUHardEdgeCommonLeftCoefficients a P Q) =
      (xiShiftedReciprocalTraceHankel (a ^ 2)
        (xiHardEdgeReciprocalPolynomial a P)).re := by
  have htrace := xiShiftedReciprocalTraceHankel_X_pow_mul_ofFn
    (sq_nonneg a) 0 (routeUHardEdgeCommonLiftDegree a P Q + 1)
      (routeUHardEdgeCommonLeftCoefficients a P Q)
  simp only [pow_zero, one_mul, ofFn_routeUHardEdgeCommonLeftCoefficients,
    Nat.mul_zero, Nat.zero_add] at htrace
  rw [xiShiftedReciprocalHankelQuadratic, htrace]
  simp only [Complex.re_sum, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]

theorem routeUHardEdgeCommonRightQuadratic_eq_trace_re
    (a : ℝ) (P Q : Polynomial ℝ) :
    xiShiftedReciprocalHankelQuadratic (a ^ 2)
        (routeUHardEdgeCommonRightCoefficients a P Q) =
      (xiShiftedReciprocalTraceHankel (a ^ 2)
        (xiHardEdgeReciprocalPolynomial a Q)).re := by
  have htrace := xiShiftedReciprocalTraceHankel_X_pow_mul_ofFn
    (sq_nonneg a) 0 (routeUHardEdgeCommonLiftDegree a P Q + 1)
      (routeUHardEdgeCommonRightCoefficients a P Q)
  simp only [pow_zero, one_mul, ofFn_routeUHardEdgeCommonRightCoefficients,
    Nat.mul_zero, Nat.zero_add] at htrace
  rw [xiShiftedReciprocalHankelQuadratic, htrace]
  simp only [Complex.re_sum, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]

/-- Literal completed prime--Gamma capital of the left channel, padded to the common degree. -/
def routeUHardEdgeCommonLeftPrimeGammaCapital
    (a : RouteUPositiveHardEdgeMass) (P Q : Polynomial ℝ) : ℝ :=
  routeUShiftedFilteredCompletedSourceCapital (a.1 ^ 2)
    (routeUHardEdgeCommonLiftDegree a.1 P Q)
    (routeUHardEdgeCommonLeftCoefficients a.1 P Q)

/-- Literal completed prime--Gamma capital of the right channel, with the same source filter. -/
def routeUHardEdgeCommonRightPrimeGammaCapital
    (a : RouteUPositiveHardEdgeMass) (P Q : Polynomial ℝ) : ℝ :=
  routeUShiftedFilteredCompletedSourceCapital (a.1 ^ 2)
    (routeUHardEdgeCommonLiftDegree a.1 P Q)
    (routeUHardEdgeCommonRightCoefficients a.1 P Q)

theorem routeUHardEdgeCommonLeftPrimeGammaCapital_eq
    (a : RouteUPositiveHardEdgeMass) (P Q : Polynomial ℝ) :
    routeUHardEdgeCommonLeftPrimeGammaCapital a P Q =
      Real.pi *
          ((2 * routeUHardEdgeCommonLiftDegree a.1 P Q).factorial : ℝ) *
        xiShiftedReciprocalHankelQuadratic (a.1 ^ 2)
          (routeUHardEdgeCommonLeftCoefficients a.1 P Q) := by
  exact routeUShiftedFilteredCompletedSourceCapital_eq_hankelQuadratic
    (sq_pos_of_pos a.2) _ _

theorem routeUHardEdgeCommonRightPrimeGammaCapital_eq
    (a : RouteUPositiveHardEdgeMass) (P Q : Polynomial ℝ) :
    routeUHardEdgeCommonRightPrimeGammaCapital a P Q =
      Real.pi *
          ((2 * routeUHardEdgeCommonLiftDegree a.1 P Q).factorial : ℝ) *
        xiShiftedReciprocalHankelQuadratic (a.1 ^ 2)
          (routeUHardEdgeCommonRightCoefficients a.1 P Q) := by
  exact routeUShiftedFilteredCompletedSourceCapital_eq_hankelQuadratic
    (sq_pos_of_pos a.2) _ _

/-- Oriented divisor term before scalar aggregation. -/
def routeUHardEdgePolynomialNyquistFluxTerm
    (a : ℝ) (P Q : Polynomial ℝ) (q : XiZeroCopy) : ℂ :=
  xiHardEdgeDivisorPacketTerm a P q - xiHardEdgeDivisorPacketTerm a Q q

theorem routeUHardEdgePolynomialNyquistFluxTerm_eq
    (a : ℝ) (P Q : Polynomial ℝ) (q : XiZeroCopy) :
    routeUHardEdgePolynomialNyquistFluxTerm a P Q q =
      (((a ^ 2 : ℝ) : ℂ) * xiShiftedReciprocalSquare (a ^ 2) q) *
        (evalRealPolynomial P
              (xiHardEdgeCayleyCoordinate (a : ℂ) (xiSpectralPoint q)) ^ 2 -
          evalRealPolynomial Q
              (xiHardEdgeCayleyCoordinate (a : ℂ) (xiSpectralPoint q)) ^ 2) := by
  rw [routeUHardEdgePolynomialNyquistFluxTerm,
    xiHardEdgeDivisorPacketTerm, xiHardEdgeDivisorPacketTerm]
  ring

theorem summable_routeUHardEdgePolynomialNyquistFluxTerm
    (a : ℝ) (P Q : Polynomial ℝ) :
    Summable (routeUHardEdgePolynomialNyquistFluxTerm a P Q) := by
  exact (summable_xiHardEdgeDivisorPacketTerm a P).sub
    (summable_xiHardEdgeDivisorPacketTerm a Q)

theorem routeUHardEdgeCommonLeftQuadratic_eq_divisorPacket
    (a : ℝ) (P Q : Polynomial ℝ) :
    a ^ 2 * xiShiftedReciprocalHankelQuadratic (a ^ 2)
        (routeUHardEdgeCommonLeftCoefficients a P Q) =
      (∑' q : XiZeroCopy, xiHardEdgeDivisorPacketTerm a P q).re := by
  rw [routeUHardEdgeCommonLeftQuadratic_eq_trace_re,
    tsum_xiHardEdgeDivisorPacketTerm_eq_traceHankel]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

theorem routeUHardEdgeCommonRightQuadratic_eq_divisorPacket
    (a : ℝ) (P Q : Polynomial ℝ) :
    a ^ 2 * xiShiftedReciprocalHankelQuadratic (a ^ 2)
        (routeUHardEdgeCommonRightCoefficients a P Q) =
      (∑' q : XiZeroCopy, xiHardEdgeDivisorPacketTerm a Q q).re := by
  rw [routeUHardEdgeCommonRightQuadratic_eq_trace_re,
    tsum_xiHardEdgeDivisorPacketTerm_eq_traceHankel]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

theorem re_tsum_routeUHardEdgePolynomialNyquistFluxTerm_eq
    (a : ℝ) (P Q : Polynomial ℝ) :
    (∑' q : XiZeroCopy, routeUHardEdgePolynomialNyquistFluxTerm a P Q q).re =
      a ^ 2 *
        (xiShiftedReciprocalHankelQuadratic (a ^ 2)
            (routeUHardEdgeCommonLeftCoefficients a P Q) -
          xiShiftedReciprocalHankelQuadratic (a ^ 2)
            (routeUHardEdgeCommonRightCoefficients a P Q)) := by
  rw [show (∑' q : XiZeroCopy, routeUHardEdgePolynomialNyquistFluxTerm a P Q q) =
      (∑' q : XiZeroCopy, xiHardEdgeDivisorPacketTerm a P q) -
        ∑' q : XiZeroCopy, xiHardEdgeDivisorPacketTerm a Q q by
      exact (summable_xiHardEdgeDivisorPacketTerm a P).tsum_sub
        (summable_xiHardEdgeDivisorPacketTerm a Q)]
  rw [Complex.sub_re,
    ← routeUHardEdgeCommonLeftQuadratic_eq_divisorPacket a P Q,
    ← routeUHardEdgeCommonRightQuadratic_eq_divisorPacket a P Q]
  ring

/-- **Common-filter prime--Gamma Nyquist flux identity.**

The oriented polynomial channel divisor current is exactly the difference of two literal
completed prime--Gamma source capitals with one common positive Laplace filter. -/
theorem routeUHardEdgePrimeGammaNyquistFlux_identity
    (a : RouteUPositiveHardEdgeMass) (P Q : Polynomial ℝ) :
    a.1 ^ 2 *
        (routeUHardEdgeCommonLeftPrimeGammaCapital a P Q -
          routeUHardEdgeCommonRightPrimeGammaCapital a P Q) =
      Real.pi *
          ((2 * routeUHardEdgeCommonLiftDegree a.1 P Q).factorial : ℝ) *
        (∑' q : XiZeroCopy,
          routeUHardEdgePolynomialNyquistFluxTerm a.1 P Q q).re := by
  rw [routeUHardEdgeCommonLeftPrimeGammaCapital_eq,
    routeUHardEdgeCommonRightPrimeGammaCapital_eq,
    re_tsum_routeUHardEdgePolynomialNyquistFluxTerm_eq]
  ring

/-- Finite even-polyphase Chebyshev packet at the dyadically refined hard edge. -/
def routeUDyadicFineEvenChebyshevPacketPolynomial
    (n : ℕ) (g : SchwartzMap ℝ ℝ) (k N : ℕ) : Polynomial ℝ :=
  let r : ℝ := routeUDyadicFineIndex k
  let h : ℝ := routeUHardEdgeMesh r
  let A := SchwartzMap.compactSupportApproximation n (routeURealEvenAmplitude g)
  Polynomial.C (h * (A 0).re) +
    ∑ j ∈ Finset.range N,
      Polynomial.C (2 * h * (A (h * (2 * (j + 1 : ℝ)))).re) *
        Polynomial.Chebyshev.T ℝ ((2 * (j + 1) : ℕ) : ℤ)

/-- The odd channel is the exact residual of the full finite packet after removing even modes. -/
def routeUDyadicFineOddChebyshevPacketPolynomial
    (n : ℕ) (g : SchwartzMap ℝ ℝ) (k N : ℕ) : Polynomial ℝ :=
  routeUFiniteChebyshevPacketPolynomial n g (routeUDyadicFineIndex k : ℝ) N -
    routeUDyadicFineEvenChebyshevPacketPolynomial n g k N

theorem routeUDyadicFineEvenLatticeSample_eq_eval_evenChebyshevPacket
    (n : ℕ) (g : SchwartzMap ℝ ℝ) (k N : ℕ)
    (hcut : ∀ j : ℕ, N ≤ j →
      SchwartzMap.compactSupportApproximation n (routeURealEvenAmplitude g)
        (routeUHardEdgeMesh (routeUDyadicFineIndex k : ℝ) * (j + 1 : ℝ)) = 0)
    (q : XiZeroCopy) :
    routeUDyadicFineEvenLatticeSample n (routeURealEvenAmplitude g) k q =
      evalRealPolynomial (routeUDyadicFineEvenChebyshevPacketPolynomial n g k N)
        (xiHardEdgeCayleyCoordinate
          (routeUHardEdgeMass (routeUDyadicFineIndex k : ℝ) : ℂ)
          (xiSpectralPoint q)) := by
  let r : ℝ := routeUDyadicFineIndex k
  let h : ℝ := routeUHardEdgeMesh r
  let A : SchwartzMap ℝ ℂ :=
    SchwartzMap.compactSupportApproximation n (routeURealEvenAmplitude g)
  let z : ℂ := routeUDyadicFinePhase k (xiSpectralPoint q)
  let E : ℤ → ℂ := fun j =>
    Complex.exp (Complex.I * z * ((h * (2 * (j : ℝ)) : ℝ) : ℂ)) *
      A (h * (2 * (j : ℝ)))
  have htailPos : Summable fun j : ℕ => E ((j + 1 : ℕ) : ℤ) := by
    apply summable_of_ne_finset_zero (s := Finset.range N)
    intro j hj
    simp only [Finset.mem_range, not_lt] at hj
    have hindex : N ≤ 2 * j + 1 := by omega
    have hzero := hcut (2 * j + 1) hindex
    have hpoint : h * (2 * (((j + 1 : ℕ) : ℤ) : ℝ)) =
        routeUHardEdgeMesh (routeUDyadicFineIndex k : ℝ) *
          ((2 * j + 1 : ℕ) + 1 : ℝ) := by
      dsimp only [h, r]
      push_cast
      ring
    simp only [E]
    rw [hpoint]
    rw [show A (routeUHardEdgeMesh (routeUDyadicFineIndex k : ℝ) *
        ((2 * j + 1 : ℕ) + 1 : ℝ)) = 0 by
      simpa only [A, Nat.cast_add, Nat.cast_one] using hzero]
    simp
  have hpos : Summable fun j : ℕ => E (j : ℤ) := by
    apply (summable_nat_add_iff 1).1
    simpa only [Nat.cast_add, Nat.cast_one] using htailPos
  have hneg : Summable fun j : ℕ => E (-((j : ℤ) + 1)) := by
    apply summable_of_ne_finset_zero (s := Finset.range N)
    intro j hj
    simp only [Finset.mem_range, not_lt] at hj
    have hindex : N ≤ 2 * j + 1 := by omega
    have hzero := hcut (2 * j + 1) hindex
    have hposPoint : h * (2 * (((j + 1 : ℕ) : ℤ) : ℝ)) =
        routeUHardEdgeMesh (routeUDyadicFineIndex k : ℝ) *
          ((2 * j + 1 : ℕ) + 1 : ℝ) := by
      dsimp only [h, r]
      push_cast
      ring
    have hnegPoint : h * (2 * ((-((j : ℤ) + 1) : ℤ) : ℝ)) =
        -(h * (2 * (((j + 1 : ℕ) : ℤ) : ℝ))) := by
      push_cast
      ring
    simp only [E]
    rw [hnegPoint, routeURealEvenCompactApproximation_even,
      hposPoint]
    rw [show A (routeUHardEdgeMesh (routeUDyadicFineIndex k : ℝ) *
        ((2 * j + 1 : ℕ) + 1 : ℝ)) = 0 by
      simpa only [A, Nat.cast_add, Nat.cast_one] using hzero]
    simp
  have hhead :
      (∑' j : ℕ, E (j : ℤ)) = E 0 + ∑' j : ℕ, E ((j + 1 : ℕ) : ℤ) := by
    simpa only [Finset.sum_range_one, Nat.cast_zero, Nat.cast_add, Nat.cast_one] using
      (hpos.sum_add_tsum_nat_add 1).symm
  have htailPosFinite :
      (∑' j : ℕ, E ((j + 1 : ℕ) : ℤ)) =
        ∑ j ∈ Finset.range N, E ((j + 1 : ℕ) : ℤ) := by
    rw [tsum_eq_sum (s := Finset.range N)]
    intro j hj
    simp only [Finset.mem_range, not_lt] at hj
    have hindex : N ≤ 2 * j + 1 := by omega
    have hzero := hcut (2 * j + 1) hindex
    have hpoint : h * (2 * (((j + 1 : ℕ) : ℤ) : ℝ)) =
        routeUHardEdgeMesh (routeUDyadicFineIndex k : ℝ) *
          ((2 * j + 1 : ℕ) + 1 : ℝ) := by
      dsimp only [h, r]
      push_cast
      ring
    simp only [E]
    rw [hpoint]
    rw [show A (routeUHardEdgeMesh (routeUDyadicFineIndex k : ℝ) *
        ((2 * j + 1 : ℕ) + 1 : ℝ)) = 0 by
      simpa only [A, Nat.cast_add, Nat.cast_one] using hzero]
    simp
  have htailNegFinite :
      (∑' j : ℕ, E (-((j : ℤ) + 1))) =
        ∑ j ∈ Finset.range N, E (-((j : ℤ) + 1)) := by
    rw [tsum_eq_sum (s := Finset.range N)]
    intro j hj
    simp only [Finset.mem_range, not_lt] at hj
    have hindex : N ≤ 2 * j + 1 := by omega
    have hzero := hcut (2 * j + 1) hindex
    have hposPoint : h * (2 * (((j + 1 : ℕ) : ℤ) : ℝ)) =
        routeUHardEdgeMesh (routeUDyadicFineIndex k : ℝ) *
          ((2 * j + 1 : ℕ) + 1 : ℝ) := by
      dsimp only [h, r]
      push_cast
      ring
    have hnegPoint : h * (2 * ((-((j : ℤ) + 1) : ℤ) : ℝ)) =
        -(h * (2 * (((j + 1 : ℕ) : ℤ) : ℝ))) := by
      push_cast
      ring
    simp only [E]
    rw [hnegPoint, routeURealEvenCompactApproximation_even,
      hposPoint]
    rw [show A (routeUHardEdgeMesh (routeUDyadicFineIndex k : ℝ) *
        ((2 * j + 1 : ℕ) + 1 : ℝ)) = 0 by
      simpa only [A, Nat.cast_add, Nat.cast_one] using hzero]
    simp
  rw [routeUDyadicFineEvenLatticeSample]
  simp only [Int.cast_mul, Int.cast_ofNat]
  change (h : ℂ) * (∑' j : ℤ, E j) = _
  rw [tsum_of_nat_of_neg_add_one hpos hneg, hhead,
    htailPosFinite, htailNegFinite]
  rw [routeUDyadicFineEvenChebyshevPacketPolynomial, evalRealPolynomial]
  simp only [Polynomial.map_add, Polynomial.map_C, Polynomial.map_sum,
    Polynomial.map_mul, Polynomial.Chebyshev.map_T, Polynomial.eval_add,
    Polynomial.eval_C, Polynomial.eval_finsetSum, Polynomial.eval_mul]
  rw [mul_add, mul_add, Finset.mul_sum, Finset.mul_sum,
    add_assoc, ← Finset.sum_add_distrib]
  congr 1
  · simp only [E]
    simp only [Int.cast_zero, mul_zero, Complex.ofReal_zero,
      Complex.exp_zero, one_mul]
    have hreal := routeURealEvenCompactApproximation_im n g 0
    have hA : A 0 = ((A 0).re : ℂ) := by
      apply Complex.ext
      · simp
      · simpa only [A, Complex.ofReal_im] using hreal
    rw [hA]
    simp only [A, Complex.ofReal_re]
    norm_cast
  · apply Finset.sum_congr rfl
    intro j hj
    simp only [E]
    have hpoint : h * (2 * (((j + 1 : ℕ) : ℤ) : ℝ)) =
        h * (2 * (j + 1 : ℝ)) := by
      push_cast
      ring
    rw [hpoint]
    have hnegPoint : h * (2 * ((-((j : ℤ) + 1) : ℤ) : ℝ)) =
        -(h * (2 * (j + 1 : ℝ))) := by
      push_cast
      ring
    rw [hnegPoint, routeURealEvenCompactApproximation_even]
    have hreal := routeURealEvenCompactApproximation_im n g
      (h * (2 * (j + 1 : ℝ)))
    have hA : A (h * (2 * (j + 1 : ℝ))) =
        ((A (h * (2 * (j + 1 : ℝ)))).re : ℂ) := by
      apply Complex.ext
      · simp
      · simpa only [A, Complex.ofReal_im] using hreal
    rw [hA]
    have hpair := routeUComplexHardEdgePhase_pair_eq_two_chebyshev
      r q (2 * (j + 1))
    have hz : z = routeUComplexHardEdgePhase r (xiSpectralPoint q) := by rfl
    rw [hz] at *
    simp only [Complex.ofReal_re]
    let X : ℂ := Complex.exp
      (Complex.I * routeUComplexHardEdgePhase r (xiSpectralPoint q) *
        ((h * (2 * (j + 1 : ℝ)) : ℝ) : ℂ))
    let Y : ℂ := Complex.exp
      (Complex.I * routeUComplexHardEdgePhase r (xiSpectralPoint q) *
        ((-(h * (2 * (j + 1 : ℝ))) : ℝ) : ℂ))
    let c : ℝ := (A (h * (2 * (j + 1 : ℝ)))).re
    let T : ℂ := Polynomial.eval
      (xiHardEdgeCayleyCoordinate (routeUHardEdgeMass r : ℂ) (xiSpectralPoint q))
      (Polynomial.Chebyshev.T ℂ ((2 * (j + 1) : ℕ) : ℤ))
    have hXY : X + Y = 2 * T := by
      dsimp only [X, Y, T]
      rw [show -(h * (2 * (j + 1 : ℝ))) =
          h * (-(2 * (j + 1 : ℝ))) by ring]
      simp only [evalRealPolynomial, Polynomial.Chebyshev.map_T] at hpair
      dsimp only [h]
      convert hpair using 1
      all_goals push_cast
      all_goals ring
    change (h : ℂ) * (X * (c : ℂ)) + (h : ℂ) * (Y * (c : ℂ)) =
      ((2 * h * c : ℝ) : ℂ) * T
    rw [show (h : ℂ) * (X * (c : ℂ)) + (h : ℂ) * (Y * (c : ℂ)) =
        (h : ℂ) * (c : ℂ) * (X + Y) by ring, hXY]
    push_cast
    ring

theorem routeUDyadicEvenSample_eq_eval_evenChebyshevPacket
    (n : ℕ) (g : SchwartzMap ℝ ℝ) (k N : ℕ)
    (hcut : ∀ j : ℕ, N ≤ j →
      SchwartzMap.compactSupportApproximation n (routeURealEvenAmplitude g)
        (routeUHardEdgeMesh (routeUDyadicFineIndex k : ℝ) * (j + 1 : ℝ)) = 0)
    (q : XiZeroCopy) :
    routeUDyadicEvenSample n (routeURealEvenAmplitude g) k q =
      evalRealPolynomial (routeUDyadicFineEvenChebyshevPacketPolynomial n g k N)
        (xiHardEdgeCayleyCoordinate
          (routeUHardEdgeMass (routeUDyadicFineIndex k : ℝ) : ℂ)
          (xiSpectralPoint q)) := by
  rw [← routeUDyadicFineEvenLatticeSample_eq_evenSample]
  exact routeUDyadicFineEvenLatticeSample_eq_eval_evenChebyshevPacket
    n g k N hcut q

theorem routeUDyadicOddSample_eq_eval_oddChebyshevPacket
    (n : ℕ) (g : SchwartzMap ℝ ℝ) (k N : ℕ)
    (hcut : ∀ j : ℕ, N ≤ j →
      SchwartzMap.compactSupportApproximation n (routeURealEvenAmplitude g)
        (routeUHardEdgeMesh (routeUDyadicFineIndex k : ℝ) * (j + 1 : ℝ)) = 0)
    (q : XiZeroCopy) :
    routeUDyadicOddSample n (routeURealEvenAmplitude g) k q =
      evalRealPolynomial (routeUDyadicFineOddChebyshevPacketPolynomial n g k N)
        (xiHardEdgeCayleyCoordinate
          (routeUHardEdgeMass (routeUDyadicFineIndex k : ℝ) : ℂ)
          (xiSpectralPoint q)) := by
  rw [routeUDyadicOddSample,
    routeUDyadicFineOddChebyshevPacketPolynomial]
  simp only [evalRealPolynomial, Polynomial.map_sub, Polynomial.eval_sub]
  rw [
    routeUXiComplexHardEdgeSample_eq_eval_finiteChebyshevPacket n g
      (routeUDyadicFineIndex k : ℝ) N hcut q,
    routeUDyadicEvenSample_eq_eval_evenChebyshevPacket n g k N hcut q]
  rfl

/-- Canonical finite cutoff for the refined real-even physical lattice packet. -/
def routeUDyadicFineChebyshevCutoff
    (n : ℕ) (g : SchwartzMap ℝ ℝ) (k : ℕ) : ℕ :=
  Classical.choose
    (exists_routeUFiniteChebyshevPacket_cutoff n g (routeUDyadicFineIndex k : ℝ))

theorem routeUDyadicFineChebyshevCutoff_spec
    (n : ℕ) (g : SchwartzMap ℝ ℝ) (k : ℕ) :
    ∀ j : ℕ, routeUDyadicFineChebyshevCutoff n g k ≤ j →
      SchwartzMap.compactSupportApproximation n (routeURealEvenAmplitude g)
        (routeUHardEdgeMesh (routeUDyadicFineIndex k : ℝ) * (j + 1 : ℝ)) = 0 := by
  exact Classical.choose_spec
    (exists_routeUFiniteChebyshevPacket_cutoff n g (routeUDyadicFineIndex k : ℝ))

def routeUDyadicFineEvenSourcePolynomial
    (n : ℕ) (g : SchwartzMap ℝ ℝ) (k : ℕ) : Polynomial ℝ :=
  routeUDyadicFineEvenChebyshevPacketPolynomial n g k
    (routeUDyadicFineChebyshevCutoff n g k)

def routeUDyadicFineOddSourcePolynomial
    (n : ℕ) (g : SchwartzMap ℝ ℝ) (k : ℕ) : Polynomial ℝ :=
  routeUDyadicFineOddChebyshevPacketPolynomial n g k
    (routeUDyadicFineChebyshevCutoff n g k)

theorem routeUDyadicEvenSample_eq_eval_sourcePolynomial
    (n : ℕ) (g : SchwartzMap ℝ ℝ) (k : ℕ) (q : XiZeroCopy) :
    routeUDyadicEvenSample n (routeURealEvenAmplitude g) k q =
      evalRealPolynomial (routeUDyadicFineEvenSourcePolynomial n g k)
        (xiHardEdgeCayleyCoordinate
          (routeUHardEdgeMass (routeUDyadicFineIndex k : ℝ) : ℂ)
          (xiSpectralPoint q)) := by
  exact routeUDyadicEvenSample_eq_eval_evenChebyshevPacket n g k _
    (routeUDyadicFineChebyshevCutoff_spec n g k) q

theorem routeUDyadicOddSample_eq_eval_sourcePolynomial
    (n : ℕ) (g : SchwartzMap ℝ ℝ) (k : ℕ) (q : XiZeroCopy) :
    routeUDyadicOddSample n (routeURealEvenAmplitude g) k q =
      evalRealPolynomial (routeUDyadicFineOddSourcePolynomial n g k)
        (xiHardEdgeCayleyCoordinate
          (routeUHardEdgeMass (routeUDyadicFineIndex k : ℝ) : ℂ)
          (xiSpectralPoint q)) := by
  exact routeUDyadicOddSample_eq_eval_oddChebyshevPacket n g k _
    (routeUDyadicFineChebyshevCutoff_spec n g k) q

/-- Fine hard-edge mass as a positive source parameter. -/
def routeUDyadicPositiveFineMass (k : ℕ) : RouteUPositiveHardEdgeMass :=
  ⟨routeUHardEdgeMass (routeUDyadicFineIndex k : ℝ),
    routeUHardEdgeMass_pos (routeUDyadicFineIndex k : ℝ)⟩

theorem routeUDyadicPolynomialNyquistFluxTerm_eq_weightedCurrent
    (n : ℕ) (g : SchwartzMap ℝ ℝ) (k : ℕ) (q : XiZeroCopy) :
    routeUHardEdgePolynomialNyquistFluxTerm
        (routeUDyadicPositiveFineMass k).1
        (routeUDyadicFineEvenSourcePolynomial n g k)
        (routeUDyadicFineOddSourcePolynomial n g k) q =
      routeUDyadicXiWeightedNyquistCurrent n (routeURealEvenAmplitude g) k q := by
  rw [routeUHardEdgePolynomialNyquistFluxTerm_eq,
    routeUDyadicXiWeightedNyquistCurrent,
    routeUXiHardEdgeResolventWeight,
    routeUDyadicXiNyquistCurrent_eq_sq_sub_sq,
    routeUDyadicEvenSample_eq_eval_sourcePolynomial,
    routeUDyadicOddSample_eq_eval_sourcePolynomial]
  rfl

theorem tsum_routeUDyadicPolynomialNyquistFluxTerm_eq_weightedCurrent
    (n : ℕ) (g : SchwartzMap ℝ ℝ) (k : ℕ) :
    (∑' q : XiZeroCopy,
      routeUHardEdgePolynomialNyquistFluxTerm
        (routeUDyadicPositiveFineMass k).1
        (routeUDyadicFineEvenSourcePolynomial n g k)
        (routeUDyadicFineOddSourcePolynomial n g k) q) =
      ∑' q : XiZeroCopy,
        routeUDyadicXiWeightedNyquistCurrent n (routeURealEvenAmplitude g) k q := by
  apply tsum_congr
  exact routeUDyadicPolynomialNyquistFluxTerm_eq_weightedCurrent n g k

/-- Exact literal prime--Gamma identity for the actual Route-U even/odd source channels. -/
theorem routeUDyadicPrimeGammaNyquistFlux_identity
    (n : ℕ) (g : SchwartzMap ℝ ℝ) (k : ℕ) :
    (routeUDyadicPositiveFineMass k).1 ^ 2 *
        (routeUHardEdgeCommonLeftPrimeGammaCapital
            (routeUDyadicPositiveFineMass k)
            (routeUDyadicFineEvenSourcePolynomial n g k)
            (routeUDyadicFineOddSourcePolynomial n g k) -
          routeUHardEdgeCommonRightPrimeGammaCapital
            (routeUDyadicPositiveFineMass k)
            (routeUDyadicFineEvenSourcePolynomial n g k)
            (routeUDyadicFineOddSourcePolynomial n g k)) =
      Real.pi *
          ((2 * routeUHardEdgeCommonLiftDegree
            (routeUDyadicPositiveFineMass k).1
            (routeUDyadicFineEvenSourcePolynomial n g k)
            (routeUDyadicFineOddSourcePolynomial n g k)).factorial : ℝ) *
        (∑' q : XiZeroCopy,
          routeUDyadicXiWeightedNyquistCurrent n (routeURealEvenAmplitude g) k q).re := by
  rw [← tsum_routeUDyadicPolynomialNyquistFluxTerm_eq_weightedCurrent]
  exact routeUHardEdgePrimeGammaNyquistFlux_identity
    (routeUDyadicPositiveFineMass k)
    (routeUDyadicFineEvenSourcePolynomial n g k)
    (routeUDyadicFineOddSourcePolynomial n g k)

/-- Factorial- and mass-renormalized literal source flux. -/
def routeUDyadicRenormalizedPrimeGammaNyquistFlux
    (n : ℕ) (g : SchwartzMap ℝ ℝ) (k : ℕ) : ℝ :=
  (routeUDyadicPositiveFineMass k).1 ^ 2 *
      (routeUHardEdgeCommonLeftPrimeGammaCapital
          (routeUDyadicPositiveFineMass k)
          (routeUDyadicFineEvenSourcePolynomial n g k)
          (routeUDyadicFineOddSourcePolynomial n g k) -
        routeUHardEdgeCommonRightPrimeGammaCapital
          (routeUDyadicPositiveFineMass k)
          (routeUDyadicFineEvenSourcePolynomial n g k)
          (routeUDyadicFineOddSourcePolynomial n g k)) /
    (Real.pi *
      ((2 * routeUHardEdgeCommonLiftDegree
        (routeUDyadicPositiveFineMass k).1
        (routeUDyadicFineEvenSourcePolynomial n g k)
        (routeUDyadicFineOddSourcePolynomial n g k)).factorial : ℝ))

theorem routeUDyadicRenormalizedPrimeGammaNyquistFlux_eq
    (n : ℕ) (g : SchwartzMap ℝ ℝ) (k : ℕ) :
    routeUDyadicRenormalizedPrimeGammaNyquistFlux n g k =
      (∑' q : XiZeroCopy,
        routeUDyadicXiWeightedNyquistCurrent n (routeURealEvenAmplitude g) k q).re := by
  rw [routeUDyadicRenormalizedPrimeGammaNyquistFlux]
  apply (div_eq_iff ?_).2
  · simpa only [mul_comm] using routeUDyadicPrimeGammaNyquistFlux_identity n g k
  · exact mul_ne_zero Real.pi_ne_zero (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))

/-- **Global literal source-flux cancellation.**

The actual common-filter completed prime--Gamma even-minus-odd source flux tends to zero. -/
theorem tendsto_routeUDyadicRenormalizedPrimeGammaNyquistFlux_zero
    (n : ℕ) (g : SchwartzMap ℝ ℝ) :
    Tendsto (routeUDyadicRenormalizedPrimeGammaNyquistFlux n g)
      atTop (nhds 0) := by
  have hcomplex :=
    tendsto_tsum_routeUDyadicXiWeightedNyquistCurrent_zero
      n (routeURealEvenAmplitude g)
  have hcomplex' : Tendsto
      (fun k : ℕ => ∑' q : XiZeroCopy,
        routeUDyadicXiWeightedNyquistCurrent n (routeURealEvenAmplitude g) k q)
      atTop (nhds 0) := by
    simpa only [routeUDyadicXiWeightedNyquistCurrent] using hcomplex
  have hre := (Complex.continuous_re.tendsto (0 : ℂ)).comp hcomplex'
  refine hre.congr' (Eventually.of_forall fun k => ?_)
  exact (routeUDyadicRenormalizedPrimeGammaNyquistFlux_eq n g k).symm

end RHTower
