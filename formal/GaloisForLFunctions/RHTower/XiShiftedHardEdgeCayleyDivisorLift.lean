import GaloisForLFunctions.RHTower.XiShiftedParabolicDegreeHorizon
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

open scoped Real
open Real Complex Polynomial

noncomputable section

namespace RHTower

private theorem chebyshevT_eval_add_inv_div_two
    (u : ℂ) (hu : u ≠ 0) (n : ℕ) :
    (Polynomial.Chebyshev.T ℂ (n : ℤ)).eval ((u + u⁻¹) / 2) =
      (u ^ n + (u⁻¹) ^ n) / 2 := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp
  | more n h0 h1 =>
      have h1' :
          (Polynomial.Chebyshev.T ℂ ((n : ℤ) + 1)).eval ((u + u⁻¹) / 2) =
            (u ^ (n + 1) + (u⁻¹) ^ (n + 1)) / 2 := by
        simpa only [Nat.cast_add, Nat.cast_one] using h1
      rw [show ((n + 2 : ℕ) : ℤ) = (n : ℤ) + 2 by omega]
      rw [Polynomial.Chebyshev.T_add_two]
      simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_ofNat,
        Polynomial.eval_X, h0, h1']
      simp only [pow_succ]
      field_simp [hu]
      ring

/-- Cayley coordinate that compactifies the real spectral line to the hard edge `[-1, 1]`. -/
def xiHardEdgeCayleyCoordinate (a α : ℂ) : ℂ :=
  (a ^ (2 : ℕ) - α ^ (2 : ℕ)) / (a ^ (2 : ℕ) + α ^ (2 : ℕ))

/-- Unimodular Cayley phase whose real part is the hard-edge coordinate. -/
def xiHardEdgeCayleyPhase (a α : ℂ) : ℂ :=
  (a + Complex.I * α) / (a - Complex.I * α)

private theorem xiHardEdgeCayleyPhase_inv (a α : ℂ) :
    (xiHardEdgeCayleyPhase a α)⁻¹ =
      (a - Complex.I * α) / (a + Complex.I * α) := by
  rw [xiHardEdgeCayleyPhase]
  exact inv_div _ _

private theorem xiHardEdgeCayleyCoordinate_eq_phase_add_inv
    {a α : ℂ} (hplus : a + Complex.I * α ≠ 0)
    (hminus : a - Complex.I * α ≠ 0) :
    xiHardEdgeCayleyCoordinate a α =
      (xiHardEdgeCayleyPhase a α + (xiHardEdgeCayleyPhase a α)⁻¹) / 2 := by
  have hprod : (a + Complex.I * α) * (a - Complex.I * α) =
      a ^ (2 : ℕ) + α ^ (2 : ℕ) := by
    rw [show Complex.I * α = α * Complex.I by ring]
    ring_nf
    rw [Complex.I_sq]
    ring
  have hden : a ^ (2 : ℕ) + α ^ (2 : ℕ) ≠ 0 := by
    rw [← hprod]
    exact mul_ne_zero hplus hminus
  have hprod' : (a + α * Complex.I) * (a - α * Complex.I) =
      a ^ (2 : ℕ) + α ^ (2 : ℕ) := by
    simpa only [mul_comm α Complex.I] using hprod
  rw [xiHardEdgeCayleyCoordinate, xiHardEdgeCayleyPhase, inv_div]
  field_simp [hplus, hminus, hden, mul_ne_zero hplus hminus]
  rw [hprod']
  field_simp [hden]
  ring_nf
  rw [Complex.I_sq]
  ring

/-- Exact Cayley--Chebyshev identity. This is the algebraic hard-edge compactification step. -/
theorem chebyshevT_eval_xiHardEdgeCayleyCoordinate
    {a α : ℂ} (hplus : a + Complex.I * α ≠ 0)
    (hminus : a - Complex.I * α ≠ 0) (n : ℕ) :
    (Polynomial.Chebyshev.T ℂ (n : ℤ)).eval
        (xiHardEdgeCayleyCoordinate a α) =
      ((a + Complex.I * α) / (a - Complex.I * α)) ^ n / 2 +
        ((a - Complex.I * α) / (a + Complex.I * α)) ^ n / 2 := by
  have hphase : xiHardEdgeCayleyPhase a α ≠ 0 :=
    div_ne_zero hplus hminus
  rw [xiHardEdgeCayleyCoordinate_eq_phase_add_inv hplus hminus,
    chebyshevT_eval_add_inv_div_two _ hphase n,
    xiHardEdgeCayleyPhase_inv]
  rw [xiHardEdgeCayleyPhase]
  ring

/-- Pullback of a hard-edge polynomial to the shifted reciprocal-square coordinate. -/
def xiHardEdgeReciprocalPolynomial (a : ℝ) (P : Polynomial ℝ) : Polynomial ℝ :=
  P.comp (Polynomial.C (2 * a ^ (2 : ℕ)) * Polynomial.X - Polynomial.C 1)

theorem evalRealPolynomial_xiHardEdgeReciprocalPolynomial
    (a : ℝ) (P : Polynomial ℝ) (z : ℂ) :
    evalRealPolynomial (xiHardEdgeReciprocalPolynomial a P) z =
      evalRealPolynomial P (((2 * a ^ (2 : ℕ) : ℝ) : ℂ) * z - 1) := by
  simp only [xiHardEdgeReciprocalPolynomial, evalRealPolynomial,
    Polynomial.eval_map, Polynomial.eval₂_comp, Polynomial.eval₂_sub,
    Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X]
  congr 1

/-- A shifted reciprocal-square Xi atom is exactly the hard-edge Cayley coordinate after
the affine change `z ↦ 2a²z - 1`. -/
theorem xiHardEdgeCayleyCoordinate_xiSpectralPoint
    (a : ℝ) (q : XiZeroCopy) :
    xiHardEdgeCayleyCoordinate (a : ℂ) (xiSpectralPoint q) =
      ((2 * a ^ (2 : ℕ) : ℝ) : ℂ) *
          xiShiftedReciprocalSquare (a ^ (2 : ℕ)) q - 1 := by
  have hshift := xiShiftedReciprocalSquare_eq_inv (sq_nonneg a) q
  rw [hshift, xiSquaredNode]
  rw [xiHardEdgeCayleyCoordinate]
  have hden : ((a ^ (2 : ℕ) : ℝ) : ℂ) + xiSpectralPoint q ^ (2 : ℕ) ≠ 0 :=
    ofReal_add_xiSquaredNode_ne_zero (sq_nonneg a) q
  push_cast at hden ⊢
  rw [← div_eq_mul_inv]
  field_simp [hden]
  ring

/-- One multiplicity-labelled term of the mass-scaled hard-edge divisor packet. -/
def xiHardEdgeDivisorPacketTerm
    (a : ℝ) (P : Polynomial ℝ) (q : XiZeroCopy) : ℂ :=
  ((a ^ (2 : ℕ) : ℝ) : ℂ) * xiShiftedReciprocalSquare (a ^ (2 : ℕ)) q *
    evalRealPolynomial P
      (xiHardEdgeCayleyCoordinate (a : ℂ) (xiSpectralPoint q)) ^ (2 : ℕ)

theorem xiHardEdgeDivisorPacketTerm_eq_traceTerm
    (a : ℝ) (P : Polynomial ℝ) (q : XiZeroCopy) :
    xiHardEdgeDivisorPacketTerm a P q =
      ((a ^ (2 : ℕ) : ℝ) : ℂ) *
        xiShiftedReciprocalTraceHankelTerm (a ^ (2 : ℕ))
          (xiHardEdgeReciprocalPolynomial a P) q := by
  rw [xiHardEdgeDivisorPacketTerm, xiShiftedReciprocalTraceHankelTerm,
    evalRealPolynomial_xiHardEdgeReciprocalPolynomial,
    ← xiHardEdgeCayleyCoordinate_xiSpectralPoint a q]
  ring

theorem summable_xiHardEdgeDivisorPacketTerm
    (a : ℝ) (P : Polynomial ℝ) :
    Summable (xiHardEdgeDivisorPacketTerm a P) := by
  refine (summable_xiShiftedReciprocalTraceHankelTerm (sq_nonneg a)
    (xiHardEdgeReciprocalPolynomial a P)).mul_left (((a ^ (2 : ℕ) : ℝ) : ℂ)) |>.congr ?_
  intro q
  exact (xiHardEdgeDivisorPacketTerm_eq_traceTerm a P q).symm

theorem tsum_xiHardEdgeDivisorPacketTerm_eq_traceHankel
    (a : ℝ) (P : Polynomial ℝ) :
    (∑' q : XiZeroCopy, xiHardEdgeDivisorPacketTerm a P q) =
      ((a ^ (2 : ℕ) : ℝ) : ℂ) *
        xiShiftedReciprocalTraceHankel (a ^ (2 : ℕ))
          (xiHardEdgeReciprocalPolynomial a P) := by
  rw [xiShiftedReciprocalTraceHankel, ← tsum_mul_left]
  exact tsum_congr (xiHardEdgeDivisorPacketTerm_eq_traceTerm a P)

/-- Number of coefficients needed to encode the pulled-back hard-edge polynomial exactly. -/
def xiHardEdgeLiftSize (a : ℝ) (P : Polynomial ℝ) : ℕ :=
  (xiHardEdgeReciprocalPolynomial a P).natDegree + 1

theorem natDegree_xiHardEdgeReciprocalPolynomial_le
    (a : ℝ) (P : Polynomial ℝ) :
    (xiHardEdgeReciprocalPolynomial a P).natDegree ≤ P.natDegree := by
  have hlinear :
      (Polynomial.C (2 * a ^ (2 : ℕ)) * Polynomial.X - Polynomial.C 1).natDegree ≤ 1 := by
    have hmul : (Polynomial.C (2 * a ^ (2 : ℕ)) * Polynomial.X : Polynomial ℝ).natDegree ≤ 1 := by
      simpa only [Polynomial.natDegree_X] using
        Polynomial.natDegree_C_mul_le (2 * a ^ (2 : ℕ)) (Polynomial.X : Polynomial ℝ)
    exact (Polynomial.natDegree_sub_le _ _).trans (max_le hmul (by simp))
  calc
    (xiHardEdgeReciprocalPolynomial a P).natDegree ≤
        P.natDegree *
          (Polynomial.C (2 * a ^ (2 : ℕ)) * Polynomial.X - Polynomial.C 1).natDegree := by
      exact Polynomial.natDegree_comp_le
    _ ≤ P.natDegree * 1 := Nat.mul_le_mul_left P.natDegree hlinear
    _ = P.natDegree := Nat.mul_one _

theorem xiHardEdgeLiftSize_le_natDegree_add_one
    (a : ℝ) (P : Polynomial ℝ) :
    xiHardEdgeLiftSize a P ≤ P.natDegree + 1 := by
  exact Nat.add_le_add_right (natDegree_xiHardEdgeReciprocalPolynomial_le a P) 1

/-- Coefficient vector of the exact reciprocal-square pullback. -/
def xiHardEdgeLiftCoefficients (a : ℝ) (P : Polynomial ℝ) :
    Fin (xiHardEdgeLiftSize a P) → ℝ :=
  Polynomial.toFn (xiHardEdgeLiftSize a P) (xiHardEdgeReciprocalPolynomial a P)

theorem ofFn_xiHardEdgeLiftCoefficients
    (a : ℝ) (P : Polynomial ℝ) :
    Polynomial.ofFn (xiHardEdgeLiftSize a P) (xiHardEdgeLiftCoefficients a P) =
      xiHardEdgeReciprocalPolynomial a P := by
  exact Polynomial.ofFn_comp_toFn_eq_id_of_natDegree_lt (Nat.lt_succ_self _)

theorem xiShiftedReciprocalHankelQuadratic_xiHardEdgeLiftCoefficients_eq_trace_re
    (a : ℝ) (P : Polynomial ℝ) :
    xiShiftedReciprocalHankelQuadratic (a ^ (2 : ℕ))
        (xiHardEdgeLiftCoefficients a P) =
      (xiShiftedReciprocalTraceHankel (a ^ (2 : ℕ))
        (xiHardEdgeReciprocalPolynomial a P)).re := by
  have htrace := xiShiftedReciprocalTraceHankel_X_pow_mul_ofFn
    (sq_nonneg a) 0 (xiHardEdgeLiftSize a P) (xiHardEdgeLiftCoefficients a P)
  simp only [pow_zero, one_mul, ofFn_xiHardEdgeLiftCoefficients, Nat.mul_zero,
    Nat.zero_add] at htrace
  rw [xiShiftedReciprocalHankelQuadratic]
  rw [htrace]
  simp only [Complex.re_sum, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]

/-- **Exact hard-edge lift of the shifted-Xi Hankel form.** The finite reciprocal polynomial
quadratic is literally the complete multiplicity-labelled Cayley divisor packet. This theorem is
premise-free: it holds for every real mass scale and every real hard-edge polynomial. -/
theorem xiHardEdgeLift_hankelQuadratic_eq_divisorPacket
    (a : ℝ) (P : Polynomial ℝ) :
    a ^ (2 : ℕ) * xiShiftedReciprocalHankelQuadratic (a ^ (2 : ℕ))
        (xiHardEdgeLiftCoefficients a P) =
      (∑' q : XiZeroCopy, xiHardEdgeDivisorPacketTerm a P q).re := by
  rw [xiShiftedReciprocalHankelQuadratic_xiHardEdgeLiftCoefficients_eq_trace_re,
    tsum_xiHardEdgeDivisorPacketTerm_eq_traceHankel]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

end RHTower
