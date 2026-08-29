import GaloisForLFunctions.RHTower.LiEvenCrossCompletedAbelLanding

/-!
# Completed-Abel mass flow for the even Li clock

This module differentiates LI-CAB3's completed Xi-divisor Abel value in squared-mass time.  Every
atom first collapses to the single Chebyshev defect

`(1 - T_[2n+2](c_q(v))) / 4`,  `c_q(v) = 2v / (v + alpha_q^2) - 1`.

The actual shifted-Xi resolvent law then gives `c'_q(v) = (1-c_q(v)^2)/(2v)`.  After proving the
missing Chebyshev derivative identity from the corpus recurrences, the atom velocity becomes the
adjacent-mode flux

`((n+1)/(8v)) * (T_[2n+3](c_q(v)) - T_[2n+1](c_q(v)))`.

A reciprocal-square majorant justifies termwise differentiation of the complete multiplicity-exact
Xi divisor.  Thus LI-CAB4 is reduced to one source-native sign problem, not a generic Cayley
monotonicity claim.  Exact proof chain targeted by that conjecture is:

aggregate adjacent flux nonnegative on `0 < v <= 1/4`
`=>` completed-Abel flow from its zero-mass anchor is nonnegative at `v = 1/4`
`=>` LI-CAB3 endpoint criterion
`=>` RH.

All results below are unconditional; no sign premise is introduced.
-/

open Polynomial Real Filter Topology

namespace RHTower

noncomputable section

theorem liEvenCrossDivisorAbelTerm_eq_cayleyWeightedSquare
    (a : ℝ) (n : ℕ) (q : XiZeroCopy) :
    liEvenCrossDivisorAbelTerm a n q =
      ((a ^ 2 : ℝ) : ℂ) * xiShiftedReciprocalSquare (a ^ 2) q *
        (1 - xiHardEdgeCayleyCoordinate (a : ℂ) (xiSpectralPoint q)) *
        evalRealPolynomial (liEvenCrossLeftPolynomial n)
          (xiHardEdgeCayleyCoordinate (a : ℂ) (xiSpectralPoint q)) ^ 2 := by
  let c := xiHardEdgeCayleyCoordinate (a : ℂ) (xiSpectralPoint q)
  let P := liEvenCrossLeftPolynomial n
  let Q := liEvenCrossRightPolynomial n
  have hadd : evalRealPolynomial (P + Q) c =
      evalRealPolynomial P c + evalRealPolynomial Q c := by
    simp [evalRealPolynomial]
  have hsub : evalRealPolynomial (P - Q) c =
      evalRealPolynomial P c - evalRealPolynomial Q c := by
    simp [evalRealPolynomial]
  have hQ : evalRealPolynomial Q c = (1 - c) * evalRealPolynomial P c := by
    simp [Q, P, liEvenCrossRightPolynomial, evalRealPolynomial]
  rw [liEvenCrossDivisorAbelTerm, xiHardEdgeDivisorPacketTerm,
    xiHardEdgeDivisorPacketTerm, hadd, hsub, hQ]
  change _ = _ * (1 - c) * evalRealPolynomial P c ^ 2
  ring

theorem liEvenCrossDivisorAbelTerm_eq_chebyshevSquareDefect
    (a : ℝ) (n : ℕ) (q : XiZeroCopy) :
    liEvenCrossDivisorAbelTerm a n q =
      (1 - evalRealPolynomial
        (Polynomial.Chebyshev.T ℝ ((n : ℤ) + 1))
          (xiHardEdgeCayleyCoordinate (a : ℂ) (xiSpectralPoint q)) ^ 2) / 2 := by
  rw [liEvenCrossDivisorAbelTerm_eq_cayleyWeightedSquare]
  let c := xiHardEdgeCayleyCoordinate (a : ℂ) (xiSpectralPoint q)
  let z := ((a ^ 2 : ℝ) : ℂ) * xiShiftedReciprocalSquare (a ^ 2) q
  have hc : c = 2 * z - 1 := by
    dsimp only [c, z]
    rw [xiHardEdgeCayleyCoordinate_xiSpectralPoint]
    push_cast
    ring
  have hnorm := congrArg (fun P : Polynomial ℝ => evalRealPolynomial P c)
    (chebyshevT_sq_add_one_sub_X_sq_mul_chebyshevU_sq_real n)
  simp [evalRealPolynomial] at hnorm
  have hT : evalRealPolynomial
      (Polynomial.Chebyshev.T ℝ ((n : ℤ) + 1)) c =
      (Polynomial.Chebyshev.T ℂ ((n : ℤ) + 1)).eval c := by
    simp [evalRealPolynomial]
  have hU : evalRealPolynomial
      (Polynomial.Chebyshev.U ℝ (n : ℤ)) c =
      (Polynomial.Chebyshev.U ℂ (n : ℤ)).eval c := by
    simp [evalRealPolynomial]
  rw [← hT, ← hU] at hnorm
  change z * (1 - c) *
      evalRealPolynomial (liEvenCrossLeftPolynomial n) c ^ 2 =
        (1 - evalRealPolynomial
          (Polynomial.Chebyshev.T ℝ ((n : ℤ) + 1)) c ^ 2) / 2
  rw [liEvenCrossLeftPolynomial]
  linear_combination (norm := ring_nf) hnorm / 2 -
    (1 - c) * evalRealPolynomial
      (Polynomial.Chebyshev.U ℝ (n : ℤ)) c ^ 2 * hc / 2

theorem chebyshevT_two_mul_eq_two_mul_sq_sub_one (m : ℕ) :
    Polynomial.Chebyshev.T ℝ (2 * (m : ℤ)) =
      2 * (Polynomial.Chebyshev.T ℝ (m : ℤ)) ^ 2 - 1 := by
  have h := Polynomial.Chebyshev.T_mul_T ℝ (m : ℤ) (m : ℤ)
  simp at h
  linear_combination (norm := ring_nf) -h

theorem liEvenCrossDivisorAbelTerm_eq_singleChebyshevDefect
    (a : ℝ) (n : ℕ) (q : XiZeroCopy) :
    liEvenCrossDivisorAbelTerm a n q =
      (1 - evalRealPolynomial
        (Polynomial.Chebyshev.T ℝ (2 * ((n : ℤ) + 1)))
          (xiHardEdgeCayleyCoordinate (a : ℂ) (xiSpectralPoint q))) / 4 := by
  rw [liEvenCrossDivisorAbelTerm_eq_chebyshevSquareDefect]
  let c := xiHardEdgeCayleyCoordinate (a : ℂ) (xiSpectralPoint q)
  have hpoly : Polynomial.Chebyshev.T ℝ (2 * ((n : ℤ) + 1)) =
      2 * (Polynomial.Chebyshev.T ℝ ((n : ℤ) + 1)) ^ 2 - 1 := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      chebyshevT_two_mul_eq_two_mul_sq_sub_one (n + 1)
  change (1 - evalRealPolynomial
      (Polynomial.Chebyshev.T ℝ ((n : ℤ) + 1)) c ^ 2) / 2 =
    (1 - evalRealPolynomial
      (Polynomial.Chebyshev.T ℝ (2 * ((n : ℤ) + 1))) c) / 4
  rw [hpoly]
  simp [evalRealPolynomial]
  ring

/-- Cayley coordinate in squared-mass time. -/
def liEvenCrossCayleyAtSquareMass (v : ℝ) (q : XiZeroCopy) : ℂ :=
  ((2 * v : ℝ) : ℂ) * xiShiftedReciprocalSquare v q - 1

/-- One completed-Abel Xi atom in squared-mass time. -/
def liEvenCrossSquareMassAtom (v : ℝ) (n : ℕ) (q : XiZeroCopy) : ℂ :=
  (1 - evalRealPolynomial
    (Polynomial.Chebyshev.T ℝ (2 * ((n : ℤ) + 1)))
      (liEvenCrossCayleyAtSquareMass v q)) / 4

theorem liEvenCrossSquareMassAtom_sq (a : ℝ) (n : ℕ) (q : XiZeroCopy) :
    liEvenCrossSquareMassAtom (a ^ 2) n q =
      liEvenCrossDivisorAbelTerm a n q := by
  rw [liEvenCrossDivisorAbelTerm_eq_singleChebyshevDefect]
  simp only [liEvenCrossSquareMassAtom]
  congr 3
  rw [xiHardEdgeCayleyCoordinate_xiSpectralPoint]
  simp [liEvenCrossCayleyAtSquareMass]

theorem summable_liEvenCrossDivisorAbelTerm (a : ℝ) (n : ℕ) :
    Summable (liEvenCrossDivisorAbelTerm a n) := by
  let P := liEvenCrossLeftPolynomial n + liEvenCrossRightPolynomial n
  let Q := liEvenCrossLeftPolynomial n - liEvenCrossRightPolynomial n
  have hp := summable_xiHardEdgeDivisorPacketTerm a P
  have hq := summable_xiHardEdgeDivisorPacketTerm a Q
  refine (hp.sub hq).mul_left (1 / 4 : ℂ) |>.congr ?_
  intro q
  simp only [liEvenCrossDivisorAbelTerm, P, Q]
  ring

theorem summable_liEvenCrossSquareMassAtom
    {v : ℝ} (hv : 0 ≤ v) (n : ℕ) :
    Summable (liEvenCrossSquareMassAtom v n) := by
  have hs := summable_liEvenCrossDivisorAbelTerm (Real.sqrt v) n
  refine hs.congr (fun q => ?_)
  rw [← liEvenCrossSquareMassAtom_sq]
  rw [Real.sq_sqrt hv]

def liEvenCrossSquareMassValue (v : ℝ) (n : ℕ) : ℂ :=
  ∑' q : XiZeroCopy, liEvenCrossSquareMassAtom v n q

theorem liEvenCrossSquareMassAtom_zero (n : ℕ) (q : XiZeroCopy) :
    liEvenCrossSquareMassAtom 0 n q = 0 := by
  simp [liEvenCrossSquareMassAtom, liEvenCrossCayleyAtSquareMass,
    evalRealPolynomial]

theorem liEvenCrossSquareMassValue_zero (n : ℕ) :
    liEvenCrossSquareMassValue 0 n = 0 := by
  simp [liEvenCrossSquareMassValue, liEvenCrossSquareMassAtom_zero]

theorem continuousAt_liEvenCrossSquareMassAtom_zero (n : ℕ) (q : XiZeroCopy) :
    ContinuousAt (fun v : ℝ => liEvenCrossSquareMassAtom v n q) 0 := by
  have hcast : ContinuousAt (fun v : ℝ => ((v : ℝ) : ℂ)) 0 :=
    Complex.continuous_ofReal.continuousAt
  have hden : ContinuousAt
      (fun v : ℝ => 1 + (v : ℂ) * xiZeroCopyReciprocalSquare q) 0 :=
    continuousAt_const.add (hcast.mul continuousAt_const)
  have hlam : ContinuousAt (fun v : ℝ => xiShiftedReciprocalSquare v q) 0 := by
    rw [show (fun v : ℝ => xiShiftedReciprocalSquare v q) =
        fun v : ℝ => xiZeroCopyReciprocalSquare q /
          (1 + (v : ℂ) * xiZeroCopyReciprocalSquare q) by
      funext v
      rfl]
    exact continuousAt_const.div hden (by simp)
  have hmass : ContinuousAt (fun v : ℝ => ((2 * v : ℝ) : ℂ)) 0 := by
    fun_prop
  have hcoord : ContinuousAt (fun v : ℝ => liEvenCrossCayleyAtSquareMass v q) 0 := by
    have hfun : (fun v : ℝ => liEvenCrossCayleyAtSquareMass v q) =
        ((fun v : ℝ => ((2 * v : ℝ) : ℂ)) *
          fun v : ℝ => xiShiftedReciprocalSquare v q) - fun _ => 1 := by
      funext v
      rfl
    rw [hfun]
    exact (hmass.mul hlam).sub continuousAt_const
  have heval : ContinuousAt (fun v : ℝ => evalRealPolynomial
      (Polynomial.Chebyshev.T ℝ (2 * ((n : ℤ) + 1)))
        (liEvenCrossCayleyAtSquareMass v q)) 0 := by
    change ContinuousAt (fun v : ℝ =>
      ((Polynomial.Chebyshev.T ℝ (2 * ((n : ℤ) + 1))).map
        (algebraMap ℝ ℂ)).eval (liEvenCrossCayleyAtSquareMass v q)) 0
    rw [ContinuousAt]
    exact (Polynomial.continuous _).continuousAt.tendsto.comp hcoord
  simpa only [liEvenCrossSquareMassAtom, Pi.sub_apply, Pi.div_apply] using
    (continuousAt_const.sub heval).div_const 4

theorem liEvenCrossSquareMassValue_sq (a : ℝ) (n : ℕ) :
    liEvenCrossSquareMassValue (a ^ 2) n =
      liEvenCrossDivisorAbelValue a n := by
  rw [liEvenCrossSquareMassValue, liEvenCrossDivisorAbelValue_eq_tsum_term]
  exact tsum_congr (liEvenCrossSquareMassAtom_sq a n)

theorem hasDerivAt_liEvenCrossCayleyAtSquareMass
    {v : ℝ} (hv : 0 < v) (q : XiZeroCopy) :
    HasDerivAt (fun t : ℝ => liEvenCrossCayleyAtSquareMass t q)
      ((1 - liEvenCrossCayleyAtSquareMass v q ^ 2) / (2 * v)) v := by
  have ht : HasDerivAt (fun t : ℝ => ((t : ℝ) : ℂ)) (1 : ℂ) v := by
    simpa using (hasDerivAt_id v).ofReal_comp
  have hlam := hasDerivAt_xiShiftedReciprocalSquare_pow hv q 0
  have hprod := (ht.const_mul (2 : ℂ)).mul hlam
  have hraw : HasDerivAt (fun t : ℝ => liEvenCrossCayleyAtSquareMass t q)
      (2 * xiShiftedReciprocalSquare v q *
        (1 - (v : ℂ) * xiShiftedReciprocalSquare v q)) v := by
    have hh := (hprod.sub_const 1).congr_deriv
      (show _ = 2 * xiShiftedReciprocalSquare v q *
          (1 - (v : ℂ) * xiShiftedReciprocalSquare v q) by
        norm_num
        ring)
    simpa [liEvenCrossCayleyAtSquareMass, mul_assoc, mul_comm, mul_left_comm] using hh
  convert hraw using 1
  have hvC : (v : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hv
  rw [liEvenCrossCayleyAtSquareMass]
  push_cast
  field_simp [hvC]
  ring

theorem hasDerivAt_liEvenCrossCayleyAtSquareMass_resolvent
    {v : ℝ} (hv : 0 < v) (q : XiZeroCopy) :
    HasDerivAt (fun t : ℝ => liEvenCrossCayleyAtSquareMass t q)
      (2 * xiShiftedReciprocalSquare v q *
        (1 - (v : ℂ) * xiShiftedReciprocalSquare v q)) v := by
  refine (hasDerivAt_liEvenCrossCayleyAtSquareMass hv q).congr_deriv ?_
  rw [liEvenCrossCayleyAtSquareMass]
  have hvC : (v : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hv
  push_cast
  field_simp [hvC]
  ring

private theorem hasDerivAt_complexPolynomial_eval_comp
    {p : Polynomial ℂ} {z : ℝ → ℂ} {z' : ℂ} {u : ℝ}
    (hz : HasDerivAt z z' u) :
    HasDerivAt (fun v : ℝ => p.eval (z v))
      (p.derivative.eval (z u) * z') u := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      apply HasDerivAt.of_isLittleO
      simpa [Polynomial.eval_add, Polynomial.derivative_add, add_mul] using
        (hp.add hq).isLittleO
  | monomial n a =>
      simpa [Polynomial.eval_monomial, Polynomial.derivative_monomial, mul_assoc,
        mul_left_comm, mul_comm] using (hz.pow n).const_mul a

theorem hasDerivAt_evalRealPolynomial_comp
    {p : Polynomial ℝ} {z : ℝ → ℂ} {z' : ℂ} {u : ℝ}
    (hz : HasDerivAt z z' u) :
    HasDerivAt (fun v : ℝ => evalRealPolynomial p (z v))
      (evalRealPolynomial p.derivative (z u) * z') u := by
  simpa [evalRealPolynomial, Polynomial.derivative_map] using
    (hasDerivAt_complexPolynomial_eval_comp
      (p := p.map (algebraMap ℝ ℂ)) hz)

theorem derivative_chebyshevT_succ (n : ℕ) :
    (Polynomial.Chebyshev.T ℝ ((n : ℤ) + 1)).derivative =
      Polynomial.C ((n : ℝ) + 1) * Polynomial.Chebyshev.U ℝ (n : ℤ) := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one =>
      rw [show ((1 : ℕ) : ℤ) + 1 = 0 + 2 by norm_num,
        Polynomial.Chebyshev.T_add_two]
      simp
      ring
  | more n h0 h1 =>
      have hrecT := congrArg Polynomial.derivative
        (Polynomial.Chebyshev.T_add_two ℝ ((n : ℤ) + 1))
      simp only [Polynomial.derivative_sub, Polynomial.derivative_mul,
        Polynomial.derivative_ofNat, Polynomial.derivative_X] at hrecT
      have hU := Polynomial.Chebyshev.U_eq_X_mul_U_add_T ℝ ((n : ℤ) + 1)
      have hU' : Polynomial.Chebyshev.U ℝ ((n : ℤ) + 2) =
          X * Polynomial.Chebyshev.U ℝ ((n : ℤ) + 1) +
            Polynomial.Chebyshev.T ℝ ((n : ℤ) + 2) := by
        simpa only [show (n : ℤ) + 1 + 1 = (n : ℤ) + 2 by ring] using hU
      have hUrec := Polynomial.Chebyshev.U_add_two ℝ (n : ℤ)
      have hTU : Polynomial.Chebyshev.T ℝ ((n : ℤ) + 2) =
          X * Polynomial.Chebyshev.U ℝ ((n : ℤ) + 1) -
            Polynomial.Chebyshev.U ℝ (n : ℤ) := by
        linear_combination (norm := ring_nf) hUrec - hU
      simp only [Nat.cast_add, Nat.cast_one] at h1
      rw [show (((n + 2 : ℕ) : ℤ) + 1) = (n : ℤ) + 3 by omega]
      rw [show ((n : ℤ) + 3) = ((n : ℤ) + 1) + 2 by ring, hrecT]
      rw [show ((n + 2 : ℕ) : ℝ) + 1 = (n : ℝ) + 3 by push_cast; ring]
      rw [show ((n + 2 : ℕ) : ℤ) = (n : ℤ) + 2 by omega]
      rw [h0, h1]
      rw [show (n : ℤ) + 1 + 1 = (n : ℤ) + 2 by ring]
      rw [hU', hTU]
      simp only [map_add, map_ofNat, map_one]
      ring

theorem two_mul_one_sub_X_sq_mul_chebyshevU_eq_T_sub_T_add_two (k : ℕ) :
    2 * (1 - X ^ 2) * Polynomial.Chebyshev.U ℝ (k : ℤ) =
      Polynomial.Chebyshev.T ℝ (k : ℤ) -
        Polynomial.Chebyshev.T ℝ ((k : ℤ) + 2) := by
  have hrec := Polynomial.Chebyshev.T_add_two ℝ (k : ℤ)
  have hmix := Polynomial.Chebyshev.T_eq_X_mul_T_sub_pol_U ℝ (k : ℤ)
  linear_combination (norm := ring_nf) 2 * hmix - hrec

theorem hasDerivAt_liEvenCrossSquareMassAtom
    {v : ℝ} (hv : 0 < v) (n : ℕ) (q : XiZeroCopy) :
    HasDerivAt
      (fun t : ℝ =>
        (1 - evalRealPolynomial
          (Polynomial.Chebyshev.T ℝ (2 * ((n : ℤ) + 1)))
            (liEvenCrossCayleyAtSquareMass t q)) / 4)
      (-(evalRealPolynomial
          (Polynomial.Chebyshev.T ℝ (2 * ((n : ℤ) + 1))).derivative
            (liEvenCrossCayleyAtSquareMass v q) *
          ((1 - liEvenCrossCayleyAtSquareMass v q ^ 2) / (2 * v))) / 4) v := by
  have hpoly := hasDerivAt_evalRealPolynomial_comp
    (p := Polynomial.Chebyshev.T ℝ (2 * ((n : ℤ) + 1)))
    (hasDerivAt_liEvenCrossCayleyAtSquareMass hv q)
  have hbase := (hasDerivAt_const v (1 : ℂ)).sub hpoly |>.div_const 4
  have hder :
      (0 - evalRealPolynomial
          (Polynomial.Chebyshev.T ℝ (2 * ((n : ℤ) + 1))).derivative
            (liEvenCrossCayleyAtSquareMass v q) *
          ((1 - liEvenCrossCayleyAtSquareMass v q ^ 2) / (2 * v))) / 4 =
        -(evalRealPolynomial
          (Polynomial.Chebyshev.T ℝ (2 * ((n : ℤ) + 1))).derivative
            (liEvenCrossCayleyAtSquareMass v q) *
          ((1 - liEvenCrossCayleyAtSquareMass v q ^ 2) / (2 * v))) / 4 := by
    ring
  have hh := hbase.congr_deriv hder
  simpa only [Pi.sub_apply] using hh

/-- Resolvent form of the atom velocity; unlike the Cayley quotient form, it visibly carries one
summable reciprocal-square factor. -/
def liEvenCrossSquareMassAtomVelocity
    (v : ℝ) (n : ℕ) (q : XiZeroCopy) : ℂ :=
  -(evalRealPolynomial
      (Polynomial.Chebyshev.T ℝ (2 * ((n : ℤ) + 1))).derivative
        (liEvenCrossCayleyAtSquareMass v q) *
      (2 * xiShiftedReciprocalSquare v q *
        (1 - (v : ℂ) * xiShiftedReciprocalSquare v q))) / 4

theorem hasDerivAt_liEvenCrossSquareMassAtom_resolvent
    {v : ℝ} (hv : 0 < v) (n : ℕ) (q : XiZeroCopy) :
    HasDerivAt (fun t : ℝ => liEvenCrossSquareMassAtom t n q)
      (liEvenCrossSquareMassAtomVelocity v n q) v := by
  have hpoly := hasDerivAt_evalRealPolynomial_comp
    (p := Polynomial.Chebyshev.T ℝ (2 * ((n : ℤ) + 1)))
    (hasDerivAt_liEvenCrossCayleyAtSquareMass_resolvent hv q)
  have hbase := (hasDerivAt_const v (1 : ℂ)).sub hpoly |>.div_const 4
  have hder :
      (0 - evalRealPolynomial
          (Polynomial.Chebyshev.T ℝ (2 * ((n : ℤ) + 1))).derivative
            (liEvenCrossCayleyAtSquareMass v q) *
          (2 * xiShiftedReciprocalSquare v q *
            (1 - (v : ℂ) * xiShiftedReciprocalSquare v q))) / 4 =
        liEvenCrossSquareMassAtomVelocity v n q := by
    simp [liEvenCrossSquareMassAtomVelocity]
  have hh := hbase.congr_deriv hder
  simpa only [Pi.sub_apply, liEvenCrossSquareMassAtom] using hh

def liEvenCrossSquareMassDerivativeMajorant
    (y : ℝ) (n : ℕ) (q : XiZeroCopy) : ℝ :=
  (evalRealPolynomialNormBound
      (Polynomial.Chebyshev.T ℝ (2 * ((n : ℤ) + 1))).derivative
      (3 * y + 1) * (1 + 3 * y / 2) / 2) *
    ‖xiZeroCopyReciprocalSquare q‖

theorem summable_liEvenCrossSquareMassDerivativeMajorant
    (y : ℝ) (n : ℕ) :
    Summable (liEvenCrossSquareMassDerivativeMajorant y n) := by
  exact summable_norm_xiZeroCopyReciprocalSquare.mul_left _

theorem norm_liEvenCrossSquareMassAtomVelocity_le_majorant
    {y v : ℝ} (hy : 0 < y) (hv : v ∈ Set.Ioo (y / 2) (3 * y / 2))
    (n : ℕ) (q : XiZeroCopy) :
    ‖liEvenCrossSquareMassAtomVelocity v n q‖ ≤
      liEvenCrossSquareMassDerivativeMajorant y n q := by
  have hv0 : 0 ≤ v := by linarith [hv.1]
  have hvTop : v ≤ 3 * y / 2 := hv.2.le
  have hlam := norm_xiShiftedReciprocalSquare_le hv0 q
  have hzero : ‖xiZeroCopyReciprocalSquare q‖ ≤ 1 := by
    exact (le_of_lt (norm_xiZeroCopyReciprocalSquare_lt_two_over_fortyOne q)).trans
      (by norm_num)
  have hlamOne : ‖xiShiftedReciprocalSquare v q‖ ≤ 1 := hlam.trans hzero
  have hc : ‖liEvenCrossCayleyAtSquareMass v q‖ ≤ 3 * y + 1 := by
    rw [liEvenCrossCayleyAtSquareMass]
    calc
      ‖((2 * v : ℝ) : ℂ) * xiShiftedReciprocalSquare v q - 1‖ ≤
          ‖((2 * v : ℝ) : ℂ) * xiShiftedReciprocalSquare v q‖ + ‖(1 : ℂ)‖ :=
        norm_sub_le _ _
      _ = 2 * v * ‖xiShiftedReciprocalSquare v q‖ + 1 := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (by positivity), norm_one]
      _ ≤ 2 * v * 1 + 1 := by gcongr
      _ ≤ 3 * y + 1 := by linarith
  have hpoly := norm_evalRealPolynomial_le
    (Polynomial.Chebyshev.T ℝ (2 * ((n : ℤ) + 1))).derivative hc
  have hone : ‖1 - (v : ℂ) * xiShiftedReciprocalSquare v q‖ ≤
      1 + 3 * y / 2 := by
    calc
      ‖1 - (v : ℂ) * xiShiftedReciprocalSquare v q‖ ≤
          ‖(1 : ℂ)‖ + ‖(v : ℂ) * xiShiftedReciprocalSquare v q‖ :=
        norm_sub_le _ _
      _ = 1 + v * ‖xiShiftedReciprocalSquare v q‖ := by
        rw [norm_one, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg hv0]
      _ ≤ 1 + v * 1 := by gcongr
      _ ≤ 1 + 3 * y / 2 := by linarith
  have hpolyNonneg : 0 ≤ evalRealPolynomialNormBound
      (Polynomial.Chebyshev.T ℝ (2 * ((n : ℤ) + 1))).derivative
      (3 * y + 1) :=
    evalRealPolynomialNormBound_nonneg _ (by linarith)
  rw [liEvenCrossSquareMassAtomVelocity, norm_div, norm_neg,
    norm_mul, norm_mul]
  norm_num
  rw [liEvenCrossSquareMassDerivativeMajorant]
  calc
      ‖evalRealPolynomial
          (Polynomial.Chebyshev.T ℝ (2 * ((n : ℤ) + 1))).derivative
          (liEvenCrossCayleyAtSquareMass v q)‖ *
        (2 * ‖xiShiftedReciprocalSquare v q‖ *
          ‖1 - (v : ℂ) * xiShiftedReciprocalSquare v q‖) / 4 ≤
      evalRealPolynomialNormBound
          (Polynomial.Chebyshev.T ℝ (2 * ((n : ℤ) + 1))).derivative
          (3 * y + 1) *
        (2 * ‖xiZeroCopyReciprocalSquare q‖ *
          (1 + 3 * y / 2)) / 4 := by
          gcongr
    _ = _ := by ring

theorem hasDerivAt_liEvenCrossSquareMassAtom_adjacentFlux
    {v : ℝ} (hv : 0 < v) (n : ℕ) (q : XiZeroCopy) :
    HasDerivAt
      (fun t : ℝ =>
        (1 - evalRealPolynomial
          (Polynomial.Chebyshev.T ℝ (2 * ((n : ℤ) + 1)))
            (liEvenCrossCayleyAtSquareMass t q)) / 4)
      ((((n : ℂ) + 1) / (8 * v)) *
        (evalRealPolynomial
            (Polynomial.Chebyshev.T ℝ (2 * ((n : ℤ) + 1) + 1))
              (liEvenCrossCayleyAtSquareMass v q) -
          evalRealPolynomial
            (Polynomial.Chebyshev.T ℝ (2 * ((n : ℤ) + 1) - 1))
              (liEvenCrossCayleyAtSquareMass v q))) v := by
  let c := liEvenCrossCayleyAtSquareMass v q
  have hbase := hasDerivAt_liEvenCrossSquareMassAtom hv n q
  refine hbase.congr_deriv ?_
  have hderiv :
      (Polynomial.Chebyshev.T ℝ (2 * ((n : ℤ) + 1))).derivative =
        Polynomial.C (2 * ((n : ℝ) + 1)) *
          Polynomial.Chebyshev.U ℝ (2 * (n : ℤ) + 1) := by
    have h := derivative_chebyshevT_succ (2 * n + 1)
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_one] at h
    rw [show ((2 : ℕ) : ℤ) * (n : ℤ) + 1 + 1 =
          2 * ((n : ℤ) + 1) by norm_num; ring,
      show ((2 : ℕ) : ℝ) * (n : ℝ) + 1 + 1 =
          2 * ((n : ℝ) + 1) by norm_num; ring,
      show ((2 : ℕ) : ℤ) * (n : ℤ) + 1 =
          2 * (n : ℤ) + 1 by norm_num] at h
    exact h
  have hfluxPoly :=
    two_mul_one_sub_X_sq_mul_chebyshevU_eq_T_sub_T_add_two (2 * n + 1)
  have hflux :
      2 * (1 - c ^ 2) *
          evalRealPolynomial (Polynomial.Chebyshev.U ℝ (2 * (n : ℤ) + 1)) c =
        evalRealPolynomial
            (Polynomial.Chebyshev.T ℝ (2 * (n : ℤ) + 1)) c -
          evalRealPolynomial
            (Polynomial.Chebyshev.T ℝ (2 * (n : ℤ) + 3)) c := by
    have h := congrArg (fun P : Polynomial ℝ => evalRealPolynomial P c) hfluxPoly
    rw [show ((2 * n + 1 : ℕ) : ℤ) = 2 * (n : ℤ) + 1 by omega,
      show 2 * (n : ℤ) + 1 + 2 = 2 * (n : ℤ) + 3 by ring] at h
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_one,
      evalRealPolynomial, Polynomial.map_mul, Polynomial.map_sub,
      Polynomial.map_pow, Polynomial.map_one, Polynomial.map_X,
      Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_pow,
      Polynomial.eval_one, Polynomial.eval_X, Polynomial.map_ofNat,
      Polynomial.eval_ofNat, map_ofNat,
      Polynomial.Chebyshev.map_T, Polynomial.Chebyshev.map_U] using h
  rw [hderiv]
  simp only [evalRealPolynomial_mul]
  have hvC : (v : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hv
  change -(evalRealPolynomial (Polynomial.C (2 * ((n : ℝ) + 1))) c *
        evalRealPolynomial (Polynomial.Chebyshev.U ℝ (2 * (n : ℤ) + 1)) c *
        ((1 - c ^ 2) / (2 * v))) / 4 =
      (((n : ℂ) + 1) / (8 * v)) *
        (evalRealPolynomial
            (Polynomial.Chebyshev.T ℝ (2 * ((n : ℤ) + 1) + 1)) c -
          evalRealPolynomial
            (Polynomial.Chebyshev.T ℝ (2 * ((n : ℤ) + 1) - 1)) c)
  have hC : evalRealPolynomial (Polynomial.C (2 * ((n : ℝ) + 1))) c =
      (2 : ℂ) * ((n : ℂ) + 1) := by
    simp [evalRealPolynomial]
  rw [hC]
  rw [show 2 * ((n : ℤ) + 1) + 1 = 2 * (n : ℤ) + 3 by ring,
    show 2 * ((n : ℤ) + 1) - 1 = 2 * (n : ℤ) + 1 by ring]
  linear_combination (norm := ring_nf)
    -((n : ℂ) + 1) / (8 * (v : ℂ)) * hflux

def liEvenCrossSquareMassAdjacentFlux
    (v : ℝ) (n : ℕ) (q : XiZeroCopy) : ℂ :=
  (((n : ℂ) + 1) / (8 * v)) *
    (evalRealPolynomial
        (Polynomial.Chebyshev.T ℝ (2 * ((n : ℤ) + 1) + 1))
          (liEvenCrossCayleyAtSquareMass v q) -
      evalRealPolynomial
        (Polynomial.Chebyshev.T ℝ (2 * ((n : ℤ) + 1) - 1))
          (liEvenCrossCayleyAtSquareMass v q))

theorem liEvenCrossSquareMassAtomVelocity_eq_adjacentFlux
    {v : ℝ} (hv : 0 < v) (n : ℕ) (q : XiZeroCopy) :
    liEvenCrossSquareMassAtomVelocity v n q =
      liEvenCrossSquareMassAdjacentFlux v n q := by
  exact (hasDerivAt_liEvenCrossSquareMassAtom_resolvent hv n q).unique
    (by simpa only [liEvenCrossSquareMassAtom,
        liEvenCrossSquareMassAdjacentFlux] using
      hasDerivAt_liEvenCrossSquareMassAtom_adjacentFlux hv n q)

theorem summable_liEvenCrossSquareMassAtomVelocity
    {y : ℝ} (hy : 0 < y) (n : ℕ) :
    Summable (liEvenCrossSquareMassAtomVelocity y n) := by
  refine (summable_liEvenCrossSquareMassDerivativeMajorant y n).of_norm_bounded ?_
  intro q
  exact norm_liEvenCrossSquareMassAtomVelocity_le_majorant hy
    (Set.mem_Ioo.mpr ⟨by linarith, by linarith⟩) n q

theorem hasDerivAt_liEvenCrossSquareMassValue
    {y : ℝ} (hy : 0 < y) (n : ℕ) :
    HasDerivAt (fun v : ℝ => liEvenCrossSquareMassValue v n)
      (∑' q : XiZeroCopy, liEvenCrossSquareMassAtomVelocity y n q) y := by
  have hu := summable_liEvenCrossSquareMassDerivativeMajorant y n
  have hderiv : ∀ q : XiZeroCopy, ∀ v ∈ Set.Ioo (y / 2) (3 * y / 2),
      HasDerivAt (fun t : ℝ => liEvenCrossSquareMassAtom t n q)
        (liEvenCrossSquareMassAtomVelocity v n q) v := by
    intro q v hv
    exact hasDerivAt_liEvenCrossSquareMassAtom_resolvent (by linarith [hv.1]) n q
  have hbound : ∀ q : XiZeroCopy, ∀ v ∈ Set.Ioo (y / 2) (3 * y / 2),
      ‖liEvenCrossSquareMassAtomVelocity v n q‖ ≤
        liEvenCrossSquareMassDerivativeMajorant y n q := by
    intro q v hv
    exact norm_liEvenCrossSquareMassAtomVelocity_le_majorant hy hv n q
  have hsum0 := summable_liEvenCrossSquareMassAtom hy.le n
  have hyMem : y ∈ Set.Ioo (y / 2) (3 * y / 2) := by
    constructor <;> linarith
  have hmain := hasDerivAt_tsum_of_isPreconnected hu isOpen_Ioo
    isPreconnected_Ioo hderiv hbound hyMem hsum0 hyMem
  simpa only [liEvenCrossSquareMassValue] using hmain

theorem hasDerivAt_liEvenCrossSquareMassValue_adjacentFlux
    {y : ℝ} (hy : 0 < y) (n : ℕ) :
    HasDerivAt (fun v : ℝ => liEvenCrossSquareMassValue v n)
      (∑' q : XiZeroCopy, liEvenCrossSquareMassAdjacentFlux y n q) y := by
  have h := hasDerivAt_liEvenCrossSquareMassValue hy n
  convert h using 1
  apply tsum_congr
  intro q
  exact (liEvenCrossSquareMassAtomVelocity_eq_adjacentFlux hy n q).symm

theorem hasDerivAt_re_liEvenCrossSquareMassValue_adjacentFlux
    {y : ℝ} (hy : 0 < y) (n : ℕ) :
    HasDerivAt (fun v : ℝ => (liEvenCrossSquareMassValue v n).re)
      ((∑' q : XiZeroCopy, liEvenCrossSquareMassAdjacentFlux y n q).re) y := by
  exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt y
    (hasDerivAt_liEvenCrossSquareMassValue_adjacentFlux hy n)

theorem tendsto_liEvenCrossSquareMassValue_zero_right (n : ℕ) :
    Tendsto (fun v : ℝ => liEvenCrossSquareMassValue v n)
      (𝓝[Set.Ici (0 : ℝ)] 0) (𝓝 0) := by
  have hpoint : ∀ q : XiZeroCopy,
      Tendsto (fun v : ℝ => liEvenCrossSquareMassAtom v n q)
        (𝓝[Set.Ici (0 : ℝ)] 0)
        (𝓝 (liEvenCrossSquareMassAtom 0 n q)) := by
    intro q
    exact (continuousAt_liEvenCrossSquareMassAtom_zero n q).tendsto.mono_left inf_le_left
  have hnonneg : ∀ᶠ v : ℝ in 𝓝[Set.Ici (0 : ℝ)] 0, 0 ≤ v :=
    self_mem_nhdsWithin
  have hupper : ∀ᶠ v : ℝ in 𝓝[Set.Ici (0 : ℝ)] 0, v < 1 := by
    show Set.Iio 1 ∈ 𝓝[Set.Ici (0 : ℝ)] 0
    rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
    refine ⟨Set.Iio 1, Iio_mem_nhds (by norm_num), ?_⟩
    intro v hv
    exact hv.1
  have hbound : ∀ᶠ v : ℝ in 𝓝[Set.Ici (0 : ℝ)] 0, ∀ q : XiZeroCopy,
      ‖liEvenCrossSquareMassAtom v n q‖ ≤
        liEvenCrossDivisorAbelMajorant n q := by
    filter_upwards [hnonneg, hupper] with v hv0 hv1 q
    have hsqrt0 := Real.sqrt_nonneg v
    have hsqrt1 : Real.sqrt v ≤ 1 := by
      nlinarith [Real.sq_sqrt hv0]
    have h := norm_liEvenCrossDivisorAbelTerm_le_majorant
      hsqrt0 hsqrt1 n q
    rw [← liEvenCrossSquareMassAtom_sq] at h
    simpa only [Real.sq_sqrt hv0] using h
  have hlim := tendsto_tsum_of_dominated_convergence
    (summable_liEvenCrossDivisorAbelMajorant n) hpoint hbound
  simpa [liEvenCrossSquareMassValue, liEvenCrossSquareMassAtom_zero] using hlim

end

end RHTower
