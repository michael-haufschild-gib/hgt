import GaloisForLFunctions.RHTower.XiShiftedHardEdgeAdaptiveArithmeticSourceLaw
import GaloisForLFunctions.RHTower.XiShiftedHankelNullPolynomialRoots

/-!
# Reciprocal clearing preserves hard-edge real-rootedness

The canonical first-contact compactness route moves a finite Hankel null polynomial from the
reciprocal coordinate into the translated hard coordinate by

`S(U) = (P.reflect N)(U + y)`.

This file classifies every complex zero of `S`, including the exceptional pole `U = -y` that is
lost by informal division.  Away from that pole, zeros are exactly reciprocal images of zeros of
`P`.  At the pole, the value is exactly the depth-`N` coefficient of `P`.

It follows symbolically that reciprocal clearing preserves real-rootedness.  At a first singular
shifted-Xi Hankel face the terminal coefficient is nonzero, so the exceptional pole cannot occur;
every hard-edge zero is the reciprocal image of an actual real-simple null-polynomial zero.  This
is the finite algebraic input required by the Laguerre--Pólya first-contact limit route.
-/

open Complex Matrix Polynomial

namespace RHTower

noncomputable section

/-- Complex evaluation of reciprocal clearing is evaluation of the reflected complex polynomial
at the translated hard coordinate. -/
theorem evalRealPolynomial_xiShiftedHardEdgeReciprocalClearing
    (P : Polynomial ℝ) (N : ℕ) (y : ℝ) (u : ℂ) :
    evalRealPolynomial (xiShiftedHardEdgeReciprocalClearing y N P) u =
      ((P.map (algebraMap ℝ ℂ)).reflect N).eval (u + y) := by
  simp [evalRealPolynomial, xiShiftedHardEdgeReciprocalClearing,
    Polynomial.reflect_map]

/-- The value at the reciprocal-chart pole is exactly the coefficient at the clearing depth.
This is the degree-drop branch that cannot be discarded by multiplying through a denominator. -/
theorem evalRealPolynomial_xiShiftedHardEdgeReciprocalClearing_neg_mass
    (P : Polynomial ℝ) (N : ℕ) (y : ℝ) :
    evalRealPolynomial (xiShiftedHardEdgeReciprocalClearing y N P) (-(y : ℂ)) =
      (P.coeff N : ℂ) := by
  rw [evalRealPolynomial_xiShiftedHardEdgeReciprocalClearing]
  simp [Polynomial.eval_zero, Polynomial.coeff_reflect, Polynomial.revAt_zero]

/-- **Exact reciprocal-zero classification.** A cleared zero is either the exceptional pole,
detected by the depth coefficient, or the reciprocal image of a genuine zero of `P`. -/
theorem evalRealPolynomial_xiShiftedHardEdgeReciprocalClearing_eq_zero_iff
    {P : Polynomial ℝ} {N : ℕ} (hP : P.natDegree ≤ N)
    (y : ℝ) (u : ℂ) :
    evalRealPolynomial (xiShiftedHardEdgeReciprocalClearing y N P) u = 0 ↔
      if u + (y : ℂ) = 0 then (P.coeff N : ℂ) = 0
      else evalRealPolynomial P (u + (y : ℂ))⁻¹ = 0 := by
  rw [evalRealPolynomial_xiShiftedHardEdgeReciprocalClearing]
  by_cases hw : u + (y : ℂ) = 0
  · rw [if_pos hw, hw]
    simp [Polynomial.eval_zero, Polynomial.coeff_reflect,
      Polynomial.revAt_zero]
  · rw [if_neg hw]
    have hPmap : (P.map (algebraMap ℝ ℂ)).natDegree ≤ N :=
      (Polynomial.natDegree_map_le P (algebraMap ℝ ℂ)).trans hP
    letI : Invertible ((u + (y : ℂ))⁻¹) :=
      invertibleOfNonzero (inv_ne_zero hw)
    have hiff := Polynomial.eval₂_reflect_eq_zero_iff
      (RingHom.id ℂ) ((u + (y : ℂ))⁻¹) N
        (P.map (algebraMap ℝ ℂ)) hPmap
    simpa [evalRealPolynomial, Polynomial.eval₂_eq_eval_map,
      invOf_eq_inv, hw] using hiff

/-- **Reciprocal hyperbolicity transfer.** If all complex zeros of `P` are real, all complex
zeros of its translated depth-`N` reciprocal clearing are real, including any exceptional pole. -/
theorem xiShiftedHardEdgeReciprocalClearing_root_im_eq_zero
    {P : Polynomial ℝ} {N : ℕ} (hP : P.natDegree ≤ N)
    (hreal : ∀ z : ℂ, evalRealPolynomial P z = 0 → z.im = 0)
    (y : ℝ) {u : ℂ}
    (hu : evalRealPolynomial (xiShiftedHardEdgeReciprocalClearing y N P) u = 0) :
    u.im = 0 := by
  have hclass :=
    (evalRealPolynomial_xiShiftedHardEdgeReciprocalClearing_eq_zero_iff hP y u).mp hu
  by_cases hw : u + (y : ℂ) = 0
  · have hu_eq : u = -(y : ℂ) := eq_neg_of_add_eq_zero_left hw
    rw [hu_eq]
    simp
  · rw [if_neg hw] at hclass
    have hinv_im : ((u + (y : ℂ))⁻¹).im = 0 := hreal _ hclass
    rw [Complex.inv_im] at hinv_im
    have hnorm : 0 < Complex.normSq (u + (y : ℂ)) :=
      Complex.normSq_pos.mpr hw
    have hw_im : (u + (y : ℂ)).im = 0 := by
      field_simp [hnorm.ne'] at hinv_im
      linarith
    simpa using hw_im

/-- At an actual first singular shifted-Xi Hankel face, exact degree and the nonzero terminal
coefficient remove the exceptional pole.  Cleared zeros are precisely reciprocal images of null
polynomial zeros. -/
theorem xiShiftedHankelNullPolynomial_hardEdgeClearing_eq_zero_iff
    (y : ℝ) (n : ℕ) (c : Fin (n + 1) → ℝ)
    (hhead : (xiShiftedMomentHankelMatrix y n).PosDef)
    (hcne : c ≠ 0)
    (hc : xiShiftedMomentHankelMatrix y (n + 1) *ᵥ c = 0)
    (u : ℂ) :
    evalRealPolynomial
        (xiShiftedHardEdgeReciprocalClearing y n
          (xiShiftedHankelNullPolynomial c)) u = 0 ↔
      u + (y : ℂ) ≠ 0 ∧
        evalRealPolynomial (xiShiftedHankelNullPolynomial c)
          (u + (y : ℂ))⁻¹ = 0 := by
  have hdeg : (xiShiftedHankelNullPolynomial c).natDegree = n :=
    xiShiftedHankelNullPolynomial_natDegree y n c hhead hcne hc
  have hcoeff : (xiShiftedHankelNullPolynomial c).coeff n ≠ 0 := by
    have hlast := xiShiftedHankelNullVector_terminal_ne_zero_of_head_posDef
      y n c hhead hcne hc
    change (HTGeometry.finiteHankelNullPolynomial c).coeff n ≠ 0
    rw [HTGeometry.finiteHankelNullPolynomial,
      Polynomial.ofFn_coeff_eq_val_of_lt c (Nat.lt_succ_self n)]
    exact hlast
  rw [evalRealPolynomial_xiShiftedHardEdgeReciprocalClearing_eq_zero_iff hdeg.le y u]
  by_cases hw : u + (y : ℂ) = 0
  · simp [hw, hcoeff]
  · simp [hw]

/-- **Canonical hard-edge real-rootedness.** Reciprocal clearing of every genuine first-face
shifted-Xi null polynomial has no nonreal complex zero. -/
theorem xiShiftedHankelNullPolynomial_hardEdgeClearing_root_im_eq_zero
    (y : ℝ) (n : ℕ) (c : Fin (n + 1) → ℝ)
    (hhead : (xiShiftedMomentHankelMatrix y n).PosDef)
    (hcne : c ≠ 0)
    (hc : xiShiftedMomentHankelMatrix y (n + 1) *ᵥ c = 0)
    {u : ℂ}
    (hu : evalRealPolynomial
      (xiShiftedHardEdgeReciprocalClearing y n
        (xiShiftedHankelNullPolynomial c)) u = 0) :
    u.im = 0 := by
  apply xiShiftedHardEdgeReciprocalClearing_root_im_eq_zero
    (xiShiftedHankelNullPolynomial_natDegree y n c hhead hcne hc).le
    (fun z hz => ?_) y hu
  apply xiShiftedHankelNullPolynomial_root_im_eq_zero y n c hhead hcne hc
  simpa [evalRealPolynomial, Polynomial.aeval_def] using hz

end

end RHTower

