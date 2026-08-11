import GaloisForLFunctions.RHTower.XiShiftedAdaptiveAdmissionCovariantSource
import GaloisForLFunctions.RHTower.XiShiftedHankelTerminalFlux
import GaloisForLFunctions.RHTower.XiShiftedHankelBoundaryExtensionClass
import GaloisForLFunctions.HilbertMetric.DeterminantCurvatureJet
import GaloisForLFunctions.HTGeometry.MonicMomentAdmissionNormTransport
import GaloisForLFunctions.HTGeometry.AdaptiveOrthogonalNormJacobiFlow

/-!
# Canonical inverse-Hankel admission connection for shifted Xi

The canonical monic admission is not an externally chosen moving frame.  Its lower coefficients
are the inverse-Hankel solve `-H⁻¹ t`, hence the shifted-Xi moment recursion forces their velocity.
This file differentiates that solve literally and feeds the resulting tangent into the adaptive
source law.  The completed `P^sharp` amplitude therefore carries a canonical arithmetic
connection before any reflection aggregation or fixed linear observation is applied.
-/

open Complex Matrix Polynomial
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Velocity of the terminal column in the canonical monic Hankel solve. -/
def xiShiftedCanonicalAdmissionTailVelocity (y : ℝ) (n : ℕ) : Fin n → ℝ :=
  fun i => -((((i : ℕ) + n : ℕ) : ℝ) + 1) *
    (xiShiftedReciprocalMoment y ((i : ℕ) + n + 1)).re

/-- Forced velocity of the inverse shifted-Xi Hankel block. -/
def xiShiftedCanonicalAdmissionInverseVelocity
    (y : ℝ) (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  -((HTGeometry.momentHankelMatrix
        (fun k => (xiShiftedReciprocalMoment y k).re) n)⁻¹ *
      xiShiftedHankelTransportMatrix y n *
      (HTGeometry.momentHankelMatrix
        (fun k => (xiShiftedReciprocalMoment y k).re) n)⁻¹)

/-- Forced lower-coefficient velocity of the canonical monic admission `-H⁻¹t`. -/
def xiShiftedCanonicalAdmissionLowerVelocity (y : ℝ) (n : ℕ) : Fin n → ℝ :=
  -(xiShiftedCanonicalAdmissionInverseVelocity y n *ᵥ
        HTGeometry.momentHankelTail
          (fun k => (xiShiftedReciprocalMoment y k).re) n +
      (HTGeometry.momentHankelMatrix
          (fun k => (xiShiftedReciprocalMoment y k).re) n)⁻¹ *ᵥ
        xiShiftedCanonicalAdmissionTailVelocity y n)

/-- Full monic coefficient velocity.  Its terminal coordinate is identically zero. -/
def xiShiftedCanonicalAdmissionVelocity (y : ℝ) (n : ℕ) : Fin (n + 1) → ℝ :=
  Fin.snoc (xiShiftedCanonicalAdmissionLowerVelocity y n) 0

/-- Actual coefficient curve of the canonical shifted-Xi monic admission. -/
def xiShiftedCanonicalAdmissionCurve (n : ℕ) : Fin (n + 1) → ℝ → ℝ :=
  fun i y => HTGeometry.monicMomentAdmissionVector
    (fun k => (xiShiftedReciprocalMoment y k).re) n i

theorem hasDerivAt_xiShiftedCanonicalAdmissionTail
    {y : ℝ} (hy : 0 < y) (n : ℕ) (i : Fin n) :
    HasDerivAt
      (fun v => HTGeometry.momentHankelTail
        (fun k => (xiShiftedReciprocalMoment v k).re) n i)
      (xiShiftedCanonicalAdmissionTailVelocity y n i) y := by
  simpa only [HTGeometry.momentHankelTail,
    xiShiftedCanonicalAdmissionTailVelocity] using
      hasDerivAt_re_xiShiftedReciprocalMoment hy ((i : ℕ) + n)

/-- The corpus inverse-matrix jet plus terminal-flux law gives the literal inverse-block
derivative used by the admission solve. -/
theorem hasDerivAt_xiShiftedMomentHankelInverse_entry
    {y : ℝ} (hy : 0 < y) (n : ℕ)
    (hdet : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) n).det ≠ 0)
    (i j : Fin n) :
    HasDerivAt
      (fun v => (HTGeometry.momentHankelMatrix
        (fun k => (xiShiftedReciprocalMoment v k).re) n)⁻¹ i j)
      (xiShiftedCanonicalAdmissionInverseVelocity y n i j) y := by
  have hentry : ∀ a b : Fin n,
      HasDerivAt
        (fun v => HTGeometry.momentHankelMatrix
          (fun k => (xiShiftedReciprocalMoment v k).re) n a b)
        (xiShiftedHankelTransportMatrix y n a b) y := by
    intro a b
    simpa only [xiShiftedMomentHankelMatrix,
      GaloisForLFunctions.HTGeometry.finiteHankelMatrix,
      HTGeometry.momentHankelMatrix] using
        hasDerivAt_xiShiftedMomentHankelMatrix_entry hy n a b
  simpa only [xiShiftedCanonicalAdmissionInverseVelocity, Matrix.neg_apply] using
    GaloisForLFunctions.HilbertMetric.hasDerivAt_matrix_inv
      (fun v => HTGeometry.momentHankelMatrix
        (fun k => (xiShiftedReciprocalMoment v k).re) n)
      (xiShiftedHankelTransportMatrix y n) y hentry hdet i j

/-- Literal derivative of every lower coefficient of canonical `P^sharp`. -/
theorem hasDerivAt_xiShiftedCanonicalAdmissionCoefficient
    {y : ℝ} (hy : 0 < y) (n : ℕ)
    (hdet : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) n).det ≠ 0)
    (i : Fin n) :
    HasDerivAt
      (fun v => HTGeometry.monicMomentAdmissionCoefficients
        (fun k => (xiShiftedReciprocalMoment v k).re) n i)
      (xiShiftedCanonicalAdmissionLowerVelocity y n i) y := by
  have hsum : HasDerivAt
      (fun v => ∑ j : Fin n,
        (HTGeometry.momentHankelMatrix
          (fun k => (xiShiftedReciprocalMoment v k).re) n)⁻¹ i j *
        HTGeometry.momentHankelTail
          (fun k => (xiShiftedReciprocalMoment v k).re) n j)
      (∑ j : Fin n,
        (xiShiftedCanonicalAdmissionInverseVelocity y n i j *
          HTGeometry.momentHankelTail
            (fun k => (xiShiftedReciprocalMoment y k).re) n j +
        (HTGeometry.momentHankelMatrix
          (fun k => (xiShiftedReciprocalMoment y k).re) n)⁻¹ i j *
          xiShiftedCanonicalAdmissionTailVelocity y n j)) y := by
    exact HasDerivAt.fun_sum fun j _ =>
      (hasDerivAt_xiShiftedMomentHankelInverse_entry hy n hdet i j).mul
        (hasDerivAt_xiShiftedCanonicalAdmissionTail hy n j)
  have hcurve :
      (fun v => HTGeometry.monicMomentAdmissionCoefficients
        (fun k => (xiShiftedReciprocalMoment v k).re) n i) =
      (fun v => (-1 : ℝ) * ∑ j : Fin n,
        (HTGeometry.momentHankelMatrix
          (fun k => (xiShiftedReciprocalMoment v k).re) n)⁻¹ i j *
        HTGeometry.momentHankelTail
          (fun k => (xiShiftedReciprocalMoment v k).re) n j) := by
    funext v
    simp only [HTGeometry.monicMomentAdmissionCoefficients, Pi.neg_apply,
      Matrix.mulVec, dotProduct]
    ring
  have hvelocity : xiShiftedCanonicalAdmissionLowerVelocity y n i =
      (-1 : ℝ) * (∑ j : Fin n,
        (xiShiftedCanonicalAdmissionInverseVelocity y n i j *
          HTGeometry.momentHankelTail
            (fun k => (xiShiftedReciprocalMoment y k).re) n j +
        (HTGeometry.momentHankelMatrix
          (fun k => (xiShiftedReciprocalMoment y k).re) n)⁻¹ i j *
          xiShiftedCanonicalAdmissionTailVelocity y n j)) := by
    simp only [xiShiftedCanonicalAdmissionLowerVelocity, Pi.neg_apply, Pi.add_apply,
      Matrix.mulVec, dotProduct, Finset.sum_add_distrib]
    ring
  rw [hcurve, hvelocity]
  exact hsum.const_mul (-1)

/-- Every coordinate of the actual monic coefficient curve has the forced canonical velocity. -/
theorem hasDerivAt_xiShiftedCanonicalAdmissionCurve
    {y : ℝ} (hy : 0 < y) (n : ℕ)
    (hdet : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) n).det ≠ 0)
    (i : Fin (n + 1)) :
    HasDerivAt (xiShiftedCanonicalAdmissionCurve n i)
      (xiShiftedCanonicalAdmissionVelocity y n i) y := by
  refine Fin.lastCases ?_ (fun j => ?_) i
  · have hcurve : xiShiftedCanonicalAdmissionCurve n (Fin.last n) =
        fun _ : ℝ => (1 : ℝ) := by
      funext v
      simp [xiShiftedCanonicalAdmissionCurve]
    have hvelocity : xiShiftedCanonicalAdmissionVelocity y n (Fin.last n) = 0 := by
      simp [xiShiftedCanonicalAdmissionVelocity]
    rw [hcurve, hvelocity]
    exact hasDerivAt_const (x := y) (1 : ℝ)
  · have hcurve : xiShiftedCanonicalAdmissionCurve n j.castSucc =
        fun v => HTGeometry.monicMomentAdmissionCoefficients
          (fun k => (xiShiftedReciprocalMoment v k).re) n j := by
      funext v
      simp [xiShiftedCanonicalAdmissionCurve]
    have hvelocity : xiShiftedCanonicalAdmissionVelocity y n j.castSucc =
        xiShiftedCanonicalAdmissionLowerVelocity y n j := by
      simp [xiShiftedCanonicalAdmissionVelocity]
    rw [hcurve, hvelocity]
    exact hasDerivAt_xiShiftedCanonicalAdmissionCoefficient hy n hdet j

lemma momentInner_finitePolynomialCurve_curve
    (s : ℕ → ℝ) {N : ℕ} (c d : Fin N → ℝ → ℝ) (v : ℝ) :
    HTGeometry.momentInner s (finitePolynomialCurve c v)
        (finitePolynomialCurve d v) =
      ∑ i : Fin N, ∑ j : Fin N,
        c i v * d j v * s ((i : ℕ) + (j : ℕ)) := by
  simp only [finitePolynomialCurve]
  rw [HTGeometry.momentInner_def, Polynomial.ofFn_eq_sum_monomial,
    Polynomial.ofFn_eq_sum_monomial, Finset.sum_mul]
  simp only [Finset.mul_sum]
  rw [HTGeometry.momentFunctional_finset_sum]
  simp_rw [HTGeometry.momentFunctional_finset_sum]
  simp only [Polynomial.monomial_mul_monomial,
    HTGeometry.momentFunctional_monomial]

lemma momentInner_finitePolynomialCurve_self
    (s : ℕ → ℝ) {N : ℕ} (c : Fin N → ℝ → ℝ) (v : ℝ) :
    HTGeometry.momentInner s (finitePolynomialCurve c v)
        (finitePolynomialCurve c v) =
      ∑ i : Fin N, ∑ j : Fin N,
        c i v * c j v * s ((i : ℕ) + (j : ℕ)) :=
  momentInner_finitePolynomialCurve_curve s c c v

lemma momentInner_finitePolynomialVelocity_curve
    (s : ℕ → ℝ) {N : ℕ} (dc : Fin N → ℝ) (c : Fin N → ℝ → ℝ) (v : ℝ) :
    HTGeometry.momentInner s (finitePolynomialVelocity dc)
        (finitePolynomialCurve c v) =
      ∑ i : Fin N, ∑ j : Fin N,
        dc i * c j v * s ((i : ℕ) + (j : ℕ)) := by
  let d : Fin N → ℝ → ℝ := fun i _ => dc i
  simpa only [finitePolynomialCurve, finitePolynomialVelocity, d] using
    (momentInner_finitePolynomialCurve_curve s d c v)

/-- Moving-frame product rule for the even norm current. -/
theorem hasDerivAt_xiShiftedMomentInner_movingNorm
    {y : ℝ} (hy : 0 < y) {N : ℕ}
    (c : Fin N → ℝ → ℝ) (dc : Fin N → ℝ)
    (hc : ∀ i : Fin N, HasDerivAt (c i) (dc i) y) :
    HasDerivAt
      (fun v => HTGeometry.momentInner
        (fun k => (xiShiftedReciprocalMoment v k).re)
        (finitePolynomialCurve c v) (finitePolynomialCurve c v))
      (-HTGeometry.momentFunctional
          (fun k => (xiShiftedReciprocalMoment y k).re)
          (X * xiShiftedBoundaryShiftedEuler 1
            ((finitePolynomialCurve c y) ^ 2)) +
        2 * HTGeometry.momentInner
          (fun k => (xiShiftedReciprocalMoment y k).re)
          (finitePolynomialVelocity dc) (finitePolynomialCurve c y)) y := by
  let s : ℝ → ℕ → ℝ := fun v k => (xiShiftedReciprocalMoment v k).re
  let md : ℕ → ℝ := fun k => -((k : ℝ) + 1) * s y (k + 1)
  let move : ℝ := ∑ i : Fin N, ∑ j : Fin N,
    (dc i * c j y + c i y * dc j) * s y ((i : ℕ) + (j : ℕ))
  let fixed : ℝ := ∑ i : Fin N, ∑ j : Fin N,
    (c i y * c j y) * md ((i : ℕ) + (j : ℕ))
  have htotal : HasDerivAt
      (fun v => ∑ i : Fin N, ∑ j : Fin N,
        c i v * c j v * s v ((i : ℕ) + (j : ℕ)))
      (move + fixed) y := by
    have hraw := HasDerivAt.sum (u := (Finset.univ : Finset (Fin N)))
      (fun i _ => HasDerivAt.sum (u := (Finset.univ : Finset (Fin N)))
        (fun j _ => ((hc i).mul (hc j)).mul
          (hasDerivAt_re_xiShiftedReciprocalMoment hy
            ((i : ℕ) + (j : ℕ)))))
    have hfun :
        (∑ i : Fin N, ∑ j : Fin N,
          c i * c j *
            (fun v => (xiShiftedReciprocalMoment v
              ((i : ℕ) + (j : ℕ))).re)) =
          (fun v => ∑ i : Fin N, ∑ j : Fin N,
            c i v * c j v * s v ((i : ℕ) + (j : ℕ))) := by
      funext v
      simp only [s, Finset.sum_apply, Pi.mul_apply]
    rw [hfun] at hraw
    simpa only [s, md, move, fixed, Nat.cast_add,
      Finset.sum_add_distrib, Pi.mul_apply] using hraw
  have htotal' : HasDerivAt
      (fun v => HTGeometry.momentInner
        (fun k => (xiShiftedReciprocalMoment v k).re)
        (finitePolynomialCurve c v) (finitePolynomialCurve c v))
      (move + fixed) y := by
    rw [show (fun v => HTGeometry.momentInner
        (fun k => (xiShiftedReciprocalMoment v k).re)
        (finitePolynomialCurve c v) (finitePolynomialCurve c v)) =
      (fun v => ∑ i : Fin N, ∑ j : Fin N,
        c i v * c j v * s v ((i : ℕ) + (j : ℕ))) by
      funext v
      exact momentInner_finitePolynomialCurve_self (s v) c v]
    exact htotal
  have hfixedDirect : HasDerivAt
      (fun v => HTGeometry.momentInner
        (fun k => (xiShiftedReciprocalMoment v k).re)
        (finitePolynomialCurve c y) (finitePolynomialCurve c y)) fixed y := by
    rw [show (fun v => HTGeometry.momentInner
        (fun k => (xiShiftedReciprocalMoment v k).re)
        (finitePolynomialCurve c y) (finitePolynomialCurve c y)) =
      (fun v => ∑ i : Fin N, ∑ j : Fin N,
        c i y * c j y * s v ((i : ℕ) + (j : ℕ))) by
      funext v
      exact momentInner_finitePolynomialCurve_self (s v) c y]
    have hraw := HasDerivAt.sum (u := (Finset.univ : Finset (Fin N)))
      (fun i _ => HasDerivAt.sum (u := (Finset.univ : Finset (Fin N)))
        (fun j _ => (hasDerivAt_re_xiShiftedReciprocalMoment hy
          ((i : ℕ) + (j : ℕ))).const_mul (c i y * c j y)))
    have hfun :
        (∑ i : Fin N, ∑ j : Fin N,
          (fun v => c i y * c j y *
            (xiShiftedReciprocalMoment v ((i : ℕ) + (j : ℕ))).re)) =
          (fun v => ∑ i : Fin N, ∑ j : Fin N,
            c i y * c j y * s v ((i : ℕ) + (j : ℕ))) := by
      funext v
      simp only [s, Finset.sum_apply]
    rw [hfun] at hraw
    simpa only [s, md, fixed, Nat.cast_add, Finset.sum_apply] using hraw
  have hfixedSource := hasDerivAt_xiShiftedMomentFunctional_sourceConnection hy
    ((finitePolynomialCurve c y) ^ 2)
  have hfixed : fixed =
      -HTGeometry.momentFunctional (s y)
        (X * xiShiftedBoundaryShiftedEuler 1
          ((finitePolynomialCurve c y) ^ 2)) := by
    apply hfixedDirect.unique
    simpa only [HTGeometry.momentInner_self] using hfixedSource
  have hmove : move = 2 * HTGeometry.momentInner (s y)
      (finitePolynomialVelocity dc) (finitePolynomialCurve c y) := by
    have hcomm := HTGeometry.momentInner_comm (s y)
      (finitePolynomialCurve c y) (finitePolynomialVelocity dc)
    change (∑ i : Fin N, ∑ j : Fin N,
      (dc i * c j y + c i y * dc j) * s y ((i : ℕ) + (j : ℕ))) = _
    simp_rw [add_mul, Finset.sum_add_distrib]
    rw [← momentInner_finitePolynomialVelocity_curve (s y) dc c y]
    let d : Fin N → ℝ → ℝ := fun i _ => dc i
    have hsecond := momentInner_finitePolynomialCurve_curve (s y) c d y
    change HTGeometry.momentInner (s y) (finitePolynomialCurve c y)
      (finitePolynomialVelocity dc) = _ at hsecond
    rw [← hsecond, hcomm]
    ring
  rw [hmove, hfixed] at htotal'
  simpa only [s, add_comm] using htotal'

/-- Every leading principal shifted-Xi Hankel subblock inherits positive definiteness. -/
theorem xiShiftedMomentHankel_posDef_of_le
    {y : ℝ} {m N : ℕ} (hmN : m ≤ N)
    (hH : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) N).PosDef) :
    (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) m).PosDef := by
  let e : Fin m → Fin N := fun i => ⟨i, lt_of_lt_of_le i.isLt hmN⟩
  have he : Function.Injective e := by
    intro i j hij
    apply Fin.ext
    simpa [e] using congrArg Fin.val hij
  have hsub := hH.submatrix he
  have heq :
      (HTGeometry.momentHankelMatrix
        (fun k => (xiShiftedReciprocalMoment y k).re) N).submatrix e e =
      HTGeometry.momentHankelMatrix
        (fun k => (xiShiftedReciprocalMoment y k).re) m := by
    ext i j
    rfl
  rwa [heq] at hsub

/-- A positive `(n+1)` block makes the leading admission block invertible. -/
theorem xiShiftedMomentHankel_det_ne_zero_of_succ_posDef
    {y : ℝ} {n : ℕ}
    (hH : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) (n + 1)).PosDef) :
    (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) n).det ≠ 0 := by
  exact ne_of_gt (xiShiftedMomentHankel_posDef_of_le (by omega) hH).det_pos

/-- A positive `(n+2)` block makes the leading admission block invertible. -/
theorem xiShiftedMomentHankel_det_ne_zero_of_add_two_posDef
    {y : ℝ} {n : ℕ}
    (hH : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) (n + 2)).PosDef) :
    (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) n).det ≠ 0 := by
  exact ne_of_gt (xiShiftedMomentHankel_posDef_of_le (by omega) hH).det_pos

/-- The finite coefficient curve is literally the canonical admission polynomial. -/
theorem finitePolynomialCurve_xiShiftedCanonicalAdmission
    (y : ℝ) (n : ℕ) :
    finitePolynomialCurve (xiShiftedCanonicalAdmissionCurve n) y =
      HTGeometry.monicMomentAdmissionPolynomial
        (fun k => (xiShiftedReciprocalMoment y k).re) n := by
  rfl

/-- Removing the zero terminal tangent coordinate leaves the lower inverse-Hankel velocity
polynomial. -/
theorem finitePolynomialVelocity_xiShiftedCanonicalAdmission
    (y : ℝ) (n : ℕ) :
    finitePolynomialVelocity (xiShiftedCanonicalAdmissionVelocity y n) =
      Polynomial.ofFn n (xiShiftedCanonicalAdmissionLowerVelocity y n) := by
  rw [finitePolynomialVelocity, Polynomial.ofFn_eq_sum_monomial,
    Fin.sum_univ_castSucc, Polynomial.ofFn_eq_sum_monomial]
  simp only [xiShiftedCanonicalAdmissionVelocity, Fin.snoc_castSucc, Fin.val_castSucc,
    Fin.snoc_last, Fin.val_last, Polynomial.monomial_zero_right, add_zero]

theorem natDegree_finitePolynomialVelocity_xiShiftedCanonicalAdmission_lt
    {n : ℕ} (hn : 0 < n) (y : ℝ) :
    (finitePolynomialVelocity
      (xiShiftedCanonicalAdmissionVelocity y n)).natDegree < n := by
  rw [finitePolynomialVelocity_xiShiftedCanonicalAdmission]
  exact Polynomial.ofFn_natDegree_lt hn
    (xiShiftedCanonicalAdmissionLowerVelocity y n)

/-- Positive definiteness of the leading solve block alone identifies inverse-Hankel and
Gram--Schmidt admissions. -/
theorem xiShiftedCanonicalAdmissionPolynomial_eq_monicOrtho_of_hankelPosDef
    {y : ℝ} {n : ℕ}
    (hH : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) n).PosDef) :
    HTGeometry.monicMomentAdmissionPolynomial
        (fun k => (xiShiftedReciprocalMoment y k).re) n =
      HTGeometry.monicOrtho
        (fun k => (xiShiftedReciprocalMoment y k).re) n := by
  let s : ℕ → ℝ := fun k => (xiShiftedReciprocalMoment y k).re
  let hbelow := HTGeometry.positiveMomentFormBelow_of_hankelPosDef hH
  symm
  apply HTGeometry.eq_monicMomentAdmissionPolynomial_of_monic_of_orthogonal
    (ne_of_gt hH.det_pos) (HTGeometry.monicOrtho_monic s n)
      (HTGeometry.natDegree_monicOrtho_eq s n)
  intro i
  rw [← HTGeometry.momentInner_def, HTGeometry.momentInner_comm]
  apply HTGeometry.monicOrtho_inner_eq_zero_of_degree_lt_below hbelow le_rfl
  rw [Polynomial.degree_X_pow]
  exact_mod_cast i.isLt

/-- In a finite positive chamber, canonical inverse-Hankel admission and Gram--Schmidt admission
are the same object. -/
theorem xiShiftedCanonicalAdmissionPolynomial_eq_monicOrtho
    {y : ℝ} {n : ℕ}
    (hH : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) (n + 2)).PosDef) :
    HTGeometry.monicMomentAdmissionPolynomial
        (fun k => (xiShiftedReciprocalMoment y k).re) n =
      HTGeometry.monicOrtho
        (fun k => (xiShiftedReciprocalMoment y k).re) n := by
  exact xiShiftedCanonicalAdmissionPolynomial_eq_monicOrtho_of_hankelPosDef
    (xiShiftedMomentHankel_posDef_of_le (by omega) hH)

/-- Canonical connection term forced by the moving inverse-Hankel admission. -/
def xiShiftedCanonicalAdmissionSourceConnection (y : ℝ) (n : ℕ) : ℝ :=
  2 * HTGeometry.monicOrthoNorm
      (fun k => (xiShiftedReciprocalMoment y k).re) n *
    (finitePolynomialVelocity
      (xiShiftedCanonicalAdmissionVelocity y n)).coeff (n - 1)

/-- First subleading coefficient of the actual inverse-Hankel admission. -/
def xiShiftedCanonicalAdmissionFirstCoeff (y : ℝ) (n : ℕ) : ℝ :=
  (HTGeometry.monicMomentAdmissionPolynomial
    (fun k => (xiShiftedReciprocalMoment y k).re) n).coeff (n - 1)

/-- Norm of the actual inverse-Hankel admission in its moving moment form. -/
def xiShiftedCanonicalAdmissionNorm (y : ℝ) (n : ℕ) : ℝ :=
  HTGeometry.momentInner (fun k => (xiShiftedReciprocalMoment y k).re)
    (HTGeometry.monicMomentAdmissionPolynomial
      (fun k => (xiShiftedReciprocalMoment y k).re) n)
    (HTGeometry.monicMomentAdmissionPolynomial
      (fun k => (xiShiftedReciprocalMoment y k).re) n)

/-- Actual canonical admission norm is literally its inverse-Hankel coefficient quadratic. -/
theorem xiShiftedCanonicalAdmissionNorm_eq_hankelQuadratic
    (y : ℝ) (n : ℕ) :
    xiShiftedCanonicalAdmissionNorm y n =
      xiShiftedMomentHankelQuadratic y (n + 1)
        (HTGeometry.monicMomentAdmissionVector
          (fun k => (xiShiftedReciprocalMoment y k).re) n) := by
  rw [xiShiftedCanonicalAdmissionNorm,
    HTGeometry.monicMomentAdmissionPolynomial,
    xiShiftedMomentHankelQuadratic, xiShiftedMomentHankelMatrix]
  exact HTGeometry.momentInner_ofFn_ofFn
    (fun k => (xiShiftedReciprocalMoment y k).re) (n + 1)
      (HTGeometry.monicMomentAdmissionVector
        (fun k => (xiShiftedReciprocalMoment y k).re) n)
      (HTGeometry.monicMomentAdmissionVector
        (fun k => (xiShiftedReciprocalMoment y k).re) n)

/-- On a flat next face, the actual inverse-Hankel admission has zero norm. -/
theorem xiShiftedCanonicalAdmissionNorm_eq_zero_of_flatFace
    {y : ℝ} {n : ℕ}
    (hflat : xiShiftedMomentHankelMatrix y (n + 1) *ᵥ
      HTGeometry.monicMomentAdmissionVector
        (fun k => (xiShiftedReciprocalMoment y k).re) n = 0) :
    xiShiftedCanonicalAdmissionNorm y n = 0 := by
  rw [xiShiftedCanonicalAdmissionNorm_eq_hankelQuadratic,
    xiShiftedMomentHankelQuadratic, hflat, dotProduct_zero]

/-- Odd current of the actual inverse-Hankel admission. -/
def xiShiftedCanonicalAdmissionOddCurrent (y : ℝ) (n : ℕ) : ℝ :=
  HTGeometry.momentInner (fun k => (xiShiftedReciprocalMoment y k).re)
    (HTGeometry.monicMomentAdmissionPolynomial
      (fun k => (xiShiftedReciprocalMoment y k).re) n)
    (X * HTGeometry.monicMomentAdmissionPolynomial
      (fun k => (xiShiftedReciprocalMoment y k).re) n)

/-- Adaptive bilinear source shear formed from the actual inverse-Hankel admission. -/
def xiShiftedCanonicalAdmissionAdaptiveShear (y : ℝ) (n : ℕ) : ℝ :=
  let P := HTGeometry.monicMomentAdmissionPolynomial
    (fun k => (xiShiftedReciprocalMoment y k).re) n
  HTGeometry.momentInner (fun k => (xiShiftedReciprocalMoment y k).re)
    (X * P) (X * xiShiftedBoundaryShiftedEuler 1 P)

/-- Division-free norm flux.  Unlike Jacobi quotients, this coordinate remains defined on a flat
Hankel face. -/
def xiShiftedCanonicalAdmissionNormFlux (y : ℝ) (n : ℕ) : ℝ :=
  2 * xiShiftedCanonicalAdmissionFirstCoeff y n *
      xiShiftedCanonicalAdmissionNorm y n -
    ((2 * n + 1 : ℕ) : ℝ) * xiShiftedCanonicalAdmissionOddCurrent y n

/-- At a flat next face, actual canonical odd current is the first-unseen monic arithmetic
remainder. -/
theorem xiShiftedCanonicalAdmissionOddCurrent_eq_monicRemainder_of_flatFace
    {y : ℝ} {n : ℕ}
    (hflat : xiShiftedMomentHankelMatrix y (n + 1) *ᵥ
      HTGeometry.monicMomentAdmissionVector
        (fun k => (xiShiftedReciprocalMoment y k).re) n = 0) :
    xiShiftedCanonicalAdmissionOddCurrent y n =
      xiShiftedHankelBoundaryMonicRemainder y
        (HTGeometry.monicMomentAdmissionVector
          (fun k => (xiShiftedReciprocalMoment y k).re) n) := by
  let s : ℕ → ℝ := fun k => (xiShiftedReciprocalMoment y k).re
  let c : Fin (n + 1) → ℝ := HTGeometry.monicMomentAdmissionVector s n
  have hmono : HTGeometry.finiteHankelNullMonicPolynomial c =
      HTGeometry.finiteHankelNullPolynomial c := by
    rw [HTGeometry.finiteHankelNullMonicPolynomial,
      HTGeometry.finiteHankelNullPolynomial_leadingCoeff_eq_terminal c (by simp [c])]
    simp [c]
  have hrem := xiShiftedHankelBoundaryMonicRemainder_eq_shiftedSquare
    c hflat (by simp [c])
  rw [hmono] at hrem
  rw [xiShiftedCanonicalAdmissionOddCurrent,
    HTGeometry.monicMomentAdmissionPolynomial]
  change HTGeometry.momentInner s (HTGeometry.finiteHankelNullPolynomial c)
      (X * HTGeometry.finiteHankelNullPolynomial c) = _
  rw [HTGeometry.momentInner_def, hrem]
  congr 1
  ring

/-- Canonical diagonal Jacobi coordinate, defined from actual moving admission currents. -/
def xiShiftedCanonicalAdmissionAlpha (y : ℝ) (n : ℕ) : ℝ :=
  xiShiftedCanonicalAdmissionOddCurrent y n /
    xiShiftedCanonicalAdmissionNorm y n

/-- Gauge-invariant cumulative Jacobi trace carried by actual moving admission. -/
def xiShiftedCanonicalAdmissionCumulativeJacobiFlux (y : ℝ) (n : ℕ) : ℝ :=
  -2 * xiShiftedCanonicalAdmissionFirstCoeff y n +
    xiShiftedCanonicalAdmissionAlpha y n

/-- Strict Jacobi dissipation predicted after cancellation of admission velocity. -/
def xiShiftedCanonicalAdmissionCumulativeJacobiDissipation
    (y : ℝ) (n : ℕ) : ℝ :=
  2 * (∑ j ∈ Finset.range n,
      HTGeometry.monicOrthoAlpha
        (fun k => (xiShiftedReciprocalMoment y k).re) j ^ 2) +
    HTGeometry.monicOrthoAlpha
      (fun k => (xiShiftedReciprocalMoment y k).re) n ^ 2 +
    4 * (∑ j ∈ Finset.range n,
      HTGeometry.monicOrthoBeta
        (fun k => (xiShiftedReciprocalMoment y k).re) j) +
    2 * (n + 1 : ℝ) *
      (HTGeometry.monicOrthoBeta
          (fun k => (xiShiftedReciprocalMoment y k).re) n +
        HTGeometry.monicOrthoBeta
          (fun k => (xiShiftedReciprocalMoment y k).re) (n + 1))

theorem xiShiftedCanonicalAdmissionFirstCoeff_eq_monicOrthoFirstCoeff
    {y : ℝ} {n : ℕ} (hn : 0 < n)
    (hH : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) (n + 2)).PosDef) :
    xiShiftedCanonicalAdmissionFirstCoeff y n =
      HTGeometry.monicOrthoFirstCoeff
        (fun k => (xiShiftedReciprocalMoment y k).re) n := by
  rw [xiShiftedCanonicalAdmissionFirstCoeff,
    xiShiftedCanonicalAdmissionPolynomial_eq_monicOrtho hH]
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  rfl

theorem xiShiftedCanonicalAdmissionNorm_eq_monicOrthoNorm
    {y : ℝ} {n : ℕ}
    (hH : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) (n + 2)).PosDef) :
    xiShiftedCanonicalAdmissionNorm y n =
      HTGeometry.monicOrthoNorm
        (fun k => (xiShiftedReciprocalMoment y k).re) n := by
  rw [xiShiftedCanonicalAdmissionNorm,
    xiShiftedCanonicalAdmissionPolynomial_eq_monicOrtho hH]
  rfl

theorem xiShiftedCanonicalAdmissionAlpha_eq_monicOrthoAlpha
    {y : ℝ} {n : ℕ}
    (hH : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) (n + 2)).PosDef) :
    xiShiftedCanonicalAdmissionAlpha y n =
      HTGeometry.monicOrthoAlpha
        (fun k => (xiShiftedReciprocalMoment y k).re) n := by
  rw [xiShiftedCanonicalAdmissionAlpha, xiShiftedCanonicalAdmissionOddCurrent,
    xiShiftedCanonicalAdmissionNorm,
    xiShiftedCanonicalAdmissionPolynomial_eq_monicOrtho hH,
    HTGeometry.momentInner_comm]
  rfl

/-- Actual subleading admission coordinate has the inverse-Hankel velocity. -/
theorem hasDerivAt_xiShiftedCanonicalAdmissionFirstCoeff
    {y : ℝ} (hy : 0 < y) {n : ℕ} (hn : 0 < n)
    (hdet : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) n).det ≠ 0) :
    HasDerivAt (fun v => xiShiftedCanonicalAdmissionFirstCoeff v n)
      ((finitePolynomialVelocity
        (xiShiftedCanonicalAdmissionVelocity y n)).coeff (n - 1)) y := by
  let i : Fin (n + 1) := ⟨n - 1, by omega⟩
  have hi := hasDerivAt_xiShiftedCanonicalAdmissionCurve hy n hdet i
  have hcurve : (fun v => xiShiftedCanonicalAdmissionFirstCoeff v n) =
      xiShiftedCanonicalAdmissionCurve n i := by
    funext v
    rw [xiShiftedCanonicalAdmissionFirstCoeff,
      ← finitePolynomialCurve_xiShiftedCanonicalAdmission v n]
    exact Polynomial.ofFn_coeff_eq_val_of_lt _ (by omega)
  have hvelocity :
      (finitePolynomialVelocity
        (xiShiftedCanonicalAdmissionVelocity y n)).coeff (n - 1) =
      xiShiftedCanonicalAdmissionVelocity y n i := by
    exact Polynomial.ofFn_coeff_eq_val_of_lt _ (by omega)
  rw [hcurve, hvelocity]
  exact hi

/-- **Actual canonical moving-admission law.**  The odd current derivative is the negative adaptive
Jacobi source plus the unique inverse-Hankel connection term. -/
theorem hasDerivAt_xiShiftedCanonicalAdmissionOddCurrent_eq_jacobiEnergy
    {y : ℝ} (hy : 0 < y) {n : ℕ} (hn : 0 < n)
    (hH : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) (n + 2)).PosDef) :
    HasDerivAt
      (fun v => HTGeometry.momentInner
        (fun k => (xiShiftedReciprocalMoment v k).re)
        (HTGeometry.monicMomentAdmissionPolynomial
          (fun k => (xiShiftedReciprocalMoment v k).re) n)
        (X * HTGeometry.monicMomentAdmissionPolynomial
          (fun k => (xiShiftedReciprocalMoment v k).re) n))
      (-2 * HTGeometry.monicOrthoNorm
          (fun k => (xiShiftedReciprocalMoment y k).re) n *
          HTGeometry.adaptiveOrthoJacobiEnergy
            (fun k => (xiShiftedReciprocalMoment y k).re) n +
        xiShiftedCanonicalAdmissionSourceConnection y n) y := by
  have hdet := xiShiftedMomentHankel_det_ne_zero_of_add_two_posDef hH
  have hcurve := hasDerivAt_xiShiftedCanonicalAdmissionCurve hy n hdet
  have hPy : finitePolynomialCurve (xiShiftedCanonicalAdmissionCurve n) y =
      HTGeometry.monicOrtho
        (fun k => (xiShiftedReciprocalMoment y k).re) n := by
    rw [finitePolynomialCurve_xiShiftedCanonicalAdmission,
      xiShiftedCanonicalAdmissionPolynomial_eq_monicOrtho hH]
  have hvelocity :=
    natDegree_finitePolynomialVelocity_xiShiftedCanonicalAdmission_lt hn y
  have hsource :=
    hasDerivAt_xiShiftedMovingAdmissionOddCurrent_eq_jacobiEnergy
      hy hn hH (xiShiftedCanonicalAdmissionCurve n)
        (xiShiftedCanonicalAdmissionVelocity y n) hcurve hPy hvelocity
  simpa only [finitePolynomialCurve_xiShiftedCanonicalAdmission,
    xiShiftedCanonicalAdmissionSourceConnection] using hsource

/-- Canonical covariant derivative is strictly negative under one finite Hankel hypothesis. -/
theorem xiShiftedCanonicalAdmissionOddCurrent_covariantDerivative_neg
    {y : ℝ} (hy : 0 < y) {n : ℕ} (hn : 0 < n)
    (hH : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) (n + 2)).PosDef)
    {Bdot : ℝ}
    (hB : HasDerivAt
      (fun v => HTGeometry.momentInner
        (fun k => (xiShiftedReciprocalMoment v k).re)
        (HTGeometry.monicMomentAdmissionPolynomial
          (fun k => (xiShiftedReciprocalMoment v k).re) n)
        (X * HTGeometry.monicMomentAdmissionPolynomial
          (fun k => (xiShiftedReciprocalMoment v k).re) n)) Bdot y) :
    Bdot - xiShiftedCanonicalAdmissionSourceConnection y n < 0 := by
  have hcanonical :=
    hasDerivAt_xiShiftedCanonicalAdmissionOddCurrent_eq_jacobiEnergy hy hn hH
  have hBdot := hB.unique hcanonical
  rw [hBdot]
  let hbelow := HTGeometry.positiveMomentFormBelow_of_hankelPosDef hH
  have hnorm := HTGeometry.monicOrthoNorm_pos_below hbelow (n := n) (by omega)
  have henergy := HTGeometry.adaptiveOrthoJacobiEnergy_pos_below
    hbelow hn (n := n) (le_refl (n + 2))
  nlinarith

/-- **Division-free canonical norm law.**  On every leading-nonsingular chamber, actual
inverse-Hankel norm derivative is the raw flux `2a_n N_n-(2n+1)B_n`.  No positivity of the next
one or two Hankel blocks and no Jacobi quotient is used. -/
theorem hasDerivAt_xiShiftedCanonicalAdmissionNorm_eq_normFlux_of_det
    {y : ℝ} (hy : 0 < y) {n : ℕ} (hn : 0 < n)
    (hdet : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) n).det ≠ 0) :
    HasDerivAt (fun v => xiShiftedCanonicalAdmissionNorm v n)
      (xiShiftedCanonicalAdmissionNormFlux y n) y := by
  let s : ℕ → ℝ := fun k => (xiShiftedReciprocalMoment y k).re
  let P := HTGeometry.monicMomentAdmissionPolynomial s n
  let dc : Fin (n + 1) → ℝ := xiShiftedCanonicalAdmissionVelocity y n
  have hcurve := hasDerivAt_xiShiftedCanonicalAdmissionCurve hy n hdet
  have hmoving := hasDerivAt_xiShiftedMomentInner_movingNorm hy
    (xiShiftedCanonicalAdmissionCurve n) dc hcurve
  have hPy : finitePolynomialCurve (xiShiftedCanonicalAdmissionCurve n) y = P := by
    rfl
  have hvelocity :=
    natDegree_finitePolynomialVelocity_xiShiftedCanonicalAdmission_lt hn y
  have hmovezero : HTGeometry.momentInner s
      (finitePolynomialVelocity dc) P = 0 := by
    rw [HTGeometry.momentInner_comm]
    exact HTGeometry.momentInner_monicMomentAdmission_lower_eq_zero hdet hvelocity
  have htransport :=
    HTGeometry.momentFunctional_X_shiftedEuler_one_sq_monicMomentAdmission hn hdet
  dsimp only at htransport
  have htransport' : HTGeometry.momentFunctional s
      (X * xiShiftedBoundaryShiftedEuler 1 (P ^ 2)) =
    ((2 * n + 1 : ℕ) : ℝ) * HTGeometry.momentInner s P (X * P) -
      2 * P.coeff (n - 1) * HTGeometry.momentInner s P P := by
    simpa only [xiShiftedBoundaryShiftedEuler, C_1, one_mul] using htransport
  rw [hPy, hmovezero, mul_zero, add_zero, htransport'] at hmoving
  have hfun :
      (fun v => xiShiftedCanonicalAdmissionNorm v n) =
      (fun v => HTGeometry.momentInner
        (fun k => (xiShiftedReciprocalMoment v k).re)
        (finitePolynomialCurve (xiShiftedCanonicalAdmissionCurve n) v)
        (finitePolynomialCurve (xiShiftedCanonicalAdmissionCurve n) v)) := by
    funext v
    rw [xiShiftedCanonicalAdmissionNorm,
      finitePolynomialCurve_xiShiftedCanonicalAdmission]
  rw [hfun]
  refine hmoving.congr_deriv ?_
  simp only [xiShiftedCanonicalAdmissionNormFlux,
    xiShiftedCanonicalAdmissionFirstCoeff, xiShiftedCanonicalAdmissionNorm,
    xiShiftedCanonicalAdmissionOddCurrent, s, P]
  push_cast
  ring

/-- **Actual-admission singular-face law.**  At a flat next Hankel face, the forced
inverse-Hankel coefficient motion is tangent to the null flag.  Therefore it contributes no norm
velocity: the derivative of the actual moving canonical norm is exactly `-(2n+1)` times the
first-unseen monic arithmetic remainder. -/
theorem hasDerivAt_xiShiftedCanonicalAdmissionNorm_of_flatFace
    {y : ℝ} (hy : 0 < y) {n : ℕ} (hn : 0 < n)
    (hhead : (xiShiftedMomentHankelMatrix y n).PosDef)
    (hflat : xiShiftedMomentHankelMatrix y (n + 1) *ᵥ
      HTGeometry.monicMomentAdmissionVector
        (fun k => (xiShiftedReciprocalMoment y k).re) n = 0) :
    HasDerivAt (fun v => xiShiftedCanonicalAdmissionNorm v n)
      (-((2 * n + 1 : ℕ) : ℝ) *
        xiShiftedHankelBoundaryMonicRemainder y
          (HTGeometry.monicMomentAdmissionVector
            (fun k => (xiShiftedReciprocalMoment y k).re) n)) y := by
  have hdet : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) n).det ≠ 0 :=
    ne_of_gt hhead.det_pos
  have hraw :=
    hasDerivAt_xiShiftedCanonicalAdmissionNorm_eq_normFlux_of_det hy hn hdet
  have hNzero := xiShiftedCanonicalAdmissionNorm_eq_zero_of_flatFace hflat
  have hB := xiShiftedCanonicalAdmissionOddCurrent_eq_monicRemainder_of_flatFace hflat
  refine hraw.congr_deriv ?_
  rw [xiShiftedCanonicalAdmissionNormFlux, hNzero, hB]
  ring

/-- At a flat face the inverse-Hankel coefficient velocity is tangent to the null flag, so the
actual moving odd current loses its connection term and differentiates to minus twice the adaptive
bilinear source shear. -/
theorem hasDerivAt_xiShiftedCanonicalAdmissionOddCurrent_eq_adaptiveShear_of_flatFace
    {y : ℝ} (hy : 0 < y) {n : ℕ} (hn : 0 < n)
    (hhead : (xiShiftedMomentHankelMatrix y n).PosDef)
    (hflat : xiShiftedMomentHankelMatrix y (n + 1) *ᵥ
      HTGeometry.monicMomentAdmissionVector
        (fun k => (xiShiftedReciprocalMoment y k).re) n = 0) :
    HasDerivAt (fun v => xiShiftedCanonicalAdmissionOddCurrent v n)
      (-2 * xiShiftedCanonicalAdmissionAdaptiveShear y n) y := by
  let s : ℕ → ℝ := fun k => (xiShiftedReciprocalMoment y k).re
  let c : Fin (n + 1) → ℝ := HTGeometry.monicMomentAdmissionVector s n
  let dc : Fin (n + 1) → ℝ := xiShiftedCanonicalAdmissionVelocity y n
  have hdet : (HTGeometry.momentHankelMatrix s n).det ≠ 0 :=
    ne_of_gt hhead.det_pos
  have hflat' : HTGeometry.momentHankelMatrix s (n + 1) *ᵥ c = 0 := by
    change HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) (n + 1) *ᵥ
        HTGeometry.monicMomentAdmissionVector
          (fun k => (xiShiftedReciprocalMoment y k).re) n = 0 at hflat
    simpa only [s, c] using hflat
  have hcurve := hasDerivAt_xiShiftedCanonicalAdmissionCurve hy n hdet
  have hmoving := hasDerivAt_xiShiftedMomentInner_movingOddCurrent hy
    (xiShiftedCanonicalAdmissionCurve n) dc hcurve
  have hPy : finitePolynomialCurve (xiShiftedCanonicalAdmissionCurve n) y =
      HTGeometry.finiteHankelNullPolynomial c := by
    rfl
  have hvelocity :=
    natDegree_finitePolynomialVelocity_xiShiftedCanonicalAdmission_lt hn y
  have hXvelocity :
      (X * finitePolynomialVelocity dc).natDegree < n + 1 := by
    have hsum : 1 + (finitePolynomialVelocity dc).natDegree < 1 + n :=
      Nat.add_lt_add_left hvelocity 1
    calc
      (X * finitePolynomialVelocity dc).natDegree ≤
          X.natDegree + (finitePolynomialVelocity dc).natDegree :=
        Polynomial.natDegree_mul_le
      _ = 1 + (finitePolynomialVelocity dc).natDegree := by
        rw [Polynomial.natDegree_X]
      _ < 1 + n := hsum
      _ = n + 1 := by omega
  have hmovezero : HTGeometry.momentInner s (finitePolynomialVelocity dc)
      (X * HTGeometry.finiteHankelNullPolynomial c) = 0 := by
    have hcomm : HTGeometry.momentInner s (finitePolynomialVelocity dc)
        (X * HTGeometry.finiteHankelNullPolynomial c) =
      HTGeometry.momentInner s (HTGeometry.finiteHankelNullPolynomial c)
        (X * finitePolynomialVelocity dc) := by
      simp only [HTGeometry.momentInner_def]
      congr 1
      ring
    rw [hcomm]
    exact HTGeometry.momentInner_finiteHankelNullPolynomial_eq_zero_of_kernel
      hflat' hXvelocity
  rw [hPy, hmovezero, mul_zero, add_zero] at hmoving
  have hfun :
      (fun v => xiShiftedCanonicalAdmissionOddCurrent v n) =
      (fun v => HTGeometry.momentInner
        (fun k => (xiShiftedReciprocalMoment v k).re)
        (finitePolynomialCurve (xiShiftedCanonicalAdmissionCurve n) v)
        (X * finitePolynomialCurve (xiShiftedCanonicalAdmissionCurve n) v)) := by
    funext v
    rw [xiShiftedCanonicalAdmissionOddCurrent,
      finitePolynomialCurve_xiShiftedCanonicalAdmission]
  rw [hfun]
  have hshear : xiShiftedCanonicalAdmissionAdaptiveShear y n =
      HTGeometry.momentInner s (X * HTGeometry.finiteHankelNullPolynomial c)
        (X * xiShiftedBoundaryShiftedEuler 1
          (HTGeometry.finiteHankelNullPolynomial c)) := by
    rfl
  rw [hshear]
  exact hmoving

/-- **Singular producer law.**  If the first-unseen remainder also vanishes, the division-free
norm flux differentiates to the adaptive source.  This is the source-side replacement for the
Jacobi quotient, which is undefined on the flat face. -/
theorem hasDerivAt_xiShiftedCanonicalAdmissionNormFlux_of_flatTangent
    {y : ℝ} (hy : 0 < y) {n : ℕ} (hn : 0 < n)
    (hhead : (xiShiftedMomentHankelMatrix y n).PosDef)
    (hflat : xiShiftedMomentHankelMatrix y (n + 1) *ᵥ
      HTGeometry.monicMomentAdmissionVector
        (fun k => (xiShiftedReciprocalMoment y k).re) n = 0)
    (htangent : xiShiftedHankelBoundaryMonicRemainder y
      (HTGeometry.monicMomentAdmissionVector
        (fun k => (xiShiftedReciprocalMoment y k).re) n) = 0) :
    HasDerivAt (fun v => xiShiftedCanonicalAdmissionNormFlux v n)
      (2 * ((2 * n + 1 : ℕ) : ℝ) *
        xiShiftedCanonicalAdmissionAdaptiveShear y n) y := by
  have hdet : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) n).det ≠ 0 := by
    exact ne_of_gt hhead.det_pos
  have ha := hasDerivAt_xiShiftedCanonicalAdmissionFirstCoeff hy hn hdet
  have hNraw := hasDerivAt_xiShiftedCanonicalAdmissionNorm_of_flatFace
    hy hn hhead hflat
  have hN : HasDerivAt (fun v => xiShiftedCanonicalAdmissionNorm v n) 0 y := by
    refine hNraw.congr_deriv ?_
    rw [htangent]
    ring
  have hNzero := xiShiftedCanonicalAdmissionNorm_eq_zero_of_flatFace hflat
  have hB :=
    hasDerivAt_xiShiftedCanonicalAdmissionOddCurrent_eq_adaptiveShear_of_flatFace
      hy hn hhead hflat
  have hraw := ((ha.mul hN).const_mul 2).sub
    (hB.const_mul (((2 * n + 1 : ℕ) : ℝ)))
  have hderiv :
      2 *
          ((finitePolynomialVelocity
            (xiShiftedCanonicalAdmissionVelocity y n)).coeff (n - 1) *
              xiShiftedCanonicalAdmissionNorm y n +
            xiShiftedCanonicalAdmissionFirstCoeff y n * 0) -
        ((2 * n + 1 : ℕ) : ℝ) *
          (-2 * xiShiftedCanonicalAdmissionAdaptiveShear y n) =
      2 * ((2 * n + 1 : ℕ) : ℝ) *
        xiShiftedCanonicalAdmissionAdaptiveShear y n := by
    rw [hNzero]
    ring
  have hfun : (fun v => xiShiftedCanonicalAdmissionNormFlux v n) =
      (fun v => 2 *
          (xiShiftedCanonicalAdmissionFirstCoeff v n *
            xiShiftedCanonicalAdmissionNorm v n) -
        ((2 * n + 1 : ℕ) : ℝ) *
          xiShiftedCanonicalAdmissionOddCurrent v n) := by
    funext v
    simp only [xiShiftedCanonicalAdmissionNormFlux]
    ring
  rw [hfun]
  exact hraw.congr_deriv hderiv

/-- **Arithmetic source-first boundary law.**  At a tangential flat face, the derivative of the
actual inverse-Hankel norm flux is the odd-contact factor times the literal completed mixed
arithmetic source formed from that admission before reflection aggregation. -/
theorem hasDerivAt_xiShiftedCanonicalAdmissionNormFlux_eq_arithmeticSource_of_flatTangent
    {w : ℝ} (hw : 1 / 2 < w) {n : ℕ} (hn : 0 < n)
    (hhead : (xiShiftedMomentHankelMatrix (w ^ 2) n).PosDef)
    (hflat : xiShiftedMomentHankelMatrix (w ^ 2) (n + 1) *ᵥ
      HTGeometry.monicMomentAdmissionVector (xiShiftedRealMomentSequence w) n = 0)
    (htangent : xiShiftedHankelBoundaryMonicRemainder (w ^ 2)
      (HTGeometry.monicMomentAdmissionVector (xiShiftedRealMomentSequence w) n) = 0) :
    HasDerivAt (fun v => xiShiftedCanonicalAdmissionNormFlux v n)
      (((2 * n + 1 : ℕ) : ℝ) *
        xiShiftedAdaptiveMixedCompletedArithmeticSource w
          (HTGeometry.monicMomentAdmissionPolynomial
            (xiShiftedRealMomentSequence w) n)) (w ^ 2) := by
  have hy : 0 < w ^ 2 := sq_pos_of_pos (by linarith : 0 < w)
  have hflux := hasDerivAt_xiShiftedCanonicalAdmissionNormFlux_of_flatTangent
    hy hn hhead hflat htangent
  let P := HTGeometry.monicMomentAdmissionPolynomial
    (xiShiftedRealMomentSequence w) n
  have hsource := two_mul_xiShiftedAdaptiveShear_eq_arithmeticSource hw P
  change 2 * HTGeometry.momentInner (xiShiftedRealMomentSequence w)
      (X * P) (X * xiShiftedBoundaryShiftedEuler 1 P) =
    xiShiftedAdaptiveMixedCompletedArithmeticSource w P at hsource
  have hshear : xiShiftedCanonicalAdmissionAdaptiveShear (w ^ 2) n =
      HTGeometry.momentInner (xiShiftedRealMomentSequence w)
        (X * P) (X * xiShiftedBoundaryShiftedEuler 1 P) := by
    rfl
  rw [hshear] at hflux
  refine hflux.congr_deriv ?_
  rw [← hsource]
  dsimp only [P]
  ring

/-- The same singular producer law stated for completed adaptive `P^sharp` packet itself. -/
theorem hasDerivAt_xiShiftedCanonicalAdmissionNormFlux_eq_completedAggregate_of_flatTangent
    {w : ℝ} (hw : 1 / 2 < w) {n : ℕ} (hn : 0 < n)
    (hhead : (xiShiftedMomentHankelMatrix (w ^ 2) n).PosDef)
    (hflat : xiShiftedMomentHankelMatrix (w ^ 2) (n + 1) *ᵥ
      HTGeometry.monicMomentAdmissionVector (xiShiftedRealMomentSequence w) n = 0)
    (htangent : xiShiftedHankelBoundaryMonicRemainder (w ^ 2)
      (HTGeometry.monicMomentAdmissionVector (xiShiftedRealMomentSequence w) n) = 0) :
    let P := HTGeometry.monicMomentAdmissionPolynomial
      (xiShiftedRealMomentSequence w) n
    HasDerivAt (fun v => xiShiftedCanonicalAdmissionNormFlux v n)
      (((2 * n + 1 : ℕ) : ℝ) *
        xiShiftedCompletedMomentAggregate (w ^ 2) 2
          (xiShiftedBoundaryAdaptiveMidpointCoefficients 1
            (xiShiftedOddCrossingCoefficientPacket P))) (w ^ 2) := by
  dsimp only
  rw [xiShiftedCompletedMomentAggregate_adaptiveOddPacket_eq_arithmeticSource hw]
  exact
    hasDerivAt_xiShiftedCanonicalAdmissionNormFlux_eq_arithmeticSource_of_flatTangent
      hw hn hhead hflat htangent

/-- Exact norm flow needs only the next Hankel block, one degree less than adaptive source energy. -/
theorem hasDerivAt_xiShiftedCanonicalAdmissionNorm_eq_jacobiFlow_of_succ_posDef
    {y : ℝ} (hy : 0 < y) {n : ℕ} (hn : 0 < n)
    (hH : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) (n + 1)).PosDef) :
    HasDerivAt (fun v => xiShiftedCanonicalAdmissionNorm v n)
      ((2 * HTGeometry.monicOrthoFirstCoeff
          (fun k => (xiShiftedReciprocalMoment y k).re) n -
        ((2 * n + 1 : ℕ) : ℝ) * HTGeometry.monicOrthoAlpha
          (fun k => (xiShiftedReciprocalMoment y k).re) n) *
        HTGeometry.monicOrthoNorm
          (fun k => (xiShiftedReciprocalMoment y k).re) n) y := by
  let s : ℕ → ℝ := fun k => (xiShiftedReciprocalMoment y k).re
  let hbelow := HTGeometry.positiveMomentFormBelow_of_hankelPosDef hH
  have hhead := xiShiftedMomentHankel_posDef_of_le (by omega : n ≤ n + 1) hH
  have hdet := xiShiftedMomentHankel_det_ne_zero_of_succ_posDef hH
  have hcurve := hasDerivAt_xiShiftedCanonicalAdmissionCurve hy n hdet
  have hPy : finitePolynomialCurve (xiShiftedCanonicalAdmissionCurve n) y =
      HTGeometry.monicOrtho s n := by
    rw [finitePolynomialCurve_xiShiftedCanonicalAdmission,
      xiShiftedCanonicalAdmissionPolynomial_eq_monicOrtho_of_hankelPosDef hhead]
  have hvelocity :=
    natDegree_finitePolynomialVelocity_xiShiftedCanonicalAdmission_lt hn y
  have hmovezero : HTGeometry.momentInner s
      (finitePolynomialVelocity (xiShiftedCanonicalAdmissionVelocity y n))
      (HTGeometry.monicOrtho s n) = 0 := by
    rw [HTGeometry.momentInner_comm]
    apply HTGeometry.monicOrtho_inner_eq_zero_of_degree_lt_below hbelow (by omega)
    exact lt_of_le_of_lt Polynomial.degree_le_natDegree (by exact_mod_cast hvelocity)
  have htransport : HTGeometry.momentFunctional s
      (X * xiShiftedBoundaryShiftedEuler 1 ((HTGeometry.monicOrtho s n) ^ 2)) =
      ((2 * n + 1 : ℕ) : ℝ) * HTGeometry.monicOrthoAlpha s n *
          HTGeometry.monicOrthoNorm s n -
        2 * HTGeometry.monicOrthoFirstCoeff s n *
          HTGeometry.monicOrthoNorm s n := by
    simpa only [xiShiftedBoundaryShiftedEuler, C_1, one_mul] using
      HTGeometry.momentFunctional_X_shiftedEuler_one_sq_monicOrtho
        hbelow hn (by omega)
  have hnorm := hasDerivAt_xiShiftedMomentInner_movingNorm hy
    (xiShiftedCanonicalAdmissionCurve n)
    (xiShiftedCanonicalAdmissionVelocity y n) hcurve
  rw [hPy, hmovezero, mul_zero, add_zero, htransport] at hnorm
  have hfun :
      (fun v => xiShiftedCanonicalAdmissionNorm v n) =
      (fun v => HTGeometry.momentInner
        (fun k => (xiShiftedReciprocalMoment v k).re)
        (finitePolynomialCurve (xiShiftedCanonicalAdmissionCurve n) v)
        (finitePolynomialCurve (xiShiftedCanonicalAdmissionCurve n) v)) := by
    funext v
    rw [xiShiftedCanonicalAdmissionNorm,
      finitePolynomialCurve_xiShiftedCanonicalAdmission]
  rw [hfun]
  exact hnorm.congr_deriv (by ring)

/-- Exact norm flow of actual canonical admission.  Moving-frame terms vanish by orthogonality;
only first subleading coefficient and diagonal Jacobi coordinate remain. -/
theorem hasDerivAt_xiShiftedCanonicalAdmissionNorm_eq_jacobiFlow
    {y : ℝ} (hy : 0 < y) {n : ℕ} (hn : 0 < n)
    (hH : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) (n + 2)).PosDef) :
    HasDerivAt (fun v => xiShiftedCanonicalAdmissionNorm v n)
      ((2 * HTGeometry.monicOrthoFirstCoeff
          (fun k => (xiShiftedReciprocalMoment y k).re) n -
        ((2 * n + 1 : ℕ) : ℝ) * HTGeometry.monicOrthoAlpha
          (fun k => (xiShiftedReciprocalMoment y k).re) n) *
        HTGeometry.monicOrthoNorm
          (fun k => (xiShiftedReciprocalMoment y k).re) n) y := by
  exact hasDerivAt_xiShiftedCanonicalAdmissionNorm_eq_jacobiFlow_of_succ_posDef
    hy hn (xiShiftedMomentHankel_posDef_of_le (by omega) hH)

/-- Quotient Jacobi coordinate differentiates with source energy, norm flow, and admission
velocity all visible. -/
theorem hasDerivAt_xiShiftedCanonicalAdmissionAlpha_eq_sourceConnection
    {y : ℝ} (hy : 0 < y) {n : ℕ} (hn : 0 < n)
    (hH : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) (n + 2)).PosDef) :
    HasDerivAt (fun v => xiShiftedCanonicalAdmissionAlpha v n)
      (-2 * HTGeometry.adaptiveOrthoJacobiEnergy
          (fun k => (xiShiftedReciprocalMoment y k).re) n +
        2 * (finitePolynomialVelocity
          (xiShiftedCanonicalAdmissionVelocity y n)).coeff (n - 1) -
        HTGeometry.monicOrthoAlpha
          (fun k => (xiShiftedReciprocalMoment y k).re) n *
          (2 * HTGeometry.monicOrthoFirstCoeff
              (fun k => (xiShiftedReciprocalMoment y k).re) n -
            ((2 * n + 1 : ℕ) : ℝ) * HTGeometry.monicOrthoAlpha
              (fun k => (xiShiftedReciprocalMoment y k).re) n)) y := by
  let s : ℕ → ℝ := fun k => (xiShiftedReciprocalMoment y k).re
  let hval := HTGeometry.monicOrthoNorm s n
  let aval := HTGeometry.monicOrthoFirstCoeff s n
  let alpha := HTGeometry.monicOrthoAlpha s n
  let energy := HTGeometry.adaptiveOrthoJacobiEnergy s n
  let adot := (finitePolynomialVelocity
    (xiShiftedCanonicalAdmissionVelocity y n)).coeff (n - 1)
  have hB : HasDerivAt (fun v => xiShiftedCanonicalAdmissionOddCurrent v n)
      (-2 * hval * energy + 2 * hval * adot) y := by
    simpa only [xiShiftedCanonicalAdmissionOddCurrent,
      xiShiftedCanonicalAdmissionSourceConnection, s, hval, energy, adot] using
      hasDerivAt_xiShiftedCanonicalAdmissionOddCurrent_eq_jacobiEnergy hy hn hH
  have hN : HasDerivAt (fun v => xiShiftedCanonicalAdmissionNorm v n)
      ((2 * aval - ((2 * n + 1 : ℕ) : ℝ) * alpha) * hval) y := by
    simpa only [s, hval, aval, alpha] using
      hasDerivAt_xiShiftedCanonicalAdmissionNorm_eq_jacobiFlow hy hn hH
  let hbelow := HTGeometry.positiveMomentFormBelow_of_hankelPosDef hH
  have hvalpos : 0 < hval := HTGeometry.monicOrthoNorm_pos_below hbelow (by omega)
  have hvalne : hval ≠ 0 := ne_of_gt hvalpos
  have hNval : xiShiftedCanonicalAdmissionNorm y n = hval := by
    simpa only [s, hval] using xiShiftedCanonicalAdmissionNorm_eq_monicOrthoNorm hH
  have hAval : xiShiftedCanonicalAdmissionAlpha y n = alpha := by
    simpa only [s, alpha] using xiShiftedCanonicalAdmissionAlpha_eq_monicOrthoAlpha hH
  have hBval : xiShiftedCanonicalAdmissionOddCurrent y n = alpha * hval := by
    have hquot := hAval
    rw [xiShiftedCanonicalAdmissionAlpha, hNval] at hquot
    exact (div_eq_iff hvalne).mp hquot
  have hdiv := hB.div hN (by simpa only [hNval] using hvalne)
  have hderiv :
      ((-2 * hval * energy + 2 * hval * adot) *
          xiShiftedCanonicalAdmissionNorm y n -
        xiShiftedCanonicalAdmissionOddCurrent y n *
          ((2 * aval - ((2 * n + 1 : ℕ) : ℝ) * alpha) * hval)) /
          xiShiftedCanonicalAdmissionNorm y n ^ 2 =
        -2 * energy + 2 * adot -
          alpha * (2 * aval - ((2 * n + 1 : ℕ) : ℝ) * alpha) := by
    rw [hNval, hBval]
    field_simp [hvalne]
  have hfunction : (fun v => xiShiftedCanonicalAdmissionAlpha v n) =
      (fun v => xiShiftedCanonicalAdmissionOddCurrent v n) /
        (fun v => xiShiftedCanonicalAdmissionNorm v n) := by
    funext v
    rfl
  rw [hfunction]
  exact hdiv.congr_deriv hderiv

/-- **Cumulative Jacobi-flux law.**  Admission velocity cancels exactly.  The remaining derivative
is a negative sum of Jacobi squares and positive lower-coupling terms. -/
theorem hasDerivAt_xiShiftedCanonicalAdmissionCumulativeJacobiFlux
    {y : ℝ} (hy : 0 < y) {n : ℕ} (hn : 0 < n)
    (hH : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) (n + 2)).PosDef) :
    HasDerivAt
      (fun v => xiShiftedCanonicalAdmissionCumulativeJacobiFlux v n)
      (-xiShiftedCanonicalAdmissionCumulativeJacobiDissipation y n) y := by
  let s : ℕ → ℝ := fun k => (xiShiftedReciprocalMoment y k).re
  let a := HTGeometry.monicOrthoFirstCoeff s n
  let alpha := HTGeometry.monicOrthoAlpha s n
  let energy := HTGeometry.adaptiveOrthoJacobiEnergy s n
  let adot := (finitePolynomialVelocity
    (xiShiftedCanonicalAdmissionVelocity y n)).coeff (n - 1)
  have hdet := xiShiftedMomentHankel_det_ne_zero_of_add_two_posDef hH
  have ha := hasDerivAt_xiShiftedCanonicalAdmissionFirstCoeff hy hn hdet
  have halpha :=
    hasDerivAt_xiShiftedCanonicalAdmissionAlpha_eq_sourceConnection hy hn hH
  have hraw := (ha.const_mul (-2)).add halpha
  have hcore :
      (-2 : ℝ) * adot +
        (-2 * energy + 2 * adot -
          alpha * (2 * a - ((2 * n + 1 : ℕ) : ℝ) * alpha)) =
      -xiShiftedCanonicalAdmissionCumulativeJacobiDissipation y n := by
    let hbelow := HTGeometry.positiveMomentFormBelow_of_hankelPosDef hH
    have henergy := HTGeometry.adaptiveOrthoJacobiEnergy_eq_coeffJet_below
      hbelow (n := n) (by omega)
    have hjet := HTGeometry.monicOrtho_coeffJet_energy_below
      hbelow (n := n) (by omega)
    have hfirst : a = HTGeometry.monicOrthoFirstCoeff s n := rfl
    have halpha' : alpha = HTGeometry.monicOrthoAlpha s n := rfl
    have henergy' : energy = HTGeometry.adaptiveOrthoJacobiEnergy s n := rfl
    rw [hfirst, halpha', henergy', henergy]
    calc
      (-2 : ℝ) * adot +
          (-2 *
              (HTGeometry.monicOrthoFirstCoeff s n ^ 2 -
                2 * HTGeometry.monicOrthoSecondCoeff s n -
                HTGeometry.monicOrthoAlpha s n *
                  HTGeometry.monicOrthoFirstCoeff s n +
                (n + 1 : ℝ) * HTGeometry.monicOrthoAlpha s n ^ 2 +
                (n + 1 : ℝ) *
                  (HTGeometry.monicOrthoBeta s n +
                    HTGeometry.monicOrthoBeta s (n + 1))) +
            2 * adot -
            HTGeometry.monicOrthoAlpha s n *
              (2 * HTGeometry.monicOrthoFirstCoeff s n -
                ((2 * n + 1 : ℕ) : ℝ) * HTGeometry.monicOrthoAlpha s n)) =
          -2 * (HTGeometry.monicOrthoFirstCoeff s n ^ 2 -
              2 * HTGeometry.monicOrthoSecondCoeff s n) -
            HTGeometry.monicOrthoAlpha s n ^ 2 -
            2 * (n + 1 : ℝ) *
              (HTGeometry.monicOrthoBeta s n +
                HTGeometry.monicOrthoBeta s (n + 1)) := by
          push_cast
          ring
      _ = -xiShiftedCanonicalAdmissionCumulativeJacobiDissipation y n := by
          rw [hjet]
          simp only [xiShiftedCanonicalAdmissionCumulativeJacobiDissipation, s]
          ring
  have hderiv :
      (-2 : ℝ) *
          (finitePolynomialVelocity
            (xiShiftedCanonicalAdmissionVelocity y n)).coeff (n - 1) +
        (-2 * HTGeometry.adaptiveOrthoJacobiEnergy s n +
          2 * (finitePolynomialVelocity
            (xiShiftedCanonicalAdmissionVelocity y n)).coeff (n - 1) -
          HTGeometry.monicOrthoAlpha s n *
            (2 * HTGeometry.monicOrthoFirstCoeff s n -
              ((2 * n + 1 : ℕ) : ℝ) * HTGeometry.monicOrthoAlpha s n)) =
        -xiShiftedCanonicalAdmissionCumulativeJacobiDissipation y n := by
    simpa only [a, alpha, energy, adot] using hcore
  have hfunction :
      (fun v => xiShiftedCanonicalAdmissionCumulativeJacobiFlux v n) =
      (fun v => -2 * xiShiftedCanonicalAdmissionFirstCoeff v n) +
        (fun v => xiShiftedCanonicalAdmissionAlpha v n) := by
    funext v
    rfl
  rw [hfunction]
  exact hraw.congr_deriv hderiv

/-- Dissipation in the cumulative Jacobi-flux law is strictly positive. -/
theorem xiShiftedCanonicalAdmissionCumulativeJacobiDissipation_pos
    {y : ℝ} {n : ℕ} (hn : 0 < n)
    (hH : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) (n + 2)).PosDef) :
    0 < xiShiftedCanonicalAdmissionCumulativeJacobiDissipation y n := by
  let s : ℕ → ℝ := fun k => (xiShiftedReciprocalMoment y k).re
  let hbelow := HTGeometry.positiveMomentFormBelow_of_hankelPosDef hH
  have hsquares : 0 ≤ ∑ j ∈ Finset.range n,
      HTGeometry.monicOrthoAlpha s j ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hbetas : 0 ≤ ∑ j ∈ Finset.range n,
      HTGeometry.monicOrthoBeta s j := by
    apply Finset.sum_nonneg
    intro j hj
    rcases j with _ | j
    · simp [HTGeometry.monicOrthoBeta]
    · exact (HTGeometry.monicOrthoBeta_pos_below hbelow (Nat.succ_pos j) (by
        have hjn := Finset.mem_range.mp hj
        omega)).le
  have hboundary : 0 < HTGeometry.monicOrthoBeta s n +
      HTGeometry.monicOrthoBeta s (n + 1) :=
    add_pos
      (HTGeometry.monicOrthoBeta_pos_below hbelow hn (by omega))
      (HTGeometry.monicOrthoBeta_pos_below hbelow (by omega) (by omega))
  simp only [xiShiftedCanonicalAdmissionCumulativeJacobiDissipation]
  positivity

/-- In a positive chamber the gauge-invariant flux is the cumulative Jacobi trace
`2∑_{j<n} αⱼ + αₙ`. -/
theorem xiShiftedCanonicalAdmissionCumulativeJacobiFlux_eq_trace
    {y : ℝ} {n : ℕ} (hn : 0 < n)
    (hH : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) (n + 2)).PosDef) :
    xiShiftedCanonicalAdmissionCumulativeJacobiFlux y n =
      2 * (∑ j ∈ Finset.range n,
        HTGeometry.monicOrthoAlpha
          (fun k => (xiShiftedReciprocalMoment y k).re) j) +
        HTGeometry.monicOrthoAlpha
          (fun k => (xiShiftedReciprocalMoment y k).re) n := by
  let s : ℕ → ℝ := fun k => (xiShiftedReciprocalMoment y k).re
  let hbelow := HTGeometry.positiveMomentFormBelow_of_hankelPosDef hH
  rw [xiShiftedCanonicalAdmissionCumulativeJacobiFlux,
    xiShiftedCanonicalAdmissionFirstCoeff_eq_monicOrthoFirstCoeff hn hH,
    xiShiftedCanonicalAdmissionAlpha_eq_monicOrthoAlpha hH,
    HTGeometry.monicOrthoFirstCoeff_eq_neg_sum_below hbelow (by omega)]
  ring

/-- Literal cumulative Jacobi trace decreases strictly wherever the finite positive chamber
persists. -/
theorem deriv_xiShiftedCanonicalAdmissionCumulativeJacobiFlux_neg
    {y : ℝ} (hy : 0 < y) {n : ℕ} (hn : 0 < n)
    (hH : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) (n + 2)).PosDef) :
    deriv (fun v => xiShiftedCanonicalAdmissionCumulativeJacobiFlux v n) y < 0 := by
  rw [(hasDerivAt_xiShiftedCanonicalAdmissionCumulativeJacobiFlux
    hy hn hH).deriv]
  exact neg_neg_of_pos
    (xiShiftedCanonicalAdmissionCumulativeJacobiDissipation_pos hn hH)

/-- **Canonical adaptive arithmetic-source law.**  The actual inverse-Hankel `P^sharp`, chosen
before formation, makes the completed source exactly twice norm times Jacobi energy. -/
theorem xiShiftedAdaptiveMixedCompletedArithmeticSource_canonicalAdmission_eq_jacobiEnergy
    {w : ℝ} (hw : 1 / 2 < w) {n : ℕ} (hn : 0 < n)
    (hH : (HTGeometry.momentHankelMatrix (xiShiftedRealMomentSequence w)
      (n + 2)).PosDef) :
    xiShiftedAdaptiveMixedCompletedArithmeticSource w
        (HTGeometry.monicMomentAdmissionPolynomial
          (xiShiftedRealMomentSequence w) n) =
      2 * HTGeometry.monicOrthoNorm (xiShiftedRealMomentSequence w) n *
        HTGeometry.adaptiveOrthoJacobiEnergy (xiShiftedRealMomentSequence w) n := by
  have heq := xiShiftedCanonicalAdmissionPolynomial_eq_monicOrtho
    (y := w ^ 2) hH
  change HTGeometry.monicMomentAdmissionPolynomial (xiShiftedRealMomentSequence w) n =
    HTGeometry.monicOrtho (xiShiftedRealMomentSequence w) n at heq
  rw [heq]
  exact
    xiShiftedAdaptiveMixedCompletedArithmeticSource_monicOrtho_eq_jacobiEnergy_of_hankelPosDef
      hw hn hH

/-- Strict positivity of the canonical arithmetic source is generated at formation time. -/
theorem xiShiftedAdaptiveMixedCompletedArithmeticSource_canonicalAdmission_pos
    {w : ℝ} (hw : 1 / 2 < w) {n : ℕ} (hn : 0 < n)
    (hH : (HTGeometry.momentHankelMatrix (xiShiftedRealMomentSequence w)
      (n + 2)).PosDef) :
    0 < xiShiftedAdaptiveMixedCompletedArithmeticSource w
      (HTGeometry.monicMomentAdmissionPolynomial (xiShiftedRealMomentSequence w) n) := by
  rw [xiShiftedAdaptiveMixedCompletedArithmeticSource_canonicalAdmission_eq_jacobiEnergy
    hw hn hH]
  let hbelow := HTGeometry.positiveMomentFormBelow_of_hankelPosDef hH
  exact mul_pos
    (mul_pos (by norm_num) (HTGeometry.monicOrthoNorm_pos_below hbelow (by omega)))
    (HTGeometry.adaptiveOrthoJacobiEnergy_pos_below hbelow hn le_rfl)

/-- The completed adaptive packet itself, not a reporter applied afterward, equals the canonical
positive Jacobi source. -/
theorem xiShiftedCompletedMomentAggregate_canonicalAdaptiveOddPacket_eq_jacobiEnergy
    {w : ℝ} (hw : 1 / 2 < w) {n : ℕ} (hn : 0 < n)
    (hH : (HTGeometry.momentHankelMatrix (xiShiftedRealMomentSequence w)
      (n + 2)).PosDef) :
    xiShiftedCompletedMomentAggregate (w ^ 2) 2
        (xiShiftedBoundaryAdaptiveMidpointCoefficients 1
          (xiShiftedOddCrossingCoefficientPacket
            (HTGeometry.monicMomentAdmissionPolynomial
              (xiShiftedRealMomentSequence w) n))) =
      2 * HTGeometry.monicOrthoNorm (xiShiftedRealMomentSequence w) n *
        HTGeometry.adaptiveOrthoJacobiEnergy (xiShiftedRealMomentSequence w) n := by
  rw [xiShiftedCompletedMomentAggregate_adaptiveOddPacket_eq_arithmeticSource hw]
  exact
    xiShiftedAdaptiveMixedCompletedArithmeticSource_canonicalAdmission_eq_jacobiEnergy
      hw hn hH

end

end RHTower
