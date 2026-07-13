import GaloisForLFunctions.HTGeometry.FiniteOPUCRootLocation
import Mathlib.Algebra.Polynomial.Reverse

/-!
# The reversed finite OPUC polynomial is zero-free on the closed disk

This is the second finite OPUC input to the Bernstein--Szegő construction.  Reversal converts a
closed-disk zero into a unit-or-exterior zero of the original normalized orthogonal polynomial,
contradicting the strict root-location theorem.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex Matrix Polynomial
open scoped ComplexOrder InnerProductSpace ComplexConjugate

noncomputable section

/-- The reversed-conjugate polynomial appearing in the Bernstein--Szegő density. -/
def finiteOPUCReversedPolynomial {N : ℕ} (c : ℤ → ℂ)
    (hG : (circleToeplitzGram N c).PosDef) : Polynomial ℂ :=
  ((finiteOPUCPolynomial c hG).map (starRingEnd ℂ)).reverse

/-- The Bernstein--Szegő denominator has no zero on the closed unit disk. -/
theorem finiteOPUCReversedPolynomial_ne_zero_on_closedBall
    {N : ℕ} (c : ℤ → ℂ) (hG : (circleToeplitzGram N c).PosDef)
    {z : ℂ} (hz : ‖z‖ ≤ 1) :
    (finiteOPUCReversedPolynomial c hG).eval z ≠ 0 := by
  intro hzero
  by_cases hz0 : z = 0
  · subst z
    have hlead : (finiteOPUCPolynomial c hG).leadingCoeff ≠ 0 := by
      rw [Polynomial.leadingCoeff, finiteOPUCPolynomial_natDegree c hG]
      simpa [finiteOPUCPolynomial] using finiteOPUCVector_last_ne_zero c hG
    have hmaplead :
        ((finiteOPUCPolynomial c hG).map (starRingEnd ℂ)).leadingCoeff ≠ 0 := by
      rw [Polynomial.leadingCoeff_map_of_injective (starRingEnd ℂ).injective]
      exact (star_eq_zero.not.mpr hlead)
    have := hzero
    rw [← Polynomial.coeff_zero_eq_eval_zero,
      finiteOPUCReversedPolynomial, Polynomial.coeff_zero_reverse] at this
    exact hmaplead this
  · have hzinv : z⁻¹ ≠ 0 := inv_ne_zero hz0
    letI : Invertible (z⁻¹) := invertibleOfNonzero hzinv
    let f : Polynomial ℂ := (finiteOPUCPolynomial c hG).map (starRingEnd ℂ)
    have hfrev : Polynomial.eval₂ (RingHom.id ℂ) (⅟(z⁻¹)) f.reverse = 0 := by
      simpa [f, finiteOPUCReversedPolynomial, invOf_eq_inv] using hzero
    have hfzero : Polynomial.eval₂ (RingHom.id ℂ) (z⁻¹) f = 0 :=
      (Polynomial.eval₂_reverse_eq_zero_iff (RingHom.id ℂ) (z⁻¹) f).mp hfrev
    let w : ℂ := star (z⁻¹)
    have hwroot : (finiteOPUCPolynomial c hG).IsRoot w := by
      have harg : (starRingEnd ℂ) w = z⁻¹ := by simp [w]
      have hmapped :
          ((finiteOPUCPolynomial c hG).map (starRingEnd ℂ)).IsRoot
            ((starRingEnd ℂ) w) := by
        rw [Polynomial.IsRoot, harg]
        simpa [f] using hfzero
      exact Polynomial.IsRoot.of_map hmapped (starRingEnd ℂ).injective
    have hwlt : ‖w‖ < 1 := finiteOPUCPolynomial_isRoot_norm_lt_one c hG hwroot
    have hznorm : 0 < ‖z‖ := norm_pos_iff.mpr hz0
    have hwge : 1 ≤ ‖w‖ := by
      change 1 ≤ ‖star (z⁻¹)‖
      rw [norm_star, norm_inv]
      exact (one_le_inv₀ hznorm).2 hz
    exact (not_lt_of_ge hwge) hwlt

/-- Exact reversal identity on the unit circle. -/
theorem finiteOPUCReversedPolynomial_eval_unitCircle
    {N : ℕ} (c : ℤ → ℂ) (hG : (circleToeplitzGram N c).PosDef)
    {z : ℂ} (hz : ‖z‖ = 1) :
    (finiteOPUCReversedPolynomial c hG).eval z =
      z ^ N * star ((finiteOPUCPolynomial c hG).eval z) := by
  have hz0 : z ≠ 0 := by
    intro hzero
    rw [hzero, norm_zero] at hz
    norm_num at hz
  have hzinv : z⁻¹ ≠ 0 := inv_ne_zero hz0
  letI : Invertible (z⁻¹) := invertibleOfNonzero hzinv
  let p : Polynomial ℂ := finiteOPUCPolynomial c hG
  let f : Polynomial ℂ := p.map (starRingEnd ℂ)
  have hfdeg : f.natDegree = N := by
    change (p.map (starRingEnd ℂ)).natDegree = N
    rw [Polynomial.natDegree_map_eq_of_injective (starRingEnd ℂ).injective]
    change (finiteOPUCPolynomial c hG).natDegree = N
    exact finiteOPUCPolynomial_natDegree c hG
  have hrev := Polynomial.eval₂_reverse_mul_pow (RingHom.id ℂ) (z⁻¹) f
  have harg : (⅟(z⁻¹)) = z := by simp [invOf_eq_inv]
  have hright : Polynomial.eval₂ (RingHom.id ℂ) (z⁻¹) f =
      star (p.eval z) := by
    have hzc : z⁻¹ = star z := Complex.inv_eq_conj hz
    rw [hzc]
    change f.eval (star z) = star (p.eval z)
    change (p.map (starRingEnd ℂ)).eval (star z) = star (p.eval z)
    exact Polynomial.eval_map_apply (p := p) (f := starRingEnd ℂ) z
  have heval : (finiteOPUCReversedPolynomial c hG).eval z * (z⁻¹) ^ N =
      star (p.eval z) := by
    simpa [finiteOPUCReversedPolynomial, f, p, harg, hfdeg, hright] using hrev
  calc
    (finiteOPUCReversedPolynomial c hG).eval z =
        (finiteOPUCReversedPolynomial c hG).eval z * 1 := by rw [mul_one]
    _ = (finiteOPUCReversedPolynomial c hG).eval z * ((z⁻¹) ^ N * z ^ N) := by
      rw [← mul_pow, inv_mul_cancel₀ hz0, one_pow]
    _ = ((finiteOPUCReversedPolynomial c hG).eval z * (z⁻¹) ^ N) * z ^ N := by
      rw [← mul_assoc]
    _ = star (p.eval z) * z ^ N := by rw [heval]
    _ = z ^ N * star ((finiteOPUCPolynomial c hG).eval z) := by
      change star (p.eval z) * z ^ N = z ^ N * star (p.eval z)
      exact mul_comm _ _

/-- On the unit circle, reversal preserves the squared modulus.  Thus the stable denominator is
pointwise the same modulus as the original normalized orthogonal polynomial. -/
theorem finiteOPUCReversedPolynomial_normSq_eq_on_unitCircle
    {N : ℕ} (c : ℤ → ℂ) (hG : (circleToeplitzGram N c).PosDef)
    {z : ℂ} (hz : ‖z‖ = 1) :
    Complex.normSq ((finiteOPUCReversedPolynomial c hG).eval z) =
      Complex.normSq ((finiteOPUCPolynomial c hG).eval z) := by
  have heval := finiteOPUCReversedPolynomial_eval_unitCircle c hG hz
  have hnorm := congrArg norm heval
  have hnormeq : ‖(finiteOPUCReversedPolynomial c hG).eval z‖ =
      ‖(finiteOPUCPolynomial c hG).eval z‖ := by
    simpa [norm_mul, norm_pow, hz] using hnorm
  change Complex.normSq ((finiteOPUCReversedPolynomial c hG).eval z) =
    Complex.normSq ((finiteOPUCPolynomial c hG).eval z)
  rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq, hnormeq]

end

end GaloisForLFunctions.HTGeometry
