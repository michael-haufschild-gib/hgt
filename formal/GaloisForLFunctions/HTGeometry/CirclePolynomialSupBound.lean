import GaloisForLFunctions.HTGeometry.HardyCrossParseval
import Mathlib.Algebra.Order.Chebyshev

/-!
# Sup bounds for a polynomial from its circle energy

A polynomial of degree below `M` is bounded on the closed disc of radius `r` by

`√M · (coefficient energy)^{1/2} · max(1, r)^M`,

and its coefficient energy is exactly its mean square on the unit circle.  Consequently a family of
polynomials of controlled degree and controlled circle energy is uniformly bounded on every compact
subset of the plane, which is the hypothesis of Montel's theorem.
-/

open MeasureTheory Complex
open scoped BigOperators Real Interval ComplexConjugate

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Cauchy--Schwarz bound for a polynomial sum in terms of its coefficient energy. -/
theorem norm_polySum_le (M : ℕ) (c : ℕ → ℂ) (w : ℂ) :
    ‖∑ k ∈ Finset.range M, c k * w ^ k‖
      ≤ Real.sqrt M * Real.sqrt (∑ k ∈ Finset.range M, ‖c k‖ ^ 2) * (max 1 ‖w‖) ^ M := by
  have hmax : (1 : ℝ) ≤ max 1 ‖w‖ := le_max_left _ _
  have hpow : ∀ k ∈ Finset.range M, ‖c k * w ^ k‖ ≤ ‖c k‖ * (max 1 ‖w‖) ^ M := by
    intro k hk
    have hkM : k ≤ M := le_of_lt (Finset.mem_range.1 hk)
    have h1 : ‖w‖ ^ k ≤ (max 1 ‖w‖) ^ k :=
      pow_le_pow_left₀ (norm_nonneg w) (le_max_right _ _) k
    have h2 : (max 1 ‖w‖) ^ k ≤ (max 1 ‖w‖) ^ M := pow_le_pow_right₀ hmax hkM
    rw [norm_mul, norm_pow]
    exact mul_le_mul_of_nonneg_left (h1.trans h2) (norm_nonneg _)
  have hsum : ‖∑ k ∈ Finset.range M, c k * w ^ k‖
      ≤ ∑ k ∈ Finset.range M, ‖c k‖ * (max 1 ‖w‖) ^ M :=
    (norm_sum_le _ _).trans (Finset.sum_le_sum hpow)
  have hcs : (∑ k ∈ Finset.range M, ‖c k‖) ^ 2
      ≤ (M : ℝ) * ∑ k ∈ Finset.range M, ‖c k‖ ^ 2 := by
    have h := sq_sum_le_card_mul_sum_sq (s := Finset.range M) (f := fun k => ‖c k‖)
    simpa using h
  have hnonneg : 0 ≤ ∑ k ∈ Finset.range M, ‖c k‖ :=
    Finset.sum_nonneg fun k _ => norm_nonneg _
  have hroot : ∑ k ∈ Finset.range M, ‖c k‖
      ≤ Real.sqrt M * Real.sqrt (∑ k ∈ Finset.range M, ‖c k‖ ^ 2) := by
    rw [← Real.sqrt_mul (Nat.cast_nonneg M)]
    have := Real.sqrt_le_sqrt hcs
    rwa [Real.sqrt_sq hnonneg] at this
  calc ‖∑ k ∈ Finset.range M, c k * w ^ k‖
      ≤ ∑ k ∈ Finset.range M, ‖c k‖ * (max 1 ‖w‖) ^ M := hsum
    _ = (∑ k ∈ Finset.range M, ‖c k‖) * (max 1 ‖w‖) ^ M := by rw [Finset.sum_mul]
    _ ≤ (Real.sqrt M * Real.sqrt (∑ k ∈ Finset.range M, ‖c k‖ ^ 2)) * (max 1 ‖w‖) ^ M := by
        exact mul_le_mul_of_nonneg_right hroot (pow_nonneg (le_trans zero_le_one hmax) M)

/-- **The coefficient energy of a polynomial is its mean square on the unit circle.** -/
theorem sum_normSq_coeff_eq_circleAverage (M : ℕ) (c : ℕ → ℂ) :
    (∑ k ∈ Finset.range M, ‖c k‖ ^ 2)
      = (2 * Real.pi)⁻¹ * ∫ theta in (0 : ℝ)..2 * Real.pi,
          ‖∑ k ∈ Finset.range M, c k * circleMap 0 1 theta ^ k‖ ^ 2 := by
  have hpar := circleAverage_poly_mul_conj 1 M c c
  have hint : ∀ theta : ℝ,
      (∑ k ∈ Finset.range M, c k * circleMap 0 1 theta ^ k) *
          conj (∑ j ∈ Finset.range M, c j * circleMap 0 1 theta ^ j)
        = ((‖∑ k ∈ Finset.range M, c k * circleMap 0 1 theta ^ k‖ ^ 2 : ℝ) : ℂ) := by
    intro theta
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hrhs : (∑ k ∈ Finset.range M, c k * conj (c k) * ((1 : ℝ) : ℂ) ^ (2 * k))
      = ((∑ k ∈ Finset.range M, ‖c k‖ ^ 2 : ℝ) : ℂ) := by
    push_cast
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    simp
  rw [intervalIntegral.integral_congr (g := fun theta =>
    ((‖∑ k ∈ Finset.range M, c k * circleMap 0 1 theta ^ k‖ ^ 2 : ℝ) : ℂ))
    (fun theta _ => hint theta), hrhs] at hpar
  rw [intervalIntegral.integral_ofReal] at hpar
  have hreal : ((2 * Real.pi : ℝ) : ℂ)⁻¹ *
      ((∫ theta in (0 : ℝ)..2 * Real.pi,
        ‖∑ k ∈ Finset.range M, c k * circleMap 0 1 theta ^ k‖ ^ 2 : ℝ) : ℂ)
      = (((2 * Real.pi)⁻¹ * ∫ theta in (0 : ℝ)..2 * Real.pi,
        ‖∑ k ∈ Finset.range M, c k * circleMap 0 1 theta ^ k‖ ^ 2 : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hreal] at hpar
  exact_mod_cast hpar.symm

/-! ## The Zhukovsky lift -/

/-- `w ^ d · P((w + w⁻¹)/2)`, written as a polynomial in `w` of degree at most `2d`. -/
def zhukovskyLift (d : ℕ) (P : Polynomial ℂ) : Polynomial ℂ :=
  ∑ k ∈ Finset.range (d + 1), Polynomial.C (P.coeff k) * Polynomial.C ((2 : ℂ)⁻¹) ^ k *
    Polynomial.X ^ (d - k) * (Polynomial.X ^ 2 + 1) ^ k

theorem natDegree_zhukovskyLift_le (d : ℕ) (P : Polynomial ℂ) :
    (zhukovskyLift d P).natDegree ≤ 2 * d := by
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun k hk => ?_
  have hkd : k ≤ d := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
  refine le_trans Polynomial.natDegree_mul_le ?_
  have h1 : (Polynomial.C (P.coeff k) * Polynomial.C ((2 : ℂ)⁻¹) ^ k
      * Polynomial.X ^ (d - k)).natDegree ≤ d - k := by
    refine le_trans Polynomial.natDegree_mul_le ?_
    have h2 : (Polynomial.C (P.coeff k) * Polynomial.C ((2 : ℂ)⁻¹) ^ k).natDegree ≤ 0 := by
      refine le_trans Polynomial.natDegree_mul_le ?_
      rw [Polynomial.natDegree_C, ← Polynomial.C_pow, Polynomial.natDegree_C]
    rw [Polynomial.natDegree_X_pow]
    omega
  have h3 : ((Polynomial.X ^ 2 + 1 : Polynomial ℂ) ^ k).natDegree ≤ 2 * k := by
    refine le_trans (Polynomial.natDegree_pow_le) ?_
    have h4 : (Polynomial.X ^ 2 + 1 : Polynomial ℂ).natDegree ≤ 2 := by
      refine le_trans (Polynomial.natDegree_add_le _ _) ?_
      rw [Polynomial.natDegree_X_pow, Polynomial.natDegree_one]
      omega
    calc k * (Polynomial.X ^ 2 + 1 : Polynomial ℂ).natDegree ≤ k * 2 :=
          Nat.mul_le_mul_left k h4
      _ = 2 * k := by ring
  omega

theorem eval_zhukovskyLift (d : ℕ) (P : Polynomial ℂ) (hd : P.natDegree ≤ d)
    {w : ℂ} (hw : w ≠ 0) :
    (zhukovskyLift d P).eval w = w ^ d * P.eval ((w + w⁻¹) / 2) := by
  rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hd), Finset.mul_sum, zhukovskyLift,
    Polynomial.eval_finsetSum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hkd : k ≤ d := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
  have hsplit : w ^ d = w ^ (d - k) * w ^ k := by
    rw [← pow_add]
    congr 1
    omega
  have hkey : w ^ k * (w + w⁻¹) ^ k = (w ^ 2 + 1) ^ k := by
    rw [← mul_pow]
    congr 1
    field_simp
  simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_C,
    Polynomial.eval_X, Polynomial.eval_one]
  rw [hsplit, div_pow, ← hkey, inv_pow, div_eq_mul_inv]
  ring

/-- The mean square of `P` on the Cayley interval, taken on the unit circle. -/
def cayleyEnergy (P : Polynomial ℂ) : ℝ :=
  (2 * Real.pi)⁻¹ * ∫ theta in (0 : ℝ)..2 * Real.pi,
    ‖P.eval ((circleMap 0 1 theta + (circleMap 0 1 theta)⁻¹) / 2)‖ ^ 2

/-- **A polynomial on the Cayley interval is bounded off the interval by its circle energy.**
This is the uniform bound that makes a family of controlled degree and controlled energy normal. -/
theorem norm_eval_cayley_le (d : ℕ) (P : Polynomial ℂ) (hd : P.natDegree ≤ d)
    {w : ℂ} (hw : 1 ≤ ‖w‖) :
    ‖P.eval ((w + w⁻¹) / 2)‖
      ≤ Real.sqrt (2 * d + 2) * Real.sqrt (cayleyEnergy P) * ‖w‖ ^ (d + 2) := by
  obtain ⟨Q, hQ⟩ : ∃ Q : Polynomial ℂ, Q = zhukovskyLift d P := ⟨_, rfl⟩
  have hdegQ : Q.natDegree < 2 * d + 2 := by
    rw [hQ]
    exact lt_of_le_of_lt (natDegree_zhukovskyLift_le d P) (by omega)
  have hrange : ∀ v : ℂ, Q.eval v = ∑ k ∈ Finset.range (2 * d + 2), Q.coeff k * v ^ k :=
    fun v => Polynomial.eval_eq_sum_range' hdegQ v
  have hcircle : ∀ theta : ℝ, circleMap 0 1 theta ≠ 0 := by
    intro theta hcon
    have := norm_circleMap_zero 1 theta
    rw [hcon] at this
    simp at this
  have henergy : (∑ k ∈ Finset.range (2 * d + 2), ‖Q.coeff k‖ ^ 2) = cayleyEnergy P := by
    rw [sum_normSq_coeff_eq_circleAverage (2 * d + 2) (fun k => Q.coeff k), cayleyEnergy]
    congr 1
    refine intervalIntegral.integral_congr fun theta _ => ?_
    have hne := hcircle theta
    have hnorm : ‖circleMap 0 1 theta‖ = 1 := by
      rw [norm_circleMap_zero]; norm_num
    rw [← hrange, hQ, eval_zhukovskyLift d P hd hne, norm_mul, norm_pow, hnorm, one_pow, one_mul]
  have hw0 : w ≠ 0 := by
    intro hcon
    rw [hcon] at hw
    simp at hw
    linarith
  have hbound := norm_polySum_le (2 * d + 2) (fun k => Q.coeff k) w
  rw [← hrange w, henergy] at hbound
  have hmax : max 1 ‖w‖ = ‖w‖ := max_eq_right hw
  rw [hmax] at hbound
  rw [hQ, eval_zhukovskyLift d P hd hw0, norm_mul, norm_pow] at hbound
  have hwd : (0 : ℝ) < ‖w‖ ^ d := pow_pos (lt_of_lt_of_le zero_lt_one hw) d
  have hsplit : ‖w‖ ^ (2 * d + 2) = ‖w‖ ^ d * ‖w‖ ^ (d + 2) := by
    rw [← pow_add]
    congr 1
    omega
  rw [hsplit] at hbound
  have hfinal : ‖w‖ ^ d * ‖P.eval ((w + w⁻¹) / 2)‖
      ≤ ‖w‖ ^ d * (Real.sqrt (2 * d + 2) * Real.sqrt (cayleyEnergy P) * ‖w‖ ^ (d + 2)) := by
    calc ‖w‖ ^ d * ‖P.eval ((w + w⁻¹) / 2)‖
        ≤ Real.sqrt (↑(2 * d + 2)) * Real.sqrt (cayleyEnergy P) * (‖w‖ ^ d * ‖w‖ ^ (d + 2)) :=
          hbound
      _ = ‖w‖ ^ d * (Real.sqrt (↑(2 * d + 2)) * Real.sqrt (cayleyEnergy P) * ‖w‖ ^ (d + 2)) := by
          ring
      _ = ‖w‖ ^ d * (Real.sqrt (2 * d + 2) * Real.sqrt (cayleyEnergy P) * ‖w‖ ^ (d + 2)) := by
          push_cast
          ring
  exact le_of_mul_le_mul_left hfinal hwd

/-- The same bound with no side of the circle preferred: the Zhukovsky coordinate is invariant
under `w ↦ w⁻¹`. -/
theorem norm_eval_cayley_le' (d : ℕ) (P : Polynomial ℂ) (hd : P.natDegree ≤ d)
    {w : ℂ} (hw : w ≠ 0) :
    ‖P.eval ((w + w⁻¹) / 2)‖
      ≤ Real.sqrt (2 * d + 2) * Real.sqrt (cayleyEnergy P) * (max ‖w‖ ‖w‖⁻¹) ^ (d + 2) := by
  have hpos : 0 < ‖w‖ := norm_pos_iff.2 hw
  have hinvmul : ‖w‖⁻¹ * ‖w‖ = 1 := inv_mul_cancel₀ (ne_of_gt hpos)
  by_cases h : 1 ≤ ‖w‖
  · have h1 : ‖w‖⁻¹ ≤ ‖w‖ := by nlinarith [hinvmul, hpos, h]
    rw [max_eq_left h1]
    exact norm_eval_cayley_le d P hd h
  · have hlt : ‖w‖ < 1 := lt_of_not_ge h
    have h1 : ‖w‖ ≤ ‖w‖⁻¹ := by nlinarith [hinvmul, hpos, hlt]
    have hinv : (1 : ℝ) ≤ ‖w⁻¹‖ := by
      rw [norm_inv]
      nlinarith [hinvmul, hpos, hlt]
    have hsym : (w⁻¹ + w⁻¹⁻¹) / 2 = (w + w⁻¹) / 2 := by
      rw [inv_inv]
      ring
    rw [max_eq_right h1, ← norm_inv, ← hsym]
    exact norm_eval_cayley_le d P hd hinv

end

end GaloisForLFunctions.HTGeometry
