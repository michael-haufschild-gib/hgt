import GaloisForLFunctions.RHTower.XiShiftedHardEdgeFiniteHankelWitness
import GaloisForLFunctions.RHTower.XiShiftedHardEdgeDyadicSampleCoherence

/-!
# Arbitrary complex-frequency evaluation of finite Route-U Chebyshev packets

The original finite-packet identity was restricted to multiplicity-labelled Xi divisor points.
This module proves the exact identity at every complex frequency where the two Cayley denominators
are nonzero.  It is the source-pure bridge needed to evaluate the literal explicit-formula pole at
`i / 2`; no zero-location statement or numerical computation enters.
-/

open scoped BigOperators SchwartzMap FourierTransform
open Complex Filter Polynomial

noncomputable section

namespace RHTower

theorem routeUComplexHardEdgePhase_character_eq_cayley_general
    (r : ℝ) (alpha : ℂ)
    (hplus : (routeUHardEdgeMass r : ℂ) + Complex.I * alpha ≠ 0)
    (hminus : (routeUHardEdgeMass r : ℂ) - Complex.I * alpha ≠ 0) :
    Complex.exp
        (Complex.I * routeUComplexHardEdgePhase r alpha *
          (routeUHardEdgeMesh r : ℂ)) =
      ((routeUHardEdgeMass r : ℂ) + Complex.I * alpha) /
        ((routeUHardEdgeMass r : ℂ) - Complex.I * alpha) := by
  let a : ℝ := routeUHardEdgeMass r
  have ha : (a : ℂ) ≠ 0 := ofReal_ne_zero.mpr (routeUHardEdgeMass_pos r).ne'
  have hnum : 1 + (alpha / (a : ℂ)) * Complex.I ≠ 0 := by
    rw [show 1 + (alpha / (a : ℂ)) * Complex.I =
        ((a : ℂ) + Complex.I * alpha) / (a : ℂ) by
      field_simp [ha]]
    exact div_ne_zero hplus ha
  have hden : 1 - (alpha / (a : ℂ)) * Complex.I ≠ 0 := by
    rw [show 1 - (alpha / (a : ℂ)) * Complex.I =
        ((a : ℂ) - Complex.I * alpha) / (a : ℂ) by
      field_simp [ha]]
    exact div_ne_zero hminus ha
  rw [routeUComplexHardEdgePhase, routeUHardEdgeMesh]
  change Complex.exp
      (Complex.I * ((a : ℂ) * Complex.arctan (alpha / (a : ℂ))) *
        ((2 / a : ℝ) : ℂ)) = _
  rw [Complex.arctan]
  have harg : (1 + (alpha / (a : ℂ)) * Complex.I) /
      (1 - (alpha / (a : ℂ)) * Complex.I) ≠ 0 := div_ne_zero hnum hden
  rw [show Complex.I *
      ((a : ℂ) * (-Complex.I / 2 * Complex.log
        ((1 + (alpha / (a : ℂ)) * Complex.I) /
          (1 - (alpha / (a : ℂ)) * Complex.I)))) *
        ((2 / a : ℝ) : ℂ) =
      Complex.log
        ((1 + (alpha / (a : ℂ)) * Complex.I) /
          (1 - (alpha / (a : ℂ)) * Complex.I)) by
      push_cast
      field_simp [ha]
      rw [Complex.I_sq]
      ring]
  rw [Complex.exp_log harg]
  field_simp [ha, hminus]
  ring

theorem routeUComplexHardEdgePhase_character_zpow_general
    (r : ℝ) (alpha : ℂ)
    (hplus : (routeUHardEdgeMass r : ℂ) + Complex.I * alpha ≠ 0)
    (hminus : (routeUHardEdgeMass r : ℂ) - Complex.I * alpha ≠ 0)
    (k : ℤ) :
    Complex.exp
        (Complex.I * routeUComplexHardEdgePhase r alpha *
          (((routeUHardEdgeMesh r) * (k : ℝ) : ℝ) : ℂ)) =
      (((routeUHardEdgeMass r : ℂ) + Complex.I * alpha) /
        ((routeUHardEdgeMass r : ℂ) - Complex.I * alpha)) ^ k := by
  rw [show Complex.I * routeUComplexHardEdgePhase r alpha *
      (((routeUHardEdgeMesh r) * (k : ℝ) : ℝ) : ℂ) =
      (k : ℂ) * (Complex.I * routeUComplexHardEdgePhase r alpha *
        (routeUHardEdgeMesh r : ℂ)) by
    push_cast
    ring]
  rw [Complex.exp_int_mul,
    routeUComplexHardEdgePhase_character_eq_cayley_general r alpha hplus hminus]

theorem routeUComplexHardEdgePhase_pair_eq_two_chebyshev_general
    (r : ℝ) (alpha : ℂ)
    (hplus : (routeUHardEdgeMass r : ℂ) + Complex.I * alpha ≠ 0)
    (hminus : (routeUHardEdgeMass r : ℂ) - Complex.I * alpha ≠ 0)
    (m : ℕ) :
    Complex.exp
        (Complex.I * routeUComplexHardEdgePhase r alpha *
          (((routeUHardEdgeMesh r) * (m : ℝ) : ℝ) : ℂ)) +
      Complex.exp
        (Complex.I * routeUComplexHardEdgePhase r alpha *
          (((routeUHardEdgeMesh r) * (-(m : ℝ)) : ℝ) : ℂ)) =
      2 * evalRealPolynomial (Polynomial.Chebyshev.T ℝ (m : ℤ))
        (xiHardEdgeCayleyCoordinate (routeUHardEdgeMass r : ℂ) alpha) := by
  let u : ℂ := ((routeUHardEdgeMass r : ℂ) + Complex.I * alpha) /
    ((routeUHardEdgeMass r : ℂ) - Complex.I * alpha)
  let v : ℂ := ((routeUHardEdgeMass r : ℂ) - Complex.I * alpha) /
    ((routeUHardEdgeMass r : ℂ) + Complex.I * alpha)
  have hv : v = u⁻¹ := by
    dsimp [u, v]
    exact (inv_div _ _).symm
  have hp := routeUComplexHardEdgePhase_character_zpow_general
    r alpha hplus hminus (m : ℤ)
  have hn := routeUComplexHardEdgePhase_character_zpow_general
    r alpha hplus hminus (-(m : ℤ))
  simp only [Int.cast_natCast, zpow_natCast] at hp
  simp only [Int.cast_neg, Int.cast_natCast, zpow_neg, zpow_natCast] at hn
  have hp' : Complex.exp
        (Complex.I * routeUComplexHardEdgePhase r alpha *
          (((routeUHardEdgeMesh r) * (m : ℝ) : ℝ) : ℂ)) = u ^ m := by
    simpa only [u] using hp
  have hn' : Complex.exp
        (Complex.I * routeUComplexHardEdgePhase r alpha *
          (((routeUHardEdgeMesh r) * (-(m : ℝ)) : ℝ) : ℂ)) = (u ^ m)⁻¹ := by
    simpa only [u, Int.cast_neg, Int.cast_natCast] using hn
  rw [hp', hn', evalRealPolynomial, Polynomial.Chebyshev.map_T,
    chebyshevT_eval_xiHardEdgeCayleyCoordinate hplus hminus]
  change u ^ m + (u ^ m)⁻¹ = 2 * (u ^ m / 2 + v ^ m / 2)
  rw [hv, inv_pow]
  ring

theorem routeUComplexHardEdgePeriodizationAt_eq_eval_finiteChebyshevPacket_of_pair
    (n : ℕ) (g : SchwartzMap ℝ ℝ) (r : ℝ) (N : ℕ)
    (hcut : ∀ j : ℕ, N ≤ j →
      SchwartzMap.compactSupportApproximation n (routeURealEvenAmplitude g)
        (routeUHardEdgeMesh r * (j + 1 : ℝ)) = 0)
    (z x : ℂ)
    (hpair : ∀ m : ℕ,
      Complex.exp
          (Complex.I * z *
            (((routeUHardEdgeMesh r) * (m : ℝ) : ℝ) : ℂ)) +
        Complex.exp
          (Complex.I * z *
            (((routeUHardEdgeMesh r) * (-(m : ℝ)) : ℝ) : ℂ)) =
        2 * evalRealPolynomial (Polynomial.Chebyshev.T ℝ (m : ℤ)) x) :
    routeUComplexHardEdgePeriodizationAt n (routeURealEvenAmplitude g) r
        z =
      evalRealPolynomial (routeUFiniteChebyshevPacketPolynomial n g r N) x := by
  let A : SchwartzMap ℝ ℂ :=
    SchwartzMap.compactSupportApproximation n (routeURealEvenAmplitude g)
  let E : ℤ → ℂ := fun k =>
    Complex.exp
        (Complex.I * z *
          (((routeUHardEdgeMesh r) * (k : ℝ) : ℝ) : ℂ)) *
      A (routeUHardEdgeMesh r * (k : ℝ))
  have htailPos : Summable fun j : ℕ => E ((j + 1 : ℕ) : ℤ) := by
    apply summable_of_ne_finset_zero (s := Finset.range N)
    intro j hj
    simp only [Finset.mem_range, not_lt] at hj
    simp only [E]
    rw [show ((((j + 1 : ℕ) : ℤ) : ℝ)) = (j : ℝ) + 1 by norm_num,
      show A (routeUHardEdgeMesh r * ((j : ℝ) + 1)) = 0 by
        simpa only [A, Nat.cast_add, Nat.cast_one] using hcut j hj]
    simp
  have hpos : Summable fun j : ℕ => E (j : ℤ) := by
    apply (summable_nat_add_iff 1).1
    simpa only [Nat.cast_add, Nat.cast_one] using htailPos
  have hneg : Summable fun j : ℕ => E (-((j : ℤ) + 1)) := by
    apply summable_of_ne_finset_zero (s := Finset.range N)
    intro j hj
    simp only [Finset.mem_range, not_lt] at hj
    simp only [E]
    have heven := routeURealEvenCompactApproximation_even n g
      (routeUHardEdgeMesh r * (j + 1 : ℝ))
    have harg : routeUHardEdgeMesh r * ((-((j : ℤ) + 1) : ℤ) : ℝ) =
        -(routeUHardEdgeMesh r * (j + 1 : ℝ)) := by
      push_cast
      ring
    rw [harg, heven, hcut j hj]
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
    simp only [E]
    rw [show ((((j + 1 : ℕ) : ℤ) : ℝ)) = (j : ℝ) + 1 by norm_num,
      show A (routeUHardEdgeMesh r * ((j : ℝ) + 1)) = 0 by
        simpa only [A, Nat.cast_add, Nat.cast_one] using hcut j hj]
    simp
  have htailNegFinite :
      (∑' j : ℕ, E (-((j : ℤ) + 1))) =
        ∑ j ∈ Finset.range N, E (-((j : ℤ) + 1)) := by
    rw [tsum_eq_sum (s := Finset.range N)]
    intro j hj
    simp only [Finset.mem_range, not_lt] at hj
    simp only [E]
    have heven := routeURealEvenCompactApproximation_even n g
      (routeUHardEdgeMesh r * (j + 1 : ℝ))
    have harg : routeUHardEdgeMesh r * ((-((j : ℤ) + 1) : ℤ) : ℝ) =
        -(routeUHardEdgeMesh r * (j + 1 : ℝ)) := by
      push_cast
      ring
    rw [harg, heven, hcut j hj]
    simp
  rw [routeUComplexHardEdgePeriodizationAt]
  change (routeUHardEdgeMesh r : ℂ) * (∑' k : ℤ, E k) = _
  rw [tsum_of_nat_of_neg_add_one hpos hneg, hhead,
    htailPosFinite, htailNegFinite]
  rw [routeUFiniteChebyshevPacketPolynomial, evalRealPolynomial]
  simp only [Polynomial.map_add, Polynomial.map_C, Polynomial.map_sum,
    Polynomial.map_mul, Polynomial.Chebyshev.map_T, Polynomial.eval_add,
    Polynomial.eval_C, Polynomial.eval_finsetSum, Polynomial.eval_mul]
  rw [mul_add, mul_add, Finset.mul_sum, Finset.mul_sum,
    add_assoc, ← Finset.sum_add_distrib]
  congr 1
  · simp only [E]
    simp only [Int.cast_zero, mul_zero, Complex.ofReal_zero,
      mul_zero, Complex.exp_zero, one_mul]
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
    rw [show (((((j + 1 : ℕ) : ℤ) : ℝ))) = (j : ℝ) + 1 by norm_num]
    have hreal := routeURealEvenCompactApproximation_im n g
      (routeUHardEdgeMesh r * (j + 1 : ℝ))
    have heven := routeURealEvenCompactApproximation_even n g
      (routeUHardEdgeMesh r * (j + 1 : ℝ))
    have harg : routeUHardEdgeMesh r * ((-((j : ℤ) + 1) : ℤ) : ℝ) =
        -(routeUHardEdgeMesh r * (j + 1 : ℝ)) := by
      push_cast
      ring
    rw [harg, heven]
    rw [show -(routeUHardEdgeMesh r * ((j : ℝ) + 1)) =
        routeUHardEdgeMesh r * (-((j + 1 : ℕ) : ℝ)) by
      push_cast
      ring]
    have hA : A (routeUHardEdgeMesh r * (j + 1 : ℝ)) =
        ((A (routeUHardEdgeMesh r * (j + 1 : ℝ))).re : ℂ) := by
      apply Complex.ext
      · simp
      · simpa only [A, Complex.ofReal_im] using hreal
    rw [hA]
    have hpairMode := hpair (j + 1)
    have hpair' :
        Complex.exp
            (Complex.I * z *
              (((routeUHardEdgeMesh r) * ((j + 1 : ℕ) : ℝ) : ℝ) : ℂ)) +
          Complex.exp
            (Complex.I * z *
              (((routeUHardEdgeMesh r) * (-((j + 1 : ℕ) : ℝ)) : ℝ) : ℂ)) =
          2 * Polynomial.eval
            x
            (Polynomial.Chebyshev.T ℂ ((j + 1 : ℕ) : ℤ)) := by
      simpa only [evalRealPolynomial, Polynomial.Chebyshev.map_T] using hpairMode
    simp only [Complex.ofReal_re]
    let X : ℂ := Complex.exp
      (Complex.I * z *
        (((routeUHardEdgeMesh r) * ((j : ℝ) + 1) : ℝ) : ℂ))
    let Y : ℂ := Complex.exp
      (Complex.I * z *
        (((routeUHardEdgeMesh r) * (-((j + 1 : ℕ) : ℝ)) : ℝ) : ℂ))
    let c : ℝ := (A (routeUHardEdgeMesh r * ((j : ℝ) + 1))).re
    let T : ℂ := Polynomial.eval
      x
      (Polynomial.Chebyshev.T ℂ ((j + 1 : ℕ) : ℤ))
    have hXY : X + Y = 2 * T := by
      dsimp only [X, Y, T]
      simpa only [Nat.cast_add, Nat.cast_one, Int.cast_add, Int.cast_natCast,
        Int.cast_one] using hpair'
    change (routeUHardEdgeMesh r : ℂ) * (X * (c : ℂ)) +
        (routeUHardEdgeMesh r : ℂ) * (Y * (c : ℂ)) =
      ((2 * routeUHardEdgeMesh r * c : ℝ) : ℂ) * T
    rw [show (routeUHardEdgeMesh r : ℂ) * (X * (c : ℂ)) +
        (routeUHardEdgeMesh r : ℂ) * (Y * (c : ℂ)) =
        (routeUHardEdgeMesh r : ℂ) * (c : ℂ) * (X + Y) by ring,
      hXY]
    push_cast
    ring

theorem routeUComplexHardEdgePeriodizationAt_phase_eq_eval_finiteChebyshevPacket
    (n : ℕ) (g : SchwartzMap ℝ ℝ) (r : ℝ) (N : ℕ)
    (hcut : ∀ j : ℕ, N ≤ j →
      SchwartzMap.compactSupportApproximation n (routeURealEvenAmplitude g)
        (routeUHardEdgeMesh r * (j + 1 : ℝ)) = 0)
    (alpha : ℂ)
    (hplus : (routeUHardEdgeMass r : ℂ) + Complex.I * alpha ≠ 0)
    (hminus : (routeUHardEdgeMass r : ℂ) - Complex.I * alpha ≠ 0) :
    routeUComplexHardEdgePeriodizationAt n (routeURealEvenAmplitude g) r
        (routeUComplexHardEdgePhase r alpha) =
      evalRealPolynomial (routeUFiniteChebyshevPacketPolynomial n g r N)
        (xiHardEdgeCayleyCoordinate (routeUHardEdgeMass r : ℂ) alpha) := by
  exact routeUComplexHardEdgePeriodizationAt_eq_eval_finiteChebyshevPacket_of_pair
    n g r N hcut (routeUComplexHardEdgePhase r alpha)
      (xiHardEdgeCayleyCoordinate (routeUHardEdgeMass r : ℂ) alpha)
      (routeUComplexHardEdgePhase_pair_eq_two_chebyshev_general
        r alpha hplus hminus)

end RHTower
