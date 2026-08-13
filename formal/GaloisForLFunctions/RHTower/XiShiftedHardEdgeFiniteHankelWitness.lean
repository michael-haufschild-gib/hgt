import GaloisForLFunctions.RHTower.XiShiftedHardEdgeComplexPaleyWienerDivisorLimit
import GaloisForLFunctions.RHTower.XiShiftedHardEdgeCayleyDivisorLift
import GaloisForLFunctions.RHTower.BurnolCoPoissonIntertwiningLine
import GaloisForLFunctions.HTGeometry.SchwartzPositiveCompactDiagonal

/-!
# Exact finite Hankel witness for Route U

This module closes the algebraic gap between Route U's compact lattice sample and the finite
reciprocal-polynomial Hankel form. For every real-even compact approximation and every hard-edge
mass it constructs an explicit finite real Chebyshev packet, proves pointwise equality at every
multiplicity-labelled Xi zero, and identifies the complete weighted divisor sum with the existing
finite shifted-reciprocal Hankel quadratic. No numerical computation or zero-location hypothesis
is used.
-/

open scoped BigOperators SchwartzMap FourierTransform
open Complex Polynomial
noncomputable section

namespace RHTower

theorem routeUHardEdgeMass_add_I_mul_xiSpectralPoint_ne_zero (r : ℝ) (q : XiZeroCopy) :
    (routeUHardEdgeMass r : ℂ) + Complex.I * xiSpectralPoint q ≠ 0 := by
  let a := routeUHardEdgeMass r
  have hden : ((a ^ 2 : ℝ) : ℂ) + xiSpectralPoint q ^ 2 ≠ 0 :=
    ofReal_add_xiSquaredNode_ne_zero (sq_nonneg a) q
  have hprod : ((a : ℂ) + Complex.I * xiSpectralPoint q) *
      ((a : ℂ) - Complex.I * xiSpectralPoint q) =
      ((a ^ 2 : ℝ) : ℂ) + xiSpectralPoint q ^ 2 := by
    push_cast
    rw [show Complex.I * xiSpectralPoint q = xiSpectralPoint q * Complex.I by ring]
    ring_nf
    rw [Complex.I_sq]
    ring
  exact (mul_ne_zero_iff.mp (hprod.symm ▸ hden)).1

theorem routeUHardEdgeMass_sub_I_mul_xiSpectralPoint_ne_zero (r : ℝ) (q : XiZeroCopy) :
    (routeUHardEdgeMass r : ℂ) - Complex.I * xiSpectralPoint q ≠ 0 := by
  let a := routeUHardEdgeMass r
  have hden : ((a ^ 2 : ℝ) : ℂ) + xiSpectralPoint q ^ 2 ≠ 0 :=
    ofReal_add_xiSquaredNode_ne_zero (sq_nonneg a) q
  have hprod : ((a : ℂ) + Complex.I * xiSpectralPoint q) *
      ((a : ℂ) - Complex.I * xiSpectralPoint q) =
      ((a ^ 2 : ℝ) : ℂ) + xiSpectralPoint q ^ 2 := by
    push_cast
    rw [show Complex.I * xiSpectralPoint q = xiSpectralPoint q * Complex.I by ring]
    ring_nf
    rw [Complex.I_sq]
    ring
  exact (mul_ne_zero_iff.mp (hprod.symm ▸ hden)).2

theorem routeUComplexHardEdgePhase_character_eq_cayley (r : ℝ) (q : XiZeroCopy) :
    Complex.exp
        (Complex.I * routeUComplexHardEdgePhase r (xiSpectralPoint q) *
          (routeUHardEdgeMesh r : ℂ)) =
      ((routeUHardEdgeMass r : ℂ) + Complex.I * xiSpectralPoint q) /
        ((routeUHardEdgeMass r : ℂ) - Complex.I * xiSpectralPoint q) := by
  let a : ℝ := routeUHardEdgeMass r
  let alpha : ℂ := xiSpectralPoint q
  have ha : (a : ℂ) ≠ 0 := ofReal_ne_zero.mpr (routeUHardEdgeMass_pos r).ne'
  have hplus : (a : ℂ) + Complex.I * alpha ≠ 0 := routeUHardEdgeMass_add_I_mul_xiSpectralPoint_ne_zero r q
  have hminus : (a : ℂ) - Complex.I * alpha ≠ 0 := routeUHardEdgeMass_sub_I_mul_xiSpectralPoint_ne_zero r q
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

def routeURealEvenAmplitude (g : SchwartzMap ℝ ℝ) : SchwartzMap ℝ ℂ :=
  schwartzEvenPart (SchwartzMap.realToComplexSchwartz g)

theorem routeURealEvenAmplitude_even (g : SchwartzMap ℝ ℝ) (x : ℝ) :
    routeURealEvenAmplitude g (-x) = routeURealEvenAmplitude g x := by
  exact schwartzEvenPart_even _ x

theorem routeURealEvenAmplitude_im (g : SchwartzMap ℝ ℝ) (x : ℝ) :
    (routeURealEvenAmplitude g x).im = 0 := by
  simp [routeURealEvenAmplitude, schwartzEvenPart_apply,
    SchwartzMap.realToComplexSchwartz_apply, Complex.mul_im]

theorem scaledUnitCutoff_even (n : ℕ) (x : ℝ) :
    SchwartzMap.scaledUnitCutoff n (-x) = SchwartzMap.scaledUnitCutoff n x := by
  rw [SchwartzMap.scaledUnitCutoff_apply, SchwartzMap.scaledUnitCutoff_apply]
  simp only [mul_neg]
  rw [SchwartzMap.compactIntervalCutoff]
  simp only [HasCompactSupport.toSchwartzMap_toFun, Function.comp_apply]
  rw [ContDiffBump.neg]

theorem routeURealEvenCompactApproximation_even (n : ℕ) (g : SchwartzMap ℝ ℝ) (x : ℝ) :
    SchwartzMap.compactSupportApproximation n (routeURealEvenAmplitude g) (-x) =
      SchwartzMap.compactSupportApproximation n (routeURealEvenAmplitude g) x := by
  rw [SchwartzMap.compactSupportApproximation_apply,
    SchwartzMap.compactSupportApproximation_apply, scaledUnitCutoff_even,
    routeURealEvenAmplitude_even]

theorem routeURealEvenCompactApproximation_im (n : ℕ) (g : SchwartzMap ℝ ℝ) (x : ℝ) :
    (SchwartzMap.compactSupportApproximation n (routeURealEvenAmplitude g) x).im = 0 := by
  rw [SchwartzMap.compactSupportApproximation_apply]
  simp [routeURealEvenAmplitude_im, Complex.mul_im,
    SchwartzMap.scaledUnitCutoff_apply, SchwartzMap.compactIntervalCutoff]

theorem exists_complex_physicalLattice_cutoff_of_hasCompactSupport
    {f : ℝ → ℂ} (hcompact : HasCompactSupport f)
    {h : ℝ} (hh : 0 < h) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → f (h * (n + 1 : ℝ)) = 0 := by
  obtain ⟨B, hB⟩ := hcompact.isCompact.isBounded.exists_norm_le
  obtain ⟨N, hN⟩ := exists_nat_gt (B / h)
  refine ⟨N, ?_⟩
  intro n hn
  by_contra hx
  have hsupp : h * (n + 1 : ℝ) ∈ Function.support f := by
    simpa only [Function.mem_support] using hx
  have hxt : h * (n + 1 : ℝ) ∈ tsupport f := subset_tsupport f hsupp
  have hbound := hB _ hxt
  have hNlt : N < n + 1 := by omega
  have hcast : (N : ℝ) < (n : ℝ) + 1 := by exact_mod_cast hNlt
  have hlarge : B < h * (n + 1 : ℝ) := by
    have hBN : B < h * N := by
      simpa [mul_comm] using (div_lt_iff₀ hh).mp hN
    exact hBN.trans (mul_lt_mul_of_pos_left hcast hh)
  have hxnonneg : 0 ≤ h * (n + 1 : ℝ) := by positivity
  rw [Real.norm_eq_abs, abs_of_nonneg hxnonneg] at hbound
  exact (not_lt_of_ge hbound) hlarge

theorem routeUComplexHardEdgePhase_character_zpow (r : ℝ) (q : XiZeroCopy) (k : ℤ) :
    Complex.exp
        (Complex.I * routeUComplexHardEdgePhase r (xiSpectralPoint q) *
          (((routeUHardEdgeMesh r) * (k : ℝ) : ℝ) : ℂ)) =
      (((routeUHardEdgeMass r : ℂ) + Complex.I * xiSpectralPoint q) /
        ((routeUHardEdgeMass r : ℂ) - Complex.I * xiSpectralPoint q)) ^ k := by
  rw [show Complex.I * routeUComplexHardEdgePhase r (xiSpectralPoint q) *
      (((routeUHardEdgeMesh r) * (k : ℝ) : ℝ) : ℂ) =
      (k : ℂ) * (Complex.I * routeUComplexHardEdgePhase r (xiSpectralPoint q) *
        (routeUHardEdgeMesh r : ℂ)) by
    push_cast
    ring]
  rw [Complex.exp_int_mul, routeUComplexHardEdgePhase_character_eq_cayley]

theorem evalRealChebyshev_xiHardEdgeCayleyCoordinate (r : ℝ) (q : XiZeroCopy) (m : ℕ) :
    evalRealPolynomial (Polynomial.Chebyshev.T ℝ (m : ℤ))
        (xiHardEdgeCayleyCoordinate (routeUHardEdgeMass r : ℂ)
          (xiSpectralPoint q)) =
      ((((routeUHardEdgeMass r : ℂ) + Complex.I * xiSpectralPoint q) /
          ((routeUHardEdgeMass r : ℂ) - Complex.I * xiSpectralPoint q)) ^ m) / 2 +
        ((((routeUHardEdgeMass r : ℂ) - Complex.I * xiSpectralPoint q) /
          ((routeUHardEdgeMass r : ℂ) + Complex.I * xiSpectralPoint q)) ^ m) / 2 := by
  rw [evalRealPolynomial, Polynomial.Chebyshev.map_T]
  exact chebyshevT_eval_xiHardEdgeCayleyCoordinate
    (routeUHardEdgeMass_add_I_mul_xiSpectralPoint_ne_zero r q) (routeUHardEdgeMass_sub_I_mul_xiSpectralPoint_ne_zero r q) m

theorem routeUComplexHardEdgePhase_pair_eq_two_chebyshev (r : ℝ) (q : XiZeroCopy) (m : ℕ) :
    Complex.exp
        (Complex.I * routeUComplexHardEdgePhase r (xiSpectralPoint q) *
          (((routeUHardEdgeMesh r) * (m : ℝ) : ℝ) : ℂ)) +
      Complex.exp
        (Complex.I * routeUComplexHardEdgePhase r (xiSpectralPoint q) *
          (((routeUHardEdgeMesh r) * (-(m : ℝ)) : ℝ) : ℂ)) =
      2 * evalRealPolynomial (Polynomial.Chebyshev.T ℝ (m : ℤ))
        (xiHardEdgeCayleyCoordinate (routeUHardEdgeMass r : ℂ)
          (xiSpectralPoint q)) := by
  let u : ℂ := ((routeUHardEdgeMass r : ℂ) + Complex.I * xiSpectralPoint q) /
    ((routeUHardEdgeMass r : ℂ) - Complex.I * xiSpectralPoint q)
  let v : ℂ := ((routeUHardEdgeMass r : ℂ) - Complex.I * xiSpectralPoint q) /
    ((routeUHardEdgeMass r : ℂ) + Complex.I * xiSpectralPoint q)
  have hv : v = u⁻¹ := by
    dsimp [u, v]
    exact (inv_div _ _).symm
  have hp := routeUComplexHardEdgePhase_character_zpow r q (m : ℤ)
  have hn := routeUComplexHardEdgePhase_character_zpow r q (-(m : ℤ))
  simp only [Int.cast_natCast, zpow_natCast] at hp
  simp only [Int.cast_neg, Int.cast_natCast, zpow_neg, zpow_natCast] at hn
  have hp' : Complex.exp
        (Complex.I * routeUComplexHardEdgePhase r (xiSpectralPoint q) *
          (((routeUHardEdgeMesh r) * (m : ℝ) : ℝ) : ℂ)) = u ^ m := by
    simpa only [u] using hp
  have hn' : Complex.exp
        (Complex.I * routeUComplexHardEdgePhase r (xiSpectralPoint q) *
          (((routeUHardEdgeMesh r) * (-(m : ℝ)) : ℝ) : ℂ)) = (u ^ m)⁻¹ := by
    simpa only [u, Int.cast_neg, Int.cast_natCast] using hn
  rw [hp', hn', evalRealChebyshev_xiHardEdgeCayleyCoordinate]
  change u ^ m + (u ^ m)⁻¹ = 2 * (u ^ m / 2 + v ^ m / 2)
  rw [hv, inv_pow]
  ring

def routeUFiniteChebyshevPacketPolynomial (n : ℕ) (g : SchwartzMap ℝ ℝ) (r : ℝ) (N : ℕ) :
    Polynomial ℝ :=
  Polynomial.C
      (routeUHardEdgeMesh r *
        (SchwartzMap.compactSupportApproximation n (routeURealEvenAmplitude g) 0).re) +
    ∑ j ∈ Finset.range N,
      Polynomial.C
          (2 * routeUHardEdgeMesh r *
            (SchwartzMap.compactSupportApproximation n (routeURealEvenAmplitude g)
              (routeUHardEdgeMesh r * (j + 1 : ℝ))).re) *
        Polynomial.Chebyshev.T ℝ ((j + 1 : ℕ) : ℤ)

theorem exists_routeUFiniteChebyshevPacket_cutoff (n : ℕ) (g : SchwartzMap ℝ ℝ) (r : ℝ) :
    ∃ N : ℕ, ∀ j : ℕ, N ≤ j →
      SchwartzMap.compactSupportApproximation n (routeURealEvenAmplitude g)
        (routeUHardEdgeMesh r * (j + 1 : ℝ)) = 0 := by
  exact exists_complex_physicalLattice_cutoff_of_hasCompactSupport
    (SchwartzMap.compactSupportApproximation_hasCompactSupport n (routeURealEvenAmplitude g))
    (routeUHardEdgeMesh_pos r)

theorem routeUXiComplexHardEdgeSample_eq_eval_finiteChebyshevPacket
    (n : ℕ) (g : SchwartzMap ℝ ℝ) (r : ℝ) (N : ℕ)
    (hcut : ∀ j : ℕ, N ≤ j →
      SchwartzMap.compactSupportApproximation n (routeURealEvenAmplitude g)
        (routeUHardEdgeMesh r * (j + 1 : ℝ)) = 0)
    (q : XiZeroCopy) :
    routeUXiComplexHardEdgeSample n (routeURealEvenAmplitude g) r q =
      evalRealPolynomial (routeUFiniteChebyshevPacketPolynomial n g r N)
        (xiHardEdgeCayleyCoordinate (routeUHardEdgeMass r : ℂ)
          (xiSpectralPoint q)) := by
  let A : SchwartzMap ℝ ℂ :=
    SchwartzMap.compactSupportApproximation n (routeURealEvenAmplitude g)
  let E : ℤ → ℂ := fun k =>
    Complex.exp
        (Complex.I * routeUComplexHardEdgePhase r (xiSpectralPoint q) *
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
  rw [routeUXiComplexHardEdgeSample]
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
    have hpair := routeUComplexHardEdgePhase_pair_eq_two_chebyshev r q (j + 1)
    have hpair' :
        Complex.exp
            (Complex.I * routeUComplexHardEdgePhase r (xiSpectralPoint q) *
              (((routeUHardEdgeMesh r) * ((j + 1 : ℕ) : ℝ) : ℝ) : ℂ)) +
          Complex.exp
            (Complex.I * routeUComplexHardEdgePhase r (xiSpectralPoint q) *
              (((routeUHardEdgeMesh r) * (-((j + 1 : ℕ) : ℝ)) : ℝ) : ℂ)) =
          2 * Polynomial.eval
            (xiHardEdgeCayleyCoordinate (routeUHardEdgeMass r : ℂ) (xiSpectralPoint q))
            (Polynomial.Chebyshev.T ℂ ((j + 1 : ℕ) : ℤ)) := by
      simpa only [evalRealPolynomial, Polynomial.Chebyshev.map_T] using hpair
    simp only [Complex.ofReal_re]
    let X : ℂ := Complex.exp
      (Complex.I * routeUComplexHardEdgePhase r (xiSpectralPoint q) *
        (((routeUHardEdgeMesh r) * ((j : ℝ) + 1) : ℝ) : ℂ))
    let Y : ℂ := Complex.exp
      (Complex.I * routeUComplexHardEdgePhase r (xiSpectralPoint q) *
        (((routeUHardEdgeMesh r) * (-((j + 1 : ℕ) : ℝ)) : ℝ) : ℂ))
    let c : ℝ := (A (routeUHardEdgeMesh r * ((j : ℝ) + 1))).re
    let T : ℂ := Polynomial.eval
      (xiHardEdgeCayleyCoordinate (routeUHardEdgeMass r : ℂ) (xiSpectralPoint q))
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

theorem routeUXiComplexHardEdgeSampleDivisorTerm_eq_hardEdgeDivisorPacket
    (n : ℕ) (g : SchwartzMap ℝ ℝ) (r : ℝ) (N : ℕ)
    (hcut : ∀ j : ℕ, N ≤ j →
      SchwartzMap.compactSupportApproximation n (routeURealEvenAmplitude g)
        (routeUHardEdgeMesh r * (j + 1 : ℝ)) = 0)
    (q : XiZeroCopy) :
    routeUXiComplexHardEdgeSampleDivisorTerm n (routeURealEvenAmplitude g) r q =
      xiHardEdgeDivisorPacketTerm (routeUHardEdgeMass r)
        (routeUFiniteChebyshevPacketPolynomial n g r N) q := by
  rw [routeUXiComplexHardEdgeSampleDivisorTerm, routeUXiHardEdgeResolventWeight,
    xiHardEdgeDivisorPacketTerm, routeUXiComplexHardEdgeSample_eq_eval_finiteChebyshevPacket n g r N hcut q]

theorem routeUFiniteHankelQuadratic_eq_sampleDivisorSum
    (n : ℕ) (g : SchwartzMap ℝ ℝ) (r : ℝ) (N : ℕ)
    (hcut : ∀ j : ℕ, N ≤ j →
      SchwartzMap.compactSupportApproximation n (routeURealEvenAmplitude g)
        (routeUHardEdgeMesh r * (j + 1 : ℝ)) = 0) :
    routeUHardEdgeMass r ^ 2 *
        xiShiftedReciprocalHankelQuadratic (routeUHardEdgeMass r ^ 2)
          (xiHardEdgeLiftCoefficients (routeUHardEdgeMass r)
            (routeUFiniteChebyshevPacketPolynomial n g r N)) =
      (∑' q : XiZeroCopy,
        routeUXiComplexHardEdgeSampleDivisorTerm n (routeURealEvenAmplitude g) r q).re := by
  rw [xiHardEdgeLift_hankelQuadratic_eq_divisorPacket]
  congr 1
  apply tsum_congr
  exact fun q => (routeUXiComplexHardEdgeSampleDivisorTerm_eq_hardEdgeDivisorPacket n g r N hcut q).symm

theorem exists_routeUExactFiniteHankelWitness
    (n : ℕ) (g : SchwartzMap ℝ ℝ) (r : ℝ) :
    ∃ N : ℕ,
      (∀ q : XiZeroCopy,
        routeUXiComplexHardEdgeSample n (routeURealEvenAmplitude g) r q =
          evalRealPolynomial (routeUFiniteChebyshevPacketPolynomial n g r N)
            (xiHardEdgeCayleyCoordinate (routeUHardEdgeMass r : ℂ)
              (xiSpectralPoint q))) ∧
      routeUHardEdgeMass r ^ 2 *
          xiShiftedReciprocalHankelQuadratic (routeUHardEdgeMass r ^ 2)
            (xiHardEdgeLiftCoefficients (routeUHardEdgeMass r)
              (routeUFiniteChebyshevPacketPolynomial n g r N)) =
        (∑' q : XiZeroCopy,
          routeUXiComplexHardEdgeSampleDivisorTerm n (routeURealEvenAmplitude g) r q).re := by
  obtain ⟨N, hN⟩ := exists_routeUFiniteChebyshevPacket_cutoff n g r
  exact ⟨N, routeUXiComplexHardEdgeSample_eq_eval_finiteChebyshevPacket n g r N hN,
    routeUFiniteHankelQuadratic_eq_sampleDivisorSum n g r N hN⟩

end RHTower

