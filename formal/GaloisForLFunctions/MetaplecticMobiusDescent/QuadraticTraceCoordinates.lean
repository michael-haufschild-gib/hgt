/-
Portions adapted from OpenAI’s quadratic trace formalization, Apache-2.0.
See LICENSE and NOTICE in this directory for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.TheDifferentNormalizesTheTraceCharacter
import GaloisForLFunctions.MetaplecticMobiusDescent.EisensteinCoordinates

/-!
# Integral coordinates of the quadratic trace phase

The trace pairing is the alternating coordinate pairing divided by the norm.
The fixed dual phase is a quadratic trace phase modulo four, periodic modulo
two in its argument. Its four-residue average is explicit.
-/

noncomputable section
open scoped BigOperators
namespace GaloisForLFunctions.MetaplecticMobiusDescent.Eisenstein
open Coordinates

/-- Dividing by a principal modulus gives the alternating coordinate pairing over its norm. -/
theorem trace_fraction_coordinates (a b x y : ℤ) (hc : eval a b ≠ 0) :
    Algebra.trace ℚ K
      (algebraMap O K (eval x y) /
        (algebraMap O K traceLambda * algebraMap O K (eval a b))) =
      ((a*y-b*x : ℤ) : ℚ) / ((a*a-a*b+b*b : ℤ) : ℚ) := by
  have hcK : algebraMap O K (eval a b) ≠ 0 :=
    fun h => hc (NumberField.RingOfIntegers.coe_injective h)
  have hnorm : algebraMap O K (eval a b) * algebraMap O K (conjO (eval a b)) =
      ((a*a-a*b+b*b : ℤ) : K) := by
    have h := congrArg (algebraMap O K) (eval_mul_conj a b)
    simpa only [map_mul, map_intCast, pow_two] using h
  have hnum : algebraMap O K (eval x y) * algebraMap O K (conjO (eval a b)) =
      ((x*(a-b)+y*b : ℤ) : K) + ((a*y-b*x : ℤ) : K) * algebraMap O K omega := by
    rw [← map_mul, conj_eval, eval_mul]
    simp only [eval, map_add, map_mul, map_intCast]
    push_cast
    ring
  have hquot : algebraMap O K (eval x y) / algebraMap O K (eval a b) =
      ((((x*(a-b)+y*b : ℤ) : ℚ) / ((a*a-a*b+b*b : ℤ) : ℚ)) : K) +
      ((((a*y-b*x : ℤ) : ℚ) / ((a*a-a*b+b*b : ℤ) : ℚ)) : K) * algebraMap O K omega := by
    calc
      _ = (algebraMap O K (eval x y) * algebraMap O K (conjO (eval a b))) /
          ((a*a-a*b+b*b : ℤ) : K) := by
        rw [← hnorm]
        have hconj : algebraMap O K (conjO (eval a b)) ≠ 0 := by
          intro h
          apply hc
          apply conjO.injective
          simpa only [map_zero] using NumberField.RingOfIntegers.coe_injective h
        field_simp [hcK, hconj]
      _ = _ := by rw [hnum]; push_cast; ring
  have harg : algebraMap O K (eval x y) /
      (algebraMap O K traceLambda * algebraMap O K (eval a b)) =
      (algebraMap O K (eval x y) / algebraMap O K (eval a b)) /
        algebraMap O K traceLambda := by
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  rw [harg, hquot]
  convert trace_div_traceLambda
    (((x*(a-b)+y*b : ℤ) : ℚ) / ((a*a-a*b+b*b : ℤ) : ℚ))
    (((a*y-b*x : ℤ) : ℚ) / ((a*a-a*b+b*b : ℤ) : ℚ)) using 1
  push_cast
  rfl

/-- The analytic trace character in integral coordinates. -/
theorem principalTraceChar_eval (a b x y : ℤ) (hc : eval a b ≠ 0) :
    principalTraceChar (eval a b) hc (Ideal.Quotient.mk (Ideal.span {eval a b}) (eval x y)) =
      Complex.exp (2 * Real.pi * Complex.I *
        (((a*y-b*x : ℤ) : ℂ) / ((a*a-a*b+b*b : ℤ) : ℂ))) := by
  rw [principalTraceChar_apply, trace_fraction_coordinates a b x y hc]
  congr 1
  push_cast
  ring

/-- Squaring the residue argument gives the oscillatory binary phase. -/
theorem principalTraceChar_square (a b x y : ℤ) (hc : eval a b ≠ 0) :
    principalTraceChar (eval a b) hc
      (Ideal.Quotient.mk (Ideal.span {eval a b}) (eval x y) ^ 2) =
      Complex.exp (2 * Real.pi * Complex.I *
        (((-b*x*x+2*a*x*y+(b-a)*y*y : ℤ) : ℂ) /
          ((a*a-a*b+b*b : ℤ) : ℂ))) := by
  rw [← map_pow, pow_two, eval_mul, principalTraceChar_eval]
  congr 1
  push_cast
  ring

/-- The quadratic trace sum on the actual principal quotient. -/
def quadraticTraceGauss (c : O) (hc : c ≠ 0) : ℂ := by
  letI : Finite (O ⧸ Ideal.span {c}) :=
    (Ideal.span {c}).finiteQuotientOfFreeOfNeBot
      (fun h => hc (Ideal.span_singleton_eq_bot.mp h))
  letI : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
  exact ∑ x : O ⧸ Ideal.span {c}, principalTraceChar c hc (x ^ 2)

/-- Divide the quadratic trace sum by the complex modulus of the generator. -/
def normalizedQuadraticTraceGauss (c : O) (hc : c ≠ 0) : ℂ :=
  quadraticTraceGauss c hc / (‖ringComplex c‖ : ℂ)

/-- The fixed dual phase is an actual quadratic residue phase modulo four. -/
def fixedDualPhase (c y : O) : ℂ :=
  principalTraceChar 4 (by norm_num) (Ideal.Quotient.mk (Ideal.span {(4 : O)}) (-(c*y^2)))

/-- A shift by two changes the squared numerator by a multiple of four. -/
theorem fixedDualPhase_period_two (c y w : O) :
    fixedDualPhase c (y + 2*w) = fixedDualPhase c y := by
  apply congrArg (principalTraceChar 4 (by norm_num))
  apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr
  apply Ideal.mem_span_singleton.mpr
  refine ⟨-(c * (y*w+w^2)), ?_⟩
  ring

theorem fixedDualPhase_eq_of_mod_two (c y z : O)
    (h : Ideal.Quotient.mk (Ideal.span {(2 : O)}) y =
      Ideal.Quotient.mk (Ideal.span {(2 : O)}) z) :
    fixedDualPhase c y = fixedDualPhase c z := by
  have hsub : y-z ∈ Ideal.span {(2 : O)} :=
    (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp h
  obtain ⟨w, hw⟩ := Ideal.mem_span_singleton.mp hsub
  have hy : y = z + 2*w := by
    calc
      y = z+(y-z) := by ring
      _ = z+2*w := by rw [hw]
  rw [hy, fixedDualPhase_period_two]

/-- At modulus four, the analytic character is the fourth root prescribed by the second coordinate. -/
theorem principalTraceChar_four (x y : ℤ) :
    principalTraceChar 4 (by norm_num)
      (Ideal.Quotient.mk (Ideal.span {(4 : O)}) (eval x y)) = Complex.I ^ y := by
  have h4 : eval 4 0 = 4 := by norm_num [eval]
  have ht := trace_fraction_coordinates 4 0 x y (by rw [h4]; norm_num)
  rw [h4] at ht
  rw [principalTraceChar_apply, ht]
  calc
    _ = Complex.exp ((y : ℂ) * ((Real.pi : ℂ) / 2 * Complex.I)) := by
      congr 1
      push_cast
      ring
    _ = Complex.I ^ y := by
      rw [Complex.exp_int_mul, Complex.exp_pi_div_two_mul_I]

private theorem neg_eval (a b : ℤ) : -eval a b = eval (-a) (-b) := by
  simp only [eval, Int.cast_neg]
  ring

/-- The fixed dual phase is a fourth root of unity with an explicit integral exponent. -/
theorem fixedDualPhase_eval (a b x y : ℤ) :
    fixedDualPhase (eval a b) (eval x y) =
      Complex.I ^ (-(b*x*x + 2*(a-b)*x*y - a*y*y)) := by
  unfold fixedDualPhase
  rw [pow_two, eval_mul, eval_mul, neg_eval, principalTraceChar_four]
  congr 1
  ring

/-- The fixed phase has unit modulus. -/
theorem fixedDualPhase_norm (c y : O) : ‖fixedDualPhase c y‖ = 1 := by
  obtain ⟨a,b,rfl⟩ := exists_coordinates c
  obtain ⟨x,y,rfl⟩ := exists_coordinates y
  change ‖fixedDualPhase (eval a b) (eval x y)‖ = 1
  rw [fixedDualPhase_eval, norm_zpow, Complex.norm_I, one_zpow]

/-- The four residue phases, with the normalization from the rank-two Gaussian transform. -/
def fixedDualAverage (c : O) : ℂ := by
  letI : Finite (O ⧸ Ideal.span {(2 : O)}) :=
    (Ideal.span {(2 : O)}).finiteQuotientOfFreeOfNeBot
      (fun h => (by norm_num : (2 : O) ≠ 0) (Ideal.span_singleton_eq_bot.mp h))
  letI : Fintype (O ⧸ Ideal.span {(2 : O)}) := Fintype.ofFinite _
  exact (∑ r : O ⧸ Ideal.span {(2 : O)},
    fixedDualPhase c (Classical.choose (Ideal.Quotient.mk_surjective r))) / 2

private theorem sum_zmod_two_square (f : ZMod 2 × ZMod 2 → ℂ) :
    (∑ p : ZMod 2 × ZMod 2, f p) =
      f (0,0) + f (0,1) + f (1,0) + f (1,1) := by
  rw [Fintype.sum_prod_type]
  have hu : (Finset.univ : Finset (ZMod 2)) = {0,1} := rfl
  simp [hu]
  ring

/-- The dual residue average depends only on the modulus coordinates modulo four. -/
theorem fixedDualAverage_formula (a b : ℤ) :
    fixedDualAverage (eval a b) =
      (1 + Complex.I ^ (-b) + Complex.I ^ a + Complex.I ^ (b-a)) / 2 := by
  letI : Finite (O ⧸ Ideal.span {(2 : O)}) :=
    (Ideal.span {(2 : O)}).finiteQuotientOfFreeOfNeBot
      (fun h => (by norm_num : (2 : O) ≠ 0) (Ideal.span_singleton_eq_bot.mp h))
  letI : Fintype (O ⧸ Ideal.span {(2 : O)}) := Fintype.ofFinite _
  let e := rationalCoordEquiv 2 (by norm_num)
  let P : O ⧸ Ideal.span {(2 : O)} → ℂ := fun r =>
    fixedDualPhase (eval a b) (Classical.choose (Ideal.Quotient.mk_surjective r))
  have hpoint (p : ZMod 2 × ZMod 2) : P (e p) =
      fixedDualPhase (eval a b) (eval (ZMod.cast p.1) (ZMod.cast p.2)) := by
    apply fixedDualPhase_eq_of_mod_two
    exact (Classical.choose_spec (Ideal.Quotient.mk_surjective (e p))).trans (by rfl)
  have hsum : (∑ r, P r) = ∑ p : ZMod 2 × ZMod 2,
      fixedDualPhase (eval a b) (eval (ZMod.cast p.1) (ZMod.cast p.2)) := by
    calc
      _ = ∑ p, P (e p) := (e.sum_comp P).symm
      _ = _ := Finset.sum_congr rfl (fun p _ => hpoint p)
  change (∑ r, P r) / 2 = _
  rw [hsum, sum_zmod_two_square]
  have hcast1 : (ZMod.cast (1 : ZMod 2) : ℤ) = 1 := by decide
  simp only [ZMod.cast_zero, hcast1, fixedDualPhase_eval,
    mul_zero, mul_one, add_zero, sub_zero, neg_zero, zero_sub, zpow_zero, neg_neg]
  rw [show -(b + 2 * (a-b) - a) = b-a by ring]
  ring

theorem fixedDualPhase_eq_of_mod_four (c d y : O)
    (h : Ideal.Quotient.mk (Ideal.span {(4 : O)}) c =
      Ideal.Quotient.mk (Ideal.span {(4 : O)}) d) :
    fixedDualPhase c y = fixedDualPhase d y := by
  simp only [fixedDualPhase, map_neg, map_mul, h]

/-- The complete dual average factors through reduction of the modulus modulo four. -/
theorem fixedDualAverage_eq_of_mod_four (c d : O)
    (h : Ideal.Quotient.mk (Ideal.span {(4 : O)}) c =
      Ideal.Quotient.mk (Ideal.span {(4 : O)}) d) :
    fixedDualAverage c = fixedDualAverage d := by
  unfold fixedDualAverage
  congr 1
  exact Finset.sum_congr rfl (fun r _ => fixedDualPhase_eq_of_mod_four c d _ h)

theorem fixedDualAverage_one : fixedDualAverage 1 = 1 := by
  have h := fixedDualAverage_formula 1 0
  norm_num [eval] at h
  exact h

/-- The principal residue class modulo four has trivial dual Gauss phase. -/
theorem fixedDualAverage_eq_one (c : O)
    (h : Ideal.Quotient.mk (Ideal.span {(4 : O)}) c = 1) :
    fixedDualAverage c = 1 := by
  rw [fixedDualAverage_eq_of_mod_four c 1 (by simpa only [map_one] using h),
    fixedDualAverage_one]

end GaloisForLFunctions.MetaplecticMobiusDescent.Eisenstein

#print axioms GaloisForLFunctions.MetaplecticMobiusDescent.Eisenstein.trace_fraction_coordinates

#print axioms GaloisForLFunctions.MetaplecticMobiusDescent.Eisenstein.principalTraceChar_square

#print axioms GaloisForLFunctions.MetaplecticMobiusDescent.Eisenstein.fixedDualAverage_formula

#print axioms GaloisForLFunctions.MetaplecticMobiusDescent.Eisenstein.fixedDualAverage_eq_one
