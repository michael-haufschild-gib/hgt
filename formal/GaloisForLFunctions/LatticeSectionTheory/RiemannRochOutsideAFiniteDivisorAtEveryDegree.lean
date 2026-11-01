import GaloisForLFunctions.LatticeSectionTheory.BidegreeCountsSeeNoPrimitiveClass
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.SourceRiemannRochAwayFromTheLowFrequencyDivisor

/-!
# Riemann–Roch outside a finite divisor at every degree

Over a curve of genus `g` the Riemann inequality `h⁰(D) ≥ deg D + 1 − g` fails by at most `g`
conditions: finite genus means finitely many obstructing directions. Over `ℤ` the genus is
infinite, and this module states what replaces it.

At degree (aperture) `a`, let `D_a` be the low-frequency grid of ACS and `T_a` the real tests of
aperture `a` whose transforms vanish at the pole `i/2` and on `D_a`: `2#D_a + 2` real conditions.

* **Riemann–Roch on `T_a`** (`kunneth_effectivity_lowBlindTests`). On the scaling subsurface of
  `T_a` the Künneth count is an effectivity function, at every degree `a > 0`, unconditionally;
  the subsurface is not trivial.
* **Coercive primitive `h¹`** (`kunneth_primitive_h1_ge`). There the primitive `h¹` is coercive:
  `h¹(x) − h¹_K(x) = ½ W(f, f) ≥ ½ c_a ∫ f²` with `c_a = E(a)(1 − 1/π)`, `E(a) = 10 + 68 e^a`,
  growing in the degree. The finite divisor removes exactly the directions where the primitive `h¹` could be
  small or negative.

So the genus of `ℤ` is a function of the degree: the finite divisor `D_a ∪ {i/2}`. Finite at
every degree, unbounded as the degree grows; everything the Hodge index of `ℤ` still has to decide
sits on these finitely many directions at each degree. For the golden fake curve no finite divisor
works at any degree beyond `log 5 / 2` (`goldenDatum_no_finite_divisor`), so the law selects.
-/

noncomputable section

open Real MeasureTheory

namespace GaloisForLFunctions.LatticeSectionTheory

open ArithmeticCastelnuovoSeveri ArithmeticEffectivityTheory ArithmeticOrientationGeometry

/-- **Riemann–Roch outside the low-frequency divisor.** At every degree `a > 0` the Künneth count
is an effectivity function on the scaling subsurface of tests blind to the pole and to `D_a`. -/
theorem kunneth_effectivity_lowBlindTests {a : ℝ} (ha : 0 < a) :
    RiemannInequality (scalingSubsurface (lowBlindTests a)) 0 0
        (kunnethH0 (scalingSubsurface (lowBlindTests a))) ∧
      DegreeBounded (scalingSubsurface (lowBlindTests a))
        (kunnethH0 (scalingSubsurface (lowBlindTests a))) := by
  refine (kunneth_effectivity_scalingSubsurface_iff _).mpr fun f => ?_
  have h := lowBlindCoercivity_le_weilPair ha.le f
  have hc := (lowBlindCoercivity_pos a).le
  have hi : 0 ≤ ∫ u : ℝ, (f.1.1 u) ^ 2 := integral_nonneg fun u => sq_nonneg _
  exact (mul_nonneg hc hi).trans h

/-- **The primitive `h¹` is coercive outside the divisor**:
`h_K(x) + h_K(−x) − χ(x) − h¹_K(x) ≥ ½ c_a ∫ f²` on the subsurface of `T_a`. -/
theorem kunneth_primitive_h1_ge {a : ℝ} (ha : 0 ≤ a) (x : ℝ × ℝ × lowBlindTests a) :
    lowBlindCoercivity a * (∫ u : ℝ, (x.2.2.1.1 u) ^ 2) / 2 ≤
      kunnethH0 (scalingSubsurface (lowBlindTests a)) x +
        kunnethH0 (scalingSubsurface (lowBlindTests a)) (0 - x) -
        eulerChar (scalingSubsurface (lowBlindTests a)) 0 0 x -
        kunnethH1 (scalingSubsurface (lowBlindTests a)) x := by
  rw [kunneth_h1_sub_eq_half_defect, scalingSubsurface_defect_self]
  have h := lowBlindCoercivity_le_weilPair ha x.2.2
  linarith

/-- **The divisor is a proper constraint**: at every degree `a > 0` the subsurface carries a nonzero
test, so Riemann–Roch outside the divisor is not vacuous. -/
theorem exists_ne_zero_lowBlindTests {a : ℝ} (ha : 0 < a) :
    ∃ f : lowBlindTests a, (f : realTests) ≠ 0 :=
  exists_ne_zero_mem_lowBlindTests ha

end GaloisForLFunctions.LatticeSectionTheory
