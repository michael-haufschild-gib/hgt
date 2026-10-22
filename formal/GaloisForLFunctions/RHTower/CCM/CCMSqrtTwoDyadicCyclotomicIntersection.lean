import GaloisForLFunctions.RHTower.CCM.CCMSqrtTwoIntegralTraceNorm

/-!
# The concrete dyadic cyclotomic intersection for CCM

The CCM coefficient theorem places the literal Lambert coefficients in the
concrete ring `ℤ^cyc[1/2]`.  This file makes the quadratic-field intersection
step literal on the carrier
`SqrtTwoRat = QuadraticAlgebra ℚ 2 0`.

The target is the faithful-embedding form of

`ℚ(√2) ∩ ℤ^cyc[1/2] = ℤ[√2][1/2]`.

No abstract number-field localization is used.  The right-hand localization
is represented by cleared `1, √2` coordinates, and the left-hand side by the
already literal `CCMDyadicCyclotomicInteger` predicate after the fixed real
embedding into `ℂ`.
-/

namespace RHTower

noncomputable section

open QuantumAlg.QubitTwoDesign

/-- The faithful complex realization of the literal quadratic carrier. -/
noncomputable def ccmSqrtTwoRatComplexEmbedding : SqrtTwoRat →ₐ[ℤ] ℂ where
  toRingHom := Complex.ofRealHom.comp sqrtTwoEval
  commutes' z := by
    change (Complex.ofRealHom.comp sqrtTwoEval) (algebraMap ℤ SqrtTwoRat z) = _
    simp

theorem ccmSqrtTwoRatComplexEmbedding_injective :
    Function.Injective ccmSqrtTwoRatComplexEmbedding := by
  exact Complex.ofReal_injective.comp sqrtTwoEval_injective

theorem ccm_sqrtTwoRat_isIntegral_of_complexEmbedding {x : SqrtTwoRat}
    (hx : IsIntegral ℤ (ccmSqrtTwoRatComplexEmbedding x)) : IsIntegral ℤ x := by
  exact (isIntegral_algHom_iff ccmSqrtTwoRatComplexEmbedding
    ccmSqrtTwoRatComplexEmbedding_injective).mp hx

theorem ccmSqrtTwoRatComplexEmbedding_scale (x : SqrtTwoRat) (d : ℕ) :
    ccmSqrtTwoRatComplexEmbedding
      (algebraMap ℚ SqrtTwoRat ((2 : ℚ) ^ d) * x) =
      (2 : ℂ) ^ d * ccmSqrtTwoRatComplexEmbedding x := by
  have hscalar : algebraMap ℚ SqrtTwoRat ((2 : ℚ) ^ d) = (2 : SqrtTwoRat) ^ d := by
    rw [map_pow, map_ofNat]
  have htwo : ccmSqrtTwoRatComplexEmbedding (2 : SqrtTwoRat) = (2 : ℂ) :=
    map_ofNat ccmSqrtTwoRatComplexEmbedding 2
  rw [hscalar, map_mul, map_pow, htwo]

/-- Concrete `ℤ[√2][1/2]` membership on the literal quadratic carrier. -/
def ccmSqrtTwoDyadicInteger (x : SqrtTwoRat) : Prop :=
  ∃ d : ℕ, ∃ a b : ℤ,
    (a : ℚ) = (algebraMap ℚ SqrtTwoRat ((2 : ℚ) ^ d) * x).re ∧
    (b : ℚ) = (algebraMap ℚ SqrtTwoRat ((2 : ℚ) ^ d) * x).im

theorem ccm_sqrtTwoDyadicInteger_of_complex_dyadicCyclotomic {x : SqrtTwoRat}
    (hx : CCMDyadicCyclotomicInteger (ccmSqrtTwoRatComplexEmbedding x)) :
    ccmSqrtTwoDyadicInteger x := by
  rcases hx with ⟨d, hd⟩
  have hscaled : IsIntegral ℤ
      (algebraMap ℚ SqrtTwoRat ((2 : ℚ) ^ d) * x) := by
    apply ccm_sqrtTwoRat_isIntegral_of_complexEmbedding
    rw [ccmSqrtTwoRatComplexEmbedding_scale]
    exact hd.isIntegral
  rcases ccm_sqrtTwoRat_integral_has_integer_coefficients hscaled with ⟨a, b, ha, hb⟩
  exact ⟨d, a, b, ha, hb⟩

theorem ccmSqrtTwoRatComplexEmbedding_apply (x : SqrtTwoRat) :
    ccmSqrtTwoRatComplexEmbedding x = (x.re : ℂ) +
      (x.im : ℂ) * (Real.sqrt 2 : ℂ) := by
  change (sqrtTwoEval x : ℂ) = _
  rw [sqrtTwoEval_apply]
  push_cast
  ring

theorem complex_dyadicCyclotomic_of_ccm_sqrtTwoDyadicInteger {x : SqrtTwoRat}
    (hx : ccmSqrtTwoDyadicInteger x) :
    CCMDyadicCyclotomicInteger (ccmSqrtTwoRatComplexEmbedding x) := by
  rcases hx with ⟨d, a, b, ha, hb⟩
  refine ⟨d, ?_⟩
  rw [← ccmSqrtTwoRatComplexEmbedding_scale]
  have hare : (a : ℂ) =
      ((algebraMap ℚ SqrtTwoRat ((2 : ℚ) ^ d) * x).re : ℂ) := by
    exact_mod_cast ha
  have hbim : (b : ℂ) =
      ((algebraMap ℚ SqrtTwoRat ((2 : ℚ) ^ d) * x).im : ℂ) := by
    exact_mod_cast hb
  rw [ccmSqrtTwoRatComplexEmbedding_apply, ← hare, ← hbim]
  exact (CCMCyclotomicInteger.intCast a).add
    ((CCMCyclotomicInteger.intCast b).mul ccmSqrtTwo_cyclotomicInteger)

/-- The exact concrete CCM intersection: the preimage of dyadic cyclotomic
integers under the fixed `ℚ(√2)` embedding is `ℤ[√2][1/2]`. -/
theorem ccm_sqrtTwoDyadicInteger_iff_complex_dyadicCyclotomic (x : SqrtTwoRat) :
    ccmSqrtTwoDyadicInteger x ↔
      CCMDyadicCyclotomicInteger (ccmSqrtTwoRatComplexEmbedding x) := by
  constructor
  · exact complex_dyadicCyclotomic_of_ccm_sqrtTwoDyadicInteger
  · exact ccm_sqrtTwoDyadicInteger_of_complex_dyadicCyclotomic

end
end RHTower
