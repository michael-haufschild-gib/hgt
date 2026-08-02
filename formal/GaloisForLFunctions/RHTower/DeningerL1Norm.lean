import GaloisForLFunctions.RHTower.DeningerHeightL1
import GaloisForLFunctions.RHTower.DeningerScaleFactorization

/-!
# The `ℓ¹` norm of the test space of places, and the Banach step

The sum of the absolute values of a test function on the space of places is a seminorm: finitely
many terms are nonzero, the triangle inequality is pointwise, and scalars come out.  Its completed
quotient is the Banach space of the scale, into which the test space maps densely.

On the logarithmic Kummer functions this seminorm is twice the Weil height, so the Banach step of
the scale is the completion of the Kummer functions in the height norm.

* `deningerL1Seminorm` : the `ℓ¹` seminorm of the test space of places.
* `deningerL1Seminorm_kummer` : on Kummer functions it is twice the height.
* `deningerL1_denseRange` : **the test space maps densely into its `ℓ¹` completion.**
-/

namespace RHTower

open NumberField

section L1Norm

variable (K : Type*) [Field K] [NumberField K]

theorem deningerPlaceAbs_finite_support (g : DeningerTestSpace (DeningerPlace K)) :
    Function.HasFiniteSupport fun v => |(g : DeningerPlace K → ℝ) v| := by
  have hfin : (Function.support ((g : DeningerPlace K → ℝ))).Finite := g.2.2.finite_of_discrete
  refine Set.Finite.subset hfin ?_
  intro v hv hzero
  apply hv
  show |(g : DeningerPlace K → ℝ) v| = 0
  rw [hzero, abs_zero]

/-- **The `ℓ¹` seminorm of a test function on the space of places.** -/
noncomputable def deningerL1Seminorm : Seminorm ℝ (DeningerTestSpace (DeningerPlace K)) :=
  Seminorm.ofSMulLE (fun g => ∑ᶠ v, |(g : DeningerPlace K → ℝ) v|)
    (by simp)
    (by
      intro g h
      have hg := deningerPlaceAbs_finite_support K g
      have hh := deningerPlaceAbs_finite_support K h
      have hgh := deningerPlaceAbs_finite_support K (g + h)
      have hle : (fun v => |((g + h : DeningerTestSpace (DeningerPlace K)) :
            DeningerPlace K → ℝ) v|)
          ≤ fun v => |(g : DeningerPlace K → ℝ) v| + |(h : DeningerPlace K → ℝ) v| := by
        intro v
        exact abs_add_le _ _
      have hsum : Function.HasFiniteSupport
          fun v => |(g : DeningerPlace K → ℝ) v| + |(h : DeningerPlace K → ℝ) v| := by
        refine Set.Finite.subset (hg.union hh) ?_
        intro v hv
        by_contra hmem
        simp only [Set.mem_union, Function.mem_support, not_or, not_not] at hmem
        apply hv
        show |(g : DeningerPlace K → ℝ) v| + |(h : DeningerPlace K → ℝ) v| = 0
        rw [hmem.1, hmem.2, add_zero]
      refine le_trans (finsum_le_finsum' hgh hsum hle) (le_of_eq ?_)
      exact finsum_add_distrib hg hh)
    (by
      intro c g
      have hfun : (fun v => |((c • g : DeningerTestSpace (DeningerPlace K)) :
            DeningerPlace K → ℝ) v|)
          = fun v => ‖c‖ * |(g : DeningerPlace K → ℝ) v| := by
        funext v
        show |c * (g : DeningerPlace K → ℝ) v| = ‖c‖ * |(g : DeningerPlace K → ℝ) v|
        rw [abs_mul, Real.norm_eq_abs]
      rw [hfun, ← mul_finsum])

theorem deningerL1Seminorm_apply (g : DeningerTestSpace (DeningerPlace K)) :
    deningerL1Seminorm K g = ∑ᶠ v, |(g : DeningerPlace K → ℝ) v| := rfl

/-- **On a logarithmic Kummer function the `ℓ¹` seminorm is the sum of the absolute values**, which
by the height identity is twice the Weil height. -/
theorem deningerL1Seminorm_kummer {α : K} (hα : α ≠ 0) :
    deningerL1Seminorm K (deningerKummerTest K hα)
      = ∑ᶠ v, |deningerKummerFun K α v| := rfl

/-- **The test space of places maps densely into its `ℓ¹` completion**, the Banach step of the
scale. -/
theorem deningerL1_denseRange :
    DenseRange (deningerSeminormMkC (deningerL1Seminorm K)) :=
  deningerSeminormMkC_denseRange _

end L1Norm

end RHTower
