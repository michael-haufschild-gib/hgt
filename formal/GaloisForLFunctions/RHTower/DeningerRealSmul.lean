import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Topology.Instances.Rat
import Mathlib.Topology.UniformSpace.UniformEmbedding

/-!
# Extending rational scalars to real scalars on a complete normed space

On a complete normed `ℚ`-vector space the map `q ↦ q • x` is Lipschitz with constant `‖x‖`, so it
extends uniquely and continuously along the dense embedding `ℚ ↪ ℝ`.  The extension is the real
scalar multiplication: it restricts to the rational one, is continuous, and has the same norm law.

* `deningerRealSmul` : the extended action.
* `deningerRealSmul_ratCast` : it restricts to the rational action.
* `deningerRealSmul_continuous` : continuity in the scalar.
* `deningerRealSmul_norm` : `‖r • x‖ = |r| ‖x‖`.
-/

namespace RHTower

section RealSmul

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℚ E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- Rational scaling of a fixed vector is Lipschitz with constant its norm. -/
theorem deningerRatSmul_lipschitz (x : E) :
    LipschitzWith ‖x‖₊ (fun q : ℚ => q • x) := by
  refine LipschitzWith.of_dist_le_mul fun q q' => ?_
  have hnorm : ‖(q - q') • x‖ = ‖q - q'‖ * ‖x‖ := norm_smul _ _
  rw [dist_eq_norm, ← sub_smul, hnorm, Rat.dist_eq, ← Rat.norm_cast_real, Real.norm_eq_abs,
    coe_nnnorm]
  push_cast
  exact le_of_eq (by ring)

omit [CompleteSpace E] in
theorem deningerRatSmul_uniformContinuous (x : E) :
    UniformContinuous (fun q : ℚ => q • x) :=
  (deningerRatSmul_lipschitz x).uniformContinuous

/-- **The real scalar action**, obtained by extending the rational one along `ℚ ↪ ℝ`. -/
noncomputable def deningerRealSmul (r : ℝ) (x : E) : E :=
  (Rat.isDenseEmbedding_coe_real.isDenseInducing).extend (fun q : ℚ => q • x) r

omit [CompleteSpace E] in
/-- **The extension restricts to the rational action.** -/
@[simp] theorem deningerRealSmul_ratCast (q : ℚ) (x : E) :
    deningerRealSmul ((q : ℝ)) x = q • x :=
  uniformly_extend_of_ind Rat.isUniformEmbedding_coe_real.isUniformInducing
    Rat.denseRange_cast (deningerRatSmul_uniformContinuous x) q

/-- **The extension is continuous in the scalar.** -/
theorem deningerRealSmul_continuous (x : E) :
    Continuous (fun r : ℝ => deningerRealSmul r x) :=
  (uniformContinuous_uniformly_extend Rat.isUniformEmbedding_coe_real.isUniformInducing
    Rat.denseRange_cast (deningerRatSmul_uniformContinuous x)).continuous

/-- **The norm law of the extended action.** -/
theorem deningerRealSmul_norm (r : ℝ) (x : E) :
    ‖deningerRealSmul r x‖ = |r| * ‖x‖ := by
  have hcont₁ : Continuous fun r : ℝ => ‖deningerRealSmul r x‖ :=
    (deningerRealSmul_continuous x).norm
  have hcont₂ : Continuous fun r : ℝ => |r| * ‖x‖ :=
    (continuous_abs).mul continuous_const
  have hrat : (fun q : ℚ => ‖deningerRealSmul ((q : ℝ)) x‖)
      = fun q : ℚ => |((q : ℝ))| * ‖x‖ := by
    funext q
    rw [deningerRealSmul_ratCast, norm_smul, ← Rat.norm_cast_real, Real.norm_eq_abs]
  exact congr_fun (Rat.isDenseEmbedding_coe_real.dense.equalizer hcont₁ hcont₂ hrat) r

end RealSmul

end RHTower
