import GaloisForLFunctions.RHTower.DeningerRealSmul

/-!
# The extended real action is a module structure

Each module axiom for the extended action is a density argument against the corresponding rational
identity: both sides are continuous in the real scalars and agree when those scalars are rational.
Additivity and associativity of the scalars need two such arguments in succession, one variable at
a time.

* `deningerRealSmul_one`, `deningerRealSmul_zero` : the unit and zero scalars.
* `deningerRealSmul_add_right`, `deningerRealSmul_add_left`, `deningerRealSmul_mul` : the module
  laws.
* `deningerRealModule` : the bundled `ℝ`-module structure.
-/

namespace RHTower

section RealModule

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℚ E] [CompleteSpace E]

omit [CompleteSpace E] in
@[simp] theorem deningerRealSmul_one (x : E) : deningerRealSmul (1 : ℝ) x = x := by
  have h := deningerRealSmul_ratCast (1 : ℚ) x
  rw [Rat.cast_one, one_smul] at h
  exact h

omit [CompleteSpace E] in
@[simp] theorem deningerRealSmul_zero (x : E) : deningerRealSmul (0 : ℝ) x = 0 := by
  have h := deningerRealSmul_ratCast (0 : ℚ) x
  rw [Rat.cast_zero, zero_smul] at h
  exact h

@[simp] theorem deningerRealSmul_zero_vec (r : ℝ) : deningerRealSmul r (0 : E) = 0 := by
  have hcont₁ : Continuous fun r : ℝ => deningerRealSmul r (0 : E) :=
    deningerRealSmul_continuous 0
  have hcont₂ : Continuous fun _ : ℝ => (0 : E) := continuous_const
  refine congr_fun (Rat.isDenseEmbedding_coe_real.dense.equalizer hcont₁ hcont₂ ?_) r
  funext q
  simp only [Function.comp_apply]
  rw [deningerRealSmul_ratCast, smul_zero]

/-- **The action distributes over vector addition.** -/
theorem deningerRealSmul_add_right (r : ℝ) (x y : E) :
    deningerRealSmul r (x + y) = deningerRealSmul r x + deningerRealSmul r y := by
  have hcont₁ : Continuous fun r : ℝ => deningerRealSmul r (x + y) :=
    deningerRealSmul_continuous _
  have hcont₂ : Continuous fun r : ℝ => deningerRealSmul r x + deningerRealSmul r y :=
    (deningerRealSmul_continuous x).add (deningerRealSmul_continuous y)
  refine congr_fun (Rat.isDenseEmbedding_coe_real.dense.equalizer hcont₁ hcont₂ ?_) r
  funext q
  simp only [Function.comp_apply]
  rw [deningerRealSmul_ratCast, deningerRealSmul_ratCast, deningerRealSmul_ratCast, smul_add]

/-- Additivity of the scalar, with the first scalar rational. -/
private theorem deningerRealSmul_ratAdd (q : ℚ) (s : ℝ) (x : E) :
    deningerRealSmul ((q : ℝ) + s) x = q • x + deningerRealSmul s x := by
  have hcont₁ : Continuous fun s : ℝ => deningerRealSmul ((q : ℝ) + s) x :=
    (deningerRealSmul_continuous x).comp (continuous_const.add continuous_id)
  have hcont₂ : Continuous fun s : ℝ => q • x + deningerRealSmul s x :=
    continuous_const.add (deningerRealSmul_continuous x)
  refine congr_fun (Rat.isDenseEmbedding_coe_real.dense.equalizer hcont₁ hcont₂ ?_) s
  funext q'
  simp only [Function.comp_apply]
  rw [← Rat.cast_add, deningerRealSmul_ratCast, deningerRealSmul_ratCast, add_smul]

/-- **The action is additive in the scalar.** -/
theorem deningerRealSmul_add_left (r s : ℝ) (x : E) :
    deningerRealSmul (r + s) x = deningerRealSmul r x + deningerRealSmul s x := by
  have hcont₁ : Continuous fun r : ℝ => deningerRealSmul (r + s) x :=
    (deningerRealSmul_continuous x).comp (continuous_id.add continuous_const)
  have hcont₂ : Continuous fun r : ℝ => deningerRealSmul r x + deningerRealSmul s x :=
    (deningerRealSmul_continuous x).add continuous_const
  refine congr_fun (Rat.isDenseEmbedding_coe_real.dense.equalizer hcont₁ hcont₂ ?_) r
  funext q
  simp only [Function.comp_apply]
  rw [deningerRealSmul_ratAdd, deningerRealSmul_ratCast]

/-- Associativity of the scalars, with the first scalar rational. -/
private theorem deningerRealSmul_ratMul (q : ℚ) (s : ℝ) (x : E) :
    deningerRealSmul ((q : ℝ) * s) x = q • deningerRealSmul s x := by
  have hcont₁ : Continuous fun s : ℝ => deningerRealSmul ((q : ℝ) * s) x :=
    (deningerRealSmul_continuous x).comp (continuous_const.mul continuous_id)
  have hcont₂ : Continuous fun s : ℝ => q • deningerRealSmul s x :=
    (continuous_const_smul q).comp (deningerRealSmul_continuous x)
  refine congr_fun (Rat.isDenseEmbedding_coe_real.dense.equalizer hcont₁ hcont₂ ?_) s
  funext q'
  simp only [Function.comp_apply]
  rw [← Rat.cast_mul, deningerRealSmul_ratCast, deningerRealSmul_ratCast, mul_smul]

/-- **The action is associative in the scalars.** -/
theorem deningerRealSmul_mul (r s : ℝ) (x : E) :
    deningerRealSmul (r * s) x = deningerRealSmul r (deningerRealSmul s x) := by
  have hcont₁ : Continuous fun r : ℝ => deningerRealSmul (r * s) x :=
    (deningerRealSmul_continuous x).comp (continuous_id.mul continuous_const)
  have hcont₂ : Continuous fun r : ℝ => deningerRealSmul r (deningerRealSmul s x) :=
    deningerRealSmul_continuous _
  refine congr_fun (Rat.isDenseEmbedding_coe_real.dense.equalizer hcont₁ hcont₂ ?_) r
  funext q
  simp only [Function.comp_apply]
  rw [deningerRealSmul_ratMul, deningerRealSmul_ratCast]

/-- **The bundled `ℝ`-module structure** on a complete normed `ℚ`-space. -/
@[reducible] noncomputable def deningerRealModule : Module ℝ E where
  smul := deningerRealSmul
  one_smul := deningerRealSmul_one
  mul_smul := deningerRealSmul_mul
  smul_zero := deningerRealSmul_zero_vec
  smul_add := deningerRealSmul_add_right
  add_smul := deningerRealSmul_add_left
  zero_smul := deningerRealSmul_zero

end RealModule

end RHTower
