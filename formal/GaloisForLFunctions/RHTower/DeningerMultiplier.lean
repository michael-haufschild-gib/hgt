import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# Bounded diagonal multipliers on a square-summable coefficient space

A family of scalars of modulus at most one multiplies square-summable coefficients to
square-summable coefficients without increasing the norm, so it defines a contraction.  Composing
two multipliers multiplies the families, and the constant family one is the identity.

This is the operator form of a Fourier multiplier: on the coefficients of a Hilbert basis, the
Poisson semigroup of a diagonal generator is the multiplier family `e^{-r|μ_n|}`.

* `deningerMultiplier_memℓp` : a bounded family preserves square summability.
* `deningerMultiplier` : the contraction it defines.
* `deningerMultiplier_comp`, `deningerMultiplier_one` : the multiplier laws.
-/

namespace RHTower

open scoped ENNReal

section Multiplier

variable {ι : Type*}

/-- **A family of modulus at most one preserves square summability.** -/
theorem deningerMultiplier_memℓp {g : ι → ℂ} (hg : ∀ i, ‖g i‖ ≤ 1)
    (x : lp (fun _ : ι => ℂ) 2) : Memℓp (fun i => g i * (x : ι → ℂ) i) 2 := by
  have htwo : (0 : ℝ) < (2 : ℝ≥0∞).toReal := by norm_num
  refine memℓp_gen ?_
  refine Summable.of_nonneg_of_le (fun i => by positivity) (fun i => ?_) (x.2.summable htwo)
  rw [norm_mul, Real.mul_rpow (norm_nonneg _) (norm_nonneg _)]
  refine mul_le_of_le_one_left (by positivity) ?_
  exact Real.rpow_le_one (norm_nonneg _) (hg i) htwo.le

/-- The linear map defined by a bounded family. -/
noncomputable def deningerMultiplierMap {g : ι → ℂ} (hg : ∀ i, ‖g i‖ ≤ 1) :
    lp (fun _ : ι => ℂ) 2 →ₗ[ℂ] lp (fun _ : ι => ℂ) 2 where
  toFun x := ⟨fun i => g i * (x : ι → ℂ) i, deningerMultiplier_memℓp hg x⟩
  map_add' x y := by
    refine lp.ext ?_
    funext i
    show g i * ((x : ι → ℂ) i + (y : ι → ℂ) i) = g i * (x : ι → ℂ) i + g i * (y : ι → ℂ) i
    ring
  map_smul' c x := by
    refine lp.ext ?_
    funext i
    show g i * (c * (x : ι → ℂ) i) = c * (g i * (x : ι → ℂ) i)
    ring

@[simp] theorem deningerMultiplierMap_apply {g : ι → ℂ} (hg : ∀ i, ‖g i‖ ≤ 1)
    (x : lp (fun _ : ι => ℂ) 2) (i : ι) :
    (deningerMultiplierMap hg x : ι → ℂ) i = g i * (x : ι → ℂ) i := rfl

/-- **A bounded family does not increase the square norm.** -/
theorem deningerMultiplierMap_norm_le {g : ι → ℂ} (hg : ∀ i, ‖g i‖ ≤ 1)
    (x : lp (fun _ : ι => ℂ) 2) : ‖deningerMultiplierMap hg x‖ ≤ 1 * ‖x‖ := by
  have htwo : (0 : ℝ) < (2 : ℝ≥0∞).toReal := by norm_num
  rw [one_mul, lp.norm_eq_tsum_rpow htwo, lp.norm_eq_tsum_rpow htwo]
  refine Real.rpow_le_rpow (by positivity) ?_ (by positivity)
  refine tsum_le_tsum (fun i => ?_) ?_ (x.2.summable htwo)
  · rw [deningerMultiplierMap_apply, norm_mul, Real.mul_rpow (norm_nonneg _) (norm_nonneg _)]
    refine mul_le_of_le_one_left (by positivity) ?_
    exact Real.rpow_le_one (norm_nonneg _) (hg i) htwo.le
  · exact (deningerMultiplier_memℓp hg x).summable htwo

/-- **The contraction defined by a bounded family.** -/
noncomputable def deningerMultiplier {g : ι → ℂ} (hg : ∀ i, ‖g i‖ ≤ 1) :
    lp (fun _ : ι => ℂ) 2 →L[ℂ] lp (fun _ : ι => ℂ) 2 :=
  (deningerMultiplierMap hg).mkContinuous 1 (deningerMultiplierMap_norm_le hg)

@[simp] theorem deningerMultiplier_apply {g : ι → ℂ} (hg : ∀ i, ‖g i‖ ≤ 1)
    (x : lp (fun _ : ι => ℂ) 2) (i : ι) :
    (deningerMultiplier hg x : ι → ℂ) i = g i * (x : ι → ℂ) i := rfl

/-- **Composing two multipliers multiplies the families.** -/
theorem deningerMultiplier_comp {g h : ι → ℂ} (hg : ∀ i, ‖g i‖ ≤ 1) (hh : ∀ i, ‖h i‖ ≤ 1)
    (hgh : ∀ i, ‖g i * h i‖ ≤ 1) (x : lp (fun _ : ι => ℂ) 2) :
    deningerMultiplier hg (deningerMultiplier hh x) = deningerMultiplier hgh x := by
  refine lp.ext ?_
  funext i
  show g i * (h i * (x : ι → ℂ) i) = g i * h i * (x : ι → ℂ) i
  ring

/-- **The constant family one is the identity.** -/
theorem deningerMultiplier_one (x : lp (fun _ : ι => ℂ) 2) :
    deningerMultiplier (g := fun _ : ι => (1 : ℂ)) (fun _ => le_of_eq norm_one) x = x := by
  refine lp.ext ?_
  funext i
  show (1 : ℂ) * (x : ι → ℂ) i = (x : ι → ℂ) i
  ring

end Multiplier

end RHTower
