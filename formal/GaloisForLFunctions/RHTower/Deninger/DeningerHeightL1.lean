import GaloisForLFunctions.RHTower.Deninger.DeningerPlaceIntegral

/-!
# The Weil height is half the `ℓ¹` norm of the logarithmic Kummer function

The positive part and the absolute value of a real number are related by `2 max(x,0) = x + |x|`.
Summing over the places and using the product formula, which makes the sum of the logarithmic
Kummer function vanish, the sum of its positive parts — the Weil height — is half the sum of its
absolute values.

That is the identity which makes the height an `ℓ¹` norm on the space of logarithmic Kummer
functions, the starting point of the Allcock–Vaaler picture of the height.

* `deningerHeightTest`, `deningerAbsTest` : the positive part and the absolute value of a Kummer
  function, as test functions.
* `deningerHeight_eq_half_l1` : **the height is half the `ℓ¹` norm.**
-/

namespace RHTower

open NumberField

section Height

variable (K : Type*) [Field K] [NumberField K]

theorem deningerKummer_pos_mem {α : K} (hα : α ≠ 0) :
    (fun v => max (deningerKummerFun K α v) 0) ∈ DeningerTestSpace (DeningerPlace K) := by
  refine ⟨IsLocallyConstant.of_discrete _, ?_⟩
  refine Set.Finite.isCompact (Set.Finite.subset (deningerKummerFun_support_finite K hα) ?_)
  intro v hv hzero
  apply hv
  show max (deningerKummerFun K α v) 0 = 0
  rw [hzero]
  simp

theorem deningerKummer_abs_mem {α : K} (hα : α ≠ 0) :
    (fun v => |deningerKummerFun K α v|) ∈ DeningerTestSpace (DeningerPlace K) := by
  refine ⟨IsLocallyConstant.of_discrete _, ?_⟩
  refine Set.Finite.isCompact (Set.Finite.subset (deningerKummerFun_support_finite K hα) ?_)
  intro v hv hzero
  apply hv
  show |deningerKummerFun K α v| = 0
  rw [hzero, abs_zero]

/-- The positive part of a logarithmic Kummer function, as a test function. -/
noncomputable def deningerHeightTest {α : K} (hα : α ≠ 0) :
    DeningerTestSpace (DeningerPlace K) :=
  ⟨fun v => max (deningerKummerFun K α v) 0, deningerKummer_pos_mem K hα⟩

/-- The absolute value of a logarithmic Kummer function, as a test function. -/
noncomputable def deningerAbsTest {α : K} (hα : α ≠ 0) :
    DeningerTestSpace (DeningerPlace K) :=
  ⟨fun v => |deningerKummerFun K α v|, deningerKummer_abs_mem K hα⟩

/-- **The Weil height is half the `ℓ¹` norm of the logarithmic Kummer function.**  Twice the
positive part is the function plus its absolute value, and the function sums to zero by the
product formula. -/
theorem deningerHeight_eq_half_l1 {α : K} (hα : α ≠ 0) :
    deningerPlaceSum K (deningerHeightTest K hα)
      = (1 / 2) * deningerPlaceSum K (deningerAbsTest K hα) := by
  have hpoint : (2 : ℝ) • deningerHeightTest K hα
      = deningerKummerTest K hα + deningerAbsTest K hα := by
    refine Subtype.ext (funext fun v => ?_)
    show (2 : ℝ) * max (deningerKummerFun K α v) 0
      = deningerKummerFun K α v + |deningerKummerFun K α v|
    rcases le_total (0 : ℝ) (deningerKummerFun K α v) with h | h
    · rw [max_eq_left h, abs_of_nonneg h]
      ring
    · rw [max_eq_right h, abs_of_nonpos h]
      ring
  have hmap := congrArg (deningerPlaceSum K) hpoint
  rw [map_smul, map_add, deningerKummer_sum_eq_zero K hα, zero_add] at hmap
  show deningerPlaceSum K (deningerHeightTest K hα) = _
  rw [← hmap]
  show _ = 1 / 2 * ((2 : ℝ) • deningerPlaceSum K (deningerHeightTest K hα))
  rw [smul_eq_mul]
  ring

end Height

end RHTower
