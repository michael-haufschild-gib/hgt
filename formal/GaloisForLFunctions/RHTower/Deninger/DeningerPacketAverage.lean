import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Topology.ContinuousMap.Compact

/-!
# The packet average and its strict splitting

Averaging a continuous function over a compact packet carrying a probability measure is a linear
functional that restricts to the identity on constants.  The induced projection therefore splits
the test space as the constants plus the functions of vanishing average, and the average is
bounded by both the mean modulus and the quadratic mean.

The packet itself is a product of a compact profinite factor with a circle, so it is compact
Hausdorff, and any continuous bijection out of it is a homeomorphism — which is what identifies the
packet with the product model.

* `deningerPacketAv` : the average.
* `deningerPacketAv_incl` : it restricts to the identity on constants.
* `deningerPacket_isCompl` : the strict splitting into constants and vanishing average.
* `deningerPacketAv_abs_le`, `deningerPacketAv_sq_le` : the two bounds.
* `deningerPacket_homeomorph` : a continuous bijection out of the packet is a homeomorphism.
-/

namespace RHTower

open MeasureTheory

section PacketAverage

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
  (μ : Measure X) [IsProbabilityMeasure μ]

/-- A continuous function on a compact packet is integrable. -/
theorem deningerPacketIntegrable (f : C(X, ℝ)) : Integrable (fun x => f x) μ :=
  f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- **The packet average** of a continuous function. -/
noncomputable def deningerPacketAv : C(X, ℝ) →ₗ[ℝ] ℝ where
  toFun f := ∫ x, f x ∂μ
  map_add' f g := integral_add (deningerPacketIntegrable μ f) (deningerPacketIntegrable μ g)
  map_smul' c f := by
    show (∫ x, c * f x ∂μ) = c * ∫ x, f x ∂μ
    rw [integral_const_mul]

@[simp] theorem deningerPacketAv_apply (f : C(X, ℝ)) :
    deningerPacketAv μ f = ∫ x, f x ∂μ := rfl

/-- The inclusion of scalars as constant functions on the packet. -/
def deningerPacketIncl : ℝ →ₗ[ℝ] C(X, ℝ) where
  toFun c := ContinuousMap.const X c
  map_add' c c' := by
    ext x
    rfl
  map_smul' r c := by
    ext x
    rfl

omit [CompactSpace X] [MeasurableSpace X] [BorelSpace X] in
@[simp] theorem deningerPacketIncl_apply (c : ℝ) (x : X) :
    deningerPacketIncl (X := X) c x = c := rfl

/-- **The average restricts to the identity on constants**, because the packet has total mass
one. -/
@[simp] theorem deningerPacketAv_incl (c : ℝ) :
    deningerPacketAv μ (deningerPacketIncl c) = c := by
  show (∫ _x : X, c ∂μ) = c
  rw [integral_const, probReal_univ, one_smul]

/-- The packet projection onto the constants. -/
noncomputable def deningerPacketProj : C(X, ℝ) →ₗ[ℝ] C(X, ℝ) :=
  (deningerPacketIncl (X := X)).comp (deningerPacketAv μ)

/-- **The packet projection is idempotent.** -/
theorem deningerPacketProj_idem (f : C(X, ℝ)) :
    deningerPacketProj μ (deningerPacketProj μ f) = deningerPacketProj μ f := by
  show deningerPacketIncl (deningerPacketAv μ (deningerPacketIncl (deningerPacketAv μ f)))
    = deningerPacketIncl (deningerPacketAv μ f)
  rw [deningerPacketAv_incl]

/-- **The strict splitting of the packet test space**: every function is uniquely a constant plus a
function of vanishing average. -/
theorem deningerPacket_isCompl :
    IsCompl (LinearMap.range (deningerPacketIncl (X := X)))
      (LinearMap.ker (deningerPacketAv μ)) := by
  constructor
  · rw [Submodule.disjoint_def]
    rintro f ⟨c, rfl⟩ hker
    have hc : c = 0 := by
      have := hker
      rw [LinearMap.mem_ker, deningerPacketAv_incl] at this
      exact this
    rw [hc, map_zero]
  · rw [codisjoint_iff, eq_top_iff]
    intro f _
    have hsplit : f = deningerPacketIncl (deningerPacketAv μ f)
        + (f - deningerPacketIncl (deningerPacketAv μ f)) := by
      rw [add_sub_cancel]
    rw [hsplit]
    refine Submodule.add_mem_sup ⟨deningerPacketAv μ f, rfl⟩ ?_
    rw [LinearMap.mem_ker, map_sub, deningerPacketAv_incl, sub_self]

/-- **The average is bounded by the mean modulus.** -/
theorem deningerPacketAv_abs_le (f : C(X, ℝ)) :
    |deningerPacketAv μ f| ≤ ∫ x, |f x| ∂μ := by
  show |∫ x, f x ∂μ| ≤ ∫ x, |f x| ∂μ
  have h := norm_integral_le_integral_norm (μ := μ) fun x => f x
  simpa [Real.norm_eq_abs] using h

/-- **The average is bounded by the quadratic mean.**  This is the variance inequality: the mean of
the square of the deviation is nonnegative. -/
theorem deningerPacketAv_sq_le (f : C(X, ℝ)) :
    (deningerPacketAv μ f) ^ (2 : ℕ) ≤ ∫ x, (f x) ^ (2 : ℕ) ∂μ := by
  set c : ℝ := ∫ x, f x ∂μ with hc
  have hf := deningerPacketIntegrable μ f
  have hsq : Integrable (fun x => (f x) ^ (2 : ℕ)) μ :=
    (f.continuous.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hexp : ∀ x : X, (f x - c) ^ (2 : ℕ) = (f x) ^ (2 : ℕ) - 2 * c * f x + c ^ (2 : ℕ) := by
    intro x
    ring
  have hint : (∫ x, (f x - c) ^ (2 : ℕ) ∂μ) = (∫ x, (f x) ^ (2 : ℕ) ∂μ) - c ^ (2 : ℕ) := by
    have h1 : (∫ x, (f x ^ (2 : ℕ) - 2 * c * f x + c ^ (2 : ℕ)) ∂μ)
        = (∫ x, (f x ^ (2 : ℕ) - 2 * c * f x) ∂μ) + ∫ _x : X, c ^ (2 : ℕ) ∂μ :=
      integral_add (hsq.sub (hf.const_mul (2 * c))) (integrable_const _)
    have h2 : (∫ x, (f x ^ (2 : ℕ) - 2 * c * f x) ∂μ)
        = (∫ x, f x ^ (2 : ℕ) ∂μ) - ∫ x, 2 * c * f x ∂μ :=
      integral_sub hsq (hf.const_mul (2 * c))
    have h3 : (∫ x, 2 * c * f x ∂μ) = 2 * c * c := by
      rw [integral_const_mul, ← hc]
    have h4 : (∫ _x : X, c ^ (2 : ℕ) ∂μ) = c ^ (2 : ℕ) := by
      rw [integral_const, probReal_univ, one_smul]
    rw [integral_congr_ae (Filter.Eventually.of_forall hexp), h1, h2, h3, h4]
    ring
  have hnonneg : 0 ≤ ∫ x, (f x - c) ^ (2 : ℕ) ∂μ :=
    integral_nonneg fun x => sq_nonneg _
  rw [hint] at hnonneg
  show c ^ (2 : ℕ) ≤ ∫ x, (f x) ^ (2 : ℕ) ∂μ
  linarith

end PacketAverage

section PacketTopology

/-- **A continuous bijection out of a compact packet is a homeomorphism.**  The packet is a product
of a compact profinite factor with a circle, hence compact, and the target is Hausdorff. -/
noncomputable def deningerPacketHomeomorph {B S Y : Type*} [TopologicalSpace B] [CompactSpace B]
    [TopologicalSpace S] [CompactSpace S] [TopologicalSpace Y] [T2Space Y]
    (φ : B × S → Y) (hφ : Continuous φ) (hbij : Function.Bijective φ) : (B × S) ≃ₜ Y :=
  Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective φ hbij) hφ

end PacketTopology

end RHTower
