import GaloisForLFunctions.RHTower.DeningerL1Norm
import GaloisForLFunctions.RHTower.DeningerHeightBaseChange

/-!
# The test space of places computes the Weil height

The place sum of the positive part of a logarithmic Kummer function is the logarithmic height, and
the `ℓ¹` seminorm of the Kummer function itself is twice that height.  So the Banach step of the
Kummer scale — the completion of the test space in the `ℓ¹` seminorm — is the completion in the
height norm, and the Kummer map is injective on the group of nonzero elements modulo roots of
unity.

Base change transports through the bridge: enlarging the field multiplies the seminorm by the
degree of the extension, so the seminorm divided by the absolute degree is the same in every field
containing the element.  That invariance is what lets the place models of a tower of number fields
glue.

* `deningerPlaceSum_eq_finsum` : the place sum of a test function is the sum of its values.
* `deningerHeightSum_eq_logHeight` : **the place sum of the positive part is the height.**
* `deningerL1Seminorm_eq_two_mul_logHeight` : **the `ℓ¹` seminorm is twice the height.**
* `deningerL1Seminorm_eq_zero_iff` : **it vanishes exactly on the roots of unity.**
* `deningerL1Seminorm_baseChange`, `deningerNormalizedL1Seminorm_baseChange` : the degree scaling
  and its normalized invariant form.
-/

namespace RHTower

open NumberField Module

section FinsumSplit

/-- A sum over a disjoint union splits, provided each half has finite support. -/
theorem deningerFinsum_sum_split {α β : Type*} (f : α ⊕ β → ℝ)
    (hl : (Function.support fun a => f (Sum.inl a)).Finite)
    (hr : (Function.support fun b => f (Sum.inr b)).Finite) :
    ∑ᶠ v, f v = (∑ᶠ a, f (Sum.inl a)) + ∑ᶠ b, f (Sum.inr b) := by
  have hd : Disjoint (Set.range (Sum.inl : α → α ⊕ β)) (Set.range (Sum.inr : β → α ⊕ β)) := by
    rw [Set.disjoint_left]
    rintro _ ⟨a, rfl⟩ ⟨b, hb⟩
    exact absurd hb (by simp)
  have huniv : (Set.univ : Set (α ⊕ β)) = Set.range Sum.inl ∪ Set.range Sum.inr := by
    ext v
    cases v <;> simp
  have h1 : (Set.range (Sum.inl : α → α ⊕ β) ∩ Function.support f).Finite := by
    refine Set.Finite.subset (hl.image Sum.inl) ?_
    rintro _ ⟨⟨a, rfl⟩, hs⟩
    exact ⟨a, hs, rfl⟩
  have h2 : (Set.range (Sum.inr : β → α ⊕ β) ∩ Function.support f).Finite := by
    refine Set.Finite.subset (hr.image Sum.inr) ?_
    rintro _ ⟨⟨b, rfl⟩, hs⟩
    exact ⟨b, hs, rfl⟩
  rw [← finsum_mem_univ, huniv, finsum_mem_union' hd h1 h2,
    finsum_mem_range Sum.inl_injective, finsum_mem_range Sum.inr_injective]

end FinsumSplit

section Bridge

variable {K : Type*} [Field K] [NumberField K]

/-- **The sum over the places of a test function is the sum of its values**: the archimedean part
is a sum over a finite type and the non-archimedean part has finite support. -/
theorem deningerPlaceSum_eq_finsum (g : DeningerTestSpace (DeningerPlace K)) :
    deningerPlaceSum K g = ∑ᶠ v, (g : DeningerPlace K → ℝ) v := by
  have h : ∑ᶠ v : DeningerPlace K, (g : DeningerPlace K → ℝ) v
      = (∑ᶠ a : InfinitePlace K, (g : DeningerPlace K → ℝ) (Sum.inl a : DeningerPlace K))
        + ∑ᶠ b : FinitePlace K, (g : DeningerPlace K → ℝ) (Sum.inr b : DeningerPlace K) :=
    deningerFinsum_sum_split _ (Set.toFinite _) (deningerPlaceTest_finite_support K g)
  rw [deningerPlaceSum_apply, h]
  congr 1
  exact (finsum_eq_sum_of_fintype _).symm

/-- The positive part of a scaled logarithm is the scaled positive part. -/
theorem deningerMaxZero_mul (c t : ℝ) (hc : 0 ≤ c) :
    max (c * Real.log t) 0 = c * Real.posLog t := by
  have h : Real.posLog t = max 0 (Real.log t) := rfl
  rw [h, mul_max_of_nonneg _ _ hc, mul_zero, max_comm]

/-- **The place sum of the positive part of a logarithmic Kummer function is the logarithmic
height.** -/
theorem deningerHeightSum_eq_logHeight {α : K} (hα : α ≠ 0) :
    deningerPlaceSum K (deningerHeightTest K hα) = Height.logHeight₁ α := by
  rw [NumberField.logHeight₁_eq, deningerPlaceSum_apply]
  show (∑ w : InfinitePlace K, max (deningerKummerFun K α (Sum.inl w : DeningerPlace K)) 0)
      + ∑ᶠ w : FinitePlace K, max (deningerKummerFun K α (Sum.inr w : DeningerPlace K)) 0
    = (∑ w : InfinitePlace K, (w.mult : ℝ) * Real.posLog (w α))
      + ∑ᶠ w : FinitePlace K, Real.posLog (w α)
  simp only [deningerKummerFun_inl, deningerKummerFun_inr]
  refine congrArg₂ (· + ·) (Finset.sum_congr rfl fun w _ => ?_) (finsum_congr fun w => ?_)
  · exact deningerMaxZero_mul _ _ (Nat.cast_nonneg w.mult)
  · have h := deningerMaxZero_mul 1 (w α) zero_le_one
    rwa [one_mul, one_mul] at h

/-- **The `ℓ¹` seminorm of a logarithmic Kummer function is twice the logarithmic height.**  This
is the identity that makes the Banach step of the Kummer scale the completion in the height
norm. -/
theorem deningerL1Seminorm_eq_two_mul_logHeight {α : K} (hα : α ≠ 0) :
    deningerL1Seminorm K (deningerKummerTest K hα) = 2 * Height.logHeight₁ α := by
  have habs : deningerL1Seminorm K (deningerKummerTest K hα)
      = deningerPlaceSum K (deningerAbsTest K hα) := by
    rw [deningerPlaceSum_eq_finsum]
    rfl
  have hhalf := deningerHeight_eq_half_l1 K hα
  rw [deningerHeightSum_eq_logHeight hα] at hhalf
  rw [habs, hhalf]
  ring

/-- **The `ℓ¹` seminorm of a Kummer function vanishes exactly on the roots of unity**, so the
Kummer map is injective on the nonzero elements modulo torsion. -/
theorem deningerL1Seminorm_eq_zero_iff {α : K} (hα : α ≠ 0) :
    deningerL1Seminorm K (deningerKummerTest K hα) = 0 ↔ IsOfFinOrder α := by
  rw [deningerL1Seminorm_eq_two_mul_logHeight hα,
    ← deningerKummerL1Norm_eq_two_mul_logHeight hα]
  exact deningerKummerL1Norm_eq_zero_iff hα

end Bridge

section BridgeBaseChange

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

/-- **The `ℓ¹` seminorm of a Kummer function scales by the degree of the extension.** -/
theorem deningerL1Seminorm_baseChange {α : K} (hα : α ≠ 0) (hαL : algebraMap K L α ≠ 0) :
    deningerL1Seminorm L (deningerKummerTest L hαL)
      = (finrank K L : ℝ) * deningerL1Seminorm K (deningerKummerTest K hα) := by
  rw [deningerL1Seminorm_eq_two_mul_logHeight, deningerL1Seminorm_eq_two_mul_logHeight,
    deningerLogHeight_baseChange (L := L) α]
  ring

/-- **The place sum of the positive part scales by the degree of the extension.** -/
theorem deningerHeightSum_baseChange {α : K} (hα : α ≠ 0) (hαL : algebraMap K L α ≠ 0) :
    deningerPlaceSum L (deningerHeightTest L hαL)
      = (finrank K L : ℝ) * deningerPlaceSum K (deningerHeightTest K hα) := by
  rw [deningerHeightSum_eq_logHeight, deningerHeightSum_eq_logHeight,
    deningerLogHeight_baseChange (L := L) α]

/-- **The normalized Kummer norm is independent of the field of definition.**  Dividing by the
absolute degree cancels the base-change factor, so the Kummer functions of a tower of number
fields carry one and the same norm. -/
theorem deningerNormalizedL1Seminorm_baseChange {α : K} (hα : α ≠ 0)
    (hαL : algebraMap K L α ≠ 0) :
    deningerL1Seminorm L (deningerKummerTest L hαL) / (finrank ℚ L : ℝ)
      = deningerL1Seminorm K (deningerKummerTest K hα) / (finrank ℚ K : ℝ) := by
  rw [deningerL1Seminorm_eq_two_mul_logHeight, deningerL1Seminorm_eq_two_mul_logHeight,
    mul_div_assoc, mul_div_assoc, deningerNormalizedHeight_baseChange (L := L) α]

end BridgeBaseChange

end RHTower
