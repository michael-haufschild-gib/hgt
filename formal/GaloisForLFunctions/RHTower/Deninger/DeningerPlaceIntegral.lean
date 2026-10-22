import GaloisForLFunctions.RHTower.Deninger.DeningerPlaceSpace

/-!
# The sum over the places, and the product formula

On a discrete space the integral against the counting measure is the sum over the support, which
for a test function on the space of places splits into the finite sum over the infinite places and
the sum over the finitely many finite places where the function does not vanish.

The product formula says that the product of the absolute values of a nonzero element over all
places is one; in logarithmic form it says that the sum of a logarithmic Kummer function over all
places is zero.  So the Kummer span lies in the kernel of the sum.

* `deningerPlaceSum` : the sum of a test function over the places.
* `deningerKummer_sum_eq_zero` : **the product formula in logarithmic form.**
* `deningerKummerSpan_le_ker` : **the Kummer span lies in the kernel of the sum.**
-/

namespace RHTower

open NumberField

section PlaceSum

variable (K : Type*) [Field K] [NumberField K]

theorem deningerPlaceTest_finite_support (g : DeningerTestSpace (DeningerPlace K)) :
    Function.HasFiniteSupport fun w : FinitePlace K =>
      (g : DeningerPlace K → ℝ) (Sum.inr w) := by
  have hfin : (Function.support ((g : DeningerPlace K → ℝ))).Finite := by
    have hcomp := g.2.2
    exact hcomp.finite_of_discrete
  have hsub : (Function.support fun w : FinitePlace K => (g : DeningerPlace K → ℝ) (Sum.inr w))
      = Sum.inr ⁻¹' Function.support ((g : DeningerPlace K → ℝ)) := rfl
  rw [Function.HasFiniteSupport, hsub]
  exact hfin.preimage Sum.inr_injective.injOn

/-- **The sum of a test function over the places.** -/
noncomputable def deningerPlaceSum :
    DeningerTestSpace (DeningerPlace K) →ₗ[ℝ] ℝ where
  toFun g := (∑ w : InfinitePlace K, (g : DeningerPlace K → ℝ) (Sum.inl w))
    + ∑ᶠ w : FinitePlace K, (g : DeningerPlace K → ℝ) (Sum.inr w)
  map_add' g h := by
    have hg := deningerPlaceTest_finite_support K g
    have hh := deningerPlaceTest_finite_support K h
    simp only [Submodule.coe_add, Pi.add_apply]
    rw [Finset.sum_add_distrib, finsum_add_distrib hg hh]
    ring
  map_smul' c g := by
    simp only [SetLike.val_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [← Finset.mul_sum, ← mul_finsum]
    ring

theorem deningerPlaceSum_apply (g : DeningerTestSpace (DeningerPlace K)) :
    deningerPlaceSum K g = (∑ w : InfinitePlace K, (g : DeningerPlace K → ℝ) (Sum.inl w))
      + ∑ᶠ w : FinitePlace K, (g : DeningerPlace K → ℝ) (Sum.inr w) := rfl

/-- **The product formula in logarithmic form**: the sum of a logarithmic Kummer function over all
places vanishes. -/
theorem deningerKummer_sum_eq_zero {α : K} (hα : α ≠ 0) :
    deningerPlaceSum K (deningerKummerTest K hα) = 0 := by
  classical
  have hfin := FinitePlace.hasFiniteMulSupport (K := K) hα
  set s : Finset (FinitePlace K) := hfin.toFinset with hs
  have hposInf : ∀ w : InfinitePlace K, 0 < w α := fun w => InfinitePlace.pos_iff.mpr hα
  have hposFin : ∀ w : FinitePlace K, 0 < w α := fun w => FinitePlace.pos_iff.mpr hα
  have hprod := NumberField.prod_abs_eq_one (K := K) hα
  have hfinprod : ∏ᶠ w : FinitePlace K, w α = ∏ w ∈ s, w α :=
    finprod_eq_prod_of_mulSupport_toFinset_subset _ hfin (by rw [hs])
  have hsumFin : ∑ᶠ w : FinitePlace K, Real.log (w α) = ∑ w ∈ s, Real.log (w α) := by
    refine finsum_eq_sum_of_support_subset _ ?_
    intro w hw
    have hne : w α ≠ 1 := by
      intro hone
      apply hw
      show Real.log (w α) = 0
      rw [show w α = 1 from hone, Real.log_one]
    rw [hs, Set.Finite.coe_toFinset]
    exact hne
  have hlogFin : Real.log (∏ w ∈ s, w α) = ∑ w ∈ s, Real.log (w α) :=
    Real.log_prod fun w _ => (hposFin w).ne'
  have hlogInf : Real.log (∏ w : InfinitePlace K, w α ^ w.mult)
      = ∑ w : InfinitePlace K, (w.mult : ℝ) * Real.log (w α) := by
    rw [Real.log_prod fun w _ => (pow_pos (hposInf w) w.mult).ne']
    exact Finset.sum_congr rfl fun w _ => Real.log_pow _ _
  have hprodInf_ne : (∏ w : InfinitePlace K, w α ^ w.mult) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun w _ => (pow_pos (hposInf w) w.mult).ne'
  have hprodFin_ne : (∏ w ∈ s, w α) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun w _ => (hposFin w).ne'
  have hlog : Real.log ((∏ w : InfinitePlace K, w α ^ w.mult) * ∏ w ∈ s, w α) = 0 := by
    rw [← hfinprod, hprod, Real.log_one]
  rw [Real.log_mul hprodInf_ne hprodFin_ne, hlogInf, hlogFin] at hlog
  rw [deningerPlaceSum_apply]
  show (∑ w : InfinitePlace K, deningerKummerFun K α (Sum.inl w : DeningerPlace K))
    + ∑ᶠ w : FinitePlace K, deningerKummerFun K α (Sum.inr w : DeningerPlace K) = 0
  simp only [deningerKummerFun_inl, deningerKummerFun_inr]
  rw [hsumFin]
  exact hlog

/-- **The Kummer span lies in the kernel of the sum over the places.** -/
theorem deningerKummerSpan_le_ker :
    DeningerKummerSpan K ≤ LinearMap.ker (deningerPlaceSum K) := by
  refine Submodule.span_le.mpr ?_
  rintro g ⟨α, hα, rfl⟩
  exact deningerKummer_sum_eq_zero K hα

end PlaceSum

end RHTower
