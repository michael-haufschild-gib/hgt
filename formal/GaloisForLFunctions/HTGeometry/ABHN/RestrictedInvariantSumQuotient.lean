import GaloisForLFunctions.HTGeometry.ABHN.RestrictedInvariantSum

/-!
# Quotient by the global invariant-sum relation

The raw finite-support target of the ABHN invariant sequence has one global relation: the sum of
the local values.  This file proves that relation has cokernel `ℚ/ℤ` for the project’s actual
number-field and rational-function-field place types.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

universe u

/-- A local invariant placed at one index has that value as its finite global sum. -/
theorem finsuppRatModIntSumAddHom_apply_single (ι : Type u) (i : ι) (q : RatModInt) :
    finsuppRatModIntSumAddHom ι (Finsupp.single i q) = q := by
  change (Finsupp.single i q).sum (fun _ q ↦ q) = q
  exact Finsupp.sum_single_index rfl

/-- The finite-support invariant-sum map for number-field places is surjective. -/
theorem numberFieldFinsuppRatModIntSum_surjective
    (K : Type u) [Field K] [NumberField K] :
    Function.Surjective (finsuppRatModIntSumAddHom (NumberFieldPlace K)) := by
  intro q
  refine ⟨Finsupp.single (witnessPlace K) q, ?_⟩
  exact finsuppRatModIntSumAddHom_apply_single _ _ _

/-- The finite-support invariant-sum map for rational-function-field places is surjective. -/
theorem rationalFunctionFinsuppRatModIntSum_surjective
    (F : Type u) [Field F] [Finite F] :
    Function.Surjective (finsuppRatModIntSumAddHom (RationalFunctionPlace F)) := by
  intro q
  refine ⟨Finsupp.single RationalFunctionPlace.infinite q, ?_⟩
  exact finsuppRatModIntSumAddHom_apply_single _ _ _

/-- Modulo finite-support local invariant profiles of total sum zero, the number-field target is
canonically `ℚ/ℤ`. -/
noncomputable def numberFieldFinsuppRatModIntSumQuotientEquiv
    (K : Type u) [Field K] [NumberField K] :
    ((NumberFieldPlace K →₀ RatModInt) ⧸
      (finsuppRatModIntSumAddHom (NumberFieldPlace K)).ker) ≃+ RatModInt :=
  QuotientAddGroup.quotientKerEquivOfSurjective
    (finsuppRatModIntSumAddHom (NumberFieldPlace K))
    (numberFieldFinsuppRatModIntSum_surjective K)

/-- Modulo finite-support local invariant profiles of total sum zero, the rational-function-field
target is canonically `ℚ/ℤ`. -/
noncomputable def rationalFunctionFinsuppRatModIntSumQuotientEquiv
    (F : Type u) [Field F] [Finite F] :
    ((RationalFunctionPlace F →₀ RatModInt) ⧸
      (finsuppRatModIntSumAddHom (RationalFunctionPlace F)).ker) ≃+ RatModInt :=
  QuotientAddGroup.quotientKerEquivOfSurjective
    (finsuppRatModIntSumAddHom (RationalFunctionPlace F))
    (rationalFunctionFinsuppRatModIntSum_surjective F)

/-- The number-field quotient equivalence evaluates a profile by its finite invariant sum. -/
theorem numberFieldFinsuppRatModIntSumQuotientEquiv_mk
    (K : Type u) [Field K] [NumberField K]
    (f : NumberFieldPlace K →₀ RatModInt) :
    numberFieldFinsuppRatModIntSumQuotientEquiv K (QuotientAddGroup.mk f) =
      finsuppRatModIntSumAddHom (NumberFieldPlace K) f := rfl

/-- The rational-function-field quotient equivalence evaluates a profile by its finite invariant
sum. -/
theorem rationalFunctionFinsuppRatModIntSumQuotientEquiv_mk
    (F : Type u) [Field F] [Finite F]
    (f : RationalFunctionPlace F →₀ RatModInt) :
    rationalFunctionFinsuppRatModIntSumQuotientEquiv F (QuotientAddGroup.mk f) =
      finsuppRatModIntSumAddHom (RationalFunctionPlace F) f := rfl

/-- The finite-support invariant sum is exact after including its zero-sum profiles. -/
theorem finsuppRatModIntSum_zeroSum_exact (ι : Type u) :
    Function.Exact (finsuppRatModIntSumAddHom ι).ker.subtype
      (finsuppRatModIntSumAddHom ι) := by
  intro x
  constructor
  · intro hx
    exact ⟨⟨x, hx⟩, rfl⟩
  · rintro ⟨y, hy⟩
    rw [← hy]
    exact y.property

/-- The raw number-field finite-support invariant target satisfies the formal ABHN exactness
contract.  Its left term is the zero-sum profile group, not the global Brauer group. -/
theorem numberFieldFinsuppRatModIntSum_targetExactness
    (K : Type u) [Field K] [NumberField K] :
    ABHNExactness
      (finsuppRatModIntSumAddHom (NumberFieldPlace K)).ker
      (NumberFieldPlace K →₀ RatModInt)
      (finsuppRatModIntSumAddHom (NumberFieldPlace K)).ker.subtype
      (finsuppRatModIntSumAddHom (NumberFieldPlace K)) :=
  { globalToLocal_injective :=
      (finsuppRatModIntSumAddHom (NumberFieldPlace K)).ker.subtype_injective
    exact_globalToLocal_localInvariant := finsuppRatModIntSum_zeroSum_exact _
    localInvariant_surjective := numberFieldFinsuppRatModIntSum_surjective K }

/-- The raw rational-function-field finite-support invariant target satisfies the formal ABHN
exactness contract.  Its left term is the zero-sum profile group, not the global Brauer group. -/
theorem rationalFunctionFinsuppRatModIntSum_targetExactness
    (F : Type u) [Field F] [Finite F] :
    ABHNExactness
      (finsuppRatModIntSumAddHom (RationalFunctionPlace F)).ker
      (RationalFunctionPlace F →₀ RatModInt)
      (finsuppRatModIntSumAddHom (RationalFunctionPlace F)).ker.subtype
      (finsuppRatModIntSumAddHom (RationalFunctionPlace F)) :=
  { globalToLocal_injective :=
      (finsuppRatModIntSumAddHom (RationalFunctionPlace F)).ker.subtype_injective
    exact_globalToLocal_localInvariant := finsuppRatModIntSum_zeroSum_exact _
    localInvariant_surjective := rationalFunctionFinsuppRatModIntSum_surjective F }

end GaloisForLFunctions.HTGeometry.ABHN
