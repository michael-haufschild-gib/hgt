import GaloisForLFunctions.RHTower.Deninger.DeningerRestrictedPrimeGluing

/-!
# Hasse quotients for restricted prime sections

Restriction of the weighted prime-family sheaf to a smaller arithmetic open is surjective by
extension by zero.  Hence smaller-open sections are larger-open sections modulo the families
invisible on all retained primes.  This is a literal place-restriction quotient for the Deninger
arithmetic base.
-/

namespace RHTower

open TopologicalSpace

noncomputable section

universe u

variable {E : Nat.Primes → Type u} [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
variable (n1 n2 : ∀ p, Seminorm ℝ (E p)) (α β : Nat.Primes → NNReal)

/-- Linear restriction between weighted prime-section spaces. -/
noncomputable def deningerPrimeSectionsRestrictionLinearMap
    (U V : Opens (PrimeSpectrum ℤ)) :
    deningerPrimeSections n1 n2 α β U →ₗ[ℝ] deningerPrimeSections n1 n2 α β V where
  toFun f := ⟨deningerPrimeRestrict V f, deningerPrimeRestrict_mem f.2⟩
  map_add' f g := by
    apply Subtype.ext
    funext p
    classical
    by_cases hp : p ∈ deningerPrimeIndex V <;> simp [deningerPrimeRestrict, hp]
  map_smul' c f := by
    apply Subtype.ext
    funext p
    classical
    by_cases hp : p ∈ deningerPrimeIndex V <;> simp [deningerPrimeRestrict, hp]

/-- The linear restriction map is coordinate deletion. -/
@[simp] theorem deningerPrimeSectionsRestrictionLinearMap_apply
    (U V : Opens (PrimeSpectrum ℤ)) (f : deningerPrimeSections n1 n2 α β U) :
    (deningerPrimeSectionsRestrictionLinearMap n1 n2 α β U V f).1 = deningerPrimeRestrict V f :=
  rfl

/-- Restriction to a smaller arithmetic open is surjective. -/
theorem deningerPrimeSectionsRestrictionLinearMap_surjective
    {U V : Opens (PrimeSpectrum ℤ)} (hVU : V ≤ U) :
    Function.Surjective (deningerPrimeSectionsRestrictionLinearMap n1 n2 α β U V) := by
  intro g
  obtain ⟨f, hf, hfg⟩ := deningerPrimeSections_restrict_surjective hVU g.2
  exact ⟨⟨f, hf⟩, Subtype.ext hfg⟩

/-- The restriction kernel consists exactly of sections vanishing at every retained prime. -/
theorem mem_ker_deningerPrimeSectionsRestrictionLinearMap_iff
    (U V : Opens (PrimeSpectrum ℤ)) (f : deningerPrimeSections n1 n2 α β U) :
    f ∈ LinearMap.ker (deningerPrimeSectionsRestrictionLinearMap n1 n2 α β U V) ↔
      ∀ p, p ∈ deningerPrimeIndex V → f.1 p = 0 := by
  rw [LinearMap.mem_ker]
  constructor
  · intro hf p hp
    have h := congrArg (fun y => y.1 p) hf
    simpa [deningerPrimeSectionsRestrictionLinearMap, deningerPrimeRestrict_of_mem hp] using h
  · intro hf
    apply Subtype.ext
    funext p
    classical
    by_cases hp : p ∈ deningerPrimeIndex V
    · simp [deningerPrimeSectionsRestrictionLinearMap, deningerPrimeRestrict_of_mem hp, hf p hp]
    · simp [deningerPrimeSectionsRestrictionLinearMap, deningerPrimeRestrict_of_notMem hp]

/-- Sections on a smaller prime-open are sections on a larger prime-open modulo invisible
families. -/
noncomputable def deningerPrimeRestrictionHasseQuotientEquiv
    {U V : Opens (PrimeSpectrum ℤ)} (hVU : V ≤ U) :
    (deningerPrimeSections n1 n2 α β U ⧸
      LinearMap.ker (deningerPrimeSectionsRestrictionLinearMap n1 n2 α β U V)) ≃ₗ[ℝ]
      deningerPrimeSections n1 n2 α β V :=
  LinearMap.quotKerEquivOfSurjective (deningerPrimeSectionsRestrictionLinearMap n1 n2 α β U V)
    (deningerPrimeSectionsRestrictionLinearMap_surjective n1 n2 α β hVU)

/-- The prime-restriction Hasse equivalence is induced by coordinate deletion. -/
@[simp] theorem deningerPrimeRestrictionHasseQuotientEquiv_mk
    {U V : Opens (PrimeSpectrum ℤ)} (hVU : V ≤ U)
    (f : deningerPrimeSections n1 n2 α β U) :
    deningerPrimeRestrictionHasseQuotientEquiv n1 n2 α β hVU
      (Submodule.Quotient.mk f) = deningerPrimeSectionsRestrictionLinearMap n1 n2 α β U V f := by
  rfl

/-- Two larger-open prime sections restrict equally exactly when their difference is invisible on
the smaller open. -/
theorem deningerPrimeRestriction_congr_hasse_iff
    {U V : Opens (PrimeSpectrum ℤ)} (f g : deningerPrimeSections n1 n2 α β U) :
    f - g ∈ LinearMap.ker (deningerPrimeSectionsRestrictionLinearMap n1 n2 α β U V) ↔
      deningerPrimeSectionsRestrictionLinearMap n1 n2 α β U V f =
        deningerPrimeSectionsRestrictionLinearMap n1 n2 α β U V g := by
  rw [LinearMap.mem_ker]
  change deningerPrimeSectionsRestrictionLinearMap n1 n2 α β U V (f - g) = 0 ↔ _
  rw [map_sub, sub_eq_zero]

/-- Every smaller-open section extends to the larger open, uniquely modulo sections invisible on
the smaller open. -/
theorem deningerPrimeRestriction_exists_unique_mod_kernel
    {U V : Opens (PrimeSpectrum ℤ)} (hVU : V ≤ U)
    (z : deningerPrimeSections n1 n2 α β V) :
    ∃ f : deningerPrimeSections n1 n2 α β U,
      deningerPrimeSectionsRestrictionLinearMap n1 n2 α β U V f = z ∧
      ∀ g, deningerPrimeSectionsRestrictionLinearMap n1 n2 α β U V g = z ↔
        g - f ∈ LinearMap.ker (deningerPrimeSectionsRestrictionLinearMap n1 n2 α β U V) := by
  obtain ⟨f, hf⟩ := deningerPrimeSectionsRestrictionLinearMap_surjective n1 n2 α β hVU z
  refine ⟨f, hf, fun g => ?_⟩
  rw [← hf]
  exact (deningerPrimeRestriction_congr_hasse_iff n1 n2 α β g f).symm

end

end RHTower
