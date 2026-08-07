import GaloisForLFunctions.HTGeometry.MinimalHTCompletionArchitecture

/-!
# Surjectivity of a divisor map from single-class realization

The orbit-divisor group `ℤ[G] = G →₀ ℤ` is free abelian on `G`, so a divisor homomorphism is
surjective as soon as every single class `[g]` is realized: products add divisors and integer powers
supply signed multiplicities.  This turns the surjectivity hypothesis of the Kummer root
classification into the single statement that one source with divisor `[g]` exists for each `g`.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped BigOperators

/-- **Surjectivity from single-class realization.**  A homomorphism to `ℤ[G]` whose image contains
every generator `[g]` is surjective. -/
theorem addMonoidHom_surjective_of_single {M G : Type*} [AddCommGroup M] (D : M →+ G →₀ ℤ)
    (h : ∀ g : G, ∃ Y : M, D Y = Finsupp.single g 1) : Function.Surjective D := by
  classical
  intro E
  refine Finsupp.induction E ⟨0, map_zero D⟩ ?_
  rintro a b f - - ⟨Z, hZ⟩
  obtain ⟨Y, hY⟩ := h a
  refine ⟨b • Y + Z, ?_⟩
  rw [map_add, map_zsmul, hY, hZ, Finsupp.smul_single, smul_eq_mul, mul_one]

/-- **The Kummer root classification from single-class realization.**  If every class `[g]` is
realized by some source, then a source has an `m`-th root modulo the differentially algebraic kernel
exactly when `m` divides the content of its orbit divisor. -/
theorem hasSourceRootModuloKernel_iff_content_dvd_of_single {M G : Type*} [AddCommGroup M]
    (D : M →+ G →₀ ℤ) (h : ∀ g : G, ∃ Y : M, D Y = Finsupp.single g 1) (m : ℕ) (Y : M) :
    HasSourceRootModuloKernel D m Y ↔ m ∣ integralOrbitDivisorContent (D Y) :=
  hasSourceRootModuloKernel_iff_content_dvd D (addMonoidHom_surjective_of_single D h) m Y

/-- **The effective quotient.**  With every class realized, the divisor map induces an isomorphism
of the source class group modulo its differentially algebraic kernel onto `ℤ[G]`. -/
noncomputable def sourceQuotientEquiv {M G : Type*} [AddCommGroup M] (D : M →+ G →₀ ℤ)
    (h : ∀ g : G, ∃ Y : M, D Y = Finsupp.single g 1) :
    (M ⧸ D.ker) ≃+ (G →₀ ℤ) :=
  QuotientAddGroup.quotientKerEquivOfSurjective D (addMonoidHom_surjective_of_single D h)

end GaloisForLFunctions.HTGeometry
