import GaloisForLFunctions.RHTower.XiReflectionTateConormalLocalization

/-!
# Conservative reflection-Tate reporting is exactly fixed-locus support

A charge lattice is conservatively reported by reflection-Tate cohomology exactly when every one of
its charges is supported on the reflection fixed locus.  One direction is the recorded faithful
localization theorem; the converse builds the reporter by restricting a fixed-supported charge to
the fixed locus and inverting the Tate identification, so no extra input is needed.

The reduction consuming that hypothesis therefore has an exact converse: the existence of a
conormal landing lattice with a conservative Tate reporter is *equivalent* to the Riemann
hypothesis.  The reduction restates RH; it does not weaken it.
-/

open GaloisForLFunctions

namespace GaloisForLFunctions

noncomputable section

universe u

variable {ι : Type u}

/-- The charges supported on the reflection fixed locus form a subgroup. -/
def fixedSupportedCharges (r : ι ≃ ι) : AddSubgroup (ι →₀ ZMod 2) where
  carrier := {q | ∀ i ∈ q.support, r i = i}
  zero_mem' := by
    intro i hi
    simp at hi
  add_mem' := by
    classical
    intro a b ha hb i hi
    rcases Finset.mem_union.mp (Finsupp.support_add hi) with h | h
    · exact ha i h
    · exact hb i h
  neg_mem' := by
    intro a ha i hi
    exact ha i (by simpa using hi)

theorem mem_fixedSupportedCharges {r : ι ≃ ι} {q : ι →₀ ZMod 2} :
    q ∈ fixedSupportedCharges r ↔ ∀ i ∈ q.support, r i = i :=
  ⟨fun h => h, fun h => h⟩

/-- Restriction of a charge to the reflection fixed locus. -/
noncomputable def reflectionFixedRestriction (r : ι ≃ ι) :
    (ι →₀ ZMod 2) →+ (ReflectionFixedPoint r →₀ ZMod 2) := by
  classical
  exact Finsupp.subtypeDomainAddMonoidHom (p := fun i => r i = i)

@[simp] theorem reflectionFixedRestriction_apply (r : ι ≃ ι) (q : ι →₀ ZMod 2)
    (i : ι) (hi : r i = i) :
    reflectionFixedRestriction r q ⟨i, hi⟩ = q i := rfl

/-- Extending a fixed-supported charge after restricting it returns the charge. -/
theorem reflectionFixedExtension_reflectionFixedRestriction
    (r : ι ≃ ι) {q : ι →₀ ZMod 2} (hq : ∀ i ∈ q.support, r i = i) :
    reflectionFixedExtension r (reflectionFixedRestriction r q) = q := by
  classical
  ext i
  by_cases hi : r i = i
  · simp [reflectionFixedExtension, Finsupp.extendDomain_apply, hi]
    rfl
  · have hzero : q i = 0 := by
      by_contra hne
      exact hi (hq i (Finsupp.mem_support_iff.mpr hne))
    simp [reflectionFixedExtension, Finsupp.extendDomain_apply, hi, hzero]

/-- A lattice of fixed-supported charges carries a conservative reflection-Tate reporter. -/
theorem isReflectionTateConservative_of_fixedSupport
    (r : ι ≃ ι) (hr : Function.Involutive r) (B : AddSubgroup (ι →₀ ZMod 2))
    (hB : ∀ q ∈ B, ∀ i ∈ (q : ι →₀ ZMod 2).support, r i = i) :
    IsReflectionTateConservative r hr B := by
  classical
  refine ⟨((reflectionTateCohomologyEquivFixedParity r hr).symm.toAddMonoidHom).comp
      ((reflectionFixedRestriction r).comp B.subtype), fun q => ?_⟩
  show reflectionFixedExtension r
      ((reflectionTateCohomologyEquivFixedParity r hr)
        ((reflectionTateCohomologyEquivFixedParity r hr).symm
          (reflectionFixedRestriction r q.1))) = q.1
  rw [AddEquiv.apply_symm_apply]
  exact reflectionFixedExtension_reflectionFixedRestriction r (hB q.1 q.2)

/-- **Conservativity is support.**  A charge lattice admits a conservative reflection-Tate reporter
exactly when every charge in it is supported on the reflection fixed locus. -/
theorem isReflectionTateConservative_iff
    (r : ι ≃ ι) (hr : Function.Involutive r) (B : AddSubgroup (ι →₀ ZMod 2)) :
    IsReflectionTateConservative r hr B ↔
      ∀ q ∈ B, ∀ i ∈ (q : ι →₀ ZMod 2).support, r i = i := by
  constructor
  · intro hcons q hq i hi
    exact support_fixed_of_reflectionTateConservative r hr B hcons ⟨q, hq⟩ hi
  · exact isReflectionTateConservative_of_fixedSupport r hr B

/-- The subgroup of fixed-supported charges is itself conservatively reported. -/
theorem isReflectionTateConservative_fixedSupportedCharges
    (r : ι ≃ ι) (hr : Function.Involutive r) :
    IsReflectionTateConservative r hr (fixedSupportedCharges r) :=
  (isReflectionTateConservative_iff r hr _).mpr fun _ hq => mem_fixedSupportedCharges.mp hq

end

end GaloisForLFunctions

namespace RHTower

noncomputable section

/-- **The reflection-Tate reduction is an equivalence.**  A conormal landing lattice with a
conservative reflection-Tate reporter exists exactly when the Riemann hypothesis holds.  The
forward direction is the recorded reduction; the converse takes the lattice of all
reflection-fixed-supported charges, which is conservative unconditionally and receives every Xi
point charge as soon as every Xi zero is reflection fixed. -/
theorem riemannHypothesis_iff_exists_reflectionTateConservative_landing :
    RiemannHypothesis ↔
      ∃ B : AddSubgroup (ℂ →₀ ZMod 2),
        XiPrincipalConormalLandsIn B ∧
          IsReflectionTateConservative xiFEReflection xiFEReflection_involutive B := by
  constructor
  · intro hRH
    refine ⟨fixedSupportedCharges xiFEReflection, ?_,
      isReflectionTateConservative_fixedSupportedCharges _ _⟩
    intro ρ hρ
    refine mem_fixedSupportedCharges.mpr ?_
    intro i hi
    have hiρ : i = ρ := by
      have := Finsupp.support_single_subset hi
      simpa using this
    subst hiρ
    have hfix : 1 - starRingEnd ℂ i = i :=
      (riemannHypothesis_iff_xiZero_reflection_fixed.mp hRH) i hρ
    simpa [xiFEReflection] using hfix
  · rintro ⟨B, hland, hcons⟩
    exact riemannHypothesis_of_reflectionTate_conormal_localization B hland hcons

end

end RHTower
