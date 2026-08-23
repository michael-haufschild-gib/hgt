import GaloisForLFunctions.HTGeometry.ABHN.RatModIntTorsionCircleCharacter

/-!
# Directed system of finite local-invariant targets

Finite unramified cyclic local invariants naturally land in `ℚ/ℤ[n] ≃ ℤ/nℤ`.  This file
constructs their canonical transition maps when one denominator divides another.  The maps are
injective, satisfy identity and composition laws, are uniquely characterized by compatibility
with `ℚ/ℤ`, and preserve standard circle phases.

Together with exhaustion of `ℚ/ℤ` by its finite torsion layers, this supplies the target-side
directed system needed to assemble finite local-cohomology invariants.  Constructing compatible
source-side inflation maps, and comparing their colimit with the local Brauer group, remain
separate class-field-theoretic steps.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

noncomputable section

/-- Inclusion of finite torsion layers along divisibility. -/
def ratModIntNTorsionInclusion {m n : ℕ} (hmn : m ∣ n) :
    ratModIntNTorsion m →+ ratModIntNTorsion n :=
  AddSubgroup.inclusion (ratModIntNTorsion_mono hmn)

@[simp] theorem ratModIntNTorsionInclusion_coe {m n : ℕ} (hmn : m ∣ n)
    (x : ratModIntNTorsion m) :
    ((ratModIntNTorsionInclusion hmn x : ratModIntNTorsion n) : RatModInt) = x := rfl

/-- Canonical transition `ℤ/mℤ → ℤ/nℤ` induced by the common embedding in `ℚ/ℤ`. -/
noncomputable def zmodRatModIntTransition {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0)
    (hmn : m ∣ n) : ZMod m →+ ZMod n :=
  (zmodRatModIntAddEquivNTorsion n hn).symm.toAddMonoidHom.comp
    ((ratModIntNTorsionInclusion hmn).comp
      (zmodRatModIntAddEquivNTorsion m hm).toAddMonoidHom)

/-- Transition maps preserve the represented rational class modulo integers. -/
theorem zmodRatModIntAddHom_transition {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0)
    (hmn : m ∣ n) (x : ZMod m) :
    zmodRatModIntAddHom n hn (zmodRatModIntTransition hm hn hmn x) =
      zmodRatModIntAddHom m hm x := by
  change (((zmodRatModIntAddEquivNTorsion n hn)
      ((zmodRatModIntAddEquivNTorsion n hn).symm
        (ratModIntNTorsionInclusion hmn
          (zmodRatModIntAddEquivNTorsion m hm x))) : ratModIntNTorsion n) : RatModInt) =
    ((zmodRatModIntAddEquivNTorsion m hm x : ratModIntNTorsion m) : RatModInt)
  rw [AddEquiv.apply_symm_apply]
  rfl

/-- Every torsion-level transition is injective. -/
theorem zmodRatModIntTransition_injective {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0)
    (hmn : m ∣ n) : Function.Injective (zmodRatModIntTransition hm hn hmn) := by
  intro x y hxy
  apply zmodRatModIntAddHom_injective m hm
  rw [← zmodRatModIntAddHom_transition hm hn hmn x,
    ← zmodRatModIntAddHom_transition hm hn hmn y, hxy]

/-- Canonical transition is uniquely determined by compatibility with `ℚ/ℤ`. -/
theorem zmodRatModIntTransition_unique {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0)
    (hmn : m ∣ n) (f : ZMod m →+ ZMod n)
    (hf : ∀ x, zmodRatModIntAddHom n hn (f x) = zmodRatModIntAddHom m hm x) :
    f = zmodRatModIntTransition hm hn hmn := by
  ext x
  apply zmodRatModIntAddHom_injective n hn
  rw [hf, zmodRatModIntAddHom_transition]

/-- Identity transition law. -/
theorem zmodRatModIntTransition_self (n : ℕ) (hn : n ≠ 0) :
    zmodRatModIntTransition hn hn (dvd_refl n) = AddMonoidHom.id (ZMod n) := by
  symm
  apply zmodRatModIntTransition_unique hn hn (dvd_refl n)
  intro x
  rfl

/-- Composition law for the finite torsion transition system. -/
theorem zmodRatModIntTransition_comp {l m n : ℕ}
    (hl : l ≠ 0) (hm : m ≠ 0) (hn : n ≠ 0)
    (hlm : l ∣ m) (hmn : m ∣ n) :
    (zmodRatModIntTransition hm hn hmn).comp (zmodRatModIntTransition hl hm hlm) =
      zmodRatModIntTransition hl hn (dvd_trans hlm hmn) := by
  apply zmodRatModIntTransition_unique hl hn (dvd_trans hlm hmn)
  intro x
  rw [AddMonoidHom.comp_apply, zmodRatModIntAddHom_transition,
    zmodRatModIntAddHom_transition]

/-- Standard finite circle characters are compatible under torsion-level inclusion. -/
theorem ratModIntNTorsionStdAddChar_inclusion {m n : ℕ}
    (hm : m ≠ 0) (hn : n ≠ 0) (hmn : m ∣ n) (x : ratModIntNTorsion m) :
    ratModIntNTorsionStdAddChar n hn (ratModIntNTorsionInclusion hmn x) =
      ratModIntNTorsionStdAddChar m hm x := by
  rw [← ratModIntStdAddChar_subtype_eq_ratModIntNTorsionStdAddChar n hn,
    ← ratModIntStdAddChar_subtype_eq_ratModIntNTorsionStdAddChar m hm]
  rfl

/-- Standard `ZMod` phases are unchanged by refinement to a divisible denominator. -/
theorem zmodStdAddChar_transition {m n : ℕ}
    (hm : m ≠ 0) (hn : n ≠ 0) (hmn : m ∣ n) (x : ZMod m) :
    @ZMod.stdAddChar n ⟨hn⟩ (zmodRatModIntTransition hm hn hmn x) =
      @ZMod.stdAddChar m ⟨hm⟩ x := by
  rw [← ratModIntStdAddChar_zmodRatModIntAddHom n hn,
    zmodRatModIntAddHom_transition,
    ratModIntStdAddChar_zmodRatModIntAddHom m hm]

/-- Finite torsion layers generate all of `ℚ/ℤ` as an additive subgroup. -/
theorem iSup_ratModIntNTorsion_eq_top :
    ⨆ n : ℕ, ratModIntNTorsion n = ⊤ := by
  apply le_antisymm le_top
  intro x _
  obtain ⟨n, _, hx⟩ := ratModInt_exists_nonzero_nsmul_eq_zero x
  exact (le_iSup (fun n : ℕ ↦ ratModIntNTorsion n) n) hx

/-- Maps out of `ℚ/ℤ` are determined by all finite torsion restrictions. -/
theorem ratModInt_addMonoidHom_ext_of_torsion
    {A : Type*} [AddGroup A] (f g : RatModInt →+ A)
    (h : ∀ (n : ℕ) (x : ratModIntNTorsion n), f x = g x) :
    f = g := by
  ext x
  obtain ⟨n, _, hx⟩ := ratModInt_exists_nonzero_nsmul_eq_zero x
  exact h n ⟨x, hx⟩

end

end GaloisForLFunctions.HTGeometry.ABHN
