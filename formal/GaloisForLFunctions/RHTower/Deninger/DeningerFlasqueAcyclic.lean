import GaloisForLFunctions.RHTower.Deninger.DeningerOpenFreeSheaf

/-!
# Flasque sheaves are acyclic

Sheaf cohomology on an open set is the `Ext` out of the free abelian sheaf on that open set, so
degree zero is sections.  A flasque sheaf has no higher cohomology: embed it in an injective sheaf,
which is flasque, so the quotient is flasque too and sections of the injective surject onto sections
of the quotient; the covariant long exact sequence of `Ext` then kills degree one, and the same
sequence shifts degree `n+1` of the sheaf to degree `n` of the flasque quotient.

* `deningerSheafCohomology` : sheaf cohomology on an open set.
* `deningerSheafCohomologyZeroEquiv` : degree zero is sections.
* `deningerFlasque_isZero_cohomology` : **a flasque sheaf has no higher cohomology**.
-/

namespace RHTower

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian TopologicalSpace Opposite TopCat

universe w u

variable {X : TopCat.{u}} [CategoryTheory.HasExt.{w} (TopCat.Sheaf AddCommGrpCat.{u} X)]

/-- **Sheaf cohomology on an open set**: the `Ext` out of the free abelian sheaf on it. -/
noncomputable abbrev deningerSheafCohomology (U : Opens X)
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) (n : ℕ) : Type w :=
  Abelian.Ext.{w} (deningerOpenFree U) F n

/-- **Degree zero of sheaf cohomology is sections.** -/
noncomputable def deningerSheafCohomologyZeroEquiv (U : Opens X)
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) :
    deningerSheafCohomology U F 0 ≃ ToType (F.1.obj (op U)) :=
  Ext.addEquiv₀.toEquiv.trans (deningerOpenFreeHomEquiv U F)

/-- The short exact sequence embedding a sheaf into an injective one. -/
noncomputable abbrev deningerInjectiveEmbedding (F : TopCat.Sheaf AddCommGrpCat.{u} X) :
    ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X) :=
  ShortComplex.mk (CategoryTheory.Injective.ι F)
    (cokernel.π (CategoryTheory.Injective.ι F)) (by simp)

omit [CategoryTheory.HasExt.{w} (TopCat.Sheaf AddCommGrpCat.{u} X)] in
theorem deningerInjectiveEmbedding_shortExact (F : TopCat.Sheaf AddCommGrpCat.{u} X) :
    (deningerInjectiveEmbedding F).ShortExact where
  exact := ShortComplex.exact_cokernel _
  mono_f := inferInstance
  epi_g := inferInstance

/-- **A flasque sheaf has no higher cohomology.** -/
theorem deningerFlasque_ext_eq_zero :
    ∀ (n : ℕ) (F : TopCat.Sheaf AddCommGrpCat.{u} X), TopCat.Sheaf.IsFlasque F →
      ∀ (U : Opens X) (x : deningerSheafCohomology.{w} U F (n + 1)), x = 0 := by
  intro n
  induction n with
  | zero =>
    intro F hF U x
    set S := deningerInjectiveEmbedding F with hSdef
    have hS : S.ShortExact := deningerInjectiveEmbedding_shortExact F
    haveI : TopCat.Sheaf.IsFlasque S.X₁ := hF
    haveI : CategoryTheory.Injective S.X₂ := CategoryTheory.Injective.injective_under F
    haveI : TopCat.Sheaf.IsFlasque S.X₂ := deningerInjective_isFlasque S.X₂
    obtain ⟨x₃, hx₃⟩ := Ext.covariant_sequence_exact₁ (deningerOpenFree U) hS x
      (Ext.eq_zero_of_injective _) (n₀ := 0) rfl
    have hepi : Epi (S.g.1.app (op U)) := TopCat.Sheaf.IsFlasque.epi_of_shortExact hS
    have hsurj : Function.Surjective (ConcreteCategory.hom (S.g.1.app (op U))) :=
      (AddCommGrpCat.epi_iff_surjective _).1 hepi
    obtain ⟨s₂, hs₂⟩ := hsurj (deningerOpenFreeHomEquiv U S.X₃ (Ext.addEquiv₀ x₃))
    set φ₂ : deningerOpenFree U ⟶ S.X₂ := (deningerOpenFreeHomEquiv U S.X₂).symm s₂ with hφ₂
    have hcomp : φ₂ ≫ S.g = Ext.addEquiv₀ x₃ := by
      refine (deningerOpenFreeHomEquiv U S.X₃).injective ?_
      rw [deningerOpenFreeHomEquiv_naturality_right, hφ₂, Equiv.apply_symm_apply]
      exact hs₂
    have hx₃eq : x₃ = (Ext.mk₀ φ₂).comp (Ext.mk₀ S.g) (add_zero 0) := by
      rw [Ext.mk₀_comp_mk₀, hcomp]
      exact (Ext.mk₀_addEquiv₀_apply x₃).symm
    rw [← hx₃, hx₃eq,
      Ext.comp_assoc (Ext.mk₀ φ₂) (Ext.mk₀ S.g) hS.extClass (add_zero 0) (zero_add 1) rfl,
      hS.comp_extClass]
    apply Ext.comp_zero
  | succ k ih =>
    intro F hF U x
    set S := deningerInjectiveEmbedding F with hSdef
    have hS : S.ShortExact := deningerInjectiveEmbedding_shortExact F
    haveI : TopCat.Sheaf.IsFlasque S.X₁ := hF
    haveI : CategoryTheory.Injective S.X₂ := CategoryTheory.Injective.injective_under F
    haveI : TopCat.Sheaf.IsFlasque S.X₂ := deningerInjective_isFlasque S.X₂
    haveI hQ : TopCat.Sheaf.IsFlasque S.X₃ :=
      TopCat.Sheaf.IsFlasque.of_shortExact_of_isFlasque₁₂ hS
    obtain ⟨x₃, hx₃⟩ := Ext.covariant_sequence_exact₁ (deningerOpenFree U) hS x
      (Ext.eq_zero_of_injective _) (n₀ := k + 1) rfl
    have hzero : x₃ = 0 := ih S.X₃ hQ U x₃
    rw [← hx₃, hzero]
    apply Ext.zero_comp

/-- **A flasque sheaf has no higher cohomology**, as a subsingleton statement. -/
theorem deningerFlasque_subsingleton_cohomology (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    (hF : TopCat.Sheaf.IsFlasque F) (U : Opens X) (n : ℕ) :
    Subsingleton (deningerSheafCohomology.{w} U F (n + 1)) :=
  ⟨fun a b => by
    rw [deningerFlasque_ext_eq_zero n F hF U a, deningerFlasque_ext_eq_zero n F hF U b]⟩

end RHTower

namespace RHTower

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian TopologicalSpace Opposite TopCat

universe w u

variable {X : TopCat.{u}} [CategoryTheory.HasExt.{w} (TopCat.Sheaf AddCommGrpCat.{u} X)]

/-- **A sheaf with a length-one flasque resolution has amplitude `[0,1]`**: its cohomology vanishes
in every degree above one. -/
theorem deningerLengthOneFlasque_ext_eq_zero
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)} (hS : S.ShortExact)
    (h2 : TopCat.Sheaf.IsFlasque S.X₂) (h3 : TopCat.Sheaf.IsFlasque S.X₃)
    (U : Opens X) (n : ℕ) (x : deningerSheafCohomology.{w} U S.X₁ (n + 2)) : x = 0 := by
  obtain ⟨x₃, hx₃⟩ := Ext.covariant_sequence_exact₁ (deningerOpenFree U) hS x
    (deningerFlasque_ext_eq_zero (n + 1) S.X₂ h2 U _) (n₀ := n + 1) rfl
  rw [← hx₃, deningerFlasque_ext_eq_zero n S.X₃ h3 U x₃]
  apply Ext.zero_comp

/-- **A sheaf with a length-one flasque resolution has amplitude `[0,1]`**, as a subsingleton
statement. -/
theorem deningerLengthOneFlasque_subsingleton
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)} (hS : S.ShortExact)
    (h2 : TopCat.Sheaf.IsFlasque S.X₂) (h3 : TopCat.Sheaf.IsFlasque S.X₃)
    (U : Opens X) (n : ℕ) :
    Subsingleton (deningerSheafCohomology.{w} U S.X₁ (n + 2)) :=
  ⟨fun a b => by
    rw [deningerLengthOneFlasque_ext_eq_zero hS h2 h3 U n a,
      deningerLengthOneFlasque_ext_eq_zero hS h2 h3 U n b]⟩

end RHTower
