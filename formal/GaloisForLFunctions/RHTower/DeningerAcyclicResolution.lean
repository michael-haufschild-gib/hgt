import GaloisForLFunctions.RHTower.DeningerFlasqueAcyclic

/-!
# Acyclic resolutions compute sheaf cohomology

A sheaf is acyclic when all of its higher cohomology vanishes.  Two consequences of the covariant
long exact sequence of `Ext` are enough to make acyclic resolutions usable.

Dimension shifting: in a short exact sequence with acyclic middle term, a class in degree `n + 2`
of the subsheaf comes from degree `n + 1` of the quotient, so it vanishes as soon as that one does.

The bottom of the sequence: a class in degree one of the subsheaf comes from degree zero of the
quotient, and a section of the quotient that lifts to the middle term contributes nothing, so
degree one vanishes as soon as sections lift.

Iterating along a resolution by acyclic sheaves whose sections surject onto the sections of the
successive kernels therefore kills all higher cohomology of the resolved sheaf.  This is the
sheaf-theoretic half of Cartan's theorem B: the analytic half provides the lifting of sections,
which is the solvability of the differential equation defining the kernels.

* `RHTower.DeningerAcyclic` : all higher cohomology vanishes.
* `RHTower.deningerAcyclic_of_isFlasque` : flasque sheaves are acyclic.
* `RHTower.deningerExt_eq_zero_of_shift` : dimension shifting.
* `RHTower.deningerExt_one_eq_zero_of_lift` : degree one vanishes when sections lift.
* `RHTower.deningerResolution_ext_eq_zero` : **an acyclic resolution with lifting sections kills
  all higher cohomology.**
-/

namespace RHTower

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian TopologicalSpace Opposite TopCat

universe w u

variable {X : TopCat.{u}} [CategoryTheory.HasExt.{w} (TopCat.Sheaf AddCommGrpCat.{u} X)]

/-- A sheaf is acyclic when all of its higher cohomology vanishes. -/
def DeningerAcyclic (F : TopCat.Sheaf AddCommGrpCat.{u} X) : Prop :=
  ∀ (U : Opens X) (n : ℕ) (x : deningerSheafCohomology.{w} U F (n + 1)), x = 0

/-- **Flasque sheaves are acyclic.** -/
theorem deningerAcyclic_of_isFlasque {F : TopCat.Sheaf AddCommGrpCat.{u} X}
    (hF : TopCat.Sheaf.IsFlasque F) : DeningerAcyclic.{w} F :=
  fun U n x => deningerFlasque_ext_eq_zero n F hF U x

/-- **Injective sheaves are acyclic.** -/
theorem deningerAcyclic_of_injective (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    [CategoryTheory.Injective F] : DeningerAcyclic.{w} F :=
  deningerAcyclic_of_isFlasque (deningerInjective_isFlasque F)

/-- **Dimension shifting.**  In a short exact sequence with acyclic middle term, a class of the
subsheaf in degree `n + 2` is the image of a class of the quotient in degree `n + 1`. -/
theorem deningerExt_eq_zero_of_shift {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}
    (hS : S.ShortExact) (hA : DeningerAcyclic.{w} S.X₂) (U : Opens X) (n : ℕ)
    (hG : ∀ y : deningerSheafCohomology.{w} U S.X₃ (n + 1), y = 0)
    (x : deningerSheafCohomology.{w} U S.X₁ (n + 2)) : x = 0 := by
  obtain ⟨x₃, hx₃⟩ :=
    Ext.covariant_sequence_exact₁ (deningerOpenFree U) hS x (hA U (n + 1) _) (n₀ := n + 1) rfl
  rw [← hx₃, hG x₃]
  apply Ext.zero_comp

/-- **The bottom of the long exact sequence.**  If the middle term of a short exact sequence is
acyclic and its sections surject onto the sections of the quotient, the subsheaf has no cohomology
in degree one. -/
theorem deningerExt_one_eq_zero_of_lift {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}
    (hS : S.ShortExact) (hA : DeningerAcyclic.{w} S.X₂) (U : Opens X)
    (hsurj : Function.Surjective (ConcreteCategory.hom (S.g.1.app (op U))))
    (x : deningerSheafCohomology.{w} U S.X₁ 1) : x = 0 := by
  obtain ⟨x₃, hx₃⟩ :=
    Ext.covariant_sequence_exact₁ (deningerOpenFree U) hS x (hA U 0 _) (n₀ := 0) rfl
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

section Resolution

variable {K A : ℕ → TopCat.Sheaf AddCommGrpCat.{u} X} {ι : ∀ i, K i ⟶ A i}
  {π : ∀ i, A i ⟶ K (i + 1)} {hzero : ∀ i, ι i ≫ π i = 0}

/-- The `i`-th short exact sequence of a resolution. -/
abbrev deningerResolutionStep (ι : ∀ i, K i ⟶ A i) (π : ∀ i, A i ⟶ K (i + 1))
    (hzero : ∀ i, ι i ≫ π i = 0) (i : ℕ) : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X) :=
  ShortComplex.mk (ι i) (π i) (hzero i)

/-- **An acyclic resolution whose sections surject onto the sections of the successive kernels
kills all higher cohomology.**  Degree one dies because sections lift, and every higher degree is
shifted down one step along the resolution. -/
theorem deningerResolution_ext_eq_zero
    (hSE : ∀ i, (deningerResolutionStep ι π hzero i).ShortExact)
    (hacy : ∀ i, DeningerAcyclic.{w} (A i)) (U : Opens X)
    (hlift : ∀ i, Function.Surjective (ConcreteCategory.hom ((π i).1.app (op U)))) :
    ∀ (q i : ℕ) (x : deningerSheafCohomology.{w} U (K i) (q + 1)), x = 0 := by
  intro q
  induction q with
  | zero =>
      intro i x
      exact deningerExt_one_eq_zero_of_lift (hSE i) (hacy i) U (hlift i) x
  | succ p ih =>
      intro i x
      exact deningerExt_eq_zero_of_shift (hSE i) (hacy i) U p (ih (i + 1)) x

/-- The resolved sheaf of an acyclic resolution with lifting sections is itself acyclic on every
open set carrying the lifting property. -/
theorem deningerResolution_subsingleton_cohomology
    (hSE : ∀ i, (deningerResolutionStep ι π hzero i).ShortExact)
    (hacy : ∀ i, DeningerAcyclic.{w} (A i)) (U : Opens X)
    (hlift : ∀ i, Function.Surjective (ConcreteCategory.hom ((π i).1.app (op U)))) (q : ℕ) :
    Subsingleton (deningerSheafCohomology.{w} U (K 0) (q + 1)) :=
  ⟨fun a b => by
    rw [deningerResolution_ext_eq_zero hSE hacy U hlift q 0 a,
      deningerResolution_ext_eq_zero hSE hacy U hlift q 0 b]⟩

end Resolution

end RHTower
