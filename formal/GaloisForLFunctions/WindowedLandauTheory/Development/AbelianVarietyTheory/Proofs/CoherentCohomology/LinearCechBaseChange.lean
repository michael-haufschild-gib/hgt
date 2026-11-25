import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.LinearCechComplex
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Homology.Additive
import Mathlib.RingTheory.TensorProduct.IsBaseChangePi

/-! Finite alternating Čech complexes commute with termwise scalar extension. -/

noncomputable section

open CategoryTheory HTGeometry TensorProduct
open scoped ChangeOfRings

namespace HTGeometry.FinsetCechDatum

variable {R S : Type} [CommRing R] [CommRing S]
  {ι : Type} [DecidableEq ι] [LinearOrder ι] {D E : FinsetCechDatum.{0} ι}
  [∀ s, Module R (D.obj s)] [∀ s, Module S (E.obj s)]
  (α : R →+* S) (φ : D.Hom E) (hφ : ∀ s (r : R) (x : D.obj s),
    φ.app s (r • x) = α r • φ.app s x)

private abbrev appLinear (s : Finset ι) :
    letI : Module R (E.obj s) := Module.compHom _ α
    D.obj s →ₗ[R] E.obj s :=
  letI : Module R (E.obj s) := Module.compHom _ α
  { φ.app s with map_smul' := hφ s }

private def degreeMapOver (n : ℕ) :
    letI : Module R (E.degreeSubmodule (R := S) n) := Module.compHom _ α
    D.degreeSubmodule (R := R) n →ₗ[R] E.degreeSubmodule (R := S) n :=
  letI : Module R (E.degreeSubmodule (R := S) n) := Module.compHom _ α
  { toFun := fun x => ⟨φ.onCochain x.1, φ.onCochain_isDeg x.2⟩
    map_add' := fun x y => Subtype.ext (funext fun s => map_add (φ.app s) (x.1 s) (y.1 s))
    map_smul' := fun r x => Subtype.ext (funext fun s => hφ s r (x.1 s)) }

variable (hD : ∀ {s t : Finset ι} (h : s ⊆ t) (r : R) (x : D.obj s),
    D.res h (r • x) = r • D.res h x)
  (hE : ∀ {s t : Finset ι} (h : s ⊆ t) (r : S) (x : E.obj s),
    E.res h (r • x) = r • E.res h x)

/-- The comparison map is obtained by extending each cochain pullback linearly. -/
def linearBaseChange (α : R →+* S) (φ : D.Hom E)
    (hφ : ∀ s (r : R) (x : D.obj s), φ.app s (r • x) = α r • φ.app s x)
    (hD : ∀ {s t : Finset ι} (h : s ⊆ t) (r : R) (x : D.obj s),
      D.res h (r • x) = r • D.res h x)
    (hE : ∀ {s t : Finset ι} (h : s ⊆ t) (r : S) (x : E.obj s),
      E.res h (r • x) = r • E.res h x) :
    (((ModuleCat.extendScalars α).mapHomologicalComplex (ComplexShape.up ℕ)).obj
      (D.linearComplex hD)) ⟶ E.linearComplex hE :=
  letI : Algebra R S := α.toAlgebra
  CochainComplex.ofHom (fun n => by
    letI : Module R (E.degreeSubmodule (R := S) n) := Module.compHom _ α
    letI : IsScalarTower R S (E.degreeSubmodule (R := S) n) :=
      .of_algebraMap_smul fun _ _ => rfl
    change ModuleCat.of S (S ⊗[R] (D.degreeSubmodule (R := R) n)) ⟶
      ModuleCat.of S (E.degreeSubmodule (R := S) n)
    exact ModuleCat.ofHom (LinearMap.liftBaseChange S (degreeMapOver α φ hφ n))) (by
      intro n
      apply ModuleCat.ExtendScalars.hom_ext
      intro x
      letI (k : ℕ) : Module R (E.degreeSubmodule (R := S) k) := Module.compHom _ α
      letI (k : ℕ) : IsScalarTower R S (E.degreeSubmodule (R := S) k) :=
        .of_algebraMap_smul fun _ _ => rfl
      let d := (D.linearComplex hD).d n (n + 1)
      change (E.linearComplex hE).d n (n + 1)
          ((degreeMapOver α φ hφ n).liftBaseChange S ((1 : S) ⊗ₜ[R] x)) =
        (degreeMapOver α φ hφ (n + 1)).liftBaseChange S
          ((ModuleCat.extendScalars α).map d ((1 : S) ⊗ₜ[R,α] x))
      rw [ModuleCat.ExtendScalars.map_tmul]
      let x₀ : D.degreeSubmodule (R := R) n := x
      let x₁ : D.degreeSubmodule (R := R) (n + 1) := d x
      change (E.linearComplex hE).d n (n + 1)
          ((degreeMapOver α φ hφ n).liftBaseChange S ((1 : S) ⊗ₜ[R] x₀)) =
        (degreeMapOver α φ hφ (n + 1)).liftBaseChange S ((1 : S) ⊗ₜ[R] x₁)
      simp only [LinearMap.liftBaseChange_tmul, one_smul, x₁, d,
        FinsetCechDatum.linearComplex, CochainComplex.of_d]
      exact Subtype.ext (φ.d_onCochain x₀.1))

theorem linearBaseChange_f_tmul (n : ℕ) (s : S) (x : (D.linearComplex hD).X n) (a : Finset ι) :
    ((linearBaseChange α φ hφ hD hE).f n (s ⊗ₜ[R,α] x)).1 a =
      s • φ.app a (x.1 a) := rfl

private theorem degree_isBaseChange [Fintype ι] (n : ℕ)
    (h : ∀ s : Finset ι, s.Nonempty →
      letI : Algebra R S := α.toAlgebra
      letI : Module R (E.obj s) := Module.compHom _ α
      letI : IsScalarTower R S (E.obj s) := .of_algebraMap_smul fun _ _ => rfl
      IsBaseChange S (appLinear α φ hφ s)) :
    letI : Algebra R S := α.toAlgebra
    letI : Module R (E.degreeSubmodule (R := S) n) := Module.compHom _ α
    letI : IsScalarTower R S (E.degreeSubmodule (R := S) n) :=
      .of_algebraMap_smul fun _ _ => rfl
    IsBaseChange S (degreeMapOver α φ hφ n) := by
  letI : Algebra R S := α.toAlgebra
  let I := {s : Finset ι // s.card = n + 1}
  letI (s : I) : Module R (E.obj s.1) := Module.compHom _ α
  letI (s : I) : IsScalarTower R S (E.obj s.1) := .of_algebraMap_smul fun _ _ => rfl
  letI : Module R (E.degreeSubmodule (R := S) n) := Module.compHom _ α
  letI : IsScalarTower R S (E.degreeSubmodule (R := S) n) := .of_algebraMap_smul fun _ _ => rfl
  let H := IsBaseChange.pi (fun s : I => appLinear α φ hφ s.1) (fun s =>
    h s.1 (Finset.card_pos.mp (by rw [s.2]; omega)))
  refine (IsBaseChange.iff_of_equiv_comm (D.degreeLinearEquiv (R := R) n)
    (E.degreeLinearEquiv (R := S) n) ?_).mpr H
  exact LinearMap.ext fun _ => rfl

theorem isIso_linearBaseChange [Fintype ι]
    (h : ∀ s : Finset ι, s.Nonempty →
      letI : Algebra R S := α.toAlgebra
      letI : Module R (E.obj s) := Module.compHom _ α
      letI : IsScalarTower R S (E.obj s) := .of_algebraMap_smul fun _ _ => rfl
      IsBaseChange S (appLinear α φ hφ s)) :
    IsIso (linearBaseChange α φ hφ hD hE) := by
  letI : Algebra R S := α.toAlgebra
  haveI (n : ℕ) : IsIso ((linearBaseChange α φ hφ hD hE).f n) := by
    letI : Module R (E.degreeSubmodule (R := S) n) := Module.compHom _ α
    letI : IsScalarTower R S (E.degreeSubmodule (R := S) n) := .of_algebraMap_smul fun _ _ => rfl
    let e := (degree_isBaseChange α φ hφ n h).equiv
    have he : (linearBaseChange α φ hφ hD hE).f n = e.toModuleIso.hom := by
      apply ModuleCat.ExtendScalars.hom_ext
      intro x
      change (1 : S) • degreeMapOver α φ hφ n x = e (1 ⊗ₜ[R] x)
      exact ((degree_isBaseChange α φ hφ n h).equiv_tmul 1 x).symm
    rw [he]
    infer_instance
  exact HomologicalComplex.Hom.isIso_of_components _

end HTGeometry.FinsetCechDatum
