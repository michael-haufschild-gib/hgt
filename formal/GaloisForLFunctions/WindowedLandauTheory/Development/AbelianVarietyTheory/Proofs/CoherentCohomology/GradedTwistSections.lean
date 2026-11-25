import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.GradedPolynomialAction
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.LineBundleTwistMultiplication
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.LineBundleSectionScalarChange

/-! The sections of the integer twists form a graded module over the coordinate polynomial ring. -/

noncomputable section

open AlgebraicGeometry CategoryTheory MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.SchemeCohomology

namespace GlobalTheory.LineBundleSections

variable {R : Type} [CommRing R] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of R))
  (M H : LB X) (V : X.Opens)

/-- Tag a section of a twist by the structure morphism determining its scalar action. -/
def TwistSections (_f : X ⟶ Spec (CommRingCat.of R)) (M H : LB X) (V : X.Opens) (t : ℤ) : Type :=
  Γ(toMod (twist M H t), V)

instance (t : ℤ) : AddCommGroup (TwistSections f M H V t) :=
  inferInstanceAs (AddCommGroup Γ(toMod (twist M H t), V))

instance (t : ℤ) : Module Γ(X, V) (TwistSections f M H V t) :=
  inferInstanceAs (Module Γ(X, V) Γ(toMod (twist M H t), V))

instance (t : ℤ) : Module R (TwistSections f M H V t) :=
  sectionBaseModule f (toMod (twist M H t)) V

variable {H}

def twistSections_mul (s : H.Sec) (t : ℤ) :
    TwistSections f M H V t →ₗ[R] TwistSections f M H V (t + 1) :=
  letI := sectionAlgebra f V
  { (mulTwistSection M t s V).toAddMonoidHom with
    map_smul' r x := (mulTwistSection M t s V).map_smul (algebraMap R Γ(X, V) r) x }

variable {V} {W : X.Opens}

def twistSections_res (h : W ≤ V) (t : ℤ) :
    TwistSections f M H V t →ₗ[R] TwistSections f M H W t :=
  letI := sectionAlgebra f V
  letI := sectionAlgebra f W
  { secRes (twist M H t) h with
    map_smul' r x := by
      change secRes _ h (algebraMap R Γ(X, V) r • x) =
        algebraMap R Γ(X, W) r • secRes _ h x
      have e := (sectionRes f (homOfLE h)).commutes r
      change resG X h (algebraMap R Γ(X, V) r) = algebraMap R Γ(X, W) r at e
      exact (secRes_smul (twist M H t) h (algebraMap R Γ(X, V) r) x).trans
        (congrArg (fun a : Γ(X, W) => a • secRes (twist M H t) h x) e) }

variable (V) {ι : Type}

theorem twistSections_commute (s : ι → H.Sec) :
    OperatorsCommute (A := TwistSections f M H V) fun i t => twistSections_mul f M V (s i) t :=
  fun i j _ x => mulTwistSection_comm (s i) (s j) x

/-- The direct sum of the spaces of twisted sections, with each variable acting
by multiplication by the corresponding bundle section. -/
abbrev gradedTwistSections (s : ι → H.Sec) := GrSum (twistSections_commute f M V s)

variable {V}

def gradedTwistSections_res (s : ι → H.Sec) (h : W ≤ V) :
    gradedTwistSections f M V s →ₗ[MvPolynomial ι R] gradedTwistSections f M W s :=
  GrSum.map (twistSections_commute f M V s) (twistSections_commute f M W s)
    (twistSections_res f M h) fun i _ x => (mulTwistSection_restrict (s i) h x).symm

theorem gradedTwistSections_res_of (s : ι → H.Sec) (h : W ≤ V) (t : ℤ)
    (x : TwistSections f M H V t) :
    gradedTwistSections_res f M s h (GrSum.of (twistSections_commute f M V s) t x) =
      GrSum.of (twistSections_commute f M W s) t (twistSections_res f M h t x) :=
  GrSum.map_of _ _ _ _ _ _

theorem gradedTwistSections_res_isGraded (s : ι → H.Sec) (h : W ≤ V) :
    IsGradedMap (GrSum.grading (twistSections_commute f M V s))
      (GrSum.grading (twistSections_commute f M W s)) (gradedTwistSections_res f M s h) :=
  GrSum.isGradedMap_map _ _ _ _

theorem gradedTwistSections_res_comp (s : ι → H.Sec) {U : X.Opens} (h : W ≤ V) (k : U ≤ W) :
    gradedTwistSections_res f M s k ∘ₗ gradedTwistSections_res f M s h =
      gradedTwistSections_res f M s (k.trans h) := by
  let a := gradedTwistSections_res f M s k ∘ₗ gradedTwistSections_res f M s h
  let b := gradedTwistSections_res f M s (k.trans h)
  have e : a.restrictScalars R = b.restrictScalars R :=
    GrSum.lhom_ext _ fun t x => by
      change gradedTwistSections_res f M s k
          (gradedTwistSections_res f M s h (GrSum.of (twistSections_commute f M V s) t x)) =
        gradedTwistSections_res f M s (k.trans h) (GrSum.of (twistSections_commute f M V s) t x)
      rw [gradedTwistSections_res_of, gradedTwistSections_res_of, gradedTwistSections_res_of]
      exact congrArg (GrSum.of (twistSections_commute f M U s) t)
        (sec_ext fun p => resG_resG (inf_le_inf_right _ h) (inf_le_inf_right _ k) (coord x p))
  exact LinearMap.ext fun x => LinearMap.congr_fun e x

end GlobalTheory.LineBundleSections
