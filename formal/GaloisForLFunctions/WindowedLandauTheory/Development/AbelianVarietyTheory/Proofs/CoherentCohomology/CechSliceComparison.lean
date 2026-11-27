import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.CechSupport
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.FlatLineBundleCech
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.JoinedCechExact
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.LineBundleSectionScalarChange
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.ScalarCechGrading
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.AffineCoverCechExact
import Mathlib.Order.Interval.Set.OrdConnected

/-! A slice of the Čech datum of a joined cover is a Čech datum on one open
intersection. When the intersection and its refinements are affine, the
augmented slice is exact. -/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace HTGeometry RHTower
open GlobalTheory.SchemeCohomology

namespace GlobalTheory.LineBundleSections

variable {K : Type} [Field K] {X : Scheme.{0}}
  (f : X ⟶ Spec (.of K)) (F : X.Modules)
  {ι κ : Type} [LinearOrder ι] [LinearOrder κ]
  (U : ι → X.Opens) (W : X.Opens) (V : κ → X.Opens)
  (m : Finset κ → Finset ι) (hm : Monotone m) (P : Set (Finset ι)) (hP : P.OrdConnected)

private abbrev localDatum := sheafCech ((SheafOfModules.toSheaf X.ringCatSheaf).obj F) W V

private abbrev localModule (s : Finset κ) : Module K ((localDatum F W V).obj s) :=
  sectionBaseModule f F (coverInter W V s)

/-- Equality of the indexed opens gives an isomorphism of the supported
section modules, compatible with every restriction. -/
theorem exists_slice_hom
    (e : ∀ s, coverInter (⊤ : X.Opens) U (m s) = coverInter W V s) :
    letI (s : Finset ι) := sectionDatumModule f F U s
    letI (s : Finset κ) := localModule f F W V s
    let B := (localDatum F W V).truncate (R := K) (m ⁻¹' P) (hP.preimage_mono hm)
    let T := ((sectionDatum F U).truncate (R := K) P hP).comap m hm
    ∃ φ : B.Hom T, (∀ s, Function.Bijective (φ.app s)) ∧
      ∀ s (r : K) (x : B.obj s), φ.app s (r • x) = r • φ.app s x := by
  classical
  letI (s : Finset ι) := sectionDatumModule f F U s
  letI (s : Finset κ) := localModule f F W V s
  let D := sectionDatum F U
  let A := localDatum F W V
  let G := (SheafOfModules.toSheaf X.ringCatSheaf).obj F
  let Q := m ⁻¹' P
  let hQ : Q.OrdConnected := hP.preimage_mono hm
  let B := A.truncate (R := K) Q hQ
  let T := (D.truncate (R := K) P hP).comap m hm
  let φ : B.Hom T :=
    { app s :=
        { toFun := fun x => ⟨deningerRes G (e s).le x.1, fun hs => by
            rw [x.2 hs]
            exact map_zero (ConcreteCategory.hom (G.1.map (homOfLE (e s).le).op))⟩
          map_zero' := Subtype.ext (map_zero (ConcreteCategory.hom (G.1.map (homOfLE (e s).le).op)))
          map_add' _ _ := Subtype.ext (map_add (ConcreteCategory.hom (G.1.map (homOfLE (e s).le).op)) _ _) }
      comm := fun {s t} h x => by
        refine Subtype.ext ?_
        change ((D.truncate (R := K) P hP).res (hm h) _).1 =
          deningerRes G (e t).le ((A.truncate (R := K) Q hQ).res h x).1
        rw [D.truncate_res_value, A.truncate_res_value]
        by_cases ht : m t ∈ P
        · rw [if_pos ht, if_pos (show t ∈ Q from ht)]
          change deningerRes G (coverInter_anti (hm h)) (deningerRes G (e s).le x.1) =
            deningerRes G (e t).le (deningerRes G (coverInter_anti h) x.1)
          exact (deningerRes_res (e s).le (coverInter_anti (hm h)) x.1).trans
            (deningerRes_res (coverInter_anti h) (e t).le x.1).symm
        · rw [if_neg ht, if_neg (show t ∉ Q from ht)]
          exact (map_zero (ConcreteCategory.hom (G.1.map (homOfLE (e t).le).op))).symm }
  refine ⟨φ, fun s => ⟨?_, ?_⟩, ?_⟩
  · intro x y h
    have he : deningerRes G (e s).le x.1 = deningerRes G (e s).le y.1 := congrArg Subtype.val h
    have he' := congrArg (deningerRes G (e s).ge) he
    rw [deningerRes_res, deningerRes_res, deningerRes_self, deningerRes_self] at he'
    exact Subtype.ext he'
  · intro y
    refine ⟨⟨deningerRes G (e s).ge y.1, fun hs => ?_⟩, Subtype.ext ?_⟩
    · rw [y.2 hs]
      exact map_zero (ConcreteCategory.hom (G.1.map (homOfLE (e s).ge).op))
    · exact (deningerRes_res (e s).ge (e s).le y.1).trans (deningerRes_self _ _)
  · intro s r x
    let A₀ := coverInter W V s
    let B₀ := coverInter (⊤ : X.Opens) U (m s)
    let i : B₀ ⟶ A₀ := homOfLE (e s).le
    letI := sectionAlgebra f A₀
    letI := sectionAlgebra f B₀
    let y : Γ(F, A₀) := x.1
    apply Subtype.ext
    change F.presheaf.map i.op (algebraMap K Γ(X, A₀) r • y) =
      algebraMap K Γ(X, B₀) r • F.presheaf.map i.op y
    rw [F.map_smul]
    exact congrArg (· • F.presheaf.map i.op y) ((sectionRes f i).commutes r)

variable [HasExt.{0} (TopCat.Sheaf AddCommGrpCat.{0} X)] [Fintype κ] [F.IsQuasicoherent]

/-- An affine augmented slice has primitives for all total cocycles. -/
theorem exists_primitive_of_affine_slice
    (e : ∀ s, coverInter (⊤ : X.Opens) U (m s) = coverInter W V s)
    (hs : ∀ s, m s ∈ P) (hW : IsAffineOpen W) (hcov : W ≤ ⨆ j, V j)
    (haff : ∀ s : Finset κ, s.Nonempty → IsAffineOpen (coverInter W V s)) :
    letI (s : Finset ι) := sectionDatumModule f F U s
    let T := ((sectionDatum F U).truncate (R := K) P hP).comap m hm
    ∀ x : T.Cochain, T.d x = 0 → ∃ y, T.d y = x := by
  letI (s : Finset ι) := sectionDatumModule f F U s
  letI (s : Finset κ) := localModule f F W V s
  let A := localDatum F W V
  let G := (SheafOfModules.toSheaf X.ringCatSheaf).obj F
  let Q := m ⁻¹' P
  let hQ : Q.OrdConnected := hP.preimage_mono hm
  have hA := A.exists_primitive_of_augmented_exact (K := K) (sheafCech_exactBot G hcov)
    (quasicoherent_cech_exactAt_of_isAffine F hW hcov haff)
  have hB := FinsetCechDatum.exists_primitive_of_bijective_coefficients
    (A.toTruncateOfAll (R := K) Q hQ hs) (A.toTruncateOfAll_bijective Q hQ hs) hA
  obtain ⟨φ, hφ, -⟩ := exists_slice_hom f F U W V m hm P hP e
  exact FinsetCechDatum.exists_primitive_of_bijective_coefficients φ hφ hB

end GlobalTheory.LineBundleSections
