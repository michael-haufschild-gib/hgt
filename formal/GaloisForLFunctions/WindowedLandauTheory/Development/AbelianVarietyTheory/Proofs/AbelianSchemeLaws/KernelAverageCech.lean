import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.KernelAverageLineBundle
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.LineBundleCechBaseChange
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.LinearCechMaps

/-! The normalized trace on sections splits the pullback map of Čech complexes. -/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace HTGeometry
open GlobalTheory.LineBundleSections GlobalTheory.SchemeCohomology
open ReciprocityTheory.ChartRestriction.G.Semi

namespace GlobalTheory.FlatDescent

/-- A cover computes an exact degree whenever its pullback does. The trace
and pullback are inverse on the downstairs complex. -/
theorem exactAt_cech_of_pull_average {R : Type} [CommRing R] {Y : Scheme.{0}}
    (f : Y ⟶ Spec (.of R)) {q : Y ⟶ Y} (hq : q ≫ f = f)
    {G : Type} [Group G] [Fintype G] {τ : G → (Y ⟶ Y)}
    (hτ : ∀ g, τ g ≫ q = q) (hmul : ∀ a b, τ a ≫ τ b = τ (a * b))
    (hD : Descends q τ) (u : Γ(Y, ⊤)ˣ) (hu : u.val = (Fintype.card G : Γ(Y, ⊤)))
    (L : LB Y) {ι : Type} [LinearOrder ι] (U : ι → Y.Opens) (n : ℕ)
    (hvan : (cech f (toMod (L.pull q)) (fun i => q ⁻¹ᵁ U i)).ExactAt n) :
    (cech f (toMod L) U).ExactAt n := by
  let F := toMod L
  let H := toMod (L.pull q)
  let V (i : ι) := q ⁻¹ᵁ U i
  let W (s : Finset ι) := coverInter ⊤ U s
  let T (s : Finset ι) := coverInter ⊤ V s
  let K := sectionDatum F U
  let K' := sectionDatum H V
  letI (s : Finset ι) := sectionDatumModule f F U s
  letI (s : Finset ι) := sectionDatumModule f H V s
  have he (s : Finset ι) : T s = q ⁻¹ᵁ W s := coverInter_pull (π := q) U s
  letI : Algebra R R := Algebra.id R
  have hb : q ≫ f = f ≫ Spec.map (CommRingCat.ofHom (algebraMap R R)) := by
    change q ≫ f = f ≫ Spec.map (𝟙 (CommRingCat.of R))
    rw [hq, Spec.map_id, Category.comp_id]
  let P := ChartPull.pull L q
  let α : K.Hom K' :=
    { app := fun s => pullSection P (he s).le
      comm := fun i x => (pullSection_restrict P (he _).le (he _).le
        (coverInter_anti i) (coverInter_anti i) x).symm }
  let restr (s : Finset ι) : Γ(H, T s) →+ Γ(H, q ⁻¹ᵁ W s) :=
    (H.presheaf.map (homOfLE (he s).ge).op).hom
  let β : K'.Hom K :=
    { app := fun s => (averageLineBundle hτ hmul hD u).comp (restr s)
      comm := fun {s t} i x => by
        let j : W t ≤ W s := coverInter_anti i
        let j' : T t ≤ T s := coverInter_anti i
        let y : Γ(H, T s) := x
        change (F.presheaf.map (homOfLE j).op) (averageLineBundle hτ hmul hD u (restr s y)) =
          averageLineBundle hτ hmul hD u (restr t (H.presheaf.map (homOfLE j').op y))
        rw [averageLineBundle_res hτ hmul hD u j]
        apply congrArg (averageLineBundle hτ hmul hD u)
        change (H.presheaf.map (homOfLE (q.preimage_mono j)).op)
          (H.presheaf.map (homOfLE (he s).ge).op y) =
          (H.presheaf.map (homOfLE (he t).ge).op)
            (H.presheaf.map (homOfLE j').op y)
        rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← Functor.map_comp,
          ← Functor.map_comp]
        rfl }
  have hα (s : Finset ι) (r : R) (x : K.obj s) : α.app s (r • x) = r • α.app s x := by
    letI := sectionAlgebra f (W s)
    letI := sectionAlgebra f (T s)
    let y : Γ(F, W s) := x
    change pullSection P (he s).le (algebraMap R Γ(Y, W s) r • y) =
      algebraMap R Γ(Y, T s) r • pullSection P (he s).le y
    rw [pullSection_smul, appLE_base_algebraMap hb] <;> rfl
  have hβ (s : Finset ι) (r : R) (x : K'.obj s) : β.app s (r • x) = r • β.app s x := by
    letI := sectionAlgebra f (W s)
    letI := sectionAlgebra f (T s)
    letI := sectionAlgebra f (q ⁻¹ᵁ W s)
    let y : Γ(H, T s) := x
    change averageLineBundle hτ hmul hD u
      (H.presheaf.map (homOfLE (he s).ge).op (algebraMap R Γ(Y, T s) r • y)) =
      algebraMap R Γ(Y, W s) r • averageLineBundle hτ hmul hD u (restr s y)
    rw [H.map_smul]
    have h₁ := (sectionRes f (homOfLE (he s).ge)).commutes r
    have h₂ := appLE_base_algebraMap hb (U := W s) (V := q ⁻¹ᵁ W s) le_rfl r
    rw [← Scheme.Hom.app_eq_appLE] at h₂
    change q.app (W s) (algebraMap R Γ(Y, W s) r) = algebraMap R Γ(Y, q ⁻¹ᵁ W s) r at h₂
    exact (congrArg (fun b : Γ(Y, q ⁻¹ᵁ W s) => averageLineBundle hτ hmul hD u (b • restr s y))
      (h₁.trans h₂.symm)).trans (averageLineBundle_smul hτ hmul hD u _ _)
  let C := cech f F U
  let C' := cech f H V
  let a : C ⟶ C' := FinsetCechDatum.linearCochainMap (res_base_smul f F U) (res_base_smul f H V) α hα
  let b : C' ⟶ C := FinsetCechDatum.linearCochainMap (res_base_smul f H V) (res_base_smul f F U) β hβ
  have hret : a ≫ b = 𝟙 C := by
    apply HomologicalComplex.Hom.ext
    funext d
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    funext s
    let y : Γ(F, W s) := x.1 s
    change averageLineBundle hτ hmul hD u (restr s (pullSection P (he s).le y)) = y
    have h := pullSection_restrict P (he s).le (le_rfl : q ⁻¹ᵁ W s ≤ q ⁻¹ᵁ W s)
      (le_rfl : W s ≤ W s) (he s).ge y
    have hi : F.presheaf.map (homOfLE (le_rfl : W s ≤ W s)).op y = y :=
      ConcreteCategory.congr_hom (F.presheaf.map_id (op (W s))) y
    have hr := h.symm.trans (congrArg (pullSection P
      (le_rfl : q ⁻¹ᵁ W s ≤ q ⁻¹ᵁ W s)) hi)
    exact (congrArg (averageLineBundle hτ hmul hD u) hr).trans
      (averageLineBundle_pull hτ hmul hD u hu y)
  apply (C.exactAt_iff_isZero_homology n).mpr
  apply (IsZero.iff_id_eq_zero _).mpr
  have e := congrArg (fun m : C ⟶ C => HomologicalComplex.homologyMap m n) hret
  rw [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_id] at e
  rw [hvan.isZero_homology.eq_of_tgt (HomologicalComplex.homologyMap a n) 0, zero_comp] at e
  exact e.symm

end GlobalTheory.FlatDescent
