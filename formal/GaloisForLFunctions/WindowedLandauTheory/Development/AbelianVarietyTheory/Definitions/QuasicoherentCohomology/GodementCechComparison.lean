import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.FiniteCechComplex
import GaloisForLFunctions.HTGeometry.SheafCechLeray
import Mathlib.Algebra.Homology.HomologySequenceLemmas

/-! Godement dimension shifting for Čech cohomology on a cover with acyclic intersections. -/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite TopologicalSpace
  HTGeometry RHTower

namespace GlobalTheory.SchemeCohomology

universe u w

variable {X : TopCat.{u}} {F G : TopCat.Sheaf AddCommGrpCat.{u} X}

private def godementMap (φ : F ⟶ G) : deningerGodementSheaf F ⟶ deningerGodementSheaf G :=
  ⟨{ app := fun _ => AddCommGrpCat.ofHom
      { toFun := fun s x => (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x.1).map φ.1 (s x)
        map_zero' := funext fun _ => map_zero _
        map_add' := fun s t => funext fun x => map_add _ (s x) (t x) }
     naturality := fun _ _ _ => rfl }⟩

private theorem godementMap_natural (φ : F ⟶ G) :
    deningerGodementι F ≫ godementMap φ = φ ≫ deningerGodementι G := by
  apply CategoryTheory.Sheaf.hom_ext
  refine NatTrans.ext (funext fun W => ?_)
  apply AddCommGrpCat.ext
  intro s
  funext x
  exact TopCat.Presheaf.stalkFunctor_map_germ_apply _ x.1 x.2 φ.1 s

/-- The map of short exact Godement sequences induced by a map of sheaves. -/
def godementSequenceMap (φ : F ⟶ G) : deningerGodementComplex F ⟶ deningerGodementComplex G where
  τ₁ := φ
  τ₂ := godementMap φ
  τ₃ := cokernel.map _ _ φ (godementMap φ) (godementMap_natural φ)
  comm₁₂ := (godementMap_natural φ).symm
  comm₂₃ := (cokernel.π_desc _ _ _).symm

variable {ι : Type u} [DecidableEq ι] [LinearOrder ι] (V : Opens X) (U : ι → Opens X)

/-- The alternating Čech complex of a sheaf on the given cover. -/
abbrev sheafCechComplex (F : TopCat.Sheaf AddCommGrpCat.{u} X) : CochainComplex AddCommGrpCat.{u} ℕ :=
  (sheafCech F V U).cochainComplex

/-- A map of sheaves acts on the Čech complex by applying it on each intersection. -/
abbrev sheafCechComplexMap (φ : F ⟶ G) : sheafCechComplex V U F ⟶ sheafCechComplex V U G :=
  (sheafCechMap φ V U).cochainMap

private theorem sheafCechComplexMap_comp {H : TopCat.Sheaf AddCommGrpCat.{u} X}
    (φ : F ⟶ G) (ψ : G ⟶ H) :
    sheafCechComplexMap V U (φ ≫ ψ) = sheafCechComplexMap V U φ ≫ sheafCechComplexMap V U ψ := by
  ext n c
  rfl

/-- Alternating Čech cochains on a fixed cover are functorial in the sheaf. -/
abbrev abelianCechFunctor (X : TopCat.{u}) (V : Opens X) {ι : Type u}
    [DecidableEq ι] [LinearOrder ι] (U : ι → Opens X) :
    TopCat.Sheaf AddCommGrpCat.{u} X ⥤ CochainComplex AddCommGrpCat.{u} ℕ where
  obj := sheafCechComplex V U
  map := sheafCechComplexMap V U
  map_id _ := by ext n c; rfl
  map_comp _ _ := sheafCechComplexMap_comp V U _ _

instance abelianCechFunctor_additive (X : TopCat.{u}) (V : Opens X) {ι : Type u}
    [DecidableEq ι] [LinearOrder ι] (U : ι → Opens X) :
    (abelianCechFunctor X V U).Additive where
  map_add := by intros; ext n c; rfl

/-- The Godement short complex on the Čech cochains of the three sheaves. -/
def godementCechSequence (F : TopCat.Sheaf AddCommGrpCat.{u} X) :
    ShortComplex (CochainComplex AddCommGrpCat.{u} ℕ) :=
  ShortComplex.mk
    (sheafCechComplexMap V U (deningerGodementComplex F).f)
    (sheafCechComplexMap V U (deningerGodementComplex F).g) (by
      ext n c
      exact Subtype.ext (funext fun a => sheafCech_comp_zero V U a (c.1 a)))

def godementCechSequenceMap (φ : F ⟶ G) :
    godementCechSequence V U F ⟶ godementCechSequence V U G where
  τ₁ := sheafCechComplexMap V U φ
  τ₂ := sheafCechComplexMap V U (godementSequenceMap φ).τ₂
  τ₃ := sheafCechComplexMap V U (godementSequenceMap φ).τ₃
  comm₁₂ := by
    change _ ≫ sheafCechComplexMap V U (deningerGodementComplex G).f =
      sheafCechComplexMap V U (deningerGodementComplex F).f ≫ _
    rw [← sheafCechComplexMap_comp, ← sheafCechComplexMap_comp]
    exact congrArg (sheafCechComplexMap V U) (godementSequenceMap φ).comm₁₂
  comm₂₃ := by
    change _ ≫ sheafCechComplexMap V U (deningerGodementComplex G).g =
      sheafCechComplexMap V U (deningerGodementComplex F).g ≫ _
    rw [← sheafCechComplexMap_comp, ← sheafCechComplexMap_comp]
    exact congrArg (sheafCechComplexMap V U) (godementSequenceMap φ).comm₂₃

variable {V U}

/-- A short exact sequence of sheaves induces a termwise short exact sequence
of Čech complexes when the kernel is acyclic on the intersections. -/
theorem coverCech_shortExact [HasExt.{w} (TopCat.Sheaf AddCommGrpCat.{u} X)]
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)} (hS : S.ShortExact)
    (h₁ : ∀ a : Finset ι, a.Nonempty → DeningerAcyclicOn.{w} S.X₁ (coverInter V U a)) :
    (S.map (abelianCechFunctor X V U)).ShortExact := by
  exact FinsetCechDatum.shortExact_cochainMap _ _
    (sheafCech_comp_zero V U)
    (fun a _ => sheafCech_injective hS a)
    (fun a _ y => ⟨fun h => sheafCech_exact hS a y h, by
      rintro ⟨x, rfl⟩
      exact sheafCech_comp_zero V U a x⟩)
    (fun a ha => deningerSections_surjective_of_acyclic hS _ (h₁ a ha))

/-- The Godement sequence is termwise short exact on an acyclic cover. -/
theorem godementCech_shortExact [HasExt.{w} (TopCat.Sheaf AddCommGrpCat.{u} X)]
    (hF : ∀ a : Finset ι, a.Nonempty → DeningerAcyclicOn.{w} F (coverInter V U a)) :
    (godementCechSequence V U F).ShortExact :=
  coverCech_shortExact (deningerGodementShortExact F) hF

theorem isZero_godementCech_homology (hcov : V ≤ ⨆ i, U i) (n : ℕ) :
    IsZero ((sheafCechComplex V U (deningerGodementSheaf F)).homology (n + 1)) :=
  (HomologicalComplex.exactAt_iff_isZero_homology _ _).1
    (FinsetCechDatum.cochainComplex_exactAt _ (godementCech_exactAt hcov (n + 1)))

variable [HasExt.{w} (TopCat.Sheaf AddCommGrpCat.{u} X)]

/-- The positive-degree Čech connecting map of the Godement sequence is an isomorphism. -/
def godementCechShift (hcov : V ≤ ⨆ i, U i)
    (hF : ∀ a : Finset ι, a.Nonempty → DeningerAcyclicOn.{w} F (coverInter V U a)) (n : ℕ) :
    (sheafCechComplex V U (deningerGodementComplex F).X₃).homology (n + 1) ≅
      (sheafCechComplex V U F).homology (n + 2) :=
  (godementCech_shortExact hF).δIso (n + 1) (n + 2) rfl
    (isZero_godementCech_homology hcov n) (isZero_godementCech_homology hcov (n + 1))

theorem godementCechShift_natural (hcov : V ≤ ⨆ i, U i)
    (hF : ∀ a : Finset ι, a.Nonempty → DeningerAcyclicOn.{w} F (coverInter V U a))
    (hG : ∀ a : Finset ι, a.Nonempty → DeningerAcyclicOn.{w} G (coverInter V U a))
    (φ : F ⟶ G) (n : ℕ) :
    (godementCechShift hcov hF n).hom ≫ HomologicalComplex.homologyMap (sheafCechComplexMap V U φ) _ =
      HomologicalComplex.homologyMap (sheafCechComplexMap V U (godementSequenceMap φ).τ₃) _ ≫
        (godementCechShift hcov hG n).hom :=
  HomologicalComplex.HomologySequence.δ_naturality (godementCechSequenceMap V U φ)
    (godementCech_shortExact hF) (godementCech_shortExact hG) (n + 1) (n + 2) rfl

/-- Dimension shifting along the flasque Godement embedding on sheaf cohomology. -/
def godementExtShift (F : TopCat.Sheaf AddCommGrpCat.{u} X) (W : Opens X) (n : ℕ) :
    deningerSheafCohomology.{w} W (deningerGodementComplex F).X₃ (n + 1) ≃+
      deningerSheafCohomology.{w} W F (n + 2) := by
  let h := deningerGodementShortExact F
  let δ := h.extClass.postcomp (deningerOpenFree W) (rfl : (n + 1) + 1 = n + 2)
  refine AddEquiv.ofBijective δ ⟨?_, ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨y, hy⟩ := Ext.covariant_sequence_exact₃ (deningerOpenFree W) h x rfl hx
    rw [← hy, godement_acyclicOn F W n y, Ext.zero_comp]
  · intro x
    exact Ext.covariant_sequence_exact₁ (deningerOpenFree W) h x
      (godement_acyclicOn F W (n + 1) _) rfl

theorem godementExtShift_natural (φ : F ⟶ G) (W : Opens X) (n : ℕ)
    (x : deningerSheafCohomology.{w} W (deningerGodementComplex F).X₃ (n + 1)) :
    godementExtShift G W n (x.comp (Ext.mk₀ (godementSequenceMap φ).τ₃) (add_zero _)) =
      (godementExtShift F W n x).comp (Ext.mk₀ φ) (add_zero _) := by
  change (x.comp (Ext.mk₀ (godementSequenceMap φ).τ₃) (add_zero _)).comp
    (deningerGodementShortExact G).extClass rfl =
    (x.comp (deningerGodementShortExact F).extClass rfl).comp (Ext.mk₀ φ) (add_zero _)
  rw [Ext.comp_assoc_of_second_deg_zero, Ext.comp_assoc_of_third_deg_zero,
    ← (deningerGodementShortExact F).extClass_naturality (deningerGodementShortExact G)
      (godementSequenceMap φ)]
  rfl

end GlobalTheory.SchemeCohomology
