import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.CohomologyPullback
import GaloisForLFunctions.RHTower.Deninger.DeningerFlasqueAcyclic
import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
import Mathlib.CategoryTheory.Sites.EpiMono

/-! Acyclicity over the preimages of a basis gives the direct-image comparison isomorphism. -/

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite TopologicalSpace

noncomputable section

namespace GlobalTheory.SchemeCohomology

private abbrev AbSheaf (X : TopCat.{0}) := TopCat.Sheaf AddCommGrpCat.{0} X

local instance directImageSheafHasExt (X : TopCat.{0}) : HasExt.{0} (AbSheaf X) :=
  hasExt_of_enoughInjectives _

variable {X Y : TopCat.{0}} (f : Y ⟶ X)

private abbrev push := TopCat.Sheaf.pushforward AddCommGrpCat.{0} f

local instance : (push f).Additive where
  map_add := rfl

local instance : (push f).PreservesInjectiveObjects := by
  let K := TopCat.Sheaf.pullback AddCommGrpCat.{0} f
  haveI : PreservesFiniteLimits K := RHTower.deningerSheafPullback_preservesFiniteLimits f
  exact Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{0} f)

/-- All higher cohomology vanishes over preimages of opens in the specified family. -/
def AcyclicOnPreimages (B : Set (Opens X)) (G : AbSheaf Y) : Prop :=
  ∀ U ∈ B, ∀ q : ℕ, ∀ x : Ext (openFree ((Opens.map f).obj U)) G (q + 1), x = 0

variable {B : Set (Opens X)}

private theorem push_epi_of_acyclic (hB : Opens.IsBasis B) {S : ShortComplex (AbSheaf Y)}
    (hS : S.ShortExact) (hG : AcyclicOnPreimages f B S.X₁) : Epi ((push f).map S.g) := by
  apply (Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat ((push f).map S.g)).mp
  constructor
  intro U t p hp
  obtain ⟨V, hV, hpV, hVU⟩ := Opens.isBasis_iff_nbhd.1 hB hp
  let i : V ⟶ U := homOfLE hVU
  let W := (Opens.map f).obj V
  let t' := S.X₃.obj.map ((Opens.map f).map i).op t
  let a := (openFreeHomEquiv W S.X₃).symm t'
  have hzero : (Ext.mk₀ a).comp hS.extClass rfl = 0 := hG V hV 0 _
  obtain ⟨z, hz⟩ := Ext.covariant_sequence_exact₃ (openFree W) hS (Ext.mk₀ a) rfl hzero
  let b := Ext.homEquiv₀ z
  have hb : b ≫ S.g = a := by
    apply (Ext.mk₀_bijective _ _).injective
    rw [← Ext.mk₀_comp_mk₀]
    exact (congrArg (fun w => w.comp (Ext.mk₀ S.g) (add_zero 0))
      (Ext.mk₀_homEquiv₀_apply z)).trans hz
  refine ⟨V, i, ⟨openFreeHomEquiv W S.X₂ b, ?_⟩, hpV⟩
  exact (openFreeHomEquiv_natural W b S.g).symm.trans
    ((congrArg (openFreeHomEquiv W S.X₃) hb).trans (Equiv.apply_symm_apply _ _))

private theorem push_shortExact_of_acyclic (hB : Opens.IsBasis B) {S : ShortComplex (AbSheaf Y)}
    (hS : S.ShortExact) (hG : AcyclicOnPreimages f B S.X₁) :
    (S.map (push f)).ShortExact := by
  letI : Mono S.f := hS.mono_f
  exact .mk' (hS.exact.map_of_mono_of_preservesKernel _ inferInstance inferInstance)
    (Functor.map_mono (push f) S.f) (push_epi_of_acyclic f hB hS hG)

private theorem quotient_acyclic {S : ShortComplex (AbSheaf Y)} (hS : S.ShortExact)
    [Injective S.X₂] (hG : AcyclicOnPreimages f B S.X₁) : AcyclicOnPreimages f B S.X₃ := by
  intro U hU q x
  obtain ⟨y, hy⟩ := Ext.covariant_sequence_exact₃ (openFree ((Opens.map f).obj U)) hS x
    rfl (hG U hU (q + 1) _)
  rw [Ext.eq_zero_of_injective y, Ext.zero_comp] at hy
  exact hy.symm

/-- Cohomology of the direct image agrees with cohomology on preimage opens
if the sheaf is acyclic over the preimages of a basis. -/
theorem abelianPushforwardComparison_bijective (hB : Opens.IsBasis B)
    (G : AbSheaf Y) (hG : AcyclicOnPreimages f B G) (U : Opens X) (n : ℕ) :
    Function.Bijective (abelianPushforwardComparison f G U n) := by
  induction n generalizing G with
  | zero => exact abelianPushforwardComparison_bijective_zero f G U
  | succ n ih =>
    let V := (Opens.map f).obj U
    let S := RHTower.deningerInjectiveEmbedding G
    have hS : S.ShortExact := RHTower.deningerInjectiveEmbedding_shortExact G
    haveI : Injective S.X₂ := CategoryTheory.Injective.injective_under G
    haveI : Injective (S.map (push f)).X₂ :=
      inferInstanceAs (Injective ((push f).obj S.X₂))
    have hT := push_shortExact_of_acyclic f hB hS hG
    have hquot := ih S.X₃ (quotient_acyclic f hS hG)
    have hmiddle : Function.Surjective (abelianPushforwardComparison f S.X₂ U n) := by
      cases n with
      | zero => exact (abelianPushforwardComparison_bijective_zero f S.X₂ U).surjective
      | succ q =>
        intro y
        exact ⟨0, (map_zero _).trans (Ext.eq_zero_of_injective y).symm⟩
    refine ⟨(injective_iff_map_eq_zero _).2 ?_, ?_⟩
    · intro x hx
      obtain ⟨x₃, hx₃⟩ := Ext.covariant_sequence_exact₁ (openFree U) hT x
        (Ext.eq_zero_of_injective _) rfl
      have hδ := abelianPushforwardComparison_boundary f hS hT U n x₃
      have hzero := hδ.symm.trans
        ((congrArg (abelianPushforwardComparison f S.X₁ U (n + 1)) hx₃).trans hx)
      obtain ⟨y₂, hy₂⟩ := Ext.covariant_sequence_exact₃ (openFree V) hS
        (abelianPushforwardComparison f S.X₃ U n x₃) rfl hzero
      obtain ⟨x₂, hx₂⟩ := hmiddle y₂
      have hmap := abelianPushforwardComparison_map f S.g U n x₂
      let g := Ext.mk₀ (S.map (push f)).g
      have h₃ : x₂.comp g (add_zero n) = x₃ := hquot.injective (hmap.trans
        ((congrArg (fun y => y.comp (Ext.mk₀ S.g) (add_zero n)) hx₂).trans hy₂))
      calc
        x = x₃.comp hT.extClass rfl := hx₃.symm
        _ = (x₂.comp g (add_zero n)).comp hT.extClass rfl :=
          congrArg (fun y => y.comp hT.extClass rfl) h₃.symm
        _ = x₂.comp (g.comp hT.extClass (zero_add 1)) rfl :=
          Ext.comp_assoc_of_second_deg_zero _ _ _ rfl
        _ = 0 := (congrArg (fun y => x₂.comp y rfl) hT.comp_extClass).trans
          (Ext.comp_zero x₂ (S.map (push f)).X₁ 1 (n + 1) rfl)
    · intro y
      obtain ⟨y₃, hy₃⟩ := Ext.covariant_sequence_exact₁ (openFree V) hS y
        (Ext.eq_zero_of_injective _) rfl
      obtain ⟨x₃, hx₃⟩ := hquot.surjective y₃
      refine ⟨x₃.comp hT.extClass rfl, (abelianPushforwardComparison_boundary f hS hT U n x₃).trans ?_⟩
      rw [hx₃, hy₃]

end GlobalTheory.SchemeCohomology
