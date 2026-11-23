import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.CechDifferentialComplex
import Mathlib.Algebra.Homology.ShortComplex.Ab

/-! Categorical homology agrees with the cycle quotient in a graded ambient module. -/

noncomputable section

open CategoryTheory

namespace GlobalTheory.CechDR.Cx

variable {k M : Type} [Field k] [AddCommGroup M] [Module k M]
  {K : Cx k M} {n : ℤ} {S : ShortComplex AddCommGrpCat.{0}}
  (e : S.X₂ ≃+ K.C n) (hg : ∀ x, S.g x = 0 ↔ K.D (e x) = 0)
  (hf : ∀ x : K.C n, (x : M) ∈ K.B n ↔ ∃ y, e (S.f y) = x)

private def toGradedCycles : S.cycles →+ K.Z n where
  toFun z := ⟨e (S.iCycles z), (e (S.iCycles z)).2,
    LinearMap.mem_ker.mpr ((hg _).mp (ConcreteCategory.congr_hom S.iCycles_g z))⟩
  map_zero' := by
    apply Subtype.ext
    change (e (S.iCycles 0) : M) = 0
    rw [map_zero, map_zero]
    rfl
  map_add' z z' := by
    apply Subtype.ext
    change (e (S.iCycles (z + z')) : M) = (e (S.iCycles z) : M) + (e (S.iCycles z') : M)
    rw [map_add, map_add]
    rfl

private theorem toGradedCycles_bijective : Function.Bijective (toGradedCycles e hg) := by
  constructor
  · intro z z' he
    apply (AddCommGrpCat.mono_iff_injective S.iCycles).mp inferInstance
    apply e.injective
    exact Subtype.ext (congrArg (fun a : K.Z n => a.val) he)
  · intro z
    let x := e.symm ⟨z.1, z.2.1⟩
    have hx : e x = ⟨z.1, z.2.1⟩ := e.apply_symm_apply _
    have hgx : S.g x = 0 := (hg _).mpr (by rw [hx]; exact z.2.2)
    refine ⟨S.abCyclesIso.inv ⟨x, hgx⟩, Subtype.ext ?_⟩
    change (e (S.iCycles (S.abCyclesIso.inv ⟨x, hgx⟩)) : M) = z.val
    rw [S.abCyclesIso_inv_apply_iCycles]
    exact congrArg Subtype.val hx

private abbrev quotientHom : S.cycles ⟶ AddCommGrpCat.of (K.H n) :=
  AddCommGrpCat.ofHom (((K.B n).submoduleOf (K.Z n)).mkQ.toAddMonoidHom.comp
    (toGradedCycles e hg))

include hf in
private theorem quotientHom_exact : Function.Exact S.toCycles (quotientHom e hg) := by
  intro z
  change Submodule.Quotient.mk (toGradedCycles e hg z) = 0 ↔ _
  rw [Submodule.Quotient.mk_eq_zero]
  change ((e (S.iCycles z) : K.C n) : M) ∈ K.B n ↔ _
  rw [hf]
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨y, (AddCommGrpCat.mono_iff_injective S.iCycles).mp inferInstance ?_⟩
    exact (ConcreteCategory.congr_hom S.toCycles_i y).trans (e.injective hy)
  · rintro ⟨y, rfl⟩
    exact ⟨y, congrArg e (ConcreteCategory.congr_hom S.toCycles_i y).symm⟩

private def homologyComparison : S.homology ⟶ AddCommGrpCat.of (K.H n) :=
  S.descHomology (quotientHom e hg) (by
    apply AddCommGrpCat.ext
    intro y
    exact (quotientHom_exact e hg hf _).mpr ⟨y, rfl⟩)

private theorem homologyComparison_bijective :
    Function.Bijective (homologyComparison e hg hf) := by
  have hπ : ∀ z, homologyComparison e hg hf (S.homologyπ z) = quotientHom e hg z :=
    fun z => ConcreteCategory.congr_hom (S.π_descHomology _ _) z
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨z, rfl⟩ := (AddCommGrpCat.epi_iff_surjective S.homologyπ).mp inferInstance x
    rw [hπ] at hx
    obtain ⟨y, rfl⟩ := (quotientHom_exact e hg hf _).mp hx
    exact ConcreteCategory.congr_hom S.toCycles_comp_homologyπ y
  · intro x
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    obtain ⟨y, rfl⟩ := (toGradedCycles_bijective e hg).2 z
    exact ⟨S.homologyπ y, hπ y⟩

/-- Identify homology by identifying the middle term, cycles and boundaries. -/
def homologyAddEquiv : S.homology ≃+ K.H n :=
  AddEquiv.ofBijective (homologyComparison e hg hf).hom (homologyComparison_bijective e hg hf)

theorem homologyAddEquiv_π_val (z : S.cycles) (a : K.Z n)
    (ha : a.val = (e (S.iCycles z) : M)) :
    homologyAddEquiv e hg hf (S.homologyπ z) = Submodule.Quotient.mk a := by
  change homologyComparison e hg hf (S.homologyπ z) = _
  rw [show homologyComparison e hg hf (S.homologyπ z) = quotientHom e hg z from
    ConcreteCategory.congr_hom (S.π_descHomology _ _) z]
  exact congrArg (fun a : K.Z n => (Submodule.Quotient.mk a : K.H n)) (Subtype.ext ha.symm)

end GlobalTheory.CechDR.Cx
