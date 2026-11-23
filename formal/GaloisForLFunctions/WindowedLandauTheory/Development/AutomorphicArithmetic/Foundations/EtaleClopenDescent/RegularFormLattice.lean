import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.GenericChartForms
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.NormalHeightOneLattice

/-! Regular differential forms on a smooth affine chart are detected at
its height-one localizations. -/

noncomputable section

open GlobalTheory.CechDR GlobalTheory.SchemeCohomology
open scoped nonZeroDivisors GlobalTheory.CechDR GlobalTheory.SchemeCohomology

namespace GlobalTheory.PD

private theorem exteriorPower_projective {A M : Type*} [CommRing A]
    [AddCommGroup M] [Module A M] [Module.Projective A M] (p : ℕ) :
    Module.Projective A (⋀[A]^p M) := by
  obtain ⟨s, hs⟩ := Module.projective_def'.mp (inferInstance : Module.Projective A M)
  exact Module.Projective.of_split (exteriorPower.map p s)
    (exteriorPower.map p (Finsupp.linearCombination A id)) (by
      rw [← exteriorPower.map_comp, hs, exteriorPower.map_id])

variable {k E : Type} [Field k] [Field E] [Algebra k E]
  (B : Subalgebra k E) [IsFractionRing B E] [Algebra.Smooth k B]
  [IsNoetherianRing B] [IsIntegrallyClosed B]

/-- A rational form regular at every height-one point is regular on the
whole smooth chart. -/
theorem mem_omB_of_forall_height_one (p : ℕ) (ω : ExteriorDifferentials k E p)
    (h : ∀ (Q : Ideal B) [Q.IsPrime], Q.height = 1 →
      ∃ r : B, r ∉ Q ∧ (r : E) • (ω : DR k E) ∈ omB k E B p) :
    (ω : DR k E) ∈ omB k E B p := by
  letI : Module B (ExteriorDifferentials k E p) := exteriorPowerModule p
  letI : Module k (ExteriorDifferentials k B p) := exteriorPowerModule p
  let f : ExteriorDifferentials k B p →ₗ[B] ExteriorDifferentials k E p :=
    algebraFormPullback k B E p
  letI : Algebra.FormallyEtale B E := .of_isLocalization B⁰
  letI : IsLocalizedModule B⁰ f := (isLocalizedModule_iff_isBaseChange B⁰ E f).mpr
    (algebraFormPullback_isBaseChange k B E p)
  letI : Module.Projective B (ExteriorDifferentials k B p) := exteriorPower_projective p
  letI : Module.IsTorsionFree B (ExteriorDifferentials k E p) :=
    .trans_faithfulSMul B E _
  have hf (v : ExteriorDifferentials k B p) :
      f v = ExteriorDifferentials.map B.val p v := algebraFormPullback_eq_map k B E B.val rfl p v
  have hinj : Function.Injective f := by
    intro v w e
    exact exteriorDifferentials_map_fraction_injective B.val rfl p ((hf v).symm.trans (e.trans (hf w)))
  obtain ⟨⟨v, r⟩, hr⟩ := IsLocalizedModule.surj B⁰ f ω
  have hrω : (r : B) • ω ∈ LinearMap.range f := ⟨v, hr.symm⟩
  have hz : ω ∈ LinearMap.range f := mem_range_of_forall_height_one_of_projective f hinj
    (mem_nonZeroDivisors_iff_ne_zero.mp r.property) hrω (by
      intro Q _ hQ
      obtain ⟨s, hs, hω⟩ := h Q hQ
      obtain ⟨u, hu⟩ := LinearMap.mem_range.mp ((range_genericForm k E B p).ge hω)
      refine ⟨s, hs, u, Subtype.ext ?_⟩
      change (f u : DR k E) = (s : E) • (ω : DR k E)
      exact (congrArg Subtype.val (hf u)).trans hu)
  obtain ⟨w, hw⟩ := LinearMap.mem_range.mp hz
  rw [← range_genericForm]
  exact ⟨w, congrArg Subtype.val ((hf w).symm.trans hw)⟩

end GlobalTheory.PD
