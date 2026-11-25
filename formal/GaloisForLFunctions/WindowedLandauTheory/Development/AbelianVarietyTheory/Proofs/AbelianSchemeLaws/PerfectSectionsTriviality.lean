import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.GlobalLineBundleCoordinates
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.PerfectLineBundleSections

/-! The matrix model detects triviality by nonvanishing of its kernel sections. -/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.SchemeCohomology

namespace GlobalTheory.LineBundleSections.PerfectSections

variable {R S : Type} [CommRing R] [CommRing S] {X Y : Scheme.{0}} {L : LB X}
  {f : X ⟶ Spec (CommRingCat.of R)} (P : PerfectSections f L)
  {π : Y ⟶ X} {g : Y ⟶ Spec (CommRingCat.of S)}

/-- The local coordinate of a vector in the matrix model. -/
def value (π : Y ⟶ X) (g : Y ⟶ Spec (CommRingCat.of S))
    (v : Fin P.a → S) (i : P.I) : Γ(Y, π ⁻¹ᵁ P.W i) :=
  letI := sectionAlgebra g (π ⁻¹ᵁ P.W i)
  ∑ k, algebraMap S Γ(Y, π ⁻¹ᵁ P.W i) (v k) * π.app (P.W i) (P.coeff k i)

def valueBase (v : Fin P.a → R) (i : P.I) : Γ(X, P.W i) :=
  letI := sectionAlgebra f (P.W i)
  ∑ k, algebraMap R Γ(X, P.W i) (v k) * P.coeff k i

theorem value_smul (c : S) (v : Fin P.a → S) (i : P.I) :
    letI := sectionAlgebra g (π ⁻¹ᵁ P.W i)
    P.value π g (c • v) i = algebraMap S Γ(Y, π ⁻¹ᵁ P.W i) c * P.value π g v i := by
  letI := sectionAlgebra g (π ⁻¹ᵁ P.W i)
  simp only [value, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum, mul_assoc]

theorem value_comp {α : R →+* S} (H : IsPullback π g f (Spec.map (CommRingCat.ofHom α)))
    (v : Fin P.a → R) (i : P.I) :
    P.value π g (α ∘ v) i = π.app (P.W i) (P.valueBase v i) := by
  letI : Algebra R S := α.toAlgebra
  letI := sectionAlgebra f (P.W i)
  letI := sectionAlgebra g (π ⁻¹ᵁ P.W i)
  have e (x : R) : π.app (P.W i) (algebraMap R Γ(X, P.W i) x) =
      algebraMap S Γ(Y, π ⁻¹ᵁ P.W i) (α x) := by
    rw [Scheme.Hom.app_eq_appLE]
    exact appLE_base_algebraMap H.w le_rfl x
  simp only [value, valueBase, map_sum, map_mul, e, Function.comp_apply]

private theorem chartLe (i : P.I) :
    π ⁻¹ᵁ P.W i ≤ (L.pull π).U (fun _ => P.chart i) :=
  (π.preimage_mono (P.le_chart i)).trans (pull_chart L π (P.chart i)).ge

private theorem exists_coordinate_comparison (α : R →+* S)
    (H : IsPullback π g f (Spec.map (CommRingCat.ofHom α))) :
    ∃ E : {v : Fin P.a → S // (P.d₀.map α).mulVec v = 0} ≃ (L.pull π).Sec,
      ∀ v i, resG Y (P.chartLe (π := π) i) ((E v).f (fun _ => P.chart i)) =
        P.value π g v.1 i := by
  obtain ⟨E, hE⟩ := (P.compare S α Y π g H).1
  refine ⟨E.trans globalCoordinates, fun v i => ?_⟩
  change resG Y (P.chartLe i) ((globalCoordinates (E v)).f (fun _ => P.chart i)) = _
  rw [globalCoordinates_apply, resG_resG]
  exact hE v i

theorem trivial_of_values {α : R →+* S} (H : IsPullback π g f (Spec.map (CommRingCat.ofHom α)))
    {v : Fin P.a → S} (hv : (P.d₀.map α).mulVec v = 0)
    (hu : ∀ y : Y, ∃ i : P.I, y ∈ Y.basicOpen (P.value π g v i)) :
    ∃ t : (L.pull π).Gen, t.IsGen := by
  obtain ⟨E, hE⟩ := P.exists_coordinate_comparison α H
  refine exists_gen_of_nonvanishing_coordinates (globalCoordinates.symm (E ⟨v, hv⟩))
    (fun i => π ⁻¹ᵁ P.W i) (fun i _ => P.chart i) (P.chartLe (π := π)) fun y => ?_
  obtain ⟨i, hi⟩ := hu y
  refine ⟨i, ?_⟩
  rwa [Equiv.apply_symm_apply, hE ⟨v, hv⟩ i]

/-- When the pullback is trivial, a kernel vector gives a generator on every chart.
If base scalars exhaust the global functions, it spans the kernel. -/
theorem values_of_trivial (hL : L.IsLB) {α : R →+* S}
    (H : IsPullback π g f (Spec.map (CommRingCat.ofHom α)))
    (ht : ∃ t : (L.pull π).Gen, t.IsGen) :
    ∃ v : Fin P.a → S, (P.d₀.map α).mulVec v = 0 ∧
      (∀ i, IsUnit (P.value π g v i)) ∧
      (Function.Surjective g.appTop → ∀ w, (P.d₀.map α).mulVec w = 0 → ∃ c : S, w = c • v) := by
  obtain ⟨E, hE⟩ := P.exists_coordinate_comparison α H
  obtain ⟨t, ht⟩ := ht
  let σ : (L.pull π).Sec := ⟨fun i => (t.s i).val, fun i j => congrArg Units.val (ht i j)⟩
  obtain ⟨v, hv⟩ := E.surjective σ
  have hgen (i : P.I) : P.value π g v.1 i =
      resG Y (P.chartLe i) (t.s (fun _ => P.chart i)).val := by
    rw [← hE v i, hv]
  refine ⟨v.1, v.2, fun i => hgen i ▸ (Units.isUnit _).map (resG Y (P.chartLe i)), ?_⟩
  intro hsurj w hw
  obtain ⟨a, ha⟩ := section_proportional_to_gen (hL.pull π) (E ⟨w, hw⟩) t ht
  letI := sectionAlgebra g ⊤
  have hs : Function.Surjective (algebraMap S Γ(Y, ⊤)) := by
    have e : g.appLE ⊤ ⊤ le_top = g.appTop := by
      simp only [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE, Scheme.Hom.preimage_top]
    change Function.Surjective (((Scheme.ΓSpecIso (CommRingCat.of S)).inv ≫ g.appLE ⊤ ⊤ le_top).hom)
    rw [e]
    exact hsurj.comp (ConcreteCategory.bijective_of_isIso
      (Scheme.ΓSpecIso (CommRingCat.of S)).inv).2
  obtain ⟨c, rfl⟩ := hs a
  have hcv : (P.d₀.map α).mulVec (c • v.1) = 0 := by rw [Matrix.mulVec_smul, v.2, smul_zero]
  refine ⟨c, congrArg Subtype.val (E.injective (a₁ := ⟨w, hw⟩) (a₂ := ⟨c • v.1, hcv⟩) ?_)⟩
  refine globalSection_ext_on_coordinates _ _ (fun i => π ⁻¹ᵁ P.W i)
    (fun i _ => P.chart i) (P.chartLe (π := π)) (π.iSup_preimage_eq_top P.cover) fun i => ?_
  letI := sectionAlgebra g (π ⁻¹ᵁ P.W i)
  rw [ha, map_mul, resG_resG, hE ⟨c • v.1, hcv⟩ i, value_smul, hgen]
  have hres := (sectionRes g (homOfLE (le_top : π ⁻¹ᵁ P.W i ≤ ⊤))).commutes c
  exact congrArg (· * resG Y (P.chartLe i) (t.s (fun _ => P.chart i)).val) hres

end GlobalTheory.LineBundleSections.PerfectSections
