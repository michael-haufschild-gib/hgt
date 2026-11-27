import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.MatrixKernelBasisAtPoint
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.PerfectSectionsTriviality

/-! Exactness at a field point gives a local basis of sections, described
by the same matrix of vectors after every base change. -/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open GlobalTheory.SchemeCohomology ReciprocityTheory.ChartRestriction.G.Semi

namespace GlobalTheory.LineBundleSections.PerfectSections

variable {R S : Type} [CommRing R] [CommRing S] {X Y : Scheme.{0}} {L : LB X}
  {f : X ⟶ Spec (.of R)} (P : PerfectSections f L)
  {π : Y ⟶ X} {g : Y ⟶ Spec (.of S)}

private theorem chart_le (i : P.I) :
    π ⁻¹ᵁ P.W i ≤ (L.pull π).U (fun _ => P.chart i) :=
  (π.preimage_mono (P.le_chart i)).trans (pull_chart L π (P.chart i)).ge

private theorem value_add (v w : Fin P.a → S) (i : P.I) :
    P.value π g (v + w) i = P.value π g v i + P.value π g w i := by
  simp only [PerfectSections.value, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]

/-- The matrix comparison is linear because the chart formulas are linear
in the entries of the vector and the charts cover the scheme. -/
theorem exists_linear_compare (α : R →+* S)
    (H : IsPullback π g f (Spec.map (CommRingCat.ofHom α))) :
    letI := sectionBaseModule g (toMod (L.pull π)) ⊤
    ∃ e : LinearMap.ker (P.d₀.map α).mulVecLin ≃ₗ[S] Γ(toMod (L.pull π), ⊤),
      ∀ v i, resG Y (le_inf le_top (P.chart_le (π := π) i)) (coord (e v) (fun _ => P.chart i)) =
        P.value π g v.1 i := by
  let M := LinearMap.ker (P.d₀.map α).mulVecLin
  let F := toMod (L.pull π)
  letI := sectionBaseModule g F ⊤
  obtain ⟨E, hE⟩ := (P.compare S α Y π g H).1
  let e : M ≃ Γ(F, ⊤) := E
  have he (v : M) (i : P.I) : resG Y (le_inf le_top (P.chart_le (π := π) i))
      (coord (e v) (fun _ => P.chart i)) = P.value π g v.1 i := hE v i
  have ext_on (a b : Γ(F, ⊤))
      (h : ∀ i, resG Y (le_inf le_top (P.chart_le (π := π) i)) (coord a (fun _ => P.chart i)) =
        resG Y (le_inf le_top (P.chart_le (π := π) i)) (coord b (fun _ => P.chart i))) : a = b := by
    apply globalCoordinates.injective
    refine globalSection_ext_on_coordinates _ _ (fun i => π ⁻¹ᵁ P.W i) (fun i _ => P.chart i)
      (P.chart_le (π := π)) (π.iSup_preimage_eq_top P.cover) fun i => ?_
    simpa only [globalCoordinates_apply, resG_resG] using h i
  refine ⟨{ e with
    map_add' := fun v w => ext_on _ _ fun i => ?_
    map_smul' := fun r v => ext_on _ _ fun i => ?_ }, he⟩
  · let valueOf (s : Γ(F, ⊤)) :=
      resG Y (le_inf le_top (P.chart_le (π := π) i)) (coord s (fun _ => P.chart i))
    change valueOf (e (v + w)) = valueOf (e v + e w)
    calc
      _ = P.value π g (v.1 + w.1) i := he (v + w) i
      _ = valueOf (e v) + valueOf (e w) :=
        (P.value_add v.1 w.1 i).trans (congrArg₂ (· + ·) (he v i).symm (he w i).symm)
      _ = _ := by
        let j : (L.pull π).ι := fun _ => P.chart i
        let ρ := resG Y (le_inf le_top (P.chart_le (π := π) i))
        exact ((congrArg ρ (coord_add (L := L.pull π) (V := ⊤) (e v) (e w) j)).trans
          (map_add ρ (coord (e v) j) (coord (e w) j))).symm
  · let V := π ⁻¹ᵁ P.W i
    letI := sectionAlgebra g (⊤ : Y.Opens)
    letI := sectionAlgebra g V
    let valueOf (s : Γ(F, ⊤)) :=
      resG Y (le_inf le_top (P.chart_le (π := π) i)) (coord s (fun _ => P.chart i))
    change valueOf (e (r • v)) = valueOf (algebraMap S Γ(Y, ⊤) r • e v)
    have hr : resG Y (le_top : V ≤ ⊤) (algebraMap S Γ(Y, ⊤) r) = algebraMap S Γ(Y, V) r :=
      (sectionRes g (homOfLE le_top)).commutes r
    calc
      _ = P.value π g (r • v.1) i := he (r • v) i
      _ = algebraMap S Γ(Y, V) r * valueOf (e v) :=
        (P.value_smul (π := π) (g := g) r v.1 i).trans
          (congrArg (fun z => algebraMap S Γ(Y, V) r * z) (he v i).symm)
      _ = _ := by
        let j : (L.pull π).ι := fun _ => P.chart i
        let W := (⊤ : Y.Opens) ⊓ (L.pull π).U j
        let hV : V ≤ W := le_inf le_top (P.chart_le (π := π) i)
        let hW : W ≤ ⊤ := inf_le_left
        let a := algebraMap S Γ(Y, ⊤) r
        have h₁ := congrArg (resG Y hV) (coord_smul (L := L.pull π) (V := ⊤) a (e v) j)
        have h₂ := map_mul (resG Y hV) (resG Y hW a) (coord (e v) j)
        have h₃ := (resG_resG hW hV a).trans hr
        exact (h₁.trans (h₂.trans (congrArg (· * valueOf (e v)) h₃))).symm

/-- The same coefficient vectors give bases of sections over every affine
base where the chosen coefficient is invertible. -/
theorem exists_baseChange_basis_at_point {K : Type} [Field K]
    (α₀ : R →+* K) {Y₀ : Scheme.{0}} {π₀ : Y₀ ⟶ X} {g₀ : Y₀ ⟶ Spec (.of K)}
    (H₀ : IsPullback π₀ g₀ f (Spec.map (CommRingCat.ofHom α₀)))
    (h₀ : Subsingleton (CohomologyOn (toMod (L.pull π₀)) ⊤ 1)) :
    ∃ (r : R) (n : ℕ) (B : Matrix (Fin P.a) (Fin n) R), α₀ r ≠ 0 ∧ P.d₀ * B = 0 ∧
      ∀ (T : Type) [CommRing T] (α : R →+* T) {Z : Scheme.{0}} {ρ : Z ⟶ X} {h : Z ⟶ Spec (.of T)},
        IsPullback ρ h f (Spec.map (CommRingCat.ofHom α)) → IsUnit (α r) →
        letI := sectionBaseModule h (toMod (L.pull ρ)) ⊤
        ∃ e : (Fin n → T) ≃ₗ[T] Γ(toMod (L.pull ρ), ⊤),
          ∀ v i, resG Z (le_inf le_top (P.chart_le (π := ρ) i)) (coord (e v) (fun _ => P.chart i)) =
            P.value ρ h ((B.map α).mulVec v) i := by
  obtain ⟨r, n, B, hr, hB, hBasis⟩ := exists_matrix_basis_ker_of_exact_at_point α₀ P.d₀ P.d₁ P.comp
    ((P.compare K α₀ Y₀ π₀ g₀ H₀).2 h₀)
  refine ⟨r, n, B, hr, hB, fun T _ α Z ρ h H ha => ?_⟩
  letI := sectionBaseModule h (toMod (L.pull ρ)) ⊤
  let φ := (B.map α).mulVecLin
  let M := LinearMap.ker (P.d₀.map α).mulVecLin
  have hφ (v : Fin n → T) : φ v ∈ M := by
    change (P.d₀.map α).mulVec ((B.map α).mulVec v) = 0
    rw [Matrix.mulVec_mulVec, ← Matrix.map_mul, hB]
    simp
  let ψ : (Fin n → T) →ₗ[T] M :=
    { toFun := fun v => ⟨φ v, hφ v⟩
      map_add' := fun a b => Subtype.ext (map_add φ a b)
      map_smul' := fun a b => Subtype.ext (map_smul φ a b) }
  have hψ : Function.Bijective ψ := by
    refine ⟨fun v w hv => ?_, fun v => ?_⟩
    · obtain ⟨z, _, hu⟩ := hBasis T α ha (φ w) (hφ w)
      exact (hu v (congrArg Subtype.val hv)).trans (hu w rfl).symm
    · obtain ⟨w, hw, -⟩ := hBasis T α ha v.1 v.2
      exact ⟨w, Subtype.ext hw⟩
  obtain ⟨e, he⟩ := P.exists_linear_compare α H
  exact ⟨(LinearEquiv.ofBijective ψ hψ).trans e, fun v i => he (ψ v) i⟩

end GlobalTheory.LineBundleSections.PerfectSections
