import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.PerfectSectionBasisAtPoint
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.PerfectSmoothProjectiveSections
import Mathlib.FieldTheory.AlgebraicClosure
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-! Vanishing on the geometric closed fibre gives a section basis over a
local ring that persists under all changes of coefficients. -/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits UpperTheory.Cb
open GlobalTheory.SchemeCohomology
open ReciprocityTheory.ChartRestriction.G.Semi

namespace GlobalTheory.LineBundleSections

private def pullIdentityChart {X : Scheme.{0}} (L : LB X) :
    ChartPull L (L.pull (𝟙 X)) (𝟙 X) where
  idx i := fun _ => i
  le i := (pull_chart L (𝟙 X) i).ge
  g i j := by
    rw [pullLE_id]
    have e := (ChartPull.pull L (𝟙 X)).restrict_g
      (inf_le_left.trans (pull_chart L (𝟙 X) i).ge)
      (inf_le_right.trans (pull_chart L (𝟙 X) j).ge)
    rw [pullLE_id] at e
    exact (e.trans (res_refl (L.g i j))).symm

private theorem chartValue_pull {X Y : Scheme.{0}} {L : LB X} (π : Y ⟶ X)
    (s : Γ(toMod L, ⊤)) {W : X.Opens} {i : L.ι} (hW : W ≤ L.U i) :
    resG Y (le_inf le_top ((π.preimage_mono hW).trans (pull_chart L π i).ge))
        (coord (pullSection (ChartPull.pull L π) (U := ⊤) (V := ⊤) (by simp) s) (fun _ => i)) =
      π.app W (resG X (le_inf le_top hW) (coord s i)) := by
  let P := ChartPull.pull L π
  rw [coord_pullSection, resG_appLE]
  have h := appLE_resG (π := π) (show π ⁻¹ᵁ W ≤ π ⁻¹ᵁ W from le_rfl)
    (le_inf le_top hW : W ≤ (⊤ : X.Opens) ⊓ L.U i) (coord s i)
  refine h.symm.trans ?_
  exact congrArg (fun f : Γ(X, W) ⟶ Γ(Y, π ⁻¹ᵁ W) =>
    f (resG X (le_inf le_top hW) (coord s i))) (Scheme.Hom.app_eq_appLE π).symm

private theorem chartValue_of_identity {X : Scheme.{0}} {L : LB X}
    (s : Γ(toMod (L.pull (𝟙 X)), ⊤)) {W : X.Opens} {i : L.ι} (hW : W ≤ L.U i) :
    (𝟙 X : X ⟶ X).app W
        (resG X (le_inf le_top hW)
          (coord (pullSection (pullIdentityChart L) (U := ⊤) (V := ⊤) (by simp) s) i)) =
      resG X (le_inf le_top (((𝟙 X : X ⟶ X).preimage_mono hW).trans (pull_chart L (𝟙 X) i).ge))
        (coord s (fun _ => i)) := by
  rw [coord_pullSection, resG_appLE]
  let j : (L.pull (𝟙 X)).ι := fun _ => i
  let U := (⊤ : X.Opens) ⊓ (L.pull (𝟙 X)).U j
  let h : W ≤ U := le_inf le_top
    (((𝟙 X : X ⟶ X).preimage_mono hW).trans (pull_chart L (𝟙 X) i).ge)
  let r : Γ(X, U) ⟶ Γ(X, W) := X.presheaf.map (homOfLE h).op
  have e : (𝟙 X : X ⟶ X).appLE U W h = r :=
    (congrArg (· ≫ r) (Scheme.Hom.id_app U)).trans (Category.id_comp r)
  let a := coord s j
  change (𝟙 X : X ⟶ X).app W ((𝟙 X : X ⟶ X).appLE U W h a) = r a
  exact (congrArg (fun r' : Γ(X, U) ⟶ Γ(X, W) => (𝟙 X : X ⟶ X).app W (r' a)) e).trans
    (ConcreteCategory.congr_hom (Scheme.Hom.id_app W) (r a))

/-- Choose one matrix of kernel vectors at the geometric closed fibre, and
use the section comparison on each scalar extension to descend its basis. -/
theorem exists_local_basis_of_geometric_closed_fibre {R : Type} [CommRing R] [IsLocalRing R]
    {X : Scheme.{0}} (f : X ⟶ Spec (.of R)) [Smooth f] {M : LB X} (hM : M.IsLB) (hf : IsProjOver f)
    (m : ℕ)
    (h₀ :
      let k := IsLocalRing.ResidueField R
      let K := AlgebraicClosure k
      let α₀ : R →+* K := (algebraMap k K).comp (IsLocalRing.residue R)
      let t := Spec.map (CommRingCat.ofHom α₀)
      let F := toMod (M.pull (pullback.fst f t))
      letI := sectionBaseModule (pullback.snd f t) F ⊤
      Module.finrank K Γ(F, ⊤) = m ∧ Subsingleton (CohomologyOn F ⊤ 1)) :
    ∃ b : Fin m → Γ(toMod M, ⊤),
      ∀ (S : Type) [CommRing S] (α : R →+* S) {Y : Scheme.{0}} {π : Y ⟶ X}
        {g : Y ⟶ Spec (.of S)}, IsPullback π g f (Spec.map (CommRingCat.ofHom α)) →
        letI := sectionBaseModule g (toMod (M.pull π)) ⊤
        ∃ e : (Fin m → S) ≃ₗ[S] Γ(toMod (M.pull π), ⊤),
          ∀ k, e (Pi.single k 1) =
            pullSection (ChartPull.pull M π) (U := ⊤) (V := ⊤) (by simp) (b k) := by
  classical
  obtain ⟨P⟩ := nonempty_perfectSections_of_smooth_projective f hM hf
  let k := IsLocalRing.ResidueField R
  let K := AlgebraicClosure k
  let α₀ : R →+* K := (algebraMap k K).comp (IsLocalRing.residue R)
  let t := Spec.map (CommRingCat.ofHom α₀)
  let π₀ := pullback.fst f t
  let f₀ := pullback.snd f t
  let H₀ : IsPullback π₀ f₀ f t := IsPullback.of_hasPullback _ _
  letI := sectionBaseModule f₀ (toMod (M.pull π₀)) ⊤
  obtain ⟨r, n, B, hr, -, hB⟩ := P.exists_baseChange_basis_at_point α₀ H₀ h₀.2
  have hr' : IsUnit r := by
    by_contra hn
    have hzero : IsLocalRing.residue R r = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr
      ((IsLocalRing.mem_maximalIdeal r).mpr (mem_nonunits_iff.mpr hn))
    exact hr (by simp only [α₀, RingHom.comp_apply, hzero, map_zero])
  obtain ⟨e₀, -⟩ := hB K α₀ H₀ (hr'.map α₀)
  have hfin : Module.finrank K (Fin n → K) = n := Module.finrank_fin_fun K
  have hn : n = m := hfin.symm.trans (e₀.finrank_eq.trans h₀.1)
  subst n
  have HI : IsPullback (𝟙 X) f f (Spec.map (CommRingCat.ofHom (RingHom.id R))) := by
    rw [CommRingCat.ofHom_id, Spec.map_id]
    exact IsPullback.of_horiz_isIso ⟨by simp⟩
  obtain ⟨eR, heR⟩ := hB R (RingHom.id R) HI (hr'.map (RingHom.id R))
  let b (a : Fin (m)) : Γ(toMod M, ⊤) :=
    pullSection (pullIdentityChart M) (U := ⊤) (V := ⊤) (by simp) (eR (Pi.single a 1))
  have hb (a : Fin (m)) (i : P.I) :
      resG X (le_inf le_top (P.le_chart i)) (coord (b a) (P.chart i)) =
        P.valueBase (B.col a) i := by
    apply (ConcreteCategory.bijective_of_isIso ((𝟙 X : X ⟶ X).app (P.W i))).1
    refine (chartValue_of_identity (eR (Pi.single a 1)) (P.le_chart i)).trans ?_
    refine (heR (Pi.single a 1) i).trans ?_
    have hcol : ((B.map (RingHom.id R)).mulVec (Pi.single a 1)) = (RingHom.id R) ∘ B.col a := by
      rw [Matrix.mulVec_single_one]
      rfl
    rw [hcol]
    exact P.value_comp HI (B.col a) i
  refine ⟨b, fun S _ α Y π g H => ?_⟩
  letI := sectionBaseModule g (toMod (M.pull π)) ⊤
  obtain ⟨e, he⟩ := hB S α H (hr'.map α)
  refine ⟨e, fun a => ?_⟩
  apply globalCoordinates.injective
  let hW (i : P.I) : π ⁻¹ᵁ P.W i ≤ (M.pull π).U (fun _ => P.chart i) :=
    (π.preimage_mono (P.le_chart i)).trans (pull_chart M π (P.chart i)).ge
  refine globalSection_ext_on_coordinates _ _ (fun i => π ⁻¹ᵁ P.W i) (fun i _ => P.chart i)
    hW (π.iSup_preimage_eq_top P.cover) fun i => ?_
  simp only [globalCoordinates_apply, resG_resG]
  refine (he (Pi.single a 1) i).trans ?_
  have hcol : (B.map α).mulVec (Pi.single a 1) = α ∘ B.col a := by
    rw [Matrix.mulVec_single_one]
    rfl
  exact (congrArg (fun v => P.value π g v i) hcol).trans
    ((P.value_comp H (B.col a) i).trans
      ((congrArg (fun r : Γ(X, P.W i) => π.app (P.W i) r) (hb a i).symm).trans
        (chartValue_pull π (b a) (P.le_chart i)).symm))

end GlobalTheory.LineBundleSections
