import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.FormalProductPullback
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.CechHomologyZero
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.OpenRestrictionCech
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.GradedTwistSections
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.LineBundleCechBaseChange
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.LineBundleSectionIsomorphism

/-! Very ample powers on a top affine-base restriction compute the global
sections of the original bundle powers. -/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace HTGeometry
open GlobalTheory.SchemeCohomology UpperTheory.Cb
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.LineBundleSections

variable {K : Type} [Field K] {X Y : Scheme.{0}} (f : X ⟶ Spec (.of K))

private theorem nonempty_globalSections_pull_iso (hf : IsProjOver f) {L : LB X} (hL : L.IsLB)
    (π : Y ⟶ X) [IsIso π] :
    letI := sectionBaseModule f (toMod L) ⊤
    letI := sectionBaseModule (π ≫ f) (toMod (L.pull π)) ⊤
    Nonempty (Γ(toMod L, ⊤) ≃ₗ[K] Γ(toMod (L.pull π), ⊤)) := by
  letI := sectionBaseModule f (toMod L) ⊤
  letI := sectionBaseModule (π ≫ f) (toMod (L.pull π)) ⊤
  obtain ⟨n, i, hi, hif⟩ := hf
  letI := hi
  let U (j : Fin (n + 1)) := i ⁻¹ᵁ PSpace.coordinateOpen K n j
  have cU : ⨆ j, U j = ⊤ := i.iSup_preimage_eq_top (PSpace.iSup_coordinateOpen K n)
  have hπ : π.opensRange = ⊤ := Scheme.Hom.opensRange_of_isIso π
  have ha (s : Finset (Fin (n + 1))) (hs : s.Nonempty) :
      IsAffineOpen (coverInter π.opensRange U s) := by
    rw [hπ]
    exact (coverInter_pull (π := i) (PSpace.coordinateOpen K n) s).symm ▸
      (PSpace.isAffineOpen_coordinateInter K n hs).preimage i
  have hc : cech f (toMod L) U = cechOverOpen f (toMod L) π.opensRange U := by
    rw [hπ]
    rfl
  let e := eqToIso hc ≪≫ openCechPullbackIso f U π hL ha
  let eX := cechHomologyZeroEquiv f (toMod L) U cU
  let eY := cechHomologyZeroEquiv (π ≫ f) (toMod (L.pull π)) (fun j => π ⁻¹ᵁ U j)
    (π.iSup_preimage_eq_top cU)
  exact ⟨eX.symm.trans ((HomologicalComplex.homologyMapIso e 0).toLinearEquiv.trans eY)⟩

private def chart_trivialTwist (L : LB X) (π : Y ⟶ X) (N t : ℕ) :
    ChartPull (LB.LinComb L (fun _ : PUnit => π) (fun _ => ((N * t : ℕ) : ℤ)))
      (twist (LB.trivial Y)
        (LB.LinComb L (fun _ : Fin N => π) (fun _ => 1)) (t : ℤ)) (𝟙 Y) where
  idx i := (PUnit.unit, fun _ => i PUnit.unit)
  le i := le_inf le_top (fun _ h => Set.mem_iInter.2 fun _ => Set.mem_iInter.1 h PUnit.unit)
  g i j := by
    rw [pullLE_id]
    let U := L.U (i PUnit.unit) ⊓ L.U (j PUnit.unit)
    let F : PUnit → (Y ⟶ X) := fun _ => π
    let G : Fin N → (Y ⟶ X) := fun _ => π
    let a : Fin N → L.ι := fun _ => i PUnit.unit
    let b : Fin N → L.ι := fun _ => j PUnit.unit
    let H := LB.LinComb L G (fun _ => 1)
    let W := LB.wchart L F i ⊓ LB.wchart L F j
    let V := LB.wchart L G a ⊓ LB.wchart L G b
    have wi : LB.wchart L F i ≤ H.U a := fun _ h =>
      Set.mem_iInter.2 fun _ => Set.mem_iInter.1 h PUnit.unit
    have wj : LB.wchart L F j ≤ H.U b := fun _ h =>
      Set.mem_iInter.2 fun _ => Set.mem_iInter.1 h PUnit.unit
    have hw : W ≤ V := le_inf (inf_le_left.trans wi) (inf_le_right.trans wj)
    let u := L.g (i PUnit.unit) (j PUnit.unit)
    let r : W ≤ π ⁻¹ᵁ U := le_inf
      (inf_le_left.trans (LB.wchart_le L F i PUnit.unit))
      (inf_le_right.trans (LB.wchart_le L F j PUnit.unit))
    have hM : (LB.LinComb L F (fun _ => ((N * t : ℕ) : ℤ))).g i j =
        (pullLE π r u) ^ ((N * t : ℕ) : ℤ) := by
      change (∏ k : PUnit, _) = _
      rw [Fintype.prod_unique]
      exact congrArg (fun a : Γ(Y, W)ˣ => a ^ ((N * t : ℕ) : ℤ)) (res_pullU π U r u)
    have hH : res hw (H.g a b) = (pullLE π r u) ^ N := by
      let h (k : Fin N) : V ≤ π ⁻¹ᵁ U := le_inf
        (inf_le_left.trans (LB.wchart_le L G a k))
        (inf_le_right.trans (LB.wchart_le L G b k))
      change res hw (∏ k : Fin N, (pullLE π (h k) u) ^ (1 : ℤ)) = _
      simp only [map_prod, zpow_one, res_pullLE]
      exact (Finset.prod_const _).trans (congrArg (fun n => (pullLE π r u) ^ n) (Fintype.card_fin N))
    have e := res_twist_g (M := LB.trivial Y) (H := H) (t : ℤ) (PUnit.unit, a) (PUnit.unit, b)
      (W := W) (le_inf le_top (inf_le_left.trans wi)) (le_inf le_top (inf_le_right.trans wj))
    change _ = res _ (1 : Γ(Y, (⊤ : Y.Opens) ⊓ ⊤)ˣ) * (res hw (H.g a b)) ^ (t : ℤ) at e
    rw [map_one, one_mul, hH, ← zpow_natCast, ← zpow_mul, ← Nat.cast_mul] at e
    exact hM.trans e.symm

/-- The degree `t` twist by the `N`-fold pullback computes the sections
of the degree `N*t` power on the original scheme. -/
theorem finrank_trivialTwist_of_iso (hf : IsProjOver f) {L : LB X} (hL : L.IsLB)
    (π : Y ⟶ X) [IsIso π] (N t : ℕ) :
    let M := LB.LinComb L (fun _ : PUnit => 𝟙 X) (fun _ => ((N * t : ℕ) : ℤ))
    letI := sectionBaseModule f (toMod M) ⊤
    Module.finrank K Γ(toMod M, ⊤) =
      Module.finrank K (TwistSections (π ≫ f) (LB.trivial Y)
        (LB.LinComb L (fun _ : Fin N => π) (fun _ => 1)) ⊤ (t : ℤ)) := by
  let d : PUnit → ℤ := fun _ => ((N * t : ℕ) : ℤ)
  let M := LB.LinComb L (fun _ : PUnit => 𝟙 X) d
  let P := LB.LinComb L (fun _ : PUnit => π) d
  let H := LB.LinComb L (fun _ : Fin N => π) (fun _ => 1)
  let T := twist (LB.trivial Y) H (t : ℤ)
  have hM : M.IsLB := hL.linComb _ _
  have hP : P.IsLB := hL.linComb _ _
  have hT : T.IsLB := twist_isLB (LB.isLB_trivial Y) (hL.linComb _ _) _
  letI := sectionBaseModule f (toMod M) ⊤
  letI := sectionBaseModule (π ≫ f) (toMod (M.pull π)) ⊤
  letI := sectionBaseModule (π ≫ f) (toMod P) ⊤
  letI := sectionBaseModule (π ≫ f) (toMod T) ⊤
  obtain ⟨e⟩ := nonempty_globalSections_pull_iso f hf hM π
  let Q : ChartPull P M π := by
    have he : (fun _ : PUnit => π ≫ 𝟙 X) = fun _ => π := funext fun _ => Category.comp_id π
    exact (congrArg (fun g => ChartPull (LB.LinComb L g d) M π) he).mp
      (ChartPull.linComb L (fun _ : PUnit => 𝟙 X) d π)
  obtain ⟨u, hu⟩ := (ChartPull.pull M π).iso_of_common Q hM
  obtain ⟨v, hv⟩ := (chart_trivialTwist L π N t).iso_of_common (ChartPull.id T) hT
  letI := sectionAlgebra (π ≫ f) (⊤ : Y.Opens)
  letI : IsScalarTower K Γ(Y, ⊤) Γ(toMod (M.pull π), ⊤) := .of_algebraMap_smul fun _ _ => rfl
  letI : IsScalarTower K Γ(Y, ⊤) Γ(toMod P, ⊤) := .of_algebraMap_smul fun _ _ => rfl
  letI : IsScalarTower K Γ(Y, ⊤) Γ(toMod T, ⊤) := .of_algebraMap_smul fun _ _ => rfl
  let eP := (sectionIsoEquiv (hM.pull π) hP hu (V := ⊤)).restrictScalars K
  let eT := (sectionIsoEquiv hP hT hv (V := ⊤)).restrictScalars K
  exact (e.trans (eP.trans eT)).finrank_eq

end GlobalTheory.LineBundleSections
