import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.AffineQuasicoherentAcyclic

/-! Vanishing above the length of a finite affine cover with affine intersections. -/

open AlgebraicGeometry CategoryTheory TopologicalSpace HTGeometry RHTower

noncomputable section

namespace GlobalTheory.SchemeCohomology

universe u w

section Leray

variable {X : TopCat.{u}} [HasExt.{w} (TopCat.Sheaf AddCommGrpCat.{u} X)]
  {ι : Type*} [DecidableEq ι] [LinearOrder ι] {V : Opens X} {U : ι → Opens X}

private theorem leray_vanishing_exactAt_aux (hcov : V ≤ ⨆ i, U i) :
    ∀ (q : ℕ) (F : TopCat.Sheaf AddCommGrpCat.{u} X),
      (∀ a : Finset ι, a.Nonempty → DeningerAcyclicOn.{w} F (coverInter V U a)) →
      (sheafCech F V U).ExactAt (q + 1) →
      ∀ x : deningerSheafCohomology.{w} (coverInter V U ∅) F (q + 1), x = 0 := by
  intro q
  induction q with
  | zero =>
    intro F hF hExact x
    let S := deningerGodementComplex F
    have hS := deningerGodementShortExact F
    have hsurj : Function.Surjective ((sheafCechMap S.g V U).app ∅) :=
      FinsetCechDatum.surjective_bot_of_chase (sheafCechMap S.f V U) (sheafCechMap S.g V U)
        (fun a _ x => sheafCech_comp_zero V U a x)
        (fun a ha => deningerSections_surjective_of_acyclic hS _
          (hF a (Finset.card_pos.mp (by omega))))
        (fun a _ y hy => sheafCech_exact hS a y hy)
        (fun a _ => sheafCech_injective hS a)
        hExact (godementCech_exactAt hcov 0) (sheafCech_exactBot _ hcov)
    exact deningerExt_one_eq_zero_of_lift hS _ (godement_acyclicOn F _) hsurj x
  | succ q ih =>
    intro F hF hExact x
    let S := deningerGodementComplex F
    have hS := deningerGodementShortExact F
    have hQ : (sheafCech S.X₃ V U).ExactAt (q + 1) :=
      FinsetCechDatum.exactAt_of_chase (sheafCechMap S.f V U) (sheafCechMap S.g V U) (q + 1)
        (fun a _ x => sheafCech_comp_zero V U a x)
        (fun a ha => deningerSections_surjective_of_acyclic hS _
          (hF a (Finset.card_pos.mp (by omega))))
        (fun a _ y hy => sheafCech_exact hS a y hy)
        (fun a _ => sheafCech_injective hS a)
        hExact (godementCech_exactAt hcov (q + 1))
    exact deningerExt_eq_zero_of_shift hS _ (godement_acyclicOn F _)
      q (ih S.X₃ (fun a ha => godementQuotient_acyclicOn (hF a ha)) hQ) x

/-- For a cover by acyclic intersections, exactness in one positive Čech degree
annihilates sheaf cohomology in that degree. -/
theorem leray_vanishing_exactAt (hcov : V ≤ ⨆ i, U i)
    {F : TopCat.Sheaf AddCommGrpCat.{u} X}
    (hF : ∀ a : Finset ι, a.Nonempty → DeningerAcyclicOn.{w} F (coverInter V U a))
    (q : ℕ) (hExact : (sheafCech F V U).ExactAt (q + 1))
    (x : deningerSheafCohomology.{w} V F (q + 1)) : x = 0 := by
  have h := leray_vanishing_exactAt_aux hcov q F hF hExact
  rw [coverInter_empty] at h
  exact h x

end Leray

/-- A quasi-coherent sheaf has vanishing cohomology in degrees at least the
size of a finite affine cover whose nonempty intersections are affine. -/
theorem quasicoherent_vanishing_of_finite_affineCover {X : Scheme.{u}}
    [HasExt.{w} (TopCat.Sheaf AddCommGrpCat.{u} X)]
    (M : X.Modules) [M.IsQuasicoherent] {ι : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    {V : X.Opens} (U : ι → X.Opens) (hcov : V ≤ ⨆ i, U i)
    (hU : ∀ a : Finset ι, a.Nonempty → IsAffineOpen (coverInter V U a))
    (q : ℕ) (hq : Fintype.card ι ≤ q + 1)
    (x : deningerSheafCohomology.{w} V ((SheafOfModules.toSheaf X.ringCatSheaf).obj M)
      (q + 1)) : x = 0 := by
  refine leray_vanishing_exactAt hcov (fun a ha => quasicoherent_acyclicOn M (hU a ha)) q ?_ x
  let D := sheafCech ((SheafOfModules.toSheaf X.ringCatSheaf).obj M) V U
  intro c hc _
  refine ⟨0, fun _ _ => rfl, ?_⟩
  change D.dHom 0 = c
  rw [map_zero]
  funext a
  have ha : a.card ≤ Fintype.card ι := Finset.card_le_univ a
  exact (hc a (by omega)).symm

end GlobalTheory.SchemeCohomology
