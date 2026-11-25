import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.FormalPullbackGenerators
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.FormalPullbackGeneratorOperations

/-! The ratio of two generators of the same formal line bundle is a unit. -/

noncomputable section

open AlgebraicGeometry CategoryTheory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi

namespace GlobalTheory.CommPairing

/-- If global functions descend through `p`, the ratio is a unit on its base. -/
theorem exists_ratio {X Y S : Scheme.{0}} {L : LB X} (hL : L.IsLB)
    {I J : Type} [Fintype I] [Fintype J] {f : I → (Y ⟶ X)} {e : I → ℤ}
    {g : J → (Y ⟶ X)} {d : J → ℤ} (h : FormEq f e g d)
    (p : Y ⟶ S) [IsIso p.appTop]
    {s : LB.Gen (LB.LinComb L f e)} {t : LB.Gen (LB.LinComb L g d)} (hs : s.IsGen) (ht : t.IsGen) :
    ∃ c : Γ(S, ⊤)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (j : (Z ⟶ X) → L.ι),
      Good L z j → val s r z j = val t r z j * gm (r ≫ p) z ⊤ c := by
  have hzero : FormEq (Sum.elim f g) (Sum.elim e (fun j => -d j))
      (PEmpty.elim : PEmpty → (Y ⟶ X)) PEmpty.elim := by
    intro U _ a
    rw [Fintype.prod_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib,
      h U a, mul_inv_cancel, Fintype.prod_empty]
  obtain ⟨u, _, hu⟩ := exists_gen_of_formEq hL hzero
    (LB.mulGen L f e g (fun j => -d j) s (LB.invGen L g d t))
    (mulGen_isGen hs (invGen_isGen ht))
  have le : (⊤ : Y.Opens) ≤ LB.wchart L (PEmpty.elim : PEmpty → (Y ⟶ X)) PEmpty.elim :=
    fun _ _ => Set.mem_iInter.2 fun i => i.elim
  let v := res le (u.s PEmpty.elim)
  let E := Units.mapEquiv (asIso p.appTop).commRingCatIsoToRingEquiv.toMulEquiv
  refine ⟨E.symm v, fun Z r z j hj => ?_⟩
  have e₁ : gm r z ⊤ v = val s r z j * (val t r z j)⁻¹ := by
    have ej : (fun i : PEmpty => j (r ≫ PEmpty.elim i)) = PEmpty.elim := funext fun i => i.elim
    have eu := hu Z r z j hj
    rw [val_mul hj, val_inv] at eu
    exact (gm_res r z le trivial _).trans ((val_of u r z j PEmpty.elim (congrFun ej)).symm.trans eu)
  have e₂ : gm r z ⊤ v = gm (r ≫ p) z ⊤ (E.symm v) := by
    have hE := E.apply_symm_apply v
    change pullU p ⊤ (E.symm v) = v at hE
    exact (congrArg (gm r z ⊤) hE.symm).trans (gm_pull r p z ⊤ trivial _)
  rw [← e₂, e₁, mul_comm _ (val s r z j * (val t r z j)⁻¹), mul_assoc, inv_mul_cancel, mul_one]

end GlobalTheory.CommPairing
