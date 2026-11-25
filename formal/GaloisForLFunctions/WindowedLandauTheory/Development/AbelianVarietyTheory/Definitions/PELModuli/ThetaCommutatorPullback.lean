import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.PELModuli.ThetaCommutatorValues
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.PELModuli.PELGeneratorTransport
import Mathlib.Tactic.Abel

/-! The theta commutator survives pullback of a polarized group scheme. -/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.WeilPull

open GlobalTheory.CommPairing

variable {S S' : Scheme.{0}} {G : Over S} [GrpObj G] {A : Over S'} [GrpObj A]
  {f : S' ⟶ S} {φ : A.left ⟶ G.left} (hp : IsGrpPullback A G f φ)
  {T : Over S'} {T₀ : Over S} (τ : T.left ⟶ T₀.left) (hτ : τ ≫ T₀.hom = T.hom ≫ f)
  {L₀ : LB G.left} {L₁ : LB A.left} {k : ℤ}

private def fiberMap : (T ⊗ A).left ⟶ (T₀ ⊗ G).left :=
  (psiO hp τ hτ).left

private theorem fiberMap_fst : fiberMap hp τ hτ ≫ (fst T₀ G).left = (fst T A).left ≫ τ :=
  psi_fst hp τ hτ

private theorem fiberMap_snd : fiberMap hp τ hτ ≫ (snd T₀ G).left = (snd T A).left ≫ φ :=
  psi_snd hp τ hτ

private theorem fiberMap_tr (x : T ⟶ A) (x₀ : T₀ ⟶ G) (h : τ ≫ x₀.left = x.left ≫ φ) :
    fiberMap hp τ hτ ≫ (translPt G x₀).left = (translPt A x).left ≫ φ :=
  psi_tr hp τ hτ x x₀ h

private theorem fiberMap_transl (x : T ⟶ A) (x₀ : T₀ ⟶ G) (h : τ ≫ x₀.left = x.left ≫ φ) :
    (translT A x).left ≫ fiberMap hp τ hτ = fiberMap hp τ hτ ≫ (translT G x₀).left :=
  psi_transl hp τ hτ x x₀ h

private theorem exists_fiberMap_inv [IsIso τ] : ∃ χ : (T₀ ⊗ G).left ⟶ (T ⊗ A).left,
    fiberMap hp τ hτ ≫ χ = 𝟙 _ ∧ χ ≫ fiberMap hp τ hτ = 𝟙 _ :=
  exists_psi_inv hp τ hτ

private theorem exists_pullGen_of_comp_eq {X Y Y' : Scheme.{0}} {L : LB X}
    {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {φ' : K → (Y' ⟶ X)} {h : Y' ⟶ Y} {ε : K → ℤ}
    (e : ∀ k, h ≫ φ k = φ' k) (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) :
    ∃ u : LB.Gen (LB.LinComb L φ' ε), u.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (J : (Z ⟶ X) → L.ι), Good L z J →
        val u r z J = val t (r ≫ h) z J := by
  obtain rfl : φ' = fun k => h ≫ φ k := (funext e).symm
  exact ⟨L.pullGen φ ε t h, ht.pullGen φ ε h, fun Z r z J hJ => val_pull hJ t h r⟩

theorem exists_theta_move (hL₀ : L₀.IsLB) (hL₁ : L₁.IsLB) (w : LB.Iso L₁ (L₀.pull φ)) (hw : w.IsGen) (k : ℤ)
    (x : T ⟶ A) (θ₀ : ThetaGrp G L₀ k T₀) (hx : τ ≫ θ₀.pt.left = x.left ≫ φ) :
    ∃ θ : ThetaGrp A L₁ k T, θ.pt = x ∧
      PMaps w ![(snd T A).left, (translPt A θ.pt).left] ![(snd T₀ G).left, (translPt G θ₀.pt).left] ![k, -k]
        θ.φ θ₀.φ (fiberMap hp τ hτ) := by
  obtain ⟨a, ha, hm⟩ := exists_gen_move hL₀ hL₁ w (pGen_of_isGen hw)
    ![(snd T₀ G).left, (translPt G θ₀.pt).left] ![(snd T A).left, (translPt A x).left] ![k, -k]
    (fiberMap hp τ hτ) (fun i => by
      fin_cases i
      · exact (fiberMap_snd hp τ hτ).symm
      · exact (fiberMap_tr hp τ hτ x θ₀.pt hx).symm) θ₀.φ θ₀.isGen
  exact ⟨⟨x, a, ha⟩, rfl, hm⟩

/-- Comparison of theta generators via the change of trivialization on the two translations. -/
def Rel (w : LB.Iso L₁ (L₀.pull φ)) (θ : ThetaGrp A L₁ k T) (θ₀ : ThetaGrp G L₀ k T₀) : Prop :=
  ∀ (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ A).left) (z : Z) (J₀) (J), Good L₀ z J₀ → Good L₁ z J →
    tval θ₀ (r ≫ fiberMap hp τ hτ) z J₀ =
      (gw w (r ≫ (snd T A).left) z (J₀ ((r ≫ (snd T A).left) ≫ φ)) (J (r ≫ (snd T A).left)) ^ k *
        gw w (r ≫ (translPt A θ.pt).left) z (J₀ ((r ≫ (translPt A θ.pt).left) ≫ φ))
          (J (r ≫ (translPt A θ.pt).left)) ^ (-k)) * tval θ r z J

theorem exists_rel_down (hL₀ : L₀.IsLB) (hL₁ : L₁.IsLB) (w : LB.Iso L₁ (L₀.pull φ)) (hw : w.IsGen)
    (x : T ⟶ A) (θ₀ : ThetaGrp G L₀ k T₀) (hx : τ ≫ θ₀.pt.left = x.left ≫ φ) :
    ∃ θ : ThetaGrp A L₁ k T, θ.pt = x ∧ Rel hp τ hτ w θ θ₀ := by
  obtain ⟨θ, rfl, m⟩ := exists_theta_move hp τ hτ hL₀ hL₁ w hw k x θ₀ hx
  refine ⟨θ, rfl, fun Z r z J₀ J hG hJ => ?_⟩
  have e₀ : (r ≫ fiberMap hp τ hτ) ≫ (snd T₀ G).left = (r ≫ (snd T A).left) ≫ φ := by
    rw [Category.assoc, Category.assoc, fiberMap_snd]
  have e₁ : (r ≫ fiberMap hp τ hτ) ≫ (translPt G θ₀.pt).left = (r ≫ (translPt A θ.pt).left) ≫ φ := by
    rw [Category.assoc, Category.assoc, fiberMap_tr hp τ hτ _ _ hx]
  have e : ∀ i, (r ≫ fiberMap hp τ hτ) ≫ ![(snd T₀ G).left, (translPt G θ₀.pt).left] i =
      (r ≫ ![(snd T A).left, (translPt A θ.pt).left] i) ≫ φ := fun i => by
    fin_cases i
    · exact e₀
    · exact e₁
  calc tval θ₀ (r ≫ fiberMap hp τ hτ) z J₀ = _ :=
        m _ r z _ (fun i => J (r ≫ ![(snd T A).left, (translPt A θ.pt).left] i)) (fun i => by
          show _ ∈ L₀.U (J₀ ((r ≫ fiberMap hp τ hτ) ≫ _))
          rw [e i]; exact hG _) (fun i => hJ _)
    _ = _ := by
      congr 1
      simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
      rw [e₀, e₁]

theorem exists_rel_up [IsIso τ] (hL₀ : L₀.IsLB) (hL₁ : L₁.IsLB) (w : LB.Iso L₁ (L₀.pull φ)) (hw : w.IsGen)
    (x₀ : T₀ ⟶ G) (θ : ThetaGrp A L₁ k T) (hx : τ ≫ x₀.left = θ.pt.left ≫ φ) :
    ∃ θ₀ : ThetaGrp G L₀ k T₀, θ₀.pt = x₀ ∧ Rel hp τ hτ w θ θ₀ := by
  obtain ⟨χ, h₁, h₂⟩ := exists_fiberMap_inv hp τ hτ
  obtain ⟨t, ht, hv⟩ := exists_up (pGen_of_isGen hw) hL₀ hL₁
    (φ' := ![(snd T A).left, (translPt A θ.pt).left]) (ε := ![k, -k]) θ.φ θ.isGen
  have e₀ : χ ≫ (snd T A).left ≫ φ = (snd T₀ G).left := by
    rw [← fiberMap_snd hp τ hτ, ← Category.assoc, h₂, Category.id_comp]
  have e₁ : χ ≫ (translPt A θ.pt).left ≫ φ = (translPt G x₀).left := by
    rw [← fiberMap_tr hp τ hτ _ _ hx, ← Category.assoc, h₂, Category.id_comp]
  obtain ⟨u, hu, hu'⟩ := exists_pullGen_of_comp_eq
    (h := χ) (φ' := ![(snd T₀ G).left, (translPt G x₀).left]) (fun i => by
      fin_cases i
      · exact (Category.assoc χ (snd T A).left φ).trans e₀
      · exact (Category.assoc χ (translPt A θ.pt).left φ).trans e₁)
    t ht
  refine ⟨⟨x₀, u, hu⟩, rfl, fun Z r z J₀ J hG hJ => ?_⟩
  have e : (r ≫ fiberMap hp τ hτ) ≫ χ = r := by
    rw [Category.assoc]; exact (congrArg (r ≫ ·) h₁).trans (Category.comp_id _)
  refine ((hu' Z _ z J₀ hG).trans (congrArg (fun q => val t q z J₀) e)).trans ?_
  refine (hv Z r z _ _ (hG.mem _ r) (hJ.mem _ r)).trans ?_
  congr 1
  simp only [pw, Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Category.assoc]

theorem cancel_iff {M : Type*} [CommGroup M] (P X Y Z a b c d C : M) :
    (P * X⁻¹ * a) * (X * Z⁻¹ * b) = (P * Y⁻¹ * c) * (Y * Z⁻¹ * d) * C ↔ a * b = c * d * C := by
  have e₁ : (P * X⁻¹ * a) * (X * Z⁻¹ * b) = (P * Z⁻¹) * (a * b) := by
    apply Additive.ofMul.injective; simp only [ofMul_mul, ofMul_inv]; abel
  have e₂ : (P * Y⁻¹ * c) * (Y * Z⁻¹ * d) * C = (P * Z⁻¹) * (c * d * C) := by
    apply Additive.ofMul.injective; simp only [ofMul_mul, ofMul_inv]; abel
  rw [e₁, e₂, mul_right_inj]

theorem commIsOf_iff_of_rel [IsIso τ] (hL₀ : L₀.IsLB) (hL₁ : L₁.IsLB) (w : LB.Iso L₁ (L₀.pull φ))
    {θx θy : ThetaGrp A L₁ k T} {θx₀ θy₀ : ThetaGrp G L₀ k T₀} (hc : θx.pt * θy.pt = θy.pt * θx.pt)
    (hx : τ ≫ θx₀.pt.left = θx.pt.left ≫ φ) (hy : τ ≫ θy₀.pt.left = θy.pt.left ≫ φ)
    (mx : Rel hp τ hτ w θx θx₀) (my : Rel hp τ hτ w θy θy₀) (c₀ : Γ(T₀.left, ⊤)ˣ) (c : Γ(T.left, ⊤)ˣ)
    (hcc : ∀ (Z : Scheme.{0}) (r : Z ⟶ T.left) (z : Z), gm (r ≫ τ) z ⊤ c₀ = gm r z ⊤ c) :
    CommIsOf A L₁ k θx θy c ↔ CommIsOf G L₀ k θx₀ θy₀ c₀ := by
  have key : ∀ (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ A).left) (z : Z) (J₀) (J), Good L₀ z J₀ → Good L₁ z J →
      (tval θx₀ (r ≫ fiberMap hp τ hτ) z J₀ *
          tval θy₀ ((r ≫ fiberMap hp τ hτ) ≫ (translT G θx₀.pt).left) z J₀ =
        tval θy₀ (r ≫ fiberMap hp τ hτ) z J₀ *
          tval θx₀ ((r ≫ fiberMap hp τ hτ) ≫ (translT G θy₀.pt).left) z J₀ *
          gm ((r ≫ fiberMap hp τ hτ) ≫ (fst T₀ G).left) z ⊤ c₀ ↔
      tval θx r z J * tval θy (r ≫ (translT A θx.pt).left) z J =
        tval θy r z J * tval θx (r ≫ (translT A θy.pt).left) z J * gm (r ≫ (fst T A).left) z ⊤ c) := by
    intro Z r z J₀ J hG hJ
    have t : ∀ (x : T ⟶ A) (x₀ : T₀ ⟶ G), τ ≫ x₀.left = x.left ≫ φ →
        (r ≫ fiberMap hp τ hτ) ≫ (translT G x₀).left = (r ≫ (translT A x).left) ≫ fiberMap hp τ hτ :=
      fun x x₀ h => (Category.assoc _ _ _).trans
        ((congrArg (r ≫ ·) (fiberMap_transl hp τ hτ x x₀ h).symm).trans (Category.assoc _ _ _).symm)
    have g : gm ((r ≫ fiberMap hp τ hτ) ≫ (fst T₀ G).left) z ⊤ c₀ = gm (r ≫ (fst T A).left) z ⊤ c := by
      rw [Category.assoc, fiberMap_fst, ← Category.assoc, hcc]
    have s : ∀ x : T ⟶ A, (r ≫ (translT A x).left) ≫ (snd T A).left = r ≫ (translPt A x).left := fun x => by
      rw [Category.assoc, ← Over.comp_left, translT, lift_snd]
    have q : (r ≫ (translT A θx.pt).left) ≫ (translPt A θy.pt).left =
        (r ≫ (translT A θy.pt).left) ≫ (translPt A θx.pt).left := by
      rw [Category.assoc, Category.assoc, transl_commute hc]
    rw [t _ _ hx, t _ _ hy, g, mx Z _ z J₀ J hG hJ, mx Z _ z J₀ J hG hJ, my Z _ z J₀ J hG hJ, my Z _ z J₀ J hG hJ,
      s, s, q]
    simp only [zpow_neg]
    exact cancel_iff _ _ _ _ _ _ _ _ _
  rw [commIsOf_iff hL₀, commIsOf_iff hL₁]
  constructor
  · intro H Z r₀ z J₀ hG
    obtain ⟨χ, -, h₂⟩ := exists_fiberMap_inv hp τ hτ
    choose J hJ using fun ψ : Z ⟶ A.left => exists_chart hL₁ (ψ z)
    have e : (r₀ ≫ χ) ≫ fiberMap hp τ hτ = r₀ := by rw [Category.assoc, h₂, Category.comp_id]
    have := (key Z (r₀ ≫ χ) z J₀ J hG hJ).2 (H Z _ z J hJ)
    rwa [e] at this
  · intro H Z r z J hJ
    choose J₀ hG using fun ψ : Z ⟶ G.left => exists_chart hL₀ (ψ z)
    exact (key Z r z J₀ J hG hJ).1 (H Z _ z J₀ hG)

end GlobalTheory.WeilPull
