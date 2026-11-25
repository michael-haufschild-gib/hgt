import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.LineBundleSectionPullback
import Mathlib.Tactic.LinearCombination

/-! Local primitives for a Čech one-cocycle differ by a section of the structure sheaf. -/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.LineBundleSections

namespace GlobalTheory.CechOne

variable {Z : Scheme.{0}}

theorem sections_ext_on_cover {J : Type} {N : Z.Opens} (W : J → Z.Opens) (hc : N ≤ iSup W) (x y : Γ(Z, N))
    (h : ∀ j, resG _ (inf_le_left : N ⊓ W j ≤ N) x = resG _ inf_le_left y) : x = y := by
  refine Z.sheaf.eq_of_locally_eq' (fun j => N ⊓ W j) N (fun j => homOfLE inf_le_left) ?_ x y h
  rw [← inf_iSup_eq]
  exact le_inf le_rfl hc

variable {I : Type} (V : I → Z.Opens) (φ : ∀ a b, Γ(Z, V a ⊓ V b))

def IsCocycle : Prop :=
  ∀ a b d (N : Z.Opens) (ha : N ≤ V a) (hb : N ≤ V b) (hd : N ≤ V d),
    resG _ (le_inf ha hb) (φ a b) + resG _ (le_inf hb hd) (φ b d) = resG _ (le_inf ha hd) (φ a d)

def Splits (O : Z.Opens) (ψ : ∀ a, Γ(Z, O ⊓ V a)) : Prop :=
  ∀ a b (N : Z.Opens) (hO : N ≤ O) (ha : N ≤ V a) (hb : N ≤ V b),
    resG _ (le_inf ha hb) (φ a b) = resG _ (le_inf hO ha) (ψ a) - resG _ (le_inf hO hb) (ψ b)

def IsDifference {O O' P : Z.Opens} (ψ : ∀ a, Γ(Z, O ⊓ V a)) (ψ' : ∀ a, Γ(Z, O' ⊓ V a))
    (hO : P ≤ O) (hO' : P ≤ O') (c : Γ(Z, P)) : Prop :=
  ∀ a (M : Z.Opens) (hM : M ≤ P) (ha : M ≤ V a),
    resG _ hM c = resG _ (le_inf (hM.trans hO) ha) (ψ a) - resG _ (le_inf (hM.trans hO') ha) (ψ' a)

variable {V φ}

theorem exists_difference (hV : ⨆ a, V a = ⊤) {O O' P : Z.Opens} {ψ : ∀ a, Γ(Z, O ⊓ V a)}
    {ψ' : ∀ a, Γ(Z, O' ⊓ V a)} (h : Splits V φ O ψ) (h' : Splits V φ O' ψ')
    (hO : P ≤ O) (hO' : P ≤ O') : ∃ c : Γ(Z, P), IsDifference V ψ ψ' hO hO' c := by
  obtain ⟨c, hc⟩ := exists_fun_of_cover (fun a => P ⊓ V a) (fun a => inf_le_left)
    (by rw [← inf_iSup_eq, hV]; simp)
    (fun a => resG _ (inf_le_inf_right _ hO) (ψ a) - resG _ (inf_le_inf_right _ hO') (ψ' a)) (by
      intro a b
      have hP : P ⊓ V a ⊓ (P ⊓ V b) ≤ P := inf_le_left.trans inf_le_left
      have ha : P ⊓ V a ⊓ (P ⊓ V b) ≤ V a := inf_le_left.trans inf_le_right
      have hb : P ⊓ V a ⊓ (P ⊓ V b) ≤ V b := inf_le_right.trans inf_le_right
      have e1 := h a b _ (hP.trans hO) ha hb
      have e2 := h' a b _ (hP.trans hO') ha hb
      simp only [map_sub, resG_resG]
      linear_combination e2 - e1)
  refine ⟨c, fun a M hM ha => ?_⟩
  have := congrArg (resG _ (le_inf hM ha)) (hc a)
  simpa only [map_sub, resG_resG] using this

theorem splittings_glue {J : Type} (O : J → Z.Opens) (ψ : ∀ j a, Γ(Z, O j ⊓ V a))
    (h : ∀ j, Splits V φ (O j) (ψ j)) (g : ∀ j, Γ(Z, O j))
    (hg : ∀ j k a (M : Z.Opens) (hj : M ≤ O j) (hk : M ≤ O k) (ha : M ≤ V a),
      resG _ (le_inf hj ha) (ψ j a) - resG _ (le_inf hk ha) (ψ k a) = resG _ hj (g j) - resG _ hk (g k))
    (O₀ : Z.Opens) (hc : O₀ ≤ iSup O) : ∃ χ, Splits V φ O₀ χ := by
  have key : ∀ a, ∃ χ : Γ(Z, O₀ ⊓ V a), ∀ j,
      resG _ (inf_le_left : O₀ ⊓ V a ⊓ O j ≤ O₀ ⊓ V a) χ =
        resG _ (le_inf inf_le_right (inf_le_left.trans inf_le_right)) (ψ j a) -
          resG _ inf_le_right (g j) := by
    intro a
    refine exists_fun_of_cover (fun j => O₀ ⊓ V a ⊓ O j) (fun j => inf_le_left) ?_ _ ?_
    · rw [← inf_iSup_eq]
      exact le_inf le_rfl (inf_le_left.trans hc)
    · intro j k
      have e := hg j k a (O₀ ⊓ V a ⊓ O j ⊓ (O₀ ⊓ V a ⊓ O k)) (inf_le_left.trans inf_le_right)
        (inf_le_right.trans inf_le_right) (inf_le_left.trans (inf_le_left.trans inf_le_right))
      simp only [map_sub, resG_resG]
      linear_combination e
  choose χ hχ using key
  refine ⟨χ, fun a b N hO ha hb => sections_ext_on_cover O (hO.trans hc) _ _ fun j => ?_⟩
  have e1 := congrArg (resG _ (inf_le_inf_right (O j) (le_inf hO ha))) (hχ a j)
  have e2 := congrArg (resG _ (inf_le_inf_right (O j) (le_inf hO hb))) (hχ b j)
  have e3 := h j a b (N ⊓ O j) inf_le_right (inf_le_left.trans ha) (inf_le_left.trans hb)
  simp only [map_sub, resG_resG] at e1 e2 ⊢
  linear_combination e3 - e1 + e2

theorem pullback_difference_of_coboundary (hV : ⨆ a, V a = ⊤) {T : Scheme.{0}} (f : T ⟶ Z)
    (ρ : ∀ a, Γ(T, f ⁻¹ᵁ V a))
    (hρ : ∀ a b, (f.app (V a ⊓ V b)).hom (φ a b) =
      resG _ (f.preimage_mono inf_le_left) (ρ a) - resG _ (f.preimage_mono inf_le_right) (ρ b))
    {J : Type} (O : J → Z.Opens) (ψ : ∀ j a, Γ(Z, O j ⊓ V a))
    (h : ∀ j, Splits V φ (O j) (ψ j)) (N : J → T.Opens) (hN : ∀ j, N j ≤ f ⁻¹ᵁ O j) :
    ∃ x : ∀ j, Γ(T, N j), ∀ j k (P : Z.Opens) (hj : P ≤ O j) (hk : P ≤ O k) (c : Γ(Z, P)),
      IsDifference V (ψ j) (ψ k) hj hk c → ∀ (M : T.Opens) (hMj : M ≤ N j) (hMk : M ≤ N k)
        (hM : M ≤ f ⁻¹ᵁ P), (f.appLE P M hM).hom c = resG _ hMj (x j) - resG _ hMk (x k) := by
  have hV' : ⨆ a, f ⁻¹ᵁ V a = ⊤ := by rw [← f.preimage_iSup, hV]; rfl
  let φ' : ∀ a b, Γ(T, f ⁻¹ᵁ V a ⊓ f ⁻¹ᵁ V b) := fun a b =>
    (f.appLE (V a ⊓ V b) _ (by rw [f.preimage_inf])).hom (φ a b)
  let ρ' : ∀ a, Γ(T, ⊤ ⊓ f ⁻¹ᵁ V a) := fun a => resG _ inf_le_right (ρ a)
  have h1 : Splits (fun a => f ⁻¹ᵁ V a) φ' ⊤ ρ' := by
    intro a b M _ ha hb
    have hM : M ≤ f ⁻¹ᵁ (V a ⊓ V b) := by rw [f.preimage_inf]; exact le_inf ha hb
    have := congrArg (resG _ hM) (hρ a b)
    rw [f.app_eq_appLE] at this
    simpa only [φ', ρ', resG_appLE, resG_resG, map_sub] using this
  let ψ' : ∀ j a, Γ(T, N j ⊓ f ⁻¹ᵁ V a) := fun j a =>
    (f.appLE (O j ⊓ V a) _ (by rw [f.preimage_inf]; exact inf_le_inf_right _ (hN j))).hom (ψ j a)
  have h2 : ∀ j, Splits (fun a => f ⁻¹ᵁ V a) φ' (N j) (ψ' j) := by
    intro j a b M hj ha hb
    have hM : M ≤ f ⁻¹ᵁ (O j ⊓ (V a ⊓ V b)) := by
      rw [f.preimage_inf, f.preimage_inf]; exact le_inf (hj.trans (hN j)) (le_inf ha hb)
    have := congrArg (f.appLE _ M hM).hom (h j a b (O j ⊓ (V a ⊓ V b)) inf_le_left
      (inf_le_right.trans inf_le_left) (inf_le_right.trans inf_le_right))
    simpa only [φ', ψ', resG_appLE, appLE_resG, map_sub] using this
  choose x hx using fun j => exists_difference hV' (h2 j) h1 le_rfl le_top
  refine ⟨x, fun j k P hj hk c hc M hMj hMk hM => sections_ext_on_cover (fun a => f ⁻¹ᵁ V a) (by rw [hV']; exact le_top)
    _ _ fun a => ?_⟩
  have e1 := hx j a (M ⊓ f ⁻¹ᵁ V a) (inf_le_left.trans hMj) inf_le_right
  have e2 := hx k a (M ⊓ f ⁻¹ᵁ V a) (inf_le_left.trans hMk) inf_le_right
  have hM' : M ⊓ f ⁻¹ᵁ V a ≤ f ⁻¹ᵁ (P ⊓ V a) := by
    rw [f.preimage_inf]; exact inf_le_inf_right _ hM
  have e3 := congrArg (f.appLE _ _ hM').hom (hc a (P ⊓ V a) inf_le_left inf_le_right)
  simp only [ψ', ρ', resG_appLE, appLE_resG, map_sub, resG_resG] at e1 e2 e3 ⊢
  linear_combination e3 - e1 + e2

end GlobalTheory.CechOne
