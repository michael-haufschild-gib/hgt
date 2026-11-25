import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.CechOneSplitting
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.LineBundleDefectSlices

/-! The square-zero obstruction is a Čech class on the closed fibre. -/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory.SchemeCohomology GlobalTheory.LineBundleSections

namespace GlobalTheory.AbLaw.SmallExtension

variable {R : Type} [CommRing R] [IsLocalRing R] {X Z T : Scheme.{0}} {L : LB X}
  {p : X ⟶ Spec (CommRingCat.of R)} {ε : R}
  {I : Type} {W : I → X.Opens} {c : I → L.ι} {hle : ∀ i, W i ≤ L.U (c i)}
  {u : ∀ i, Γ(X, W i)} {α : ∀ i j, Γ(X, W i ⊓ W j)}

/-- The additive defects after restriction to the closed fibre. -/
def fibreDefect (q : Z ⟶ X) (α : ∀ i j, Γ(X, W i ⊓ W j)) (i j : I) :
    Γ(Z, q ⁻¹ᵁ W i ⊓ q ⁻¹ᵁ W j) :=
  q.appLE (W i ⊓ W j) _ (fun _ hx => hx) (α i j)

private theorem resG_app {Y Y' : Scheme.{0}} (q : Y' ⟶ Y)
    {U : Y.Opens} {V : Y'.Opens} (h : V ≤ q ⁻¹ᵁ U) (x : Γ(Y, U)) :
    resG Y' h (q.app U x) = q.appLE U V h x :=
  (congrArg (resG Y' h) (ConcreteCategory.congr_hom (q.app_eq_appLE (U := U)) x)).trans
    (resG_appLE le_rfl h x)

theorem LiftDefect.isCocycle_fibre [Flat p] [X.IsSeparated]
    (h : LiftDefect (p := p) (ε := ε) W c hle u α) (hL : L.IsLB)
    (haff : ∀ i, IsAffineOpen (W i)) (hu : ∀ i, IsUnit (u i))
    (hne : ε ≠ 0) (hm : ε ∈ IsLocalRing.maximalIdeal R)
    (hann : ∀ a ∈ IsLocalRing.maximalIdeal R, a * ε = 0)
    {q : Z ⟶ X} {s : Z ⟶ Spec (CommRingCat.of (IsLocalRing.ResidueField R))}
    (H : IsPullback q s p (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))) :
    GlobalTheory.CechOne.IsCocycle (fun i => q ⁻¹ᵁ W i) (fibreDefect q α) := by
  intro i j k N hi hj hk
  let V := W i ⊓ W j ⊓ W k
  have hN : N ≤ q ⁻¹ᵁ V := le_inf (le_inf hi hj) hk
  have e := congrArg (resG Z hN)
    (h.cocycle_on_closed_fibre hL haff hu hne hm hann H i j k)
  rw [map_add] at e
  have hr (a b : I) (ha : N ≤ q ⁻¹ᵁ W a) (hb : N ≤ q ⁻¹ᵁ W b) :
      resG Z (le_inf ha hb) (fibreDefect q α a b) =
        q.appLE (W a ⊓ W b) N (fun z hz => ⟨ha hz, hb hz⟩) (α a b) :=
    resG_appLE (fun _ hx => hx) (le_inf ha hb) (α a b)
  rw [hr i j hi hj, hr j k hj hk, hr i k hi hk]
  have hres (U : X.Opens) (hU : V ≤ U) (z : Γ(X, U)) :
      resG Z hN (q.app V (resG X hU z)) =
        q.appLE U N (hN.trans (q.preimage_mono hU)) z :=
    (resG_app q hN (resG X hU z)).trans (appLE_resG hN hU z)
  have e₁ := hres (W i ⊓ W j) inf_le_left (α i j)
  have e₂ := hres (W j ⊓ W k) (le_inf (inf_le_left.trans inf_le_right) inf_le_right) (α j k)
  have e₃ := hres (W i ⊓ W k) (le_inf (inf_le_left.trans inf_le_left) inf_le_right) (α i k)
  exact (congrArg₂ (· + ·) e₁ e₂).symm.trans (e.trans e₃)

private theorem appLE_congr {A B : Scheme.{0}} {f g : A ⟶ B}
    (e : f = g) (U : B.Opens) {V : A.Opens} (hf : V ≤ f ⁻¹ᵁ U) (hg : V ≤ g ⁻¹ᵁ U) :
    f.appLE U V hf = g.appLE U V hg := by
  subst g
  rfl

/-- On the closed fibre of a flat slice admitting a generator, the obstruction pulls back
to an additive coboundary. -/
theorem LiftDefect.coboundary_on_fibre_slice [X.IsSeparated]
    (h : LiftDefect (p := p) (ε := ε) W c hle u α) (hu : ∀ i, IsUnit (u i))
    (hne : ε ≠ 0) (hm : ε ∈ IsLocalRing.maximalIdeal R)
    (hann : ∀ a ∈ IsLocalRing.maximalIdeal R, a * ε = 0)
    (hc : ⨆ i, W i = ⊤) (haff : ∀ i, IsAffineOpen (W i))
    (a : T ⟶ X) [IsAffineHom a] [Flat (a ≫ p)] (t : (L.pull a).Gen) (ht : t.IsGen)
    {T' : Scheme.{0}} {π : T' ⟶ T} {f : T' ⟶ Spec (CommRingCat.of (R ⧸ Ideal.span {ε}))}
    (H : IsPullback π f (a ≫ p) (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {ε})))))
    (hΓ : Function.Surjective f.appTop)
    {T₀ : Scheme.{0}} {q₀ : T₀ ⟶ T} {s₀ : T₀ ⟶ Spec (CommRingCat.of (IsLocalRing.ResidueField R))}
    (H₀ : IsPullback q₀ s₀ (a ≫ p) (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))))
    {q : Z ⟶ X} (b : T₀ ⟶ Z) (hb : b ≫ q = q₀ ≫ a) :
    ∃ v : ∀ i, Γ(T₀, b ⁻¹ᵁ q ⁻¹ᵁ W i),
      ∀ i j, b.app (q ⁻¹ᵁ W i ⊓ q ⁻¹ᵁ W j) (fibreDefect q α i j) =
        resG T₀ (b.preimage_mono inf_le_left) (v i) -
          resG T₀ (b.preimage_mono inf_le_right) (v j) := by
  obtain ⟨β, hβ⟩ := h.coboundary_on_slice hu (hann ε hm) hc haff a t ht H hΓ
  have he (i : I) : b ⁻¹ᵁ q ⁻¹ᵁ W i = q₀ ⁻¹ᵁ a ⁻¹ᵁ W i := by
    rw [← Scheme.Hom.comp_preimage, hb, Scheme.Hom.comp_preimage]
  refine ⟨fun i => q₀.appLE (a ⁻¹ᵁ W i) (b ⁻¹ᵁ q ⁻¹ᵁ W i) (he i).le (β i), fun i j => ?_⟩
  let M := a ⁻¹ᵁ W i ⊓ a ⁻¹ᵁ W j
  let V := q ⁻¹ᵁ W i ⊓ q ⁻¹ᵁ W j
  let N := b ⁻¹ᵁ V
  have hN : N ≤ q₀ ⁻¹ᵁ M :=
    le_inf ((b.preimage_mono inf_le_left).trans (he i).le)
      ((b.preimage_mono inf_le_right).trans (he j).le)
  have hM : IsAffineOpen M := by
    dsimp only [M]
    rw [← a.preimage_inf]
    exact ((haff i).inf (haff j)).preimage a
  have hz := (mul_scalar_eq_zero_iff H₀ hM hne hann _).1 (hβ i j)
  have e := congrArg (resG T₀ hN) hz
  simp only [map_sub, map_zero, resG_app, appLE_resG, sub_eq_zero] at e
  rw [Scheme.Hom.app_eq_appLE]
  simp only [fibreDefect, resG_appLE]
  refine Eq.trans ?_ e
  let O := W i ⊓ W j
  have hVO : V ≤ q ⁻¹ᵁ O := fun _ h => h
  have hMO : M ≤ a ⁻¹ᵁ O := fun _ h => h
  have h₁ : N ≤ (b ≫ q) ⁻¹ᵁ O := b.preimage_mono hVO
  have h₂ : N ≤ (q₀ ≫ a) ⁻¹ᵁ O := hN.trans (q₀.preimage_mono hMO)
  calc
    _ = (b ≫ q).appLE O N h₁ (α i j) :=
      ConcreteCategory.congr_hom (Scheme.Hom.appLE_comp_appLE b q O V N hVO le_rfl) _
    _ = (q₀ ≫ a).appLE O N h₂ (α i j) :=
      ConcreteCategory.congr_hom (appLE_congr hb O h₁ h₂) _
    _ = _ :=
      (ConcreteCategory.congr_hom (Scheme.Hom.appLE_comp_appLE q₀ a O M N hMO hN) _).symm

end GlobalTheory.AbLaw.SmallExtension
