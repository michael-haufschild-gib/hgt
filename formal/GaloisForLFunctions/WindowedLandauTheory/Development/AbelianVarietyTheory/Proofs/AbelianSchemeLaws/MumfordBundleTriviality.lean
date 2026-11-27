import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.MumfordBundleFibres
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.CubeGeneratorRestriction

/-! Triviality of the universal translation difference detects the identity
on affine test schemes, including nonreduced tests. -/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.MumfordFibre

attribute [local instance] Over.cartesianMonoidalCategory

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left}

/-- Along the identity section, the two factors have the same pullback. -/
theorem exists_gen_at_identity (hL : L.IsLB) {Y : Scheme.{0}}
    (q : Y ⟶ (A ⊗ A).left) (s : Y ⟶ S)
    (h : q ≫ (fst A A).left = s ≫ η[A].left) :
    ∃ v : ((translDiff A L (𝟙 A)).pull q).Gen, v.IsGen := by
  let Q : Over.mk (q ≫ (A ⊗ A).hom) ⟶ A ⊗ A := Over.homMk q rfl
  have hs : s = q ≫ (A ⊗ A).hom := by
    rw [← Over.w (fst A A), ← Category.assoc, h, Category.assoc]
    have hbase : (η[A].left : S ⟶ A.left) ≫ A.hom = 𝟙 S := Over.w η[A]
    exact (Category.comp_id s).symm.trans (congrArg (fun m : S ⟶ S => s ≫ m) hbase.symm)
  have h₀ : Q ≫ fst A A = 1 := by
    ext1
    exact h.trans (congrArg (· ≫ η[A].left) hs)
  have hm : q ≫ (translPt A (𝟙 A)).left = q ≫ (snd A A).left := by
    change (Q ≫ translPt A (𝟙 A)).left = (Q ≫ snd A A).left
    apply congrArg Over.Hom.left
    rw [translPt, Category.comp_id, ← Hom.mul_def, MonObj.comp_mul, h₀, _root_.one_mul]
  let f : Fin 2 → ((A ⊗ A).left ⟶ A.left) := ![(translPt A (𝟙 A)).left, (snd A A).left]
  let d : Fin 2 → ℤ := ![1, -1]
  apply (AbLaw.Cube.trivial_pull_linComb L hL f d q).mpr
  obtain ⟨v, hv, -⟩ := AbLaw.Cube.exists_gen_of_cancellation L hL (fun k => q ≫ f k) d
    (fun U _ k => by
      rw [Fin.prod_univ_two]
      change k (q ≫ (translPt A (𝟙 A)).left) ^ (1 : ℤ) *
        k (q ≫ (snd A A).left) ^ (-1 : ℤ) = 1
      rw [hm, ← zpow_add]
      simp)
  exact ⟨v, hv⟩

omit [GrpObj A] in
/-- The product over an affine test base is a pullback of the universal
product along the translating point. -/
theorem isPullback_whiskerRight {T : Over S} (x : T ⟶ A) :
    IsPullback (x ▷ A).left (fst T A).left (fst A A).left x.left := by
  have H : IsPullback (snd A A).left (fst A A).left A.hom A.hom :=
    (IsPullback.of_hasPullback A.hom A.hom).flip
  have J : IsPullback (snd T A).left (fst T A).left A.hom T.hom :=
    (IsPullback.of_hasPullback T.hom A.hom).flip
  refine IsPullback.of_right ?_ ?_ H
  · rw [← Over.comp_left, whiskerRight_snd, Over.w]
    exact J
  · rw [← Over.comp_left, whiskerRight_fst, Over.comp_left]

/-- Triviality of the pullback forces the test morphism to be the identity.
The trivial-kernel hypothesis is used on the test scheme itself. -/
theorem eq_identity_of_exists_gen (hL : L.IsLB) (hK : KTriv A L)
    {R : Type} [CommRing R] {t : Spec (.of R) ⟶ S} (x : Over.mk t ⟶ A)
    {Y : Scheme.{0}} {π : Y ⟶ (A ⊗ A).left} {f : Y ⟶ Spec (.of R)}
    (H : IsPullback π f (fst A A).left x.left)
    (h : ∃ v : ((translDiff A L (𝟙 A)).pull π).Gen, v.IsGen) : x = 1 := by
  let p := (x ▷ A).left
  let q := (fst (Over.mk t) A).left
  let J : IsPullback p q (fst A A).left x.left := isPullback_whiskerRight x
  let j := H.lift p q J.w
  have hj : j ≫ π = p := H.lift_fst _ _ _
  let M := translDiff A L (𝟙 A)
  have hM : M.IsLB := hL.linComb _ _
  obtain ⟨v, hv⟩ := h
  obtain ⟨w, hw⟩ := exists_iso_pull_comp hM π j
  have hgen : ∃ u : (M.pull p).Gen, u.IsGen := by
    rw [← hj]
    obtain ⟨v', hv'⟩ := (ChartPull.pull (M.pull π) j).exists_gen hv
    exact hv'.exists_gen_of_iso hw ((hM.pull π).pull j) (hM.pull (j ≫ π))
  let d : Fin 2 → ℤ := ![1, -1]
  let a : Fin 2 → ((A ⊗ A).left ⟶ A.left) := ![(translPt A (𝟙 A)).left, (snd A A).left]
  let b : Fin 2 → (((Over.mk t) ⊗ A).left ⟶ A.left) :=
    ![(translPt A x).left, (snd (Over.mk t) A).left]
  have hab : (fun i => p ≫ a i) = b := by
    funext i
    fin_cases i
    · change (x ▷ A ≫ translPt A (𝟙 A)).left = (translPt A x).left
      apply congrArg Over.Hom.left
      rw [translPt, translPt, Category.comp_id, comp_lift_assoc, whiskerRight_fst, whiskerRight_snd]
    · exact congrArg Over.Hom.left (whiskerRight_snd x A)
  have hb : ∃ u : (LB.LinComb L b d).Gen, u.IsGen := by
    rw [← hab]
    exact (AbLaw.Cube.trivial_pull_linComb L hL a d p).mp hgen
  obtain ⟨u, hu⟩ := hb
  apply hK R t x
  intro y
  let i := (q ⁻¹ᵁ (⊤ : (Spec (.of R)).Opens)).ι
  exact ⟨⊤, trivial, (AbLaw.Cube.trivial_pull_linComb L hL b d i).mpr
    ⟨LB.pullGen L b d u i, hu.pullGen b d i⟩⟩

end GlobalTheory.MumfordFibre
