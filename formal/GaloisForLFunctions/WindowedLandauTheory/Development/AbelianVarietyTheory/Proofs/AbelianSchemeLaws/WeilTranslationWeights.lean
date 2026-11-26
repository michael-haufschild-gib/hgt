import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.WeilTorsionCharacters
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.FieldTranslationBundles
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.FormalSectionModule

/-! Weil characters give generators for the weight spaces of multiplication pullback. -/

noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.MulSplit GlobalTheory.TwistTranslate
open scoped CategoryTheory.Obj

namespace GlobalTheory.CommPairing

attribute [local instance] Over.cartesianMonoidalCategory

open GrpTangent (mulN comp_mulN)

variable {K : Type} [Field K] [IsAlgClosed K] {A : Over (Spec (.of K))} [GrpObj A] {L : LB A.left}

omit [IsAlgClosed K] in
private theorem translation_gen_on_source (hA : IsAbelianScheme A) (hL : L.IsLB)
    (hAmp : RelAmple A L) (n : ℕ) (x : 𝟙_ (Over (Spec (.of K))) ⟶ A) (hx : x ^ n = 1) :
    let q := (mulN A n).left
    ∃ s : (LB.LinComb L (K := Fin 2) ![q ≫ (translate A x).left, q] ![1, -1]).Gen,
      s.IsGen ∧ ∀ (y : 𝟙_ (Over (Spec (.of K))) ⟶ A) (c : Γ(Spec (.of K), ⊤)ˣ),
        y ^ n = 1 → WeilIs A L (n : ℤ) x y c →
        ∀ (r : A.left ⟶ A.left) (z : A.left) J, Good L z J →
          val s (r ≫ (translate A y).left) z J = val s r z J * gm (r ≫ A.hom) z ⊤ c := by
  let T := 𝟙_ (Over (Spec (.of K)))
  let Q := T ⊗ A
  letI := hA.comm
  letI : Subsingleton T.left := inferInstanceAs (Subsingleton (PrimeSpectrum K))
  letI : Nonempty T.left := inferInstanceAs (Nonempty (PrimeSpectrum K))
  obtain ⟨u, hu, hcov⟩ := exists_translation_generator_with_weil hA hL hAmp n x hx
  let q := mulN A n
  let p : A ⟶ T := toUnit A
  let σ : A ⟶ Q := lift p (𝟙 A)
  let F : Fin 2 → (Q.left ⟶ A.left) := ![((snd T A ^ n) * (fst T A ≫ x)).left, (snd T A ^ n).left]
  let f : Fin 2 → (A.left ⟶ A.left) := ![q.left ≫ (translate A x).left, q.left]
  let d : Fin 2 → ℤ := ![1, -1]
  have hfst : σ ≫ fst T A = p := lift_fst _ _
  have hsnd : σ ≫ snd T A = 𝟙 A := lift_snd _ _
  have hp : σ.left ≫ (fst T A).left = A.hom := congrArg Over.Hom.left hfst
  have hpow : σ ≫ snd T A ^ n = q :=
    (MonObj.comp_pow (snd T A) n σ).trans (congrArg (· ^ n) hsnd)
  have hf (i : Fin 2) : σ.left ≫ F i = f i := by
    fin_cases i
    · change (σ ≫ ((snd T A ^ n) * (fst T A ≫ x))).left = (q ≫ translate A x).left
      congr 1
      rw [TwistTranslate.translate, MonObj.comp_mul, MonObj.comp_mul, hpow, Category.comp_id, ← Category.assoc σ,
        hfst, ← Category.assoc q, comp_toUnit, _root_.mul_comm q]
    · exact congrArg Over.Hom.left hpow
  obtain ⟨s, hs, hsval⟩ := exists_gen_of_formEq hL (g := f) (d := d)
    (fun U _ k => Finset.prod_congr rfl fun i _ => congrArg (fun v => k v ^ d i) (hf i))
    (LB.pullGen L F d u σ.left) (hu.pullGen F d σ.left)
  refine ⟨s, hs, fun y c hy hc r z J hJ => ?_⟩
  let τ := translate A y
  let t := translT A y
  have he : τ ≫ σ = σ ≫ t := by
    apply CartesianMonoidalCategory.hom_ext
    · exact toUnit_unique _ _
    · change (τ ≫ σ) ≫ snd T A = (σ ≫ lift (fst T A) (translPt A y)) ≫ snd T A
      rw [Category.assoc, Category.assoc, hsnd, lift_snd, Category.comp_id]
      change τ = σ ≫ ((fst T A ≫ y) * snd T A)
      rw [MonObj.comp_mul, ← Category.assoc σ, hfst, hsnd]
      rfl
  have hvalue (r' : A.left ⟶ A.left) : val s r' z J = val u (r' ≫ σ.left) z J :=
    (hsval A.left r' z J hJ).trans (val_pull hJ u _ _)
  have h := val_corr hJ (hcov y c hy hc) (r ≫ σ.left)
  simp only [val_pull hJ, val_mul hJ, val_constGen] at h
  have hh : (r ≫ σ.left) ≫ (fst T A).left = r ≫ A.hom :=
    (Category.assoc _ _ _).trans (congrArg (r ≫ ·) hp)
  have he' : τ.left ≫ σ.left = σ.left ≫ t.left := congrArg Over.Hom.left he
  calc
    val s (r ≫ τ.left) z J = val u ((r ≫ τ.left) ≫ σ.left) z J := hvalue _
    _ = val u ((r ≫ σ.left) ≫ t.left) z J := by
      exact congrArg (fun v : A.left ⟶ Q.left => val u v z J)
        ((Category.assoc _ _ _).trans ((congrArg (r ≫ ·) he').trans (Category.assoc _ _ _).symm))
    _ = val u (r ≫ σ.left) z J * gm (r ≫ A.hom) z ⊤ c :=
      h.trans (congrArg (fun v : A.left ⟶ Spec (.of K) =>
        val u (r ≫ σ.left) z J * gm v z ⊤ c) hh)
    _ = val s r z J * gm (r ≫ A.hom) z ⊤ c := congrArg (· * _) (hvalue r).symm

/-- Each torsion character has a generator of that weight in the pullback of a
translation difference with the opposite sign. -/
theorem exists_section_weight_generator (hA : IsAbelianScheme A) (hL : L.IsLB)
    (hAmp : RelAmple A L) (hK : KTriv A L)
    (n : ℕ) (hn : (n : K) ≠ 0)
    (χ : letI := hA.comm
      (powMonoidHom n : (𝟙_ (Over (Spec (.of K))) ⟶ A) →* _).ker →* Γ(Spec (.of K), ⊤)ˣ) :
    letI := hA.comm
    let G := (powMonoidHom n : (𝟙_ (Over (Spec (.of K))) ⟶ A) →* _).ker
    let q := (mulN A n).left
    ∃ b : 𝟙_ (Over (Spec (.of K))) ⟶ A, ∃ u : (Vals L A.hom)ˣ,
      IsG (Finsupp.single q 1 + Finsupp.single (q ≫ (translate A b).left) (-1)) u ∧
      ∀ y : G, pl L (translate A y.1).left (Over.w _) u.val = (χ y).val • u.val := by
  letI := hA.comm
  let T := 𝟙_ (Over (Spec (.of K)))
  let G := (powMonoidHom n : (T ⟶ A) →* (T ⟶ A)).ker
  let q := (mulN A n).left
  obtain ⟨b, ⟨hb, hχ⟩, -⟩ := existsUnique_weil_character hA hL hAmp hK n hn
    (fun x => χ (⟨x.1, x.2⟩ : G)) (fun x y => χ.map_mul (⟨x.1, x.2⟩ : G) ⟨y.1, y.2⟩)
  obtain ⟨s, hs, hcov⟩ := translation_gen_on_source hA hL hAmp n b hb
  obtain ⟨u, hu, huv⟩ := exists_isG (p := A.hom) hL s hs
  have he : dv (![q ≫ (translate A b).left, q] : Fin 2 → (A.left ⟶ A.left)) ![1, -1] =
      Finsupp.single (q ≫ (translate A b).left) 1 + Finsupp.single q (-1) := Fin.sum_univ_two _
  have hu' : IsG (Finsupp.single (q ≫ (translate A b).left) 1 + Finsupp.single q (-1)) u := he ▸ hu
  refine ⟨b, u⁻¹, ?_, ?_⟩
  · convert hu'.inv using 1
    rw [neg_add, ← Finsupp.single_neg, ← Finsupp.single_neg, neg_neg, add_comm]
  · intro y
    funext i
    let τ := (translate A y.1).left
    let j : Idx L A.hom := ⟨(i.1.1, i.1.2.1, i.1.2.2 ≫ τ), i.2.1,
      (Category.assoc _ _ _).trans ((congrArg (i.1.2.2 ≫ ·) (Over.w (translate A y.1))).trans i.2.2)⟩
    have h : val s j.1.2.2 i.1.1 i.1.2.1 =
        val s i.1.2.2 i.1.1 i.1.2.1 * gm A.hom i.1.1 ⊤ (χ y)⁻¹ := by
      have hχy : WeilIs A L (n : ℤ) y.1 b (χ y) := hχ ⟨y.1, y.2⟩
      have h' := hcov y.1 _ y.2 (weilIs_swap_of_local_lifts hA hL hχy)
        i.1.2.2 i.1.1 i.1.2.1 i.2.1
      exact h'.trans (congrArg (fun v : A.left ⟶ Spec (.of K) =>
        val s i.1.2.2 i.1.1 i.1.2.1 * gm v i.1.1 ⊤ (χ y)⁻¹) i.2.2)
    have hv : u.val j = u.val i * (gm A.hom i.1.1 ⊤ (χ y)⁻¹).val :=
      (huv j).trans ((congrArg Units.val h).trans (congrArg (· * _) (huv i).symm))
    have hv' : (u⁻¹).val j = (gm A.hom i.1.1 ⊤ (χ y)).val * (u⁻¹).val i := by
      let evj : (Vals L A.hom)ˣ →* (A.left.presheaf.stalk i.1.1)ˣ :=
        Units.map (Pi.evalRingHom _ j).toMonoidHom
      let evi : (Vals L A.hom)ˣ →* (A.left.presheaf.stalk i.1.1)ˣ :=
        Units.map (Pi.evalRingHom _ i).toMonoidHom
      let g := gm A.hom i.1.1 ⊤
      have hp : evj u = evi u * g (χ y)⁻¹ := Units.ext hv
      have hg : (g (χ y)⁻¹)⁻¹ = g (χ y) := (congrArg (·⁻¹) (map_inv g (χ y))).trans (inv_inv _)
      have hi : evj u⁻¹ = g (χ y) * evi u⁻¹ :=
        (map_inv evj u).trans ((congrArg (·⁻¹) hp).trans
          ((mul_inv_rev _ _).trans (congrArg₂ (· * ·) hg (map_inv evi u).symm)))
      exact congrArg Units.val hi
    change (u⁻¹).val j = ((χ y).val • (u⁻¹).val : Vals L A.hom) i
    rw [Algebra.smul_def, mul_vals, algebraMap_vals,
      gs_unit A.hom i.1.1 ⊤ trivial (χ y)]
    exact hv'

end GlobalTheory.CommPairing
