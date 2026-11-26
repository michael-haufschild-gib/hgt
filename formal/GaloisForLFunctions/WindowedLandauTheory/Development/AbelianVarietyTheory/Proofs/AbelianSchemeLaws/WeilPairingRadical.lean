import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.WeilTranslationGenerator
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.InvariantGeneratorDescent
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IsogenyEtaleTranslation.GroupMultiplicationEtale

/-! A torsion point in the radical of the Weil pairing has trivial translation
difference, by descent along the étale multiplication map. -/

open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.CommPairing

open GrpTangent (mulN comp_mulN finiteEtaleSurjective_mulN)

attribute [local instance] Over.cartesianMonoidalCategory

/-- If every Weil scalar of a torsion point is one, the translation difference
of the relatively ample bundle has a global generator. -/
theorem exists_gen_translation_of_trivial_weil {K : Type} [Field K] [IsAlgClosed K]
    {A : Over (Spec (.of K))} [GrpObj A] {L : LB A.left}
    (hA : IsAbelianScheme A) (hL : L.IsLB) (hAmp : RelAmple A L) (n : ℕ) (hn : (n : K) ≠ 0)
    (x : 𝟙_ (Over (Spec (.of K))) ⟶ A) (hx : x ^ n = 1)
    (hpair : ∀ (y : 𝟙_ (Over (Spec (.of K))) ⟶ A), y ^ n = 1 →
      WeilIs A L (n : ℤ) x y 1) :
    ∃ v : (LB.LinComb L (K := Fin 2) ![((toUnit A ≫ x) * 𝟙 A).left, 𝟙 A.left] ![1, -1]).Gen,
      v.IsGen := by
  let S := Spec (.of K)
  let T := 𝟙_ (Over S)
  let Q := T ⊗ A
  letI := hA.comm
  letI := hA.smooth
  letI := hA.proper
  letI := hA.geomConnected
  letI : IsReduced A.left := GlobalTheory.isReduced_of_smooth_of_isReduced A.hom
  letI : Subsingleton T.left := inferInstanceAs (Subsingleton (PrimeSpectrum K))
  letI : Nonempty T.left := inferInstanceAs (Nonempty (PrimeSpectrum K))
  let q := mulN A n
  have hunit : IsUnit (n : Γ(S, ⊤)) := by
    simpa using (Ne.isUnit hn).map (Scheme.ΓSpecIso (.of K)).inv.hom
  obtain ⟨hq, hq', hq''⟩ := finiteEtaleSurjective_mulN A hunit
  letI : IsFinite q.left := hq
  letI : Etale q.left := hq'
  letI : Surjective q.left := hq''
  obtain ⟨u, hu, hcov⟩ := exists_translation_generator_with_weil hA hL hAmp n x hx
  let p : A ⟶ T := toUnit A
  let σ : A ⟶ Q := lift p (𝟙 A)
  let f : Fin 2 → (A.left ⟶ A.left) := ![((p ≫ x) * 𝟙 A).left, 𝟙 A.left]
  let F : Fin 2 → (Q.left ⟶ A.left) := ![((snd T A ^ n) * (fst T A ≫ x)).left, (snd T A ^ n).left]
  let d : Fin 2 → ℤ := ![1, -1]
  have hfst : σ ≫ fst T A = p := lift_fst _ _
  have hsnd : σ ≫ snd T A = 𝟙 A := lift_snd _ _
  have hpow : σ ≫ snd T A ^ n = q :=
    (MonObj.comp_pow (snd T A) n σ).trans (congrArg (· ^ n) hsnd)
  have hf (i : Fin 2) : σ.left ≫ F i = q.left ≫ f i := by
    fin_cases i
    · change (σ ≫ ((snd T A ^ n) * (fst T A ≫ x))).left =
        (q ≫ ((p ≫ x) * 𝟙 A)).left
      have hqP : q ≫ p = p := comp_toUnit q
      congr 1
      rw [MonObj.comp_mul, MonObj.comp_mul, hpow, Category.comp_id, ← Category.assoc σ, hfst,
        ← Category.assoc q, hqP, _root_.mul_comm q]
    · exact congrArg Over.Hom.left (hpow.trans (Category.comp_id q).symm)
  obtain ⟨s, hs, hsval⟩ := exists_gen_of_formEq hL (g := fun i => q.left ≫ f i) (d := d)
    (fun U _ k => Finset.prod_congr rfl fun i _ => congrArg (fun v => k v ^ d i) (hf i))
    (LB.pullGen L F d u σ.left) (hu.pullGen F d σ.left)
  refine FlatDescent.exists_generator_of_kernel_translation_invariant q hL f d hs fun y hy z J hJ => ?_
  let τ : A ⟶ A := (toUnit A ≫ y) * 𝟙 A
  let ty : Q ⟶ Q := translT A y
  have hy' : y ^ n = 1 := (comp_mulN y n).symm.trans hy
  have h := val_corr hJ (hcov y 1 hy' (hpair y hy')) σ.left
  have he : τ ≫ σ = σ ≫ ty := by
    apply CartesianMonoidalCategory.hom_ext
    · exact toUnit_unique _ _
    · change (τ ≫ σ) ≫ snd T A = (σ ≫ lift (fst T A) (translPt A y)) ≫ snd T A
      rw [Category.assoc, Category.assoc, hsnd, lift_snd, Category.comp_id]
      change _ = σ ≫ ((fst T A ≫ y) * snd T A)
      rw [MonObj.comp_mul, ← Category.assoc σ, hfst, hsnd]
  have hval : val u (σ.left ≫ ty.left) z J = val u σ.left z J := by
    simpa only [val_pull hJ, val_mul hJ, val_constGen, map_one, _root_.mul_one] using h
  calc
    _ = val u (τ.left ≫ σ.left) z J := (hsval A.left τ.left z J hJ).trans (val_pull hJ u _ _)
    _ = val u (σ.left ≫ ty.left) z J := congrArg (fun r => val u r z J) (congrArg Over.Hom.left he)
    _ = val u σ.left z J := hval
    _ = _ := ((hsval A.left (𝟙 A.left) z J hJ).trans
      ((val_pull hJ u _ _).trans (congrArg (fun r => val u r z J) (Category.id_comp σ.left)))).symm

end GlobalTheory.CommPairing
