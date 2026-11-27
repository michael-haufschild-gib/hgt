import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.PrincipalPowerSectionRank
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.PositivePowerVanishing
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.OpenIsoCech
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.CechHomologyZero

/-! A power with one translated factor is itself a translate of a full
power, so its cohomology and section dimension agree with that power. -/

noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory MonObj TopologicalSpace HTGeometry
open GlobalTheory.LineBundleSections GlobalTheory.MulSplit GlobalTheory.ProjectiveSections GlobalTheory.TwistTranslate
open GlobalTheory.SchemeCohomology
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out UpperTheory.Cb
open scoped CategoryTheory.Obj

namespace GlobalTheory.PrincipalSections

attribute [local instance] Over.cartesianMonoidalCategory

/-- A single translated factor preserves the section dimension and higher
cohomology vanishing of a positive power of a principal polarization. -/
theorem field_twist_finrank_and_vanishing {K : Type} [Field K] [IsAlgClosed K]
    {A : Over (Spec (.of K))} [GrpObj A] {L : LB A.left}
    (hA : IsAbelianScheme A) (hL : L.IsLB) (hAmp : RelAmple A L) (hK : KTriv A L)
    (hrig : ∃ t : (L.pull η[A].left).Gen, t.IsGen)
    (hsym : ∀ s : Spec (.of K), ∃ U : (Spec (.of K)).Opens, s ∈ U ∧
      ∃ t : (LB.LinComb L (K := Fin 2)
        ![(A.hom ⁻¹ᵁ U).ι ≫ (GrpObj.inv : A ⟶ A).left, (A.hom ⁻¹ᵁ U).ι] ![1, -1]).Gen, t.IsGen)
    (d : ℕ) [SmoothOfRelativeDimension d A.hom]
    (x : 𝟙_ (Over (Spec (.of K))) ⟶ A) (j : ℕ) (hj : 1 ≤ j) :
    let M := LB.LinComb L ![𝟙 A.left, (translate A x).left] ![(j : ℤ) - 1, 1]
    letI := sectionBaseModule A.hom (toMod M) ⊤
    Module.finrank K Γ(toMod M, ⊤) = j ^ d ∧
      ∀ n : ℕ, Subsingleton (CohomologyOn (toMod M) ⊤ (n + 1)) := by
  let F : Fin 2 → (A.left ⟶ A.left) := ![𝟙 A.left, (translate A x).left]
  let a : Fin 2 → ℤ := ![(j : ℤ) - 1, 1]
  let M := LB.LinComb L F a
  let b : PUnit → ℤ := fun _ => (j : ℤ)
  let P := LB.LinComb L (fun _ : PUnit => 𝟙 A.left) b
  have hM : M.IsLB := hL.linComb _ _
  have hP : P.IsLB := hL.linComb _ _
  letI := sectionBaseModule A.hom (toMod M) ⊤
  letI := sectionBaseModule A.hom (toMod P) ⊤
  obtain ⟨y, -, s, hs⟩ := exists_gen_twisted_pow_translate hA hL hAmp hrig hsym j (Nat.ne_zero_of_lt hj) x
  let τ := translate A y
  let B := LB.LinComb L (fun _ : PUnit => τ.left) b
  have hB : B.IsLB := hL.linComb _ _
  have hcomp (u v : 𝟙_ (Over (Spec (.of K))) ⟶ A) (h : v * u = 1) :
      (translate A u).left ≫ (translate A v).left = 𝟙 A.left :=
    congrArg Over.Hom.left ((translate_comp u v).trans ((congrArg (translate A) h).trans translate_one))
  letI : IsIso τ.left := ⟨⟨(translate A y⁻¹).left, hcomp _ _ (inv_mul_cancel _), hcomp _ _ (mul_inv_cancel _)⟩⟩
  obtain ⟨v, hv⟩ := exists_iso_of_formal_difference_gen hL F (fun _ : PUnit => τ.left) a b
    (fun G _ k => by
      simp only [Fintype.prod_sum_type, Fin.prod_univ_two, Fin.prod_univ_three, Fintype.prod_unique,
        Sum.elim_inl, Sum.elim_inr, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        F, τ, a, b]
      rfl) s hs
  let Q : ChartPull B P τ.left := by
    have he : (fun _ : PUnit => τ.left ≫ 𝟙 A.left) = fun _ => τ.left := funext fun _ => Category.comp_id _
    exact (congrArg (fun g => ChartPull (LB.LinComb L g b) P τ.left) he).mp
      (ChartPull.linComb L (fun _ : PUnit => 𝟙 A.left) b τ.left)
  obtain ⟨w, hw⟩ := (ChartPull.pull P τ.left).iso_of_common Q hP
  obtain ⟨m, i, hi, hif⟩ := isProjOver_of_relAmple hL hAmp
  letI := hi
  let U (l : Fin (m + 1)) := i ⁻¹ᵁ PSpace.coordinateOpen K m l
  let V (l : Fin (m + 1)) := τ.left ⁻¹ᵁ U l
  have hU : ⨆ l, U l = ⊤ := i.iSup_preimage_eq_top (PSpace.iSup_coordinateOpen K m)
  have hV : ⨆ l, V l = ⊤ := τ.left.iSup_preimage_eq_top hU
  have ha (I : Finset (Fin (m + 1))) (hI : I.Nonempty) : IsAffineOpen (coverInter ⊤ U I) :=
    (coverInter_pull (π := i) (PSpace.coordinateOpen K m) I).symm ▸
      (PSpace.isAffineOpen_coordinateInter K m hI).preimage i
  have ha' (I : Finset (Fin (m + 1))) (hI : I.Nonempty) : IsAffineOpen (coverInter ⊤ V I) :=
    (coverInter_pull (π := τ.left) U I).symm ▸ (ha I hI).preimage τ.left
  let E := cechPullbackIso_of_isIso A.hom hP τ.left U ha
  let e := E ≪≫ eqToIso (congrArg (fun f => cech f (toMod (P.pull τ.left)) V) (Over.w τ)) ≪≫
    cechIsoOfIsGen A.hom V (hP.pull τ.left) hB hw ≪≫ cechIsoOfIsGen A.hom V hB hM hv
  constructor
  · have hd : dv (fun _ : PUnit => 𝟙 A.left) b = Finsupp.single (𝟙 A.left) (j : ℤ) := Fintype.sum_unique _
    let eP := cechHomologyZeroEquiv A.hom (toMod P) U hU
    let eM := cechHomologyZeroEquiv A.hom (toMod M) V hV
    let E₀ := eP.symm.trans ((HomologicalComplex.homologyMapIso e 0).toLinearEquiv.trans eM)
    exact E₀.finrank_eq.symm.trans ((finrank_formalSections A.hom _ b hL hd).symm.trans
      (finrank_sections_pow_eq_pow hA hL hAmp hK hrig hsym d j hj))
  · intro n
    have hvan := cohomology_positive_power_subsingleton hA hL hAmp hrig hsym j hj n
    have he := (exactAt_cech_iff_subsingleton_cohomology A.hom hP U hU.ge ha (n + 1)).mpr hvan
    exact (exactAt_cech_iff_subsingleton_cohomology A.hom hM V hV.ge ha' (n + 1)).mp (he.of_iso e)

end GlobalTheory.PrincipalSections
