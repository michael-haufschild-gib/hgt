import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.HighPowerSections
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.TorsionSectionDecomposition
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.FormalSectionCoordinates
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.FiniteGlobalLineBundleSections
import Mathlib.Algebra.Field.Equiv

/-! A principal polarization over an algebraically closed field has a nonzero section.
An invertible square exponent lies in the progression of powers with nonzero sections. -/

noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.LineBundleSections GlobalTheory.SchemeCohomology
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj

namespace GlobalTheory.MulSplit

attribute [local instance] Over.cartesianMonoidalCategory

private theorem exists_invertible_square_in_progression (K : Type) [Field K] (N k : ℕ) :
    ∃ n j : ℕ, (n : K) ≠ 0 ∧ k ≤ j ∧ (n : ℤ) ^ 2 = 1 + (j : ℤ) * (N : ℤ) := by
  obtain ⟨p, hp⟩ := CharP.exists K
  letI := hp
  have ha : ∃ a : ℕ, k ≤ a ∧ ((1 + N * a : ℕ) : K) ≠ 0 := by
    rcases CharP.char_is_prime_or_zero K p with h | h
    · refine ⟨p * k, Nat.le_mul_of_pos_left _ h.pos, ?_⟩
      push_cast
      rw [CharP.cast_eq_zero K p]
      simp
    · subst p
      letI := CharP.charP_to_charZero K
      exact ⟨k, le_rfl, Nat.cast_ne_zero.2 (by omega)⟩
  obtain ⟨a, hka, hKa⟩ := ha
  refine ⟨1 + N * a, 2 * a + N * a ^ 2, hKa, by omega, ?_⟩
  push_cast
  ring

/-- The section module of a rigidified symmetric relatively ample line bundle
with trivial translation kernel has positive dimension. -/
theorem one_le_finrank_sections {K : Type} [Field K] [IsAlgClosed K]
    {A : Over (Spec (.of K))} [GrpObj A] {L : LB A.left}
    (hA : IsAbelianScheme A) (hL : L.IsLB) (hAmp : RelAmple A L) (hK : KTriv A L)
    (hrig : ∃ t : (L.pull η[A].left).Gen, t.IsGen)
    (hsym : ∀ s : Spec (.of K), ∃ U : (Spec (.of K)).Opens, s ∈ U ∧
      ∃ t : (LB.LinComb L (K := Fin 2)
        ![(A.hom ⁻¹ᵁ U).ι ≫ (GrpObj.inv : A ⟶ A).left, (A.hom ⁻¹ᵁ U).ι] ![1, -1]).Gen, t.IsGen) :
    1 ≤ Module.finrank Γ(Spec (.of K), ⊤) (Sg L A.hom (Finsupp.single (𝟙 A.left) (1 : ℤ))) := by
  let S := Spec (.of K)
  let R := Γ(S, ⊤)
  let D (a : ℤ) : (A.left ⟶ A.left) →₀ ℤ := Finsupp.single (𝟙 A.left) a
  obtain ⟨N, -, k, hk⟩ := exists_nontrivial_high_power_of_relAmple hL hAmp
  obtain ⟨n, j, hn, hj, he⟩ := exists_invertible_square_in_progression K N k
  letI : Nontrivial (Sg L A.hom (D ((n : ℤ) ^ 2))) := he.symm ▸ hk j hj
  haveI : Nontrivial (Sg L A.hom (D 1)) := by
    by_contra! h
    letI : Subsingleton (Sg L A.hom (D 1)) := h
    obtain ⟨e⟩ := sections_mulPull_split hA hL hAmp hK hrig hsym n 1 hn one_ne_zero
    have h1 : (n : ℤ) ^ 2 * ((1 : ℕ) : ℤ) = (n : ℤ) ^ 2 := mul_one _
    haveI : Nontrivial (Sg L A.hom (D ((n : ℤ) ^ 2 * ((1 : ℕ) : ℤ)))) := h1.symm ▸ inferInstance
    exact not_subsingleton _ e.toEquiv.subsingleton
  let eK : R ≃+* K := (Scheme.ΓSpecIso (.of K)).commRingCatIsoToRingEquiv
  letI : Field R := (MulEquiv.isField (Semifield.toIsField K) eK.toMulEquiv).toField
  let f : PUnit → (A.left ⟶ A.left) := fun _ => 𝟙 A.left
  let d : PUnit → ℤ := fun _ => 1
  let M := LB.LinComb L f d
  let W := Γ(toMod M, ⊤)
  letI : Module R W := globalSectionModule A.hom M
  letI : Module K W := sectionBaseModule A.hom (toMod M) ⊤
  letI : Algebra K R := (Scheme.ΓSpecIso (.of K)).inv.hom.toAlgebra
  letI : IsScalarTower K R W := .of_algebraMap_smul fun a w => by
    have e : A.hom.appTop = A.hom.appLE ⊤ ⊤ (by simp) := A.hom.app_eq_appLE
    exact congrArg (fun φ : Γ(S, ⊤) ⟶ Γ(A.left, ⊤) =>
      φ ((Scheme.ΓSpecIso (.of K)).inv a) • w) e
  letI : Module.Finite K W := moduleFinite_globalSections A.hom
    (GlobalTheory.ProjectiveSections.isProjOver_of_relAmple hL hAmp) (hL.linComb f d)
  letI : Module.Finite R W := .of_restrictScalars_finite K R W
  obtain ⟨e⟩ := nonempty_globalSections_equiv_Sg A.hom f d hL
  have hd : dv f d = D 1 := Fintype.sum_unique _
  letI : Module.Finite R (Sg L A.hom (D 1)) := hd ▸ Module.Finite.equiv e
  exact Module.finrank_pos

end GlobalTheory.MulSplit
