import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.CubeMultiplicationPullback
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.FiniteMultiplicationFibreSections
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.ProperPrincipalOpens
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem

/-! A positive multiplication map of an abelian scheme with a rigidified symmetric
relatively ample bundle is finite, including in residue characteristics dividing the multiplier. -/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.MulFinite

attribute [local instance] Over.cartesianMonoidalCategory

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left}

/-- A proper endomorphism pulling a relatively ample bundle back to a positive power
has a principal affine cover on each fibre and is therefore finite. -/
theorem isFinite_of_relAmple_pullback [IsProper A.hom] (hL : L.IsLB) (hAmp : RelAmple A L)
    (m : A ⟶ A) (e : ℕ) (he : e ≠ 0)
    (α : LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 A.left, m.left] ![(e : ℤ), -1])) (hα : α.IsGen) :
    IsFinite m.left := by
  have hm : m.left ≫ A.hom = A.hom := Over.w m
  haveI : IsProper (m.left ≫ A.hom) := hm.symm ▸ inferInstanceAs (IsProper A.hom)
  haveI : IsProper m.left := IsProper.of_comp _ A.hom
  suffices LocallyQuasiFinite m.left from IsFinite.of_isProper_of_locallyQuasiFinite _
  refine LocallyQuasiFinite.of_fiberToSpecResidueField _ fun y => ?_
  obtain ⟨U, hU, hyU, -⟩ := exists_isAffineOpen_mem_and_subset (X := S) (U := ⊤)
    (x := A.hom y) trivial
  obtain ⟨n, -, M, s, hcov, hs⟩ := hAmp U hU
  have hy (z : m.left.fiber y) : m.left (m.left.fiberι y z) = y :=
    (m.left.range_fiberι y).le ⟨z, rfl⟩
  let j := (A.hom ⁻¹ᵁ U).ι
  let r : m.left.fiber y ⟶ (A.hom ⁻¹ᵁ U).toScheme :=
    IsOpenImmersion.lift j (m.left.fiberι y) (by
      rintro _ ⟨z, rfl⟩
      rw [Scheme.Opens.range_ι]
      change A.hom (m.left.fiberι y z) ∈ U
      rw [← hm, Scheme.Hom.comp_apply, hy]
      exact hyU)
  have hr : r ≫ j = m.left.fiberι y := IsOpenImmersion.lift_fac _ _ _
  haveI : IsAffineHom (A.left.fromSpecResidueField y) := isAffineHom_fromSpecResidueField _ _
  haveI : IsAffineHom (r ≫ j) := by
    rw [hr]
    exact MorphismProperty.of_isPullback (P := @IsAffineHom)
      (IsPullback.of_hasPullback m.left (A.left.fromSpecResidueField y)).flip inferInstance
  haveI : IsAffineHom r := IsAffineHom.of_comp r j
  obtain ⟨k, hk⟩ := exists_chart hL y
  have hchart (i : Fin (M + 1)) : ∃ a : Γ(m.left.fiber y, ⊤),
      (m.left.fiber y).basicOpen a = r ⁻¹ᵁ nonzeroLocus (s i) :=
    exists_basicOpen_preimage_of_power_section L hL j n (s i) m.left e he α hα r k fun z => by
      rw [← Scheme.Hom.comp_apply r, hr, hy]
      exact hk
  choose a ha using hchart
  have hproper : IsProper (m.left.fiberToSpecResidueField y) :=
    MorphismProperty.of_isPullback (P := @IsProper)
      (IsPullback.of_hasPullback m.left (A.left.fromSpecResidueField y)) inferInstance
  refine @locallyQuasiFinite_of_basicOpen_cover (m.left.fiber y) (A.left.residueField y) _
    (m.left.fiberToSpecResidueField y) hproper _ a ?_ fun i => ?_
  · simp only [ha]
    rw [← Scheme.Hom.preimage_iSup]
    exact (congrArg (fun V => r ⁻¹ᵁ V) hcov).trans rfl
  · rw [ha]
    exact (hs i).1.preimage r

/-- Multiplication by a nonzero natural number is finite. -/
theorem isFinite_mul_of_rigidified_symmetric (hA : IsAbelianScheme A) (hL : L.IsLB)
    (hAmp : RelAmple A L) (hrig : ∃ t : (L.pull η[A].left).Gen, t.IsGen)
    (hsym : ∀ s : S, ∃ U : S.Opens, s ∈ U ∧ ∃ t : (LB.LinComb L (K := Fin 2)
      ![(A.hom ⁻¹ᵁ U).ι ≫ (GrpObj.inv : A ⟶ A).left, (A.hom ⁻¹ᵁ U).ι] ![1, -1]).Gen, t.IsGen)
    (n : ℕ) (hn : n ≠ 0) : IsFinite (((𝟙 A : A ⟶ A) ^ n).left) := by
  letI := hA.proper
  have hgen := GlobalTheory.AbLaw.Cube.gen_mul_pullback_of_relAmple hA hL hAmp hrig hsym n
  rw [← Nat.cast_pow] at hgen
  obtain ⟨α, hα⟩ := hgen
  exact isFinite_of_relAmple_pullback hL hAmp _ (n ^ 2) (pow_ne_zero _ hn) α hα

end GlobalTheory.MulFinite
