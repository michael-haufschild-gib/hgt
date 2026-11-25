import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.GradedLocalizationCriterion
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.GradedTwistPowerAction
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.InvertibleTwistPowers
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.TwistGlobalExtension

/-! Restricting the graded sections to a coordinate intersection localizes at its coordinate product. -/

open AlgebraicGeometry CategoryTheory MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out

namespace GlobalTheory.LineBundleSections

variable {R : Type} [CommRing R] {X : Scheme.{0}} [CompactSpace X] [X.IsSeparated]
  (f : X ⟶ Spec (CommRingCat.of R)) {M H : LB X} (hM : M.IsLB) (hH : H.IsLB)
  {ι : Type} (s : ι → H.Sec)

theorem isLocalizedModule_gradedTwistSections (I : Finset ι) :
    IsLocalizedModule.Away (xProd R I) (gradedTwistSections_res f M s
      (le_top : nonzeroLocus (sectionProduct s I) ≤ ⊤)) := by
  let σ := sectionProduct s I
  let V := nonzeroLocus σ
  let h₀ := twistSections_commute f M ⊤ s
  let h₁ := twistSections_commute f M V s
  let ρ := gradedTwistSections_res f M s (le_top : V ≤ ⊤)
  have hgrade : IsGradedMap (GrSum.grading h₀) (GrSum.grading h₁) ρ :=
    gradedTwistSections_res_isGraded f M s le_top
  have hdeg : xProd R I ∈ polyGrading ι R ((1 : ℤ) * I.card) := by
    simpa only [pow_one] using xProd_pow_mem R I 1
  have act (t : ℤ) (x : TwistSections f M H V t) :
      xProd R I • GrSum.of h₁ t x = GrSum.of h₁ (t + (1 : ℤ) * I.card)
        (mulTwistPower M σ 1 t V x) := by
    simpa only [pow_one] using gradedTwistSections_xProd_pow f M V s I 1 t x
  refine isLocalizedModuleAway_of_graded hdeg hgrade ?_ ?_ ?_ ?_
  · intro t y hy hzero
    obtain ⟨x, rfl⟩ := (GrSum.mem_grading h₁).1 hy
    rw [act] at hzero
    have h₁zero := (GrSum.of_injective h₁ _) (hzero.trans (map_zero _).symm)
    have hx := (mulTwistPower_bijective (M := M) σ (le_rfl : V ≤ nonzeroLocus σ) 1).1
      (h₁zero.trans (map_zero _).symm)
    rw [hx, map_zero]
  · intro t y hy
    obtain ⟨x, rfl⟩ := (GrSum.mem_grading h₁).1 hy
    obtain ⟨a, ha⟩ := (mulTwistPower_bijective (M := M) σ (le_rfl : V ≤ nonzeroLocus σ) 1).2 x
    exact ⟨GrSum.of h₁ t a, GrSum.of_mem_grading h₁ t a,
      (act t a).trans (congrArg (GrSum.of h₁ _) ha)⟩
  · intro t y hy
    obtain ⟨x, rfl⟩ := (GrSum.mem_grading h₁).1 hy
    obtain ⟨k, b, hb⟩ := exists_global_lift_mulTwistPower hM hH σ x
    refine ⟨k, GrSum.of h₀ _ b, ?_⟩
    rw [gradedTwistSections_xProd_pow, gradedTwistSections_res_of]
    exact congrArg (GrSum.of h₁ _) hb.symm
  · intro t y hy hz
    obtain ⟨x, rfl⟩ := (GrSum.mem_grading h₀).1 hy
    change gradedTwistSections_res f M s (le_top : V ≤ ⊤) (GrSum.of h₀ t x) = 0 at hz
    rw [gradedTwistSections_res_of] at hz
    have hx := (GrSum.of_injective h₁ t) (hz.trans (map_zero _).symm)
    obtain ⟨k, hk⟩ := exists_pow_mulTwistPower_eq_zero hM hH σ x hx
    exact ⟨k, by rw [gradedTwistSections_xProd_pow, hk, map_zero]⟩

end GlobalTheory.LineBundleSections
