import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.DehomogenizedKernels
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.DehomogenizedTwistChart
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.LineBundleAffineSections
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.TwistedSectionLocalization
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! On a smooth affine coordinate chart, the dehomogenized line-bundle module is finite projective. -/

open AlgebraicGeometry CategoryTheory MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.SchemeCohomology

namespace GlobalTheory.LineBundleSections

variable {R : Type} [CommRing R] {X : Scheme.{0}} [CompactSpace X] [X.IsSeparated]
  (f : X ⟶ Spec (CommRingCat.of R)) [Smooth f] {M H : LB X} (hM : M.IsLB) (hH : H.IsLB)
  {ι : Type} (s : ι → H.Sec)

private theorem chartAlgebra_smooth {V : X.Opens} (hV : IsAffineOpen V) :
    letI := sectionAlgebra f V
    Algebra.Smooth R Γ(X, V) := by
  let a := (Scheme.ΓSpecIso (CommRingCat.of R)).inv
  let b := f.appLE ⊤ V (by simp)
  have ha : a.hom.Smooth := RingHom.Smooth.of_bijective (ConcreteCategory.bijective_of_isIso a)
  have hb : b.hom.Smooth := f.smooth_appLE (isAffineOpen_top _) hV (by simp)
  exact ha.comp hb

theorem exists_smooth_dehomogenized_twist_chart (i : ι)
    (hV : IsAffineOpen (nonzeroLocus (s i))) (r : ι → Γ(X, nonzeroLocus (s i)))
    (hr : ∀ j k, resG X (inf_le_right : nonzeroLocus (s i) ⊓ H.U k ≤ H.U k) ((s j).f k) =
      resG X inf_le_left (r j) * resG X inf_le_right ((s i).f k))
    (hπ : letI := sectionAlgebra f (nonzeroLocus (s i))
      Function.Surjective (MvPolynomial.aeval (R := R) r)) :
    ∃ (B : Type) (_ : CommRing B) (_ : Algebra R B) (π : MvPolynomial ι R →ₐ[R] B)
      (P : Type) (_ : AddCommGroup P) (_ : Module B P),
      Algebra.Smooth R B ∧ Module.Finite B P ∧ Module.Projective B P ∧
        Function.Surjective π ∧ π (X i) = 1 ∧
        (letI := Module.compHom P π.toRingHom
         Nonempty (QuotSMulTop (X i - 1 : MvPolynomial ι R) (gradedTwistSections f M ⊤ s)
           ≃ₗ[MvPolynomial ι R] P)) := by
  let V := nonzeroLocus (s i)
  letI := sectionAlgebra f V
  let P := TwistSections f M H V 0
  let π : MvPolynomial ι R →ₐ[R] Γ(X, V) := MvPolynomial.aeval r
  letI := Module.compHom P π.toRingHom
  let ρ := gradedTwistSections_res f M s (le_top : V ≤ ⊤)
  have hloc : IsLocalizedModule.Away (X i : MvPolynomial ι R) ρ := by
    have h := isLocalizedModule_gradedTwistSections f hM hH s ({i} : Finset ι)
    simpa only [xProd, Finset.prod_singleton, nonzeroLocus_sectionProduct hH, Finset.iInf_singleton] using h
  letI := hloc
  have hker : ∀ y, ρ y = 0 → ∃ k : ℕ, (X i : MvPolynomial ι R) ^ k • y = 0 := by
    intro y hy
    obtain ⟨k, hk⟩ := IsLocalizedModule.Away.exists_of_eq (X i : MvPolynomial ι R)
      (hy.trans (map_zero ρ).symm)
    exact ⟨k, by simpa only [smul_zero] using hk⟩
  have hsat : ∀ z, ∃ k : ℕ, (X i : MvPolynomial ι R) ^ k • z ∈ LinearMap.range ρ := by
    intro z
    obtain ⟨k, y, hy⟩ := IsLocalizedModule.Away.surj ρ (X i : MvPolynomial ι R) z
    exact ⟨k, y, hy.symm⟩
  let e := LinearEquiv.ofBijective (QuotSMulTop.map (X i - 1 : MvPolynomial ι R) ρ)
    (bijective_specialization_of_saturating (gradedTwistSections_res_isGraded f M s le_top) i hker hsat)
  obtain ⟨e'⟩ := nonempty_dehomogenizedTwistChartEquiv s i le_rfl r hr f M hH
  have hπ1 : π (X i) = 1 := (MvPolynomial.aeval_X _ _).trans (sectionRatio_self s i le_rfl r hr hH)
  have hP : Module.Finite Γ(X, V) P ∧ Module.Projective Γ(X, V) P :=
    finite_projective_sections (twist_isLB hM hH 0) hV
  exact ⟨Γ(X, V), inferInstance, inferInstance, π, P, inferInstance, inferInstance,
    chartAlgebra_smooth f hV, hP.1, hP.2, hπ, hπ1, ⟨e.trans e'⟩⟩

end GlobalTheory.LineBundleSections
