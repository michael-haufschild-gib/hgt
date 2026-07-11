import GaloisForLFunctions.EllipticGammaExternalDefectDifferentialAtomic
import GaloisForLFunctions.MeromorphicThetaFamilyPoleOrbitBoundaryLocal

/-!
# Finite-family differential-linear atomicity of actual elliptic-gamma defects

A separated finite family of external differences of the logarithmic derivative of the genuine
elliptic-gamma product is `ℂ[∂]`-linearly independent modulo the `(1, τ)`-elliptic meromorphic
field.  Equivalently, any differential-operator combination with one nonzero coefficient remains
outside that elliptic field.
-/

open Filter Topology Set Function Complex
open scoped Differential BigOperators

namespace GaloisForLFunctions

open Bottcher

noncomputable section

local instance ellipticGammaFamilyAtomicDomain :
    IsDomain (analyticSubring (Set.univ : Set ℂ)) :=
  Bottcher.isDomain_analyticSubring Set.univ isOpen_univ
    isPreconnected_univ Set.univ_nonempty

local instance ellipticGammaFamilyAtomicComplexAlgebraAnalytic :
    Algebra ℂ (analyticSubring Set.univ) := (constToAnalytic Set.univ).toAlgebra

local instance ellipticGammaFamilyAtomicComplexAlgebraMero :
    Algebra ℂ (meroField Set.univ) :=
  ((algebraMap (analyticSubring Set.univ) (meroField Set.univ)).comp
    (constToAnalytic Set.univ)).toAlgebra

local instance ellipticGammaFamilyAtomicDifferential :
    Differential (meroField (Set.univ : Set ℂ)) :=
  meroFieldDifferential isOpen_univ isPreconnected_univ Set.univ_nonempty

/-- A finite differential-operator combination of actual elliptic-gamma external defects. -/
def ellipticGammaExternalDifferentialFamilySum {ι : Type*} (s : Finset ι)
    (L : ι → Polynomial ℂ) (h : ι → ℂ)
    (σ τ : ℂ) (hσ : 0 < σ.im) (hτ : 0 < τ.im) : meroField Set.univ :=
  ∑ i ∈ s, differentialOperatorApply (L i)
    (addTranslationMeroEquiv (h i) (ellipticGammaLogDerivMero σ τ hσ hτ) -
      ellipticGammaLogDerivMero σ τ hσ hτ)

/-- **Finite-family differential-linear atomicity of actual elliptic-gamma defects.**

Under nontorsion and pairwise orbit separation, no finite `ℂ[∂]`-combination containing a
nonzero operator can be an elliptic quotient of entire functions. -/
theorem ellipticGammaExternalDifferentialFamilySum_ne_ellipticFraction
    {ι : Type*} [DecidableEq ι] {s : Finset ι}
    {L : ι → Polynomial ℂ} {h : ι → ℂ}
    {σ τ : ℂ} (hσ : 0 < σ.im) (hτ : 0 < τ.im)
    (hσnt : ThetaTranslationNontorsion τ σ)
    (hnonres : ∀ j ∈ s, ThetaTranslationNonresonant τ σ (h j))
    {i₀ : ι} (hi₀ : i₀ ∈ s) (hLi₀ : L i₀ ≠ 0)
    (hsep : ∀ j ∈ s, j ≠ i₀ →
      ThetaTranslationNonresonant τ σ (h j - h i₀))
    {a b : analyticSubring (Set.univ : Set ℂ)} (hb : b ≠ 0)
    {f g : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f Set.univ)
    (hg : AnalyticOnNhd ℂ g Set.univ)
    (hfa : Germ.coeRingHom (𝓟 Set.univ) f = (a : Germ (𝓟 Set.univ) ℂ))
    (hgb : Germ.coeRingHom (𝓟 Set.univ) g = (b : Germ (𝓟 Set.univ) ℂ))
    (hperiodOne : Function.Periodic (fun z => f z / g z) 1)
    (hperiodTau : Function.Periodic (fun z => f z / g z) τ) :
    ellipticGammaExternalDifferentialFamilySum s L h σ τ hσ hτ ≠
      algebraMap (analyticSubring Set.univ) (meroField Set.univ) a /
        algebraMap (analyticSubring Set.univ) (meroField Set.univ) b := by
  intro heq
  let x : ι → meroField Set.univ := fun i =>
    addTranslationMeroEquiv (h i) (ellipticGammaLogDerivMero σ τ hσ hτ) -
      ellipticGammaLogDerivMero σ τ hσ hτ
  have hind (i : ι) :
      addTranslationMeroEquiv σ (differentialOperatorApply (L i) (x i)) -
          differentialOperatorApply (L i) (x i) =
        differentialOperatorApply (L i) (thetaLogDerivDefectMero (h i) τ hτ) := by
    have hc := addTranslationMeroEquiv_defect_differentialOperatorApply σ (L i) (x i)
    have hmixed : addTranslationMeroEquiv σ (x i) - x i =
        thetaLogDerivDefectMero (h i) τ hτ := by
      exact ellipticGammaLogDerivMero_mixed_face_sigma hσ hτ
    rw [hmixed] at hc
    exact hc
  have hsum :
      (∑ i ∈ s, differentialOperatorApply (L i)
          (thetaLogDerivDefectMero (h i) τ hτ)) =
        addTranslationMeroEquiv σ
            (ellipticGammaExternalDifferentialFamilySum s L h σ τ hσ hτ) -
          ellipticGammaExternalDifferentialFamilySum s L h σ τ hσ hτ := by
    rw [ellipticGammaExternalDifferentialFamilySum, map_sum,
      ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    exact (hind i).symm
  rw [heq] at hsum
  have hrep : HasPuncturedMeromorphicRep
      (∑ i ∈ s, differentialOperatorApply (L i)
        (thetaLogDerivDefectMero (h i) τ hτ))
      (thetaDifferentialFamilySum s L h τ) := by
    let X : ι → meroField Set.univ := fun i =>
      differentialOperatorApply (L i) (thetaLogDerivDefectMero (h i) τ hτ)
    let Φ : ι → ℂ → ℂ := fun i =>
      constantCoeffDifferentialOperator (L i) (thetaLogDerivDefect (h i) · τ)
    have hterm : ∀ i ∈ s, HasPuncturedMeromorphicRep (X i) (Φ i) := by
      intro i hi
      exact hasPuncturedMeromorphicRep_differentialOperatorApply_thetaLogDerivDefectMero
        (L i) (h i) τ hτ
    have hsumRep := hasPuncturedMeromorphicRep_sum s hterm
    change HasPuncturedMeromorphicRep (∑ i ∈ s, X i)
      (thetaDifferentialFamilySum s L h τ)
    convert hsumRep using 1
    funext z
    simp only [thetaDifferentialFamilySum, Finset.sum_apply, Φ]
  have hlocal := hrep.eq_shiftCoboundary_nhdsNE σ hb hg hfa hgb hsum
  apply thetaDifferentialFamily_ne_ellipticShiftCoboundary_of_eventuallyEq
    hτ hσnt hnonres hi₀ hLi₀ hsep (fun z => f z / g z)
  · exact hf.meromorphicOn.div hg.meromorphicOn
  · exact hperiodOne
  · exact hperiodTau
  · intro n
    exact hlocal (additiveOrbitPoint (thetaHalfPeriod τ - h i₀) σ n)

/-- Uniform form of finite-family atomicity: pairwise separated external shifts admit no
nontrivial differential-operator combination in the elliptic fraction field. -/
theorem ellipticGammaExternalDifferentialFamilySum_ne_ellipticFraction_of_nonzero
    {ι : Type*} [DecidableEq ι] {s : Finset ι}
    {L : ι → Polynomial ℂ} {h : ι → ℂ}
    {σ τ : ℂ} (hσ : 0 < σ.im) (hτ : 0 < τ.im)
    (hσnt : ThetaTranslationNontorsion τ σ)
    (hnonres : ∀ j ∈ s, ThetaTranslationNonresonant τ σ (h j))
    (hsep : ∀ i ∈ s, ∀ j ∈ s, j ≠ i →
      ThetaTranslationNonresonant τ σ (h j - h i))
    (hnz : ∃ i ∈ s, L i ≠ 0)
    {a b : analyticSubring (Set.univ : Set ℂ)} (hb : b ≠ 0)
    {f g : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f Set.univ)
    (hg : AnalyticOnNhd ℂ g Set.univ)
    (hfa : Germ.coeRingHom (𝓟 Set.univ) f = (a : Germ (𝓟 Set.univ) ℂ))
    (hgb : Germ.coeRingHom (𝓟 Set.univ) g = (b : Germ (𝓟 Set.univ) ℂ))
    (hperiodOne : Function.Periodic (fun z => f z / g z) 1)
    (hperiodTau : Function.Periodic (fun z => f z / g z) τ) :
    ellipticGammaExternalDifferentialFamilySum s L h σ τ hσ hτ ≠
      algebraMap (analyticSubring Set.univ) (meroField Set.univ) a /
        algebraMap (analyticSubring Set.univ) (meroField Set.univ) b := by
  obtain ⟨i₀, hi₀, hLi₀⟩ := hnz
  exact ellipticGammaExternalDifferentialFamilySum_ne_ellipticFraction
    hσ hτ hσnt hnonres hi₀ hLi₀ (hsep i₀ hi₀)
    hb hf hg hfa hgb hperiodOne hperiodTau

/-- **Free differential matroid on separated actual elliptic-gamma defects.** A finite
`ℂ[∂]`-combination of pairwise separated external defects vanishes exactly when every operator
coefficient vanishes. -/
theorem ellipticGammaExternalDifferentialFamilySum_eq_zero_iff
    {ι : Type*} [DecidableEq ι] {s : Finset ι}
    {L : ι → Polynomial ℂ} {h : ι → ℂ}
    {σ τ : ℂ} (hσ : 0 < σ.im) (hτ : 0 < τ.im)
    (hσnt : ThetaTranslationNontorsion τ σ)
    (hnonres : ∀ j ∈ s, ThetaTranslationNonresonant τ σ (h j))
    (hsep : ∀ i ∈ s, ∀ j ∈ s, j ≠ i →
      ThetaTranslationNonresonant τ σ (h j - h i)) :
    ellipticGammaExternalDifferentialFamilySum s L h σ τ hσ hτ = 0 ↔
      ∀ i ∈ s, L i = 0 := by
  constructor
  · intro hzero i hi
    by_contra hLi
    have hne :=
      ellipticGammaExternalDifferentialFamilySum_ne_ellipticFraction_of_nonzero
        hσ hτ hσnt hnonres hsep ⟨i, hi, hLi⟩
        (a := (0 : analyticSubring Set.univ))
        (b := (1 : analyticSubring Set.univ)) one_ne_zero
        (f := fun _ => 0) (g := fun _ => 1)
        analyticOnNhd_const analyticOnNhd_const rfl rfl
        (by intro z; simp) (by intro z; simp)
    apply hne
    simpa using hzero
  · intro hall
    rw [ellipticGammaExternalDifferentialFamilySum]
    apply Finset.sum_eq_zero
    intro i hi
    rw [hall i hi, differentialOperatorApply_zero]

end

end GaloisForLFunctions
