import GaloisForLFunctions.HTGeometry.AffineFirstOrderDifferentialAlgebraicity
import GaloisForLFunctions.HTGeometry.EllipticGammaRationalBaseMatroid

/-!
# Structural-generator DA spectrum of the genuine elliptic gamma defect

The hard off-spectrum theorem already proves differential independence for separated nonzero
rank-three cosets.  This module closes the complementary structural-generator interface.  The
direct elliptic-gamma source faces identify the two nontrivial generator defects with theta
logarithmic derivatives.  Their derivatives are elliptic, so the general affine first-order law
makes the source faces differentially algebraic over the paired elliptic compositum.
-/

open Filter Set
open scoped Differential

namespace GaloisForLFunctions

open Bottcher
open HTGeometry

noncomputable section

local instance ellipticGammaStructuralGeneratorDomain :
    IsDomain (analyticSubring (Set.univ : Set ℂ)) :=
  Bottcher.isDomain_analyticSubring Set.univ isOpen_univ
    isPreconnected_univ Set.univ_nonempty

local instance ellipticGammaStructuralGeneratorComplexAlgebraAnalytic :
    Algebra ℂ (analyticSubring Set.univ) := (constToAnalytic Set.univ).toAlgebra

local instance ellipticGammaStructuralGeneratorComplexAlgebraMero :
    Algebra ℂ (meroField Set.univ) :=
  meromorphicEllipticCompositumComplexAlgebraMero

local instance ellipticGammaStructuralGeneratorAmbientDifferential :
    Differential (meroField (Set.univ : Set ℂ)) :=
  meroFieldDifferential isOpen_univ isPreconnected_univ Set.univ_nonempty

local instance ellipticGammaStructuralGeneratorRestrictedDifferential
    (sigma tau : ℂ) :
    Differential (meromorphicEllipticCompositum sigma tau) :=
  meromorphicEllipticCompositumDifferential sigma tau

local instance ellipticGammaStructuralGeneratorDifferentialAlgebra
    (sigma tau : ℂ) :
    DifferentialAlgebra (meromorphicEllipticCompositum sigma tau)
      (meroField Set.univ) :=
  ⟨fun x ↦ derivationClosedDifferential_apply
    (meromorphicEllipticCompositum sigma tau)
    (meromorphicEllipticCompositum_derivationClosed sigma tau) x⟩

/-! ## General translated-defect span laws -/

/-- If every translate of one generator defect is DA, the same is true for every translate of
each natural multiple of that generator. -/
theorem differentialAlgebraicOver_addTranslationMeroEquiv_defect_nsmul
    {F : Type*} [Field F] [Algebra F (meroField Set.univ)] [Differential F]
    [DifferentialAlgebra F (meroField Set.univ)]
    (x : meroField Set.univ) (g : ℂ)
    (hgen : ∀ q : ℂ, DifferentialAlgebraicOver F
      (addTranslationMeroEquiv q (addTranslationMeroEquiv g x - x)))
    (q : ℂ) : ∀ n : ℕ, DifferentialAlgebraicOver F
      (addTranslationMeroEquiv q (addTranslationMeroEquiv (n • g) x - x)) := by
  intro n
  induction n with
  | zero =>
      rw [zero_nsmul, addTranslationMeroEquiv_zero_apply, sub_self, map_zero]
      exact differentialAlgebraicOver_algebraMap 0
  | succ n ih =>
      have heq :
          addTranslationMeroEquiv q
              (addTranslationMeroEquiv ((n + 1) • g) x - x) =
            addTranslationMeroEquiv q
                (addTranslationMeroEquiv (n • g) x - x) +
              addTranslationMeroEquiv (q + n • g)
                (addTranslationMeroEquiv g x - x) := by
        rw [add_nsmul, one_nsmul, addTranslationMeroEquiv_defect_add,
          map_add, addTranslationMeroEquiv_add]
      rw [heq]
      exact differentialAlgebraicOver_add ih (hgen _)

/-- **Integer-span defect law.**  DA of all translates of one generator defect propagates to all
translated integer multiples, with negative multiples supplied by the exact value-reflection
identity. -/
theorem differentialAlgebraicOver_addTranslationMeroEquiv_defect_zsmul
    {F : Type*} [Field F] [Algebra F (meroField Set.univ)] [Differential F]
    [DifferentialAlgebra F (meroField Set.univ)]
    (x : meroField Set.univ) (g : ℂ)
    (hgen : ∀ q : ℂ, DifferentialAlgebraicOver F
      (addTranslationMeroEquiv q (addTranslationMeroEquiv g x - x)))
    (q : ℂ) (n : ℤ) : DifferentialAlgebraicOver F
      (addTranslationMeroEquiv q (addTranslationMeroEquiv (n • g) x - x)) := by
  cases n with
  | ofNat n =>
      simpa using differentialAlgebraicOver_addTranslationMeroEquiv_defect_nsmul
        x g hgen q n
  | negSucc n =>
      let p : ℂ := (n + 1) • g
      have hpos := differentialAlgebraicOver_addTranslationMeroEquiv_defect_nsmul
        x g hgen (q - p) (n + 1)
      have heq :
          addTranslationMeroEquiv q
              (addTranslationMeroEquiv (-(p : ℂ)) x - x) =
            -addTranslationMeroEquiv (q - p)
              (addTranslationMeroEquiv p x - x) := by
        rw [addTranslationMeroEquiv_defect_neg, map_neg,
          addTranslationMeroEquiv_add]
        congr 2
        ring
      rw [show Int.negSucc n • g = -p by simp [p]]
      rw [heq]
      exact differentialAlgebraicOver_neg hpos

/-- Translated DA defect families are closed under addition of their shift parameters. -/
theorem differentialAlgebraicOver_addTranslationMeroEquiv_defect_add
    {F : Type*} [Field F] [Algebra F (meroField Set.univ)] [Differential F]
    [DifferentialAlgebra F (meroField Set.univ)]
    (x : meroField Set.univ) (h k : ℂ)
    (hh : ∀ q : ℂ, DifferentialAlgebraicOver F
      (addTranslationMeroEquiv q (addTranslationMeroEquiv h x - x)))
    (hk : ∀ q : ℂ, DifferentialAlgebraicOver F
      (addTranslationMeroEquiv q (addTranslationMeroEquiv k x - x)))
    (q : ℂ) : DifferentialAlgebraicOver F
      (addTranslationMeroEquiv q (addTranslationMeroEquiv (h + k) x - x)) := by
  have heq :
      addTranslationMeroEquiv q (addTranslationMeroEquiv (h + k) x - x) =
        addTranslationMeroEquiv q (addTranslationMeroEquiv h x - x) +
          addTranslationMeroEquiv (q + h)
            (addTranslationMeroEquiv k x - x) := by
    rw [addTranslationMeroEquiv_defect_add, map_add,
      addTranslationMeroEquiv_add]
  rw [heq]
  exact differentialAlgebraicOver_add (hh q) (hk (q + h))

/-- The derivative of the genuine theta logarithmic derivative is elliptic: the additive
quasiperiod constant disappears under differentiation. -/
theorem thetaLogDerivMero_deriv_mem_ellipticMeroField
    (tau : ℂ) (htau : 0 < tau.im) :
    (thetaLogDerivMero tau htau)′ ∈ ellipticMeroField tau := by
  rw [mem_ellipticMeroField_iff]
  constructor
  · rw [addTranslationMeroEquiv_deriv,
      addTranslationMeroEquiv_thetaLogDeriv_one]
  · rw [addTranslationMeroEquiv_deriv,
      addTranslationMeroEquiv_thetaLogDeriv_tau]
    simp

/-- Every translate of a theta logarithmic derivative is DA over any translation-stable paired
elliptic compositum containing its elliptic derivative field. -/
theorem differentialAlgebraicOver_addTranslationMeroEquiv_thetaLogDerivMero
    (q omega sigma tau : ℂ) (homega : 0 < omega.im)
    (hsub : ellipticMeroField omega ≤ meromorphicEllipticCompositum sigma tau) :
    DifferentialAlgebraicOver (meromorphicEllipticCompositum sigma tau)
      (addTranslationMeroEquiv q (thetaLogDerivMero omega homega)) := by
  have hderiv : (thetaLogDerivMero omega homega)′ ∈
      meromorphicEllipticCompositum sigma tau :=
    hsub (thetaLogDerivMero_deriv_mem_ellipticMeroField omega homega)
  have htranslated : addTranslationMeroEquiv q
      (thetaLogDerivMero omega homega)′ ∈
        meromorphicEllipticCompositum sigma tau :=
    addTranslationMeroAlgEquiv_mem_ellipticCompositum sigma tau q hderiv
  let b : meromorphicEllipticCompositum sigma tau :=
    ⟨addTranslationMeroEquiv q (thetaLogDerivMero omega homega)′, htranslated⟩
  apply differentialAlgebraicOver_of_deriv_eq_base b
  simpa [b] using (addTranslationMeroEquiv_deriv q
    (thetaLogDerivMero omega homega)).symm

/-- The first nontrivial structural generator defect is DA over the paired elliptic compositum. -/
theorem differentialAlgebraicOver_ellipticGammaExternalLogDerivDefectMero_sigma
    (sigma tau : ℂ) (hsigma : 0 < sigma.im) (htau : 0 < tau.im) :
    DifferentialAlgebraicOver (meromorphicEllipticCompositum sigma tau)
      (ellipticGammaExternalLogDerivDefectMero sigma sigma tau hsigma htau) := by
  rw [ellipticGammaExternalLogDerivDefectMero_sigma]
  simpa only [addTranslationMeroEquiv_zero_apply] using
    differentialAlgebraicOver_addTranslationMeroEquiv_thetaLogDerivMero
      0 tau sigma tau htau (by
        rw [meromorphicEllipticCompositum]
        exact le_sup_right)

/-- The second nontrivial structural generator defect is DA over the paired elliptic compositum. -/
theorem differentialAlgebraicOver_ellipticGammaExternalLogDerivDefectMero_tau
    (sigma tau : ℂ) (hsigma : 0 < sigma.im) (htau : 0 < tau.im) :
    DifferentialAlgebraicOver (meromorphicEllipticCompositum sigma tau)
      (ellipticGammaExternalLogDerivDefectMero tau sigma tau hsigma htau) := by
  rw [ellipticGammaExternalLogDerivDefectMero_tau]
  exact differentialAlgebraicOver_addTranslationMeroEquiv_thetaLogDerivMero
    ((tau - sigma) / 2) sigma sigma tau hsigma (by
      rw [meromorphicEllipticCompositum]
      exact le_sup_left)

/-- **Structural-generator DA law.**  Every generator of the actual rank-three source group has
a differentially algebraic elliptic-gamma logarithmic-derivative defect over the paired elliptic
compositum.  No nonresonance or rational-independence hypothesis is needed. -/
theorem differentialAlgebraicOver_ellipticGammaExternalLogDerivDefectMero_sourcePeriod
    (sigma tau : ℂ) (hsigma : 0 < sigma.im) (htau : 0 < tau.im)
    (i : Fin 3) :
    DifferentialAlgebraicOver (meromorphicEllipticCompositum sigma tau)
      (ellipticGammaExternalLogDerivDefectMero
        (ellipticGammaSourcePeriods sigma tau i)
        sigma tau hsigma htau) := by
  fin_cases i
  · simp only [ellipticGammaSourcePeriods,
      ellipticGammaExternalLogDerivDefectMero_one]
    exact differentialAlgebraicOver_algebraMap 0
  · simpa only [ellipticGammaSourcePeriods] using
      differentialAlgebraicOver_ellipticGammaExternalLogDerivDefectMero_sigma
        sigma tau hsigma htau
  · simpa only [ellipticGammaSourcePeriods] using
      differentialAlgebraicOver_ellipticGammaExternalLogDerivDefectMero_tau
        sigma tau hsigma htau

/-! ## Exact rank-three spectrum over the paired elliptic base -/

/-- Every defect whose shift belongs to the rank-three integer period group is DA over the paired
elliptic compositum.  The proof is translation-uniform, so no coefficient-fixing assumption is
hidden in the integer-span propagation. -/
theorem differentialAlgebraicOver_ellipticGammaExternalLogDerivDefectMero_of_resonant
    (sigma tau : ℂ) (hsigma : 0 < sigma.im) (htau : 0 < tau.im)
    (a b n : ℤ) :
    DifferentialAlgebraicOver (meromorphicEllipticCompositum sigma tau)
      (ellipticGammaExternalLogDerivDefectMero
        ((a : ℂ) + (b : ℂ) * tau + (n : ℂ) * sigma)
        sigma tau hsigma htau) := by
  let x := ellipticGammaLogDerivMero sigma tau hsigma htau
  have hone : ∀ q : ℂ, DifferentialAlgebraicOver
      (meromorphicEllipticCompositum sigma tau)
      (addTranslationMeroEquiv q (addTranslationMeroEquiv 1 x - x)) := by
    intro q
    rw [addTranslationMeroEquiv_ellipticGammaLogDerivMero_one, sub_self, map_zero]
    exact differentialAlgebraicOver_algebraMap 0
  have hsigmaGen : ∀ q : ℂ, DifferentialAlgebraicOver
      (meromorphicEllipticCompositum sigma tau)
      (addTranslationMeroEquiv q (addTranslationMeroEquiv sigma x - x)) := by
    intro q
    rw [ellipticGammaLogDerivMero_source_face_sigma hsigma htau]
    exact differentialAlgebraicOver_addTranslationMeroEquiv_thetaLogDerivMero
      q tau sigma tau htau (by
        rw [meromorphicEllipticCompositum]
        exact le_sup_right)
  have htauGen : ∀ q : ℂ, DifferentialAlgebraicOver
      (meromorphicEllipticCompositum sigma tau)
      (addTranslationMeroEquiv q (addTranslationMeroEquiv tau x - x)) := by
    intro q
    rw [ellipticGammaLogDerivMero_source_face_tau hsigma htau]
    rw [addTranslationMeroEquiv_add]
    exact differentialAlgebraicOver_addTranslationMeroEquiv_thetaLogDerivMero
      (q + (tau - sigma) / 2) sigma sigma tau hsigma (by
        rw [meromorphicEllipticCompositum]
        exact le_sup_left)
  have ha := fun q ↦ differentialAlgebraicOver_addTranslationMeroEquiv_defect_zsmul
    x 1 hone q a
  have hb := fun q ↦ differentialAlgebraicOver_addTranslationMeroEquiv_defect_zsmul
    x tau htauGen q b
  have hn := fun q ↦ differentialAlgebraicOver_addTranslationMeroEquiv_defect_zsmul
    x sigma hsigmaGen q n
  have hab := fun q ↦ differentialAlgebraicOver_addTranslationMeroEquiv_defect_add
    x (a • (1 : ℂ)) (b • tau) ha hb q
  have hall := differentialAlgebraicOver_addTranslationMeroEquiv_defect_add
    x (a • (1 : ℂ) + b • tau) (n • sigma) hab hn 0
  simp only [addTranslationMeroEquiv_zero_apply] at hall
  simpa [ellipticGammaExternalLogDerivDefectMero] using hall

/-- **Exact natural-base DA spectrum.**  Under rational independence of `1`, `sigma`, and `tau`,
the genuine elliptic-gamma logarithmic-derivative defect is DA over the paired elliptic compositum
exactly on the rank-three integer period group.  The reverse implication is the existing
finite-family Ostrowski theorem specialized to one defect; the forward implication is the new
structural integer-span law above. -/
theorem differentialAlgebraicOver_ellipticGammaExternalLogDerivDefectMero_iff_resonant
    (h sigma tau : ℂ) (hsigma : 0 < sigma.im) (htau : 0 < tau.im)
    (hindependent : LinearIndependent ℚ (ellipticGammaSourcePeriods sigma tau)) :
    DifferentialAlgebraicOver (meromorphicEllipticCompositum sigma tau)
        (ellipticGammaExternalLogDerivDefectMero h sigma tau hsigma htau) ↔
      ∃ a b n : ℤ, h = a + b * tau + n * sigma := by
  constructor
  · intro hDA
    by_contra hres
    have hnonres : ThetaTranslationNonresonant tau sigma h := hres
    have hDI := ellipticGammaExternalDefectFamily_differentialIndependent
      (fun _ : Unit ↦ h) sigma tau hsigma htau hindependent
      (fun _ ↦ hnonres) (by simp)
    have hHT : HypertranscendentalOver
        (meromorphicEllipticCompositum sigma tau)
        (ellipticGammaExternalLogDerivDefectMero h sigma tau hsigma htau) := by
      rw [hypertranscendentalOver_iff_differentialIndependent_singleton]
      simpa [ellipticGammaExternalDefectFamily] using hDI
    exact hHT hDA
  · rintro ⟨a, b, n, rfl⟩
    exact differentialAlgebraicOver_ellipticGammaExternalLogDerivDefectMero_of_resonant
      sigma tau hsigma htau a b n

end


end GaloisForLFunctions
