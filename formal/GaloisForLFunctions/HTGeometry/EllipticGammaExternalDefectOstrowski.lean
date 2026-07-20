import GaloisForLFunctions.HTGeometry.EllipticGammaPairedIncrement
import GaloisForLFunctions.HTGeometry.MeromorphicEllipticPuncturedPeriod
import GaloisForLFunctions.HTGeometry.ElementaryOstrowski
import GaloisForLFunctions.HTGeometry.SourceBoundaryQuotientMatroid
import GaloisForLFunctions.HTGeometry.MeromorphicThetaDefectPunctured
import GaloisForLFunctions.HTGeometry.MeromorphicPuncturedTranslationEquality

/-!
# Differential independence of actual elliptic-gamma external defects

The unconditional several-automorphism Ostrowski criterion is instantiated on the genuine
elliptic-gamma logarithmic derivative.  A putative finite simultaneous jet telescoper is flattened
to a finite family of polynomial differential operators.  Its `sigma` equation descends from
`E_sigma E_tau` to `E_tau` by product specialization, where the punctured-local theta pole-orbit
obstruction excludes it.
-/

open Filter Topology Set Function Complex
open scoped Differential BigOperators nonZeroDivisors

namespace GaloisForLFunctions

open Bottcher HTGeometry

noncomputable section

local instance ellipticGammaOstrowskiDomain :
    IsDomain (analyticSubring (Set.univ : Set ℂ)) :=
  Bottcher.isDomain_analyticSubring Set.univ isOpen_univ
    isPreconnected_univ Set.univ_nonempty

local instance ellipticGammaOstrowskiComplexAlgebraAnalytic :
    Algebra ℂ (analyticSubring Set.univ) := (constToAnalytic Set.univ).toAlgebra

local instance ellipticGammaOstrowskiComplexAlgebraMero :
    Algebra ℂ (meroField Set.univ) :=
  meromorphicEllipticCompositumComplexAlgebraMero

local instance ellipticGammaOstrowskiAmbientDifferential :
    Differential (meroField (Set.univ : Set ℂ)) :=
  meroFieldDifferential isOpen_univ isPreconnected_univ Set.univ_nonempty

local instance ellipticGammaOstrowskiRestrictedDifferential
    (sigma tau : ℂ) :
    Differential (meromorphicEllipticCompositum sigma tau) :=
  meromorphicEllipticCompositumDifferential sigma tau

local instance ellipticGammaOstrowskiDifferentialAlgebra
    (sigma tau : ℂ) :
    DifferentialAlgebra (meromorphicEllipticCompositum sigma tau)
      (meroField Set.univ) :=
  ⟨fun x ↦ derivationClosedDifferential_apply
    (meromorphicEllipticCompositum sigma tau)
    (meromorphicEllipticCompositum_derivationClosed sigma tau) x⟩

theorem meromorphicEllipticCompositum_deriv_algebraMap_complex
    (sigma tau c : ℂ) :
    (algebraMap ℂ (meromorphicEllipticCompositum sigma tau) c)′ = 0 := by
  apply Subtype.ext
  change (algebraMap ℂ (meroField Set.univ) c)′ = 0
  change
    (algebraMap (analyticSubring Set.univ) (meroField Set.univ)
      (constToAnalytic Set.univ c))′ = 0
  rw [meroFieldDifferential_algebraMap isOpen_univ isPreconnected_univ
    Set.univ_nonempty]
  have hconst : analyticSubringDeriv isOpen_univ
      (constToAnalytic Set.univ c) = 0 := by
    apply Subtype.ext
    rw [analyticSubringDeriv_coe]
    let f : ℂ → ℂ := fun _ ↦ c
    calc
      Germ.coeRingHom (Filter.principal Set.univ) (deriv f) =
          Germ.coeRingHom (Filter.principal Set.univ) (0 : ℂ → ℂ) := by
        congr 1
        funext z
        simp [f]
      _ = 0 := (Germ.coeRingHom (Filter.principal Set.univ)).map_zero
  rw [hconst, map_zero]

/-! ## Differential-operator closure and coercion -/

theorem DerivationClosed.differentialJet_mem
    {F K : Type*} [Field F] [Field K] [Algebra F K] [Differential K]
    {E : IntermediateField F K} (hE : DerivationClosed E)
    {x : K} (hx : x ∈ E) (n : ℕ) : differentialJet n x ∈ E := by
  induction n with
  | zero => simpa using hx
  | succ n ih =>
      rw [differentialJet_succ]
      exact hE ih

theorem DerivationClosed.differentialOperatorApply_mem
    {C F K : Type*} [Field C] [Field F] [Field K]
    [Algebra C K] [Algebra F K] [Differential K]
    {E : IntermediateField F K} (hE : DerivationClosed E)
    (hconstants : ∀ c : C, algebraMap C K c ∈ E)
    {x : K} (hx : x ∈ E) (L : Polynomial C) :
    differentialOperatorApply L x ∈ E := by
  classical
  rw [differentialOperatorApply, Polynomial.sum_def]
  apply IntermediateField.sum_mem
  intro n hn
  exact E.mul_mem (hconstants (L.coeff n))
    (hE.differentialJet_mem hx n)

/-- Coercion of the restricted compositum commutes with every constant-coefficient differential
operator. -/
theorem algebraMap_meromorphicEllipticCompositum_differentialOperatorApply
    (sigma tau : ℂ) (L : Polynomial ℂ)
    (x : meromorphicEllipticCompositum sigma tau) :
    algebraMap (meromorphicEllipticCompositum sigma tau) (meroField Set.univ)
        (differentialOperatorApply L x) =
      differentialOperatorApply L
        (algebraMap (meromorphicEllipticCompositum sigma tau)
          (meroField Set.univ) x) := by
  exact differentialOperatorApply_algebraMap_of_differentialAlgebra
    (C := ℂ) (K := meromorphicEllipticCompositum sigma tau)
    (L := meroField Set.univ) (fun _ ↦ rfl) L x

/-! ## Rational independence gives nontorsion of the transverse source -/

/-- Rational independence of `1`, `sigma`, and `tau` makes translation by `sigma` nontorsion on
the `(1,tau)` elliptic curve. -/
theorem thetaTranslationNontorsion_of_ellipticGammaSourcePeriods_linearIndependent
    (sigma tau : ℂ)
    (hindependent : LinearIndependent ℚ (ellipticGammaSourcePeriods sigma tau)) :
    ThetaTranslationNontorsion tau sigma := by
  intro a b n hab
  have hcomb : ∑ i, (![(-a : ℚ), (n : ℚ), (-b : ℚ)] : Fin 3 → ℚ) i •
      ellipticGammaSourcePeriods sigma tau i = 0 := by
    simp only [Fin.sum_univ_three, ellipticGammaSourcePeriods,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons, Rat.smul_def]
    push_cast
    linear_combination hab
  have hz := Fintype.linearIndependent_iff.mp hindependent _ hcomb
  have hn : (n : ℚ) = 0 := hz 1
  exact_mod_cast hn

/-! ## The actual primitive and increment families -/

def ellipticGammaExternalDefectFamily
    {kappa : Type*} (h : kappa → ℂ)
    (sigma tau : ℂ) (hsigma : 0 < sigma.im) (htau : 0 < tau.im) :
    kappa → meroField Set.univ := fun j ↦
  ellipticGammaExternalLogDerivDefectMero (h j) sigma tau hsigma htau

def ellipticGammaExternalDefectIncrementFamily
    {kappa : Type*} (h : kappa → ℂ)
    (sigma tau : ℂ) (hsigma : 0 < sigma.im) (htau : 0 < tau.im) :
    Fin 3 → kappa → meromorphicEllipticCompositum sigma tau :=
  fun i j ↦ ellipticGammaExternalDefectIncrement
    (h j) sigma tau hsigma htau i

/-! ## Excluding every finite simultaneous jet telescoper -/

/-- A nonzero polynomial differential-operator character of a pairwise separated actual defect
family cannot be the `sigma`-coboundary of an element of `E_sigma E_tau`. -/
theorem ellipticGammaExternalDefectFamily_no_operator_telescoping
    {kappa : Type*}
    (h : kappa → ℂ) (sigma tau : ℂ)
    (hsigma : 0 < sigma.im) (htau : 0 < tau.im)
    (hindependent : LinearIndependent ℚ (ellipticGammaSourcePeriods sigma tau))
    (hnonres : ∀ j, ThetaTranslationNonresonant tau sigma (h j))
    (hsep : ∀ i j, j ≠ i →
      ThetaTranslationNonresonant tau sigma (h j - h i))
    (operatorCoefficients : kappa →₀ Polynomial ℂ)
    (i0 : kappa) (hi0 : i0 ∈ operatorCoefficients.support)
    (hLi0 : operatorCoefficients i0 ≠ 0)
    (k : meromorphicEllipticCompositum sigma tau) :
    (ellipticGammaCompositumDifferenceDifferentialField sigma tau).defect 1 k ≠
      differentialOperatorLinearCombination
        (fun j i ↦ ellipticGammaExternalDefectIncrementFamily
          h sigma tau hsigma htau i j) operatorCoefficients 1 := by
  classical
  let omega : kappa → Fin 3 →
      meromorphicEllipticCompositum sigma tau := fun j i ↦
    ellipticGammaExternalDefectIncrementFamily
      h sigma tau hsigma htau i j
  let thetaSum : meroField Set.univ :=
    ∑ j ∈ operatorCoefficients.support,
      differentialOperatorApply (operatorCoefficients j)
        (thetaLogDerivDefectMero (h j) tau htau)
  have hthetaElliptic : thetaSum ∈ ellipticMeroField tau := by
    dsimp only [thetaSum]
    apply IntermediateField.sum_mem
    intro j hj
    apply (ellipticMeroField_derivationClosed tau).differentialOperatorApply_mem
      (fun z ↦ (ellipticMeroField tau).algebraMap_mem z)
    exact thetaLogDerivDefectMero_mem_ellipticMeroField (h j) tau htau
  let aTau : ellipticMeroField tau := ⟨thetaSum, hthetaElliptic⟩
  have homegaCoe :
      algebraMap (meromorphicEllipticCompositum sigma tau)
          (meroField Set.univ)
          (differentialOperatorLinearCombination
            omega operatorCoefficients (1 : Fin 3)) =
        thetaSum := by
    dsimp only [thetaSum]
    rw [differentialOperatorLinearCombination,
      map_finsuppSum
        (algebraMap (meromorphicEllipticCompositum sigma tau)
          (meroField Set.univ))]
    unfold Finsupp.sum
    apply Finset.sum_congr rfl
    intro j hj
    change algebraMap (meromorphicEllipticCompositum sigma tau)
        (meroField Set.univ)
          (differentialOperatorApply (operatorCoefficients j) (omega j 1)) = _
    rw [algebraMap_meromorphicEllipticCompositum_differentialOperatorApply]
    exact congrArg (differentialOperatorApply (operatorCoefficients j)) (by
      simp [omega, ellipticGammaExternalDefectIncrementFamily,
        ellipticGammaExternalDefectIncrement_one_coe])
  intro htel
  have htelAmbient := congrArg
    (algebraMap (meromorphicEllipticCompositum sigma tau)
      (meroField Set.univ)) htel
  rw [CommutingDifferenceDifferentialField.defect] at htelAmbient
  rw [(algebraMap (meromorphicEllipticCompositum sigma tau)
    (meroField Set.univ)).map_sub] at htelAmbient
  rw [← ellipticGammaCompositum_aut_algebraMap sigma tau
    (1 : Fin 3) k] at htelAmbient
  have hcoboundary : addTranslationMeroAlgEquiv sigma
        (k : meroField Set.univ) - (k : meroField Set.univ) =
      (aTau : meroField Set.univ) := by
    change addTranslationMeroEquiv sigma (k : meroField Set.univ) -
        (k : meroField Set.univ) = thetaSum
    rw [← homegaCoe]
    exact htelAmbient
  obtain ⟨u, hu⟩ := exists_ellipticTau_coboundary_of_compositum_sigma
    sigma tau hindependent aTau k.2 hcoboundary
  obtain ⟨a, b, hbmem, hab⟩ :=
    IsFractionRing.div_surjective (analyticSubring Set.univ)
      (u : meroField Set.univ)
  have hb : b ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hbmem
  obtain ⟨f, hf, hfa⟩ := a.2
  obtain ⟨g, hg, hgb⟩ := b.2
  have huAmbient := congrArg
    (fun w : ellipticMeroField tau ↦ (w : meroField Set.univ)) hu
  have hfield : thetaSum =
      addTranslationMeroEquiv sigma
          (algebraMap (analyticSubring Set.univ) (meroField Set.univ) a /
            algebraMap (analyticSubring Set.univ) (meroField Set.univ) b) -
        algebraMap (analyticSubring Set.univ) (meroField Set.univ) a /
          algebraMap (analyticSubring Set.univ) (meroField Set.univ) b := by
    change addTranslationMeroEquiv sigma (u : meroField Set.univ) -
      (u : meroField Set.univ) = thetaSum at huAmbient
    rw [hab]
    exact huAmbient.symm
  have hrep : HasPuncturedMeromorphicRep thetaSum
      (thetaDifferentialFamilySum operatorCoefficients.support
        (fun j ↦ operatorCoefficients j) h tau) := by
    let X : kappa → meroField Set.univ := fun j ↦
      differentialOperatorApply (operatorCoefficients j)
        (thetaLogDerivDefectMero (h j) tau htau)
    let Phi : kappa → ℂ → ℂ := fun j ↦
      constantCoeffDifferentialOperator (operatorCoefficients j)
        (thetaLogDerivDefect (h j) · tau)
    have hterm : ∀ j ∈ operatorCoefficients.support,
        HasPuncturedMeromorphicRep (X j) (Phi j) := by
      intro j hj
      exact
        hasPuncturedMeromorphicRep_differentialOperatorApply_thetaLogDerivDefectMero
          (operatorCoefficients j) (h j) tau htau
    have hsumRep := hasPuncturedMeromorphicRep_sum
      operatorCoefficients.support hterm
    change HasPuncturedMeromorphicRep
      (∑ j ∈ operatorCoefficients.support, X j)
      (thetaDifferentialFamilySum operatorCoefficients.support
        (fun j ↦ operatorCoefficients j) h tau)
    convert hsumRep using 1
    funext z
    simp only [thetaDifferentialFamilySum, Finset.sum_apply, Phi]
  have hlocal := hrep.eq_shiftCoboundary_nhdsNE
    sigma hb hg hfa hgb hfield
  have hellipticFraction :
      algebraMap (analyticSubring Set.univ) (meroField Set.univ) a /
          algebraMap (analyticSubring Set.univ) (meroField Set.univ) b ∈
        ellipticMeroField tau := by
    rw [hab]
    exact u.2
  exact thetaDifferentialFamily_ne_ellipticFieldShiftCoboundary_of_eventuallyEq
    htau
    (thetaTranslationNontorsion_of_ellipticGammaSourcePeriods_linearIndependent
      sigma tau hindependent)
    (fun j hj ↦ hnonres j)
    hi0 hLi0 (fun j hj hji ↦ hsep i0 j hji)
    hb hf hg hfa hgb hellipticFraction
    (fun n ↦ hlocal (additiveOrbitPoint
      (thetaHalfPeriod tau - h i0) sigma n))

/-- No nonzero finite jet character of a pairwise separated actual defect family can be the
simultaneous coboundary of one element of `E_sigma E_tau`. -/
theorem ellipticGammaExternalDefectFamily_no_simultaneous_jet_telescoping
    {kappa : Type*}
    (h : kappa → ℂ) (sigma tau : ℂ)
    (hsigma : 0 < sigma.im) (htau : 0 < tau.im)
    (hindependent : LinearIndependent ℚ (ellipticGammaSourcePeriods sigma tau))
    (hnonres : ∀ j, ThetaTranslationNonresonant tau sigma (h j))
    (hsep : ∀ i j, j ≠ i →
      ThetaTranslationNonresonant tau sigma (h j - h i))
    (c : (kappa × ℕ) →₀ ℂ) (hc : c ≠ 0)
    (k : meromorphicEllipticCompositum sigma tau) :
    ∃ i,
      (ellipticGammaCompositumDifferenceDifferentialField sigma tau).defect i k ≠
        Finsupp.linearCombination (meromorphicEllipticCompositum sigma tau)
          (fun p ↦ differentialJet p.2
            (ellipticGammaExternalDefectIncrementFamily
              h sigma tau hsigma htau i p.1))
          (Finsupp.mapRange
            (algebraMap ℂ (meromorphicEllipticCompositum sigma tau))
            (map_zero (algebraMap ℂ
              (meromorphicEllipticCompositum sigma tau))) c) := by
  classical
  let operatorCoefficients : kappa →₀ Polynomial ℂ :=
    differentialOperatorCoefficientEquiv c
  have hoperators : operatorCoefficients ≠ 0 := by
    intro hzero
    apply hc
    apply (differentialOperatorCoefficientEquiv
      (J := kappa) (C := ℂ)).injective
    simpa [operatorCoefficients] using hzero
  obtain ⟨i0, hLi0⟩ := Finsupp.ne_iff.mp hoperators
  have hi0 : i0 ∈ operatorCoefficients.support :=
    Finsupp.mem_support_iff.mpr hLi0
  let omega : kappa → Fin 3 →
      meromorphicEllipticCompositum sigma tau := fun j i ↦
    ellipticGammaExternalDefectIncrementFamily
      h sigma tau hsigma htau i j
  have hflat :
      differentialOperatorLinearCombination omega operatorCoefficients (1 : Fin 3) =
        Finsupp.linearCombination (meromorphicEllipticCompositum sigma tau)
          (fun p ↦ differentialJet p.2
            (ellipticGammaExternalDefectIncrementFamily
              h sigma tau hsigma htau 1 p.1))
          (Finsupp.mapRange
            (algebraMap ℂ (meromorphicEllipticCompositum sigma tau))
            (map_zero (algebraMap ℂ
              (meromorphicEllipticCompositum sigma tau))) c) := by
    have hflatten := differentialOperator_linearCombination_eq_jetLinearCombination
      omega operatorCoefficients (1 : Fin 3)
    simpa [omega, operatorCoefficients] using hflatten
  refine ⟨(1 : Fin 3), ?_⟩
  intro htel
  apply ellipticGammaExternalDefectFamily_no_operator_telescoping
    h sigma tau hsigma htau hindependent hnonres hsep
    operatorCoefficients i0 hi0 hLi0 k
  exact htel.trans hflat.symm

/-! ## Differential independence -/

/-- **Actual elliptic-gamma finite-family Ostrowski theorem.**  External defects indexed by
pairwise distinct nonzero rank-three period cosets are differentially algebraically independent
over the concrete paired elliptic compositum. -/
theorem ellipticGammaExternalDefectFamily_differentialIndependent
    {kappa : Type*}
    (h : kappa → ℂ) (sigma tau : ℂ)
    (hsigma : 0 < sigma.im) (htau : 0 < tau.im)
    (hindependent : LinearIndependent ℚ (ellipticGammaSourcePeriods sigma tau))
    (hnonres : ∀ j, ThetaTranslationNonresonant tau sigma (h j))
    (hsep : ∀ i j, j ≠ i →
      ThetaTranslationNonresonant tau sigma (h j - h i)) :
    DifferentialIndependent (meromorphicEllipticCompositum sigma tau)
      (ellipticGammaExternalDefectFamily h sigma tau hsigma htau) := by
  classical
  let SK := ellipticGammaCompositumDifferenceDifferentialField sigma tau
  let SL := rankThreeGeneratorMeromorphicDifferenceDifferentialField
    (ellipticGammaSourcePeriods sigma tau)
  let x := ellipticGammaExternalDefectFamily h sigma tau hsigma htau
  let b := ellipticGammaExternalDefectIncrementFamily h sigma tau hsigma htau
  have hcomp : ∀ i k, SL.aut i
      (algebraMap (meromorphicEllipticCompositum sigma tau)
        (meroField Set.univ) k) =
      algebraMap (meromorphicEllipticCompositum sigma tau)
        (meroField Set.univ) (SK.aut i k) := by
    intro i k
    exact ellipticGammaCompositum_aut_algebraMap sigma tau i k
  have hfixed : ∀ z : meroField Set.univ, JointFixed SL z →
      ∃ c : ℂ, algebraMap ℂ (meroField Set.univ) c = z := by
    intro z hz
    have hz' : JointFixed
        (rankThreeGeneratorMeromorphicDifferenceDifferentialField
          (ellipticGammaSourcePeriods sigma tau)) z := by
      simpa only [SL] using hz
    obtain ⟨c, hc⟩ :=
      (rankThree_generator_jointFixed_iff_constant
        (ellipticGammaSourcePeriods sigma tau) hindependent z).mp hz'
    exact ⟨c, by simpa [meromorphicConstantEmbedding] using hc⟩
  have hshift : ∀ i j, SL.aut i (x j) =
      x j + algebraMap (meromorphicEllipticCompositum sigma tau)
        (meroField Set.univ) (b i j) := by
    intro i j
    simpa only [SL, x, b, ellipticGammaExternalDefectFamily,
      ellipticGammaExternalDefectIncrementFamily] using
      ellipticGammaExternalDefect_shift
        (h j) sigma tau hsigma htau i
  have hnot : ∀ c : (kappa × ℕ) →₀ ℂ, c ≠ 0 →
      ∀ k : meromorphicEllipticCompositum sigma tau, ∃ i,
        SK.defect i k ≠
          Finsupp.linearCombination (meromorphicEllipticCompositum sigma tau)
            (fun p ↦ differentialJet p.2 (b i p.1))
            (Finsupp.mapRange
              (algebraMap ℂ (meromorphicEllipticCompositum sigma tau))
              (map_zero (algebraMap ℂ
                (meromorphicEllipticCompositum sigma tau))) c) := by
    intro c hc k
    simpa only [SK, b, ellipticGammaExternalDefectIncrementFamily] using
      ellipticGammaExternalDefectFamily_no_simultaneous_jet_telescoping
        h sigma tau hsigma htau hindependent hnonres hsep c hc k
  exact differentialIndependent_of_no_constant_simultaneous_jet_telescoping
    SK SL hcomp hfixed x b hshift hnot

end

end GaloisForLFunctions
