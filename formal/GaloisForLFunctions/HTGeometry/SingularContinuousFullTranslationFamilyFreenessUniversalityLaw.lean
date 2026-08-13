import GaloisForLFunctions.HTGeometry.AnalyticNevanlinnaCarrierRelationFree
import GaloisForLFunctions.HTGeometry.CarrierHerglotzPresentationFree
import GaloisForLFunctions.HTGeometry.CauchyHerglotzLocalGlobalHypertranscendenceUniversalityLaw
import GaloisForLFunctions.HTGeometry.FamilyPatternBridge
import GaloisForLFunctions.HTGeometry.FiniteSpectralHankelRank
import GaloisForLFunctions.HTGeometry.FiniteStateSpaceHankelRank
import GaloisForLFunctions.HTGeometry.FiberClosed
import GaloisForLFunctions.HTGeometry.MomentHankelStrict
import GaloisForLFunctions.HTGeometry.MutuallySingularTotalVariation
import GaloisForLFunctions.HTGeometry.NevanlinnaPositiveCarrierCapstone
import GaloisForLFunctions.HTGeometry.PacketValueFamilyJet
import GaloisForLFunctions.HTGeometry.SingularContinuousLawWitnesses
import GaloisForLFunctions.HTGeometry.ToeplitzHankelPolarization
import GaloisForLFunctions.HTGeometry.TranslatedFamilyGauge

/-!
# Singular-continuous full-translation family-freeness universality

The all-pattern Nevanlinna theorem is generic in a countable shift palette.  Taking the fixed
palette `ℕ` lets one encode every finite family of distinct translates in one residual phase.  The
family-pattern bridge then upgrades coefficient rigidity to the absence of every mixed
differential-polynomial relation among the complete translated Cauchy family, and the translated
Nevanlinna gauge transfers the result to every Herglotz presentation.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Filter MeasureTheory OnePoint Set Topology
open scoped ENNReal OnePoint Topology

noncomputable section

/-- Canonical injection of an arbitrary finite translation family into the fixed countable palette
used by the simultaneous residual theorem. -/
def naturalFamilyShiftCode (m : ℕ) : Fin m → ℕ := fun i => i

theorem naturalFamilyShiftCode_injective (m : ℕ) :
    Function.Injective (naturalFamilyShiftCode m) := by
  intro i j hij
  exact Fin.ext hij

/-- An atomless probability representation of a complete Hamburger sequence has a strict
positive-definite Hankel ray, with every finite determinant strictly positive. -/
theorem strictHankelRay_of_atomlessProbability_hamburgerMoments
    {s : ℕ → ℝ} (mu : Measure ℝ)
    [IsProbabilityMeasure mu] [NullSingletonClass mu]
    (hmoments : HasHamburgerMoments s mu) :
    ∀ n : ℕ,
      (HTGeometry.momentHankelMatrix s n).PosDef ∧
        0 < (HTGeometry.momentHankelMatrix s n).det := by
  have hinfinite : ∀ F : Finset ℝ, 0 < mu {x : ℝ | x ∉ F} := by
    intro F
    have hzero : mu (↑F : Set ℝ) = 0 := F.measure_zero mu
    have hcomplement : mu (↑F : Set ℝ)ᶜ = 1 := by
      rw [measure_compl F.measurableSet (measure_ne_top mu _), measure_univ, hzero]
      norm_num
    rw [show {x : ℝ | x ∉ F} = (↑F : Set ℝ)ᶜ by ext x; simp]
    rw [hcomplement]
    norm_num
  intro n
  have hpos := HTGeometry.momentHankelMatrix_posDef_of_infiniteSupport s
    (fun k => (hmoments k).2.symm) (fun k => (hmoments k).1) hinfinite n
  exact ⟨hpos, hpos.det_pos⟩

/-- A strict Hamburger Hankel ray excludes every uniformly bounded finite spectral palette and
every uniformly bounded finite linear state-space model, even from local finite-coordinate
closure. -/
theorem noFiniteSpectralOrStateLocalClosure_of_strictHankelRay
    {s : ℕ → ℝ}
    (hstrict : ∀ n : ℕ, 0 < (HTGeometry.momentHankelMatrix s n).det) :
    ∀ d : ℕ,
      ¬ HTGeometry.FixedSpectralWidthLocalClosure d s ∧
        ¬ HTGeometry.FixedStateSpaceDimensionLocalClosure d s := by
  intro d
  exact ⟨
    HTGeometry.not_fixedSpectralWidthLocalClosure_of_det_ne_zero
      (ne_of_gt (hstrict (d + 1))),
    HTGeometry.not_fixedStateSpaceDimensionLocalClosure_of_det_ne_zero
      (ne_of_gt (hstrict (d + 1)))⟩

/-- A strict Hamburger Hankel ray cannot be the Gram kernel of any simultaneously
shift-invariant orbit, in any real inner-product space. -/
theorem noShiftInvariantGramRealization_of_strictHankelRay
    {s : ℕ → ℝ}
    (hstrict : ∀ n : ℕ, (HTGeometry.momentHankelMatrix s n).PosDef) :
    (¬ HTGeometry.HankelShiftInvariant s) ∧
      ∀ {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
        (v : ℕ → E),
        (∀ i j, inner ℝ (v i) (v j) = s (i + j)) →
        ¬ ∀ i j,
          inner ℝ (v (i + 1)) (v (j + 1)) = inner ℝ (v i) (v j) := by
  constructor
  · intro hshift
    exact HTGeometry.not_posDef_momentHankelMatrix_add_three_of_shiftInvariant
      s hshift 0 (by simpa using hstrict 3)
  · intro E _ _ v hgram hshift
    exact HTGeometry.not_posDef_momentHankelMatrix_add_three_of_shiftInvariantGram
      s v hgram hshift 0 (by simpa using hstrict 3)

/-- Maximal total-variation separation from every absolutely continuous probability, packaged so
the probability instance for the carrier is supplied by the proposition itself. -/
def MaximallySeparatedFromAbsolutelyContinuousProbabilities
    (mu : Measure ℝ) : Prop :=
  ∀ hprobability : IsProbabilityMeasure mu,
    letI : IsProbabilityMeasure mu := hprobability
    ∀ nu : ProbabilityMeasure ℝ,
        (nu : Measure ℝ) ≪ (volume : Measure ℝ) →
          mu ⟂ₘ (nu : Measure ℝ) ∧
            (mu.toSignedMeasure -
                (nu : Measure ℝ).toSignedMeasure).totalVariation Set.univ = 2

/-- A singular probability measure is maximally separated in total variation from every
absolutely continuous probability measure. -/
theorem singularProbability_maximalTotalVariation_from_everyACProbability
    (mu : Measure ℝ) (hsingular : mu ⟂ₘ (volume : Measure ℝ)) :
    MaximallySeparatedFromAbsolutelyContinuousProbabilities mu := by
  intro hprobability
  letI : IsProbabilityMeasure mu := hprobability
  intro nu hnu
  have hsingularNu :=
    hsingular.mono_ac Measure.AbsolutelyContinuous.rfl hnu
  exact ⟨hsingularNu,
    HTGeometry.totalVariation_univ_eq_of_isProbability
      mu (nu : Measure ℝ) hsingularNu⟩

/-- Relabel a finite differential pattern along an injection of shift palettes. -/
def remapFiniteDifferentialPattern
    {Γ Δ : Type*} (e : Γ → Δ) (he : Function.Injective e)
    (p : FiniteDifferentialPattern Γ) : FiniteDifferentialPattern Δ where
  shiftCount := p.shiftCount
  shiftCode := e ∘ p.shiftCode
  orders := p.orders
  monomialCount := p.monomialCount
  jetExponent := p.jetExponent
  coefficientDegree := p.coefficientDegree
  shiftCode_injective := he.comp p.shiftCode_injective
  jetExponent_injective := p.jetExponent_injective

/-- Base points at which every member of a translated family lies in the upper half-plane. -/
def commonUpperTranslationDomain {m : ℕ}
    (shift : InjectiveShiftConfiguration (Fin m)) : Set ℂ :=
  {z | ∀ i, 0 < (z + shift.1 i).im}

/-- Common translation domain for the lower-placed boundary-carrier packets: every translate of a
point of the domain has strictly negative imaginary part. -/
def commonLowerTranslationDomain {m : ℕ}
    (shift : InjectiveShiftConfiguration (Fin m)) : Set ℂ :=
  {z | ∀ i, (z + shift.1 i).im < 0}

/-- Family relation pattern after injecting its components into an arbitrary shift palette. -/
def codedFamilyPatternOfRelation {Γ : Type*} {m n : ℕ}
    (shiftCode : Fin m → Γ) (hshiftCode : Function.Injective shiftCode)
    (P : MvPolynomial (FamilyJetIndex m n) ℂ) :
    FiniteDifferentialPattern Γ :=
  finitePatternOfPolynomial shiftCode hshiftCode (familyOrders m n)
    (renameToFamilyShiftJets m n (familyReshapeJet m n P))

/-- Vanishing coded pattern coefficients force the original family relation to vanish. -/
theorem familyJetRelation_eq_zero_of_codedPatternCoefficients_zero
    {Γ : Type*} {m n : ℕ}
    (shiftCode : Fin m → Γ) (hshiftCode : Function.Injective shiftCode)
    (P : MvPolynomial (FamilyJetIndex m n) ℂ)
    (hzero : ∀ b, polynomialPatternCoefficientVector shiftCode hshiftCode (familyOrders m n)
        (renameToFamilyShiftJets m n (familyReshapeJet m n P)) b = 0) :
    P = 0 := by
  have hQ : renameToFamilyShiftJets m n (familyReshapeJet m n P) = 0 :=
    polynomial_eq_zero_of_patternCoefficientVector_eq_zero shiftCode hshiftCode
      (familyOrders m n) _ hzero
  have hR : familyReshapeJet m n P = 0 := by
    refine renameToFamilyShiftJets_injective m n ?_
    rw [hQ]
    simp [renameToFamilyShiftJets]
  exact familyReshapeJet_injective m n (by rw [hR, map_zero])

/-- Coded pattern expansion is exactly evaluation of the original family relation. -/
theorem codedFamilyPatternExpansion_eq_eval
    {Γ : Type*} {m n : ℕ}
    (shiftCode : Fin m → Γ) (hshiftCode : Function.Injective shiftCode)
    (P : MvPolynomial (FamilyJetIndex m n) ℂ)
    (z : ℂ) (x : (Σ _ : Fin m, Fin (n + 1)) → ℂ) :
    (∑ b, polynomialPatternCoefficientVector shiftCode hshiftCode (familyOrders m n)
        (renameToFamilyShiftJets m n (familyReshapeJet m n P)) b *
      z ^ patternDegree (codedFamilyPatternOfRelation shiftCode hshiftCode P) b *
      (patternExponent (codedFamilyPatternOfRelation shiftCode hshiftCode P) b).prod
        (fun i e => x i ^ e))
      = MvPolynomial.eval (Sum.elim (fun _ => z) fun p => x ⟨p.1, p.2⟩) P := by
  simp only [codedFamilyPatternOfRelation]
  rw [polynomialPatternCoefficientExpansion]
  have hrename : MvPolynomial.eval x (specializePolynomialCoefficients z
        (renameToFamilyShiftJets m n (familyReshapeJet m n P)))
      = MvPolynomial.eval (fun q => x ((familySigmaEquiv m n).symm q))
          (specializePolynomialCoefficients z (familyReshapeJet m n P)) := by
    simp only [renameToFamilyShiftJets, specializePolynomialCoefficients, MvPolynomial.eval_map]
    simpa [Function.comp_def] using
      (MvPolynomial.eval₂_rename (Polynomial.evalRingHom z) (familySigmaEquiv m n).symm x
        (familyReshapeJet m n P))
  exact hrename.trans (eval_specialize_familyReshapeJet m n z
    (fun q => x ((familySigmaEquiv m n).symm q)) P)

namespace ClassicalAnalyticNevanlinnaCarrierFamily

variable {s : ℕ → ℝ} (F : ClassicalAnalyticNevanlinnaCarrierFamily s)

/-- Relation-freeness for a larger shift palette restricts along every injective palette map. -/
theorem allFinitePatterns_relationFree_of_shiftPaletteEmbedding
    {Γ Δ : Type*}
    (eta : Measure (OnePoint ℝ))
    (density : Lp ℝ (⊤ : ENNReal) eta)
    (e : Γ → Δ) (he : Function.Injective e)
    (hfree : ∀ (p : FiniteDifferentialPattern Δ)
      (shift : InjectiveShiftConfiguration (CarrierPatternShift p))
      (coeff : CarrierPatternMonomial p × Fin (p.coefficientDegree + 1) → ℂ),
      F.weightedBoundaryCarrierExpandedPatternRelationHolds
        (row := CarrierPatternRow p) eta density p.coefficientDegree p.orders
          (carrierPatternExponent p) shift coeff →
        ∀ col, coeff col = 0) :
    ∀ (p : FiniteDifferentialPattern Γ)
      (shift : InjectiveShiftConfiguration (CarrierPatternShift p))
      (coeff : CarrierPatternMonomial p × Fin (p.coefficientDegree + 1) → ℂ),
      F.weightedBoundaryCarrierExpandedPatternRelationHolds
        (row := CarrierPatternRow p) eta density p.coefficientDegree p.orders
          (carrierPatternExponent p) shift coeff →
        ∀ col, coeff col = 0 := by
  intro p shift coeff hrelation
  let q := remapFiniteDifferentialPattern e he p
  have hq := hfree q shift coeff (by
    simpa [q, remapFiniteDifferentialPattern] using! hrelation)
  simpa [q, remapFiniteDifferentialPattern] using hq

/-- Countable-palette coefficient rigidity excludes every mixed differential relation among an
arbitrary finite family of distinct translated Cauchy transforms. -/
theorem
    not_familyDifferentiallyAlgebraicOn_translatedCauchy_of_allFinitePatterns_relationFree
    {m : ℕ}
    (eta : Measure (OnePoint ℝ)) [IsFiniteMeasure eta]
    (density : Lp ℝ (⊤ : ENNReal) eta)
    (hfree : ∀ (p : FiniteDifferentialPattern ℕ)
      (shift : InjectiveShiftConfiguration (CarrierPatternShift p))
      (coeff : CarrierPatternMonomial p × Fin (p.coefficientDegree + 1) → ℂ),
      F.weightedBoundaryCarrierExpandedPatternRelationHolds
        (row := CarrierPatternRow p) eta density p.coefficientDegree p.orders
          (carrierPatternExponent p) shift coeff →
        ∀ col, coeff col = 0)
    (shift : InjectiveShiftConfiguration (Fin m)) :
    ¬ FamilyDifferentiallyAlgebraicOn
      (fun i z => cauchyTransform
        (weightedBoundaryCarrier F.base.toBoundaryFamily eta density) (z + shift.1 i))
      (commonLowerTranslationDomain shift) := by
  intro hDA
  obtain ⟨n, P, hPne, hPzero⟩ := hDA
  let shiftCode : Fin m → ℕ := naturalFamilyShiftCode m
  have hshiftCode : Function.Injective shiftCode := naturalFamilyShiftCode_injective m
  let Q : MvPolynomial (Σ _ : Fin m, Fin (n + 1)) (Polynomial ℂ) :=
    renameToFamilyShiftJets m n (familyReshapeJet m n P)
  let p : FiniteDifferentialPattern ℕ :=
    codedFamilyPatternOfRelation shiftCode hshiftCode P
  let shiftP : InjectiveShiftConfiguration (CarrierPatternShift p) :=
    ⟨shift.1, shift.2⟩
  let patternCoeff : PatternRow p → ℂ :=
    polynomialPatternCoefficientVector shiftCode hshiftCode (familyOrders m n) Q
  let coeff : CarrierPatternMonomial p × Fin (p.coefficientDegree + 1) → ℂ :=
    fun col => patternCoeff (Fintype.equivFin (PatternShape p) col)
  let carrier := weightedBoundaryCarrier F.base.toBoundaryFamily eta density
  have hrelation : F.weightedBoundaryCarrierExpandedPatternRelationHolds
      (row := CarrierPatternRow p) eta density p.coefficientDegree p.orders
        (carrierPatternExponent p) shiftP coeff := by
    intro packet hupper r
    let z : ℂ := packet.1 r
    let sigma := Σ i : CarrierPatternShift p, Fin (p.orders i)
    let y : CarrierPatternRow p × Fin (Fintype.card sigma) → ℂ :=
      F.weightedBoundaryCarrierExpandedPacketValue eta density p.orders packet shiftP
    let x : sigma → ℂ := fun t =>
      familyJetVec (n := n)
        (fun i w => cauchyTransform carrier (w + shift.1 i)) z
        (Sum.inr (t.1, t.2))
    have hy : ∀ t : sigma, y (r, Fintype.equivFin sigma t) = x t := by
      intro t
      simpa [y, x, p, Q, shiftP, shiftCode, carrier, codedFamilyPatternOfRelation,
        familyOrders] using!
        (F.weightedBoundaryCarrierExpandedPacketValue_eq_familyJetVec
          eta density packet shift r
          (⟨t.1, t.2⟩ : Σ _ : Fin m, Fin (n + 1)))
    have hprod : ∀ a : CarrierPatternMonomial p,
        (carrierPatternExponent p a).prod (fun k e => y (r, k) ^ e) =
          (p.jetExponent a).prod (fun t e => x t ^ e) := by
      intro a
      rw [carrierPatternExponent, Finsupp.equivCongrLeft_apply,
        Finsupp.prod_equivMapDomain]
      apply Finsupp.prod_congr
      intro t ht
      rw [hy t]
    have hsum :
        (∑ col, coeff col *
          expandedDifferentialEvaluationMatrix p.coefficientDegree
            (Fintype.card sigma) packet.1 (carrierPatternExponent p) y r col) =
          ∑ b : PatternRow p,
            patternCoeff b * z ^ patternDegree p b *
              (patternExponent p b).prod (fun t e => x t ^ e) := by
      apply Fintype.sum_equiv (Fintype.equivFin (PatternShape p))
      intro col
      rw [expandedDifferentialEvaluationMatrix_apply, hprod]
      simp [coeff, patternCoeff, patternDegree, patternExponent, z]
      ring
    rw [hsum]
    have hdomain : z ∈ commonLowerTranslationDomain shift := by
      intro i
      have hi := hupper (r, i)
      simpa [commonLowerTranslationDomain, combinedProjectiveRowShiftPacket,
        z, shiftP, p, codedFamilyPatternOfRelation] using hi
    calc
      (∑ b : PatternRow p,
          patternCoeff b * z ^ patternDegree p b *
            (patternExponent p b).prod (fun t e => x t ^ e)) =
          MvPolynomial.eval (Sum.elim (fun _ => z) fun q => x ⟨q.1, q.2⟩) P := by
            simpa [patternCoeff, p, Q] using!
              (codedFamilyPatternExpansion_eq_eval shiftCode hshiftCode P z x)
      _ = 0 := hPzero z hdomain
  have hcoeffZero := hfree p shiftP coeff hrelation
  have hpatternZero : ∀ b : PatternRow p, patternCoeff b = 0 := by
    intro b
    let col : PatternShape p := (Fintype.equivFin (PatternShape p)).symm b
    have hz := hcoeffZero col
    simpa [coeff, col] using hz
  have hP : P = 0 := familyJetRelation_eq_zero_of_codedPatternCoefficients_zero
    shiftCode hshiftCode P (by
      intro b
      exact hpatternZero b)
  exact hPne hP

/-- The same simultaneous finite-family no-relation law survives every normalized translated
Herglotz polynomial gauge. -/
theorem
    not_familyDifferentiallyAlgebraicOn_translatedHerglotz_of_allFinitePatterns_relationFree
    {m : ℕ}
    (eta : Measure (OnePoint ℝ)) [IsFiniteMeasure eta]
    (density : Lp ℝ (⊤ : ENNReal) eta)
    (hfree : ∀ (p : FiniteDifferentialPattern ℕ)
      (shift : InjectiveShiftConfiguration (CarrierPatternShift p))
      (coeff : CarrierPatternMonomial p × Fin (p.coefficientDegree + 1) → ℂ),
      F.weightedBoundaryCarrierExpandedPatternRelationHolds
        (row := CarrierPatternRow p) eta density p.coefficientDegree p.orders
          (carrierPatternExponent p) shift coeff →
        ∀ col, coeff col = 0)
    (shift : InjectiveShiftConfiguration (Fin m)) (M : ℂ) :
    ¬ FamilyDifferentiallyAlgebraicOn
      (fun i z => (z + shift.1 i) * M + (1 + (z + shift.1 i) ^ 2) *
        cauchyTransform
          (weightedBoundaryCarrier F.base.toBoundaryFamily eta density) (z + shift.1 i))
      (commonLowerTranslationDomain shift) := by
  intro hrel
  apply F.not_familyDifferentiallyAlgebraicOn_translatedCauchy_of_allFinitePatterns_relationFree
    eta density hfree shift
  exact familyDifferentiallyAlgebraicOn_translatedCauchy_of_presentation
    (weightedBoundaryCarrier F.base.toBoundaryFamily eta density) M shift.1
    (fun z hz i => ne_of_lt (hz i)) hrel

/-- **Residual singular-continuous full-translation family-freeness law.**  One dense residual
positive phase excludes every mixed differential relation among every finite family of distinct
Cauchy translates and every corresponding Herglotz family, while retaining the prescribed
singular-continuous Hamburger carrier. -/
theorem singularContinuousCarrier_fullTranslationFamilyFreeness_denseResidual
    {ιf : Type} [Fintype ιf] [DecidableEq ιf]
    (hCmin : HasMinimalExponentialType F.c)
    (hnoCommon : ∀ z, ¬ (F.c z = 0 ∧ F.d z = 0))
    {p0 : ℂ} (hCp : F.c p0 = 0) {c0 : ℂ} (hCc : F.c c0 ≠ 0)
    (hupperMap : ∀ z, z.im < 0 → 0 < (F.quotient z).im)
    (zf : ιf → ℂ)
    (hqf_inj : Function.Injective (fun i => F.quotient (zf i)))
    (hupperf : ∀ i, 0 < (F.quotient (zf i)).im)
    (nf : ιf → ℕ)
    (eta : ProbabilityMeasure (OnePoint ℝ))
    (hetaSC : eta ∈ projectiveSingularContinuousProbabilityLaws)
    (hnull : ∀ E : Set (OnePoint ℝ), MeasurableSet E →
      (projectiveLebesgueProbability : Measure (OnePoint ℝ)) E = 0 →
      (volume : Measure ℝ)
        (F.base.toBoundaryFamily.matrix.projectiveLabel ⁻¹' E) = 0) :
    let mu : Measure (OnePoint ℝ) := eta
    let frozen := normalizedProjectiveCauchyJetLinftyContinuousControl
      (fun i => F.quotient (zf i)) nf mu hupperf
    let S := LinearMap.ker frozen.toLinearMap
    let positiveChart : Set S := Metric.ball 0 1
    let universalPhase : Set positiveChart := {w | ∀
      (p : FiniteDifferentialPattern ℕ)
      (shift : InjectiveShiftConfiguration (CarrierPatternShift p))
      (coeff : CarrierPatternMonomial p × Fin (p.coefficientDegree + 1) → ℂ),
      F.weightedBoundaryCarrierExpandedPatternRelationHolds
        (row := CarrierPatternRow p) mu (linftyOne mu + w.1.1)
          p.coefficientDegree p.orders (carrierPatternExponent p) shift coeff →
        ∀ col, coeff col = 0}
    Dense universalPhase ∧ universalPhase ∈ residual positiveChart ∧
      (∀ t u : ℝ, t ≠ u →
        (F.base.leaf (t : OnePoint ℝ) : Measure ℝ) ⟂ₘ
            (F.base.leaf (u : OnePoint ℝ) : Measure ℝ) ∧
          (((F.base.leaf (t : OnePoint ℝ) : Measure ℝ).toSignedMeasure -
              (F.base.leaf (u : OnePoint ℝ) : Measure ℝ).toSignedMeasure).totalVariation
                Set.univ = 2)) ∧
      ∀ w : positiveChart,
        let density := linftyOne mu + w.1.1
        let carrier := weightedBoundaryCarrier F.base.toBoundaryFamily mu density
        LinftyStrictlyPositive mu density ∧
          ∫ t, density t ∂mu = 1 ∧
          IsProbabilityMeasure carrier ∧ NullSingletonClass carrier ∧
          carrier ⟂ₘ (volume : Measure ℝ) ∧
          MaximallySeparatedFromAbsolutelyContinuousProbabilities carrier ∧
          HasHamburgerMoments s carrier ∧
          (∀ n : ℕ,
            (HTGeometry.momentHankelMatrix s n).PosDef ∧
              0 < (HTGeometry.momentHankelMatrix s n).det) ∧
          (∀ d : ℕ,
            ¬ HTGeometry.FixedSpectralWidthLocalClosure d s ∧
              ¬ HTGeometry.FixedStateSpaceDimensionLocalClosure d s) ∧
          (¬ HTGeometry.HankelShiftInvariant s) ∧
          (∀ {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
            (v : ℕ → E),
            (∀ i j, inner ℝ (v i) (v j) = s (i + j)) →
            ¬ ∀ i j,
              inner ℝ (v (i + 1)) (v (j + 1)) = inner ℝ (v i) (v j)) ∧
          (w ∈ universalPhase →
            (∀ (m : ℕ) (shift : InjectiveShiftConfiguration (Fin m)),
                (¬ FamilyDifferentiallyAlgebraicOn
                  (fun i z => cauchyTransform carrier (z + shift.1 i))
                  (commonLowerTranslationDomain shift)) ∧
                ∀ M : ℂ,
                  ¬ FamilyDifferentiallyAlgebraicOn
                    (fun i z => (z + shift.1 i) * M + (1 + (z + shift.1 i) ^ 2) *
                      cauchyTransform carrier (z + shift.1 i))
                    (commonLowerTranslationDomain shift)) ∧
              Hypertranscendental (cauchyTransform carrier) ∧
              ∀ M : ℂ, Hypertranscendental
                (fun z => z * M + (1 + z ^ 2) * cauchyTransform carrier z)) := by
  dsimp only
  have hetaInfinite := projectiveSingularContinuousProbabilityLaw_support_infinite eta hetaSC
  let mu : Measure (OnePoint ℝ) := eta
  let frozen := normalizedProjectiveCauchyJetLinftyContinuousControl
    (fun i => F.quotient (zf i)) nf mu hupperf
  let S := LinearMap.ker frozen.toLinearMap
  let positiveChart : Set S := Metric.ball 0 1
  let universalPhase : Set positiveChart := {w | ∀
    (p : FiniteDifferentialPattern ℕ)
    (shift : InjectiveShiftConfiguration (CarrierPatternShift p))
    (coeff : CarrierPatternMonomial p × Fin (p.coefficientDegree + 1) → ℂ),
    F.weightedBoundaryCarrierExpandedPatternRelationHolds
      (row := CarrierPatternRow p) mu (linftyOne mu + w.1.1)
        p.coefficientDegree p.orders (carrierPatternExponent p) shift coeff →
      ∀ col, coeff col = 0}
  letI : IsProbabilityMeasure mu := eta.prop
  have hphase :
      Dense universalPhase ∧ universalPhase ∈ residual positiveChart ∧
        ∀ w : positiveChart,
          LinftyStrictlyPositive mu (linftyOne mu + w.1.1) ∧
            ∫ t, (linftyOne mu + w.1.1) t ∂mu = 1 := by
    simpa [universalPhase, positiveChart, frozen, S, mu] using
      (F.allFinitePatterns_positiveActualCarrier_relationFree_dense_residual
        (Γ := ℕ) hCmin hnoCommon hCp hCc hupperMap
        zf hqf_inj hupperf nf mu hetaInfinite)
  have hleaves : ∀ t u : ℝ, t ≠ u →
      (F.base.leaf (t : OnePoint ℝ) : Measure ℝ) ⟂ₘ
          (F.base.leaf (u : OnePoint ℝ) : Measure ℝ) ∧
        (((F.base.leaf (t : OnePoint ℝ) : Measure ℝ).toSignedMeasure -
            (F.base.leaf (u : OnePoint ℝ) : Measure ℝ).toSignedMeasure).totalVariation
              Set.univ = 2) := by
    intro t u htu
    have hsing := HTGeometry.mutuallySingular_leaf F.base htu
    exact ⟨hsing,
      HTGeometry.totalVariation_univ_eq_of_isProbability
        (F.base.leaf (t : OnePoint ℝ) : Measure ℝ)
        (F.base.leaf (u : OnePoint ℝ) : Measure ℝ) hsing⟩
  refine ⟨hphase.1, hphase.2.1, hleaves, ?_⟩
  intro w
  let density := linftyOne mu + w.1.1
  let carrier := weightedBoundaryCarrier F.base.toBoundaryFamily mu density
  have hpositive : LinftyStrictlyPositive mu density := hphase.2.2 w |>.1
  have hintegral : ∫ t, density t ∂mu = 1 := hphase.2.2 w |>.2
  have hstructure := weightedBoundaryCarrier_singularContinuous_probability
    F.base.toBoundaryFamily eta hetaSC hnull density hpositive hintegral
  letI : IsProbabilityMeasure carrier := hstructure.1
  letI : NullSingletonClass carrier := hstructure.2.1
  have hmaximalTV :=
    singularProbability_maximalTotalVariation_from_everyACProbability
      carrier hstructure.2.2.1
  have hstrictHankel :=
    strictHankelRay_of_atomlessProbability_hamburgerMoments
      carrier hstructure.2.2.2
  have hnoFiniteRealization :=
    noFiniteSpectralOrStateLocalClosure_of_strictHankelRay
      (fun n => (hstrictHankel n).2)
  have hnoShiftInvariantGram :=
    noShiftInvariantGramRealization_of_strictHankelRay
      (fun n => (hstrictHankel n).1)
  refine ⟨hpositive, hintegral, hstructure.1, hstructure.2.1,
    hstructure.2.2.1, hmaximalTV, hstructure.2.2.2, hstrictHankel,
    hnoFiniteRealization, hnoShiftInvariantGram.1,
    hnoShiftInvariantGram.2, ?_⟩
  intro hw
  have hfree : ∀ (p : FiniteDifferentialPattern ℕ)
      (shift : InjectiveShiftConfiguration (CarrierPatternShift p))
      (coeff : CarrierPatternMonomial p × Fin (p.coefficientDegree + 1) → ℂ),
      F.weightedBoundaryCarrierExpandedPatternRelationHolds
        (row := CarrierPatternRow p) mu density p.coefficientDegree p.orders
          (carrierPatternExponent p) shift coeff →
        ∀ col, coeff col = 0 := by
    simpa only [universalPhase, Set.mem_setOf_eq] using hw
  have hfamily : ∀ (m : ℕ) (shift : InjectiveShiftConfiguration (Fin m)),
      (¬ FamilyDifferentiallyAlgebraicOn
        (fun i z => cauchyTransform carrier (z + shift.1 i))
        (commonLowerTranslationDomain shift)) ∧
      ∀ M : ℂ,
        ¬ FamilyDifferentiallyAlgebraicOn
          (fun i z => (z + shift.1 i) * M + (1 + (z + shift.1 i) ^ 2) *
            cauchyTransform carrier (z + shift.1 i))
          (commonLowerTranslationDomain shift) := by
    intro m shift
    have hcauchy :=
      F.not_familyDifferentiallyAlgebraicOn_translatedCauchy_of_allFinitePatterns_relationFree
        mu density hfree shift
    have hherglotz : ∀ M : ℂ,
        ¬ FamilyDifferentiallyAlgebraicOn
          (fun i z => (z + shift.1 i) * M + (1 + (z + shift.1 i) ^ 2) *
            cauchyTransform carrier (z + shift.1 i))
          (commonLowerTranslationDomain shift) :=
      fun M =>
        F.not_familyDifferentiallyAlgebraicOn_translatedHerglotz_of_allFinitePatterns_relationFree
          mu density hfree shift M
    exact ⟨hcauchy, hherglotz⟩
  refine ⟨hfamily, ?_⟩
  have hfreeUnit :=
    F.allFinitePatterns_relationFree_of_shiftPaletteEmbedding
      mu density (fun _ : Unit => 0) (fun _ _ _ => Subsingleton.elim _ _) hfree
  have hlocal :=
    F.not_differentiallyAlgebraicOn_cauchyTransform_weightedBoundaryCarrier
      mu density hfreeUnit
  exact cauchyHerglotz_lowerHalfPlane_globalHypertranscendence carrier hlocal

end ClassicalAnalyticNevanlinnaCarrierFamily

end

end GaloisForLFunctions.HTGeometry
