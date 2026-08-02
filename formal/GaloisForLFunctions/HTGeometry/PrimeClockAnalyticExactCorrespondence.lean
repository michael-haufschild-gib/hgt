import GaloisForLFunctions.HTGeometry.AnalyticEulerTailExactFaithfulnessUniversalityLaw
import GaloisForLFunctions.HTGeometry.PrimeClockAnalyticEulerCompletion
import GaloisForLFunctions.HTGeometry.SourceLogarithmicBoundary

/-!
# Exact analytic prime-clock correspondence

For finite-abscissa Dirichlet sources supported on positive prime powers, analytic realization has
an exact source-side classifier after adjoining the rational coordinate and all finite-prime Euler
germs.  Differential independence is equivalent to linear independence of the complete
logarithmic clock orbit modulo finite prime rays.  The relative form identifies the precise
quotient by an arbitrary free old clock module.

This closes the converse absent from the one-way analytic transfer theorem: neither analytic
continuation nor the genuine coordinate can create, destroy, or identify a prime-clock direction.
-/

namespace GaloisForLFunctions.HTGeometry

open ArithmeticFunction Set
open scoped Differential

noncomputable section

attribute [local instance]
  analyticObservableUpperEndAnalyticDomain
  analyticObservableUpperEndMeroComplexAlgebra
  analyticObservableUpperEndMeroDifferential

local instance pulledCoordinateComplexAlgebra :
    Algebra ℂ analyticPulledFinitePrimeCoordinateField :=
  ((algebraMap finiteAbscissaFinitePrimeCoefficientField
      analyticPulledFinitePrimeCoordinateField).comp
    (algebraMap ℂ finiteAbscissaFinitePrimeCoefficientField)).toAlgebra

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 300000

/-- Algebraic independence over the intrinsic finite-prime field transfers faithfully to the
finite-abscissa fraction model over its pulled-back coefficient field. -/
theorem algebraicIndependent_finiteAbscissaFraction_over_pulledFinitePrime
    {I : Type*} (f : I → finiteAbscissaArithmeticSubalgebra)
    (hf : AlgebraicIndependent finitePrimeCoefficientField
      (fun i => algebraMap (ArithmeticFunction ℂ)
        arithmeticFunctionFractionField (f i).1)) :
    AlgebraicIndependent finiteAbscissaFinitePrimeCoefficientField
      (fun i => algebraMap finiteAbscissaArithmeticSubalgebra
        finiteAbscissaDirichletFractionField (f i)) := by
  let kToF := finiteAbscissaFinitePrimeToFinitePrimeCoefficient
  letI : Algebra finiteAbscissaFinitePrimeCoefficientField
      finitePrimeCoefficientField := kToF.toAlgebra
  let kToA : finiteAbscissaFinitePrimeCoefficientField →+*
      arithmeticFunctionFractionField :=
    finiteAbscissaFractionToArithmeticFraction.comp
      finiteAbscissaFinitePrimeCoefficientField.subtype
  letI : Algebra finiteAbscissaFinitePrimeCoefficientField
      arithmeticFunctionFractionField := kToA.toAlgebra
  letI : IsScalarTower finiteAbscissaFinitePrimeCoefficientField
      finitePrimeCoefficientField arithmeticFunctionFractionField :=
    .of_algebraMap_eq fun x => rfl
  let h : finiteAbscissaDirichletFractionField →ₐ[
      finiteAbscissaFinitePrimeCoefficientField]
      arithmeticFunctionFractionField :=
    { __ := finiteAbscissaFractionToArithmeticFraction
      commutes' := fun x => rfl }
  have hfK : AlgebraicIndependent finiteAbscissaFinitePrimeCoefficientField
      (fun i => algebraMap (ArithmeticFunction ℂ)
        arithmeticFunctionFractionField (f i).1) :=
    hf.restrictScalars finiteAbscissaFinitePrimeToFinitePrimeCoefficient_injective
  apply (AlgHom.algebraicIndependent_iff h
    finiteAbscissaFractionToArithmeticFraction_injective).mp
  convert hfK using 1
  funext i
  exact finiteAbscissaFractionToArithmeticFraction_algebraMap (f i)

/-- Clock freeness is sufficient for analytic differential freeness even over the enlarged
coordinate field containing every finite-prime Euler germ. -/
theorem differentialIndependent_finiteAbscissaPrimeProfiles_over_pulledCoordinate_of_clock
    {I : Type*}
    (f : I → finiteAbscissaArithmeticSubalgebra)
    (hsupport : ∀ i, PrimeProfileSupportedOnPositivePrimePowers (f i).1)
    (hclock : PrimeProfileClockIndependent (fun i => (f i).1)) :
    GaloisForLFunctions.DifferentialIndependent
      analyticPulledFinitePrimeCoordinateField
      (fun i => finiteAbscissaLSeriesToUpperEndMero (f i)) := by
  let sourceJets : I × Nat → finiteAbscissaArithmeticSubalgebra := fun q =>
    (finiteAbscissaRotatedDeriv^[q.2]) (f q.1)
  have hsourceSupport : ∀ q,
      PrimeProfileSupportedOnPositivePrimePowers (sourceJets q).1 := by
    intro q n hn
    exact hsupport q.1
      (by
        rw [finiteAbscissaRotatedDeriv_iterate_apply] at hn
        exact fun hzero => hn (by simp [hzero]))
  have hclockJets : LinearIndependent ℂ
      (fun q => primeProfileClockClass (sourceJets q).1) := by
    have hfamily :
        (fun q => primeProfileClockClass (sourceJets q).1) =
          primeProfileClockJetFamily (fun i => (f i).1) := by
      funext q
      congr 1
      apply ArithmeticFunction.ext
      intro n
      exact finiteAbscissaRotatedDeriv_iterate_apply (f q.1) q.2 n
    rw [hfamily]
    exact hclock
  have hformal : AlgebraicIndependent finitePrimeCoefficientField
      (fun q => algebraMap (ArithmeticFunction ℂ)
        arithmeticFunctionFractionField (sourceJets q).1) :=
    (algebraicIndependent_fractionPrimeProfiles_iff_clockClassIndependent_arbitrary
      (fun q => (sourceJets q).1) hsourceSupport).mpr hclockJets
  have hfraction :=
    algebraicIndependent_finiteAbscissaFraction_over_pulledFinitePrime
      sourceJets hformal
  have hanalytic :=
    algebraicIndependent_finiteAbscissaLSeries_over_pulledFinitePrimeCoordinate
      sourceJets hfraction
  unfold GaloisForLFunctions.DifferentialIndependent
  convert hanalytic using 1
  funext q
  exact differentialJet_finiteAbscissaLSeriesToUpperEndMero (f q.1) q.2

/-- Analytic differential freeness over the coordinate--finite-Euler base detects the entire
prime-clock orbit: the analytic realization has no additional kernel. -/
theorem primeProfileClockIndependent_of_differentialIndependent_pulledCoordinate
    {I : Type*}
    (f : I → finiteAbscissaArithmeticSubalgebra)
    (hsupport : ∀ i, PrimeProfileSupportedOnPositivePrimePowers (f i).1)
    (hDI : GaloisForLFunctions.DifferentialIndependent
      analyticPulledFinitePrimeCoordinateField
      (fun i => finiteAbscissaLSeriesToUpperEndMero (f i))) :
    PrimeProfileClockIndependent (fun i => (f i).1) := by
  classical
  let sourceJets : I × Nat → finiteAbscissaArithmeticSubalgebra := fun q =>
    (finiteAbscissaRotatedDeriv^[q.2]) (f q.1)
  let carrierJets : I × Nat → upperEndMeroField := fun q =>
    GaloisForLFunctions.differentialJet q.2
      (finiteAbscissaLSeriesToUpperEndMero (f q.1))
  have hsourceSupport : ∀ q,
      PrimeProfileSupportedOnPositivePrimePowers (sourceJets q).1 := by
    intro q n hn
    apply hsupport q.1
    rw [finiteAbscissaRotatedDeriv_iterate_apply] at hn
    exact fun hzero => hn (by simp [hzero])
  have hAI : AlgebraicIndependent analyticPulledFinitePrimeCoordinateField
      carrierJets := by
    unfold GaloisForLFunctions.DifferentialIndependent at hDI
    simpa only [carrierJets] using hDI
  unfold PrimeProfileClockIndependent
  rw [linearIndependent_iff]
  intro a ha
  let combo : finiteAbscissaArithmeticSubalgebra :=
    Finsupp.linearCombination ℂ sourceJets a
  have hcomboVal : combo.1 =
      Finsupp.linearCombination ℂ (fun q => (sourceJets q).1) a := by
    apply ArithmeticFunction.ext
    intro n
    simp [combo, Finsupp.linearCombination_apply, Finsupp.sum]
  have hsourceClass :
      (fun q => primeProfileClockClass (sourceJets q).1) =
        primeProfileClockJetFamily (fun i => (f i).1) := by
    funext q
    congr 1
    apply ArithmeticFunction.ext
    intro n
    exact finiteAbscissaRotatedDeriv_iterate_apply (f q.1) q.2 n
  have hcomboClass : primeProfileClockClass combo.1 = 0 := by
    calc
      primeProfileClockClass combo.1 =
          Finsupp.linearCombination ℂ
            (fun q => primeProfileClockClass (sourceJets q).1) a := by
        rw [hcomboVal]
        rw [Finsupp.linearCombination_apply, Finsupp.linearCombination_apply,
          map_finsuppSum]
        simp only [map_smul]
      _ = Finsupp.linearCombination ℂ
          (primeProfileClockJetFamily (fun i => (f i).1)) a := by
        rw [hsourceClass]
      _ = 0 := ha
  have hcomboLocal : PrimePowerClockLocal
      (primePowerCoordinateProfile combo.1) := by
    unfold primeProfileClockClass at hcomboClass
    change primePowerCoordinateProfile combo.1 ∈
      rayLocalSubmodule primePowerClockRay
    simpa only [LinearMap.comp_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero] using! hcomboClass
  have hcomboSupport :
      PrimeProfileSupportedOnPositivePrimePowers combo.1 := by
    intro n hn
    by_contra hnone
    have hzero : ∀ q, (sourceJets q).1 n = 0 := by
      intro q
      by_contra hq
      exact hnone (hsourceSupport q hq)
    have hsum : ∀ s : Finset (I × Nat),
        (∑ q ∈ s, a q • (sourceJets q).1) n = 0 := by
      intro s
      induction s using Finset.induction_on with
      | empty => simp
      | @insert q s hq ih =>
          rw [Finset.sum_insert hq, ArithmeticFunction.add_apply,
            ArithmeticFunction.smul_map, hzero q, smul_zero, ih, zero_add]
    apply hn
    rw [hcomboVal,
      Finsupp.linearCombination_apply_of_mem_supported ℂ
        (Finsupp.mem_supported_support ℂ a)]
    exact hsum a.support
  have hcomboFinite :
      algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField combo.1 ∈
        finitePrimeCoefficientField :=
    algebraMap_primeProfile_mem_finitePrimeCoefficientField_of_local
      combo.1 hcomboSupport hcomboLocal
  have hcomboBase : finiteAbscissaLSeriesToUpperEndMero combo ∈
      analyticPulledFinitePrimeCoordinateField :=
    finiteAbscissaLSeries_mem_pulledFinitePrimeCoordinate combo hcomboFinite
  have hcarrier :
      a.sum (fun q z =>
        algebraMap ℂ upperEndMeroField z * carrierJets q) =
          finiteAbscissaLSeriesToUpperEndMero combo := by
    change _ =
      finiteAbscissaLSeriesToUpperEndMero
        (Finsupp.linearCombination ℂ sourceJets a)
    rw [Finsupp.linearCombination_apply, map_finsuppSum]
    unfold Finsupp.sum
    apply Finset.sum_congr rfl
    intro q hq
    change algebraMap ℂ upperEndMeroField (a q) * carrierJets q =
      finiteAbscissaLSeriesToUpperEndMero ((a q) • sourceJets q)
    rw [Algebra.smul_def, map_mul]
    rw [finiteAbscissaLSeriesToUpperEndMero.commutes]
    dsimp only [carrierJets]
    congr 1
    exact differentialJet_finiteAbscissaLSeriesToUpperEndMero (f q.1) q.2
  by_contra hane
  have ha0 : a ≠ 0 := hane
  let b : analyticPulledFinitePrimeCoordinateField :=
    ⟨finiteAbscissaLSeriesToUpperEndMero combo, hcomboBase⟩
  let P : MvPolynomial (I × Nat) analyticPulledFinitePrimeCoordinateField :=
    a.sum (fun q z =>
      MvPolynomial.C
        (algebraMap ℂ analyticPulledFinitePrimeCoordinateField z) *
          MvPolynomial.X q) - MvPolynomial.C b
  have hPne : P ≠ 0 :=
    primeClock_finsuppLinearPolynomial_sub_C_ne_zero a ha0 b
  have hscalar : ∀ z : ℂ,
      algebraMap analyticPulledFinitePrimeCoordinateField upperEndMeroField
          (algebraMap ℂ analyticPulledFinitePrimeCoordinateField z) =
        algebraMap ℂ upperEndMeroField z := by
    intro z
    change finiteAbscissaFractionToUpperEndMero
        (algebraMap ℂ finiteAbscissaDirichletFractionField z) =
      algebraMap ℂ upperEndMeroField z
    rw [show algebraMap ℂ finiteAbscissaDirichletFractionField z =
        algebraMap finiteAbscissaArithmeticSubalgebra
          finiteAbscissaDirichletFractionField
            (algebraMap ℂ finiteAbscissaArithmeticSubalgebra z) from
      (IsScalarTower.algebraMap_apply ℂ finiteAbscissaArithmeticSubalgebra
        finiteAbscissaDirichletFractionField z).symm,
      finiteAbscissaFractionToUpperEndMero_algebraMap]
    exact finiteAbscissaLSeriesToUpperEndMero.commutes z
  have hPzero : MvPolynomial.aeval carrierJets P = 0 := by
    simp only [P, Finsupp.sum, map_sub, map_sum, map_mul,
      MvPolynomial.aeval_C, MvPolynomial.aeval_X]
    simp_rw [hscalar]
    change a.sum (fun q z =>
      algebraMap ℂ upperEndMeroField z * carrierJets q) - b.1 = 0
    rw [hcarrier]
    change finiteAbscissaLSeriesToUpperEndMero combo -
      finiteAbscissaLSeriesToUpperEndMero combo = 0
    exact sub_self _
  exact hPne (hAI.eq_zero_of_aeval_eq_zero P hPzero)

/-- **Exact analytic prime-clock law.**  For an arbitrary finite-abscissa positive-prime-power
family, differential independence over the coordinate field completed by every finite-prime Euler
germ is equivalent to linear independence of its complete logarithmic clock orbit modulo finite
prime rays. -/
theorem differentialIndependent_finiteAbscissaPrimeProfiles_over_pulledCoordinate_iff_clock
    {I : Type*}
    (f : I → finiteAbscissaArithmeticSubalgebra)
    (hsupport : ∀ i, PrimeProfileSupportedOnPositivePrimePowers (f i).1) :
    GaloisForLFunctions.DifferentialIndependent
        analyticPulledFinitePrimeCoordinateField
        (fun i => finiteAbscissaLSeriesToUpperEndMero (f i)) ↔
      PrimeProfileClockIndependent (fun i => (f i).1) := by
  exact ⟨
    primeProfileClockIndependent_of_differentialIndependent_pulledCoordinate
      f hsupport,
    differentialIndependent_finiteAbscissaPrimeProfiles_over_pulledCoordinate_of_clock
      f hsupport⟩

/-- **Exact relative analytic prime-clock law.**  If the old finite-abscissa sources freely
generate their clock module, then a new analytic family is differentially independent over the
old analytic differential field exactly when all of its clock jets are independent modulo the
complete old clock submodule. -/
theorem differentialIndependent_finiteAbscissaPrimeProfiles_relative_iff_clockQuotient
    {I H : Type*}
    (c : I → finiteAbscissaArithmeticSubalgebra)
    (g : H → finiteAbscissaArithmeticSubalgebra)
    (hcsupport : ∀ i, PrimeProfileSupportedOnPositivePrimePowers (c i).1)
    (hgsupport : ∀ h, PrimeProfileSupportedOnPositivePrimePowers (g h).1)
    (hc : PrimeProfileClockIndependent (fun i => (c i).1)) :
    GaloisForLFunctions.DifferentialIndependent
        (GaloisForLFunctions.differentialAdjoin
          analyticPulledFinitePrimeCoordinateField
          (Set.range (fun i => finiteAbscissaLSeriesToUpperEndMero (c i))))
        (fun h => finiteAbscissaLSeriesToUpperEndMero (g h)) ↔
      PrimeProfileRelativeClockIndependent
        (fun i => (c i).1) (fun h => (g h).1) := by
  let oldCarrier : I → upperEndMeroField := fun i =>
    finiteAbscissaLSeriesToUpperEndMero (c i)
  let newCarrier : H → upperEndMeroField := fun h =>
    finiteAbscissaLSeriesToUpperEndMero (g h)
  let profile : I ⊕ H → finiteAbscissaArithmeticSubalgebra :=
    Sum.elim c g
  have hold : GaloisForLFunctions.DifferentialIndependent
      analyticPulledFinitePrimeCoordinateField oldCarrier := by
    apply
      (differentialIndependent_finiteAbscissaPrimeProfiles_over_pulledCoordinate_iff_clock
        c hcsupport).mpr
    exact hc
  have hprofileSupport : ∀ z,
      PrimeProfileSupportedOnPositivePrimePowers (profile z).1 := by
    intro z
    rcases z with i | h
    · exact hcsupport i
    · exact hgsupport h
  have hclockSplit :
      PrimeProfileClockIndependent (fun z => (profile z).1) ↔
        PrimeProfileClockIndependent (fun i => (c i).1) ∧
          PrimeProfileRelativeClockIndependent
            (fun i => (c i).1) (fun h => (g h).1) := by
    have hprofileVal :
        (fun z => (profile z).1) =
          Sum.elim (fun i => (c i).1) (fun h => (g h).1) := by
      funext z
      rcases z with i | h <;> rfl
    rw [hprofileVal, primeProfileClockIndependent_sumElim_iff,
      linearIndependent_sumElim_iff_quotient]
    rfl
  have hprofileCarrier :
      (fun z => finiteAbscissaLSeriesToUpperEndMero (profile z)) =
        Sum.elim oldCarrier newCarrier := by
    funext z
    rcases z with i | h <;> rfl
  constructor
  · intro hrel
    have hjoint : GaloisForLFunctions.DifferentialIndependent
        analyticPulledFinitePrimeCoordinateField
        (Sum.elim oldCarrier newCarrier) :=
      (GaloisForLFunctions.differentialIndependent_sumElim_iff
        oldCarrier newCarrier).mpr ⟨hold, by
          simpa only [oldCarrier, newCarrier] using hrel⟩
    have hprofileDI : GaloisForLFunctions.DifferentialIndependent
        analyticPulledFinitePrimeCoordinateField
        (fun z => finiteAbscissaLSeriesToUpperEndMero (profile z)) := by
      rw [hprofileCarrier]
      exact hjoint
    have hclock :=
      (differentialIndependent_finiteAbscissaPrimeProfiles_over_pulledCoordinate_iff_clock
        profile hprofileSupport).mp hprofileDI
    exact (hclockSplit.mp hclock).2
  · intro hquot
    have hclock : PrimeProfileClockIndependent (fun z => (profile z).1) :=
      hclockSplit.mpr ⟨hc, hquot⟩
    have hprofileDI :=
      (differentialIndependent_finiteAbscissaPrimeProfiles_over_pulledCoordinate_iff_clock
        profile hprofileSupport).mpr hclock
    have hjoint : GaloisForLFunctions.DifferentialIndependent
        analyticPulledFinitePrimeCoordinateField
        (Sum.elim oldCarrier newCarrier) := by
      rw [← hprofileCarrier]
      exact hprofileDI
    have hrel :=
      (GaloisForLFunctions.differentialIndependent_sumElim_iff
        oldCarrier newCarrier).mp hjoint |>.2
    simpa only [oldCarrier, newCarrier] using hrel

end

end GaloisForLFunctions.HTGeometry
