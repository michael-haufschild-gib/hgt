import GaloisForLFunctions.HTGeometry.FixedDivisorTranslationFreeness
import GaloisForLFunctions.HTGeometry.MovingCanonicalUpperEndDifferentialIndependence
import GaloisForLFunctions.HTGeometry.DifferentialIndependentFieldUniversality
import GaloisForLFunctions.HTGeometry.UpperEndRatfuncDifferentialAlgebra

/-!
# Fixed-divisor full-translation differential-field universality

Functional relation-freeness of an entire exponential gauge is promoted to genuine differential
independence in the upper-end meromorphic field. This closes the fixed-divisor genericity theorem
at object and generated-field level.
-/

open scoped Differential

namespace GaloisForLFunctions.HTGeometry

open Set Topology
open GaloisForLFunctions

noncomputable section

def fixedDivisorGaugedTranslatedUpperEndMero
    (W : ℂ → ℂ) (hWd : Differentiable ℂ W)
    (g : EntireGauge) (h : ℂ) : upperEndMeroField :=
  analyticUpperEndMero
    (fun z => W (z + h) * Complex.exp ((g : C(ℂ, ℂ)) (z + h))) 0 (by
      intro z hz
      have hbase : AnalyticOnNhd ℂ
          (fun w => W w * Complex.exp ((g : C(ℂ, ℂ)) w)) Set.univ :=
        (hWd.mul g.2.cexp).differentiableOn.analyticOnNhd isOpen_univ
      change AnalyticAt ℂ
        ((fun w => W w * Complex.exp ((g : C(ℂ, ℂ)) w)) ∘ fun w => w + h) z
      exact AnalyticAt.comp (hbase (z + h) (Set.mem_univ _))
        (analyticAt_id.add analyticAt_const))

theorem fixedDivisorGaugedFiniteTranslation_upperEnd_differentialIndependent
    {W : ℂ → ℂ} (hWd : Differentiable ℂ W) (g : EntireGauge)
    {m : ℕ} (shift : InjectiveShiftConfiguration (Fin m))
    (hfree : ¬ FamilyDifferentiallyAlgebraicOn
      (fun i z => W (z + shift.1 i) *
        Complex.exp ((g : C(ℂ, ℂ)) (z + shift.1 i))) Set.univ) :
    letI := isDomain_upperEndAnalyticSubring
    letI : Algebra (RatFunc ℂ) upperEndMeroField := upperEndRatfuncToMero.toAlgebra
    letI := ratFuncCoordinateDifferential
    letI := upperEndMeroFieldDifferential
    letI := upperEndRatfuncDifferentialAlgebra
    DifferentialIndependent (RatFunc ℂ)
      (fun i => fixedDivisorGaugedTranslatedUpperEndMero W hWd g (shift.1 i)) := by
  let family : Fin m → ℂ → ℂ := fun i z =>
    W (z + shift.1 i) * Complex.exp ((g : C(ℂ, ℂ)) (z + shift.1 i))
  let H : Fin m → ℝ := fun _ => 0
  have hbase : AnalyticOnNhd ℂ
      (fun w => W w * Complex.exp ((g : C(ℂ, ℂ)) w)) Set.univ :=
    (hWd.mul g.2.cexp).differentiableOn.analyticOnNhd isOpen_univ
  have hfamily : ∀ i, AnalyticOnNhd ℂ (family i) Set.univ := by
    intro i z hz
    change AnalyticAt ℂ
      ((fun w => W w * Complex.exp ((g : C(ℂ, ℂ)) w)) ∘
        fun w => w + shift.1 i) z
    exact AnalyticAt.comp (hbase (z + shift.1 i) (Set.mem_univ _))
      (analyticAt_id.add analyticAt_const)
  have hg : ∀ i, AnalyticOnNhd ℂ (family i) (upperTail (H i)) := by
    intro i z hz
    exact hfamily i z (Set.mem_univ _)
  have hgU : ∀ i, AnalyticOnNhd ℂ (family i) Set.univ := by
    exact hfamily
  have hcofinal : ∀ L : ℝ, ∃ z ∈ (Set.univ : Set ℂ), z ∈ upperTail L := by
    intro L
    refine ⟨Complex.I * (L + 1), Set.mem_univ _, ?_⟩
    simp [upperTail]
  simpa [family, H, fixedDivisorGaugedTranslatedUpperEndMero] using
    analyticUpperEndFiniteFamily_differentialIndependent
      family H hg hgU isPreconnected_univ hcofinal hfree

theorem fixedDivisorGaugedTranslation_upperEnd_differentialIndependent
    {W : ℂ → ℂ} (hWd : Differentiable ℂ W) (g : EntireGauge)
    (hfree : ∀ (mm : ℕ) (shift : InjectiveShiftConfiguration (Fin mm)),
      ¬ FamilyDifferentiallyAlgebraicOn
        (fun i z => W (z + shift.1 i) *
          Complex.exp ((g : C(ℂ, ℂ)) (z + shift.1 i))) Set.univ) :
    letI := isDomain_upperEndAnalyticSubring
    letI : Algebra (RatFunc ℂ) upperEndMeroField := upperEndRatfuncToMero.toAlgebra
    letI := upperEndMeroFieldDifferential
    DifferentialIndependent (RatFunc ℂ)
      (fixedDivisorGaugedTranslatedUpperEndMero W hWd g) := by
  letI := isDomain_upperEndAnalyticSubring
  letI : Algebra ℤ upperEndAnalyticSubring := Ring.toIntAlgebra _
  letI : Algebra ℤ upperEndMeroField := Ring.toIntAlgebra _
  letI : Algebra (RatFunc ℂ) upperEndMeroField := upperEndRatfuncToMero.toAlgebra
  letI := ratFuncCoordinateDifferential
  letI := upperEndMeroFieldDifferential
  letI := upperEndRatfuncDifferentialAlgebra
  unfold DifferentialIndependent
  apply algebraicIndependent_of_finite_type
  intro t ht
  let s : Set ℂ := Prod.fst '' t
  have hs : s.Finite := ht.image Prod.fst
  letI : Finite s := hs
  letI : Fintype s := Fintype.ofFinite s
  let eShift : s ≃ Fin (Fintype.card s) := Fintype.equivFin s
  let shift : InjectiveShiftConfiguration (Fin (Fintype.card s)) :=
    ⟨fun i => (eShift.symm i).1, by
      intro i j hij
      apply eShift.symm.injective
      exact Subtype.ext hij⟩
  have hfin := fixedDivisorGaugedFiniteTranslation_upperEnd_differentialIndependent
    hWd g shift (hfree _ shift)
  have hsDI : DifferentialIndependent (RatFunc ℂ)
      (fun h : s => fixedDivisorGaugedTranslatedUpperEndMero W hWd g h.1) := by
    have hcomp := hfin.comp eShift eShift.injective
    simpa [shift, Function.comp_def] using hcomp
  unfold DifferentialIndependent at hsDI
  let et : t → s × ℕ := fun p =>
    (⟨p.1.1, ⟨p.1, p.2, rfl⟩⟩, p.1.2)
  have het : Function.Injective et := by
    intro p q hpq
    apply Subtype.ext
    apply Prod.ext
    · exact congrArg (fun x : s × ℕ => x.1.1) hpq
    · exact congrArg (fun x : s × ℕ => x.2) hpq
  have hcomp := hsDI.comp et het
  simpa [et, s] using! hcomp

/-- The exact fixed-divisor card endpoint: one residual gauge phase preserves the complete
divisor and realizes a genuinely free full complex translation family over `ℂ(z)`. -/
theorem fixedDivisor_fullTranslationUpperEndDifferentialIndependence_denseResidual
    {W : ℂ → ℂ} (hWd : Differentiable ℂ W) (h0 : ∃ w, W w ≠ 0) :
    let universalPhase : Set EntireGauge := {g |
      ∀ (p : FiniteDifferentialPattern ℕ)
        (shift : InjectiveShiftConfiguration
          (ClassicalAnalyticNevanlinnaCarrierFamily.CarrierPatternShift p))
        (coeff : ClassicalAnalyticNevanlinnaCarrierFamily.CarrierPatternMonomial p ×
          Fin (p.coefficientDegree + 1) → ℂ),
        gaugeExpandedPatternRelationHolds (row :=
          ClassicalAnalyticNevanlinnaCarrierFamily.CarrierPatternRow p)
          W p.coefficientDegree p.orders
          (ClassicalAnalyticNevanlinnaCarrierFamily.carrierPatternExponent p)
          g shift coeff → ∀ col, coeff col = 0}
    Dense universalPhase ∧ universalPhase ∈ residual EntireGauge ∧
      (∀ (g : EntireGauge) (z : ℂ),
        analyticOrderAt (fun w => W w * Complex.exp ((g : C(ℂ, ℂ)) w)) z =
          analyticOrderAt W z) ∧
      ∀ g ∈ universalPhase,
        letI := isDomain_upperEndAnalyticSubring
        letI : Algebra (RatFunc ℂ) upperEndMeroField := upperEndRatfuncToMero.toAlgebra
        letI := upperEndMeroFieldDifferential
        DifferentialIndependent (RatFunc ℂ)
          (fixedDivisorGaugedTranslatedUpperEndMero W hWd g) := by
  dsimp only
  obtain ⟨hdense, hresidual, -, -, hfree⟩ :=
    fixedDivisor_fullTranslationFreeness_denseResidual hWd h0
  refine ⟨hdense, hresidual, fun g z => analyticOrderAt_gaugeCarrier hWd g z, ?_⟩
  intro g hg
  exact fixedDivisorGaugedTranslation_upperEnd_differentialIndependent hWd g (hfree g hg)

/-- Any two prescribed entire divisors admit free representatives whose labelled generated
differential fields are canonically isomorphic, jet by jet. -/
theorem exists_pair_fixedDivisor_freeDifferentialFieldEquiv
    {W₀ W₁ : ℂ → ℂ}
    (hW₀ : Differentiable ℂ W₀) (h₀ : ∃ w, W₀ w ≠ 0)
    (hW₁ : Differentiable ℂ W₁) (h₁ : ∃ w, W₁ w ≠ 0) :
    letI := isDomain_upperEndAnalyticSubring
    letI : Algebra (RatFunc ℂ) upperEndMeroField := upperEndRatfuncToMero.toAlgebra
    letI := ratFuncCoordinateDifferential
    letI := upperEndMeroFieldDifferential
    letI := upperEndRatfuncDifferentialAlgebra
    ∃ g₀ g₁ : EntireGauge,
      (∀ z, analyticOrderAt
        (fun w => W₀ w * Complex.exp ((g₀ : C(ℂ, ℂ)) w)) z = analyticOrderAt W₀ z) ∧
      (∀ z, analyticOrderAt
        (fun w => W₁ w * Complex.exp ((g₁ : C(ℂ, ℂ)) w)) z = analyticOrderAt W₁ z) ∧
      let x₀ := fixedDivisorGaugedTranslatedUpperEndMero W₀ hW₀ g₀
      let x₁ := fixedDivisorGaugedTranslatedUpperEndMero W₁ hW₁ g₁
      DifferentialIndependent (RatFunc ℂ) x₀ ∧
      DifferentialIndependent (RatFunc ℂ) x₁ ∧
      ∃ e : differentialAdjoin (RatFunc ℂ) (Set.range x₀) ≃ₐ[RatFunc ℂ]
          differentialAdjoin (RatFunc ℂ) (Set.range x₁),
        (∀ h n,
          e ⟨differentialJet n (x₀ h),
              differentialJet_mem_differentialAdjoin (RatFunc ℂ)
                (Set.mem_range_self h) n⟩ =
            ⟨differentialJet n (x₁ h),
              differentialJet_mem_differentialAdjoin (RatFunc ℂ)
                (Set.mem_range_self h) n⟩) ∧
        ∀ z, e z′ = (e z)′ := by
  letI := isDomain_upperEndAnalyticSubring
  letI : Algebra ℤ upperEndAnalyticSubring := Ring.toIntAlgebra _
  letI : Algebra ℤ upperEndMeroField := Ring.toIntAlgebra _
  letI : Algebra (RatFunc ℂ) upperEndMeroField := upperEndRatfuncToMero.toAlgebra
  letI := ratFuncCoordinateDifferential
  letI := upperEndMeroFieldDifferential
  letI := upperEndRatfuncDifferentialAlgebra
  obtain ⟨hdense₀, -, horder₀, hfree₀⟩ :=
    fixedDivisor_fullTranslationUpperEndDifferentialIndependence_denseResidual hW₀ h₀
  obtain ⟨hdense₁, -, horder₁, hfree₁⟩ :=
    fixedDivisor_fullTranslationUpperEndDifferentialIndependence_denseResidual hW₁ h₁
  obtain ⟨g₀, hg₀⟩ := hdense₀.nonempty
  obtain ⟨g₁, hg₁⟩ := hdense₁.nonempty
  let x₀ := fixedDivisorGaugedTranslatedUpperEndMero W₀ hW₀ g₀
  let x₁ := fixedDivisorGaugedTranslatedUpperEndMero W₁ hW₁ g₁
  have hx₀ : DifferentialIndependent (RatFunc ℂ) x₀ := hfree₀ g₀ hg₀
  have hx₁ : DifferentialIndependent (RatFunc ℂ) x₁ := hfree₁ g₁ hg₁
  let e := differentialIndependentAdjoinAlgEquiv x₀ x₁ hx₀ hx₁
  refine ⟨g₀, g₁, horder₀ g₀, horder₁ g₁, hx₀, hx₁, e, ?_, ?_⟩
  · intro h n
    exact differentialIndependentAdjoinAlgEquiv_jet x₀ x₁ hx₀ hx₁ h n
  · intro z
    exact differentialIndependentAdjoinAlgEquiv_deriv x₀ x₁ hx₀ hx₁ z

end
end GaloisForLFunctions.HTGeometry
