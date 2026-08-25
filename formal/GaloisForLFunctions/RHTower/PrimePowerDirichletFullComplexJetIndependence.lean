import GaloisForLFunctions.RHTower.PrimePowerDirichletComplexJetIndependence
import GaloisForLFunctions.HTGeometry.DifferentialPointedCollisionMatroid

/-!
# Full complex-shift jet independence over the small-growth field

The finite heterogeneous packet theorem has finite character.  This leaf upgrades it to the
literal full family indexed by every complex shift and every derivative order, first on the
arithmetic fraction field and then on the analytic upper-end carrier over Nagoshi's exact
small-growth meromorphic field.
-/

namespace RHTower

open scoped Differential

noncomputable section

open GaloisForLFunctions
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.RHTower.PrimeShiftJet

local instance fullComplexJetArithmeticFractionCharZero :
    CharZero arithmeticFunctionFractionField :=
  charZero_of_injective_ringHom
    (algebraMap ℂ arithmeticFunctionFractionField).injective

local instance fullComplexJetComplexDifferential : Differential ℂ where
  deriv := 0

local instance fullComplexJetArithmeticFractionDifferentialAlgebra :
    DifferentialAlgebra ℂ arithmeticFunctionFractionField :=
  ⟨fun z => by
    rw [arithmeticFunctionFractionField_deriv_algebraMap_complex]
    change 0 = algebraMap ℂ arithmeticFunctionFractionField 0
    rw [map_zero]⟩

/-- The complete complex translation orbit of a prime-power source is differentially independent
over the constants.  This is the arbitrary-family form of the finite prime-feature theorem. -/
theorem primePowerDirichlet_fullComplexShiftOrbit_differentialIndependent
    (F : ArithmeticFunction ℂ)
    (hsupport : SupportedOnPositivePrimePowers F)
    (hzeros : {p : Nat.Primes | F ((p : ℕ)) = 0}.Finite) :
    DifferentialIndependent ℂ
      (fun h : ℂ => algebraMap (ArithmeticFunction ℂ)
        arithmeticFunctionFractionField (dirichletShift h F)) := by
  classical
  apply differentialIndependent_of_forall_finite_subfamily
  intro I hI
  letI : Fintype I := hI.fintype
  by_cases hIempty : IsEmpty I
  · letI : IsEmpty I := hIempty
    have hsingleton := dirichletShiftFamily_differentialIndependent
      F hsupport hzeros (fun _ : Fin 1 => 0) (fun i j _ => Subsingleton.elim i j)
    have hcomp := hsingleton.comp (fun i : I => isEmptyElim i)
      (fun i => isEmptyElim i)
    have heq :
        ((fun _ : Fin 1 => algebraMap (ArithmeticFunction ℂ)
            arithmeticFunctionFractionField (dirichletShift 0 F)) ∘
          fun i : I => isEmptyElim i) =
        (fun i : I => algebraMap (ArithmeticFunction ℂ)
          arithmeticFunctionFractionField (dirichletShift (i : ℂ) F)) := by
      funext i
      exact isEmptyElim i
    rw [heq] at hcomp
    exact hcomp
  · letI : Nonempty I := not_isEmpty_iff.mp hIempty
    let e : I ≃ Fin (Fintype.card I) := Fintype.equivFin I
    have hfinite := dirichletShiftFamily_differentialIndependent
      F hsupport hzeros (fun j => ((e.symm j : I) : ℂ))
        (fun i j hij => e.symm.injective (Subtype.ext hij))
    have hcomp := hfinite.comp e e.injective
    simpa [e, Function.comp_def] using hcomp

local instance fullComplexJetUpperEndDomain : IsDomain upperEndAnalyticSubring :=
  isDomain_upperEndAnalyticSubring

local instance fullComplexJetUpperEndDifferential : Differential upperEndMeroField :=
  upperEndMeroFieldDifferential

/-- Every complex translate and derivative order of a finite-abscissa prime-power source form one
algebraically independent family over the genuine rational-coordinate field. -/
theorem primePowerDirichlet_upperEnd_fullComplexShiftJets_algebraicIndependent
    (S : finiteAbscissaArithmeticSubalgebra)
    (hsupport : SupportedOnPositivePrimePowers S.1)
    (hzeros : {p : Nat.Primes | S.1 ((p : ℕ)) = 0}.Finite) :
    AlgebraicIndependent upperEndRationalCoordinateField
      (fun hk : ℂ × ℕ => differentialJet hk.2
        (upperEndTranslationMeroEquiv (Complex.I * hk.1)
          (finiteAbscissaLSeriesToUpperEndMero S))) := by
  classical
  let sourceJets : ℂ × ℕ → finiteAbscissaArithmeticSubalgebra := fun hk =>
    (finiteAbscissaRotatedDeriv^[hk.2])
      (finiteAbscissaDirichletShift hk.1 S)
  have hfrac := primePowerDirichlet_fullComplexShiftOrbit_differentialIndependent
    S.1 hsupport hzeros
  unfold DifferentialIndependent at hfrac
  let arithmeticIncl : ArithmeticFunction ℂ →ₐ[ℂ]
      arithmeticFunctionFractionField :=
    IsScalarTower.toAlgHom ℂ (ArithmeticFunction ℂ)
      arithmeticFunctionFractionField
  have harithmetic : AlgebraicIndependent ℂ
      (fun hk => (sourceJets hk).1) := by
    apply (AlgHom.algebraicIndependent_iff arithmeticIncl
      (IsFractionRing.injective (ArithmeticFunction ℂ)
        arithmeticFunctionFractionField)).mp
    convert hfrac using 1
    funext hk
    rw [differentialJet_algebraMap_rotatedLogArithmeticJet]
    change algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
        (sourceJets hk).1 =
      algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
        (rotatedLogArithmeticJet hk.2 (dirichletShift hk.1 S.1))
    apply congrArg (algebraMap (ArithmeticFunction ℂ)
      arithmeticFunctionFractionField)
    apply ArithmeticFunction.ext
    intro n
    rw [finiteAbscissaRotatedDeriv_iterate_apply]
    rfl
  let finiteIncl : finiteAbscissaArithmeticSubalgebra →ₐ[ℂ]
      ArithmeticFunction ℂ := finiteAbscissaArithmeticSubalgebra.val
  have hfiniteIncl : Function.Injective finiteIncl := by
    intro x y hxy
    exact Subtype.ext hxy
  have hsourceJets : AlgebraicIndependent ℂ sourceJets := by
    apply (AlgHom.algebraicIndependent_iff finiteIncl hfiniteIncl).mp
    convert harithmetic using 1
    rfl
  have hanalytic :=
    algebraicIndependent_finiteAbscissaLSeries_over_upperEndRationalCoordinate
      sourceJets hsourceJets
  convert hanalytic using 1
  funext hk
  rw [show upperEndTranslationMeroEquiv (Complex.I * hk.1)
      (finiteAbscissaLSeriesToUpperEndMero S) =
        finiteAbscissaLSeriesToUpperEndMero
          (finiteAbscissaDirichletShift hk.1 S) by
    exact (finiteAbscissaLSeriesToUpperEndMero_dirichletShift hk.1 S).symm]
  exact differentialJet_finiteAbscissaLSeriesToUpperEndMero
    (finiteAbscissaDirichletShift hk.1 S) hk.2

/-- **Full Nagoshi-field form of the prime-power theorem.**  Every complex translate and every
derivative order of a finite-abscissa prime-power source form one algebraically independent family
over the genuine small-growth meromorphic field `F_s`. -/
theorem primePowerDirichlet_upperEnd_fullComplexShiftJets_algebraicIndependent_over_smallGrowth
    (S : finiteAbscissaArithmeticSubalgebra)
    (hsupport : SupportedOnPositivePrimePowers S.1)
    (hzeros : {p : Nat.Primes | S.1 ((p : ℕ)) = 0}.Finite) :
    AlgebraicIndependent SmallGrowthMeromorphicField
      (fun hk : ℂ × ℕ => differentialJet hk.2
        (upperEndTranslationMeroEquiv (Complex.I * hk.1)
          (finiteAbscissaLSeriesToUpperEndMero S))) := by
  classical
  let sourceJets : ℂ × ℕ → finiteAbscissaArithmeticSubalgebra := fun hk =>
    (finiteAbscissaRotatedDeriv^[hk.2])
      (finiteAbscissaDirichletShift hk.1 S)
  have hfrac := primePowerDirichlet_fullComplexShiftOrbit_differentialIndependent
    S.1 hsupport hzeros
  unfold DifferentialIndependent at hfrac
  let arithmeticIncl : ArithmeticFunction ℂ →ₐ[ℂ]
      arithmeticFunctionFractionField :=
    IsScalarTower.toAlgHom ℂ (ArithmeticFunction ℂ)
      arithmeticFunctionFractionField
  have harithmetic : AlgebraicIndependent ℂ
      (fun hk => (sourceJets hk).1) := by
    apply (AlgHom.algebraicIndependent_iff arithmeticIncl
      (IsFractionRing.injective (ArithmeticFunction ℂ)
        arithmeticFunctionFractionField)).mp
    convert hfrac using 1
    funext hk
    rw [differentialJet_algebraMap_rotatedLogArithmeticJet]
    change algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
        (sourceJets hk).1 =
      algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
        (rotatedLogArithmeticJet hk.2 (dirichletShift hk.1 S.1))
    apply congrArg (algebraMap (ArithmeticFunction ℂ)
      arithmeticFunctionFractionField)
    apply ArithmeticFunction.ext
    intro n
    rw [finiteAbscissaRotatedDeriv_iterate_apply]
    rfl
  let finiteIncl : finiteAbscissaArithmeticSubalgebra →ₐ[ℂ]
      ArithmeticFunction ℂ := finiteAbscissaArithmeticSubalgebra.val
  have hfiniteIncl : Function.Injective finiteIncl := by
    intro x y hxy
    exact Subtype.ext hxy
  have hsourceJets : AlgebraicIndependent ℂ sourceJets := by
    apply (AlgHom.algebraicIndependent_iff finiteIncl hfiniteIncl).mp
    convert harithmetic using 1
    rfl
  have hanalytic :=
    algebraicIndependent_finiteAbscissaLSeries_over_smallGrowth
      sourceJets hsourceJets
  convert hanalytic using 1
  funext hk
  rw [show upperEndTranslationMeroEquiv (Complex.I * hk.1)
      (finiteAbscissaLSeriesToUpperEndMero S) =
        finiteAbscissaLSeriesToUpperEndMero
          (finiteAbscissaDirichletShift hk.1 S) by
    exact (finiteAbscissaLSeriesToUpperEndMero_dirichletShift hk.1 S).symm]
  exact differentialJet_finiteAbscissaLSeriesToUpperEndMero
    (finiteAbscissaDirichletShift hk.1 S) hk.2

/-- Differential-independence form of the complete Nagoshi-field theorem. -/
theorem primePowerDirichlet_upperEnd_fullComplexShiftOrbit_differentialIndependent_over_smallGrowth
    (S : finiteAbscissaArithmeticSubalgebra)
    (hsupport : SupportedOnPositivePrimePowers S.1)
    (hzeros : {p : Nat.Primes | S.1 ((p : ℕ)) = 0}.Finite) :
    DifferentialIndependent SmallGrowthMeromorphicField
      (fun h : ℂ => upperEndTranslationMeroEquiv (Complex.I * h)
        (finiteAbscissaLSeriesToUpperEndMero S)) := by
  unfold DifferentialIndependent
  exact primePowerDirichlet_upperEnd_fullComplexShiftJets_algebraicIndependent_over_smallGrowth
    S hsupport hzeros

/-- The exposed completed-Xi increment has a single algebraically independent family containing
all complex translates and all derivative orders over `F_s`. -/
theorem filteredVonMangoldt_fullComplexShiftJets_algebraicIndependent_over_smallGrowth :
    AlgebraicIndependent SmallGrowthMeromorphicField
      (fun hk : ℂ × ℕ => differentialJet hk.2
        (upperEndTranslationMeroEquiv (Complex.I * hk.1)
          filteredVonMangoldtUpperEndCarrier)) := by
  refine primePowerDirichlet_upperEnd_fullComplexShiftJets_algebraicIndependent_over_smallGrowth
    filteredVonMangoldtFiniteAbscissaSource ?_ ?_
  · exact filteredVonMangoldtArithmetic_supportedOnPositivePrimePowers
  · have hempty :
        {p : Nat.Primes |
          filteredVonMangoldtFiniteAbscissaSource.1 ((p : ℕ)) = 0} = ∅ := by
      ext p
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      simpa [filteredVonMangoldtFiniteAbscissaSource,
        filteredVonMangoldtArithmetic] using filteredVonMangoldtCoeff_prime_ne_zero p
    rw [hempty]
    exact Set.finite_empty

/-- The exposed completed-Xi increment has a single algebraically independent family containing
all complex translates and derivative orders over the genuine rational-coordinate field. -/
theorem filteredVonMangoldt_fullComplexShiftJets_algebraicIndependent :
    AlgebraicIndependent upperEndRationalCoordinateField
      (fun hk : ℂ × ℕ => differentialJet hk.2
        (upperEndTranslationMeroEquiv (Complex.I * hk.1)
          filteredVonMangoldtUpperEndCarrier)) := by
  refine primePowerDirichlet_upperEnd_fullComplexShiftJets_algebraicIndependent
    filteredVonMangoldtFiniteAbscissaSource ?_ ?_
  · exact filteredVonMangoldtArithmetic_supportedOnPositivePrimePowers
  · have hempty :
        {p : Nat.Primes |
          filteredVonMangoldtFiniteAbscissaSource.1 ((p : ℕ)) = 0} = ∅ := by
      ext p
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      simpa [filteredVonMangoldtFiniteAbscissaSource,
        filteredVonMangoldtArithmetic] using filteredVonMangoldtCoeff_prime_ne_zero p
    rw [hempty]
    exact Set.finite_empty

/-- The exposed completed-Xi increment has a differentially independent full complex translation
orbit over `F_s`. -/
theorem filteredVonMangoldt_fullComplexShiftOrbit_differentialIndependent_over_smallGrowth :
    DifferentialIndependent SmallGrowthMeromorphicField
      (fun h : ℂ => upperEndTranslationMeroEquiv (Complex.I * h)
        filteredVonMangoldtUpperEndCarrier) := by
  unfold DifferentialIndependent
  exact filteredVonMangoldt_fullComplexShiftJets_algebraicIndependent_over_smallGrowth

end

end RHTower
