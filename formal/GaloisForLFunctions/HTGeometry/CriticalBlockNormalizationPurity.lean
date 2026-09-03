import GaloisForLFunctions.HTGeometry.FiniteFlatUfdPurity
import GaloisForLFunctions.HTGeometry.CriticalBlockAwaySchurUnramified
import GaloisForLFunctions.HTGeometry.CriticalBlockSchurAtPrimeUnramified
import GaloisForLFunctions.HTGeometry.CriticalBlockNormalizationTraceRetract
import GaloisForLFunctions.HTGeometry.CriticalBlockNormalizationFinitePresentation
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Smooth.Fiber

namespace GaloisForLFunctions.HTGeometry

noncomputable section

set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 3000000

variable (K : Type*) [Field K] [CharZero K] [IsAlgClosed K] {m n : ℕ}
variable [Fact (0 < m)] [Fact (0 < n)] [Fact (1 < m)] [Fact (1 < n)]

/-- The generic fibre of a critical block normalization is formally unramified. -/
theorem criticalBlockNormalization_genericLocalization_formallyUnramified
    (B : Set (criticalGeometricSheet K m n)) :
    Algebra.FormallyUnramified
      (FractionRing (criticalObservationChartRing K m n))
      (Localization (Algebra.algebraMapSubmonoid (CriticalBlockNormalization K B)
        (nonZeroDivisors (criticalObservationChartRing K m n)))) := by
  let A := criticalObservationChartRing K m n
  let F := criticalObservationField K m n
  let M := CriticalBlockFixedField K B
  let C := CriticalBlockNormalization K B
  let BF := Localization (Algebra.algebraMapSubmonoid C (nonZeroDivisors A))
  letI : CharZero A := Algebra.charZero_of_charZero K A
  letI : CharZero (FractionRing A) := Algebra.charZero_of_charZero A (FractionRing A)
  letI : PerfectField (FractionRing A) := PerfectField.ofCharZero
  letI : IsLocalization (Algebra.algebraMapSubmonoid C (nonZeroDivisors A)) M :=
    IsIntegralClosure.isLocalization A F M C
  let e : BF ≃ₐ[C] M :=
    IsLocalization.algEquiv (Algebra.algebraMapSubmonoid C (nonZeroDivisors A)) BF M
  letI : Field BF :=
    (e.toRingEquiv.toMulEquiv.isField (Field.toIsField M)).toField
  letI : Module.Finite (FractionRing A) BF := inferInstance
  letI : Algebra.IsAlgebraic (FractionRing A) BF := inferInstance
  letI : Algebra.IsSeparable (FractionRing A) BF := inferInstance
  exact Algebra.FormallyUnramified.of_isSeparable _ _

/-- Purity: every nontrivial canonical-sheet block normalization is formally unramified over the
whole observation chart. -/
theorem criticalBlockNormalization_formallyUnramified
    {B : Set (criticalGeometricSheet K m n)}
    (hB : MulAction.IsBlock (criticalGeometricMonodromy K m n) B)
    (hmem : criticalSourceNormalClosureEmbedding K m n ∈ B)
    (hB2 : ∃ x ∈ B, ∃ y ∈ B, x ≠ y) :
    Algebra.FormallyUnramified (criticalObservationChartRing K m n)
      (CriticalBlockNormalization K B) := by
  classical
  letI : Module.Flat (criticalObservationChartRing K m n)
      (CriticalBlockNormalization K B) :=
    criticalBlockNormalization_flat_of_sourceChart_flat K hB hmem
  letI : Algebra.FormallyUnramified
      (FractionRing (criticalObservationChartRing K m n))
      (Localization (Algebra.algebraMapSubmonoid (CriticalBlockNormalization K B)
        (nonZeroDivisors (criticalObservationChartRing K m n)))) :=
    criticalBlockNormalization_genericLocalization_formallyUnramified K B
  apply Algebra.formallyUnramified_of_flat_fraction_formallyUnramified_of_height_one_localizations
  intro P hP hheight
  by_cases h : P = criticalSchurChartUnder K (m := m) (n := n)
  · subst P
    exact criticalBlockSchurAtPrime_formallyUnramified K Fact.out Fact.out hB hB2
  · exact criticalBlockNormalization_baseLocalization_formallyUnramified_of_ne_schur
      K P hheight hB hmem h

/-- Finite flat purity upgrades a nontrivial canonical-sheet block normalization to a formally
étale algebra. -/
theorem criticalBlockNormalization_formallyEtale
    {B : Set (criticalGeometricSheet K m n)}
    (hB : MulAction.IsBlock (criticalGeometricMonodromy K m n) B)
    (hmem : criticalSourceNormalClosureEmbedding K m n ∈ B)
    (hB2 : ∃ x ∈ B, ∃ y ∈ B, x ≠ y) :
    Algebra.FormallyEtale (criticalObservationChartRing K m n)
      (CriticalBlockNormalization K B) := by
  letI : Module.Flat (criticalObservationChartRing K m n)
      (CriticalBlockNormalization K B) :=
    criticalBlockNormalization_flat_of_sourceChart_flat K hB hmem
  letI : Algebra.FormallyUnramified (criticalObservationChartRing K m n)
      (CriticalBlockNormalization K B) :=
    criticalBlockNormalization_formallyUnramified K hB hmem hB2
  letI : Algebra.Etale (criticalObservationChartRing K m n)
      (CriticalBlockNormalization K B) :=
    Algebra.Etale.of_formallyUnramified_of_flat
  exact inferInstance

end

end GaloisForLFunctions.HTGeometry
