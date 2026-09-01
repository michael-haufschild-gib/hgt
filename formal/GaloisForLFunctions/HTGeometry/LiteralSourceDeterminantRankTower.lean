import GaloisForLFunctions.HTGeometry.SourceFormationHarmonicMechanics
import GaloisForLFunctions.HTGeometry.DiffIndepLinearIndependence
import GaloisForLFunctions.HTGeometry.RankJumpDeterminantCreation

/-!
# Literal-source determinant rank tower

The actual depth-12 normalized finite-abscissa source channels are differentially independent over
the full zeta differential field.  Consequently their finite complex spans form a strict tower of
every finite rank.  Each successor quotient is a canonically pointed line, while moving top
exterior degree cannot be transported from the preceding stage.
-/

open scoped Differential UpperEndDifferentialInstances UpperEndComplexTowerInstances

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open _root_.RHTower
open Module Set

local instance complexZetaUpperEndMeroScalarTower :
    IsScalarTower ℂ zetaUpperEndDifferentialField upperEndMeroField :=
  .of_algebraMap_eq fun _ => rfl

/-- Analytic realization of the `j`th literal normalized depth-12 source channel. -/
abbrev rankTwelveLiteralSourceChannel (j : ℕ) : upperEndMeroField :=
  finiteAbscissaLSeriesToUpperEndMero
    (completeResolutionNormalizedFiniteAbscissaSource 12 j)

/-- Actual source channels are linearly independent even over the full zeta differential field. -/
theorem rankTwelveLiteralSourceChannel_linearIndependent :
    LinearIndependent zetaUpperEndDifferentialField rankTwelveLiteralSourceChannel := by
  exact linearIndependent_of_differentialIndependent
    rankTwelveFiniteAbscissaSource_relativeDifferentialIndependent

/-- In particular the literal source channels are complex-linearly independent. -/
theorem rankTwelveLiteralSourceChannel_complexLinearIndependent :
    LinearIndependent ℂ rankTwelveLiteralSourceChannel := by
  apply rankTwelveLiteralSourceChannel_linearIndependent.restrict_scalars
  simpa only [Algebra.smul_def, mul_one] using
    (FaithfulSMul.algebraMap_injective ℂ zetaUpperEndDifferentialField)

/-- Complex span of the first `n` literal source channels. -/
def rankTwelveLiteralSourcePrefix (n : ℕ) :
    Submodule ℂ upperEndMeroField :=
  Submodule.span ℂ
    (Set.range (fun j : Fin n => rankTwelveLiteralSourceChannel j))

noncomputable instance rankTwelveLiteralSourcePrefix_finiteDimensional (n : ℕ) :
    FiniteDimensional ℂ (rankTwelveLiteralSourcePrefix n) :=
  Module.Finite.span_of_finite ℂ (Set.finite_range _)

/-- Every finite literal source prefix remains linearly independent. -/
theorem rankTwelveLiteralSourcePrefix_linearIndependent (n : ℕ) :
    LinearIndependent ℂ
      (fun j : Fin n => rankTwelveLiteralSourceChannel j) := by
  exact rankTwelveLiteralSourceChannel_complexLinearIndependent.comp
    (fun j : Fin n => j.1) Fin.val_injective

/-- The `n`th literal source prefix has exact rank `n`. -/
theorem rankTwelveLiteralSourcePrefix_finrank (n : ℕ) :
    finrank ℂ (rankTwelveLiteralSourcePrefix n) = n := by
  unfold rankTwelveLiteralSourcePrefix
  rw [finrank_span_eq_card (rankTwelveLiteralSourcePrefix_linearIndependent n)]
  simp

/-- Prefix formation is monotone. -/
theorem rankTwelveLiteralSourcePrefix_mono (n : ℕ) :
    rankTwelveLiteralSourcePrefix n ≤ rankTwelveLiteralSourcePrefix (n + 1) := by
  apply Submodule.span_mono
  rintro y ⟨j, rfl⟩
  exact ⟨Fin.castSucc j, rfl⟩

/-- The next literal source channel never belongs to its predecessor prefix. -/
theorem rankTwelveLiteralSourceChannel_not_mem_prefix (n : ℕ) :
    rankTwelveLiteralSourceChannel n ∉ rankTwelveLiteralSourcePrefix n := by
  intro hmem
  have hnot := (linearIndependent_iff_notMem_span.mp
    rankTwelveLiteralSourceChannel_complexLinearIndependent) n
  apply hnot
  apply Submodule.span_mono _ hmem
  rintro y ⟨j, rfl⟩
  refine ⟨j.1, ?_, rfl⟩
  exact ⟨Set.mem_univ _, by simpa using (Nat.ne_of_lt j.isLt)⟩

/-- The new literal source channel, as an element of the successor prefix. -/
def rankTwelveLiteralSourceNewChannel (n : ℕ) :
    rankTwelveLiteralSourcePrefix (n + 1) :=
  ⟨rankTwelveLiteralSourceChannel n, by
    apply Submodule.subset_span
    exact ⟨Fin.last n, by simp [rankTwelveLiteralSourceChannel]⟩⟩

/-- Every source tick is a strict rank jump. -/
theorem rankTwelveLiteralSourcePrefix_strict (n : ℕ) :
    rankTwelveLiteralSourcePrefix n < rankTwelveLiteralSourcePrefix (n + 1) := by
  refine lt_of_le_of_ne (rankTwelveLiteralSourcePrefix_mono n) ?_
  intro heq
  apply rankTwelveLiteralSourceChannel_not_mem_prefix n
  rw [heq]
  exact (rankTwelveLiteralSourceNewChannel n).2

/-- Old prefix viewed inside its successor prefix. -/
def rankTwelveLiteralSourceOldInsideNext (n : ℕ) :
    Submodule ℂ (rankTwelveLiteralSourcePrefix (n + 1)) :=
  (rankTwelveLiteralSourcePrefix n).comap
    (rankTwelveLiteralSourcePrefix (n + 1)).subtype

/-- Relative determinant increment created by one literal source tick. -/
abbrev RankTwelveLiteralSourceDeterminantIncrement (n : ℕ) :=
  (rankTwelveLiteralSourcePrefix (n + 1)) ⧸
    rankTwelveLiteralSourceOldInsideNext n

theorem rankTwelveLiteralSourceOldInsideNext_finrank (n : ℕ) :
    finrank ℂ (rankTwelveLiteralSourceOldInsideNext n) = n := by
  calc
    finrank ℂ (rankTwelveLiteralSourceOldInsideNext n) =
      finrank ℂ (rankTwelveLiteralSourcePrefix n) :=
      LinearEquiv.finrank_eq
        (Submodule.comapSubtypeEquivOfLe
          (rankTwelveLiteralSourcePrefix_mono n))
    _ = n := rankTwelveLiteralSourcePrefix_finrank n

/-- Every literal source tick creates exactly one new relative determinant direction. -/
theorem rankTwelveLiteralSourceDeterminantIncrement_finrank (n : ℕ) :
    finrank ℂ (RankTwelveLiteralSourceDeterminantIncrement n) = 1 := by
  have h := (rankTwelveLiteralSourceOldInsideNext n).finrank_quotient_add_finrank
  rw [rankTwelveLiteralSourceOldInsideNext_finrank,
    rankTwelveLiteralSourcePrefix_finrank] at h
  have hh : finrank ℂ (RankTwelveLiteralSourceDeterminantIncrement n) + n =
      1 + n := by
    simpa [Nat.add_comm] using h
  exact Nat.add_right_cancel hh

/-- Canonical quotient class of the newly created literal source channel. -/
def rankTwelveLiteralSourceIncrementGenerator (n : ℕ) :
    RankTwelveLiteralSourceDeterminantIncrement n :=
  Submodule.Quotient.mk (rankTwelveLiteralSourceNewChannel n)

/-- The canonical new-channel quotient class is nonzero. -/
theorem rankTwelveLiteralSourceIncrementGenerator_ne_zero (n : ℕ) :
    rankTwelveLiteralSourceIncrementGenerator n ≠ 0 := by
  intro hzero
  have hmem := (Submodule.Quotient.mk_eq_zero
    (rankTwelveLiteralSourceOldInsideNext n)).mp hzero
  exact rankTwelveLiteralSourceChannel_not_mem_prefix n hmem

/-- The canonical new-channel quotient class spans the complete successor increment. -/
theorem rankTwelveLiteralSourceIncrementGenerator_span_eq_top (n : ℕ) :
    ℂ ∙ rankTwelveLiteralSourceIncrementGenerator n = ⊤ := by
  exact (finrank_eq_one_iff_of_nonzero
    (rankTwelveLiteralSourceIncrementGenerator n)
    (rankTwelveLiteralSourceIncrementGenerator_ne_zero n)).mp
      (rankTwelveLiteralSourceDeterminantIncrement_finrank n)

/-- Determinant of every relative source increment is a line. -/
theorem rankTwelveLiteralSourceIncrementDeterminant_finrank (n : ℕ) :
    finrank ℂ
      (⋀[ℂ]^1 (RankTwelveLiteralSourceDeterminantIncrement n)) = 1 := by
  rw [exteriorPower.finrank_eq,
    rankTwelveLiteralSourceDeterminantIncrement_finrank]
  simp

/-- Top exterior carrier of every finite literal source stage is a line. -/
theorem rankTwelveLiteralSourceStageDeterminant_finrank (n : ℕ) :
    finrank ℂ (⋀[ℂ]^n (rankTwelveLiteralSourcePrefix n)) = 1 := by
  rw [exteriorPower.finrank_eq, rankTwelveLiteralSourcePrefix_finrank,
    Nat.choose_self]

/-- Canonical inclusion of consecutive literal source prefixes. -/
def rankTwelveLiteralSourcePrefixInclusion (n : ℕ) :
    rankTwelveLiteralSourcePrefix n →ₗ[ℂ]
      rankTwelveLiteralSourcePrefix (n + 1) :=
  Submodule.inclusion (rankTwelveLiteralSourcePrefix_mono n)

theorem rankTwelveLiteralSourcePrefixInclusion_injective (n : ℕ) :
    Function.Injective (rankTwelveLiteralSourcePrefixInclusion n) := by
  exact (rankTwelveLiteralSourcePrefix n).inclusion_injective
    (rankTwelveLiteralSourcePrefix_mono n)

/-- Moving top exterior volume cannot be inherited from the preceding literal source stage. -/
theorem rankTwelveLiteralSourceMovingTop_not_surjective (n : ℕ) :
    ¬ Function.Surjective
      (exteriorPower.map (n + 1) (rankTwelveLiteralSourcePrefixInclusion n)) := by
  exact not_surjective_exteriorPower_newDegree_of_rankJump n
    (rankTwelveLiteralSourcePrefixInclusion n)
    (rankTwelveLiteralSourcePrefix_finrank n)
    (rankTwelveLiteralSourcePrefix_finrank (n + 1))

end

end GaloisForLFunctions.HTGeometry
