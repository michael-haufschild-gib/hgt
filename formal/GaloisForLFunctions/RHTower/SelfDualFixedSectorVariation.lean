import GaloisForLFunctions.RHTower.RealCoronaKZeroMultiplicityFracture

/-!
# Variation of fixed-sector defect in self-dual analytic families

This file computes P4 as a genuine two-parameter variation law.  Cyclic fixed-sector defect
varies by central analytic-rank change plus twice the upper off-central multiplicity change.
Ordinary coordinate `K₀`, by contrast, records only whether central multiplicity is zero or
positive.  The discrepancy is exactly variation of central multiplicity excess.
-/

noncomputable section

namespace GaloisForLFunctions.RHTower

variable {T : Type*}

/-- Signed change of cyclic fixed-sector defect between two family parameters. -/
def CompletedSelfDualAnalyticFamily.fixedSectorDefectVariation
    (F : CompletedSelfDualAnalyticFamily T) (t₀ t₁ : T) : ℤ :=
  F.toSelfDualRealZeroFamily.defectRank t₁ -
    F.toSelfDualRealZeroFamily.defectRank t₀

/-- Signed change of central analytic rank. -/
def CompletedSelfDualAnalyticFamily.analyticRankVariation
    (F : CompletedSelfDualAnalyticFamily T) (t₀ t₁ : T) : ℤ :=
  F.toSelfDualRealZeroFamily.analyticRank t₁ -
    F.toSelfDualRealZeroFamily.analyticRank t₀

/-- Signed change of upper off-central real-zero multiplicity. -/
def CompletedSelfDualAnalyticFamily.upperOffCentralMultiplicityVariation
    (F : CompletedSelfDualAnalyticFamily T) (t₀ t₁ : T) : ℤ :=
  F.toSelfDualRealZeroFamily.upperOffCentralMultiplicity t₁ -
    F.toSelfDualRealZeroFamily.upperOffCentralMultiplicity t₀

/-- Exact P4 fixed-sector variation formula. -/
theorem CompletedSelfDualAnalyticFamily.fixedSectorDefectVariation_eq
    (F : CompletedSelfDualAnalyticFamily T) (t₀ t₁ : T) :
    F.fixedSectorDefectVariation t₀ t₁ =
      F.analyticRankVariation t₀ t₁ +
        2 * F.upperOffCentralMultiplicityVariation t₀ t₁ := by
  rw [CompletedSelfDualAnalyticFamily.fixedSectorDefectVariation,
    CompletedSelfDualAnalyticFamily.analyticRankVariation,
    CompletedSelfDualAnalyticFamily.upperOffCentralMultiplicityVariation,
    F.toSelfDualRealZeroFamily.defectRank_eq_analyticRank_add_twice_upper t₁,
    F.toSelfDualRealZeroFamily.defectRank_eq_analyticRank_add_twice_upper t₀]
  push_cast
  ring

/-- Central `K₀` support rank, expressed as an integer for variation formulas. -/
def CompletedSelfDualAnalyticFamily.centralKZeroRankInt
    (F : CompletedSelfDualAnalyticFamily T) (t : T) : ℤ :=
  finiteCoordinateKZeroEvaluationRank F.center (F.fixedKZeroClass t)

/-- Signed change of the central evaluation of the fixed Real-corona `K₀` class. -/
def CompletedSelfDualAnalyticFamily.centralKZeroVariation
    (F : CompletedSelfDualAnalyticFamily T) (t₀ t₁ : T) : ℤ :=
  F.centralKZeroRankInt t₁ - F.centralKZeroRankInt t₀

/-- `K₀` sees the support indicator of central analytic rank and no multiplicity beyond one. -/
theorem CompletedSelfDualAnalyticFamily.centralKZeroRankInt_eq_supportIndicator
    (F : CompletedSelfDualAnalyticFamily T) (t : T) :
    F.centralKZeroRankInt t =
      if F.toSelfDualRealZeroFamily.analyticRank t = 0 then 0 else 1 := by
  rw [CompletedSelfDualAnalyticFamily.centralKZeroRankInt,
    CompletedSelfDualAnalyticFamily.fixedKZeroClass,
    finiteCoordinateKZeroEvaluationRank_realCoronaFixedKZeroClass,
    realCoronaKZeroSupportVector_apply]
  have hRank : F.toSelfDualRealZeroFamily.analyticRank t =
      F.realWindowMultiplicity t F.center := rfl
  rw [hRank]
  split_ifs <;> norm_num

/-- Exact central `K₀` variation: only creation or annihilation of central support changes the
class evaluation. -/
theorem CompletedSelfDualAnalyticFamily.centralKZeroVariation_eq
    (F : CompletedSelfDualAnalyticFamily T) (t₀ t₁ : T) :
    F.centralKZeroVariation t₀ t₁ =
      (if F.toSelfDualRealZeroFamily.analyticRank t₁ = 0 then 0 else 1) -
        (if F.toSelfDualRealZeroFamily.analyticRank t₀ = 0 then 0 else 1) := by
  rw [CompletedSelfDualAnalyticFamily.centralKZeroVariation,
    F.centralKZeroRankInt_eq_supportIndicator,
    F.centralKZeroRankInt_eq_supportIndicator]

/-- Central multiplicity invisible to ordinary coordinate `K₀`. -/
def centralKZeroMultiplicityExcess (n : ℕ) : ℤ :=
  (n : ℤ) - if n = 0 then 0 else 1

/-- Pointwise analytic rank is support rank plus its exact multiplicity excess. -/
theorem analyticRank_eq_supportIndicator_add_excess (n : ℕ) :
    (n : ℤ) = (if n = 0 then 0 else 1) + centralKZeroMultiplicityExcess n := by
  simp [centralKZeroMultiplicityExcess]

/-- Family variation form of the support--multiplicity fracture: analytic-rank variation equals
central `K₀` variation plus variation of the missing multiplicity excess. -/
theorem CompletedSelfDualAnalyticFamily.analyticRankVariation_eq_kZero_add_excess
    (F : CompletedSelfDualAnalyticFamily T) (t₀ t₁ : T) :
    F.analyticRankVariation t₀ t₁ =
      F.centralKZeroVariation t₀ t₁ +
        (centralKZeroMultiplicityExcess
            (F.toSelfDualRealZeroFamily.analyticRank t₁) -
          centralKZeroMultiplicityExcess
            (F.toSelfDualRealZeroFamily.analyticRank t₀)) := by
  rw [CompletedSelfDualAnalyticFamily.analyticRankVariation,
    F.centralKZeroVariation_eq]
  rw [analyticRank_eq_supportIndicator_add_excess
      (F.toSelfDualRealZeroFamily.analyticRank t₁),
    analyticRank_eq_supportIndicator_add_excess
      (F.toSelfDualRealZeroFamily.analyticRank t₀)]
  ring

end GaloisForLFunctions.RHTower
