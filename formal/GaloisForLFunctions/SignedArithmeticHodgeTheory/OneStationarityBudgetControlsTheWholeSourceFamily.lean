import GaloisForLFunctions.SignedArithmeticHodgeTheory.TheArithmeticSchurComplementHasCertifiedErrorBounds

/-!
# A single operator budget for a whole source family

The trial Schur error is a positive form, bounded by the square of one
stationarity operator. The estimate applies to every signed coefficient vector
at once and incurs no separate charge for each matrix entry.
-/

noncomputable section

open scoped InnerProductSpace
open RHTower RHTower.CHMDDoobGraph RHTower.CHMDPolar

namespace GaloisForLFunctions.SignedArithmeticHodgeTheory

open ArithmeticIndexDescent

local instance : NormedSpace ℝ closedFixedLogCellGraph :=
  closedFixedLogCellGraph.normedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The actual stationarity defect of a whole family and its trial corrections. -/
def familyStationarity (F : E →L[ℝ] SourceGraph)
    (U : E →L[ℝ] closedFixedLogCellGraph) :
    E →L[ℝ] closedFixedLogCellGraph :=
  arithmeticStationarity.comp (F - closedFixedLogCellGraph.subtypeL.comp U)

theorem familyStationarity_apply (F : E →L[ℝ] SourceGraph)
    (U : E →L[ℝ] closedFixedLogCellGraph) (c : E) :
    familyStationarity F U c = arithmeticStationarity (F c - U c) := rfl

/-- The complete error is positive and controlled before any entrywise estimate. -/
theorem family_energy_error_bounds (F : E →L[ℝ] SourceGraph)
    (U : E →L[ℝ] closedFixedLogCellGraph) (c : E) :
    0 ≤ weilForm (F c - U c) - weilForm (arithmeticResidual (F c)) ∧
      weilForm (F c - U c) - weilForm (arithmeticResidual (F c)) ≤
        2 * ‖familyStationarity F U c‖ ^ 2 := by
  obtain ⟨hlo, hhi⟩ := arithmetic_trial_energy_bounds (F c) (U c)
  rw [familyStationarity_apply]
  constructor
  · nlinarith only [hhi, sq_nonneg ‖fixedLogCellWeilProjection (F c) - U c‖]
  · linarith only [hlo]

/-- One operator norm controls every signed vector, independently of its presentation. -/
theorem family_energy_error_le_opNorm (F : E →L[ℝ] SourceGraph)
    (U : E →L[ℝ] closedFixedLogCellGraph) (c : E) :
    weilForm (F c - U c) - weilForm (arithmeticResidual (F c)) ≤
      2 * ‖familyStationarity F U‖ ^ 2 * ‖c‖ ^ 2 := by
  have h := (familyStationarity F U).le_opNorm c
  have hs : ‖familyStationarity F U c‖ ^ 2 ≤
      (‖familyStationarity F U‖ * ‖c‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) h 2
  calc
    _ ≤ 2 * ‖familyStationarity F U c‖ ^ 2 := (family_energy_error_bounds F U c).2
    _ ≤ 2 * (‖familyStationarity F U‖ * ‖c‖) ^ 2 :=
      mul_le_mul_of_nonneg_left hs (by norm_num)
    _ = _ := by ring

/-- The same budget controls the source-graph error of every correction. -/
theorem family_graph_error_le_opNorm (F : E →L[ℝ] SourceGraph)
    (U : E →L[ℝ] closedFixedLogCellGraph) (c : E) :
    ‖fixedLogCellWeilProjection (F c) - U c‖ ≤
      2 * ‖familyStationarity F U‖ * ‖c‖ := by
  calc
    _ ≤ 2 * ‖familyStationarity F U c‖ := arithmetic_trial_graph_error (F c) (U c)
    _ ≤ 2 * (‖familyStationarity F U‖ * ‖c‖) :=
      mul_le_mul_of_nonneg_left ((familyStationarity F U).le_opNorm c) (by norm_num)
    _ = _ := by ring

/-- All mixed entries share one budget, including interactions of distant blocks. -/
theorem family_mixed_error_le_opNorm (F : E →L[ℝ] SourceGraph)
    (U : E →L[ℝ] closedFixedLogCellGraph) (c d : E) :
    |weilBilin (F c - U c) (F d - U d) -
        weilBilin (arithmeticResidual (F c)) (arithmeticResidual (F d))| ≤
      2 * ‖familyStationarity F U‖ ^ 2 * ‖c‖ * ‖d‖ := by
  have hc := (familyStationarity F U).le_opNorm c
  have hd := (familyStationarity F U).le_opNorm d
  calc
    _ ≤ 2 * ‖familyStationarity F U c‖ * ‖familyStationarity F U d‖ :=
      arithmetic_trial_mixed_error (F c) (F d) (U c) (U d)
    _ ≤ 2 * (‖familyStationarity F U‖ * ‖c‖) *
        (‖familyStationarity F U‖ * ‖d‖) := by
      have h := mul_le_mul hc hd (norm_nonneg _)
        (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left h (by norm_num : (0 : ℝ) ≤ 2)
    _ = _ := by ring

end GaloisForLFunctions.SignedArithmeticHodgeTheory

#print axioms GaloisForLFunctions.SignedArithmeticHodgeTheory.family_energy_error_le_opNorm
#print axioms GaloisForLFunctions.SignedArithmeticHodgeTheory.family_mixed_error_le_opNorm
