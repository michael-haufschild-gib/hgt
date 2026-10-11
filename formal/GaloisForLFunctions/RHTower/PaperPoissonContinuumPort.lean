import GaloisForLFunctions.RHTower.PaperPoissonPortSymbol
import GaloisForLFunctions.HTGeometry.PaperModulationCalkin
import GaloisForLFunctions.HTGeometry.LpContinuousMultiplierNorm
import GaloisForLFunctions.HTGeometry.BoundedMultiplierHilbert

/-!
# The full native Poisson continuum port retains its compact-quotient norm

Positive frequency decay does not make multiplication compact on Lebesgue `L²(ℝ)`.
The proven paper ideal trace therefore detects every native Poisson port, including all
positive gaps. The exact source symbol and its intermediate-depth composition are retained.
-/

namespace RHTower
noncomputable section
open MeasureTheory GaloisForLFunctions.HTGeometry Filter
open scoped Topology ENNReal NNReal

abbrev PaperPoissonSpace := Lp ℂ 2 (volume : Measure ℝ)

/-- The literal native transfer on the full real-frequency Hilbert space. -/
def paperPoissonPort (h d : ℝ≥0) : PaperPoissonSpace →L[ℂ] PaperPoissonSpace :=
  lpBoundedMulCLM
    (Complex.continuous_ofReal.comp (continuous_paperPoissonSymbol h d)).measurable
    zero_le_one (norm_paperPoissonSymbol_complex_le h d)

theorem paperPoissonPort_apply_ae (h d : ℝ≥0) (f : PaperPoissonSpace) :
    (paperPoissonPort h d f : ℝ → ℂ) =ᵐ[volume]
      fun u => (paperPoissonSymbol h d u : ℂ) * f u :=
  lpBoundedMulCLM_coeFn _ _ _ f

/-- The port belongs to the entire modulation commutant, without a frequency cutoff. -/
def paperPoissonPortCommutant (h d : ℝ≥0) : paperModulationCommutant :=
  ⟨paperPoissonPort h d, mem_paperModulationCommutant_of_mul _ _ (paperPoissonPort_apply_ae h d)⟩

theorem norm_paperPoissonPort (h d : ℝ≥0) : ‖paperPoissonPort h d‖ = 1 := by
  apply le_antisymm
  · exact norm_lpBoundedMulCLM_le _ _ _
  · have hp := norm_symbol_le_of_ae_mul_continuous
      (Complex.continuous_ofReal.comp (continuous_paperPoissonSymbol h d))
      (paperPoissonPort_apply_ae h d) 0
    simpa only [Function.comp_apply, paperPoissonSymbol_zero_frequency,
      Complex.ofReal_one, norm_one] using hp

theorem paperPoissonPort_ne_zero (h d : ℝ≥0) : paperPoissonPort h d ≠ 0 := by
  intro hz
  have hn := norm_paperPoissonPort h d
  rw [hz, norm_zero] at hn
  exact zero_ne_one hn

/-- No compact operator can reduce the unit norm of this native continuum transfer. -/
theorem one_le_norm_paperPoissonPort_sub_compact (h d : ℝ≥0)
    (K : compactOperatorStarAlgebra PaperPoissonSpace) :
    1 ≤ ‖paperPoissonPort h d - K.1‖ := by
  have hp := paperModulationCommutant_norm_le_sub_compact (paperPoissonPortCommutant h d) K
  change ‖paperPoissonPort h d‖ ≤ _ at hp
  rwa [norm_paperPoissonPort] at hp

theorem compactIdealDistance_paperPoissonPort (h d : ℝ≥0) :
    compactIdealDistance (paperPoissonPort h d) = 1 :=
  (paperModulationCommutant_compactIdealDistance (paperPoissonPortCommutant h d)).trans
    (norm_paperPoissonPort h d)

theorem paperPoissonPort_not_compact (h d : ℝ≥0) :
    ¬ IsCompactOperator (paperPoissonPort h d) := by
  intro hc
  have hp := one_le_norm_paperPoissonPort_sub_compact h d ⟨paperPoissonPort h d, hc⟩
  simp only [sub_self, norm_zero] at hp
  norm_num at hp

/-- The proven TraceCone cost is infinite at every depth and gap. -/
theorem paperPoissonPort_traceCost (h d : ℝ≥0) :
    compactOperatorTraceCost PaperPoissonSpace (paperPoissonPort h d) = ∞ :=
  (compactOperatorTraceCost_eq_top_iff _).2 (paperPoissonPort_not_compact h d)

theorem paperPoissonPort_traceCost_add_compact (h d : ℝ≥0)
    (K : compactOperatorStarAlgebra PaperPoissonSpace) :
    compactOperatorTraceCost PaperPoissonSpace (paperPoissonPort h d + K.1) = ∞ := by
  rw [compactOperatorTraceCost_add_compact, paperPoissonPort_traceCost]

/-- Positive smoothing loses no Hilbert-space source vector. -/
theorem paperPoissonPort_injective (h d : ℝ≥0) : Function.Injective (paperPoissonPort h d) := by
  apply lpBoundedMulCLM_injective_general
  intro u
  change (paperPoissonSymbol h d u : ℂ) ≠ 0
  exact_mod_cast (paperPoissonSymbol_pos h d u).ne'

/-- Every Hilbert-space target remains in the closure of the actual transfer range. -/
theorem paperPoissonPort_denseRange (h d : ℝ≥0) : DenseRange (paperPoissonPort h d) := by
  apply denseRange_lpBoundedMulCLM
  · intro u
    simp
  · intro u
    change (paperPoissonSymbol h d u : ℂ) ≠ 0
    exact_mod_cast (paperPoissonSymbol_pos h d u).ne'

@[simp] theorem paperPoissonPort_zero_gap (h : ℝ≥0) : paperPoissonPort h 0 = 1 := by
  apply ContinuousLinearMap.ext
  intro f
  change paperPoissonPort h 0 f = f
  apply Lp.ext
  filter_upwards [paperPoissonPort_apply_ae h 0 f] with u hu
  simpa only [paperPoissonSymbol_zero_gap, Complex.ofReal_one, one_mul] using hu

/-- The entire continuum operators satisfy the source-depth transfer law. -/
theorem paperPoissonPort_compose (h d e : ℝ≥0) :
    paperPoissonPort h d * paperPoissonPort (h + d) e = paperPoissonPort h (d + e) := by
  apply ContinuousLinearMap.ext
  intro f
  change paperPoissonPort h d (paperPoissonPort (h + d) e f) = _
  apply Lp.ext
  filter_upwards [paperPoissonPort_apply_ae h d (paperPoissonPort (h + d) e f),
    paperPoissonPort_apply_ae (h + d) e f, paperPoissonPort_apply_ae h (d + e) f]
    with u hu hv hw
  rw [hu, hv, hw, ← mul_assoc, ← Complex.ofReal_mul, paperPoissonSymbol_compose]

/-- Every distance between two native continuum ports survives modulo compact operators. -/
theorem compactIdealDistance_paperPoissonPort_sub (h d k e : ℝ≥0) :
    compactIdealDistance (paperPoissonPort h d - paperPoissonPort k e) =
      ‖paperPoissonPort h d - paperPoissonPort k e‖ :=
  paperModulationCommutant_compactIdealDistance
    (paperPoissonPortCommutant h d - paperPoissonPortCommutant k e)

/-- Compact equivalence of native continuum ports is literal operator equality. -/
theorem paperPoissonPort_compact_sub_iff_eq (h d k e : ℝ≥0) :
    IsCompactOperator (paperPoissonPort h d - paperPoissonPort k e) ↔
      paperPoissonPort h d = paperPoissonPort k e := by
  change IsCompactOperator ((paperPoissonPortCommutant h d).1 -
    (paperPoissonPortCommutant k e).1) ↔
      (paperPoissonPortCommutant h d).1 = (paperPoissonPortCommutant k e).1
  rw [paperModulationCommutant_compact_sub_iff_eq
    (paperPoissonPortCommutant h d) (paperPoissonPortCommutant k e)]
  exact Subtype.ext_iff

end
end RHTower
