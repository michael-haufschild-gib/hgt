import GaloisForLFunctions.HTGeometry.NevLeafFunction
import GaloisForLFunctions.HTGeometry.GaussMomentLimit

/-!
# The leaves form a tight family

Every leaf represents the same moment sequence, so all of them have second moment `s₂` and Chebyshev
gives the same tail bound `s₂/R²` for all of them at once.  Tightness is uniform in the parameter,
with no reference to how the leaves were constructed.
-/

open scoped BigOperators
open MeasureTheory

namespace HTGeometry

variable {s : ℕ → ℝ}

/-- The second moment of a leaf, as a lower integral. -/
theorem lintegral_sq_nevLeaf (h : PositiveMomentForm s) (h0b : BoundedKernel s 0) (h0 : s 0 = 1)
    (t : OnePoint ℝ) :
    ∫⁻ x, ENNReal.ofReal (x ^ 2) ∂(nevLeaf h h0b h0 t : Measure ℝ) = ENNReal.ofReal (s 2) := by
  have hmom := nevLeaf_hasHamburgerMoments h h0b h0 t
  have hint : Integrable (fun x : ℝ => x ^ 2) (nevLeaf h h0b h0 t : Measure ℝ) := (hmom 2).1
  have hval : ∫ x, x ^ 2 ∂(nevLeaf h h0b h0 t : Measure ℝ) = s 2 := (hmom 2).2
  have hnn : 0 ≤ᵐ[(nevLeaf h h0b h0 t : Measure ℝ)] fun x : ℝ => x ^ 2 :=
    Filter.Eventually.of_forall fun x => sq_nonneg x
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnn, hval]

/-- **A uniform tail bound for every leaf.** -/
theorem nevLeaf_tail_le (h : PositiveMomentForm s) (h0b : BoundedKernel s 0) (h0 : s 0 = 1)
    (t : OnePoint ℝ) {R : ℝ} (hR : 0 < R) :
    (nevLeaf h h0b h0 t : Measure ℝ) ((Set.Icc (-R) R)ᶜ) ≤ ENNReal.ofReal (s 2 / R ^ 2) := by
  have hle : ∫⁻ x, ENNReal.ofReal (x ^ 2) ∂(nevLeaf h h0b h0 t : Measure ℝ)
      ≤ ENNReal.ofReal (s 2) := le_of_eq (lintegral_sq_nevLeaf h h0b h0 t)
  have hcheb := measure_compl_Icc_le_of_lintegral_sq_le hle hR
  refine le_trans hcheb (le_of_eq ?_)
  rw [ENNReal.ofReal_div_of_pos (by positivity)]

/-- **The leaves form a tight family.** -/
theorem isTightMeasureSet_nevLeaf (h : PositiveMomentForm s) (h0b : BoundedKernel s 0)
    (h0 : s 0 = 1) :
    IsTightMeasureSet (Set.range fun t : OnePoint ℝ => (nevLeaf h h0b h0 t : Measure ℝ)) := by
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ε hε
  rcases eq_or_ne ε ⊤ with rfl | hεtop
  · exact ⟨Set.Icc (-1) 1, isCompact_Icc, fun μ _ => le_top⟩
  · have he0 : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' hεtop
    have hs2 : 0 < s 2 := moment_two_pos h
    have hquot : 0 < s 2 / ε.toReal := div_pos hs2 he0
    refine ⟨Set.Icc (-Real.sqrt (s 2 / ε.toReal)) (Real.sqrt (s 2 / ε.toReal)), isCompact_Icc, ?_⟩
    rintro μ ⟨t, rfl⟩
    have hRpos : 0 < Real.sqrt (s 2 / ε.toReal) := Real.sqrt_pos.mpr hquot
    refine le_trans (nevLeaf_tail_le h h0b h0 t hRpos) ?_
    rw [Real.sq_sqrt hquot.le]
    have hval : s 2 / (s 2 / ε.toReal) = ε.toReal := by
      have hs2' : s 2 ≠ 0 := hs2.ne'
      have he0' : ε.toReal ≠ 0 := he0.ne'
      field_simp
    rw [hval, ENNReal.ofReal_toReal hεtop]

end HTGeometry
