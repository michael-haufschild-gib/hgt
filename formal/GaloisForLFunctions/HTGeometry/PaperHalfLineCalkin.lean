import GaloisForLFunctions.HTGeometry.SchurKernelHalfLineCompression
import GaloisForLFunctions.HTGeometry.PaperModulationOrder

/-!
# Faithful compact quotient on the continuous half-line

Zero extension transports actual half-line multiplication to the full-line
modulation commutant. This preserves its operator norm and order, including
against arbitrary compact corrections. Decay of a symbol at infinity does
not turn its multiplication operator into a compact operator.
-/

namespace GaloisForLFunctions.HTGeometry
noncomputable section
open MeasureTheory Set Classical
open scoped ENNReal

private abbrev H := Lp ℂ 2 (volume : Measure ℝ)
private abbrev P := Lp ℂ 2 halfLineMeasure

/-- Extension by zero of a half-line operator, with zero action off the half-line. -/
def paperHalfLineLift (A : P →L[ℂ] P) : H →L[ℂ] H :=
  halfLineExtend ∘L A ∘L halfLineRestrict

theorem norm_halfLineExtend_le_one : ‖halfLineExtend‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  change ‖halfLineExtendLM f‖ ≤ 1 * ‖f‖
  rw [norm_halfLineExtendLM, one_mul]

theorem norm_halfLineRestrict_le_one : ‖halfLineRestrict‖ ≤ 1 := by
  rw [← adjoint_halfLineExtend, ContinuousLinearMap.adjoint.norm_map]
  exact norm_halfLineExtend_le_one

theorem paperHalfLineLift_compress (A : P →L[ℂ] P) :
    halfLineRestrict ∘L paperHalfLineLift A ∘L halfLineExtend = A := by
  simp only [paperHalfLineLift, ← ContinuousLinearMap.comp_assoc,
    halfLineRestrict_comp_halfLineExtend, ContinuousLinearMap.id_comp]
  rw [ContinuousLinearMap.comp_assoc, halfLineRestrict_comp_halfLineExtend,
    ContinuousLinearMap.comp_id]

theorem norm_paperHalfLineLift (A : P →L[ℂ] P) : ‖paperHalfLineLift A‖ = ‖A‖ := by
  have hupper : ‖paperHalfLineLift A‖ ≤ ‖A‖ := by
    calc
      _ ≤ ‖halfLineExtend‖ * (‖A‖ * ‖halfLineRestrict‖) :=
        (ContinuousLinearMap.opNorm_comp_le _ _).trans
          (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
      _ ≤ 1 * (‖A‖ * 1) := by
        gcongr
        · exact norm_halfLineExtend_le_one
        · exact norm_halfLineRestrict_le_one
      _ = ‖A‖ := by ring
  apply le_antisymm hupper
  calc
    ‖A‖ = ‖halfLineRestrict ∘L paperHalfLineLift A ∘L halfLineExtend‖ := by
      rw [paperHalfLineLift_compress]
    _ ≤ ‖halfLineRestrict‖ * (‖paperHalfLineLift A‖ * ‖halfLineExtend‖) :=
      (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
    _ ≤ 1 * (‖paperHalfLineLift A‖ * 1) := by
      gcongr
      · exact norm_halfLineRestrict_le_one
      · exact norm_halfLineExtend_le_one
    _ = ‖paperHalfLineLift A‖ := by ring

theorem paperHalfLineLift_sub (A B : P →L[ℂ] P) :
    paperHalfLineLift (A - B) = paperHalfLineLift A - paperHalfLineLift B := by
  simp only [paperHalfLineLift, ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub]

theorem paperHalfLineLift_add (A B : P →L[ℂ] P) :
    paperHalfLineLift (A + B) = paperHalfLineLift A + paperHalfLineLift B := by
  simp only [paperHalfLineLift, ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_add]

theorem paperHalfLineLift_positive_iff (A : P →L[ℂ] P) :
    (paperHalfLineLift A).IsPositive ↔ A.IsPositive := by
  constructor
  · intro h
    have hh := h.adjoint_conj halfLineExtend
    simpa only [adjoint_halfLineExtend, paperHalfLineLift_compress] using hh
  · intro h
    simpa only [paperHalfLineLift, adjoint_halfLineExtend] using h.conj_adjoint halfLineExtend

theorem paperHalfLineLift_compact {A : P →L[ℂ] P} (hA : IsCompactOperator A) :
    IsCompactOperator (paperHalfLineLift A) :=
  (hA.comp_clm halfLineRestrict).clm_comp halfLineExtend

theorem paperHalfLineLift_mul_ae {A : P →L[ℂ] P} {ψ : ℝ → ℂ}
    (hA : ∀ f, (A f : ℝ → ℂ) =ᵐ[halfLineMeasure] fun x => ψ x * f x) (f : H) :
    (paperHalfLineLift A f : ℝ → ℂ) =ᵐ[volume]
      fun x => (Ici (0 : ℝ)).indicator ψ x * f x := by
  filter_upwards [halfLineExtend_coeFn (A (halfLineRestrict f)),
    (ae_restrict_iff' measurableSet_Ici).mp (hA (halfLineRestrict f)),
    (ae_restrict_iff' measurableSet_Ici).mp (halfLineRestrict_coeFn f)] with x hE hA hR
  change (halfLineExtend (A (halfLineRestrict f)) : ℝ → ℂ) x = _
  rw [hE]
  by_cases hx : x ∈ Ici (0 : ℝ)
  · rw [indicator_of_mem hx, indicator_of_mem hx, hA hx, hR hx]
  · rw [indicator_of_notMem hx, indicator_of_notMem hx, zero_mul]

theorem paperHalfLineLift_mem_commutant {A : P →L[ℂ] P} {ψ : ℝ → ℂ}
    (hA : ∀ f, (A f : ℝ → ℂ) =ᵐ[halfLineMeasure] fun x => ψ x * f x) :
    paperHalfLineLift A ∈ paperModulationCommutant :=
  mem_paperModulationCommutant_of_mul _ _ (paperHalfLineLift_mul_ae hA)

/-- Only the values on the actual half-line enter the norm bound. -/
theorem paperHalfLine_norm_le {A : P →L[ℂ] P} {ψ : ℝ → ℂ}
    (hA : ∀ f, (A f : ℝ → ℂ) =ᵐ[halfLineMeasure] fun x => ψ x * f x)
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ x ≥ 0, ‖ψ x‖ ≤ C) : ‖A‖ ≤ C := by
  rw [← norm_paperHalfLineLift]
  apply norm_le_of_ae_mul hC _ (paperHalfLineLift_mul_ae hA)
  intro x
  by_cases hx : x ∈ Ici (0 : ℝ)
  · rw [indicator_of_mem hx]
    exact hbound x hx
  · rw [indicator_of_notMem hx, norm_zero]
    exact hC

/-- The entire operator norm survives every compact correction on the actual half-line. -/
theorem paperHalfLine_norm_le_sub_compact {A : P →L[ℂ] P} {ψ : ℝ → ℂ}
    (hA : ∀ f, (A f : ℝ → ℂ) =ᵐ[halfLineMeasure] fun x => ψ x * f x)
    (K : compactOperatorStarAlgebra P) : ‖A‖ ≤ ‖A - K.1‖ := by
  have h := paperModulationCommutant_norm_le_sub_compact
    ⟨paperHalfLineLift A, paperHalfLineLift_mem_commutant hA⟩
    ⟨paperHalfLineLift K.1, paperHalfLineLift_compact K.2⟩
  simpa only [← paperHalfLineLift_sub, norm_paperHalfLineLift] using h

theorem paperHalfLine_compactIdealDistance {A : P →L[ℂ] P} {ψ : ℝ → ℂ}
    (hA : ∀ f, (A f : ℝ → ℂ) =ᵐ[halfLineMeasure] fun x => ψ x * f x) :
    compactIdealDistance A = ‖A‖ := by
  apply le_antisymm
  · simpa using compactIdealDistance_le A 0 isCompactOperator_zero
  · exact le_compactIdealDistance A ‖A‖ fun K hK =>
      paperHalfLine_norm_le_sub_compact hA ⟨K, hK⟩

theorem paperHalfLine_compact_iff_zero {A : P →L[ℂ] P} {ψ : ℝ → ℂ}
    (hA : ∀ f, (A f : ℝ → ℂ) =ᵐ[halfLineMeasure] fun x => ψ x * f x) :
    IsCompactOperator A ↔ A = 0 := by
  constructor
  · intro h
    have hn := paperHalfLine_norm_le_sub_compact hA ⟨A, h⟩
    rw [sub_self, norm_zero] at hn
    exact norm_eq_zero.mp (le_antisymm hn (norm_nonneg _))
  · rintro rfl
    exact isCompactOperator_zero

theorem paperHalfLine_traceCost {A : P →L[ℂ] P} {ψ : ℝ → ℂ}
    (hA : ∀ f, (A f : ℝ → ℂ) =ᵐ[halfLineMeasure] fun x => ψ x * f x) :
    compactOperatorTraceCost P A = if A = 0 then 0 else ∞ := by
  rw [compactOperatorTraceCost_eq, paperHalfLine_compact_iff_zero hA]

/-- Compact corrections cannot create positivity in a self-adjoint half-line multiplier. -/
theorem paperHalfLine_exists_compact_positive_iff {A : P →L[ℂ] P} {ψ : ℝ → ℂ}
    (hA : ∀ f, (A f : ℝ → ℂ) =ᵐ[halfLineMeasure] fun x => ψ x * f x)
    (hself : IsSelfAdjoint A) :
    (∃ K : compactOperatorStarAlgebra P, (A + K.1).IsPositive) ↔ A.IsPositive := by
  constructor
  · rintro ⟨K, hK⟩
    have hp := (paperHalfLineLift_positive_iff (A + K.1)).mpr hK
    rw [paperHalfLineLift_add] at hp
    have hs : IsSelfAdjoint (paperHalfLineLift A) := by
      simpa only [paperHalfLineLift, adjoint_halfLineExtend] using hself.conj_adjoint halfLineExtend
    exact (paperHalfLineLift_positive_iff A).mp
      (paperModulationCommutant_positive_of_compact
        ⟨paperHalfLineLift A, paperHalfLineLift_mem_commutant hA⟩ hs
        ⟨paperHalfLineLift K.1, paperHalfLineLift_compact K.2⟩ hp)
  · intro h
    exact ⟨0, by simpa using h⟩

end
end GaloisForLFunctions.HTGeometry
