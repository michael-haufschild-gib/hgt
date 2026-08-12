import GaloisForLFunctions.HTGeometry.RectangularTraceNorm
import GaloisForLFunctions.RHTower.TraceNormLimit
import GaloisForLFunctions.RHTower.WeakSchattenResidue

namespace RHTower

noncomputable section

variable {E F G : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable [NormedAddCommGroup G] [InnerProductSpace ℂ G]

/-- Weak rectangular Schatten membership, with every source-to-target
approximation multiplicity retained. -/
def MemRectWeakSchattenClass (p : ℝ) (T : E →L[ℂ] F) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ,
    rectApproxNumber T n ^ p ≤ C / ((n : ℝ) + 1)

theorem memRectWeakSchattenClass_iff_lowerBlock (p : ℝ) (T : E →L[ℂ] F) :
    MemRectWeakSchattenClass p T ↔
      MemWeakSchattenClass p (rectangularLowerBlock T) := by
  unfold MemRectWeakSchattenClass MemWeakSchattenClass
  simp_rw [rectApproxNumber_eq_approxNumber_lowerBlock]

theorem memRectWeakSchattenClass_iff_memWeakSchattenClass
    (p : ℝ) (T : E →L[ℂ] E) :
    MemRectWeakSchattenClass p T ↔ MemWeakSchattenClass p T := by
  rfl

/-- A bounded target map preserves the rectangular weak trace class. -/
theorem MemRectWeakSchattenClass.one_comp_left
    {T : E →L[ℂ] F} (hT : MemRectWeakSchattenClass 1 T)
    (A : F →L[ℂ] G) :
    MemRectWeakSchattenClass 1 (A ∘L T) := by
  obtain ⟨C, hC, hbound⟩ := hT
  refine ⟨‖A‖ * C, mul_nonneg (norm_nonneg _) hC, fun n => ?_⟩
  simp only [Real.rpow_one] at hbound ⊢
  calc
    rectApproxNumber (A ∘L T) n ≤ ‖A‖ * rectApproxNumber T n :=
      rectApproxNumber_comp_le_left A T n
    _ ≤ ‖A‖ * (C / ((n : ℝ) + 1)) :=
      mul_le_mul_of_nonneg_left (hbound n) (norm_nonneg _)
    _ = ‖A‖ * C / ((n : ℝ) + 1) := by ring

/-- A bounded source map preserves the rectangular weak trace class. -/
theorem MemRectWeakSchattenClass.one_comp_right
    {T : E →L[ℂ] F} (hT : MemRectWeakSchattenClass 1 T)
    (B : G →L[ℂ] E) :
    MemRectWeakSchattenClass 1 (T ∘L B) := by
  obtain ⟨C, hC, hbound⟩ := hT
  refine ⟨C * ‖B‖, mul_nonneg hC (norm_nonneg _), fun n => ?_⟩
  simp only [Real.rpow_one] at hbound ⊢
  calc
    rectApproxNumber (T ∘L B) n ≤ rectApproxNumber T n * ‖B‖ :=
      rectApproxNumber_comp_le_right T B n
    _ ≤ (C / ((n : ℝ) + 1)) * ‖B‖ :=
      mul_le_mul_of_nonneg_right (hbound n) (norm_nonneg _)
    _ = C * ‖B‖ / ((n : ℝ) + 1) := by ring

variable [CompleteSpace E] [CompleteSpace F]

/-- Rectangular Schatten-one maps are closed under subtraction. -/
theorem MemRectSchattenClass.one_sub
    {S T : E →L[ℂ] F} (hS : MemRectSchattenClass 1 S)
    (hT : MemRectSchattenClass 1 T) :
    MemRectSchattenClass 1 (S - T) := by
  apply (memRectSchattenClass_iff_lowerBlock 1 (S - T)).2
  rw [rectangularLowerBlock_sub]
  exact ((memRectSchattenClass_iff_lowerBlock 1 S).1 hS).one_sub
    ((memRectSchattenClass_iff_lowerBlock 1 T).1 hT)

end

end RHTower
