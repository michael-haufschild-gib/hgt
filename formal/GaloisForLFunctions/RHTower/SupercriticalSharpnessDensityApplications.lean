import GaloisForLFunctions.HTGeometry.SupercriticalSharpnessMechanisms
import GaloisForLFunctions.RHTower.DirichletLZeroDensityVerticalWindow

/-!
# Finite-density selection for Dirichlet-L zero windows

Closed applications of the finite-family density selector from arXiv:2603.03257 to the corpus's
centered Dirichlet-L zero-density aggregates.
-/

namespace RHTower

/-- Primitive contribution of one ambient nonprincipal character. -/
noncomputable def primitiveVerticalWindowTerm
    (n : ℕ) (σ τ : ℝ) (H : NNReal) (χ : NonprincipalDirichletCharacter n) : ℝ := by
  classical
  exact if DirichletCharacter.IsPrimitive χ.1 then
    completedLFunctionZeroDensityVerticalWindowCount n χ σ τ H else 0

/-- The nonprincipal-character carrier is empty, or one character carries at least the average
centered-window zero count. -/
theorem completedLFunctionFamilyVerticalWindow_empty_or_exists_averageCarrier
    (n : ℕ) (σ τ : ℝ) (H : NNReal) :
    Fintype.card (NonprincipalDirichletCharacter n) = 0 ∨
      ∃ χ : NonprincipalDirichletCharacter n,
        completedLFunctionFamilyZeroDensityVerticalWindowCount n σ τ H ≤
          (Fintype.card (NonprincipalDirichletCharacter n) : ℝ) *
            completedLFunctionZeroDensityVerticalWindowCount n χ σ τ H := by
  simpa [completedLFunctionFamilyZeroDensityVerticalWindowCount] using
    (GaloisForLFunctions.HTGeometry.finiteFamilySum_empty_or_le_card_mul
      (fun χ : NonprincipalDirichletCharacter n ↦
        completedLFunctionZeroDensityVerticalWindowCount n χ σ τ H))

/-- The ambient character carrier is empty, or one character carries at least the average
primitive centered-window contribution (zero for a nonprimitive member). -/
theorem completedLFunctionPrimitiveFamilyVerticalWindow_empty_or_exists_averageCarrier
    (n : ℕ) (σ τ : ℝ) (H : NNReal) :
    Fintype.card (NonprincipalDirichletCharacter n) = 0 ∨
      ∃ χ : NonprincipalDirichletCharacter n,
        completedLFunctionPrimitiveFamilyZeroDensityVerticalWindowCount n σ τ H ≤
          (Fintype.card (NonprincipalDirichletCharacter n) : ℝ) *
            primitiveVerticalWindowTerm n σ τ H χ := by
  classical
  simpa [completedLFunctionPrimitiveFamilyZeroDensityVerticalWindowCount,
    primitiveVerticalWindowTerm] using
    (GaloisForLFunctions.HTGeometry.finiteFamilySum_empty_or_le_card_mul
      (fun χ : NonprincipalDirichletCharacter n ↦
        if DirichletCharacter.IsPrimitive χ.1 then
          completedLFunctionZeroDensityVerticalWindowCount n χ σ τ H else 0))

/-- A zero-length modulus range is empty; otherwise one modulus carries at least the average
primitive-family centered-window count across the range. -/
theorem completedLFunctionPrimitiveRangeVerticalWindow_empty_or_exists_averageModulus
    (Q : ℕ) (σ τ : ℝ) (H : NNReal) :
    Q = 0 ∨ ∃ n : Fin Q,
      completedLFunctionPrimitiveRangeZeroDensityVerticalWindowCount Q σ τ H ≤
        (Q : ℝ) * completedLFunctionPrimitiveFamilyZeroDensityVerticalWindowCount n σ τ H := by
  have hselect := GaloisForLFunctions.HTGeometry.finiteFamilySum_empty_or_le_card_mul
    (fun n : Fin Q ↦
      completedLFunctionPrimitiveFamilyZeroDensityVerticalWindowCount n σ τ H)
  rcases hselect with hempty | ⟨n, hn⟩
  · left
    simpa using hempty
  · right
    refine ⟨n, ?_⟩
    rw [completedLFunctionPrimitiveRangeZeroDensityVerticalWindowCount,
      ← Fin.sum_univ_eq_sum_range
        (fun k ↦ completedLFunctionPrimitiveFamilyZeroDensityVerticalWindowCount k σ τ H) Q]
    simpa using hn

/-- The conductor-divisor carrier is empty, or one divisor carries at least the average primitive
family contribution to the divisor aggregate. -/
theorem completedLFunctionPrimitiveDivisorVerticalWindow_empty_or_exists_averageDivisor
    (q : ℕ) (σ τ : ℝ) (H : NNReal) :
    q.divisors.card = 0 ∨ ∃ d ∈ q.divisors,
      completedLFunctionPrimitiveDivisorZeroDensityVerticalWindowCount q σ τ H ≤
        (q.divisors.card : ℝ) *
          completedLFunctionPrimitiveFamilyZeroDensityVerticalWindowCount (d - 1) σ τ H := by
  classical
  have hselect :=
    GaloisForLFunctions.HTGeometry.finiteFamilySum_empty_or_le_card_mul
      (fun d : q.divisors ↦
        completedLFunctionPrimitiveFamilyZeroDensityVerticalWindowCount (d.1 - 1) σ τ H)
  rcases hselect with hempty | ⟨d, hd⟩
  · left
    simpa [Fintype.card_coe] using hempty
  · right
    refine ⟨d.1, d.2, ?_⟩
    rw [completedLFunctionPrimitiveDivisorZeroDensityVerticalWindowCount,
      ← Finset.sum_attach]
    simpa [Fintype.card_coe] using hd

end RHTower
