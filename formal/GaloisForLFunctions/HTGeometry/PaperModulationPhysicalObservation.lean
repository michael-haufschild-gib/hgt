import GaloisForLFunctions.HTGeometry.PaperModulationCalkin
import GaloisForLFunctions.HTGeometry.L2PhysicalSolidObservation

/-! # Physical phase masks retain modulation-conjugate observations

The physical solid hull is invariant under modulation. Hence its complete
supremal response is invariant under conjugation, even for compact operators
whose conjugates converge strongly to zero on every fixed input.
-/

namespace GaloisForLFunctions.HTGeometry
noncomputable section
open MeasureTheory Filter Topology
local notation "H" => Lp ℂ 2 (volume : Measure ℝ)

theorem modulationMul_mem_l2PhysicalSolidHull (t : ℝ) {x y : H}
    (hy : y ∈ l2PhysicalSolidHull x) : modulationMul t y ∈ l2PhysicalSolidHull x := by
  filter_upwards [hy, coeFn_modulationMul t y] with u hu he
  rw [he, norm_mul, norm_modulationSymbol, one_mul]
  exact hu

theorem modulationMul_physical_modulus (t : ℝ) (x : H) :
    ∀ᵐ u ∂(volume : Measure ℝ), ‖modulationMul t x u‖ = ‖x u‖ := by
  filter_upwards [coeFn_modulationMul t x] with u hu
  rw [hu, norm_mul, norm_modulationSymbol, one_mul]

theorem image_modulationMul_l2PhysicalSolidHull (t : ℝ) (x : H) :
    modulationMul t '' l2PhysicalSolidHull x = l2PhysicalSolidHull x := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact modulationMul_mem_l2PhysicalSolidHull t hz
  · intro hy
    refine ⟨modulationMul (-t) y, modulationMul_mem_l2PhysicalSolidHull (-t) hy, ?_⟩
    rw [modulationMul_modulationMul, add_neg_cancel, modulationMul_zero_apply]

def modulationPhysicalConjugate (t : ℝ) (T : H →L[ℂ] H) : H →L[ℂ] H :=
  modulationMul (-t) ∘L (T ∘L modulationMul t)

@[simp] theorem modulationPhysicalConjugate_apply (t : ℝ) (T : H →L[ℂ] H) (x : H) :
    modulationPhysicalConjugate t T x = modulationMul (-t) (T (modulationMul t x)) := rfl

theorem modulationPhysicalConjugate_apply_norm (t : ℝ) (T : H →L[ℂ] H) (x : H) :
    ‖modulationPhysicalConjugate t T x‖ = ‖T (modulationMul t x)‖ :=
  norm_modulationMul_eq _ _

theorem modulationPhysicalConjugate_norm_le (t : ℝ) (T : H →L[ℂ] H) :
    ‖modulationPhysicalConjugate t T‖ ≤ ‖T‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg T)
  intro x
  rw [modulationPhysicalConjugate_apply_norm]
  simpa only [norm_modulationMul_eq] using T.le_opNorm (modulationMul t x)

theorem modulationPhysicalConjugate_inverse (t : ℝ) (T : H →L[ℂ] H) :
    modulationPhysicalConjugate (-t) (modulationPhysicalConjugate t T) = T := by
  apply ContinuousLinearMap.ext
  intro x
  simp only [modulationPhysicalConjugate_apply, neg_neg, modulationMul_modulationMul,
    add_neg_cancel, modulationMul_zero_apply]

theorem modulationPhysicalConjugate_norm (t : ℝ) (T : H →L[ℂ] H) :
    ‖modulationPhysicalConjugate t T‖ = ‖T‖ := by
  apply le_antisymm (modulationPhysicalConjugate_norm_le t T)
  have h := modulationPhysicalConjugate_norm_le (-t) (modulationPhysicalConjugate t T)
  rwa [modulationPhysicalConjugate_inverse] at h

/-- A literal unit-modulus physical mask retains the exact original response. -/
theorem modulationPhysicalConjugate_adaptive_norm (t : ℝ) (T : H →L[ℂ] H) (x : H) :
    ‖modulationPhysicalConjugate t T (modulationMul (-t) x)‖ = ‖T x‖ := by
  rw [modulationPhysicalConjugate_apply_norm, modulationMul_modulationMul,
    add_neg_cancel, modulationMul_zero_apply]

/-- The entire physical-mask supremum is unchanged, not merely bounded below. -/
theorem l2PhysicalObservation_modulationConjugate (t : ℝ) (T : H →L[ℂ] H) (x : H) :
    l2PhysicalObservation (modulationPhysicalConjugate t T) x = l2PhysicalObservation T x := by
  unfold l2PhysicalObservation
  congr 1
  ext r
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨modulationMul t y, modulationMul_mem_l2PhysicalSolidHull t hy,
      (modulationPhysicalConjugate_apply_norm t T y).symm⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨modulationMul (-t) y, modulationMul_mem_l2PhysicalSolidHull (-t) hy,
      modulationPhysicalConjugate_adaptive_norm t T y⟩

theorem modulationPhysicalConjugate_compact (t : ℝ) (K : compactOperatorStarAlgebra H) :
    IsCompactOperator (modulationPhysicalConjugate t K.1) :=
  (K.2.comp_clm (modulationMul t)).clm_comp (modulationMul (-t))

theorem modulationPhysicalConjugate_traceCost (t : ℝ) (K : compactOperatorStarAlgebra H) :
    compactOperatorTraceCost H (modulationPhysicalConjugate t K.1) = 0 :=
  (compactOperatorTraceCost_eq_zero_iff _).mpr (modulationPhysicalConjugate_compact t K)

theorem modulationPhysicalConjugate_strong (K : compactOperatorStarAlgebra H) (x : H) :
    Tendsto (fun N : ℕ => modulationPhysicalConjugate (N : ℝ) K.1 x) atTop (𝓝 0) :=
  modulationMul_compact_conjugation_tendsto K x

theorem modulationPhysicalObservation_tendsto_zero_iff (T : H →L[ℂ] H) (x : H) :
    Tendsto (fun N : ℕ => l2PhysicalObservation (modulationPhysicalConjugate (N : ℝ) T) x)
      atTop (𝓝 0) ↔ ∀ y ∈ l2PhysicalSolidHull x, T y = 0 := by
  simp only [l2PhysicalObservation_modulationConjugate, tendsto_const_nhds_iff,
    l2PhysicalObservation_eq_zero_iff]

end
end GaloisForLFunctions.HTGeometry
