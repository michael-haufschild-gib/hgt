import GaloisForLFunctions.HTGeometry.CenteredIndicatorHilbert
import GaloisForLFunctions.HTGeometry.FiniteRankTransportUnitary

open MeasureTheory Set

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Unit normalization used to represent an unoriented real ray. -/
def normalizedRayVector (v : E) : E := ‖v‖⁻¹ • v

/-- Rank-one projector represented by a normalized ray vector. -/
def normalizedRankOneProjection (v : E) : E →L[ℝ] E :=
  rankOneTransport (𝕜 := ℝ) (normalizedRayVector v) (normalizedRayVector v)

theorem normalizedRayVector_neg (v : E) :
    normalizedRayVector (-v) = -normalizedRayVector v := by
  rw [normalizedRayVector, normalizedRayVector, norm_neg]
  module

/-- Unoriented rank-one projection identifies antipodal vectors. -/
theorem normalizedRankOneProjection_neg (v : E) :
    normalizedRankOneProjection (-v) = normalizedRankOneProjection v := by
  rw [normalizedRankOneProjection, normalizedRankOneProjection, normalizedRayVector_neg]
  ext x
  simp [rankOneTransport_apply]

/-- Chordal gap of two real rays, in its exact Gram form `(AH19)`. -/
def realProjectiveChordalGap (v w : E) : ℝ :=
  Real.sqrt (1 - (inner ℝ v w) ^ (2 : ℕ) / (‖v‖ ^ (2 : ℕ) * ‖w‖ ^ (2 : ℕ)))

theorem realProjectiveChordalGap_eq (v w : E) :
    realProjectiveChordalGap v w =
      Real.sqrt (1 - (inner ℝ v w) ^ (2 : ℕ) / (‖v‖ ^ (2 : ℕ) * ‖w‖ ^ (2 : ℕ))) :=
  rfl

theorem realProjectiveChordalGap_neg_left (v w : E) :
    realProjectiveChordalGap (-v) w = realProjectiveChordalGap v w := by
  simp [realProjectiveChordalGap]

theorem realProjectiveChordalGap_neg_right (v w : E) :
    realProjectiveChordalGap v (-w) = realProjectiveChordalGap v w := by
  simp [realProjectiveChordalGap]

/-- Same-sign and antipodal two-point clouds have identical ray projectors. -/
theorem same_antipodal_cloud_projectors_eq (v : E) (i : Fin 2) :
    normalizedRankOneProjection ((fun _ : Fin 2 => v) i) =
      normalizedRankOneProjection ((fun j : Fin 2 => if j = 0 then v else -v) i) := by
  fin_cases i
  · simp
  · simpa using (normalizedRankOneProjection_neg v).symm

/-- Same-sign and antipodal clouds have identical complete pairwise projective-gap data. -/
theorem same_antipodal_cloud_projectiveGap_eq (v : E) (i j : Fin 2) :
    realProjectiveChordalGap ((fun _ : Fin 2 => v) i) ((fun _ : Fin 2 => v) j) =
      realProjectiveChordalGap
        ((fun k : Fin 2 => if k = 0 then v else -v) i)
        ((fun k : Fin 2 => if k = 0 then v else -v) j) := by
  fin_cases i <;> fin_cases j <;>
    simp [realProjectiveChordalGap_neg_left, realProjectiveChordalGap_neg_right]

/-- Oriented resultant of the repeated cloud retains four times the one-vector energy. -/
theorem norm_sq_same_oriented_pair (v : E) :
    ‖v + v‖ ^ (2 : ℕ) = 4 * ‖v‖ ^ (2 : ℕ) := by
  rw [← two_smul ℝ v, norm_smul, Real.norm_ofNat]
  ring

/-- Oriented resultant of the antipodal cloud cancels exactly. -/
theorem norm_sq_antipodal_oriented_pair (v : E) :
    ‖v + -v‖ ^ (2 : ℕ) = 0 := by
  simp

/-- Complete abstract projective-blindness no-go: all unoriented data agree while oriented
resultant energies are `4‖v‖²` and `0`. -/
theorem projectiveGap_cannot_recover_oriented_resultant (v : E) :
    (∀ i : Fin 2,
      normalizedRankOneProjection ((fun _ : Fin 2 => v) i) =
        normalizedRankOneProjection ((fun j : Fin 2 => if j = 0 then v else -v) i)) ∧
    (∀ i j : Fin 2,
      realProjectiveChordalGap ((fun _ : Fin 2 => v) i) ((fun _ : Fin 2 => v) j) =
        realProjectiveChordalGap
          ((fun k : Fin 2 => if k = 0 then v else -v) i)
          ((fun k : Fin 2 => if k = 0 then v else -v) j)) ∧
    ‖v + v‖ ^ (2 : ℕ) = 4 * ‖v‖ ^ (2 : ℕ) ∧
    ‖v + -v‖ ^ (2 : ℕ) = 0 := by
  exact ⟨same_antipodal_cloud_projectors_eq v,
    same_antipodal_cloud_projectiveGap_eq v,
    norm_sq_same_oriented_pair v,
    norm_sq_antipodal_oriented_pair v⟩

/-- The abstract projective no-go specializes exactly to a proper centered aperture and its
relative complement. -/
theorem centeredIndicatorOn_projective_complement_noGo
    {X : Type*} [MeasurableSpace X] (μ : Measure X) (Ω E : Set X)
    (hΩ : MeasurableSet Ω) (hΩfin : μ Ω ≠ ⊤)
    (hE : MeasurableSet E) (hEfin : μ E ≠ ⊤)
    (hEΩ : E ⊆ Ω) (hΩpos : 0 < μ.real Ω) :
    let κ := centeredIndicatorOn μ Ω E hΩ hΩfin hE hEfin
    let κc := centeredIndicatorOn μ Ω (Ω \ E) hΩ hΩfin (hΩ.diff hE)
      (measure_ne_top_of_subset Set.sdiff_subset hΩfin)
    normalizedRankOneProjection κc = normalizedRankOneProjection κ ∧
      realProjectiveChordalGap κ κc = realProjectiveChordalGap κ κ ∧
      ‖κ + κ‖ ^ (2 : ℕ) = 4 * ‖κ‖ ^ (2 : ℕ) ∧
      ‖κ + κc‖ ^ (2 : ℕ) = 0 := by
  dsimp only
  rw [centeredIndicatorOn_sdiff_eq_neg μ Ω E hΩ hΩfin hE hEfin hEΩ hΩpos]
  exact ⟨normalizedRankOneProjection_neg _,
    realProjectiveChordalGap_neg_right _ _,
    norm_sq_same_oriented_pair _,
    norm_sq_antipodal_oriented_pair _⟩

end
end GaloisForLFunctions.HTGeometry
