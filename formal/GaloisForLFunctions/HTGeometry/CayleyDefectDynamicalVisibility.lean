import GaloisForLFunctions.HTGeometry.GeometricAmplitudeDominance
import Mathlib.Analysis.Complex.Basic

/-!
# Dynamical visibility of positive Cayley defects

A positive summable mass carried at nonzero points of the open unit disc has an inverse-radial
moment tower.  Every atom is amplified geometrically, without phase cancellation.  Consequently a
nonempty defect supports a positive exponential lower bound at every observation order, and a
bounded full tower forces the defect to be empty.

This is an index-free law.  The Riemann-Xi application supplies the masses from its endpoint source
and the disc points from the Li Cayley coordinate.
-/

open scoped BigOperators

namespace HTGeometry

noncomputable section

variable {I : Type*}

/-- The `n`-th inverse-radial moment of a positively marked Cayley divisor. -/
def inverseRadialMoment (a : I → ℝ) (w : I → ℂ) (n : ℕ) : ℝ :=
  ∑' i : I, a i * ‖w i‖⁻¹ ^ n

/-- Every summable inverse-radial moment is nonnegative when all marks are nonnegative. -/
theorem inverseRadialMoment_nonneg
    (a : I → ℝ) (w : I → ℂ) (ha : ∀ i, 0 ≤ a i) (n : ℕ) :
    0 ≤ inverseRadialMoment a w n := by
  rw [inverseRadialMoment]
  exact tsum_nonneg fun i => mul_nonneg (ha i) (pow_nonneg (inv_nonneg.mpr (norm_nonneg _)) _)

/-- Every atom is a pointwise lower bound for the complete positive moment. -/
theorem le_inverseRadialMoment
    (a : I → ℝ) (w : I → ℂ) (ha : ∀ i, 0 ≤ a i)
    (hsum : ∀ n, Summable (fun i => a i * ‖w i‖⁻¹ ^ n))
    (i : I) (n : ℕ) :
    a i * ‖w i‖⁻¹ ^ n ≤ inverseRadialMoment a w n := by
  rw [inverseRadialMoment]
  exact (hsum n).le_tsum i fun j _ =>
    mul_nonneg (ha j) (pow_nonneg (inv_nonneg.mpr (norm_nonneg _)) _)

/-- The zeroth inverse-radial moment is exactly the total marked mass. -/
theorem inverseRadialMoment_zero
    (a : I → ℝ) (w : I → ℂ) :
    inverseRadialMoment a w 0 = ∑' i, a i := by
  simp only [inverseRadialMoment, pow_zero, mul_one]

/-- **Positive Cayley-defect dynamical visibility.**  Every positive atom strictly inside the
unit disc supplies a positive exponential lower bound at every observation order. -/
theorem exists_exponential_lowerBound_inverseRadialMoment
    (a : I → ℝ) (w : I → ℂ)
    (ha : ∀ i, 0 < a i)
    (hw0 : ∀ i, w i ≠ 0)
    (hw1 : ∀ i, ‖w i‖ < 1)
    (hsum : ∀ n, Summable (fun i => a i * ‖w i‖⁻¹ ^ n))
    (i : I) :
    ∃ m c : ℝ, 0 < m ∧ 1 < c ∧
      ∀ n : ℕ, m * c ^ n ≤ inverseRadialMoment a w n := by
  refine ⟨a i, ‖w i‖⁻¹, ha i, ?_, ?_⟩
  · exact (one_lt_inv₀ (norm_pos_iff.mpr (hw0 i))).mpr (hw1 i)
  · intro n
    exact le_inverseRadialMoment a w (fun j => (ha j).le) hsum i n

/-- A bounded inverse-radial tower has no positive atom in the open unit disc. -/
theorem isEmpty_of_bounded_inverseRadialMoment
    (a : I → ℝ) (w : I → ℂ)
    (ha : ∀ i, 0 < a i)
    (hw0 : ∀ i, w i ≠ 0)
    (hw1 : ∀ i, ‖w i‖ < 1)
    (hsum : ∀ n, Summable (fun i => a i * ‖w i‖⁻¹ ^ n))
    (hbounded : ∃ K : ℝ, ∀ n : ℕ, inverseRadialMoment a w n ≤ K) :
    IsEmpty I := by
  constructor
  intro i
  obtain ⟨m, c, hm, hc, hlower⟩ :=
    exists_exponential_lowerBound_inverseRadialMoment a w ha hw0 hw1 hsum i
  obtain ⟨K, hK⟩ := hbounded
  exact not_forall_mul_pow_le hc hm (fun n => (hlower n).trans (hK n))

end

end HTGeometry
