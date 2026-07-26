/-
# Coordinate bounds for Bourgain's six-fold moment cloud

Every coordinate of the six-fold cloud lies in the explicit box

`[0,6H] × [0,6H²] × [0,6H^(3/2)] × [0,6H^(1/2)]`.

These are the `Y_j` values in Bourgain's equation (3.9).
-/
import GaloisForLFunctions.RHTower.BourgainDoubleLargeSieveCloud

open scoped BigOperators

namespace RHTower

noncomputable section

def bourgainMomentCoordinateBound (H : ℕ) : BourgainPhaseSpace :=
  ![6 * (H : ℝ), 6 * (H : ℝ) ^ (2 : ℕ),
    6 * (H : ℝ) ^ (3 / 2 : ℝ),
    6 * (H : ℝ) ^ (1 / 2 : ℝ)]

theorem bourgainIndex_real_le
    {H : ℕ} (h : Fin H) :
    (bourgainIndex h : ℝ) ≤ H := by
  exact_mod_cast bourgainIndex_le h

theorem bourgainMomentCurve_nonneg
    (h : ℕ) (j : Fin 4) :
    0 ≤ bourgainMomentCurve h j := by
  fin_cases j <;> simp [bourgainMomentCurve] <;> positivity

theorem bourgainSixfoldMoment_nonneg
    {H : ℕ} (h : Fin 6 → Fin H) (j : Fin 4) :
    0 ≤ bourgainSixfoldMoment h j := by
  unfold bourgainSixfoldMoment
  simp only [Finset.sum_apply]
  exact Finset.sum_nonneg fun k hk =>
    bourgainMomentCurve_nonneg (bourgainIndex (h k)) j

theorem bourgainSixfoldMoment_le_coordinateBound
    {H : ℕ} (h : Fin 6 → Fin H) (j : Fin 4) :
    bourgainSixfoldMoment h j ≤ bourgainMomentCoordinateBound H j := by
  unfold bourgainSixfoldMoment
  simp only [Finset.sum_apply]
  fin_cases j
  · simp only [bourgainMomentCurve, bourgainMomentCoordinateBound]
    calc
      (∑ k : Fin 6, (bourgainIndex (h k) : ℝ)) ≤
          ∑ _k : Fin 6, (H : ℝ) :=
        Finset.sum_le_sum fun k hk => bourgainIndex_real_le (h k)
      _ = 6 * (H : ℝ) := by norm_num
  · simp only [bourgainMomentCurve, bourgainMomentCoordinateBound]
    calc
      (∑ k : Fin 6, (bourgainIndex (h k) : ℝ) ^ (2 : ℕ)) ≤
          ∑ _k : Fin 6, (H : ℝ) ^ (2 : ℕ) := by
        apply Finset.sum_le_sum
        intro k hk
        exact pow_le_pow_left₀ (by positivity)
          (bourgainIndex_real_le (h k)) 2
      _ = 6 * (H : ℝ) ^ (2 : ℕ) := by norm_num
  · simp only [bourgainMomentCurve, bourgainMomentCoordinateBound]
    calc
      (∑ k : Fin 6, (bourgainIndex (h k) : ℝ) ^ (3 / 2 : ℝ)) ≤
          ∑ _k : Fin 6, (H : ℝ) ^ (3 / 2 : ℝ) := by
        apply Finset.sum_le_sum
        intro k hk
        exact Real.rpow_le_rpow (by positivity)
          (bourgainIndex_real_le (h k)) (by norm_num)
      _ = 6 * (H : ℝ) ^ (3 / 2 : ℝ) := by norm_num
  · simp only [bourgainMomentCurve, bourgainMomentCoordinateBound]
    calc
      (∑ k : Fin 6, (bourgainIndex (h k) : ℝ) ^ (1 / 2 : ℝ)) ≤
          ∑ _k : Fin 6, (H : ℝ) ^ (1 / 2 : ℝ) := by
        apply Finset.sum_le_sum
        intro k hk
        exact Real.rpow_le_rpow (by positivity)
          (bourgainIndex_real_le (h k)) (by norm_num)
      _ = 6 * (H : ℝ) ^ (1 / 2 : ℝ) := by norm_num

theorem abs_bourgainSixfoldMoment_le_coordinateBound
    {H : ℕ} (h : Fin 6 → Fin H) (j : Fin 4) :
    |bourgainSixfoldMoment h j| ≤ bourgainMomentCoordinateBound H j := by
  rw [abs_of_nonneg (bourgainSixfoldMoment_nonneg h j)]
  exact bourgainSixfoldMoment_le_coordinateBound h j

theorem bourgainMomentCoordinateBound_pos
    {H : ℕ} (hH : 0 < H) :
    ∀ j, 0 < bourgainMomentCoordinateBound H j := by
  intro j
  fin_cases j <;> simp [bourgainMomentCoordinateBound] <;> positivity

/-- Equation (3.7)--(3.9) with the six-fold cloud bounds discharged. -/
theorem bourgainDoubleLargeSieve_shortCurveSum_coordinateBound
    {ι : Type*} [Fintype ι]
    {H : ℕ} {X : BourgainPhaseSpace}
    (α : Fin H → ℂ) (x : ι → BourgainPhaseSpace)
    (hH : 0 < H) (hX : ∀ j, 0 < X j)
    (hx : ∀ q j, |x q j| ≤ X j)
    (hα : ∀ h, ‖α h‖ ≤ 1) :
    (∑ i : ι, ‖bourgainShortCurveSum H α (x i)‖) ^ (12 : ℕ) ≤
      (Fintype.card ι : ℝ) ^ (10 : ℕ) *
        (((Real.exp (4 * Real.pi) * 331776) *
          (∏ j : Fin 4,
            (Real.pi ^ (2 : ℕ) *
              (1 + X j * bourgainMomentCoordinateBound H j)))) *
        ((bourgainScaledNearCount
            (bourgainMomentCoordinateBound H) x : ℝ) *
          (bourgainFirstSpacingCount H X : ℝ))) := by
  exact bourgainDoubleLargeSieve_shortCurveSum α x hX
    (bourgainMomentCoordinateBound_pos hH) hx
    abs_bourgainSixfoldMoment_le_coordinateBound hα

end

end RHTower
