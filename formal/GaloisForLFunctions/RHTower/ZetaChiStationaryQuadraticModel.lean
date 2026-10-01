import GaloisForLFunctions.RHTower.ZetaChiCoherentPhaseModel
import GaloisForLFunctions.RHTower.ChiStationaryQuadraticError

open Complex
noncomputable section
namespace RHTower

private theorem bourgainOscillation_add_eq (x y : ℝ) :
    bourgainOscillation (x + y) = bourgainOscillation x * bourgainOscillation y := by
  unfold bourgainOscillation
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- One common unit controls both the global conductor entropy model and
its local quadratic saddle model. The shared unit permits their integrals
to be combined without losing the common orientation. -/
theorem exists_zetaChi_stationary_phase_models :
    ∃ κ : ℂ, ‖κ‖ = 1 ∧
      (∀ a : ℝ, 0 < a → ∀ t : ℝ, 4 ≤ t →
        ‖zetaChi (linePt t) * bourgainOscillation (t * Real.log (a / (2 * Real.pi))) -
          κ * bourgainOscillation (t - t * Real.log (t / a))‖ ≤ 26 / t) ∧
      (∀ a : ℝ, 0 < a → ∀ t : ℝ, 4 ≤ t → |t - a| ≤ a / 2 →
        ‖zetaChi (linePt t) * bourgainOscillation (t * Real.log (a / (2 * Real.pi))) -
          κ * bourgainOscillation (a - (t - a) ^ 2 / (2 * a))‖ ≤
            26 / t + 2 * |t - a| ^ 3 / a ^ 2) := by
  obtain ⟨κ, hκ, hm⟩ := exists_zetaChi_coherent_integerGrade_model
  have hglobal : ∀ a : ℝ, 0 < a → ∀ t : ℝ, 4 ≤ t →
      ‖zetaChi (linePt t) * bourgainOscillation (t * Real.log (a / (2 * Real.pi))) -
        κ * bourgainOscillation (t - t * Real.log (t / a))‖ ≤ 26 / t := by
    intro a ha t ht
    have ht0 : 0 < t := by linarith
    have hp : 0 < 2 * Real.pi := by positivity
    let p : ℝ := t - t * Real.log (t / (2 * Real.pi))
    let v : ℝ := t * Real.log (a / (2 * Real.pi))
    have hphase : p + v = t - t * Real.log (t / a) := by
      dsimp only [p, v]
      rw [Real.log_div ht0.ne' hp.ne', Real.log_div ha.ne' hp.ne', Real.log_div ht0.ne' ha.ne']
      ring
    have hb : ‖zetaChi (linePt t) - κ * bourgainOscillation p‖ ≤ 26 / t := by
      have h := hm 1 t ht
      simp only [Int.cast_one, zpow_one, one_mul, abs_one, mul_one] at h
      have he : Complex.exp ((p : ℂ) * I) = bourgainOscillation p := by
        unfold bourgainOscillation
        congr 1
        ring
      rw [show t - t * Real.log (t / (2 * Real.pi)) = p from rfl, he] at h
      exact h
    change ‖zetaChi (linePt t) * bourgainOscillation v -
      κ * bourgainOscillation (t - t * Real.log (t / a))‖ ≤ 26 / t
    rw [← hphase, bourgainOscillation_add_eq, ← mul_assoc, ← sub_mul,
      norm_mul, norm_bourgainOscillation, mul_one]
    exact hb
  refine ⟨κ, hκ, hglobal, ?_⟩
  intro a ha t ht hta
  let v : ℝ := t * Real.log (a / (2 * Real.pi))
  let P : ℝ := t - t * Real.log (t / a)
  let Q : ℝ := a - (t - a) ^ 2 / (2 * a)
  have hfirst := hglobal a ha t ht
  have hsecond : ‖κ * bourgainOscillation P - κ * bourgainOscillation Q‖ ≤
      2 * |t - a| ^ 3 / a ^ 2 := by
    rw [← mul_sub, norm_mul, hκ, one_mul]
    apply (norm_bourgainOscillation_sub_le _ _).trans
    have he : P - Q = -(t * Real.log (t / a) - t + a - (t - a) ^ 2 / (2 * a)) := by
      dsimp only [P, Q]
      ring
    rw [he, abs_neg]
    exact abs_stationary_entropy_sub_quadratic_le ha hta
  calc
    _ = ‖(zetaChi (linePt t) * bourgainOscillation v - κ * bourgainOscillation P) +
        (κ * bourgainOscillation P - κ * bourgainOscillation Q)‖ := by
      congr 1
      dsimp only [v, Q]
      ring
    _ ≤ ‖zetaChi (linePt t) * bourgainOscillation v - κ * bourgainOscillation P‖ +
        ‖κ * bourgainOscillation P - κ * bourgainOscillation Q‖ := norm_add_le _ _
    _ ≤ _ := add_le_add hfirst hsecond

end RHTower
