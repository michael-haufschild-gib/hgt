/-
# The collision moments of the cubic-phase ensemble

The evaluation vector of a uniformly sampled cubic phase polynomial is uniform on any fifteen
register points, so every character of support at most fifteen averages to zero over the ensemble
exactly as it does over the phase box.  The collision is a character sum on four points and its
square one on eight, so both moments of the finite cubic-phase ensemble are the continuous
Steinhaus moments.

Main results:
* `cubicEval` — the evaluation map of a cubic phase polynomial.
* `eighthPhaseUniform_cubicEval` — **the ensemble kills every character of support `≤ 15`**.
* `average_phaseCollision_polyEval_eq_integral`, `average_phaseCollision_sq_polyEval_eq_integral` —
  **both collision moments transfer**.
-/
import GaloisForLFunctions.HTGeometry.PhaseCollisionTrigForm
import GaloisForLFunctions.HTGeometry.EighthRootTrigTransfer
import GaloisForLFunctions.HTGeometry.CubicPhaseEvaluationUniformity

open Finset MeasureTheory Matrix

noncomputable section

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The evaluation of a degree-`≤ m` phase polynomial at a register point. -/
def polyEval (m : ℕ) (c : MonLe ι m → ZMod 8) (a : ι → Bool) : ZMod 8 :=
  ∑ S, (if ∀ i ∈ S.1, a i = true then (1 : ZMod 8) else 0) * c S

theorem mulVec_reedMullerEvalMatrix_apply {m k : ℕ} (pts : Fin k → (ι → Bool))
    (c : MonLe ι m → ZMod 8) (i : Fin k) :
    (reedMullerEvalMatrix (ZMod 8) m pts *ᵥ c) i = polyEval m c (pts i) := rfl

/-- **The cubic-phase ensemble kills every character of support at most fifteen.** -/
theorem eighthPhaseUniform_polyEval (m : ℕ) :
    EighthPhaseUniform (α := ι → Bool) (polyEval m) (2 ^ (m + 1) - 1) := by
  classical
  refine eighthPhaseUniform_of_tupleUniform _ _ ?_
  intro k hk pts hinj w
  have hklt : k < 2 ^ (m + 1) := by
    have hpos : 0 < 2 ^ (m + 1) := Nat.two_pow_pos _
    omega
  have hset : (Finset.univ.filter fun c : MonLe ι m → ZMod 8 =>
        (fun i => polyEval m c (pts i)) = w)
      = Finset.univ.filter fun c : MonLe ι m → ZMod 8 =>
        (reedMullerEvalMatrix (ZMod 8) m pts) *ᵥ c = w := by
    refine Finset.filter_congr fun c _ => ?_
    constructor
    · intro h
      funext i
      rw [mulVec_reedMullerEvalMatrix_apply]
      exact congrFun h i
    · intro h
      funext i
      rw [← mulVec_reedMullerEvalMatrix_apply]
      exact congrFun h i
  rw [hset]
  exact card_fiber_evalMatrix_mul_card_eq hklt pts hinj w

/-! ## Transfer of the two collision moments -/

variable {κ : Type*} [Fintype κ]

theorem average_phaseCollision_polyEval_eq_integral (m : ℕ)
    (hm : 4 ≤ 2 ^ (m + 1) - 1) (e : κ → (ι → Bool) → ℂ) :
    ((Fintype.card (MonLe ι m → ZMod 8) : ℝ))⁻¹ *
        ∑ c : MonLe ι m → ZMod 8, phaseCollision e (eighthPhase (polyEval m c))
      = ∫ x in torusBox (ι → Bool), phaseCollision e x := by
  classical
  haveI : Nonempty (MonLe ι m → ZMod 8) := ⟨fun _ => 0⟩
  have hcomplex : ((Fintype.card (MonLe ι m → ZMod 8) : ℂ))⁻¹ *
      ∑ c : MonLe ι m → ZMod 8,
        ((phaseCollision e (eighthPhase (polyEval m c)) : ℝ) : ℂ)
      = ∫ x in torusBox (ι → Bool), ((phaseCollision e x : ℝ) : ℂ) := by
    rw [Finset.sum_congr rfl (fun c _ => phaseCollision_eq_trigLift e (eighthPhase (polyEval m c)))]
    rw [average_trigLift_eighthPhase_eq_integral_box (polyEval m) (eighthPhaseUniform_polyEval m)
      _ _ _ (fun q _ => le_trans (card_freqSupport_collisionFreq_le q) hm)
      (fun q _ hq => exists_collisionFreq_ne_zero_mod_eight hq)]
    refine setIntegral_congr_fun measurableSet_torusBox fun x _ => ?_
    exact (phaseCollision_eq_trigLift e x).symm
  have hint : ∫ x in torusBox (ι → Bool), ((phaseCollision e x : ℝ) : ℂ)
      = ((∫ x in torusBox (ι → Bool), phaseCollision e x : ℝ) : ℂ) := integral_ofReal
  rw [hint] at hcomplex
  refine Complex.ofReal_injective ?_
  push_cast
  exact hcomplex

theorem average_phaseCollision_sq_polyEval_eq_integral (m : ℕ)
    (hm : 8 ≤ 2 ^ (m + 1) - 1) (e : κ → (ι → Bool) → ℂ) :
    ((Fintype.card (MonLe ι m → ZMod 8) : ℝ))⁻¹ *
        ∑ c : MonLe ι m → ZMod 8, phaseCollision e (eighthPhase (polyEval m c)) ^ (2 : ℕ)
      = ∫ x in torusBox (ι → Bool), phaseCollision e x ^ (2 : ℕ) := by
  classical
  haveI : Nonempty (MonLe ι m → ZMod 8) := ⟨fun _ => 0⟩
  have hcomplex : ((Fintype.card (MonLe ι m → ZMod 8) : ℂ))⁻¹ *
      ∑ c : MonLe ι m → ZMod 8,
        ((phaseCollision e (eighthPhase (polyEval m c)) ^ (2 : ℕ) : ℝ) : ℂ)
      = ∫ x in torusBox (ι → Bool), ((phaseCollision e x ^ (2 : ℕ) : ℝ) : ℂ) := by
    rw [Finset.sum_congr rfl
      (fun c _ => phaseCollision_sq_eq_trigLift_fin8 e (eighthPhase (polyEval m c)))]
    rw [average_trigLift_eighthPhase_eq_integral_box (polyEval m) (eighthPhaseUniform_polyEval m)
      _ _ _ (fun r _ => le_trans (card_freqSupport_sqFreq_le r) hm)
      (fun r _ hr => exists_sqFreq_ne_zero_mod_eight hr)]
    refine setIntegral_congr_fun measurableSet_torusBox fun x _ => ?_
    exact (phaseCollision_sq_eq_trigLift_fin8 e x).symm
  have hint : ∫ x in torusBox (ι → Bool), ((phaseCollision e x ^ (2 : ℕ) : ℝ) : ℂ)
      = ((∫ x in torusBox (ι → Bool), phaseCollision e x ^ (2 : ℕ) : ℝ) : ℂ) := integral_ofReal
  rw [hint] at hcomplex
  refine Complex.ofReal_injective ?_
  push_cast
  exact_mod_cast hcomplex

end GaloisForLFunctions.HTGeometry

end
