/-
# Completed-time density of the complete circuit union

Composing the completed-time capture-density bound with the replica-order counting inequality gives
the physical-time statement the static-local complexity laws consume: for a Hamiltonian with
maximally projective spectrum and a bounded input collision, the long-time density of the times at
which the evolved state is within capture threshold of *some* member of a depth-`s` circuit
dictionary is at most `2^{-r/2}`.

Main results:
* `replicaMoment_le_two_rpow` — the counting chain `h_r · r! · (16C/a²)^r ≤ |Z| 2^{-r} ≤ 2^{-r/2}`.
* `limsup_completedTime_capture_le_two_rpow` — **the completed-time circuit bound**.
-/
import GaloisForLFunctions.HTGeometry.SpectralOrbitCaptureDensity
import GaloisForLFunctions.HTGeometry.CircuitCountingCollisionBound

open MeasureTheory Complex UnitAddTorus Set Filter

noncomputable section

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

variable {I : Type*} [Fintype I] [DecidableEq I]
variable {C : Type*} [Fintype C] [Nonempty C]

/-- **The counting chain.**  At a replica order below the reciprocal collision scale, and with a
dictionary whose logarithm is below half that order, the replica moment is at most `2^{-r/2}`. -/
theorem replicaMoment_le_two_rpow {p : I → ℝ} {a : ℝ} (ha : 0 < a) (z : C → (I → ℂ))
    {r : ℕ} (hr : 1 ≤ r) {c₀ : ℝ}
    (hcoll : occupationCollision p ≤ c₀)
    (hscale : 16 * c₀ / a ^ 2 ≤ 1 / (2 * r))
    {M : ℝ} (hM : 1 < M) {s : ℕ} (hcard : (Fintype.card C : ℝ) ≤ M ^ (s + 1))
    (hs : ((s : ℝ) + 1) * Real.log M ≤ ((r : ℝ) / 2) * Real.log 2) :
    (Module.finrank ℂ (replicaTargetSpan r z) : ℝ) * (r.factorial : ℝ) *
        (16 * occupationCollision p / a ^ 2) ^ r
      ≤ (2 : ℝ) ^ (-((r : ℝ) / 2)) := by
  have hcoll0 : 0 ≤ occupationCollision p :=
    Finset.sum_nonneg fun j _ => by positivity
  have hx0 : (0 : ℝ) ≤ 16 * occupationCollision p / a ^ 2 := by positivity
  have hxle : 16 * occupationCollision p / a ^ 2 ≤ 1 / (2 * r) := by
    refine le_trans ?_ hscale
    have : 16 * occupationCollision p ≤ 16 * c₀ := by linarith
    exact div_le_div_of_nonneg_right this (by positivity)
  have hkey : (r.factorial : ℝ) * (16 * occupationCollision p / a ^ 2) ^ r ≤ (1 / 2 : ℝ) ^ r :=
    factorial_mul_pow_le_two_pow_neg r hr hx0 hxle
  have hrank : (Module.finrank ℂ (replicaTargetSpan r z) : ℝ) ≤ (Fintype.card C : ℝ) := by
    exact_mod_cast finrank_replicaTargetSpan_le_card r z
  have hnn : (0 : ℝ) ≤ (Module.finrank ℂ (replicaTargetSpan r z) : ℝ) := by positivity
  calc (Module.finrank ℂ (replicaTargetSpan r z) : ℝ) * (r.factorial : ℝ) *
        (16 * occupationCollision p / a ^ 2) ^ r
      = (Module.finrank ℂ (replicaTargetSpan r z) : ℝ) *
        ((r.factorial : ℝ) * (16 * occupationCollision p / a ^ 2) ^ r) := by ring
    _ ≤ (Module.finrank ℂ (replicaTargetSpan r z) : ℝ) * (1 / 2 : ℝ) ^ r :=
        mul_le_mul_of_nonneg_left hkey hnn
    _ ≤ (Fintype.card C : ℝ) * (1 / 2 : ℝ) ^ r :=
        mul_le_mul_of_nonneg_right hrank (by positivity)
    _ ≤ (2 : ℝ) ^ (-((r : ℝ) / 2)) := card_mul_two_pow_le_rpow (by positivity) hM hcard hs

/-- **The completed-time circuit bound.**  Under a maximally projective spectrum, a bounded input
collision and a dictionary below the replica order, the long-time density of the times at which the
evolution is captured by the dictionary is at most `2^{-r/2}`. -/
theorem limsup_completedTime_capture_le_two_rpow
    (lam : I → ℝ) (hmax : MaximallyProjectiveEnergy lam) (ref : I)
    (c : I → ℂ) (hcsum : ∑ j, ‖c j‖ ^ 2 ≤ 1) {a : ℝ} (ha : 0 < a)
    (z : C → (I → ℂ)) (hz : ∀ κ, finiteComplexInner (z κ) (z κ) = 1)
    (hznorm : ∀ κ, ∑ j, ‖z κ j‖ ^ 2 ≤ 1)
    {r : ℕ} (hr : 1 ≤ r) {c₀ : ℝ}
    (hcoll : occupationCollision (fun j => ‖c j‖ ^ 2) ≤ c₀)
    (hscale : 16 * c₀ / a ^ 2 ≤ 1 / (2 * r))
    {M : ℝ} (hM : 1 < M) {s : ℕ} (hcard : (Fintype.card C : ℝ) ≤ M ^ (s + 1))
    (hs : ((s : ℝ) + 1) * Real.log M ≤ ((r : ℝ) / 2) * Real.log 2) :
    atTop.limsup (fun T => (finiteTorusPhaseProbabilityMeasure
        (projectiveFrequency (fun i => -lam i) ref) T :
        Measure (UnitAddTorus {i : I // i ≠ ref})) (projectiveAmpCaptureTarget ref c a z))
      ≤ ENNReal.ofReal ((2 : ℝ) ^ (-((r : ℝ) / 2))) := by
  refine le_trans (limsup_finiteTorusPhaseProbabilityMeasure_evolutionCapture_le lam hmax ref c
    hcsum ha z hz hznorm r) ?_
  refine ENNReal.ofReal_le_ofReal ?_
  exact replicaMoment_le_two_rpow ha z hr hcoll hscale hM hcard hs

end GaloisForLFunctions.HTGeometry

end
