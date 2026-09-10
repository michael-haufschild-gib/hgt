import GaloisForLFunctions.HTGeometry.FiniteResponseForce
import GaloisForLFunctions.HTGeometry.FiniteProbabilityGiniLayerCake

/-!
# Oriented response thresholds and existing cumulative cuts

The oriented-tail mechanism of Araújo, arXiv:2609.05560, Theorem 11 is applied to the
existing finite strict lower-cut mass. A finite affine-plus-jump response admits an exact
cumulative decomposition. For a specified pairing of source and summary atoms, its
finite-probe distortion differs from the jump discrepancy by at most the affine slope
times the pairing's transport cost. These are identities and bounds for arbitrary signed
weights; probability normalization is unnecessary.
-/
open scoped BigOperators
namespace GaloisForLFunctions.HTGeometry
noncomputable section

/-- A response step remembers whether the atom at the threshold belongs to the upper branch. -/
def orientedResponseStep (closed : Bool) (threshold u : ℝ) : ℝ :=
  if (if closed then threshold ≤ u else threshold < u) then 1 else 0

/-- A closed upper response tail is the complement of the existing strict lower cut. -/
theorem finiteResponseForce_closedStep {ι : Type*} [Fintype ι]
    (w z : ι → ℝ) (threshold x : ℝ) :
    finiteResponseForce (orientedResponseStep true threshold) w z x =
      (∑ i, w i) - _root_.HTGeometry.finiteStrictLowerCutMass w z (x + threshold) := by
  unfold finiteResponseForce _root_.HTGeometry.finiteStrictLowerCutMass
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : z i < x + threshold
  · have ht : ¬ threshold ≤ z i - x := by linarith
    simp [orientedResponseStep, h, ht]
  · have ht : threshold ≤ z i - x := by linarith
    simp [orientedResponseStep, h, ht]

/-- An open upper response tail is a strict lower cut after reflection. -/
theorem finiteResponseForce_openStep {ι : Type*} [Fintype ι]
    (w z : ι → ℝ) (threshold x : ℝ) :
    finiteResponseForce (orientedResponseStep false threshold) w z x =
      _root_.HTGeometry.finiteStrictLowerCutMass w (fun i => -z i) (-(x + threshold)) := by
  unfold finiteResponseForce _root_.HTGeometry.finiteStrictLowerCutMass
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : threshold < z i - x
  · have ht : x + threshold < z i := by linarith
    simp [orientedResponseStep, h, ht]
  · have ht : ¬ x + threshold < z i := by linarith
    simp [orientedResponseStep, h, ht]

/-- The two orientations differ exactly by the atomic mass on the threshold. -/
theorem finiteResponseForce_step_orientation_defect {ι : Type*} [Fintype ι]
    (w z : ι → ℝ) (threshold x : ℝ) :
    finiteResponseForce (orientedResponseStep true threshold) w z x -
      finiteResponseForce (orientedResponseStep false threshold) w z x =
        ∑ i, if z i = x + threshold then w i else 0 := by
  unfold finiteResponseForce
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rcases lt_trichotomy (z i) (x + threshold) with h | h | h
  · have hle : ¬ threshold ≤ z i - x := by linarith
    have hlt : ¬ threshold < z i - x := by linarith
    simp [orientedResponseStep, hle, hlt, h.ne]
  · simp [orientedResponseStep, h]
  · have hlt : threshold < z i - x := by linarith
    simp [orientedResponseStep, hlt, hlt.le, h.ne']

/-- A finite response with affine drift and explicitly oriented jumps. -/
def affineJumpResponse {κ : Type*} [Fintype κ]
    (a b : ℝ) (jump threshold : κ → ℝ) (closed : κ → Bool) (u : ℝ) : ℝ :=
  a * u + b + ∑ k, jump k * orientedResponseStep (closed k) (threshold k) u

/-- The entire jump response factors through the finite family of cumulative cut observables. -/
theorem finiteResponseForce_affineJump {ι κ : Type*} [Fintype ι] [Fintype κ]
    (w z : ι → ℝ) (a b : ℝ) (jump threshold : κ → ℝ) (closed : κ → Bool) (x : ℝ) :
    finiteResponseForce (affineJumpResponse a b jump threshold closed) w z x =
      finiteResponseForce (fun u => a * u + b) w z x +
        ∑ k, jump k * finiteResponseForce (orientedResponseStep (closed k) (threshold k)) w z x := by
  unfold affineJumpResponse
  rw [finiteResponseForce_add]
  congr 1
  unfold finiteResponseForce
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Translating paired atoms changes affine response by the same amount at every recipient. -/
theorem finiteResponseForce_affine_paired_difference {ι : Type*} [Fintype ι]
    (w z t : ι → ℝ) (a b x : ℝ) :
    finiteResponseForce (fun u => a * u + b) w t x -
      finiteResponseForce (fun u => a * u + b) w z x = a * ∑ i, w i * (t i - z i) := by
  unfold finiteResponseForce
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Signed-weight transport cost of an explicit pairing. For probability weights this is
an admissible coupling cost. -/
def finiteResponsePairingCost {ι : Type*} [Fintype ι] (w z t : ι → ℝ) : ℝ :=
  ∑ i, |w i| * |t i - z i|

/-- The first-moment error is bounded by the cost of the specified atomic pairing. -/
theorem finiteResponse_moment_error_le_pairing {ι : Type*} [Fintype ι] (w z t : ι → ℝ) :
    |∑ i, w i * (t i - z i)| ≤ finiteResponsePairingCost w z t := by
  simpa [finiteResponsePairingCost, abs_mul] using
    Finset.abs_sum_le_sum_abs (fun i => w i * (t i - z i)) Finset.univ

/-- Jump discrepancy on a finite panel, with the response's actual endpoint conventions. -/
def finiteJumpDiscrepancy {ι κ : Type*} [Fintype ι] [Fintype κ] {n : ℕ}
    (w z t : ι → ℝ) (jump threshold : κ → ℝ) (closed : κ → Bool)
    (probe : Fin (n + 1) → ℝ) : ℝ :=
  ‖fun j => ∑ k, jump k *
    (finiteResponseForce (orientedResponseStep (closed k) (threshold k)) w t (probe j) -
      finiteResponseForce (orientedResponseStep (closed k) (threshold k)) w z (probe j))‖

/-- The finite-panel sandwich separates threshold error from the exact mean error. -/
theorem finiteResponseDistortion_jump_sandwich {ι κ : Type*} [Fintype ι] [Fintype κ] {n : ℕ}
    (w z t : ι → ℝ) (a b : ℝ) (jump threshold : κ → ℝ) (closed : κ → Bool)
    (probe : Fin (n + 1) → ℝ) :
    |finiteResponseDistortion (affineJumpResponse a b jump threshold closed) w z w t probe -
      finiteJumpDiscrepancy w z t jump threshold closed probe| ≤
        |a| * |∑ i, w i * (t i - z i)| := by
  let A : Fin (n + 1) → ℝ := fun j =>
    finiteResponseForce (affineJumpResponse a b jump threshold closed) w t (probe j) -
      finiteResponseForce (affineJumpResponse a b jump threshold closed) w z (probe j)
  let B : Fin (n + 1) → ℝ := fun j => ∑ k, jump k *
    (finiteResponseForce (orientedResponseStep (closed k) (threshold k)) w t (probe j) -
      finiteResponseForce (orientedResponseStep (closed k) (threshold k)) w z (probe j))
  have hd : A - B = fun _ => a * ∑ i, w i * (t i - z i) := by
    funext j
    simp only [A, B, Pi.sub_apply, finiteResponseForce_affineJump,
      mul_sub, Finset.sum_sub_distrib]
    have h := finiteResponseForce_affine_paired_difference w z t a b (probe j)
    simp only [mul_sub, Finset.sum_sub_distrib] at h
    linarith
  change |‖A‖ - ‖B‖| ≤ _
  calc
    |‖A‖ - ‖B‖| ≤ ‖A - B‖ := abs_norm_sub_norm_le A B
    _ = |a| * |∑ i, w i * (t i - z i)| := by
      rw [hd]
      simp [norm_mul, Real.norm_eq_abs]

/-- A coupling-cost version of the cumulative-discrepancy sandwich needs no moment premise. -/
theorem finiteResponseDistortion_jump_sandwich_transport {ι κ : Type*}
    [Fintype ι] [Fintype κ] {n : ℕ}
    (w z t : ι → ℝ) (a b : ℝ) (jump threshold : κ → ℝ) (closed : κ → Bool)
    (probe : Fin (n + 1) → ℝ) :
    |finiteResponseDistortion (affineJumpResponse a b jump threshold closed) w z w t probe -
      finiteJumpDiscrepancy w z t jump threshold closed probe| ≤
        |a| * finiteResponsePairingCost w z t :=
  (finiteResponseDistortion_jump_sandwich w z t a b jump threshold closed probe).trans
    (mul_le_mul_of_nonneg_left (finiteResponse_moment_error_le_pairing w z t) (abs_nonneg a))

end
end GaloisForLFunctions.HTGeometry
