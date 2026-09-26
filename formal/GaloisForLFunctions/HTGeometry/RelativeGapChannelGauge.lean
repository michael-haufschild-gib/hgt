import GaloisForLFunctions.HTGeometry.ResponseDeploymentCovariance
import GaloisForLFunctions.HTGeometry.RelativeGapCurvature

/-!
# Channel exposure and block-origin laws

Channel totals respond to common drift in proportion to their exposure. Homogeneous
centering removes that ambiguity, while retaining exact fine-to-coarse conservation.
Block positions rotate under an origin shift, with an endpoint term at the seam.
-/

namespace GaloisForLFunctions.HTGeometry
noncomputable section
open scoped BigOperators

/-- Weighted signal assigned to a single channel. -/
def relativeChannelScore {I C : Type*} [Fintype I] [DecidableEq C]
    (label : I → C) (p f : I → ℝ) (c : C) : ℝ :=
  ∑ i, if label i = c then p i * f i else 0

/-- Exposure of a channel, including signed-weight conventions. -/
def relativeChannelMass {I C : Type*} [Fintype I] [DecidableEq C]
    (label : I → C) (p : I → ℝ) (c : C) : ℝ :=
  relativeChannelScore label p (fun _ => 1) c

/-- Homogeneous centering remains defined for empty or zero-mass channels. -/
def relativeChannelContrast {I C : Type*} [Fintype I] [DecidableEq C]
    (label : I → C) (p f : I → ℝ) (c : C) : ℝ :=
  (∑ i, p i) * relativeChannelScore label p f c -
    relativeChannelMass label p c * ∑ i, p i * f i

theorem relativeChannelScore_add {I C : Type*} [Fintype I] [DecidableEq C]
    (label : I → C) (p f g : I → ℝ) (c : C) :
    relativeChannelScore label p (fun i => f i + g i) c =
      relativeChannelScore label p f c + relativeChannelScore label p g c := by
  unfold relativeChannelScore
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> ring

/-- A common correction moves raw channel totals according to channel mass. -/
theorem relativeChannelScore_add_constant {I C : Type*} [Fintype I] [DecidableEq C]
    (label : I → C) (p f : I → ℝ) (c : C) (a : ℝ) :
    relativeChannelScore label p (fun i => f i + a) c =
      relativeChannelScore label p f c + a * relativeChannelMass label p c := by
  rw [relativeChannelScore_add]
  congr 1
  unfold relativeChannelMass relativeChannelScore
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> ring

/-- Drift may reorder raw channel totals whenever the two exposures differ. -/
theorem relativeChannelScore_difference_drift {I C : Type*} [Fintype I] [DecidableEq C]
    (label : I → C) (p f : I → ℝ) (c d : C) (a : ℝ) :
    relativeChannelScore label p (fun i => f i + a) c -
      relativeChannelScore label p (fun i => f i + a) d =
        relativeChannelScore label p f c - relativeChannelScore label p f d +
          a * (relativeChannelMass label p c - relativeChannelMass label p d) := by
  rw [relativeChannelScore_add_constant, relativeChannelScore_add_constant]
  ring

/-- The canonical contrast is the channel observation of the existing centered response. -/
theorem relativeChannelContrast_eq_centered {I C : Type*} [Fintype I] [DecidableEq C]
    (label : I → C) (p f : I → ℝ) (c : C) :
    relativeChannelContrast label p f c =
      relativeChannelScore label p (responseCenteredSignal p f) c := by
  unfold relativeChannelContrast relativeChannelMass relativeChannelScore responseCenteredSignal
  generalize (∑ i, p i) = M
  generalize (∑ i, p i * f i) = S
  rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> ring

theorem relativeChannelContrast_add_constant {I C : Type*} [Fintype I] [DecidableEq C]
    (label : I → C) (p f : I → ℝ) (c : C) (a : ℝ) :
    relativeChannelContrast label p (fun i => f i + a) c =
      relativeChannelContrast label p f c := by
  unfold relativeChannelContrast
  rw [relativeChannelScore_add_constant]
  simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul]
  ring

theorem sum_relativeChannelScore {I C : Type*} [Fintype I] [Fintype C] [DecidableEq C]
    (label : I → C) (p f : I → ℝ) :
    ∑ c, relativeChannelScore label p f c = ∑ i, p i * f i := by
  unfold relativeChannelScore
  rw [Finset.sum_comm]
  simp

theorem sum_relativeChannelContrast {I C : Type*} [Fintype I] [Fintype C] [DecidableEq C]
    (label : I → C) (p f : I → ℝ) :
    ∑ c, relativeChannelContrast label p f c = 0 := by
  simp_rw [relativeChannelContrast_eq_centered]
  rw [sum_relativeChannelScore, sum_responseCenteredSignal]

/-- Fine channels recover the exact coarse channel without an independence premise. -/
theorem relativeChannelScore_coarsen {I C D : Type*} [Fintype I] [Fintype C]
    [DecidableEq C] [DecidableEq D] (label : I → C) (coarse : C → D)
    (p f : I → ℝ) (d : D) :
    (∑ c, if coarse c = d then relativeChannelScore label p f c else 0) =
      relativeChannelScore (coarse ∘ label) p f d := by
  unfold relativeChannelScore
  have hs (c : C) : (if coarse c = d then
      ∑ i, if label i = c then p i * f i else 0 else 0) =
      ∑ i, if label i = c then (if coarse c = d then p i * f i else 0) else 0 := by
    by_cases hc : coarse c = d <;> simp [hc]
  simp_rw [hs]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp

/-- A phase total samples one position from every block. -/
def relativePhaseTotal (s : ℕ → ℝ) (width count phase : ℕ) : ℝ :=
  ∑ k ∈ Finset.range count, s (width * k + phase)

theorem relativePhaseTotal_shift (s : ℕ → ℝ) (width count phase : ℕ) :
    relativePhaseTotal (fun n => s (n + 1)) width count phase =
      relativePhaseTotal s width count (phase + 1) := by
  simp only [relativePhaseTotal, Nat.add_assoc]

/-- Moving the block origin rotates the final phase into the first, with exact endpoint cost. -/
theorem relativePhaseTotal_shift_seam (s : ℕ → ℝ) (width count : ℕ) :
    relativePhaseTotal (fun n => s (n + 1)) (width + 1) count width =
      relativePhaseTotal s (width + 1) count 0 +
        s ((width + 1) * count) - s 0 := by
  induction count with
  | zero => simp [relativePhaseTotal]
  | succ n ih =>
    simp only [relativePhaseTotal, Finset.sum_range_succ] at ih ⊢
    have he : (width + 1) * n + width + 1 = (width + 1) * (n + 1) := by ring
    simp only [Nat.add_zero, he] at ih ⊢
    linarith

/-- A common block correction cancels from every between-phase contrast. -/
theorem relativePhaseContrast_common_drift
    (x : ℕ → ℕ → ℝ) (drift : ℕ → ℝ) (count i j : ℕ) :
    (∑ k ∈ Finset.range count, (x k i + drift k)) -
      (∑ k ∈ Finset.range count, (x k j + drift k)) =
        (∑ k ∈ Finset.range count, x k i) - (∑ k ∈ Finset.range count, x k j) := by
  simp only [Finset.sum_add_distrib]
  ring

end
end GaloisForLFunctions.HTGeometry
