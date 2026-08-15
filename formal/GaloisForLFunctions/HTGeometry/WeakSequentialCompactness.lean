import Mathlib.Analysis.Normed.Module.DoubleDual
import Mathlib.Analysis.InnerProductSpace.Dual

/-!
# Sequential weak compactness in separable Hilbert spaces

This module supplies the bounded-sequence extraction needed by closed-form arguments. A
norm-bounded sequence in a separable complex Hilbert space has a weakly convergent subsequence, and
its weak limit obeys the same norm bound. The proof maps vectors into the weak-star dual through
Fréchet–Riesz, applies sequential Banach–Alaoglu, and maps the limit back.
-/

open Complex Filter Topology Set

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [TopologicalSpace.SeparableSpace H]

/-- Every norm-bounded sequence in a separable complex Hilbert space has a weakly convergent
subsequence whose limit satisfies the same bound. -/
theorem exists_weaklyConvergent_subseq_of_bounded
    (u : ℕ → H) (M : ℝ) (hM : ∀ n, ‖u n‖ ≤ M) :
    ∃ w : H, ∃ φ : ℕ → ℕ, StrictMono φ ∧ ‖w‖ ≤ M ∧
      ∀ y : H, Tendsto (fun n => inner ℂ (u (φ n)) y) atTop
        (nhds (inner ℂ w y)) := by
  let d : ℕ → WeakDual ℂ H := fun n =>
    StrongDual.toWeakDual (InnerProductSpace.toDual ℂ H (u n))
  let S : Set (WeakDual ℂ H) :=
    WeakDual.toStrongDual ⁻¹' Metric.closedBall 0 M
  have hd : ∀ n, d n ∈ S := by
    intro n
    change dist (WeakDual.toStrongDual (d n)) 0 ≤ M
    rw [dist_zero_right]
    change ‖InnerProductSpace.toDual ℂ H (u n)‖ ≤ M
    rw [(InnerProductSpace.toDual ℂ H).norm_map]
    exact hM n
  have hfreq : ∃ᶠ n in atTop, d n ∈ S :=
    (Filter.Eventually.of_forall hd).frequently
  obtain ⟨a, ha, φ, hφ, hlim⟩ :=
    (WeakDual.isSeqCompact_closedBall ℂ H 0 M).subseq_of_frequently_in hfreq
  let w : H := (InnerProductSpace.toDual ℂ H).symm
    (WeakDual.toStrongDual a)
  have hw : ‖w‖ ≤ M := by
    have ha' : dist (WeakDual.toStrongDual a) 0 ≤ M := ha
    rw [dist_zero_right] at ha'
    change ‖(InnerProductSpace.toDual ℂ H).symm
      (WeakDual.toStrongDual a)‖ ≤ M
    rwa [(InnerProductSpace.toDual ℂ H).symm.norm_map]
  refine ⟨w, φ, hφ, hw, ?_⟩
  intro y
  have heval := (WeakDual.eval_continuous y).tendsto a |>.comp hlim
  have hwval : inner ℂ w y = a y := by
    change inner ℂ ((InnerProductSpace.toDual ℂ H).symm
      (WeakDual.toStrongDual a)) y = _
    rw [InnerProductSpace.toDual_symm_apply]
    rfl
  rw [hwval]
  convert heval using 1 <;> rfl

end GaloisForLFunctions.HTGeometry
