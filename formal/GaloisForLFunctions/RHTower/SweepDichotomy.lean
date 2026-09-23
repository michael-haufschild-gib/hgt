/-
Doc 48 §2 (task #130): the collision dichotomy, machine-checked halves.

Near an FE-real conjugate pair, the cofactor-normalized carrier on the central
line is `W v = v² + η² + ε·q v` with `q` real; the sweep of the pair by one
entering term is decided by the single real number `ε·q 0`:

* kill half — `ε·q 0 ≤ -η²` gives `W 0 ≤ 0`, and positive edge values force a
  real zero on each side of `0` (the pair lands ON the line);
* survive half — `-η² < ε·q v` on the whole real segment keeps `W` positive
  there (no on-line zeros; the pair stays off-line).

The complex Rouché count that makes the kill half exhaustive is a per-instance
hypothesis discharged by the banked Peeling machinery.
-/
import Mathlib

namespace RHTower

/-- The cofactor-normalized carrier of doc 48 §2. -/
def sweepW (η ε : ℝ) (q : ℝ → ℝ) (v : ℝ) : ℝ := v ^ (2 : ℕ) + η ^ (2 : ℕ) + ε * q v

theorem sweepW_center (η ε : ℝ) (q : ℝ → ℝ) :
    sweepW η ε q 0 = η ^ (2 : ℕ) + ε * q 0 := by
  simp [sweepW]

/-- **Kill half (doc 48 §2(a))**: nonpositive center value and positive edges
force an on-line zero on each side. -/
theorem sweep_kill_exists_zeros {W : ℝ → ℝ} {w : ℝ} (hw : 0 < w)
    (hcont : ContinuousOn W (Set.Icc (-w) w))
    (hcenter : W 0 ≤ 0) (hleft : 0 < W (-w)) (hright : 0 < W w) :
    (∃ a ∈ Set.Icc (-w) 0, W a = 0) ∧ ∃ b ∈ Set.Icc 0 w, W b = 0 := by
  constructor
  · have hsub : Set.Icc (-w) (0 : ℝ) ⊆ Set.Icc (-w) w :=
      Set.Icc_subset_Icc le_rfl hw.le
    have h0 : (0 : ℝ) ∈ Set.Icc (W 0) (W (-w)) := ⟨hcenter, hleft.le⟩
    have := intermediate_value_Icc' (by linarith : (-w : ℝ) ≤ 0)
      (hcont.mono hsub) h0
    obtain ⟨a, ha, hWa⟩ := this
    exact ⟨a, ha, hWa⟩
  · have hsub : Set.Icc (0 : ℝ) w ⊆ Set.Icc (-w) w :=
      Set.Icc_subset_Icc (by linarith) le_rfl
    have h0 : (0 : ℝ) ∈ Set.Icc (W 0) (W w) := ⟨hcenter, hright.le⟩
    have := intermediate_value_Icc (by linarith : (0 : ℝ) ≤ w)
      (hcont.mono hsub) h0
    obtain ⟨b, hb, hWb⟩ := this
    exact ⟨b, hb, hWb⟩

/-- The kill condition of doc 48 in `sweepW` form. -/
theorem sweepW_kill {η ε w : ℝ} {q : ℝ → ℝ} (hw : 0 < w)
    (hq : ContinuousOn q (Set.Icc (-w) w))
    (hkill : ε * q 0 ≤ -η ^ (2 : ℕ))
    (hleft : 0 < sweepW η ε q (-w)) (hright : 0 < sweepW η ε q w) :
    (∃ a ∈ Set.Icc (-w) 0, sweepW η ε q a = 0) ∧
      ∃ b ∈ Set.Icc 0 w, sweepW η ε q b = 0 := by
  apply sweep_kill_exists_zeros hw
  · unfold sweepW
    apply ContinuousOn.add
    · fun_prop
    · exact (continuousOn_const.mul hq)
  · rw [sweepW_center]; linarith
  · exact hleft
  · exact hright

/-- **Survive half (doc 48 §2(b))**: a strict lower bound on the perturbation
along the segment forbids on-line zeros — the pair stays off the line. -/
theorem sweepW_survive {η ε w : ℝ} {q : ℝ → ℝ}
    (hsurv : ∀ v ∈ Set.Icc (-w) w, -η ^ (2 : ℕ) < ε * q v) :
    ∀ v ∈ Set.Icc (-w) w, 0 < sweepW η ε q v := by
  intro v hv
  have := hsurv v hv
  have hv2 : 0 ≤ v ^ (2 : ℕ) := sq_nonneg v
  unfold sweepW
  linarith

/-- No on-line zeros in the survive regime. -/
theorem sweepW_survive_ne_zero {η ε w : ℝ} {q : ℝ → ℝ}
    (hsurv : ∀ v ∈ Set.Icc (-w) w, -η ^ (2 : ℕ) < ε * q v) :
    ∀ v ∈ Set.Icc (-w) w, sweepW η ε q v ≠ 0 :=
  fun v hv => (sweepW_survive hsurv v hv).ne'

end RHTower
