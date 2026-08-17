import GaloisForLFunctions.HTGeometry.PowerSeriesDiscBridge
import GaloisForLFunctions.HTGeometry.HelsonZetaAnalytic

/-!
# Certificates for meromorphic continuation of a Helson zeta function to a disc

A meromorphic continuation of `Z(χ, ·)` to the disc of radius `ρ` about `s = 2` is the same thing as

* a finite list of admissible pole positions `u`, giving the monic polynomial `∏ (w - u i)`, and
* a coefficient sequence `c` with `‖c n‖ ρ ^ n` bounded,

such that the polynomial times the zeta function is the sum of the series on the part of the disc
where the Euler product converges.  The pole positions are constrained to the closed half plane
`Re s ≤ 1`, which costs nothing because a continuation agrees with the Euler product — hence is
holomorphic — on `Re s > 1`.

The point of this encoding is that both parameters range over *compact* sets: a closed polydisc of
root positions, and a product of closed balls of coefficients.
-/

open Complex Filter Topology

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- The radius of the disc used at level `N`. -/
def levelRadius (N : ℕ) : ℝ := (N : ℝ) + 3

theorem levelRadius_pos (N : ℕ) : 0 < levelRadius N := by
  have : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  simp only [levelRadius]
  linarith

theorem one_lt_levelRadius (N : ℕ) : 1 < levelRadius N := by
  have : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  simp only [levelRadius]
  linarith

/-- The monic polynomial with the prescribed roots. -/
def rootPoly {d : ℕ} (u : Fin d → ℂ) (w : ℂ) : ℂ := ∏ i, (w - u i)

@[simp] theorem rootPoly_empty (u : Fin 0 → ℂ) (w : ℂ) : rootPoly u w = 1 := by
  simp [rootPoly]

/-- The admissible pole positions at level `N`, in the coordinate `w = s - 2`. -/
def rootBox (N : ℕ) : Set ℂ := {u : ℂ | ‖u‖ ≤ levelRadius N + 1 ∧ u.re ≤ -1}

theorem isCompact_rootBox (N : ℕ) : IsCompact (rootBox N) := by
  have hclosed : IsClosed (rootBox N) := by
    have h1 : IsClosed {u : ℂ | ‖u‖ ≤ levelRadius N + 1} :=
      isClosed_le continuous_norm continuous_const
    have h2 : IsClosed {u : ℂ | u.re ≤ -1} :=
      isClosed_le Complex.continuous_re continuous_const
    exact h1.inter h2
  refine (Metric.isCompact_of_isClosed_isBounded hclosed ?_)
  refine (Metric.isBounded_iff_subset_closedBall 0).2 ⟨levelRadius N + 1, ?_⟩
  intro u hu
  simpa [Metric.mem_closedBall, dist_eq_norm] using hu.1

/-- A polynomial with all roots in the left half plane does not vanish to the right of it. -/
theorem rootPoly_ne_zero_of_mem_rootBox {N d : ℕ} {u : Fin d → ℂ}
    (hu : ∀ i, u i ∈ rootBox N) {w : ℂ} (hw : -1 < w.re) : rootPoly u w ≠ 0 := by
  refine Finset.prod_ne_zero_iff.2 fun i _ => ?_
  intro h
  have : w = u i := by
    have := sub_eq_zero.mp h
    exact this
  rw [this] at hw
  exact absurd (hu i).2 (not_le.2 hw)

/-- The certificate of continuation to the disc of level `N`. -/
def LevelData (χ : PhaseTorus) (N B : ℕ) {d : ℕ} (u : Fin d → ℂ) (c : ℕ → ℂ) : Prop :=
  (∀ i, u i ∈ rootBox N) ∧ (∀ n, ‖c n‖ * levelRadius N ^ n ≤ (B : ℝ)) ∧
    ∀ s : ℂ, ‖s - 2‖ < levelRadius N → 1 < s.re →
      rootPoly u (s - 2) * helsonZetaValue s χ = seriesSum c (s - 2)

/-- A phase satisfies the continuation criterion when every level carries a certificate. -/
def ContinuationCriterion (χ : PhaseTorus) : Prop :=
  ∀ N : ℕ, ∃ (B d : ℕ) (u : Fin d → ℂ) (c : ℕ → ℂ), LevelData χ N B u c

/-- The series of a level certificate is holomorphic on the disc of that level. -/
theorem analyticOnNhd_seriesSum_of_levelData {N B : ℕ} {c : ℕ → ℂ}
    (hc : ∀ n, ‖c n‖ * levelRadius N ^ n ≤ (B : ℝ)) :
    AnalyticOnNhd ℂ (seriesSum c) (Metric.ball 0 (levelRadius N)) :=
  analyticOnNhd_seriesSum (levelRadius_pos N) hc

/-- Listing a finite family of points with multiplicities as a vector of roots. -/
theorem exists_root_vector (S : Finset ℂ) (m : ℂ → ℕ) :
    ∃ (d : ℕ) (u : Fin d → ℂ), (∀ i, u i ∈ S) ∧
      ∀ w : ℂ, rootPoly u w = ∏ z ∈ S, (w - z) ^ m z := by
  classical
  induction S using Finset.induction with
  | empty => exact ⟨0, fun i => i.elim0, fun i => i.elim0, fun w => by simp [rootPoly]⟩
  | insert z S hz ih =>
      obtain ⟨d, u, hmem, hprod⟩ := ih
      refine ⟨d + m z, Fin.append u (fun _ : Fin (m z) => z), ?_, ?_⟩
      · refine Fin.addCases (fun j => ?_) (fun j => ?_)
        · rw [Fin.append_left]
          exact Finset.mem_insert_of_mem (hmem j)
        · rw [Fin.append_right]
          exact Finset.mem_insert_self _ _
      · intro w
        rw [rootPoly, Fin.prod_univ_add]
        have h1 : ∏ i : Fin d, (w - Fin.append u (fun _ : Fin (m z) => z) (Fin.castAdd (m z) i))
            = rootPoly u w := by
          refine Finset.prod_congr rfl fun i _ => ?_
          rw [Fin.append_left]
        have h2 : ∏ i : Fin (m z), (w - Fin.append u (fun _ : Fin (m z) => z) (Fin.natAdd d i))
            = (w - z) ^ m z := by
          rw [Finset.prod_congr rfl fun i (_ : i ∈ Finset.univ) => by
            rw [Fin.append_right]]
          simp
        rw [h1, h2, hprod w, Finset.prod_insert hz]
        ring

end GaloisForLFunctions.HTGeometry

end
