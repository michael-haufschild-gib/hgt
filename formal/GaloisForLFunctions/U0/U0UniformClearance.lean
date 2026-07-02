/-
# Uniform clearance from viability — the bridge to the m-step window branch

The load-bearing lemma of the m-step program: if the filled Julia set `K_b` avoids the closed
unit disk (viability), then a whole disk `D̄(0,r)` with `r > 1` — one that crosses the
natural-boundary circle `|z| = 1` of `u₀` — escapes past the escape fixed point `xStar ‖b‖` in a
UNIFORM number of steps `N`.  This replaces the single-step clearance `quadB_mem_farB` (which
needed `‖b‖ > 2+√2`) by an `N`-step clearance available for EVERY viable parameter, so the window
branch can be pulled back `N` steps onto the far field where the Böttcher series converges.

Proof: pointwise escape (`Bottcher.exists_orbit_gt`) puts each disk point past `xStar` at some
step; persistence of the far field (`farB_iterate`) makes the escape sets `Aₙ = {z : f^[n] z ∈
farB}` increasing and open; compactness of `D̄(0,1)` collapses the cover to a single `A_{N₀}`;
openness fattens it to `D̄(0,r)` with `r > 1` (`exists_thickening_subset_open`).
-/
import GaloisForLFunctions.U0.U0PhiLargeWindow
import GaloisForLFunctions.U0.U0MonotoneEscape

open Complex Set Bottcher Metric
open U0MonotoneEscape (xStar)
open U0PhiLargeWindow (farB farB_iterate)

namespace U0UniformClearance

/-- **Uniform `N`-step clearance from viability.**  For `2 < ‖b‖`, if the closed unit disk avoids
`K_b`, there is a strictly larger disk `D̄(0,r)` (`r > 1`) all of whose points escape past
`xStar ‖b‖` after a single uniform number of steps `N`. -/
theorem exists_uniform_clearance {b : ℂ} (hb : 2 < ‖b‖)
    (hviab : ∀ z : ℂ, ‖z‖ ≤ 1 → z ∉ filledJulia b) :
    ∃ r : ℝ, 1 < r ∧ ∃ N : ℕ,
      ∀ z : ℂ, ‖z‖ ≤ r → xStar ‖b‖ < ‖(quadratic b)^[N] z‖ := by
  -- escape set at level N
  set A : ℕ → Set ℂ := fun N => {z : ℂ | xStar ‖b‖ < ‖(quadratic b)^[N] z‖} with hA
  have hAopen : ∀ N, IsOpen (A N) := by
    intro N
    have hc : Continuous (fun z : ℂ => ‖(quadratic b)^[N] z‖) :=
      continuous_norm.comp ((continuous_quadratic b).iterate N)
    exact isOpen_lt continuous_const hc
  -- persistence: once past xStar, stays past (farB is forward-invariant)
  have hAmono : ∀ {M N : ℕ}, M ≤ N → A M ⊆ A N := by
    intro M N hMN z hz
    have hfar : (quadratic b)^[M] z ∈ farB b := hz
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hMN
    show xStar ‖b‖ < ‖(quadratic b)^[M + d] z‖
    rw [add_comm, Function.iterate_add_apply]
    exact farB_iterate hb d hfar
  -- cover: every disk point escapes past xStar at some step
  have hcover : closedBall (0 : ℂ) 1 ⊆ ⋃ N, A N := by
    intro z hz
    have hz1 : ‖z‖ ≤ 1 := by simpa [mem_closedBall, dist_zero_right] using hz
    obtain ⟨N, hN⟩ := exists_orbit_gt (hviab z hz1) (xStar ‖b‖)
    exact mem_iUnion.mpr ⟨N, hN⟩
  obtain ⟨t, ht⟩ := (isCompact_closedBall (0 : ℂ) 1).elim_finite_subcover A hAopen hcover
  -- collapse the finite subcover to a single level N₀ = sup t
  have hsub : closedBall (0 : ℂ) 1 ⊆ A (t.sup id) := by
    intro z hz
    obtain ⟨i, hit, hzi⟩ := mem_iUnion₂.mp (ht hz)
    exact hAmono (Finset.le_sup (f := id) hit) hzi
  -- fatten the compact ball inside the open set A N₀
  obtain ⟨δ, hδpos, hδ⟩ :=
    (isCompact_closedBall (0 : ℂ) 1).exists_thickening_subset_open (hAopen (t.sup id)) hsub
  refine ⟨1 + δ / 2, by linarith, t.sup id, ?_⟩
  intro z hz
  have hzin : z ∈ thickening δ (closedBall (0 : ℂ) 1) := by
    rw [Metric.mem_thickening_iff]
    by_cases h1 : ‖z‖ ≤ 1
    · exact ⟨z, by simpa [mem_closedBall, dist_zero_right] using h1, by simpa using hδpos⟩
    · push Not at h1
      have hzpos : (0 : ℝ) < ‖z‖ := by linarith
      have hzne : (‖z‖ : ℝ) ≠ 0 := ne_of_gt hzpos
      refine ⟨(‖z‖)⁻¹ • z, ?_, ?_⟩
      · rw [mem_closedBall, dist_zero_right, norm_smul, norm_inv, norm_norm,
          inv_mul_cancel₀ hzne]
      · rw [dist_eq_norm]
        have hcalc : z - (‖z‖)⁻¹ • z = ((1 - (‖z‖)⁻¹ : ℝ)) • z := by
          rw [sub_smul, one_smul]
        rw [hcalc, norm_smul, Real.norm_eq_abs,
          abs_of_nonneg (by rw [sub_nonneg]; exact inv_le_one_of_one_le₀ h1.le)]
        have : (1 - (‖z‖)⁻¹) * ‖z‖ = ‖z‖ - 1 := by
          field_simp
        rw [this]; linarith
  exact hδ hzin

end U0UniformClearance
