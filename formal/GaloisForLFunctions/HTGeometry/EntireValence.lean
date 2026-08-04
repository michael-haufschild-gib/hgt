import GaloisForLFunctions.HTGeometry.TranscendentalDenseExterior
import Mathlib.Analysis.Complex.OpenMapping

/-!
# A transcendental entire function has unbounded valence

Every transcendental entire function takes some value at arbitrarily many points, and the set of such
values contains a nonempty open set.

The open set is what the argument needs: an identity between analytic functions which holds at every
value taken often enough then holds everywhere.  Both halves are elementary — the open mapping theorem
makes "taken at `k` points" an open condition, and Casorati–Weierstrass at infinity feeds one new
preimage into the count at each step, taken so far out that it cannot coincide with the earlier ones.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

/-- A transcendental entire function is an open map. -/
theorem isOpenMap_of_transcendental {f : ℂ → ℂ} (hf : TranscendentalEntire f) : IsOpenMap f := by
  have hfan : AnalyticOnNhd ℂ f (Set.univ : Set ℂ) :=
    DifferentiableOn.analyticOnNhd (fun z _ => (hf.1 z).differentiableWithinAt) isOpen_univ
  rcases hfan.is_constant_or_isOpenMap with ⟨w, hw⟩ | hmap
  · exact absurd ⟨Polynomial.C w, fun z => by rw [hw z, Polynomial.eval_C]⟩ hf.2
  · exact hmap

/-- **Unbounded valence, on an open set of values.**  For every `k` there is a nonempty open set of
values each of which is taken at `k` distinct points, all inside a fixed disc. -/
theorem exists_open_many_preimages {f : ℂ → ℂ} (hf : TranscendentalEntire f) (k : ℕ) :
    ∃ (U : Set ℂ) (R : ℝ), IsOpen U ∧ U.Nonempty ∧
      ∀ w ∈ U, ∃ T : Finset ℂ, k ≤ T.card ∧ (∀ t ∈ T, ‖t‖ < R) ∧ ∀ t ∈ T, f t = w := by
  induction k with
  | zero =>
      exact ⟨Set.univ, 1, isOpen_univ, ⟨0, trivial⟩,
        fun w _ => ⟨∅, by simp, by simp, by simp⟩⟩
  | succ k ih =>
      obtain ⟨U, R, hU, ⟨w₀, hw₀⟩, hmany⟩ := ih
      obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hU w₀ hw₀
      obtain ⟨z, hzR, hzc⟩ := exists_norm_gt_and_dist_lt_of_transcendental hf R w₀ hδ
      have hzU : f z ∈ U := by
        refine hball ?_
        simpa [Metric.mem_ball, dist_eq_norm] using hzc
      set r₀ : ℝ := (‖z‖ - R) / 2 with hr₀
      have hr₀0 : 0 < r₀ := by
        rw [hr₀]; linarith
      have hnear : ∀ t : ℂ, t ∈ Metric.ball z r₀ → ‖t - z‖ < r₀ := by
        intro t ht
        simpa [Metric.mem_ball, dist_eq_norm] using ht
      have hupper : ∀ t : ℂ, ‖t‖ ≤ ‖z‖ + ‖t - z‖ := by
        intro t
        have heq : z + (t - z) = t := by ring
        calc ‖t‖ = ‖z + (t - z)‖ := by rw [heq]
          _ ≤ ‖z‖ + ‖t - z‖ := norm_add_le _ _
      have hlower : ∀ t : ℂ, ‖z‖ - ‖t - z‖ ≤ ‖t‖ := by
        intro t
        have := hupper t
        have hrev : ‖z - t‖ = ‖t - z‖ := norm_sub_rev z t
        have h2 : ‖z‖ ≤ ‖t‖ + ‖z - t‖ := by
          have heq : t + (z - t) = z := by ring
          calc ‖z‖ = ‖t + (z - t)‖ := by rw [heq]
            _ ≤ ‖t‖ + ‖z - t‖ := norm_add_le _ _
        rw [hrev] at h2
        linarith
      have hBfar : ∀ t : ℂ, t ∈ Metric.ball z r₀ → R < ‖t‖ := by
        intro t ht
        have h1 := hnear t ht
        have h2 := hlower t
        rw [hr₀] at h1
        linarith
      have hopen := isOpenMap_of_transcendental hf
      refine ⟨U ∩ f '' Metric.ball z r₀, ‖z‖ + r₀ + 1,
        hU.inter (hopen _ Metric.isOpen_ball),
        ⟨f z, hzU, ⟨z, Metric.mem_ball_self hr₀0, rfl⟩⟩, ?_⟩
      intro w hw
      obtain ⟨hwU, t, htB, htw⟩ := hw
      obtain ⟨T, hTcard, hTn, hTf⟩ := hmany w hwU
      have htT : t ∉ T := by
        intro hmem
        have h1 : ‖t‖ < R := hTn t hmem
        have h2 : R < ‖t‖ := hBfar t htB
        linarith
      refine ⟨insert t T, ?_, ?_, ?_⟩
      · rw [Finset.card_insert_of_notMem htT]
        omega
      · intro s hs
        rcases Finset.mem_insert.mp hs with rfl | hs'
        · have h1 := hnear s htB
          have h2 := hupper s
          linarith
        · have h1 : ‖s‖ < R := hTn s hs'
          have h2 : R < ‖z‖ := hzR
          linarith
      · intro s hs
        rcases Finset.mem_insert.mp hs with rfl | hs'
        · exact htw
        · exact hTf s hs'

end GaloisForLFunctions.HTGeometry
