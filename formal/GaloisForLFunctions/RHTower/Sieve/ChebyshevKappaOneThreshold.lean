import GaloisForLFunctions.RHTower.Sieve.ChebyshevFinalCollapse

/-!
# Every threshold of the width-`1/log` chain holds eventually

The chain's lemmas carry four side conditions: the smoothing width is at least one and at most the
cutoff, the shifted cutoff's logarithm is past `16` (which is what makes `√(log Z) ≥ 4`, hence
`log T ≥ 8`), and the truncation height's logarithm is past the contour's own threshold `L₀`.

All four hold for every large cutoff, and packaging them once keeps the capstone's proof free of
filter plumbing.  The last one is the only one that sees `L₀`: since `log T = 2√(log Z)`, it asks
only that `log N` reach `(L₀/2)²`.
-/

namespace RHTower.Sieve

open Filter Topology

/-- **Every threshold holds eventually.** -/
theorem eventually_cheb_kappa_one_conditions (L₀ : ℝ) :
    ∀ᶠ N : ℝ in atTop,
      0 < N ∧ 1 ≤ chebWidthOne N ∧ chebWidthOne N ≤ N
        ∧ 16 ≤ Real.log (N + chebWidthOne N + 1)
        ∧ L₀ ≤ Real.log (chebHeightOne (N + chebWidthOne N + 1)) := by
  filter_upwards [eventually_ge_atTop (3 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop (max 16 ((L₀ / 2) ^ 2))] with N hN3 hlogN
  have hN0 : (0 : ℝ) < N := by linarith
  have h16 : (16 : ℝ) ≤ Real.log N := le_trans (le_max_left _ _) hlogN
  have hLsq : (L₀ / 2) ^ 2 ≤ Real.log N := le_trans (le_max_right _ _) hlogN
  have hlog1 : (1 : ℝ) ≤ Real.log N := by linarith
  have hH1 : (1 : ℝ) ≤ chebWidthOne N := one_le_chebWidthOne hN0 hlog1
  have hHN : chebWidthOne N ≤ N := chebWidthOne_le hN0.le
  have hlogZ : Real.log N ≤ Real.log (N + chebWidthOne N + 1) :=
    Real.log_le_log hN0 (by linarith)
  refine ⟨hN0, hH1, hHN, by linarith, ?_⟩
  rw [log_chebHeightOne]
  have hZ16 : (16 : ℝ) ≤ Real.log (N + chebWidthOne N + 1) := by linarith
  have hsq : (L₀ / 2) ^ 2 ≤ Real.log (N + chebWidthOne N + 1) := by linarith
  have hroot : Real.sqrt ((L₀ / 2) ^ 2) ≤ Real.sqrt (Real.log (N + chebWidthOne N + 1)) :=
    Real.sqrt_le_sqrt hsq
  rw [Real.sqrt_sq_eq_abs] at hroot
  have habs : L₀ / 2 ≤ |L₀ / 2| := le_abs_self _
  linarith [hroot, habs]

end RHTower.Sieve
