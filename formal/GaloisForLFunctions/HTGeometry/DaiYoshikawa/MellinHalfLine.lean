import Mathlib.Analysis.MellinTransform

/-!
# The two half-line Mellin pieces of a regularized heat trace

The analytic continuation of a spectral zeta function past `Re s = 1` splits its Mellin integral at
`t = 1`.  Section 3.1 of Dai–Yoshikawa, *Degeneration of Riemann surfaces and small eigenvalues of
the Laplacian* (arXiv:2509.06151v2), uses exactly this split: the regularized head
`Θ(t) − a₀/t − a₁` is `O(t)` as `t → 0`, and the tail `Θ(t) − h` decays exponentially as `t → ∞`.

Consequently the head Mellin integral is holomorphic on `Re s > −1` and the tail Mellin integral is
entire.  Both statements are proved here from mathlib's Mellin differentiability criteria, applied
to the indicator of `(0,1]` and of `(1,∞)`.
-/

open MeasureTheory Set Filter Asymptotics Real Complex Topology

namespace GaloisForLFunctions.HTGeometry.DaiYoshikawa

/-- The Mellin integral over `(0,1]`. -/
noncomputable def mellinHead (g : ℝ → ℂ) : ℂ → ℂ := mellin (Set.indicator (Ioc (0 : ℝ) 1) g)

/-- The Mellin integral over `(1,∞)`. -/
noncomputable def mellinTail (g : ℝ → ℂ) : ℂ → ℂ := mellin (Set.indicator (Ioi (1 : ℝ)) g)

/-- **The head Mellin integral is holomorphic on `Re s > −1`.**

An integrand that is `O(t)` at the origin and supported in `(0,1]` has a Mellin transform
holomorphic on the half-plane `Re s > −1`. -/
theorem differentiableAt_mellinHead {g : ℝ → ℂ} {C : ℝ} (hg : Continuous g)
    (hbd : ∀ t ∈ Ioc (0 : ℝ) 1, ‖g t‖ ≤ C * t) {s : ℂ} (hs : -1 < s.re) :
    DifferentiableAt ℂ (mellinHead g) s := by
  have hfc : LocallyIntegrableOn (Set.indicator (Ioc (0 : ℝ) 1) g) (Ioi 0) volume :=
    (hg.locallyIntegrable.indicator measurableSet_Ioc).locallyIntegrableOn _
  have hf_top : Set.indicator (Ioc (0 : ℝ) 1) g =O[atTop] fun x : ℝ => x ^ (-(s.re + 1)) := by
    refine Asymptotics.IsBigO.of_bound 0 ?_
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    have : x ∉ Ioc (0 : ℝ) 1 := fun hc => absurd hc.2 (not_le.mpr hx)
    simp [Set.indicator_of_notMem this]
  have hf_bot : Set.indicator (Ioc (0 : ℝ) 1) g =O[𝓝[>] (0 : ℝ)] fun x : ℝ => x ^ (-(-1 : ℝ)) := by
    refine Asymptotics.IsBigO.of_bound |C| ?_
    have hlt : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), t < 1 :=
      nhdsWithin_le_nhds (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
    filter_upwards [self_mem_nhdsWithin, hlt] with t ht ht1
    have ht0 : (0 : ℝ) < t := ht
    have hmem : t ∈ Ioc (0 : ℝ) 1 := ⟨ht0, ht1.le⟩
    rw [Set.indicator_of_mem hmem]
    have hrpow : ‖(t : ℝ) ^ (-(-1 : ℝ))‖ = t := by
      rw [neg_neg, Real.rpow_one, Real.norm_eq_abs, abs_of_pos ht0]
    rw [hrpow]
    refine (hbd t hmem).trans ?_
    exact mul_le_mul_of_nonneg_right (le_abs_self C) ht0.le
  exact mellin_differentiableAt_of_isBigO_rpow hfc hf_top (by linarith) hf_bot hs

/-- **The tail Mellin integral is entire.**

An integrand supported in `(1,∞)` and decaying exponentially there has an entire Mellin
transform. -/
theorem differentiableAt_mellinTail {g : ℝ → ℂ} {C c : ℝ} (hc : 0 < c) (hg : Continuous g)
    (hbd : ∀ t ∈ Ioi (1 : ℝ), ‖g t‖ ≤ C * Real.exp (-c * t)) (s : ℂ) :
    DifferentiableAt ℂ (mellinTail g) s := by
  have hfc : LocallyIntegrableOn (Set.indicator (Ioi (1 : ℝ)) g) (Ioi 0) volume :=
    (hg.locallyIntegrable.indicator measurableSet_Ioi).locallyIntegrableOn _
  have hf_top : Set.indicator (Ioi (1 : ℝ)) g =O[atTop] fun t : ℝ => Real.exp (-c * t) := by
    refine Asymptotics.IsBigO.of_bound |C| ?_
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with t ht
    have hmem : t ∈ Ioi (1 : ℝ) := ht
    rw [Set.indicator_of_mem hmem]
    have hnorm : ‖Real.exp (-c * t)‖ = Real.exp (-c * t) := by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    rw [hnorm]
    refine (hbd t hmem).trans ?_
    exact mul_le_mul_of_nonneg_right (le_abs_self C) (Real.exp_nonneg _)
  have hf_bot : Set.indicator (Ioi (1 : ℝ)) g =O[𝓝[>] (0 : ℝ)] fun x : ℝ => x ^ (-(s.re - 1)) := by
    refine Asymptotics.IsBigO.of_bound 0 ?_
    have hlt : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), t < 1 :=
      nhdsWithin_le_nhds (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
    filter_upwards [hlt] with t ht1
    have : t ∉ Ioi (1 : ℝ) := not_lt.mpr ht1.le
    simp [Set.indicator_of_notMem this]
  exact mellin_differentiableAt_of_isBigO_rpow_exp hc hfc hf_top hf_bot (by linarith)

end GaloisForLFunctions.HTGeometry.DaiYoshikawa
