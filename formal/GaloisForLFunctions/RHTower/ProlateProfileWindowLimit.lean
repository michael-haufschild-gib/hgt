import GaloisForLFunctions.HTGeometry.LinearSecondOrderLimit
import GaloisForLFunctions.RHTower.ProlateRescaledCoefficients

/-!
# The rescaled prolate profile converges to the Hermite profile on every window

On a window `[0, K]` with `2K² ≤ c` the rescaled prolate equation is a regular linear equation whose
coefficients differ from the Hermite equation at the `n`-th rung by

`ε_P = 2|μ − (2n+1)| + 2K²(K² + 2n+1)/c` ,   `ε_Q = 4K/c` .

Grönwall's comparison therefore separates the prolate profile from the Hermite-rung solution with
the same initial phase vector by an envelope proportional to `ε_P + ε_Q`, and both vanish once the
bandwidth escapes and the separation constant approaches the rung.

The envelope is proportional to the a priori size `B` of the profile's phase pair on the window, so
the statement is most useful for the profile normalized at the origin, where `B` is uniform.
-/

open Set Filter Topology GaloisForLFunctions.HTGeometry

namespace RHTower

/-- Coefficient perturbation of the rescaled prolate equation against the `n`-th Hermite rung. -/
noncomputable def prolateWindowEpsP (c mu K : ℝ) (n : ℕ) : ℝ :=
  2 * |mu - (2 * (n : ℝ) + 1)| + 2 * (K ^ 2 * (K ^ 2 + (2 * (n : ℝ) + 1))) / c

/-- First-derivative coefficient of the rescaled prolate equation on the window. -/
noncomputable def prolateWindowEpsQ (c K : ℝ) : ℝ := 4 * K / c

/-- Lipschitz constant of the limiting Hermite field on the window. -/
noncomputable def hermiteWindowBound (K : ℝ) (n : ℕ) : ℝ := K ^ 2 + (2 * (n : ℝ) + 1)

/-- **Window comparison.**  The prolate profile and the Hermite-rung solution with the same initial
phase vector separate by the Grönwall envelope built from the coefficient perturbations. -/
theorem prolateProfile_window_dist_le
    {c mu K B : ℝ} {n : ℕ} {u u' u'' v v' v'' : ℝ → ℝ}
    (hK : 0 < K) (hcK : 2 * K ^ 2 ≤ c)
    (hu : ∀ x, HasDerivAt u (u' x) x) (hu' : ∀ x, HasDerivAt u' (u'' x) x)
    (hv : ∀ x, HasDerivAt v (v' x) x) (hv' : ∀ x, HasDerivAt v' (v'' x) x)
    (hequ : ∀ x ∈ Icc (0 : ℝ) K,
      u'' x = rescaledProlateP c mu x * u x + rescaledProlateQ c x * u' x)
    (heqv : ∀ x ∈ Icc (0 : ℝ) K, v'' x = hermiteRungP n x * v x)
    (hB : ∀ x ∈ Icc (0 : ℝ) K, max |u x| |u' x| ≤ B)
    (h0 : u 0 = v 0) (h0' : u' 0 = v' 0) :
    ∀ x ∈ Icc (0 : ℝ) K, max |u x - v x| |u' x - v' x|
      ≤ ((prolateWindowEpsP c mu K n + prolateWindowEpsQ c K) * B
          / max 1 (hermiteWindowBound K n))
        * (Real.exp (max 1 (hermiteWindowBound K n) * (K - 0)) - 1) := by
  have habs : ∀ x ∈ Icc (0 : ℝ) K, |x| ≤ K := by
    intro x hx
    rw [abs_of_nonneg hx.1]
    exact hx.2
  refine phasePair_dist_le_uniform (le_of_lt hK) hu hu' hv hv' hequ heqv ?_ ?_ ?_ hB h0 h0'
  · intro x hx
    exact abs_hermiteRungP_le (habs x hx)
  · intro x hx
    exact abs_rescaledProlateP_sub_le hK hcK (habs x hx)
  · intro x hx
    exact abs_rescaledProlateQ_le hK hcK (habs x hx)

/-- The coefficient perturbation vanishes as the bandwidth escapes and the separation constant
approaches the rung. -/
theorem tendsto_prolateWindowEpsP {ι : Type*} {L : Filter ι} {mu c : ι → ℝ} {K : ℝ} {n : ℕ}
    (hmu : Tendsto mu L (𝓝 (2 * (n : ℝ) + 1))) (hc : Tendsto c L atTop) :
    Tendsto (fun i => prolateWindowEpsP (c i) (mu i) K n) L (𝓝 0) := by
  have h1 : Tendsto (fun i => 2 * |mu i - (2 * (n : ℝ) + 1)|) L (𝓝 0) := by
    have hsub : Tendsto (fun i => mu i - (2 * (n : ℝ) + 1)) L (𝓝 0) := by
      simpa using hmu.sub_const (2 * (n : ℝ) + 1)
    have habs : Tendsto (fun i => |mu i - (2 * (n : ℝ) + 1)|) L (𝓝 0) := by
      simpa using hsub.abs
    simpa using habs.const_mul 2
  have h2 : Tendsto
      (fun i => 2 * (K ^ 2 * (K ^ 2 + (2 * (n : ℝ) + 1))) / c i) L (𝓝 0) :=
    tendsto_const_nhds.div_atTop hc
  have := h1.add h2
  simpa [prolateWindowEpsP] using this

/-- The first-derivative coefficient vanishes as the bandwidth escapes. -/
theorem tendsto_prolateWindowEpsQ {ι : Type*} {L : Filter ι} {c : ι → ℝ} {K : ℝ}
    (hc : Tendsto c L atTop) :
    Tendsto (fun i => prolateWindowEpsQ (c i) K) L (𝓝 0) :=
  tendsto_const_nhds.div_atTop hc

/-- **Window envelope vanishes.**  The Grönwall envelope of the window comparison tends to zero. -/
theorem tendsto_prolateWindow_envelope
    {ι : Type*} {L : Filter ι} {mu c : ι → ℝ} {K B : ℝ} {n : ℕ}
    (hmu : Tendsto mu L (𝓝 (2 * (n : ℝ) + 1))) (hc : Tendsto c L atTop) :
    Tendsto (fun i => ((prolateWindowEpsP (c i) (mu i) K n + prolateWindowEpsQ (c i) K) * B
        / max 1 (hermiteWindowBound K n))
      * (Real.exp (max 1 (hermiteWindowBound K n) * (K - 0)) - 1)) L (𝓝 0) :=
  tendsto_sup_dist_of_coeff_tendsto (Lp := hermiteWindowBound K n) (B := B) (a := 0) (b := K)
    (tendsto_prolateWindowEpsP hmu hc) (tendsto_prolateWindowEpsQ hc)

/-- **Uniform convergence on the window.**  The prolate profile converges to the Hermite-rung
solution uniformly on `[0, K]`. -/
theorem tendsto_prolateProfile_window
    {ι : Type*} {L : Filter ι} {mu c : ι → ℝ} {K B : ℝ} {n : ℕ}
    {u u' u'' : ι → ℝ → ℝ} {v v' v'' : ℝ → ℝ}
    (hK : 0 < K) (hcK : ∀ i, 2 * K ^ 2 ≤ c i)
    (hu : ∀ i x, HasDerivAt (u i) (u' i x) x) (hu' : ∀ i x, HasDerivAt (u' i) (u'' i x) x)
    (hv : ∀ x, HasDerivAt v (v' x) x) (hv' : ∀ x, HasDerivAt v' (v'' x) x)
    (hequ : ∀ i, ∀ x ∈ Icc (0 : ℝ) K,
      u'' i x = rescaledProlateP (c i) (mu i) x * u i x + rescaledProlateQ (c i) x * u' i x)
    (heqv : ∀ x ∈ Icc (0 : ℝ) K, v'' x = hermiteRungP n x * v x)
    (hB : ∀ i, ∀ x ∈ Icc (0 : ℝ) K, max |u i x| |u' i x| ≤ B)
    (h0 : ∀ i, u i 0 = v 0) (h0' : ∀ i, u' i 0 = v' 0)
    (hmu : Tendsto mu L (𝓝 (2 * (n : ℝ) + 1))) (hc : Tendsto c L atTop) :
    ∀ x ∈ Icc (0 : ℝ) K, Tendsto (fun i => u i x) L (𝓝 (v x)) := by
  intro x hx
  have henv := tendsto_prolateWindow_envelope (mu := mu) (c := c) (K := K) (B := B) (n := n)
    hmu hc
  have hbound : ∀ i, |u i x - v x|
      ≤ ((prolateWindowEpsP (c i) (mu i) K n + prolateWindowEpsQ (c i) K) * B
          / max 1 (hermiteWindowBound K n))
        * (Real.exp (max 1 (hermiteWindowBound K n) * (K - 0)) - 1) := by
    intro i
    exact le_trans (le_max_left _ _)
      (prolateProfile_window_dist_le hK (hcK i) (hu i) (hu' i) hv hv' (hequ i) heqv (hB i)
        (h0 i) (h0' i) x hx)
  have hzero : Tendsto (fun i => u i x - v x) L (𝓝 0) := by
    refine squeeze_zero_norm' (Eventually.of_forall fun i => ?_) henv
    rw [Real.norm_eq_abs]
    exact hbound i
  have := hzero.add_const (v x)
  simpa using this

/-- The normal-form coefficient is bounded on the window by the limiting bound plus the
perturbation. -/
theorem abs_rescaledProlateP_le {c K mu xi : ℝ} {n : ℕ}
    (hK : 0 < K) (hcK : 2 * K ^ 2 ≤ c) (hxi : |xi| ≤ K) :
    |rescaledProlateP c mu xi| ≤ hermiteWindowBound K n + prolateWindowEpsP c mu K n := by
  have h1 : |rescaledProlateP c mu xi - hermiteRungP n xi| ≤ prolateWindowEpsP c mu K n :=
    abs_rescaledProlateP_sub_le hK hcK hxi
  have h2 : |hermiteRungP n xi| ≤ hermiteWindowBound K n := abs_hermiteRungP_le hxi
  calc |rescaledProlateP c mu xi|
      = |(rescaledProlateP c mu xi - hermiteRungP n xi) + hermiteRungP n xi| := by ring_nf
    _ ≤ |rescaledProlateP c mu xi - hermiteRungP n xi| + |hermiteRungP n xi| := abs_add_le _ _
    _ ≤ hermiteWindowBound K n + prolateWindowEpsP c mu K n := by linarith

/-- **A priori phase bound on the window.**  A solution of the rescaled prolate equation grows at
most exponentially on the window, at a rate built from the two explicit coefficient bounds. -/
theorem prolateProfile_window_phase_le
    {c mu K : ℝ} {n : ℕ} {u u' u'' : ℝ → ℝ}
    (hK : 0 < K) (hcK : 2 * K ^ 2 ≤ c)
    (hu : ∀ x, HasDerivAt u (u' x) x) (hu' : ∀ x, HasDerivAt u' (u'' x) x)
    (hequ : ∀ x ∈ Icc (0 : ℝ) K,
      u'' x = rescaledProlateP c mu x * u x + rescaledProlateQ c x * u' x) :
    ∀ x ∈ Icc (0 : ℝ) K, max |u x| |u' x|
      ≤ max |u 0| |u' 0|
        * Real.exp (max 1 ((hermiteWindowBound K n + prolateWindowEpsP c mu K n)
            + prolateWindowEpsQ c K) * (x - 0)) := by
  have habs : ∀ x ∈ Icc (0 : ℝ) K, |x| ≤ K := by
    intro x hx
    rw [abs_of_nonneg hx.1]
    exact hx.2
  refine phasePair_norm_le (Lp := hermiteWindowBound K n + prolateWindowEpsP c mu K n)
    (Lq := prolateWindowEpsQ c K) (le_of_lt hK) hu hu' hequ ?_ ?_ le_rfl
  · intro x hx
    exact abs_rescaledProlateP_le hK hcK (habs x hx)
  · intro x hx
    exact abs_rescaledProlateQ_le hK hcK (habs x hx)

end RHTower
