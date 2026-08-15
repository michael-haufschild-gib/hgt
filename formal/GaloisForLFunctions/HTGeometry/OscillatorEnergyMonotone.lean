import Mathlib

/-!
# Two monotone quantities of the harmonic-oscillator equation

For a solution of `v″ = (ξ² − μ)v` put

`E = v′² − (ξ² − μ)v²` ,   `G = −E/(ξ² − μ)` .

Then `E′ = −2ξ v²`, so `E` is nonincreasing on the positive axis, and

`G′ = 2ξ v′²/(ξ² − μ)²  ≥ 0` ,   `v² − G = v′²/(ξ² − μ) ≥ 0`   (where `ξ² > μ`),

so `G` is nondecreasing and is dominated by `v²`.  The pair separates the two behaviours at
infinity in one step: if `E` is ever negative past the turning point then `G` is positive there and
never decreases, so `v²` stays above a positive constant and the solution is not square integrable.

Both statements are exact derivative computations; no asymptotics are involved.
-/

open Set

namespace GaloisForLFunctions.HTGeometry

/-- Energy of a solution of the oscillator equation. -/
noncomputable def oscillatorMonotoneEnergy (mu : ℝ) (v v' : ℝ → ℝ) (xi : ℝ) : ℝ :=
  v' xi ^ 2 - (xi ^ 2 - mu) * v xi ^ 2

/-- Normalized energy deficit, monotone past the turning point. -/
noncomputable def oscRatio (mu : ℝ) (v v' : ℝ → ℝ) (xi : ℝ) : ℝ :=
  -oscillatorMonotoneEnergy mu v v' xi / (xi ^ 2 - mu)

/-- **Energy derivative.**  The oscillator energy has derivative `−2ξv²`. -/
theorem hasDerivAt_oscillatorMonotoneEnergy {mu : ℝ} {v v' : ℝ → ℝ}
    (hv : ∀ x, HasDerivAt v (v' x) x)
    (hv' : ∀ x, HasDerivAt v' ((x ^ 2 - mu) * v x) x) (xi : ℝ) :
    HasDerivAt (oscillatorMonotoneEnergy mu v v') (-(2 * xi * v xi ^ 2)) xi := by
  have h1 : HasDerivAt (fun x => v' x ^ 2) (2 * v' xi * ((xi ^ 2 - mu) * v xi)) xi := by
    refine ((hv' xi).pow 2).congr_deriv ?_
    push_cast
    ring
  have ha : HasDerivAt (fun x : ℝ => x ^ 2 - mu) (2 * xi) xi := by
    have := (hasDerivAt_pow 2 xi).sub_const mu
    simpa using this
  have hb : HasDerivAt (fun x => v x ^ 2) (2 * v xi * v' xi) xi := by
    refine ((hv xi).pow 2).congr_deriv ?_
    push_cast
    ring
  have h2 : HasDerivAt (fun x => (x ^ 2 - mu) * v x ^ 2)
      (2 * xi * v xi ^ 2 + (xi ^ 2 - mu) * (2 * v xi * v' xi)) xi := ha.mul hb
  have h3 := h1.sub h2
  refine h3.congr_deriv ?_
  ring

/-- The oscillator energy is nonincreasing on any interval in the positive axis. -/
theorem antitoneOn_oscillatorMonotoneEnergy {mu : ℝ} {v v' : ℝ → ℝ} {a : ℝ} (ha : 0 ≤ a)
    (hv : ∀ x, HasDerivAt v (v' x) x)
    (hv' : ∀ x, HasDerivAt v' ((x ^ 2 - mu) * v x) x) :
    AntitoneOn (oscillatorMonotoneEnergy mu v v') (Ici a) := by
  refine antitoneOn_of_deriv_nonpos (convex_Ici a) ?_ ?_ ?_
  · exact fun x _ => ((hasDerivAt_oscillatorMonotoneEnergy hv hv' x).continuousAt).continuousWithinAt
  · intro x _
    exact (hasDerivAt_oscillatorMonotoneEnergy hv hv' x).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [interior_Ici] at hx
    rw [(hasDerivAt_oscillatorMonotoneEnergy hv hv' x).deriv]
    have hx0 : 0 ≤ x := le_of_lt (lt_of_le_of_lt ha hx)
    nlinarith [sq_nonneg (v x)]

/-- **Ratio derivative.**  Past the turning point the normalized energy deficit has derivative
`2ξ v′²/(ξ² − μ)²`. -/
theorem hasDerivAt_oscRatio {mu : ℝ} {v v' : ℝ → ℝ} {xi : ℝ} (hxi : xi ^ 2 - mu ≠ 0)
    (hv : ∀ x, HasDerivAt v (v' x) x)
    (hv' : ∀ x, HasDerivAt v' ((x ^ 2 - mu) * v x) x) :
    HasDerivAt (oscRatio mu v v') (2 * xi * v' xi ^ 2 / (xi ^ 2 - mu) ^ 2) xi := by
  have hE : HasDerivAt (fun x => -oscillatorMonotoneEnergy mu v v' x) (2 * xi * v xi ^ 2) xi := by
    refine ((hasDerivAt_oscillatorMonotoneEnergy hv hv' xi).neg).congr_deriv ?_
    ring
  have hd : HasDerivAt (fun x : ℝ => x ^ 2 - mu) (2 * xi) xi := by
    have := (hasDerivAt_pow 2 xi).sub_const mu
    simpa using this
  have hq := hE.div hd hxi
  refine hq.congr_deriv ?_
  have hne : (xi ^ 2 - mu) ≠ 0 := hxi
  simp only [oscillatorMonotoneEnergy]
  field_simp
  ring

/-- The normalized energy deficit is nondecreasing past the turning point. -/
theorem monotoneOn_oscRatio {mu : ℝ} {v v' : ℝ → ℝ} {a : ℝ} (ha : 0 < a)
    (hmu : mu < a ^ 2)
    (hv : ∀ x, HasDerivAt v (v' x) x)
    (hv' : ∀ x, HasDerivAt v' ((x ^ 2 - mu) * v x) x) :
    MonotoneOn (oscRatio mu v v') (Ici a) := by
  have hpos : ∀ x ∈ Ici a, 0 < x ^ 2 - mu := by
    intro x hx
    have hax : a ≤ x := hx
    have : a ^ 2 ≤ x ^ 2 := by nlinarith
    linarith
  refine monotoneOn_of_deriv_nonneg (convex_Ici a) ?_ ?_ ?_
  · intro x hx
    exact ((hasDerivAt_oscRatio (ne_of_gt (hpos x hx)) hv hv').continuousAt).continuousWithinAt
  · intro x hx
    rw [interior_Ici] at hx
    have hxm : x ∈ Ici a := le_of_lt (Set.mem_Ioi.1 hx)
    exact ((hasDerivAt_oscRatio (ne_of_gt (hpos x hxm)) hv hv').differentiableAt).differentiableWithinAt
  · intro x hx
    rw [interior_Ici] at hx
    have hxm : x ∈ Ici a := le_of_lt (Set.mem_Ioi.1 hx)
    rw [(hasDerivAt_oscRatio (ne_of_gt (hpos x hxm)) hv hv').deriv]
    have hx0 : 0 < x := lt_trans ha hx
    positivity

/-- Past the turning point the normalized energy deficit is dominated by the square of the
solution, the difference being `v′²/(ξ² − μ)`. -/
theorem oscRatio_le_sq {mu : ℝ} {v v' : ℝ → ℝ} {xi : ℝ} (hxi : 0 < xi ^ 2 - mu) :
    oscRatio mu v v' xi ≤ v xi ^ 2 := by
  have hid : v xi ^ 2 - oscRatio mu v v' xi = v' xi ^ 2 / (xi ^ 2 - mu) := by
    rw [oscRatio, oscillatorMonotoneEnergy]
    field_simp
    ring
  have hnn : (0 : ℝ) ≤ v' xi ^ 2 / (xi ^ 2 - mu) := by positivity
  linarith

end GaloisForLFunctions.HTGeometry
