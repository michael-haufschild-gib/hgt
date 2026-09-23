import GaloisForLFunctions.RHTower.ProlateProfileWindowLimit

/-!
# The rescaled prolate profile converges to the Gaussian on every window

At the first oscillator rung the limiting Hermite equation is `v″ = (ξ² − 1)v`, whose even solution
with `v(0) = 1` is the Gaussian `e^{−ξ²/2}` — an explicit function, so no limit profile has to be
constructed.  Feeding it into the Grönwall window comparison gives, for a rescaled prolate profile
normalized by `u(0) = 1` and `u′(0) = 0`,

`max (|u − e^{−ξ²/2}|) (|u′ + ξ e^{−ξ²/2}|) ≤ ((ε_P + ε_Q)·B/L)(exp(L·K) − 1)`

on `[0, K]`, with `ε_P = 2|μ − 1| + 2K²(K² + 1)/c` and `ε_Q = 4K/c`.  Both vanish once the bandwidth
escapes and the separation constant approaches `1`, so the profile converges to the Gaussian
uniformly on every window.
-/

open Set Filter Topology GaloisForLFunctions.HTGeometry

namespace RHTower

/-- The Gaussian profile, the even solution of `v″ = (ξ² − 1)v` with `v(0) = 1`. -/
noncomputable def gaussianProfile (x : ℝ) : ℝ := Real.exp (-(x ^ (2 : ℕ)) / 2)

/-- Its derivative. -/
noncomputable def gaussianProfileDeriv (x : ℝ) : ℝ := -x * Real.exp (-(x ^ (2 : ℕ)) / 2)

@[simp]
theorem gaussianProfile_zero : gaussianProfile 0 = 1 := by
  simp [gaussianProfile]

@[simp]
theorem gaussianProfileDeriv_zero : gaussianProfileDeriv 0 = 0 := by
  simp [gaussianProfileDeriv]

theorem hasDerivAt_gaussianProfile (x : ℝ) :
    HasDerivAt gaussianProfile (gaussianProfileDeriv x) x := by
  have hq : HasDerivAt (fun y : ℝ => -(y ^ (2 : ℕ)) / 2) (-x) x := by
    have h := ((hasDerivAt_pow 2 x).neg).div_const 2
    refine h.congr_deriv ?_
    push_cast
    ring
  have := hq.exp
  refine this.congr_deriv ?_
  rw [gaussianProfileDeriv]
  ring

theorem hasDerivAt_gaussianProfileDeriv (x : ℝ) :
    HasDerivAt gaussianProfileDeriv (hermiteRungP 0 x * gaussianProfile x) x := by
  have hq : HasDerivAt (fun y : ℝ => -(y ^ (2 : ℕ)) / 2) (-x) x := by
    have h := ((hasDerivAt_pow 2 x).neg).div_const 2
    refine h.congr_deriv ?_
    push_cast
    ring
  have he : HasDerivAt (fun y : ℝ => Real.exp (-(y ^ (2 : ℕ)) / 2))
      (Real.exp (-(x ^ (2 : ℕ)) / 2) * (-x)) x := hq.exp
  have hx : HasDerivAt (fun y : ℝ => -y) (-1 : ℝ) x := (hasDerivAt_id x).neg
  have h := hx.mul he
  refine h.congr_deriv ?_
  rw [hermiteRungP, gaussianProfile]
  push_cast
  ring

/-- **Window comparison with the Gaussian.**  A rescaled prolate profile normalized at the origin
stays within the explicit Grönwall envelope of the Gaussian on `[0, K]`. -/
theorem prolateProfile_window_gaussian_dist_le
    {c mu K B : ℝ} {u u' u'' : ℝ → ℝ}
    (hK : 0 < K) (hcK : 2 * K ^ (2 : ℕ) ≤ c)
    (hu : ∀ x, HasDerivAt u (u' x) x) (hu' : ∀ x, HasDerivAt u' (u'' x) x)
    (hequ : ∀ x ∈ Icc (0 : ℝ) K,
      u'' x = rescaledProlateP c mu x * u x + rescaledProlateQ c x * u' x)
    (hB : ∀ x ∈ Icc (0 : ℝ) K, max |u x| |u' x| ≤ B)
    (h0 : u 0 = 1) (h0' : u' 0 = 0) :
    ∀ x ∈ Icc (0 : ℝ) K, max |u x - gaussianProfile x| |u' x - gaussianProfileDeriv x|
      ≤ ((prolateWindowEpsP c mu K 0 + prolateWindowEpsQ c K) * B
          / max 1 (hermiteWindowBound K 0))
        * (Real.exp (max 1 (hermiteWindowBound K 0) * (K - 0)) - 1) := by
  refine prolateProfile_window_dist_le (n := 0) hK hcK hu hu'
    hasDerivAt_gaussianProfile hasDerivAt_gaussianProfileDeriv hequ
    (fun x _ => rfl) hB ?_ ?_
  · rw [h0, gaussianProfile_zero]
  · rw [h0', gaussianProfileDeriv_zero]

/-- **Uniform convergence to the Gaussian on the window.**  Once the bandwidth escapes and the
separation constant approaches the first rung, the normalized rescaled profile converges to
`e^{−ξ²/2}` pointwise on `[0, K]`, with a uniform envelope. -/
theorem tendsto_prolateProfile_gaussian
    {ι : Type*} {L : Filter ι} {mu c : ι → ℝ} {K B : ℝ}
    {u u' u'' : ι → ℝ → ℝ}
    (hK : 0 < K) (hcK : ∀ i, 2 * K ^ (2 : ℕ) ≤ c i)
    (hu : ∀ i x, HasDerivAt (u i) (u' i x) x) (hu' : ∀ i x, HasDerivAt (u' i) (u'' i x) x)
    (hequ : ∀ i, ∀ x ∈ Icc (0 : ℝ) K,
      u'' i x = rescaledProlateP (c i) (mu i) x * u i x + rescaledProlateQ (c i) x * u' i x)
    (hB : ∀ i, ∀ x ∈ Icc (0 : ℝ) K, max |u i x| |u' i x| ≤ B)
    (h0 : ∀ i, u i 0 = 1) (h0' : ∀ i, u' i 0 = 0)
    (hmu : Tendsto mu L (𝓝 1)) (hc : Tendsto c L atTop) :
    ∀ x ∈ Icc (0 : ℝ) K, Tendsto (fun i => u i x) L (𝓝 (gaussianProfile x)) := by
  refine tendsto_prolateProfile_window (n := 0) (v := gaussianProfile)
    (v' := gaussianProfileDeriv) (v'' := fun x => hermiteRungP 0 x * gaussianProfile x)
    hK hcK hu hu' hasDerivAt_gaussianProfile hasDerivAt_gaussianProfileDeriv hequ
    (fun x _ => rfl) hB (fun i => by rw [h0 i, gaussianProfile_zero])
    (fun i => by rw [h0' i, gaussianProfileDeriv_zero]) ?_ hc
  simpa using hmu

end RHTower
