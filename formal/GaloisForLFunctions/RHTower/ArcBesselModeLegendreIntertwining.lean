import GaloisForLFunctions.RHTower.BesselKZeroMoments

/-!
# The frequency Euler operator on arc Bessel modes is the zonal Legendre operator

For a frequency `k > 0` and an arc parameter `|u| < 1`, put `y = √(1 − u²)` and consider the arc
Bessel mode

`f(k, u) = cos(k u) K₀(k y)`   (`arcBesselMode`),

the value at the point `u + i y` of the unit circle of the decaying `s = ½` Whittaker mode
`K₀(k y) cos(k x)` (with `K₀ = kMoment 0`).

**Theorem** (`frequencyEuler_arcBesselMode_eq_legendre`).

`k² ∂²_k f + 2k ∂_k f = −∂_u ((1 − u²) ∂_u f)`.

So the frequency operator `D_k = −∂_k k² ∂_k`, which is the Fourier image of the dilation operator
`𝒟 = −∂_x x² ∂_x`, acts on the arc Bessel modes as the zonal Legendre operator
`L_u = −∂_u (1 − u²) ∂_u` with the opposite sign: `D_k f = −L_u f`, hence `D_k² f = L_u² f`.

Geometrically, `K₀(k y) cos(k x)` is harmonic for the axisymmetric Laplacian
`∂_x² + ∂_y² + y⁻¹ ∂_y` of `ℝ³` (with `y` the distance to the `x`-axis), the unit circle is a
meridian of the unit sphere, `k ∂_k` is the radial Euler operator `x ∂_x + y ∂_y`, and the
identity is `E (E + 1) = −Δ_{S²}` on harmonic functions.

Proof.  Direct differentiation with `K₀' = −K₁` and `K₁' = −K₂` (`hasDerivAt_kMoment`) and
`(√(1 − u²))' = −u/√(1 − u²)`.  Collecting terms, everything cancels except
`cos(ku) (k/y) [k y (K₂ − K₀)(k y) − K₁(k y)]`, which vanishes by Bessel's equation
`w (K₂(w) − K₀(w)) = K₁(w)` (`kMoment_ode`).
-/

open Real Filter Topology RHTower.BesselKZero

namespace RHTower

noncomputable section

/-- The arc Bessel mode `cos(k u) K₀(k √(1 − u²))`. -/
def arcBesselMode (k u : ℝ) : ℝ := Real.cos (k * u) * kMoment 0 (k * Real.sqrt (1 - u ^ 2))

/-- The frequency derivative of `arcBesselMode`. -/
def arcBesselModeFreqDeriv (k u : ℝ) : ℝ :=
  -(u * Real.sin (k * u) * kMoment 0 (k * Real.sqrt (1 - u ^ 2))) -
    Real.sqrt (1 - u ^ 2) * Real.cos (k * u) * kMoment 1 (k * Real.sqrt (1 - u ^ 2))

/-- The second frequency derivative of `arcBesselMode`. -/
def arcBesselModeFreqDeriv2 (k u : ℝ) : ℝ :=
  -(u ^ 2 * Real.cos (k * u) * kMoment 0 (k * Real.sqrt (1 - u ^ 2))) +
    2 * u * Real.sqrt (1 - u ^ 2) * Real.sin (k * u) * kMoment 1 (k * Real.sqrt (1 - u ^ 2)) +
    Real.sqrt (1 - u ^ 2) ^ 2 * Real.cos (k * u) * kMoment 2 (k * Real.sqrt (1 - u ^ 2))

/-- The arc derivative of `arcBesselMode`. -/
def arcBesselModeArcDeriv (k u : ℝ) : ℝ :=
  -(k * Real.sin (k * u) * kMoment 0 (k * Real.sqrt (1 - u ^ 2))) +
    k * u / Real.sqrt (1 - u ^ 2) * Real.cos (k * u) * kMoment 1 (k * Real.sqrt (1 - u ^ 2))

/-- The Legendre flux `(1 − u²) ∂_u f`, written without the division by `√(1 − u²)`. -/
def arcBesselModeFlux (k u : ℝ) : ℝ :=
  -(k * (1 - u ^ 2) * Real.sin (k * u) * kMoment 0 (k * Real.sqrt (1 - u ^ 2))) +
    k * u * Real.sqrt (1 - u ^ 2) * Real.cos (k * u) * kMoment 1 (k * Real.sqrt (1 - u ^ 2))

/-- The arc derivative of the Legendre flux. -/
def arcBesselModeFluxDeriv (k u : ℝ) : ℝ :=
  2 * k * u * Real.sin (k * u) * kMoment 0 (k * Real.sqrt (1 - u ^ 2)) -
    k ^ 2 * (1 - u ^ 2) * Real.cos (k * u) * kMoment 0 (k * Real.sqrt (1 - u ^ 2)) -
    2 * k ^ 2 * u * Real.sqrt (1 - u ^ 2) * Real.sin (k * u) *
      kMoment 1 (k * Real.sqrt (1 - u ^ 2)) +
    k * ((1 - 2 * u ^ 2) / Real.sqrt (1 - u ^ 2)) * Real.cos (k * u) *
      kMoment 1 (k * Real.sqrt (1 - u ^ 2)) +
    k ^ 2 * u ^ 2 * Real.cos (k * u) * kMoment 2 (k * Real.sqrt (1 - u ^ 2))

theorem sqrt_one_sub_sq_pos {u : ℝ} (hu : |u| < 1) : 0 < Real.sqrt (1 - u ^ 2) := by
  apply Real.sqrt_pos.mpr
  have h := abs_lt.mp hu
  nlinarith

theorem sq_sqrt_one_sub_sq {u : ℝ} (hu : |u| < 1) : Real.sqrt (1 - u ^ 2) ^ 2 = 1 - u ^ 2 := by
  have h := abs_lt.mp hu
  exact Real.sq_sqrt (by nlinarith)

/-- `κ ↦ K_j(κ y)` has derivative `−y K_{j+1}(k y)`. -/
theorem hasDerivAt_kMoment_mul_const (j : ℕ) {k y : ℝ} (hk : 0 < k) (hy : 0 < y) :
    HasDerivAt (fun κ => kMoment j (κ * y)) (-(y * kMoment (j + 1) (k * y))) k := by
  have h := (hasDerivAt_kMoment j (mul_pos hk hy)).comp k (hasDerivAt_mul_const y)
  refine h.congr_deriv ?_
  ring

/-- **First frequency derivative.** -/
theorem hasDerivAt_arcBesselMode_freq {k u : ℝ} (hk : 0 < k) (hu : |u| < 1) :
    HasDerivAt (fun κ => arcBesselMode κ u) (arcBesselModeFreqDeriv k u) k := by
  have hy := sqrt_one_sub_sq_pos hu
  have hc : HasDerivAt (fun κ => Real.cos (κ * u)) (-Real.sin (k * u) * u) k :=
    (hasDerivAt_mul_const u).cos
  have h := hc.mul (hasDerivAt_kMoment_mul_const 0 hk hy)
  refine h.congr_deriv ?_
  unfold arcBesselModeFreqDeriv
  ring

/-- **Second frequency derivative.** -/
theorem hasDerivAt_arcBesselModeFreqDeriv {k u : ℝ} (hk : 0 < k) (hu : |u| < 1) :
    HasDerivAt (fun κ => arcBesselModeFreqDeriv κ u) (arcBesselModeFreqDeriv2 k u) k := by
  have hy := sqrt_one_sub_sq_pos hu
  set y := Real.sqrt (1 - u ^ 2)
  have hc : HasDerivAt (fun κ => Real.cos (κ * u)) (-Real.sin (k * u) * u) k :=
    (hasDerivAt_mul_const u).cos
  have hs : HasDerivAt (fun κ => Real.sin (κ * u)) (Real.cos (k * u) * u) k :=
    (hasDerivAt_mul_const u).sin
  have h0 := hasDerivAt_kMoment_mul_const 0 hk hy
  have h1 := hasDerivAt_kMoment_mul_const 1 hk hy
  have h := ((hs.const_mul u).mul h0).neg.sub ((hc.const_mul y).mul h1)
  refine h.congr_deriv ?_
  unfold arcBesselModeFreqDeriv2
  ring

/-- `v ↦ K_j(k √(1 − v²))` has derivative `k u K_{j+1}(k y)/y`. -/
theorem hasDerivAt_kMoment_arc (j : ℕ) {k u : ℝ} (hk : 0 < k) (hu : |u| < 1) :
    HasDerivAt (fun v => kMoment j (k * Real.sqrt (1 - v ^ 2)))
      (k * u / Real.sqrt (1 - u ^ 2) * kMoment (j + 1) (k * Real.sqrt (1 - u ^ 2))) u := by
  have hy := sqrt_one_sub_sq_pos hu
  have hq : HasDerivAt (fun v : ℝ => 1 - v ^ 2) (-(2 * u)) u := by
    simpa using ((hasDerivAt_pow 2 u).const_sub 1)
  have hne : (1 : ℝ) - u ^ 2 ≠ 0 := by
    have := sq_sqrt_one_sub_sq hu
    nlinarith
  have hsq := hq.sqrt hne
  have h := (hasDerivAt_kMoment j (mul_pos hk hy)).comp u (hsq.const_mul k)
  refine h.congr_deriv ?_
  field_simp

/-- **Arc derivative.** -/
theorem hasDerivAt_arcBesselMode_arc {k u : ℝ} (hk : 0 < k) (hu : |u| < 1) :
    HasDerivAt (fun v => arcBesselMode k v) (arcBesselModeArcDeriv k u) u := by
  have hc : HasDerivAt (fun v => Real.cos (k * v)) (-Real.sin (k * u) * k) u :=
    ((hasDerivAt_id' u).const_mul k).cos.congr_deriv (by ring)
  have h := hc.mul (hasDerivAt_kMoment_arc 0 hk hu)
  refine h.congr_deriv ?_
  unfold arcBesselModeArcDeriv
  ring

theorem flux_eq {k u : ℝ} (hu : |u| < 1) :
    (1 - u ^ 2) * arcBesselModeArcDeriv k u = arcBesselModeFlux k u := by
  have hy := sqrt_one_sub_sq_pos hu
  have h2 := sq_sqrt_one_sub_sq hu
  have hinv : Real.sqrt (1 - u ^ 2) * (Real.sqrt (1 - u ^ 2))⁻¹ = 1 := mul_inv_cancel₀ hy.ne'
  unfold arcBesselModeArcDeriv arcBesselModeFlux
  linear_combination
    (-(k * u * Real.cos (k * u) * kMoment 1 (k * Real.sqrt (1 - u ^ 2)) *
      (Real.sqrt (1 - u ^ 2))⁻¹)) * h2 +
    (k * u * Real.cos (k * u) * kMoment 1 (k * Real.sqrt (1 - u ^ 2)) * Real.sqrt (1 - u ^ 2)) * hinv

/-- **Derivative of the Legendre flux.** -/
theorem hasDerivAt_arcBesselModeFlux {k u : ℝ} (hk : 0 < k) (hu : |u| < 1) :
    HasDerivAt (fun v => arcBesselModeFlux k v) (arcBesselModeFluxDeriv k u) u := by
  have hy := sqrt_one_sub_sq_pos hu
  have h2 := sq_sqrt_one_sub_sq hu
  have hinv : Real.sqrt (1 - u ^ 2) * (Real.sqrt (1 - u ^ 2))⁻¹ = 1 := mul_inv_cancel₀ hy.ne'
  have hne : (1 : ℝ) - u ^ 2 ≠ 0 := by nlinarith
  have hc : HasDerivAt (fun v => Real.cos (k * v)) (-Real.sin (k * u) * k) u :=
    ((hasDerivAt_id' u).const_mul k).cos.congr_deriv (by ring)
  have hs : HasDerivAt (fun v => Real.sin (k * v)) (Real.cos (k * u) * k) u :=
    ((hasDerivAt_id' u).const_mul k).sin.congr_deriv (by ring)
  have hq : HasDerivAt (fun v : ℝ => 1 - v ^ 2) (-(2 * u)) u := by
    simpa using ((hasDerivAt_pow 2 u).const_sub 1)
  have hsq : HasDerivAt (fun v : ℝ => Real.sqrt (1 - v ^ 2))
      (-(2 * u) / (2 * Real.sqrt (1 - u ^ 2))) u := hq.sqrt hne
  have h0 : HasDerivAt (fun v => kMoment 0 (k * Real.sqrt (1 - v ^ 2)))
      (k * u / Real.sqrt (1 - u ^ 2) * kMoment 1 (k * Real.sqrt (1 - u ^ 2))) u :=
    hasDerivAt_kMoment_arc 0 hk hu
  have h1 : HasDerivAt (fun v => kMoment 1 (k * Real.sqrt (1 - v ^ 2)))
      (k * u / Real.sqrt (1 - u ^ 2) * kMoment 2 (k * Real.sqrt (1 - u ^ 2))) u :=
    hasDerivAt_kMoment_arc 1 hk hu
  have hA := (((hq.const_mul k).mul hs).mul h0).neg
  have hB := ((((hasDerivAt_id' u).const_mul k).mul hsq).mul hc).mul h1
  have h := hA.add hB
  refine h.congr_deriv ?_
  unfold arcBesselModeFluxDeriv
  simp only [Pi.mul_apply]
  set Y := Real.sqrt (1 - u ^ 2)
  set C := Real.cos (k * u)
  set S := Real.sin (k * u)
  set K1 := kMoment 1 (k * Y)
  set K2 := kMoment 2 (k * Y)
  linear_combination (k ^ 2 * u * S * K1 + k * C * K1) * Y⁻¹ * h2 +
    (k ^ 2 * u ^ 2 * C * K2 - (k ^ 2 * u * S * K1 + k * C * K1) * Y) * hinv

/-- **Collecting terms**: the frequency Euler expression plus the flux derivative vanishes by
Bessel's equation `w (K₂(w) − K₀(w)) = K₁(w)` at `w = k √(1 − u²)`. -/
theorem freqEuler_add_fluxDeriv_eq_zero {k u : ℝ} (hk : 0 < k) (hu : |u| < 1) :
    k ^ 2 * arcBesselModeFreqDeriv2 k u + 2 * k * arcBesselModeFreqDeriv k u +
      arcBesselModeFluxDeriv k u = 0 := by
  have hy := sqrt_one_sub_sq_pos hu
  have h2 := sq_sqrt_one_sub_sq hu
  have hinv : Real.sqrt (1 - u ^ 2) * (Real.sqrt (1 - u ^ 2))⁻¹ = 1 := mul_inv_cancel₀ hy.ne'
  have hode := kMoment_ode (mul_pos hk hy)
  unfold arcBesselModeFreqDeriv2 arcBesselModeFreqDeriv arcBesselModeFluxDeriv
  set Y := Real.sqrt (1 - u ^ 2)
  set C := Real.cos (k * u)
  set K1 := kMoment 1 (k * Y)
  set K2 := kMoment 2 (k * Y)
  linear_combination (k ^ 2 * C * K2 - 2 * k * Y⁻¹ * C * K1) * h2 +
    (k ^ 2 * C * kMoment 0 (k * Y) - k ^ 2 * C * K2 + 2 * k * Y * C * K1) * hinv +
    (C * k * Y⁻¹) * hode

/-- **The frequency Euler operator is the zonal Legendre operator** on arc Bessel modes:
`k² ∂²_k f + 2k ∂_k f = −∂_u ((1 − u²) ∂_u f)` for `f(k, u) = cos(ku) K₀(k√(1 − u²))`,
`k > 0`, `|u| < 1`. -/
theorem frequencyEuler_arcBesselMode_eq_legendre {k u : ℝ} (hk : 0 < k) (hu : |u| < 1) :
    k ^ 2 * deriv (deriv fun κ => arcBesselMode κ u) k +
        2 * k * deriv (fun κ => arcBesselMode κ u) k =
      -deriv (fun v => (1 - v ^ 2) * deriv (fun w => arcBesselMode k w) v) u := by
  have hK : deriv (fun κ => arcBesselMode κ u) =ᶠ[𝓝 k] fun κ => arcBesselModeFreqDeriv κ u := by
    filter_upwards [Ioi_mem_nhds hk] with κ hκ
    exact (hasDerivAt_arcBesselMode_freq hκ hu).deriv
  have hU : (fun v => (1 - v ^ 2) * deriv (fun w => arcBesselMode k w) v) =ᶠ[𝓝 u]
      fun v => arcBesselModeFlux k v := by
    have hopen : IsOpen {v : ℝ | |v| < 1} := isOpen_lt continuous_abs continuous_const
    filter_upwards [hopen.mem_nhds hu] with v hv
    rw [(hasDerivAt_arcBesselMode_arc hk hv).deriv, flux_eq hv]
  rw [hK.deriv_eq, (hasDerivAt_arcBesselModeFreqDeriv hk hu).deriv,
    (hasDerivAt_arcBesselMode_freq hk hu).deriv, hU.deriv_eq,
    (hasDerivAt_arcBesselModeFlux hk hu).deriv]
  linarith [freqEuler_add_fluxDeriv_eq_zero hk hu]

end

end RHTower
