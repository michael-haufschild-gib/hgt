import GaloisForLFunctions.BlackHoleRingdown.NoNearArithmeticLadderOfZeros
import GaloisForLFunctions.HTGeometry.QNMPoschlTeller

/-!
# Ringdown reads the horizon spectrum

Two exact Einstein-`Λ` black holes share one radial equation.

* The massless topological AdS black hole has lapse `f = r² - 1`. In the tortoise coordinate
  `r = -coth x`, `x < 0`, the conformal scalar `ψ = rΦ` has potential
  `f (Q/r² + f'/r - 2) = Q / cosh² x`, with `Q` in the spectrum of the Laplacian of a hyperbolic
  horizon.
* The Nariai black hole `dS₂ × S²` has lapse `1 - ρ²`. With `ρ = tanh x` the massless scalar has
  potential `(1 - ρ²) Q = Q / cosh² x`, with `Q = l(l+1)` on the round horizon.

For `Q ≥ 1/4` and `ξ = √(Q - 1/4)` the equation `ψ_tt - ψ_xx + Q sech²x ψ = 0` has an exact mode of
frequency `-ξ - i/2`. Radial physics is therefore the same in both cases and the frequencies read the
horizon spectrum.

The round spectrum is rigid: `√((l+½)² - c)` is an arithmetic progression up to `O(1/l)`. So for every
time scale `κ` and shift `b`, the ladder `κ√((l+½)² - c) + b` is not eventually a sequence of critical
zero ordinates. This holds for the scalar (`c = 1/2`) and gravitational (`c = 5/2`) Nariai ladders.
-/

open Complex Filter Topology

noncomputable section

namespace GaloisForLFunctions.BlackHoleRingdown

open HTGeometry

/-! ### The massless topological black hole -/

/-- The areal radius of the massless topological black hole as a function of its tortoise coordinate,
on `x < 0`. -/
def topologicalRadius (x : ℝ) : ℝ := -(Real.cosh x / Real.sinh x)

/-- The lapse `f(r) = r² - 1`, in units of the AdS radius. -/
def topologicalLapse (r : ℝ) : ℝ := r ^ 2 - 1

/-- The radial potential `f (Q/r² + f'/r + R/6)` of the conformal scalar, where `f' = 2r` and
`R/6 = -2`. -/
def topologicalPotential (Q r : ℝ) : ℝ := topologicalLapse r * (Q / r ^ 2 + 2 * r / r - 2)

theorem topologicalLapse_radius {x : ℝ} (hx : x ≠ 0) :
    topologicalLapse (topologicalRadius x) = 1 / Real.sinh x ^ 2 := by
  have hs : Real.sinh x ≠ 0 := by rwa [Ne, Real.sinh_eq_zero]
  have h := Real.cosh_sq x
  rw [topologicalLapse, topologicalRadius]
  field_simp
  rw [h]
  ring

/-- `x` is the tortoise coordinate: `dr/dx = f(r)`. -/
theorem hasDerivAt_topologicalRadius {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt topologicalRadius (topologicalLapse (topologicalRadius x)) x := by
  have hs : Real.sinh x ≠ 0 := by rwa [Ne, Real.sinh_eq_zero]
  have hd := ((Real.hasDerivAt_cosh x).div (Real.hasDerivAt_sinh x) hs).neg
  have hval : topologicalLapse (topologicalRadius x)
      = -((Real.sinh x * Real.sinh x - Real.cosh x * Real.cosh x) / Real.sinh x ^ 2) := by
    rw [topologicalLapse_radius hx]
    have h := Real.cosh_sq x
    field_simp
    nlinarith
  rw [hval]
  exact hd

/-- **The potential is `Q sech²x`.** -/
theorem topologicalPotential_radius (Q : ℝ) {x : ℝ} (hx : x ≠ 0) :
    topologicalPotential Q (topologicalRadius x) = Q / Real.cosh x ^ 2 := by
  have hs : Real.sinh x ≠ 0 := by rwa [Ne, Real.sinh_eq_zero]
  have hc : Real.cosh x ≠ 0 := (Real.cosh_pos x).ne'
  have hr : topologicalRadius x ≠ 0 := by
    rw [topologicalRadius]
    exact neg_ne_zero.mpr (div_ne_zero hc hs)
  have hsimp : 2 * topologicalRadius x / topologicalRadius x = 2 := by
    field_simp
  rw [topologicalPotential, hsimp, topologicalLapse_radius hx, topologicalRadius]
  field_simp
  ring

/-! ### The Nariai black hole -/

/-- The lapse `1 - ρ²` of the static patch of `dS₂`, with `dS₂` and `S²` of equal radius. -/
def nariaiLapse (ρ : ℝ) : ℝ := 1 - ρ ^ 2

/-- The radial potential of the massless scalar on `dS₂ × S²`. -/
def nariaiPotential (Q ρ : ℝ) : ℝ := nariaiLapse ρ * Q

/-- `x` is the tortoise coordinate: `dρ/dx = 1 - ρ²` for `ρ = tanh x`. -/
theorem hasDerivAt_tanh_nariaiLapse (x : ℝ) :
    HasDerivAt Real.tanh (nariaiLapse (Real.tanh x)) x := by
  have hc : Real.cosh x ≠ 0 := (Real.cosh_pos x).ne'
  have hfun : Real.tanh = fun y => Real.sinh y / Real.cosh y := by
    funext y
    exact Real.tanh_eq_sinh_div_cosh y
  have hd := (Real.hasDerivAt_sinh x).div (Real.hasDerivAt_cosh x) hc
  have hval : nariaiLapse (Real.tanh x)
      = (Real.cosh x * Real.cosh x - Real.sinh x * Real.sinh x) / Real.cosh x ^ 2 := by
    rw [nariaiLapse, qnm_tanh_barrier_eq_cosh]
    have h := Real.cosh_sq x
    field_simp
    nlinarith
  rw [hval, hfun]
  exact hd

/-- **The potential is `Q sech²x`.** -/
theorem nariaiPotential_tanh (Q x : ℝ) :
    nariaiPotential Q (Real.tanh x) = Q / Real.cosh x ^ 2 := by
  rw [nariaiPotential, nariaiLapse, qnm_tanh_barrier_eq_cosh]
  ring

/-! ### The common mode -/

/-- The spectral parameter `ξ = √(Q - 1/4)` of a horizon eigenvalue. -/
def horizonSpectralParameter (Q : ℝ) : ℝ := Real.sqrt (Q - 1 / 4)

theorem horizonSpectralParameter_sq_add {Q : ℝ} (hQ : 1 / 4 ≤ Q) :
    horizonSpectralParameter Q ^ 2 + 1 / 4 = Q := by
  rw [horizonSpectralParameter, Real.sq_sqrt (by linarith)]
  ring

/-- **The ringdown mode of a horizon eigenvalue.**  Every eigenvalue `Q ≥ 1/4` has an exact solution of
`ψ_tt - ψ_xx + Q sech²x ψ = 0`. -/
theorem horizonMode_wave_equation {Q : ℝ} (hQ : 1 / 4 ≤ Q) (t x : ℝ) :
    deriv (deriv (fun u => qnmComplexHyperboloidalWave
        (qnmPoschlTellerExponent (horizonSpectralParameter Q)) 1 u x)) t -
      deriv (deriv (qnmComplexHyperboloidalWave
        (qnmPoschlTellerExponent (horizonSpectralParameter Q)) 1 t)) x +
      ((Q / Real.cosh x ^ 2 : ℝ) : ℂ) *
        qnmComplexHyperboloidalWave (qnmPoschlTellerExponent (horizonSpectralParameter Q)) 1 t x = 0 := by
  have h := qnmPoschlTeller_wave_equation (horizonSpectralParameter Q) t x
  rwa [horizonSpectralParameter_sq_add hQ] at h

/-- The mode has frequency `-ξ - i/2` in outgoing time. -/
theorem horizonMode_eq_harmonic (Q t x : ℝ) :
    qnmComplexHyperboloidalWave (qnmPoschlTellerExponent (horizonSpectralParameter Q)) 1 t x =
      qnmHarmonic (-(horizonSpectralParameter Q : ℂ) - I / 2) (t - qnmHyperboloidalHeight x) :=
  qnmPoschlTeller_wave_harmonic _ t x

/-! ### The round horizon carries no ladder of zeros -/

/-- `|√(A² - c) - A| ≤ |c|/A`. -/
theorem abs_sqrt_sq_sub_sub_le {A c : ℝ} (hA : 0 < A) (h : c ≤ A ^ 2) :
    |Real.sqrt (A ^ 2 - c) - A| ≤ |c| / A := by
  set R := Real.sqrt (A ^ 2 - c) with hR
  have hRnn : 0 ≤ R := Real.sqrt_nonneg _
  have hRsq : R ^ 2 = A ^ 2 - c := Real.sq_sqrt (by linarith)
  have hprod : |R - A| * (R + A) = |c| := by
    have hpos : 0 ≤ R + A := by linarith
    have heq : (R - A) * (R + A) = -c := by nlinarith
    rw [← abs_neg c, ← heq, abs_mul, abs_of_nonneg hpos]
  rw [le_div_iff₀ hA, ← hprod]
  exact mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)

/-- The ladder `√((l+½)² - c)` of a rigid round spectrum. -/
def roundLadder (c : ℝ) (l : ℕ) : ℝ := Real.sqrt (((l : ℝ) + 1 / 2) ^ 2 - c)

/-- **No round ladder of zeros.**  For every time scale and shift, the rigid round ladder is not
eventually a sequence of critical zero ordinates. -/
theorem not_eventually_riemannZeta_eq_zero_roundLadder {κ : ℝ} (hκ : 0 < κ) (b c : ℝ) :
    ¬ ∀ᶠ l : ℕ in atTop,
      riemannZeta (1 / 2 + ((κ * roundLadder c l + b : ℝ) : ℂ) * I) = 0 := by
  refine not_eventually_riemannZeta_critical_eq_zero_of_eikonal (Ω := κ) (b := b + κ / 2)
    (C := 2 * κ * |c|) hκ ?_
  filter_upwards [eventually_ge_atTop ⌈|c|⌉₊] with l hl
  have hlc : |c| ≤ (l : ℝ) := Nat.ceil_le.mp hl
  have hl0 : (0 : ℝ) ≤ (l : ℝ) := Nat.cast_nonneg l
  have hA : (0 : ℝ) < (l : ℝ) + 1 / 2 := by linarith
  have hc : c ≤ ((l : ℝ) + 1 / 2) ^ 2 := by
    have := le_abs_self c
    nlinarith
  have hkey := abs_sqrt_sq_sub_sub_le hA hc
  have hrw : κ * roundLadder c l + b - (b + κ / 2 + κ * (l : ℝ))
      = κ * (Real.sqrt (((l : ℝ) + 1 / 2) ^ 2 - c) - ((l : ℝ) + 1 / 2)) := by
    rw [roundLadder]
    ring
  rw [hrw, abs_mul, abs_of_pos hκ]
  have hstep : |c| / ((l : ℝ) + 1 / 2) ≤ 2 * |c| / ((l : ℝ) + 1) := by
    rw [div_le_div_iff₀ hA (by linarith)]
    nlinarith [abs_nonneg c]
  calc κ * |Real.sqrt (((l : ℝ) + 1 / 2) ^ 2 - c) - ((l : ℝ) + 1 / 2)|
      ≤ κ * (2 * |c| / ((l : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_left (hkey.trans hstep) hκ.le
    _ = 2 * κ * |c| / ((l : ℝ) + 1) := by ring

/-- **The scalar Nariai ladder.**  `Q = l(l+1)` carries no ladder of zeros at any scale. -/
theorem not_eventually_riemannZeta_eq_zero_nariaiScalar {κ : ℝ} (hκ : 0 < κ) (b : ℝ) :
    ¬ ∀ᶠ l : ℕ in atTop, riemannZeta
      (1 / 2 + ((κ * horizonSpectralParameter ((l : ℝ) * ((l : ℝ) + 1)) + b : ℝ) : ℂ) * I) = 0 := by
  have h := not_eventually_riemannZeta_eq_zero_roundLadder hκ b (1 / 2)
  intro hev
  refine h ?_
  filter_upwards [hev] with l hl
  rw [← hl, roundLadder, horizonSpectralParameter]
  congr 7
  ring

/-- **The gravitational Nariai ladder.**  `Q = (l+2)(l-1)` carries no ladder of zeros at any scale. -/
theorem not_eventually_riemannZeta_eq_zero_nariaiGravity {κ : ℝ} (hκ : 0 < κ) (b : ℝ) :
    ¬ ∀ᶠ l : ℕ in atTop, riemannZeta
      (1 / 2 + ((κ * horizonSpectralParameter (((l : ℝ) + 2) * ((l : ℝ) - 1)) + b : ℝ) : ℂ) * I)
        = 0 := by
  have h := not_eventually_riemannZeta_eq_zero_roundLadder hκ b (5 / 2)
  intro hev
  refine h ?_
  filter_upwards [hev] with l hl
  rw [← hl, roundLadder, horizonSpectralParameter]
  congr 7
  ring

end GaloisForLFunctions.BlackHoleRingdown

end
