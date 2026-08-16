import GaloisForLFunctions.RHTower.ProlateProfileWindowLimit
import GaloisForLFunctions.RHTower.HermiteOscillatorEigen

/-!
# The rescaled prolate profile converges to a Hermite function on every window

The limiting equation at the `n`-th oscillator rung is `v″ = (ξ² − (2n+1))v`, and the corpus
already carries its explicit solution: the physicists' Hermite function `hermiteFun n`.  So the
window comparison can be run against it at every rung with no limit-profile construction — the
Gaussian case `n = 0` is `hermiteFun 0`.

The normalization used here matches the initial phase vector of the Hermite function itself,
`u(0) = φ_n(0)` and `u′(0) = 0`, which avoids any nonvanishing hypothesis on `φ_n(0)`.
-/

open Set Filter Topology GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower

private theorem differentiable_probHermiteFun (n : ℕ) : Differentiable ℝ (probHermiteFun n) :=
  fun x => (hasDerivAt_probHermiteFun n x).differentiableAt

private theorem differentiable_deriv_probHermiteFun (n : ℕ) :
    Differentiable ℝ (deriv (probHermiteFun n)) := by
  rw [deriv_probHermiteFun]
  intro x
  exact ((((Polynomial.hasDerivAt_aeval (𝕜 := ℝ) (Polynomial.derivative
      (Polynomial.hermite n)) x).mul (hasDerivAt_quarterGauss x))).sub
    (((hasDerivAt_id x).div_const 2).mul (hasDerivAt_probHermiteFun n x))).differentiableAt

theorem differentiable_hermiteFun (n : ℕ) : Differentiable ℝ (hermiteFun n) := by
  intro x
  have hlin : HasDerivAt (fun y : ℝ => Real.sqrt 2 * y) (Real.sqrt 2) x := by
    simpa using (hasDerivAt_id x).const_mul (Real.sqrt 2)
  exact ((hasDerivAt_probHermiteFun n (Real.sqrt 2 * x)).comp x hlin).differentiableAt

theorem deriv_hermiteFun_eq (n : ℕ) :
    deriv (hermiteFun n) = fun x => Real.sqrt 2 * deriv (probHermiteFun n) (Real.sqrt 2 * x) :=
  funext fun x => deriv_sqrtScale 2 (probHermiteFun n) x

theorem differentiable_deriv_hermiteFun (n : ℕ) : Differentiable ℝ (deriv (hermiteFun n)) := by
  rw [deriv_hermiteFun_eq]
  intro x
  have hlin : HasDerivAt (fun y : ℝ => Real.sqrt 2 * y) (Real.sqrt 2) x := by
    simpa using (hasDerivAt_id x).const_mul (Real.sqrt 2)
  have hcomp := ((differentiable_deriv_probHermiteFun n (Real.sqrt 2 * x)).hasDerivAt.comp
    x hlin)
  exact (hcomp.const_mul (Real.sqrt 2)).differentiableAt

theorem hasDerivAt_hermiteFun (n : ℕ) (x : ℝ) :
    HasDerivAt (hermiteFun n) (deriv (hermiteFun n) x) x :=
  (differentiable_hermiteFun n x).hasDerivAt

/-- The Hermite function solves the rung-`n` limiting equation in the exact normal form used by
the window comparison. -/
theorem hasDerivAt_deriv_hermiteFun (n : ℕ) (x : ℝ) :
    HasDerivAt (deriv (hermiteFun n)) (hermiteRungP n x * hermiteFun n x) x := by
  have h := (differentiable_deriv_hermiteFun n x).hasDerivAt
  refine h.congr_deriv ?_
  rw [deriv2_hermiteFun, hermiteRungP]
  ring

/-- For even index the Hermite polynomial is an even function. -/
theorem aeval_hermite_neg_of_even {n : ℕ} (hn : Even n) (x : ℝ) :
    Polynomial.aeval (-x) (Polynomial.hermite n) = Polynomial.aeval x (Polynomial.hermite n) := by
  rw [Polynomial.aeval_eq_sum_range, Polynomial.aeval_eq_sum_range]
  refine Finset.sum_congr rfl fun k _ => ?_
  rcases Nat.even_or_odd k with hke | hko
  · rw [hke.neg_pow]
  · have hz : (Polynomial.hermite n).coeff k = 0 :=
      Polynomial.coeff_hermite_of_odd_add (hn.add_odd hko)
    rw [hz]
    simp

/-- The Hermite function of even index is even. -/
theorem even_hermiteFun {n : ℕ} (hn : Even n) : Function.Even (hermiteFun n) := by
  intro x
  have hp : Polynomial.aeval (Real.sqrt 2 * -x) (Polynomial.hermite n)
      = Polynomial.aeval (Real.sqrt 2 * x) (Polynomial.hermite n) := by
    have hrw : Real.sqrt 2 * -x = -(Real.sqrt 2 * x) := by ring
    rw [hrw]
    exact aeval_hermite_neg_of_even hn _
  show probHermiteFun n (Real.sqrt 2 * -x) = probHermiteFun n (Real.sqrt 2 * x)
  rw [probHermiteFun, probHermiteFun, hp]
  congr 2
  ring

@[simp]
theorem deriv_hermiteFun_zero_of_even {n : ℕ} (hn : Even n) : deriv (hermiteFun n) 0 = 0 := by
  have hfun : (fun y : ℝ => hermiteFun n (-y)) = hermiteFun n := funext (even_hermiteFun hn)
  have h := congrArg (fun f : ℝ → ℝ => deriv f 0) hfun
  rw [deriv_comp_neg] at h
  have hneg : -deriv (hermiteFun n) 0 = deriv (hermiteFun n) 0 := by simpa using h
  linarith

/-- **Window comparison at the `n`-th rung.**  A solution of the rescaled prolate equation whose
initial phase vector matches that of the `n`-th Hermite function stays within the explicit
Grönwall envelope of it on `[0, K]`. -/
theorem prolateProfile_window_hermiteRung_dist_le
    {c mu K B : ℝ} {n : ℕ} {u u' u'' : ℝ → ℝ}
    (hK : 0 < K) (hcK : 2 * K ^ 2 ≤ c)
    (hu : ∀ x, HasDerivAt u (u' x) x) (hu' : ∀ x, HasDerivAt u' (u'' x) x)
    (hequ : ∀ x ∈ Icc (0 : ℝ) K,
      u'' x = rescaledProlateP c mu x * u x + rescaledProlateQ c x * u' x)
    (hB : ∀ x ∈ Icc (0 : ℝ) K, max |u x| |u' x| ≤ B)
    (h0 : u 0 = hermiteFun n 0) (h0' : u' 0 = deriv (hermiteFun n) 0) :
    ∀ x ∈ Icc (0 : ℝ) K, max |u x - hermiteFun n x| |u' x - deriv (hermiteFun n) x|
      ≤ ((prolateWindowEpsP c mu K n + prolateWindowEpsQ c K) * B
          / max 1 (hermiteWindowBound K n))
        * (Real.exp (max 1 (hermiteWindowBound K n) * (K - 0)) - 1) :=
  prolateProfile_window_dist_le hK hcK hu hu' (hasDerivAt_hermiteFun n)
    (hasDerivAt_deriv_hermiteFun n) hequ (fun _ _ => rfl) hB h0 h0'

/-- **Convergence to the `n`-th Hermite function on the window.**  Once the bandwidth escapes and
the separation constant approaches the `n`-th rung, the rescaled profile normalized to the Hermite
initial phase vector converges to `φ_n` pointwise on `[0, K]`. -/
theorem tendsto_prolateProfile_hermiteRung
    {ι : Type*} {L : Filter ι} {mu c : ι → ℝ} {K B : ℝ} {n : ℕ}
    {u u' u'' : ι → ℝ → ℝ}
    (hK : 0 < K) (hcK : ∀ i, 2 * K ^ 2 ≤ c i)
    (hu : ∀ i x, HasDerivAt (u i) (u' i x) x) (hu' : ∀ i x, HasDerivAt (u' i) (u'' i x) x)
    (hequ : ∀ i, ∀ x ∈ Icc (0 : ℝ) K,
      u'' i x = rescaledProlateP (c i) (mu i) x * u i x + rescaledProlateQ (c i) x * u' i x)
    (hB : ∀ i, ∀ x ∈ Icc (0 : ℝ) K, max |u i x| |u' i x| ≤ B)
    (h0 : ∀ i, u i 0 = hermiteFun n 0) (h0' : ∀ i, u' i 0 = deriv (hermiteFun n) 0)
    (hmu : Tendsto mu L (𝓝 (2 * (n : ℝ) + 1))) (hc : Tendsto c L atTop) :
    ∀ x ∈ Icc (0 : ℝ) K, Tendsto (fun i => u i x) L (𝓝 (hermiteFun n x)) :=
  tendsto_prolateProfile_window hK hcK hu hu' (hasDerivAt_hermiteFun n)
    (hasDerivAt_deriv_hermiteFun n) hequ (fun _ _ => rfl) hB h0 h0' hmu hc

end RHTower
