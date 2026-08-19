import GaloisForLFunctions.RHTower.SoninSemilocalTwoPlaceAssociation
import GaloisForLFunctions.HTGeometry.GammaCyclicSpectralMeasure
import GaloisForLFunctions.HTGeometry.CharacteristicFunctionPositiveDefinite

/-!
# Positive semidefiniteness of the Gamma-damped stationary prime-log covariance

`SoninSemilocalTwoPlaceAssociation` constructs the diagonally damped stationary Gamma covariance

```text
d(t) = sqrt (phi (2 t)),   K_Gamma (t, u) = d(t) d(u) phi (t - u),   phi (t) = (cosh t)^(-1/2)
```

and proves strict entry positivity, the diagonal identity `K_Gamma(t,t) = phi(2t)`, and the
exponential upper bound `phi(2t) ≤ sqrt 2 · exp(-t)`.  This module closes the remaining
finite-matrix gate: the sewn kernel is genuinely **positive semidefinite**, not merely
entrywise positive.

The mechanism is diagonal congruence of a stationary positive kernel.  The corpus already owns
both halves needed:

* `HTGeometry.gammaCyclicMeasure` — the archimedean cyclic spectral probability measure with
  `∫ exp(i h y) dν = (cosh h)^(-1/2)`;
* `GaloisForLFunctions.HTGeometry.positiveDefiniteOnReal_charFun` — every probability
  characteristic function has a nonnegative finite Gram form.

Combining them gives `charFun_gammaCyclicMeasure`,
`positiveDefiniteOnReal_semilocalArchimedeanCharacteristic`, and then
`semilocalArchimedeanDampedCovarianceKernel_posSemidef` by absorbing the real diagonal damping
into the coefficients.

Also proved here:

* `exp_neg_le_semilocalArchimedeanCharacteristic_two_mul` — the lower half of the two-sided
  diagonal decay `exp(-t) ≤ phi(2t) ≤ sqrt 2 · exp(-t)` for `t ≥ 0`: the diagonal supplies
  exactly one full exponential power, no more and no less.
* `semilocalArchimedeanCharacteristic_two_mul_log_le` — the prime-log form `phi(2 log p) ≤ √2/p`
  that makes the critical-half-weight Cauchy feature summable.
* `semilocalArchimedeanDampedCovariance_gram_strict_superadditive` — the exact additivity
  obstruction: strictly positive cross terms make the coherent Gram energy strictly exceed the
  sum of the diagonal energies, so it cannot be identified with the additive Euler logarithmic
  derivative, which has no pairwise prime-power terms.

Nothing here is an RH statement.  Characteristic-function positivity and diagonal kernel
congruence are classical; the content is that this specific source-built kernel crosses the
prime-log half-weight while remaining positive, and that it cannot be collapsed additively.
-/

open MeasureTheory
open scoped ComplexConjugate

namespace RHTower

noncomputable section

lemma semilocalArchimedeanCharacteristic_eq_rpow (t : ℝ) :
    semilocalArchimedeanCharacteristic t = Real.cosh t ^ (-(1 / 2) : ℝ) := by
  dsimp [semilocalArchimedeanCharacteristic]
  norm_num

lemma semilocalArchimedeanCharacteristic_neg (x : ℝ) :
    semilocalArchimedeanCharacteristic (-x) = semilocalArchimedeanCharacteristic x := by
  dsimp [semilocalArchimedeanCharacteristic]
  rw [Real.cosh_neg]

/-- The Gamma characteristic is literally the characteristic function of the corpus's archimedean
cyclic spectral measure. -/
theorem charFun_gammaCyclicMeasure (t : ℝ) :
    charFun HTGeometry.gammaCyclicMeasure t = (semilocalArchimedeanCharacteristic t : ℂ) := by
  rw [charFun_apply_real]
  have hcongr : ∀ x : ℝ,
      Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I)
        = Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) := by
    intro x
    push_cast
    ring_nf
  simp_rw [hcongr]
  rw [HTGeometry.integral_exp_gammaCyclicMeasure t, semilocalArchimedeanCharacteristic_eq_rpow]

/-- **The archimedean Gamma characteristic is positive definite.** -/
theorem positiveDefiniteOnReal_semilocalArchimedeanCharacteristic :
    GaloisForLFunctions.HTGeometry.PositiveDefiniteOnReal
      (fun t => (semilocalArchimedeanCharacteristic t : ℂ)) := by
  intro N t c
  obtain ⟨r, hr, hsum⟩ :=
    GaloisForLFunctions.HTGeometry.positiveDefiniteOnReal_charFun
      HTGeometry.gammaCyclicMeasure N t c
  refine ⟨r, hr, ?_⟩
  rw [← hsum]
  exact Finset.sum_congr rfl fun i _ =>
    Finset.sum_congr rfl fun j _ => by rw [charFun_gammaCyclicMeasure]

/-- **The diagonally damped stationary Gamma covariance is positive semidefinite.**
This is the finite-matrix form of `(2)`: the Gram form of the sewn kernel is the archimedean
`L²` energy of the damped Fourier packet, hence nonnegative. -/
theorem semilocalArchimedeanDampedCovarianceKernel_posSemidef
    (N : ℕ) (t : Fin N → ℝ) (c : Fin N → ℂ) :
    ∃ r : ℝ, 0 ≤ r ∧
      ∑ i, ∑ j, star (c i) *
          (semilocalArchimedeanDampedCovarianceKernel (t i) (t j) : ℂ) * c j = (r : ℂ) := by
  set d : ℝ → ℝ := fun s => Real.sqrt (semilocalArchimedeanCharacteristic (2 * s)) with hd
  obtain ⟨r, hr, hsum⟩ :=
    positiveDefiniteOnReal_semilocalArchimedeanCharacteristic N t (fun i => c i * (d (t i) : ℂ))
  refine ⟨r, hr, ?_⟩
  rw [← hsum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have hker : semilocalArchimedeanDampedCovarianceKernel (t i) (t j)
      = d (t i) * d (t j) * semilocalArchimedeanCharacteristic (t j - t i) := by
    dsimp [semilocalArchimedeanDampedCovarianceKernel, hd]
    rw [show t i - t j = -(t j - t i) from by ring, semilocalArchimedeanCharacteristic_neg]
  rw [hker]
  push_cast
  rw [star_mul', Complex.star_def, Complex.conj_ofReal]
  ring

/-- **Exact exponential diagonal decay, lower half.**  `exp(-t) ≤ phi(2t)` for `t ≥ 0`. -/
theorem exp_neg_le_semilocalArchimedeanCharacteristic_two_mul {t : ℝ} (ht : 0 ≤ t) :
    Real.exp (-t) ≤ semilocalArchimedeanCharacteristic (2 * t) := by
  have hcosh : Real.cosh (2 * t) ≤ Real.exp (2 * t) := by
    rw [Real.cosh_eq]
    have h1 : Real.exp (-(2 * t)) ≤ Real.exp (2 * t) := Real.exp_le_exp.mpr (by linarith)
    linarith
  have hpos : (0 : ℝ) < Real.cosh (2 * t) := Real.cosh_pos _
  have hpow := Real.rpow_le_rpow_of_nonpos hpos hcosh (by norm_num : (-(1 : ℝ) / 2) ≤ 0)
  have hrewrite : Real.exp (-t) = Real.exp (2 * t) ^ (-(1 : ℝ) / 2) := by
    rw [← Real.exp_mul]
    congr 1
    ring
  dsimp [semilocalArchimedeanCharacteristic]
  rw [hrewrite]
  exact hpow

/-- The critical-half-weight prime-log form of the exponential diagonal bound:
`phi(2 log p) ≤ sqrt 2 / p`. -/
theorem semilocalArchimedeanCharacteristic_two_mul_log_le {p : ℝ} (hp : 0 < p) :
    semilocalArchimedeanCharacteristic (2 * Real.log p) ≤ Real.sqrt 2 / p := by
  have h := semilocalArchimedeanCharacteristic_two_mul_le_sqrtTwo_mul_exp_neg (Real.log p)
  rwa [Real.exp_neg, Real.exp_log hp, ← div_eq_mul_inv] at h

/-- **Exact additivity obstruction.**  Every cross entry of the sewn covariance is strictly
positive, so the coherent Gram energy of two distinct prime-power atoms with positive amplitudes
strictly exceeds the sum of the two diagonal energies.  Hence the Gram energy cannot equal the
additive Euler logarithmic derivative, which has no pairwise prime-power terms. -/
theorem semilocalArchimedeanDampedCovariance_gram_strict_superadditive
    (t u : ℝ) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    a ^ 2 * semilocalArchimedeanDampedCovarianceKernel t t
        + b ^ 2 * semilocalArchimedeanDampedCovarianceKernel u u
      < a ^ 2 * semilocalArchimedeanDampedCovarianceKernel t t
        + b ^ 2 * semilocalArchimedeanDampedCovarianceKernel u u
        + 2 * a * b * semilocalArchimedeanDampedCovarianceKernel t u := by
  have hpos := semilocalArchimedeanDampedCovarianceKernel_pos t u
  have hcross : 0 < 2 * a * b * semilocalArchimedeanDampedCovarianceKernel t u :=
    mul_pos (mul_pos (by linarith : (0 : ℝ) < 2 * a) hb) hpos
  linarith

end

end RHTower
