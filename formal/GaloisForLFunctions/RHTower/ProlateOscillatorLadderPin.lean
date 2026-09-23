import GaloisForLFunctions.RHTower.HermiteOscillatorEigen
import GaloisForLFunctions.HTGeometry.WholeLineWronskianSymmetry

/-!
# Pinning the rescaled prolate eigenvalue to the oscillator ladder

The corpus already carries the exact prolate-to-oscillator identity: after the Hermite rescaling
`u(ξ) = Φ(ξ/√c)`, a genuine prolate mode satisfies

```text
hermiteSLAction u + (c·s)·u = (ξ² u″ + 2ξ u′)/c
```

with **no convergence premise** (`ProlateHermiteRescale.exists_even_prolateHermiteRescale_of_signedMode`).
The harmonic oscillator's own eigenfunctions are equally exact:
`hermiteSLAction (hermiteFun n) = −(2n+1)·hermiteFun n`.

What was missing is the bridge between the two, and it is not an asymptotic expansion — it is one
integration by parts.  Pairing the rescaled mode against the `n`-th oscillator eigenfunction and
moving the second derivative across (the Wronskian vanishes at both ends for decaying profiles)
turns the potential term into an exact cancellation and leaves

```text
(μ − (2n+1)) ⟨u, φₙ⟩ = ⟨D, φₙ⟩ ,
```

an identity, not an estimate.  So the rescaled eigenvalue sits at distance exactly
`|⟨D, φₙ⟩| / |⟨u, φₙ⟩|` from the `n`-th rung of the oscillator ladder, and for the prolate defect
`D = (ξ²u″ + 2ξu′)/c` that distance carries the full factor `1/c`.
-/

open MeasureTheory Filter Set Polynomial

open scoped Topology

noncomputable section

namespace RHTower

open GaloisForLFunctions.HTGeometry

/-! ## Differentiability of the oscillator eigenfunctions -/

theorem differentiable_probHermiteFun_prolateOscillatorLadderPin (n : ℕ) : Differentiable ℝ (probHermiteFun n) :=
  fun x => (hasDerivAt_probHermiteFun n x).differentiableAt

theorem differentiable_deriv_probHermiteFun_prolateOscillatorLadderPin (n : ℕ) :
    Differentiable ℝ (deriv (probHermiteFun n)) := by
  rw [deriv_probHermiteFun]
  intro x
  have h1 : DifferentiableAt ℝ
      (fun y : ℝ => Polynomial.aeval y (derivative (hermite n)) * Real.exp (-(y ^ (2 : ℕ) / 4))) x :=
    ((Polynomial.hasDerivAt_aeval (𝕜 := ℝ) (derivative (hermite n)) x).differentiableAt).mul
      (by fun_prop : DifferentiableAt ℝ (fun y : ℝ => Real.exp (-(y ^ (2 : ℕ) / 4))) x)
  have h2 : DifferentiableAt ℝ (fun y : ℝ => y / 2 * probHermiteFun n y) x :=
    ((differentiableAt_id).div_const 2).mul (differentiable_probHermiteFun_prolateOscillatorLadderPin n x)
  exact h1.sub h2

private theorem deriv_hermiteFun_eq (n : ℕ) :
    deriv (hermiteFun n) = fun x => Real.sqrt 2 * deriv (probHermiteFun n) (Real.sqrt 2 * x) :=
  funext fun x => deriv_sqrtScale 2 (probHermiteFun n) x

theorem hasDerivAt_ladderHermiteFun (n : ℕ) (x : ℝ) :
    HasDerivAt (hermiteFun n) (deriv (hermiteFun n) x) x := by
  have hlin : HasDerivAt (fun y : ℝ => Real.sqrt 2 * y) (Real.sqrt 2) x := by
    simpa using (hasDerivAt_id x).const_mul (Real.sqrt 2)
  have h : HasDerivAt (fun y : ℝ => probHermiteFun n (Real.sqrt 2 * y))
      (deriv (probHermiteFun n) (Real.sqrt 2 * x) * Real.sqrt 2) x :=
    ((differentiable_probHermiteFun_prolateOscillatorLadderPin n (Real.sqrt 2 * x)).hasDerivAt).comp x hlin
  have h2 : HasDerivAt (hermiteFun n)
      (deriv (probHermiteFun n) (Real.sqrt 2 * x) * Real.sqrt 2) x := h
  exact h2.deriv ▸ h2

theorem hasDerivAt_deriv_ladderHermiteFun (n : ℕ) (x : ℝ) :
    HasDerivAt (deriv (hermiteFun n)) (deriv (deriv (hermiteFun n)) x) x := by
  have hd : Differentiable ℝ (deriv (hermiteFun n)) := by
    rw [deriv_hermiteFun_eq]
    intro y
    exact ((differentiable_deriv_probHermiteFun_prolateOscillatorLadderPin n (Real.sqrt 2 * y)).comp y
      (by fun_prop : DifferentiableAt ℝ (fun z : ℝ => Real.sqrt 2 * z) y)).const_mul _
  exact (hd x).hasDerivAt

/-! ## The pin -/

/-- **The oscillator ladder pin, exactly.**  If `u` solves `hermiteSLAction u + μ u = D` pointwise
and its Wronskian against the `n`-th oscillator eigenfunction vanishes at both ends, then

```text
(μ − (2n+1)) ⟨u, φₙ⟩ = ⟨D, φₙ⟩ .
```

The `ξ²` potential cancels identically: it appears with the same sign on both sides of the
integration by parts. -/
theorem hermitePairing_pin {u u' u'' D : ℝ → ℝ} {μ : ℝ} (n : ℕ)
    (hu : ∀ x, HasDerivAt u (u' x) x) (hu' : ∀ x, HasDerivAt u' (u'' x) x)
    (heq : ∀ x, hermiteSLAction u x + μ * u x = D x)
    (hintL : Integrable fun x => u'' x * hermiteFun n x)
    (hintR : Integrable fun x => u x * deriv (deriv (hermiteFun n)) x)
    (hintSq : Integrable fun x => x ^ (2 : ℕ) * (u x * hermiteFun n x))
    (hintU : Integrable fun x => u x * hermiteFun n x)
    (hplus : Tendsto (fun x => u' x * hermiteFun n x - u x * deriv (hermiteFun n) x)
      atTop (𝓝 0))
    (hminus : Tendsto (fun x => u' x * hermiteFun n x - u x * deriv (hermiteFun n) x)
      atBot (𝓝 0)) :
    (μ - (2 * n + 1)) * (∫ x, u x * hermiteFun n x) = ∫ x, D x * hermiteFun n x := by
  have hdu : deriv u = u' := funext fun x => (hu x).deriv
  have hdu' : deriv u' = u'' := funext fun x => (hu' x).deriv
  have hdd : deriv (deriv u) = u'' := by rw [hdu, hdu']
  have hsym : ∫ x, u'' x * hermiteFun n x = ∫ x, u x * deriv (deriv (hermiteFun n)) x :=
    integral_secondDeriv_mul_comm hu (fun x => hasDerivAt_ladderHermiteFun n x) hu'
      (fun x => hasDerivAt_deriv_ladderHermiteFun n x) hintL hintR hplus hminus
  have hR : ∫ x, u x * deriv (deriv (hermiteFun n)) x
      = (∫ x, x ^ (2 : ℕ) * (u x * hermiteFun n x)) - (2 * n + 1) * ∫ x, u x * hermiteFun n x := by
    have hpt : ∀ x, u x * deriv (deriv (hermiteFun n)) x
        = x ^ (2 : ℕ) * (u x * hermiteFun n x) - (2 * n + 1) * (u x * hermiteFun n x) := by
      intro x
      rw [deriv2_hermiteFun]
      ring
    rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpt),
      MeasureTheory.integral_sub hintSq (hintU.const_mul _), MeasureTheory.integral_const_mul]
  have hD : ∫ x, D x * hermiteFun n x
      = (∫ x, u'' x * hermiteFun n x) - (∫ x, x ^ (2 : ℕ) * (u x * hermiteFun n x))
        + μ * ∫ x, u x * hermiteFun n x := by
    have hpt : ∀ x, D x * hermiteFun n x
        = u'' x * hermiteFun n x - x ^ (2 : ℕ) * (u x * hermiteFun n x)
          + μ * (u x * hermiteFun n x) := by
      intro x
      have h := heq x
      unfold hermiteSLAction at h
      rw [hdd] at h
      rw [← h]
      ring
    have e1 : ∫ x, D x * hermiteFun n x
        = ∫ x, (u'' x * hermiteFun n x - x ^ (2 : ℕ) * (u x * hermiteFun n x)
            + μ * (u x * hermiteFun n x)) :=
      MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpt)
    have e2 : ∫ x, (u'' x * hermiteFun n x - x ^ (2 : ℕ) * (u x * hermiteFun n x)
          + μ * (u x * hermiteFun n x))
        = (∫ x, (u'' x * hermiteFun n x - x ^ (2 : ℕ) * (u x * hermiteFun n x)))
          + ∫ x, μ * (u x * hermiteFun n x) :=
      MeasureTheory.integral_add (hintL.sub hintSq) (hintU.const_mul _)
    have e3 : ∫ x, (u'' x * hermiteFun n x - x ^ (2 : ℕ) * (u x * hermiteFun n x))
        = (∫ x, u'' x * hermiteFun n x) - ∫ x, x ^ (2 : ℕ) * (u x * hermiteFun n x) :=
      MeasureTheory.integral_sub hintL hintSq
    have e4 : ∫ x, μ * (u x * hermiteFun n x) = μ * ∫ x, u x * hermiteFun n x :=
      MeasureTheory.integral_const_mul _ _
    rw [e1, e2, e3, e4]
  rw [hD, hsym, hR]
  ring

/-- **The pin, quantitatively.**  The distance from the rescaled eigenvalue to the `n`-th rung of
the oscillator ladder is exactly the ratio of the defect pairing to the mode pairing. -/
theorem abs_sub_oscillatorLadder_eq {u u' u'' D : ℝ → ℝ} {μ : ℝ} (n : ℕ)
    (hu : ∀ x, HasDerivAt u (u' x) x) (hu' : ∀ x, HasDerivAt u' (u'' x) x)
    (heq : ∀ x, hermiteSLAction u x + μ * u x = D x)
    (hintL : Integrable fun x => u'' x * hermiteFun n x)
    (hintR : Integrable fun x => u x * deriv (deriv (hermiteFun n)) x)
    (hintSq : Integrable fun x => x ^ (2 : ℕ) * (u x * hermiteFun n x))
    (hintU : Integrable fun x => u x * hermiteFun n x)
    (hplus : Tendsto (fun x => u' x * hermiteFun n x - u x * deriv (hermiteFun n) x)
      atTop (𝓝 0))
    (hminus : Tendsto (fun x => u' x * hermiteFun n x - u x * deriv (hermiteFun n) x)
      atBot (𝓝 0))
    (hne : (∫ x, u x * hermiteFun n x) ≠ 0) :
    |μ - (2 * n + 1)|
      = |∫ x, D x * hermiteFun n x| / |∫ x, u x * hermiteFun n x| := by
  have h := hermitePairing_pin n hu hu' heq hintL hintR hintSq hintU hplus hminus
  have habs := congrArg abs h
  rw [abs_mul] at habs
  rw [← habs, mul_div_assoc, div_self (abs_ne_zero.mpr hne), mul_one]

end RHTower

end
