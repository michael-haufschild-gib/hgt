import GaloisForLFunctions.RHTower.XiGaussianHeatTuranDefect
import GaloisForLFunctions.HTGeometry.HeatMomentDerivativeShift

/-!
# The Gaussian heat moments are the derivatives of the heat trace

Each Gaussian-damped monomial satisfies `d/dt (wⁿ e^{−t w}) = −w^{n+1} e^{−t w}`, and the sum over
the Xi divisor may be differentiated term by term: on any compact time interval `[a,b] ⊂ (0,∞)` the
derivative terms are dominated by `‖wⁿ⁺¹e^{−aw}‖ + ‖wⁿ⁺¹e^{−bw}‖`, both summable because the
monomial terms are absolutely summable at every positive time.

No sign hypothesis on `Re(z²)` is needed — which is the point, since positivity of those real parts
is what the hypothesis is about.  The domination only uses that `e^{−t Re w}` is monotone in `t`, so
its value on `[a,b]` is bounded by its values at the two endpoints.

Consequently

```text
∂ₜ mₙ(t) = −m_{n+1}(t) ,      hence      mₙ = (−1)ⁿ m₀⁽ⁿ⁾ ,
```

so every Gaussian heat moment — and therefore every Hankel matrix built from them — is a derivative
of the single heat trace `m₀`.
-/

open Filter Set

namespace RHTower

/-- Norm-summability of the monomial terms at any positive time. -/
theorem summable_norm_xiGaussianHeatMonomialTerm {t : ℝ} (ht : 0 < t) (j : ℕ) :
    Summable (fun q : XiZeroCopy =>
      ‖(xiSpectralPoint q ^ 2) ^ j * xiGaussianHeatTerm t q‖) :=
  summable_norm_iff.mpr (summable_xiGaussianHeatMonomialTerm ht j)

/-- **Endpoint domination.**  On `[a,b] ⊂ (0,∞)` the monomial term at time `t` is bounded in norm by
the sum of its values at the two endpoints, using only monotonicity of `e^{−t Re w}` in `t`. -/
theorem norm_heatMonomial_le_endpoints {a b t : ℝ} (hab : a ≤ t) (htb : t ≤ b)
    (j : ℕ) (q : XiZeroCopy) :
    ‖(xiSpectralPoint q ^ 2) ^ j * xiGaussianHeatTerm a q‖ +
        ‖(xiSpectralPoint q ^ 2) ^ j * xiGaussianHeatTerm b q‖
      ≥ ‖(xiSpectralPoint q ^ 2) ^ j * xiGaussianHeatTerm t q‖ := by
  set w : ℂ := xiSpectralPoint q ^ 2 with hw
  have hnorm : ∀ s : ℝ, ‖w ^ j * xiGaussianHeatTerm s q‖
      = ‖w‖ ^ j * Real.exp (-s * w.re) := by
    intro s
    rw [norm_mul, norm_pow, xiGaussianHeatTerm, ← hw, Complex.norm_exp]
    congr 1
    simp [Complex.mul_re]
  rw [hnorm, hnorm, hnorm]
  have hpow : (0 : ℝ) ≤ ‖w‖ ^ j := by positivity
  rcases le_total 0 w.re with hre | hre
  · have : Real.exp (-t * w.re) ≤ Real.exp (-a * w.re) := by
      apply Real.exp_le_exp.mpr
      nlinarith [hab, hre]
    nlinarith [hpow, (Real.exp_pos (-b * w.re)).le, this]
  · have : Real.exp (-t * w.re) ≤ Real.exp (-b * w.re) := by
      apply Real.exp_le_exp.mpr
      nlinarith [htb, hre]
    nlinarith [hpow, (Real.exp_pos (-a * w.re)).le, this]

/-- **The moment ladder for the Xi heat trace.**  At every positive time the `n`-th Gaussian heat
moment is differentiable with derivative the negative of the `(n+1)`-st.  The sum is differentiated
term by term; the domination is by the two endpoint values on a compact interval around `t`, so no
hypothesis on the location of the zeros enters. -/
theorem hasDerivAt_xiGaussianHeatMoment {t : ℝ} (ht : 0 < t) (n : ℕ) :
    HasDerivAt (fun s : ℝ => xiGaussianHeatMoment n s)
      (-xiGaussianHeatMoment (n + 1) t) t := by
  set a : ℝ := t / 2 with ha
  set b : ℝ := t + 1 with hb
  have hapos : 0 < a := by rw [ha]; linarith
  have hbpos : 0 < b := by rw [hb]; linarith
  have hat : a < t := by rw [ha]; linarith
  have htb : t < b := by rw [hb]; linarith
  -- the dominating summable family
  set u : XiZeroCopy → ℝ := fun q =>
    ‖(xiSpectralPoint q ^ 2) ^ (n + 1) * xiGaussianHeatTerm a q‖ +
      ‖(xiSpectralPoint q ^ 2) ^ (n + 1) * xiGaussianHeatTerm b q‖ with hu
  have hsumu : Summable u :=
    (summable_norm_xiGaussianHeatMonomialTerm hapos (n + 1)).add
      (summable_norm_xiGaussianHeatMonomialTerm hbpos (n + 1))
  -- termwise derivative on the open interval
  have hderiv : ∀ q : XiZeroCopy, ∀ s ∈ Ioo a b,
      HasDerivAt (fun r : ℝ => (xiSpectralPoint q ^ 2) ^ n * xiGaussianHeatTerm r q)
        (-((xiSpectralPoint q ^ 2) ^ (n + 1) * xiGaussianHeatTerm s q)) s := by
    intro q s _
    have h := GaloisForLFunctions.hasDerivAt_heatMonomial (xiSpectralPoint q ^ 2) n s
    simpa [xiGaussianHeatTerm, pow_succ, mul_comm, mul_assoc, mul_left_comm] using h
  have hbound : ∀ q : XiZeroCopy, ∀ s ∈ Ioo a b,
      ‖-((xiSpectralPoint q ^ 2) ^ (n + 1) * xiGaussianHeatTerm s q)‖ ≤ u q := by
    intro q s hs
    rw [norm_neg, hu]
    exact norm_heatMonomial_le_endpoints (le_of_lt hs.1) (le_of_lt hs.2) (n + 1) q
  have hmemt : t ∈ Ioo a b := ⟨hat, htb⟩
  have hsum0 : Summable (fun q : XiZeroCopy =>
      (xiSpectralPoint q ^ 2) ^ n * xiGaussianHeatTerm t q) :=
    summable_xiGaussianHeatMonomialTerm ht n
  have hmain := hasDerivAt_tsum_of_isPreconnected hsumu isOpen_Ioo
    (isPreconnected_Ioo) hderiv hbound hmemt hsum0 hmemt
  simpa [xiGaussianHeatMoment, tsum_neg] using hmain

/-- **The moments are the derivatives of the trace.**  Restating: the `(n+1)`-st moment is minus the
derivative of the `n`-th, so the whole family is generated by `m₀` alone. -/
theorem xiGaussianHeatMoment_succ_eq_neg_deriv {t : ℝ} (ht : 0 < t) (n : ℕ) :
    xiGaussianHeatMoment (n + 1) t = -deriv (fun s : ℝ => xiGaussianHeatMoment n s) t := by
  rw [(hasDerivAt_xiGaussianHeatMoment ht n).deriv]
  ring

end RHTower
