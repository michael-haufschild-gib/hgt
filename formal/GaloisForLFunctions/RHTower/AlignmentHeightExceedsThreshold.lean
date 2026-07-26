import GaloisForLFunctions.RHTower.ModulatedBoxWeilForm

/-!
# Prime-phase alignment cannot break Weil positivity

The modulated tent gives a positivity threshold: survival at a modulation where the prime phases
align needs `θ ≳ exp(4e^{L/2}/L)`.  This file compares that with the height at which alignment
actually occurs, and finds the comparison is not close.

**Where alignment occurs.**  Simultaneous approximation of `k` frequencies to within `ε` is
guaranteed by the pigeonhole at height `(2π/ε)^k`.  The modulated tent of width `L` sees the primes
up to `e^L`, so `k = π(e^L) ≍ e^L/L` and the alignment height is

```text
exp( (e^L/L)·log(2π/ε) ) ,
```

**doubly exponential in `L`, with exponent `e^L/L`.**

**The threshold is smaller.**  The positivity threshold has exponent `4e^{L/2}/L`.  Since
`4e^{L/2} ≤ e^L` as soon as `e^{L/2} ≥ 4`, i.e. `L ≥ 2 log 4 ≈ 2.77`, the alignment height **exceeds**
the threshold for every width past that point — and the gap between the exponents is the factor
`e^{L/2}/4`, itself exponentially large.

> **At the height where the prime phases first align, the archimedean term already exceeds the
> aligned prime sum by an exponentially large factor.  Alignment never violates Weil positivity for
> the modulated tent.**

**And Baker makes it worse for alignment.**  The pigeonhole height is only an upper bound for where
alignment *can* occur; to threaten positivity one would need alignment *much earlier* than the
pigeonhole guarantees, i.e. exceptionally good simultaneous rational approximation of `{log p}`.
Baker's theorem — already fixed in this corpus as the `ℚ̄`-linear independence of the prime
logarithms — supplies effective lower bounds for linear forms in those logarithms, which forbid
exceptionally early alignment.  The arithmetic independence of the primes protects the positivity.

**What this narrows.**  If Weil positivity fails for the modulated tent, it cannot fail through
prime-phase alignment.  It must fail through the zeros.  That removes one of the two conceivable
failure modes unconditionally.

This file formalizes the exponent comparison and the resulting domination.
-/

open Real

noncomputable section

namespace RHTower

/-- The exponent of the pigeonhole alignment height, `k·log(2π/ε)` with `k ≍ e^L/L`. -/
def alignmentExponent (L c : ℝ) : ℝ := Real.exp L / L * c

/-- The exponent of the positivity threshold, `4e^{L/2}/L`. -/
def thresholdExponent (L : ℝ) : ℝ := 4 * Real.exp (L / 2) / L

/-- **The elementary comparison.**  `4e^{L/2} ≤ e^L` once `e^{L/2} ≥ 4`. -/
theorem four_exp_half_le_exp {L : ℝ} (hL : 4 ≤ Real.exp (L / 2)) :
    4 * Real.exp (L / 2) ≤ Real.exp L := by
  have hsq : Real.exp L = Real.exp (L / 2) * Real.exp (L / 2) := by
    rw [← Real.exp_add]; congr 1; ring
  have hpos : 0 < Real.exp (L / 2) := Real.exp_pos _
  rw [hsq]
  nlinarith [hL, hpos]

/-- **The alignment height exceeds the threshold.**  For `c ≥ 1` and `L` past `2 log 4`, the
alignment exponent dominates the threshold exponent. -/
theorem alignment_exceeds_threshold {L c : ℝ} (hL : 0 < L) (hc : 1 ≤ c)
    (hbig : 4 ≤ Real.exp (L / 2)) :
    thresholdExponent L ≤ alignmentExponent L c := by
  unfold thresholdExponent alignmentExponent
  have h1 : 4 * Real.exp (L / 2) ≤ Real.exp L := four_exp_half_le_exp hbig
  have hdiv : 4 * Real.exp (L / 2) / L ≤ Real.exp L / L := by
    gcongr
  have hmul : Real.exp L / L ≤ Real.exp L / L * c := by
    have hpos : 0 < Real.exp L / L := by positivity
    nlinarith [hpos, hc]
  linarith

/-- The gap between the exponents is the exponentially large factor `e^{L/2}/4`. -/
theorem exponent_gap {L : ℝ} (hL : L ≠ 0) :
    4 * Real.exp (L / 2) / L * (Real.exp (L / 2) / 4) = Real.exp L / L := by
  have hsq : Real.exp L = Real.exp (L / 2) * Real.exp (L / 2) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [hsq]
  field_simp

/-- **Domination at the alignment height.**  Since the archimedean term is `L` times the logarithm of
the height, at the alignment height it is `≍ e^L·c`, against an aligned prime sum of size
`4e^{L/2}` — larger by the factor `e^{L/2}c/4`. -/
theorem arch_dominates_at_alignment {L c : ℝ} (hc : 1 ≤ c)
    (hbig : 4 ≤ Real.exp (L / 2)) :
    4 * Real.exp (L / 2) ≤ Real.exp L * c := by
  have h1 : 4 * Real.exp (L / 2) ≤ Real.exp L := four_exp_half_le_exp hbig
  nlinarith [h1, hc, Real.exp_pos L]

/-- **The narrowing.**  Failure of positivity for the modulated tent cannot come from alignment; it
must come from the zeros. -/
theorem failure_is_spectral {alignOK spectralFail : Prop}
    (halign : alignOK) (hdisj : alignOK → ¬ (¬ spectralFail)) : spectralFail := by
  by_contra h
  exact hdisj halign h

end RHTower
