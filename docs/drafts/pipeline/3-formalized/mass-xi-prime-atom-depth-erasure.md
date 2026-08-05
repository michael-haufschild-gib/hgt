# Mass–Xi prime-atom depth erasure

## Status

- Lane: `3-formalized`
- Conjecture: `C30` — proved
- Target: `docs/reports/mass-shifted-spectral-trace-route.md`, §9.3 exact open core
- Lean: `formal/GaloisForLFunctions/RHTower/XiMassBottomPrimeAtomization.lean`

## Exact theorem

Let `g(z)=xiMassAnalyticTest a τ z`, let `Λ` be the von Mangoldt function, and assume
`1/2<c<a`, `Re τ>0`. For every `n : ℕ`, define

```text
A_c(n) = ∫_ℝ g(x-ci) LSeries.term Λ ((1/2+c)+ix) n dx.
```

Lean proves

```text
A_c(n) = LSeries.term Λ (1/2) n · stripFourier g (log n).
```

The atom integral norms are summable, so the Bochner integral and Dirichlet `tsum` interchange:

```text
∫_ℝ xiMassBottomPrimeIntegrand a c τ x dx
  = ∑' n, LSeries.term Λ (1/2) n · stripFourier g (log n).
```

The centered atoms on the right form an absolutely summable family.

## Proof

For `n>0`, complex-power expansion gives the pointwise identity

```text
LSeries.term Λ ((1/2+c)+ix) n
 = LSeries.term Λ (1/2) n · exp(-i log(n) (x-ci)).
```

The product of the analytic mass test with this Fourier character is holomorphic on the closed
strip `|Im z|≤c`. Its norm is bounded there by

```text
exp((|Im τ|+|log n|)c) · exp(-Re(τ)|Re z|).
```

Lower-line horizontal transport therefore moves `x-ci` to `x`. The `n=0` term vanishes directly.

For infinite reassembly, each bottom atom is dominated by

```text
exp(|Im τ|c) · ‖LSeries.term Λ (1/2+c) n‖ · exp(-Re(τ)|x|).
```

Absolute convergence of the von-Mangoldt L-series on `Re s=1/2+c>1` makes the integrals of these
majorants summable. `integral_tsum_of_summable_integral_norm` then gives the exact source identity.

## New scientific knowledge

Contour depth is a coordinate gauge at the level of each individual von-Mangoldt atom. The factor
`n^{-c}` is exactly the imaginary-height factor of the Fourier character and disappears under
holomorphic strip transport. This is stronger than previously known depth independence of the
recombined prime integral.

The remaining §9.3 obstruction is therefore an explicit cofinal scalar series at prime-log
frequencies. Any `ℓ¹` estimate destroys the only new information and collapses back to the closed
absolute entropy wall. A viable continuation must retain cancellation between distinct
logarithmic atoms or replace their count by a source-sensitive pair statistic.

## Lean declarations

- `RHTower.integral_horizontal_shift_neg_of_decay`
- `RHTower.xiMassBottomLSeriesTerm_eq_centered_mul_fourierPhase`
- `RHTower.integral_xiMassBottomPrimeAtom_eq_centered`
- `RHTower.summable_integral_norm_xiMassBottomPrimeAtomIntegrand`
- `RHTower.summable_xiMassCenteredPrimeAtom`
- `RHTower.integral_xiMassBottomPrimeIntegrand_eq_tsum_centeredAtom`

## Verification

- `lake env lean GaloisForLFunctions/RHTower/XiMassBottomPrimeAtomization.lean`: PASS
- `lake build GaloisForLFunctions.RHTower.XiMassBottomPrimeAtomization`: PASS (`9378/9378`)
- Axiom audit of key declarations: only `propext`, `Classical.choice`, `Quot.sound`
- No `sorry`, `admit`, local axiom, `opaque`, `unsafe`, computation proof, or RH hypothesis
- Wired into `GaloisForLFunctions.RHTower`

## Novelty audit

`[LOCAL-RESEARCH] [LEAN-PROVED] [NOVELTY UNVERIFIED]`.

The ingredients—Dirichlet series, Fourier characters, strip contour transport, Bochner
interchange—are classical. The exact atomwise depth-erasure law for this analytic-mass Xi source,
its absolutely convergent centered reassembly, and its use to identify the post-entropy invariant
were not found in the audited route corpus. External priority remains unverified.
