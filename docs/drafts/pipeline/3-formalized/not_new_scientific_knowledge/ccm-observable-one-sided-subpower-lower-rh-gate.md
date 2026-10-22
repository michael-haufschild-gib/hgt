# One-sided subpower lower control of one observable rectangular Weil tail forces RH

- **ID:** `ccm-observable-one-sided-subpower-lower-rh-gate`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) / TOP-DOWN QUANTITATIVE GATE
- **Scientific status:** `[FORMALIZATION] [POSITIVE STATEMENT] [NOT AN RH PROOF]`
- **Statement:** For one fixed positive rectangular width, RH follows if its actual logarithmic
  Weil values admit an eventual lower bound `-C_epsilon n^epsilon` for every `epsilon>0`.

## Goal

Replace the previously isolated uniform lower floor by a strictly weaker, scale-sensitive source
obligation. The formal chain is

```text
for every epsilon>0, Q_L(n) >= -C_epsilon n^epsilon eventually
  -> choose epsilon = delta_*/4 under false RH
  -> nonnegative power-corrected Dirichlet coefficients
  -> local Landau transfer across the real transverse boundary
  -> absolute convergence strictly left of 1+delta_*
  -> every shifted right Xi pole has real part at most that smaller boundary
  -> delta_* is strictly smaller than itself
  -> RH.
```

Here `delta_*` is used only inside the contradiction proof. It does not occur in the hypothesis.

## Theorem

The Lean module
`GaloisForLFunctions.RHTower.CCM.CCMRectangularSubpowerLowerGate` defines

```text
XiRectangularRightSubpowerLower L
XiRectangularWeilTailSubpowerLower L N
```

and proves

```text
riemannHypothesis_of_xiRectangularRightSubpowerLower
riemannHypothesis_of_xiRectangularWeilTailSubpowerLower
```

The second theorem is the observable form. The cutoff `N` only ensures that the rectangular window
is contained in the logarithmic aperture. A finite-prefix absorption lemma upgrades the eventual
power floor to the global nonnegative coefficient sequence consumed by Landau.

## Proof architecture

For a real exponent `alpha`, define the nonnegative correction coefficient

```text
p_alpha(n) = n^alpha, n>0;   p_alpha(0)=0.
```

Its L-series is exactly `zeta(s-alpha)`. If RH is false, put
`alpha=delta_*/4`. The power-corrected rectangular coefficient has continuation

```text
2 * shiftedZetaRectangular_L(s) + C * zeta(s-alpha).
```

The extra zeta pole is at `1+alpha`, strictly left of the pole-free Landau ball centered at
`1+delta_*`. The generic local Landau theorem gives summability at a real
`sigma<1+delta_*`, while still `sigma>1+alpha`. Subtracting the summable power correction recovers
summability of the original right-divisor coefficient series. The existing exact pole-order theorem
then bounds every right Xi pole by `sigma`, contradicting the definition of `delta_*`.

For the actual Weil values, the uniformly bounded rectangular remainder changes `C` only by a
fixed nonnegative constant. The finite excluded prefix is absorbed into a larger coefficient using
`n^alpha>=1` for positive integers.

## Boundary

This is weaker than all previously formalized rectangular sufficient conditions:

- no nonnegativity is required;
- no constant lower bound is required;
- no two-sided or norm bound is required;
- the values may tend to minus infinity, provided every fixed positive power eventually dominates
  that negative drift.

The remaining source problem is therefore:

```text
prove a one-sided n^epsilon lower estimate for the completed prime--Gamma /
critical-Mellin adjacent-block formula for every epsilon>0,
without using Xi zero locations or an RH-equivalent limiting measure.
```

## Gates

- [x] 0 → 1 in-progress: weaker source obligation isolated
- [x] 1 → 2 fully-proven: power-corrected Landau proof complete
- [x] 2 → 3 formalized: exact module compiles without `sorry`, `axiom`, or `opaque`
- [ ] 3 → 4 publication-ready: independent proof and literature audit

## Log

- 2026-07-12 — Formalized the one-sided subpower lower gate and its observable bounded-remainder
  transport.
