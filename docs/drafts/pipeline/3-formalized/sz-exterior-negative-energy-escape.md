# SZ: complete exterior correction forces negative energy escape

- **ID:** SZ-EXTERIOR-NEGATIVE-ESCAPE
- **Stage:** 3-formalized
- **Type:** THEOREM; paper and Lean audited
- **Source:** exact exterior null-gauge average, literal superoscillation
  packet, actual normalized restricted Weil ground and full corrected symbol.

## Hard target and tested construction

The RH-bearing target remains the actual canonical-head joint sign.
Attempted construction: lift the negative region of the full spectral
symbol with exterior packets and damp their far lobes without spending
the whole signed-measure mass. Mass estimates alone do not decide this.
The following stronger test retains actual physical negative energy.

## Statement

For each actual aperture a, let u be the normalized actual ground,
D=|Fourier(u)|^2, S=correctedCCMSymbol(a,2*pi*xi), and

    G_N(xi)=exteriorSuperoscillationCosineSum(8*pi*a,4*pi*a,2,xi,N),
    F_N=S+G_N.

For every fixed frequency window R and every c<1, eventually

    c < integral_(|xi|>R) max(-F_N(xi),0) D(xi) dxi.

Thus all sufficiently late packets have a negative corrected-symbol
region outside each fixed window, including even packet degrees. This
is a weighted energy obstruction, not only coefficient-mass growth or
one phase-locked negative point. It is not a negative Weil quadratic.

## Dependency-closed paper proof

Plancherel gives integral D=1; the actual form domain gives integrable S*D.
Exact aperture support gives integral G_N*D=0. The corpus's packet limit
is G_N(xi)->1. Its complex binomial form gives a uniform compact bound
|G_N(xi)|<=exp(|2*(4*pi*a)*xi|), by |exp(i*t)-1|<=|t| and
(1+b/N)^N<=exp(b). Hence dominated convergence gives, on every fixed
compact interval K,

    integral_K F_N*D -> integral_K (S+1)*D.

The exact whole-line average is integral S*D for every N. Consequently
the signed tail integral tends to integral_(K^c) S*D - integral_K D.
As K exhausts the line this limit tends to -1. Negative tail energy
dominates minus its signed tail integral. Choose a larger fixed interval
than the requested window and use nonnegativity to transfer its lower
bound back. No sign of the actual ground energy is assumed.

## Positive survivor / scope

The survivor is the exact signed tail limit, retaining the full Gamma,
polar and prime symbol and actual ground mass. It locates the compulsory
negative-energy compensation outside every fixed window. A damping
construction retaining null-gauge cancellation and the same local L1(D) limit
cannot make that negative energy vanish. Selective corrections with a
different local limit remain open; route SZ is not retired.

## Log

- 2026-10-03: searches1215863,1215872,1215932 partial. Source reads verify
  existing mass walls and odd phase-locked obstruction. No novelty or
  coverage-completeness claim. Paper proof above subsequently formalized and audited.

## Lean audit

`CCMExteriorPacketNegativeEnergyEscape.lean` proves the exact signed tail
limit, eventual negative-tail energy lower law and exterior negative-point
consequence for every actual positive aperture.

- Scratch26419: exit0. Final33353: exit0, no diagnostics.
- Final command: `lake --old env lean GaloisForLFunctions/RHTower/CCMExteriorPacketNegativeEnergyEscape.lean -o .lake/build/lib/lean/GaloisForLFunctions/RHTower/CCMExteriorPacketNegativeEnergyEscape.olean`.
- Axiom90720: all10 public declarations use only propext, Classical.choice,
  Quot.sound; no new axioms or hypothesis of Weil positivity.
- One umbrella import; no umbrella/full build or heartbeat override.
- Lint5598: exit1 on13 unrelated unreachable modules; this leaf is not
  reported. No RH proof or falsification follows.

The general statement about other dampings is the paper consequence of
the same integral argument, not a separately formalized arbitrary-family
theorem. The Lean result concerns the literal packet above.
