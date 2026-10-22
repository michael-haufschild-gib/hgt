# Hedenmalm exterior Julia-phase source projector

- **ID:** `hedenmalm-exterior-julia-phase-source-projector`
- **Label:** `P-G156`
- **Stage:** 1-in-progress
- **Type:** theorem / Route P conjecture loop
- **Parents:** `P-G39`, `P-G154`, `HedenmalmExteriorSourceNativePrimeWardClock`

## Problem

The coefficient-faithful four-contour exterior source uses the unit scalar clock

```text
realCayley((A-1)/(A+1)),   A=p^(2 Re(rho)-1).
```

Its finite Lagrange lift is exact but target-fed and gives no packet-independent source norm.
Determine whether this scalarization discarded a contractive source channel capable of paying the
exterior quantum.

## Conjecture P-G156a — Julia phase before scalar Cayley compression

Let

```text
c_p(rho) = (A-1)/(A+1),
h_p(rho) = mobiusCriticalTwoSidedUnitHardyGram((A-1)/2,0),
J_p(rho) = h_p(rho) + i c_p(rho).
```

Then:

1. `c_p(rho)^2+h_p(rho)^2=1`;
2. `|J_p(rho)|=1`;
3. `J_p(rho#)=conj(J_p(rho))` and `J_p(rho)J_p(rho#)=1`;
4. `J_p` is injective in horizontal position;
5. two prime ordinate clocks plus covariant `J_p` select exactly `rho#=1-conj(rho)`;
6. replacing scalar Cayley clock by `J_p` leaves complete exterior determinant and fixed-center
   Abel landing unchanged.

### Paper proof

Items 1--2 are source Julia--Pythagoras. Reflection sends `A` to `A^-1`, hence `c` to `-c`.
The normalized Hardy overlap is nonnegative and has square `1-c^2`, so it is reflection-even.
Therefore `J_p(rho#)=h-ic=conj(h+ic)` and its reflected product is one. Equality of Julia phases
implies equality of imaginary parts, hence equality of Ward coordinates and horizontal positions.
The existing two-prime ordinate injectivity then gives exact line reflection. Generic finite
three-clock Cesaro projection and ordered Cauchy--Binet apply verbatim, so every exterior landing is
unchanged.

## Hostile audit

This theorem does **not** prove a strict source bound. A unit phase is an exact lossless clock, but
mean-ergodic projection only contracts a source norm after the continued prime--Gamma residue rows
have themselves been realized in one uniformly bounded Hilbert source. Current four-contour rows
are coefficient-faithful Lagrange lifts and supply no such bound. P-G156a can advance Route P only
by relocating the open core from clock provenance to a non-diagonal source-row norm.

## Gates

- [x] conjecture frozen
- [x] dependency-closed paper proof
- [x] exact Lean module
- [x] umbrella import
- [x] direct Lean check
- [x] module build and axiom audit
- [x] post-proof novelty audit
- [x] test whether Julia dilation gives an unconditional row budget; fail and pivot if not

## Log

- 2026-08-14 — P-G156a conjectured after coefficient-faithful source criterion proved equivalent
  to RH and Kakutani finite-packet budget was found already terminalized as an RH-equivalent
  receiver.
- 2026-08-14 — Formalized in
  `HedenmalmExteriorJuliaPhaseSourceProjector.lean`.  The module proves Julia--Pythagoras,
  unit norm, reflection covariance, exact horizontal injectivity, the two-prime reflection
  selector, finite Cesaro projection, exterior determinant convergence, and fixed-center Abel
  landing.  Direct `lake env lean` and targeted `lake build` pass.  Audited capstones use only
  `[propext, Classical.choice, Quot.sound]`.
- 2026-08-14 — Post-proof novelty search checked Hedenmalm's 2026 preprint
  (`https://arxiv.org/abs/2606.17494`) and boundary Nevanlinna--Pick/Julia literature represented
  by Agler--Young (`https://arxiv.org/abs/0905.4759`).  No source was found identifying the
  arithmetic normalized Hardy overlap and Ward displacement as a unit Julia eigenphase that is
  simultaneously an exact zeta exterior-reflection selector and preserves Pluecker/Abel landing.
- 2026-08-14 — Producer test failed cleanly: Julia unitarity controls clock evolution only after
  residue rows live in one Hilbert source with a packet-independent norm.  Existing rows are
  finite target-fed Lagrange lifts.  Thus scalar Cayley compression was not the obstruction; the
  live conjecture is a uniformly bounded non-diagonal continued source row before residue
  extraction.  Repository lint reached this module without complaint but remains globally red
  because unrelated concurrently added modules are not umbrella-reachable.
