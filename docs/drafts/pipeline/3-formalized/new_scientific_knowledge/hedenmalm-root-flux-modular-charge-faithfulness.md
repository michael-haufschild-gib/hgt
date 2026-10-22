# Hedenmalm root flux faithfully reads the reflected modular charge

- **ID:** `hedenmalm-root-flux-modular-charge-faithfulness`
- **Stage:** 3-formalized
- **Type:** THEOREM (paper + Lean)
- **Scientific status:** `[PAPER-PROVED] [LEAN-PROVED] [BRIDGE] [NOVELTY UNVERIFIED] [NOT RH]`
- **Lean status:** complete in `RHTower/Hedenmalm/HedenmalmRootFluxModularChargeFaithfulness.lean`,
  umbrella-wired. `hedenmalmRootQuantileEnergy_pos` proves `0 < E(z)` (interior-continuity
  upgrade of the a.e. zero-energy escape, then the pinned root ODE `h' = -izq·h - 1` forces
  derivative `-1` at an interior zero); `hedenmalmRootOrderedFlux_eq_neg_half_entropy_mul_energy`
  is the faithful law `(3)`; `hedenmalmRootOrderedFlux_eq_zero_iff_entropy`,
  `riemannReflectedSourceEntropy_eq_zero_iff_im` and `hedenmalmRootOrderedFlux_eq_zero_iff_im`
  are the full equivalence `(4)`. Module build passes (2026-08-13); axiom audit
  `[propext, Classical.choice, Quot.sound]` on all five theorems.
- **Statement:** At every zero `z` of the completed theta transform in `|Im z| < 1`, the
  Hedenmalm quantile-root energy is strictly positive and its ordered-correlation flux is
  `-1/2` times the reflected Riemann source entropy times that energy. Consequently flux
  neutrality, entropy neutrality, and `Im z = 0` are equivalent.

## Goal

Identify whether the newly unconditional Hedenmalm endpoint theorem supplies an independent
neutral trace, or instead exposes the same transverse charge already carried by the prime-tail,
Cayley, and divisor routes. The theorem must retain the actual theta source and actual root mode;
an abstract positivity wrapper is insufficient.

## Exact objects

For the theta source `S = thetaSource`, write

```text
h_z(t) = rootH S z t,
q(t)   = quantileSpeed S t,
E(z)   = integral_(0,1) q(t) |h_z(t)|^2 dt,
s(z)   = 1/2 + i z,
F(z)   = Re integral_(0,1) -h_z(t) dt.
```

The corpus supplies, at `xiC S z = 0` and `|Im z| < 1`,

```text
F(z) = -Im(z) E(z).                                      (1)
```

The reflected source entropy satisfies

```text
R(s) = -2(Re(s)-1/2),
R(s(z)) = 2 Im(z).                                       (2)
```

The conjectured faithful law is

```text
0 < E(z),
F(z) = -(1/2) R(s(z)) E(z),                              (3)
F(z)=0  <->  R(s(z))=0  <->  Im(z)=0.                    (4)
```

## Conjecture loop

### C1 — independent neutral trace

`[FALSIFIED AS A ROUTE] [CIRCULAR]` Conjecture that the ordered-correlation flux is an
independently neutral boundary trace at every completed-transform zero.

Exact killing mechanism: `(1)` shows that, once `E(z)>0`, flux neutrality is exactly
`Im z=0`. No theorem in the Hedenmalm, Suzuki, Burnol, Euler--Gamma, or Deninger corpus identifies
this Green leg with a separately vanishing source trace. Euler head--tail cancellation is the
formal boundary `(A,-A)` and explicitly retains `A` under its Green contraction; Suzuki proves
existence of signed endpoint traces but leaves their vanishing open. Treating either as neutrality
would assume the open core in another notation.

### C2 — faithful modular-charge reader

`[PAPER-PROVED]` The failure is not an absence of boundary data: all audited routes carry the same
transverse modular charge with the same orientation. The stronger surviving claim is `(3)`--`(4)`:
the Hedenmalm root flux loses none of that charge because `E(z)>0`.

The C1 killing argument does not kill C2. C2 does not assert neutrality; it classifies exactly what
the flux measures and converts every proposed cancellation into a test for a genuine
orientation-reversing, source-specific connector.

## Paper proof under hostile audit

Assume `|Im z| < 1` and `xiC thetaSource z = 0`.

1. `rootModeEndpoints_thetaSource` gives integrability of `q|h_z|^2` and `h_z`, together with
   vanishing endpoint norms. `rootFlux_identity_thetaSource` therefore gives `(1)`.
2. The integrand `q(t)|h_z(t)|^2` is continuous and nonnegative on `(0,1)`, since the quantile
   speed is continuous and strictly positive there and the root mode is differentiable there.
3. Suppose `E(z)=0`. A continuous nonnegative function on an open interval with zero integral
   vanishes everywhere: otherwise positivity at one point and continuity give a compact
   neighbourhood with strictly positive integral. Since `q(t)>0`, this forces `h_z(t)=0` for every
   `t in (0,1)`.
4. At `t=1/2`, local identically-zero behaviour gives `h_z'(1/2)=0`. But the exact root ODE is

   ```text
   h_z'(t) = -i z q(t) h_z(t) - 1,
   ```

   so `h_z(1/2)=0` gives `h_z'(1/2)=-1`, contradiction. Hence `E(z)>0`.
5. The corpus identity
   `riemannReflectedSourceEntropy_eq_neg_sourceCayleyRate` and the definition of the Riemann
   Cayley rate give `R(s)=-2(Re(s)-1/2)`. Since
   `Re(1/2+i z)-1/2=-Im z`, equation `(2)` follows.
6. Substitute `(2)` into `(1)` to obtain `(3)`. Strict positivity of `E(z)` makes
   `F(z)=0 <-> R(s(z))=0`; equation `(2)` makes the latter equivalent to `Im z=0`. This proves
   `(4)`.

No RH instance, zero-reality assumption, self-adjointness hypothesis, divisor-fitted metric, or
unproved source connector is used.

## Hostile tests

- **Could `E(z)=0` through an a.e. escape?** No. Interior continuity upgrades a.e. vanishing to
  pointwise vanishing before the ODE contradiction.
- **Could quantile speed vanish?** No. It is the reciprocal of the strictly positive normalized
  theta density on `(0,1)`.
- **Does endpoint decay secretly assume RH?** No. The endpoint theorem assumes only the particular
  zero under consideration and the unconditional strip bound `|Im z|<1`.
- **Does the charge identity prove RH by notation?** No. It proves faithfulness, not neutrality.
  The remaining open core is an independent source-specific reason for `F(z)=0`, or a genuinely
  opposite orientation on the same state.

## Internal and external frontier

- `[CORPUS]` `rootFlux_identity_thetaSource` and `rootModeEndpoints_thetaSource` in
  `formal/GaloisForLFunctions/RHTower/Hedenmalm/HedenmalmThetaRootEndpoints.lean` close all endpoint
  hypotheses at actual theta-transform zeros.
- `[CORPUS]` `hasDerivAt_rootH_ode` and positivity/continuity of the quantile speed in
  `HedenmalmQuantileRootMode.lean` supply the strict-energy contradiction.
- `[CORPUS]` `riemannReflectedSourceEntropy_eq_neg_sourceCayleyRate` in
  `XiSourceBoundaryOrientationConservation.lean` identifies the prime-tail modular charge.
- `[LITERATURE]` Hedenmalm, *Spectral interpretation of Riemann zeta zeros*,
  arXiv:2606.17494v1, Theorem 3.3.3 gives the complex theta-root mode and endpoint decay. It does
  not state the quantile energy flux, strict positivity, or reflected-source entropy
  identification.
- Targeted searches for the exact ordered-correlation/quantile-flux and modular-charge identity
  found no primary-source statement. Priority remains unverified; the claim is treated as a bridge,
  not promoted as new scientific knowledge.

## Positive survivor and representation lesson

- **Strongest positive survivor:** `(3)`--`(4)`, if the proof survives Lean formalization.
- **New insight:** Hedenmalm flux, prime-tail entropy, Cayley escape, and horizontal divisor charge
  are not independent budgets. They are faithful readings of one transverse modular charge. Adding
  same-orientation identities cannot cancel it. A viable Frankenstein must construct a
  source-specific orientation reversal on the same zero mode or prove a new conservation law that
  sets this charge to zero.
- **Next conjecture after formalization:** existence or impossibility of such an
  orientation-reversing connector in the actual corpus carriers, with the strict faithful law as
  discriminator.

## Gates

- [x] 0 → 1: well-posed actual-source claim; exact hostile attack stated
- [x] 1 → 2: paper proof survives dependency audit
- [x] 2 → 3: exact Lean theorem and axiom/lint gates (2026-08-13)
- [ ] 3 → 4: publication-ready

## Log

- 2026-08-07 — C1 killed as circular by unconditional root-flux identity; C2 formulated from the
  shared modular-charge obstruction and paper proof written for hostile audit.
- 2026-08-07 — C2 survived hostile dependency audit. Interior continuity rules out an a.e.
  zero-energy escape; the forced `-1` in the root ODE rules out pointwise zero. Promoted to Stage 2.
- 2026-08-13 — Faithful law and full neutrality equivalence formalized unconditionally in
  `RHTower/Hedenmalm/HedenmalmRootFluxModularChargeFaithfulness.lean`; module build and axiom audit clean.
  Promoted to 3-formalized.
