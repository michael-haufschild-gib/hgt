# Route-P Gamma-sewn Stokes Köthe boundary crossing

- **ID:** `P-G61`
- **Stage:** `1-in-progress`
- **Type:** source-topology boundary crossing / Hilbert-wall resolution
- **Status:** `[CORPUS-NEW] [PAPER-PROVED] [LEAN DIRECT GREEN] [UMBRELLA-WIRED] [FINAL AUDIT PENDING] [NOT RH]`
- **Parent:** `hedenmalm-theta-route-p-gamma-sewn-stokes-inverse-tilt.md`
- **Lean target:**
  `formal/GaloisForLFunctions/RHTower/GammaSewnMobiusApertureStokesKotheBoundary.lean`

## Goal

Determine whether P-G60's critical chamber wall is a genuine source obstruction or only failure
of ambient Hilbert operator norm.  Use actual Gamma-sewn Stokes inverse and existing nuclear
prime-log height Köthe source; do not create an unrelated completion.

## Conjecture P-G61.A: closed-chamber inverse has uniform source growth

For `s >= 1`, write `W_s(p)` for P-G60 inverse tilt.  Direct source-factor estimates give

```text
0 < W_s(p) <= 8 log p.                                  (P-G61a)
```

Extend it to Kummer exponent lattice `Gamma = Z^(P)` by

```text
Omega_s(m) = sum_p m_p W_s(p).                          (P-G61b)
```

Then

```text
|Omega_s(m)| <= 8 sum_p |m_p| log p
             = 8 log H(m)
             <= 8 H(m).                                 (P-G61c)
```

Thus actual critical inverse, unbounded on prime Hilbert basis, is continuous on existing
height-Köthe source with exactly one seminorm loss:

```text
p_k(Omega_s a) <= 8 p_(k+1)(a),    uniformly for s >= 1. (P-G61d)
```

**Verdict: proved.**  Hilbert chamber wall is not source-topology wall.

## Conjecture P-G61.B: operator crosses critical wall strongly

For every lattice coordinate, `Omega_s(m) -> Omega_1(m)` as `s -> 1+`, since support of `m` is
finite and every Gamma-sewn source factor is continuous.  Uniform domination from `(P-G61c)` gives

```text
|Omega_s(m)-Omega_1(m)| <= 16 H(m).
```

For every `a` in nuclear height-Köthe source and every defining seminorm,

```text
p_k((Omega_s-Omega_1)a) -> 0       as s -> 1+.           (P-G61e)
```

Proof is dependency-closed dominated convergence against summable majorant
`16 H(m)^(k+1)|a_m|`.

**Verdict: proved and formalized.**

## New universal principle

P-G60 exposed opposite cofinite behavior (`W_s -> 0` for fixed `s>1`, `W_1 -> infinity`).
P-G61 proves this does not forbid continuation.  Cofinite operator norm sees moving mass escape;
source-derived projective topology sees exact one-height loss and admits strong boundary value.
Therefore Route P's remaining obstruction is no longer inverse construction or boundary topology.
It is identification of a source-continuous passive response functional whose safe Euler value is
the P-G60 flux and whose critical/strip continuation is the completed Euler--Gamma response.

## Lean realization

Headline declarations:

- `gammaSewnMobiusApertureStokesInverseTilt_le_eight_log`;
- `gammaSewnMobiusApertureStokesKotheFrequency`;
- `abs_gammaSewnMobiusApertureStokesKotheFrequency_le_log_height`;
- `continuousAt_gammaSewnMobiusApertureStokesKotheFrequency`;
- `gammaSewnMobiusApertureStokesKotheOperator`;
- `deningerHeightSeminorm_gammaSewnMobiusApertureStokesKotheOperator_le`;
- `tendsto_gammaSewnMobiusApertureStokesKotheBoundarySeminorm`;
- `deningerHeightSeminorm_gammaSewnMobiusApertureStokesKotheOperator_sub_one`.

## Gates

- [x] uniform closed-chamber prime-log estimate paper-proved
- [x] actual inverse extended to full Kummer lattice
- [x] one-step Köthe seminorm bound paper-proved
- [x] coefficientwise critical continuity proved
- [x] projective dominated-convergence crossing proved
- [x] permanent direct Lean check
- [x] umbrella import wired
- [ ] exact module build and umbrella build
- [ ] formal lint and axiom audit
- [ ] construct source-continuous passive response functional
- [ ] identify safe value with P-G60 complete Euler flux
- [ ] prove locally uniform/path-independent continued response
- [ ] discharge RH capstone

## Honest boundary

P-G61 is not RH.  It eliminates P-G60's boundary-topology obstruction on actual nuclear source.
It does not yet construct passive response functional, prove critical-strip sign, or identify
source limit with completed Xi trace.
