# Route-P Gamma-sewn Stokes dual current

- **ID:** `P-G64`
- **Stage:** `1-in-progress`
- **Type:** source-native strong-dual landing / exact transpose law
- **Status:** `[CORPUS-NEW] [PAPER-PROVED] [LEAN DIRECT GREEN] [UMBRELLA-WIRED] [FINAL AUDIT PENDING] [NOT RH]`
- **Parent:** `hedenmalm-theta-route-p-gamma-sewn-stokes-kothe-vector-landing-no-go.md`
- **Lean target:**
  `formal/GaloisForLFunctions/RHTower/GammaSewnMobiusApertureStokesDualCurrent.lean`

## Goal

Construct P-G63's forced dual landing from literal sewn coefficients, rather than postulating an
abstract functional or placing feature illegally inside rapid test source.

## Conjecture P-G64.A: divided sewn edge is continuous Köthe-dual current

For prime-power axis `m_(p,e)=(e+1)[p]`, set `b_s(p,e)=B_s(p,e)/(e+1)`. Positive aperture gives
`0 <= b_s(p,e) <= 1`. Prime-power axes embed injectively into Kummer lattice, so every rapid
height-Köthe test `a` has an absolutely convergent pairing

```text
L_s(a)=sum_(p,e) b_s(p,e) a(m_(p,e)),    |L_s(a)| <= p_0(a).
```

Thus actual sewn feature belongs to `K_H'`, controlled by zeroth source seminorm.

**Verdict: proved and formalized.**

## Conjecture P-G64.B: transpose Stokes action is exactly Euler current

P-G61 frequency on prime-power axis is `(e+1)W_s(p)`. Valuation division is therefore forced, and
P-G60 gives coefficientwise

```text
b_s(p,e) (e+1) W_s(p) = log(p) p^(-s(e+1)).
```

Consequently, throughout `s>=1`,

```text
L_s(T_s a) = sum_(p,e) log(p) p^(-s(e+1)) a(m_(p,e)).
```

For `s>1`, total coefficient mass is complete Euler flux `-zeta'(s)/zeta(s)`.

**Verdict: proved and formalized.**

## Higher universal principle

Inverse tilt is connection on tests, not state evolution on one Hilbert vector; its transpose
differentiates boundary current. Prime-power valuation is simultaneously orbit length and exact
Radon--Nikodym factor converting sewn edge measure into von Mangoldt current. Route P's repeated
Hilbert walls were shadows of this variance: tests transform covariantly, arithmetic currents
contravariantly.

## Lean realization

Headline declarations:

- `gammaSewnMobiusApertureStokesPrimePowerAxis_injective`;
- `norm_gammaSewnMobiusApertureStokesDualFeaturePairing_le`;
- `gammaSewnMobiusApertureStokesDualFeaturePairing_operator_eq_euler`;
- `tsum_gammaSewnMobiusApertureStokesEulerDualCoefficient`.

## Gates

- [x] prime-power axis embedded injectively
- [x] physical dual coefficient uniformly bounded
- [x] continuous dual pairing constructed on full rapid source
- [x] exact transpose Stokes-to-Euler law
- [x] total safe-chamber coefficient mass identified with Euler flux
- [x] permanent direct Lean check
- [x] umbrella import wired
- [x] exact module build
- [ ] full umbrella build
- [ ] formal lint and axiom audit
- [ ] weld fixed archimedean current in same source-native pairing
- [ ] prove passive/Markov order for completed dual current
- [ ] discharge RH capstone

## Honest boundary

P-G64 is not RH. It closes strong-dual existence and exact finite-place production, but does not
prove completed prime--Gamma current passive. Existing Deninger explicit formula is already an
unconditional equality of distributions, but its spectral side is indexed by Xi zeros and is a
receiver, not independently positive source flow.
