# Route-P Gamma-sewn Stokes phase-sensitive Mellin response

- **ID:** `P-G62`
- **Stage:** `1-in-progress`
- **Type:** phase-retaining source response / reflection law
- **Status:** `[CORPUS-NEW] [PAPER-PROVED] [LEAN DIRECT GREEN] [UMBRELLA-WIRED] [FINAL AUDIT PENDING] [NOT RH]`
- **Parent:** `hedenmalm-theta-route-p-gamma-sewn-stokes-kothe-boundary.md`
- **Lean target:**
  `formal/GaloisForLFunctions/RHTower/GammaSewnMobiusApertureStokesMellinResponse.lean`

## Goal

Meet P-G59's surviving falsifier: preserve actual complex height phase through Gamma-sewn aperture
crossing before norm, KL, determinant action, Gram completion, or reflection folding.

## Conjecture P-G62.A: signed connection is reflection-odd

For P-G61 lattice frequency `Omega_s`, finite-support additivity gives

```text
Omega_s(m+n)=Omega_s(m)+Omega_s(n),
Omega_s(-m)=-Omega_s(m).                                 (P-G62a)
```

Therefore its source operator anticommutes with Kummer reflection:

```text
T_s R = -R T_s.                                          (P-G62b)
```

Unlike P-G55--P-G59 positive descendants, `(P-G62b)` retains orientation until observation.

**Verdict: proved and formalized.**

## Conjecture P-G62.B: all centered Mellin phases cross the wall

Freeze P-G61 operator at its critical boundary outside closed chamber, yielding globally typed
`Tbar_s`.  For centered Mellin jet

```text
M_z^j(a)=sum_m (-ell(m))^j exp(-(z-1/2)ell(m)) a_m,
R_s(z,j;a)=M_z^j(Tbar_s a),                               (P-G62c)
```

existing Mellin multiplier estimate gives, whenever
`|Re(z-1/2)|+j <= k`,

```text
|R_s(z,j;a)-R_1(z,j;a)|
  <= p_k((Tbar_s-Tbar_1)a) -> 0.                         (P-G62d)
```

Thus every complex height phase has path-independent source boundary value at `s=1+`.

**Verdict: proved and formalized.**

## New universal principle

Earlier scalar/KL/Bockstein attempts failed because positive completion erased orientation before
critical crossing.  Correct order is now forced:

```text
literal Gamma-sewn edge
  -> signed additive height connection
  -> nuclear source boundary
  -> complex Mellin phase observation
  -> only then passive/Julia/Markov completion.
```

P-G62 closes phase-retention part.  Remaining hard theorem is source-value identification: find a
source vector, corona functional, or trace-class pairing whose P-G62 response equals existing
`continuedPrimeArchSourceRelativeTrace` without importing Xi values, then prove its passive order.

## Lean realization

Headline declarations:

- `gammaSewnMobiusApertureStokesKotheFrequency_add`;
- `gammaSewnMobiusApertureStokesKotheFrequency_neg`;
- `gammaSewnMobiusApertureStokesKotheClosedOperator`;
- `tendsto_deningerHeightSeminorm_gammaSewnMobiusApertureStokesKotheClosedOperator`;
- `deningerMellinJet_sub_of_growth`;
- `gammaSewnMobiusApertureStokesMellinResponse`;
- `tendsto_gammaSewnMobiusApertureStokesMellinResponse`;
- `gammaSewnMobiusApertureStokesKotheOperator_reflect`.

## Gates

- [x] signed lattice additivity and reflection law
- [x] source operator reflection anticommutation
- [x] centered Mellin phase retained before completion
- [x] path-independent critical response crossing
- [x] permanent direct Lean check
- [x] umbrella import wired
- [ ] exact module build and umbrella build
- [ ] formal lint and axiom audit
- [ ] source-value identification with completed Euler--Gamma trace
- [ ] passive/Markov response producer
- [ ] discharge RH capstone

## Honest boundary

P-G62 is not RH.  It constructs unconditional phase-sensitive boundary responses for every nuclear
source vector.  It does not identify any one response with continued Xi trace and does not prove
passivity or compact Markov positivity.
