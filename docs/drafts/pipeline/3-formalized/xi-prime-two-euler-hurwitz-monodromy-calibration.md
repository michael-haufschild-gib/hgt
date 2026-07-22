# Prime-two Euler boundary calibration of Hurwitz monodromy

- **ID:** `xi-prime-two-euler-hurwitz-monodromy-calibration`
- **Stage:** 3-formalized
- **Type:** THEOREM / right-to-left source-character weld
- **Scientific status:** `[PROVED HERE] [FORMALIZED] [CORPUS-NOVEL INTERFACE] [NOT AN RH PROOF]`
- **Target:** `formal/GaloisForLFunctions/RHTower/XiPrimeTwoEulerHurwitzMonodromyCalibration.lean`

## Claim

For `s : C`, set

```text
u(s) = -4*pi*Im(s)/log 2,
t(s) =  4*pi*Re(s)/log 2,
pe   = (2, 0).
```

The existing Gamma-renormalized Euler height boundary feature satisfies the exact calibration

```text
xiGammaEulerHeightBoundaryFeature(u(s), t(s), pe)
  = sqrt(log 2 / 2) * exp(-2*pi*I*s).                    (1)
```

For a Xi divisor point `rho`, define the source boundary seam by taking its two
functional-equation/Schwarz endpoint samples:

```text
E(rho) = feature(conj(rho)) - feature(1-rho).            (2)
```

Then

```text
E(rho)
  = sqrt(log 2 / 2)
      * (monoScalar(conj(rho)) - conj(monoScalar(conj(rho)))),       (3)

normSq(E(rho))
  = 2*log 2*exp(-4*pi*Im(rho))*xiHurwitzOrientationDefect(rho).     (4)
```

Consequently, pointwise and globally,

```text
E(rho)=0 <-> orbitwiseFirstPrimeSeamCharge(rho)=0,

(forall rho, E(rho)=0)
  <-> XiFirstPrimeSeamChargesVanish
  <-> xiHurwitzOrientationEnergy=0
  <-> RH.                                                           (5)
```

### Stronger radial calibration

The same prime-two cell carries the actual reciprocal-prime character, not only a zero-fibre
model of Hurwitz monodromy.  Define

```text
u_rad(s)=2*Re(s),
t_ht(s)=2*Im(s).
```

Then Lean and the paper calculation prove

```text
xiGammaEulerHeightBoundaryFeature(u_rad(s),t_ht(s),(2,0))
  = sqrt(log 2/2)*2^(-s).                                  (6)
```

For the radial seam

```text
R(rho)=radialSample(conj(rho))-radialSample(1-rho),
```

one has the exact value identity, not merely a zero-fibre equivalence,

```text
log(2)*R(rho)
  = sqrt(log 2/2)*orbitwiseFirstPrimeSeamCharge(rho).       (7)
```

Both scalar factors are nonzero.  Hence, for every complex `rho`,

```text
R(rho)=0 <-> orbitwiseFirstPrimeSeamCharge(rho)=0.          (8)
```

Globally this gives a direct RH-independent source/operator weld

```text
all radial prime-two Euler seams vanish
  <-> all first-prime von Mangoldt seams vanish
  <-> fixed reciprocal-square Cauchy real-Krylov seam saturation
  <-> RH.                                                   (9)
```

### All-cell Hilbert section

The radial identity is not a prime-two coincidence.  For every prime-power cell
`pe=(p,e)`, `n=p^(e+1)`, the same proof gives

```text
xiGammaEulerHeightBoundaryFeature(2*Re(s),2*Im(s),pe)
  = sqrt(log(p)/n)*n^(-s).                                (10)
```

The map `pe -> n-2` is injective by uniqueness of prime-power presentation.  Composing the
existing absolutely summable pointed-Ward Euler stream with this injection proves that, whenever
`Re(s)>0`, the complete section in `(10)` is a genuine complex `ell^2` vector.  Therefore both
Xi reflection endpoints define unconditional Hilbert vectors, and their difference

```text
S(rho)=section(conj(rho))-section(1-rho)                  (11)
```

is an actual all-prime/all-valuation source seam.

For every cell, Lean proves the exact value law

```text
log(n)*S(rho)[p,e]
  = sqrt(log(p)/n)*orbitwiseNatPrimeSeamCharge(n,rho).    (12)
```

The prime-two coordinate is faithful, while equality of the endpoints makes every coordinate
zero.  Hence

```text
S(rho)=0 <-> Re(rho)=1/2,

(forall Xi rho, S(rho)=0)
  <-> all prime-two radial seams vanish
  <-> fixed reciprocal-square Cauchy real-Krylov seam saturation
  <-> RH.                                                  (13)
```

This upgrades the bridge from a selected scalar cell to a complete source Hilbert section.  The
reverse implication in `(13)` is still faithful at one coordinate; no artificial all-coordinate
hypothesis is needed to detect off-line support.

## Proof

At `pe=(2,0)`, the boundary coordinate is

```text
sqrt((log 2)/2 * exp(-u(s)*log 2))
  * exp(-I*t(s)*log 2/2).
```

Substituting `u(s)` and `t(s)` gives

```text
sqrt(log 2/2) * exp(2*pi*Im(s)) * exp(-2*pi*I*Re(s))
  = sqrt(log 2/2) * exp(-2*pi*I*s),
```

which proves `(1)`.  The already proved Hurwitz functional-equation reflection law

```text
monoScalar(1-rho) = conj(monoScalar(conj(rho)))
```

gives `(3)`.  In the open critical strip, the existing monodromy fixed-point theorem says its
anti-conjugation defect vanishes exactly when `Re(rho)=1/2`; this is exactly the zero fibre of the
first-prime seam charge.

For `(4)`, use

```text
normSq(z-conj(z)) = 4*Im(z)^2,
Im(exp(-2*pi*I*conj(rho)))
  = -exp(-2*pi*Im(rho))*sin(2*pi*Re(rho)),
xiHurwitzOrientationDefect(rho)
  = 4*sin(2*pi*Re(rho))^2.
```

After multiplying by the squared source amplitude `log 2/2`, both sides agree exactly.

## New knowledge and right-to-left consequence

This closes three missing source-character interfaces.  A source-defined Gamma-renormalized Euler
cell is literally the Hurwitz unit-translation character at one forced sampling law, and literally
the reciprocal-prime character at another; the latter extends to the complete `ell^2`
square-root von Mangoldt section `(10)`.  Earlier strict Bianchi, Hardy, and joint-Gram objects
were prime-source objects but did not carry the first periodic character.  Equations `(4)` and
`(7)` identify two actual-source seams whose global vanishing is the rightmost open obligation.

For upper-half Xi zeros, both endpoints in `(2)` use the same positive damping

```text
u(conj(rho)) = u(1-rho) = 4*pi*Im(rho)/log 2 > 0.
```

Only their phase differs.  Therefore the exact remaining frontier is:

```text
At common positive damping, prove equality of the two calibrated prime-two Euler phase samples
for every Xi divisor point.                                               [OPEN]
```

The stronger radial calibration gives the dual formulation.  At the two endpoints,

```text
t_ht(conj(rho))=t_ht(1-rho)=-2*Im(rho),
u_rad(conj(rho))=2*Re(rho)>0,
u_rad(1-rho)=2*(1-Re(rho))>0.
```

Thus the same frontier is equivalently

```text
At common height phase, prove equality of the two positive-damping prime-two Euler samples
for every Xi divisor point.                                               [OPEN]
```

This radial statement is stronger as an interface: its defect is exactly a fixed normalization
of the von Mangoldt first-prime seam, not only another function with the same zero set.

That statement is equivalent to RH.  The calibration does not assume or establish it, and no
size estimate is proposed.  It replaces the abstract first-prime/Hurwitz charge by equality of
two concrete points of the existing Gamma-renormalized Euler boundary source.

External literature search was intentionally not used: this task asks for internal theorem
creation and exact formal interfaces rather than a literature survey.

## Gates

- [x] 0 → 1: source-pure statement and exact algebraic attack
- [x] 1 → 2: dependency-closed paper proof above
- [x] 2 → 3: dedicated Lean module, umbrella import, targeted build, and axiom audit complete
- [ ] 3 → 4: publication-ready standalone theorem

## Log

- 2026-07-22 — corpus audit found no existing prime-two Euler/Hurwitz calibration.
- 2026-07-22 — paper proof and stronger exact seam-energy law closed.
- 2026-07-22 — discovered and Lean-checked exact radial calibration `(6)`--`(9)`; this upgrades
  zero-fibre agreement to a literal value-level Gamma--Euler/von-Mangoldt weld.
- 2026-07-22 — generalized radial calibration to every prime-power cell, proved positive-half-
  plane square summability from the existing pointed-Ward Euler stream, constructed the full
  Hilbert section, and welded its reflection seam directly to fixed real-Krylov saturation.
- 2026-07-22 — targeted `lake build` and direct `lake env lean` checks passed; axiom audit reports
  only `propext`, `Classical.choice`, and `Quot.sound`; scoped forbidden-declaration and diff checks
  passed. Full-repository lint remains red only because 22 unrelated concurrently owned modules
  are not imported by their theorem-area umbrellas.
