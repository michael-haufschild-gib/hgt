# Xi true-aperture transport compactness phase law

- **ID:** `xi-aperture-transport-compactness-phase-law`
- **Stage:** 3-formalized / needs-audit
- **Type:** THEOREM (paper + Lean)
- **Source:** `XiAperturePoissonValuationClockShuttle.lean`,
  `XiMobiusContinuousApertureSzegoMetric.lean`, and
  `XiAperturePoissonUnitApertureHilbertTransport.lean`
- **Statement:** The exact squared gain from the valuation-fused Poisson response to the true
  continuous-aperture Szegő ray has a unique noncompact boundary at integral aperture one; every
  deeper integral aperture has summable all-prime gain.
- **Lean:** `GaloisForLFunctions.RHTower.XiAperturePoissonFullApertureHilbertTransport`
- **Scientific status:** `[PROVED HERE ON PAPER AND IN LEAN] [CORPUS-NEW]`
  `[CANDIDATE NEW RH-PROOF-SHAPE KNOWLEDGE] [EXTERNAL NOVELTY UNVERIFIED] [NOT RH]`

## Exact theorem

For a prime `p`, write

```text
q_p=p^(-1),                 r_(a,p)=p^(-a),              a>=1,
```

and let `M_(a,p)` be the diagonal of the actual continuous-aperture Szegő metric.  The complete
valuation-fused Poisson response has coefficient

```text
F_(a,p)=a r_(a,p)/(1-r_(a,p)).                           (1)
```

The exact squared transport gain is

```text
G_(a,p)
 =a^2 (r_(a,p)/q_p)^2
   (1+q_p)^2 (1+r_(a,p))/(1-r_(a,p))^3,                 (2)

F_(a,p)^2=G_(a,p) M_(a,p).                              (3)
```

At the unit aperture, `r_(1,p)=q_p`, so

```text
G_(1,p)=((1+q_p)/(1-q_p))^3.                            (4)
```

Hence `G_(1,p)` tends to one, while its nonidentity correction is Hilbert--Schmidt but not trace
class and has the unique counterterm `6/p`.

For every integral aperture `a>=2`,

```text
0<G_(a,p)<=27 a^2 q_p^2.                                (5)
```

Consequently

```text
sum_p G_(a,p)<infinity                  iff a>=2,        (6)
```

among positive integral apertures.  Thus the true source-to-response transport is noncompact only
at the first aperture; one valuation step deeper makes its squared gain trace class.  Moreover
`sum_p F_(a,p)^2<infinity` for every `a>=1`.

## Paper proof

The metric diagonal already proved in the corpus is

```text
M_(a,p)
 =(q_p/(1+q_p))^2 (1-r_(a,p))/(1+r_(a,p)).              (7)
```

Dividing `(1)^2` by `(7)` gives `(2)` and hence `(3)`.  Formula `(4)` is the specialization
`r_(1,p)=q_p`.

Let `a=k+2`.  Since `0<q_p<=1/2`,

```text
r_(a,p)=q_p^(k+2),
r_(a,p)/q_p=q_p^(k+1)<=q_p,
r_(a,p)<=q_p<=1/2.                                      (8)
```

Therefore

```text
(1+q_p)^2<=9/4,
1+r_(a,p)<=3/2,
(1-r_(a,p))^(-3)<=8.
```

Substitution in `(2)` gives `(5)`.  Prime-square summability proves the forward trace-class
statement.  At `a=1`, `G_(1,p)>=1`, so its prime sum diverges; equivalently the already formalized
correction `G_(1,p)-1` is not summable.  This proves `(6)`.

Finally, `(3)`, `M_(a,p)<=q_p^2<=1`, and `(5)` give square summability of `(1)` for `a>=2`; the
unit case is already Lean-proved.

## Why this changes the RH proof shape

The unit aperture is not an arbitrary normalization.  It is the unique depth at which the actual
Poisson response retains an identity-sized channel against the true Szegő source metric.  Every
deeper integral aperture is compactified into a trace-class all-prime gain.  Therefore:

1. a proof cannot replace the unit boundary by one convenient deeper cofinal ray without losing
   the anomaly-bearing channel;
2. the `6/p` counterterm is a boundary phenomenon, not a generic feature at all depths; and
3. any viable completion must retain non-diagonal cross-aperture transport joining the unique
   noncompact boundary to the compact deeper tower.

This matches the independent HTGeometry minimal-architecture theorem: one cofinal direction is
nonconservative, while the full source-depth by observable-order bornology is necessary.

## Hostile audit

1. The estimates use elementary geometric-series and prime-square summability.  Candidate novelty
   is the exact phase classification forced by the project-specific true-aperture transport, not
   those parent facts.
2. The theorem is stronger than the unit gain bound but still does not produce the global joined
   response inequality `(AC25)` or cancel the three-node Xi orbit obstruction.
3. Trace-class compactification at `a>=2` does not orient the determinant line.  The missing
   mechanism remains off-diagonal completed prime--Gamma/functional-equation reflection.
4. External specialist novelty review remains open.

## Gates

- [x] 0 -> 1: exact source-defined theorem and RH fit
- [x] 1 -> 2: dependency-closed paper proof
- [x] 2 -> 3: Lean exact gain, unit specialization, deep-aperture bound, and summability phase
- [ ] external novelty audit
- [ ] couple the compact depth tower to the unit anomaly through a source-defined off-diagonal map
- [ ] prove `(AC25)` / RH

## Log

- 2026-07-19 — derived the exact gain by dividing the valuation-fused Poisson coefficient by the
  already formalized continuous Szegő metric diagonal.  An artificial scale-normalized gain was
  discarded because it changed the true source metric.  The corrected gain exposes aperture one
  as the unique noncompact boundary and every aperture `a>=2` as trace class.
- 2026-07-19 — formalized the exact local energy identity, positivity, unit specialization,
  `27 a^2 p^-2` deep-aperture bound, all-prime summability phase iff `2 <= a`, and fused-response
  square summability.  A narrow module build and `#print axioms` audit passed; the declarations use
  only `propext`, `Classical.choice`, and `Quot.sound`.
