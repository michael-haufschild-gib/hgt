# Quantitative cyclic gauge--attainment wall crossing

- **ID:** `cyclic-gauge-attainment-wall-crossing`
- **Stage:** 3-formalized
- **Type:** PERIOD-SOURCE WALL-CROSSING MODEL / QUANTITATIVE TRANSGRESSION SEED
- **Scientific status:** `[PROVED] [LEAN-FORMALIZED] [QUANTITATIVE BRIDGE]`
  `[NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH RESULT]`
- **Lean:**
  `formal/GaloisForLFunctions/HTGeometry/CyclicGaugeAttainmentWallCrossing.lean`
- **Conceptual parent:**
  `../../1-in-progress/hypertranscendental-normalization-horizon-uniformization.md`

## Exact theorem

Put

```text
q_n=1/(n+1),
g_n(z)=exp(2 pi i (n+1) z),
w(q)=q/(1+|q|).
```

Then `g_n(0)=1`, `g_n(z+q_n)=g_n(z)`, and Lean proves

```text
|q_n|=1/(n+1),
|g_n'(0)|=2 pi (n+1),

|w(q_n)|^(-1)=1+|g_n'(0)|/(2 pi).                    (1)
```

It also proves the simultaneous limits

```text
q_n -> 0,
|g_n'(0)| -> infinity,
w(q_n) -> 0.                                          (2)
```

Thus the primitive normalized fixed gauge on the discrete cyclic side escapes at exactly the
reciprocal rate at which the corresponding regularized incidence coordinate becomes an
approximate-null direction.  Equation `(1)` is pointwise in the horizon parameter; it is stronger
than merely observing two divergent sequences.

## What this proves and what it does not

The complete period-source theorem had shown only the qualitative exchange

```text
discrete source:     nonconstant fixed gauge + bounded incidence inverse;
nondiscrete source:  fixed-gauge rigidity + incidence nonattainment.
```

The cyclic model supplies the first exact rate identity across that exchange.  It is a positive
successor to the bare-source reconstruction no-go: the lost gauge direction has a concrete
approximate-kernel receiver rather than simply disappearing.

It does **not** yet construct a canonical wall-crossing map for an arbitrary source.  The model
uses the positively oriented primitive character of one cyclic group.  Without an orientation,
the source retains the pair of inverse primitive characters; for higher-rank sources the whole
annihilator lattice is the natural object.  A scalar or a chosen character cannot be promoted to
the universal transgression.

## Novelty and anti-theatre gate

Pontryagin--Chabauty duality already proves that taking annihilators is a homeomorphism on the
Chabauty spaces of closed subgroups of a locally compact abelian group.  The degeneration
`q_n Z -> R` and the reciprocal behavior of its primitive characters are therefore parent
harmonic analysis.  Formula `(1)` is the exact coordinate identity produced by the project's
bounded regularization; its proof is elementary once that coordinate is chosen.

- `[NOVELTY GATE -- FAIL]` This is not standalone new scientific knowledge.
- `[SIGNIFICANCE GATE -- PASS AS A DISCRIMINATOR]` It forces any higher theory to transport rates
  and directions, not just the Boolean labels “gauge” and “nonattainment.”
- `[ANTI-THEATRE -- PASS]` The result is classified as a bridge and is not advertised as a paper.

Relevant parent source:

- Y. Cornulier, *On the Chabauty space of locally compact abelian groups*, Algebraic & Geometric
  Topology 11 (2011), Theorem 1.1 (Pontryagin--Chabauty duality),
  `https://msp.org/agt/2011/11-4/agt-v11-n4-p06-s.pdf`.

## Positive next theorem

The first non-parent target is the rank-two cusp.  For lattices

```text
L_t=Z+Z(alpha+i t),     t -> 0+,     alpha irrational,
```

one must compare all three independently defined objects:

1. the incidence strictness scale determined by the systole of `L_t`;
2. the escape profile of normalized elliptic fixed gauges, measured by a source-independent
   spherical-derivative or projective-jet normalization;
3. the annihilator/character direction selected only up to the source symmetry.

A paper-level theorem would construct a presentation-invariant correspondence between the full
escape profile and the strictness defect at the nondiscrete limit.  Merely applying lattice
duality or estimating a single shortest vector remains parent theory.

## Lean certificate

Lean proves unconditionally:

- nonzero shrinking periods;
- pointing and exact periodicity of the primitive gauge;
- the period norm and first-jet norm identities;
- the exact conservation law `(1)`;
- all three limits `(2)`.

The exact module cache was built and the source file was then checked directly.  No full or area
build was run.

## Gates

- [x] normalized fixed gauge constructed
- [x] exact gauge/period compatibility proved
- [x] exact escape/collapse conservation proved
- [x] asymptotic wall behavior proved
- [x] unconditional Lean formalization
- [x] Pontryagin--Chabauty parent identified
- [x] bridge status recorded honestly
- [ ] rank-two cusp escape profile constructed
- [ ] source-symmetry-invariant correspondence constructed
- [ ] natural non-periodic HT family exhibits the same transgression
