# Singular Euler source--divisor incidence law

- **ID:** singular-euler-source-divisor-incidence-law
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper) / THEOREM (Lean) / RH ROUTE ARCHITECTURE
- **Source:** synthesis of exponent-zero Euler gauge foliation, isodivisorial Prime--Walsh Stone
  saturation, rigid reflection transversality, source-conormal topology, and the Xi projective
  source--temperature spectrum
- **Statement:** Continuable Euler products form dense, codense, maximally hypertranscendental
  isodivisorial gauge leaves carrying every pointed metrizable Stone tail spectrum; every
  nonconstant separated leaf-invariant is nowhere continuous, no continuous global leaf selector
  exists, and a completed functional equation is a rigid but necessarily singular transversal.

## Goal

Prove one structural law explaining why the corpus repeatedly preserves divisor location while
losing the orientation needed for RH.  Hypertranscendental and Stone-tail information lives
tangentially inside one exact divisor fibre.  The functional equation selects a source
transversally.  The Xi reflection displacement is a normal divisor coordinate.  A valid RH route
must therefore construct a calibrated, singular source--divisor incidence; no continuous,
finite-observable, unpolarized, or marginal invariant can substitute for it.

The intended scientific contribution is not another RH equivalence.  It is an arithmetic
source-space theorem with three new consequences:

1. the exact continued divisor is a necessarily singular observable of prime phase;
2. no continuous global Euler gauge fixing can select one source per isodivisorial leaf;
3. even the complete nonlinear Stone tail algebra and its entropy profile are freely prescribable
   inside every leaf, while completed reflection cuts a leaf in at most one point.

## Gates

- [x] 0 → 1  in-progress: exact objects, anti-transport attack, and falsifiable capstone stated
- [ ] 1 → 2  fully-proven: complete paper proof, concrete nonconstant divisor labels, and no hidden
  analytic hypothesis
- [ ] 2 → 3  formalized: capstone and nowhere-continuity/no-selector corollaries compile and pass
  axiom audit
- [ ] 3 → 4  publication-ready: specialist novelty audit, standalone paper, claim trace, hostile
  referee report

## Candidate master theorem

Let

```text
Omega = product_(p prime) S^1,
G_0 = {omega : sum_p |1-omega(p)| p^(-sigma) < infinity for every sigma>0},
q : Omega -> Omega/G_0.
```

Then:

1. every `q`-fibre is dense and codense, the quotient is indiscrete, and it has continuum
   cardinality;
2. every Euler continuation transported by the canonical `G_0` unit has exactly the same signed
   divisor on `Re(s)>0`;
3. every nonconstant `T_1`-valued invariant constant on `q`-fibres is discontinuous at every point;
4. there is no continuous map `S : Omega -> Omega` that is constant on `q`-fibres and satisfies
   `q(S(eta))=q(eta)` for all `eta`;
5. in every continuable leaf and every finite prime cylinder, every pointed compact metrizable
   Stone space occurs as the exact recurring prime-tail spectrum, with the corresponding exact
   Prime--Walsh differential ranks and entropy profile, without changing the divisor;
6. every exponent-zero-gauge-separated completed reflection class meets each leaf in at most one
   point;
7. for the Riemann member selected by positivity and completed reflection, the projective
   reflection displacement of a zero is exactly its horizontal critical-line defect and the
   associated source-abscissa/Born-temperature coordinate, while the endpoint energy is its
   weighted quadratic shadow.

Items 1--6 give a singular foliation--transversal theorem.  Item 7 identifies the RH-bearing normal
coordinate after the singular source-to-divisor passage.

## Approach

1. Instantiate the existing dense-fibre continuity theorem with the exponent-zero quotient to
   prove item 3.
2. Prove item 4 by contradiction: continuity and fibre constancy force `S` to be constant, while
   the section law would identify the distinct constant `+1` and `-1` gauge classes.
3. Package existing analytic unit/divisor preservation and Stone saturation into one leaf theorem.
4. Package existing reflection transversality and Xi projective spectrum without strengthening
   either beyond its exact hypotheses.
5. Prove a concrete nonconstant divisor witness using the positive Euler phase and the constant
   negative phase, whose Euler product is `zeta(2s)/zeta(s)`, or replace it with a simpler
   already-formalized continuable pair if meromorphic-order bookkeeping is cleaner.
6. Attack the result against Grosswald--Schnitzer, Helson-zeta divisor prescription, dense subgroup
   quotients, Stone duality, symbolic dynamics, and strong multiplicity one.  Novelty must reside
   in the exact arithmetic foliation--singular-observable--Stone-universality--reflection-transversal
   law, not in any parent ingredient.

## Kill tests

- If the master theorem is only a conjunction of existing cards and yields no new
  nowhere-continuity or no-selector consequence, reject it.
- If a published Helson-zeta theorem already identifies the exponent-zero dense foliation,
  nowhere-continuous divisor reader, Stone-universal leaf, and rigid functional-equation
  transversal together, reject novelty.
- If item 7 is used to imply zero exclusion or an upper bound not supplied by the source, reject
  the RH claim.
- If the paper presents hypertranscendence itself as RH evidence, reject significance.
- If the paper cannot state a concrete mathematical question answered completely by items 1--6,
  do not promote it.

## Log

- 2026-07-30 — created directly in stage 1 after the positive-to-Möbius scale law failed the
  significance gate.  Candidate extracted from formalized `HTGeometry`/`RHTower` structures rather
  than from a coordinate transport or a new RH equivalence.
