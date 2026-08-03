# Möbius critical countable one-corner common Hardy reporter

- **ID:** `mobius-critical-countable-one-corner-common-hardy-reporter`
- **Stage:** 3-formalized
- **Type:** THEOREM / ROUTE-R SOURCE OBJECT
- **Source:** `polarized-critical-rees-corona-transgression-rh.md` and C49 of
  `ccm-four-unit-source-codiagonal-attack.md`
- **Statement:** The actual countable squarefree-Möbius Fisher lower corner, paired with one
  source contraction before scalarization, is a single half-line `L²` field whose Laplace transform
  is the simultaneous countable hard-cut/soft-damping divided-difference column; cubic physical
  clock splitting evacuates the atomic collision without changing its graph-scale energy class.

## Goal

Construct the literal prelimit source object required before the Gamma/Julia Hardy mate can be
asked for.  This removes neither polarized contractivity nor RH: the remaining theorem must prove
that the actual Gamma/co-Poisson/Julia transgression factors through this same reporter with norm at
most one, rather than append a target-fitted scalar map.

## Exact conjecture `MCCOCHR`

Fix `sigma > 1`.  Let

```text
psi_sigma(n) = normalized signed squarefree Möbius weight,
chi_sigma(n) = centered critical Fisher tangent,
e_(sigma,u) = hard projection at (sigma-1) log n <= u,
L_(sigma,u) = (1-e_(sigma,u)) A(psi_sigma,chi_sigma) e_(sigma,u).
```

For every contraction `D_sigma` on the actual countable source Hilbert space, define before any
divisor evaluation

```text
c_(sigma,D)(u)
  = <L_(sigma,u),
      (1-e_(sigma,u)) A(psi_sigma,D_sigma psi_sigma) e_(sigma,u)>_HS.
```

Prove unconditionally:

```text
(MCCOCHR.1) c_(sigma,D) is strongly measurable and belongs to L²(0,infinity),

(MCCOCHR.2) integral |c_(sigma,D)(u)|² du
             <= (1/2) integral ||L_(sigma,u)||_HS² du < infinity,

(MCCOCHR.3) for every Re(w)>0, one common reporter satisfies
             Laplace(c_(sigma,D))(w)
             = the countable source divided-difference column at w,

(MCCOCHR.4) the cubic clock-split replicas define the same graph-scale corona class:
             their atomic codiagonal error tends to zero after the Gamma normal division,
             and their added L² energy tends to zero after squared normal division.
```

The finite-`sigma` global energy is controlled by the first three squarefree logarithmic moments;
no limiting closed profile is substituted for the actual source field.  Countable Tonelli and
dominated convergence must be proved, not inferred from finite packets.

## Paper proof plan

1. Expand both lower corners into their two rank-one summands.  The Hilbert--Schmidt pairing is a
   four-term expression in hard-cut inner products of fixed `ell²` vectors.  Each cut inner product
   is a countable sum of Borel half-line indicators, hence the full field is strongly measurable.
2. Apply the already formalized infinite joined-reporter half-unit law pointwise:

   ```text
   |c_(sigma,D)(u)|² <= (1/2)||L_(sigma,u)||_HS².
   ```

3. Use the exact cutoff Ward formula and discard only its negative overlap square:

   ```text
   2||L||_HS²
     <= tailFisherEnergy(u) + totalFisherEnergy * tailMass(u).
   ```

   Layer cake turns the two cutoff-ray integrals into respectively
   `E[Y |score|²]` and `E[Y]`.  All are finite at `sigma>1` by the existing squarefree log moments.
4. Expand the measurable field as an absolutely summable ordered-pair series.  Tonelli/Fubini and
   the exact interval Laplace integral give the countable divided-difference formula at every
   right-half-plane node.  The domination is the same finite holonomy moment as step 3, so there is
   no nodewise reporter choice.
5. Apply cubic clock splitting to the same actual squarefree probability, centered Fisher,
   damping, and logarithmic-clock data.  The codiagonal error divided by one Gamma normal scale
   tends to zero, while added holonomy energy divided by the squared normal scale tends to zero.

## Anti-theatre / hostile audit

- Finite common reporters already exist; reproving them is no progress.
- Pointwise infinite contraction already exists; restating its inequality is no progress.
- Critical limiting density has integral four; replacing finite-`sigma` field by that density is
  invalid for C49.
- A diagonal or target-fitted `D_sigma` is not the Route-R incidence.  `MCCOCHR` constructs the
  domain object and exact factorization interface only.
- Full Route-R closure still requires a source-defined noncompact Gamma/Julia family `D_sigma`
  whose reporter Laplace columns converge to `continuedXiAntiCausalWardResponse` and whose
  contraction is proved in the independently fixed source/Hardy polarizations.  That clause is
  RH-bearing by the existing cofinal connection-overspend theorem.

## Gates

- [x] 0 → 1: source-pure statement, exact finite/countable corpus audit, hostile scope fixed
- [x] complete countable paper proof of `(MCCOCHR.1)--(MCCOCHR.4)`
- [x] Lean formalization, direct module check, targeted final module build, axiom audit, umbrella
  wiring; global lint reaches unrelated unwired `HTGeometry.SupportEscapeDescentLaw`
- [ ] construct actual Gamma/Julia mate on this reporter
- [ ] prove polarized contractivity and deduce RH

## No-go closure

- **Exact killing theorem/mechanism:** none; `MobiusClockSplitReplicaOneCorner` proves the proposed
  cofinal split is graph-scale energy-safe.
- **Strongest positive survivor:** cubic split supplies a source-global, noncompact collision
  evacuation compatible with the singular Gamma normal scale.
- **New insight:** atomic collision is not C49's obstruction.  Missing datum is the countable
  half-line reporter topology and its polarized Gamma/Julia factorization.
- **Status:** source object formalized; actual Gamma/Julia mate remains active frontier.

## Log

- 2026-08-02 — Corpus audit located finite common reporter, pointwise infinite contraction,
  cofinal replica recovery, and graph-safe cubic physical clock splitting.  Promoted exact
  countable `L²` source object as next dependency-closed Route-R theorem.
- 2026-08-03 — Formalized the actual countable ordered-pair codiagonal, absolute summability,
  simultaneous right-half-plane Laplace transform, measurable `L²` reporter, literal integrated
  half-energy inequality, exact finite-Euler budget
  `(sigma-1)^3 (M3-M1*M2)`, and its four-unit boundary limit.  Added the new third critical clock
  moment `(sigma-1)^3 M3 -> 6`.  Cubic physical splitting now has zero codiagonal error after one
  inverse normal amplification and zero added energy after squared amplification on the actual
  Möbius Fisher source.  `lake env lean` and targeted builds pass; axiom audit reports only
  `propext`, `Classical.choice`, and `Quot.sound`.
