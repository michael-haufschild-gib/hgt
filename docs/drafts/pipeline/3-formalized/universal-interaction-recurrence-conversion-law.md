# Universal interaction recurrence-constraint conversion law

- **ID:** `universal-interaction-recurrence-conversion-law`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) / MASTER PAPER CANDIDATE
- **Date:** 2026-07-31
- **Formal source:**
  `formal/GaloisForLFunctions/HTGeometry/UniversalInteractionRecurrenceConversionLaw.lean`
- **External priority:** OPEN
- **Nature significance gate:** OPEN

## One invariant

Let \(\mu\) be any probability law on a finite projective phase carrier.
Write

\[
  \tau(\mu)
  =
  \text{operational temporal dimension},
  \qquad
  \rho(\mu)
  =
  \text{rank}_{\mathbb Q}
  \{\text{almost-sure projective phase constraints}\}.
\]

The carrier has fixed projective capacity \(D-1\), and

\[
  \boxed{\tau(\mu)+\rho(\mu)=D-1.}
\]

Consequently, for any two phase laws on the same carrier with
\(\tau(\mu)\leq\tau(\nu)\),

\[
  \boxed{
  \tau(\nu)-\tau(\mu)
  =
  \rho(\mu)-\rho(\nu).}
  \tag{C}
\]

Temporal directions are not added independently of recurrence structure.
Every gained temporal direction is exactly one lost recurrence constraint.

For a finite spectrum \(E\), \(\rho(E)\) is the rational rank of its exact
balanced integer energy-relation lattice and \(\tau(E)\) is the rational
rank of its anchored gap packet. Equation `(C)` therefore becomes an exact
spectral law.

## Universal weak-interaction realization

Take arbitrary spectra with \(m+1\) and \(n+1\) levels. Their uncoupled
tensor-sum spectrum has \(D=(m+1)(n+1)\) levels and temporal rank at most
\(m+n\). Hence it carries at least

\[
  (D-1)-(m+n)=mn
\]

independent projective recurrence constraints.

For every \(\delta>0\), a single separable diagonal interaction

\[
  V_{ab}=x_a y_b
\]

exists with operator norm at most \(\delta\) such that the coupled spectrum
has no nonzero balanced integer energy relation. The interaction therefore
converts the complete uncoupled constraint rank into temporal dimension:

\[
  \boxed{
  \tau(H_0+V)-\tau(H_0)
  =
  \rho(H_0)
  \ge mn,}
  \qquad
  \boxed{\rho(H_0+V)=0.}
  \tag{I}
\]

The same witness satisfies, for every bounded observable \(O\) and every
real \(t\),

\[
  \|\alpha_t^{H_0+V}(O)-\alpha_t^{H_0}(O)\|
  \le 2|t|\delta\|O\|,
  \tag{F}
\]

while every positive full-support long-time survival-return moment reaches
its unavoidable permutation floor at every replica order.

Thus an arbitrarily weak interaction can be invisible on every prescribed
bounded time horizon while completely changing the completed recurrence
geometry.

## Formal declarations

- `phaseLawTemporalDimension_sub_eq_constraintRank_sub`;
- `projectiveTemporalRank_sub_eq_relationRank_sub`;
- `projectiveTemporalRank_gain_eq_relationRank_of_maximallyProjective`;
- `projectiveRelationRank_eq_zero_of_maximallyProjective`;
- `exists_smallSeparableInteraction_fullConstraintConversion`.

## What the law subsumes

| Corpus result | Status under `(C)` and `(I)` |
|---|---|
| additive-to-multiplicative temporal-rank jump | rectangle-sector instance of exact constraint conversion |
| weak-interaction recurrence singularity | complete conversion can coexist with `(F)` |
| all-order replica collision floors | zero post-coupling relation rank |
| product rectangle relations | explicit \(mn\)-dimensional constraint sector released by coupling |
| l-bit temporal-rank growth | each independent interaction coefficient releases one projective recurrence constraint |
| noninteracting l-bit ceiling | unresolved recurrence constraints occupy the remaining \(2^N-1-N\) capacity |
| Anderson locality/recurrence separation | spatial confinement does not fix relation rank, so it does not fix temporal dimension |
| observer-dependent temporal dimension | changing observer or clock changes zero-action constraint rank while total visible capacity stays fixed |
| no finite replica cutoff | finite detector depth sees only a height truncation of the relation lattice, not its full rank |
| recurrence-swap interaction reconstruction | selected order-two relations recover additive cuts and their Boolean atoms |
| countable relation-hull metric entropy | the relation lattice fixes orbit carrier; state weights metrize it; covering entropy bounds first return |
| finite dissipative threshold | apply phase conversion to the peripheral carrier; transient mass controls whether recurrence remains observable |
| local/perturbative completion no-gos | bounded-time or finite-depth data need not determine the full constraint lattice |

## Corpus results not collapsed into one false formula

The following are consequences only after their own physical structure is
specified:

1. open-system survival thresholds require a peripheral/transient split;
2. actual first-return deadlines require a metric on the relation hull and
   state weights;
3. atomless spectra lie outside the finite rational-rank formula and have a
   zero-density recurrence phase;
4. spatial locality, l-bit locality, or Anderson localization do not follow
   from recurrence arithmetic;
5. black-hole, horizon, or cosmological claims require a model-specific
   identification of the finite spectral carrier and observable algebra.

These are scope boundaries, not hypotheses hidden inside `(C)` or `(I)`.

## Hostile novelty boundary

No novelty credit is due for:

- rank-nullity by itself;
- Kronecker--Weyl equidistribution;
- generic rational independence;
- sinc dephasing;
- Duhamel perturbation estimates;
- replica collision counting;
- the existence of product rectangle relations.

The priority-sensitive candidate is their exact physical closure:

> every finite pair admits an arbitrarily weak single separable interaction
> that converts its complete pre-coupling recurrence-constraint rank
> one-for-one into operational temporal dimension, simultaneously erases
> all post-coupling balanced relations, minimizes all positive full-support
> long-time return moments, and remains dimension-free close on bounded
> observation horizons.

Primary literature searches found adjacent results on generic quantum
recurrence-time scaling, rationally independent local free fermions, and
spectral-form-factor moment obstructions. No searched source states the
full conversion theorem. This is not yet a completed priority audit.

## Verification

Targeted foreground compilation with cached output passes:

```text
lake env lean \
  GaloisForLFunctions/HTGeometry/UniversalInteractionRecurrenceConversionLaw.lean \
  -o .lake/build/lib/lean/GaloisForLFunctions/HTGeometry/UniversalInteractionRecurrenceConversionLaw.olean
```

Axiom audit of every load-bearing declaration reports only:

- `propext`;
- `Classical.choice`;
- `Quot.sound`.

No `sorry`, `admit`, custom `axiom`, `opaque`, or `unsafe` declaration is
used. Final module build and repository lint are reserved for publication
audit.
