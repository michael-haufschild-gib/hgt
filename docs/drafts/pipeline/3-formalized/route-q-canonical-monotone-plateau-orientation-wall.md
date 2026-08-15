# Route Q canonical monotone plateau orientation wall

- **ID:** `route-q-canonical-monotone-plateau-orientation-wall`
- **Stage:** 3-formalized
- **Type:** THEOREM / structural no-go with positive survivor
- **Routes:** Q primary; U comparison
- **Source:** `rh-current-frontier-map.md`, Route Q plateau-orientation survivor

## Status labels

`[PAPER-PROVED] [LEAN-PROVED] [NOVELTY UNVERIFIED] [NO RH CLAIM]`

## Question

Arbitrary measurable theta-to-Xi plateau transport is kinematic.  Does imposing the literal order
of the theta source select an arithmetic plateau geometry strong enough to orient the Xi
barycenter, or can the canonical order-preserving transport also be built without RH?

## Theorem Q-MONOTONE-PLATEAU-WALL

Write

```text
lambda_j = xiThermalNode (xiThermalEnumeration j) > 0,
M_0      = normalizedPrimeArchMoment 0,
mu_Xi    = sum_j lambda_j delta_(lambda_j).
```

There is an explicit nondecreasing measurable reporter `Q_mon : R -> R` such that

```text
(Q_mon)_*(M_0 thetaSource.law) = mu_Xi.                    (1)
```

It is obtained without a representation choice.  Normalize `mu_Xi`, restrict it to `[0,1]`, take
its generalized inverse `q_Xi`, and set

```text
Q_mon(x) = q_Xi(thetaSource.cdfFun(x)).                    (2)
```

Consequently every enumerated Xi thermal node has a positive theta-source fibre and, for every
`n >= 0`,

```text
integral Q_mon(x)^n d(M_0 thetaSource.law)(x)
  = xiThermalPositiveMoment n.                             (3)
```

The first-moment defect is nevertheless

```text
integral Q_mon d(M_0 thetaSource.law) - normalizedPrimeArchMoment 1
  = xiThermalOrientationEnergy >= 0.                       (4)
```

Its vanishing, and full prime--archimedean moment-witness status of `Q_mon`, are each equivalent to
RH.  Thus even canonical ambient source order does not provide Route Q's missing orientation.

## Heavy conjecture loop

### Q-MON-1 — ordered plateaus retain enough source arithmetic

**Conjecture.** Requiring `Q` to be nondecreasing in literal theta coordinate prevents the
unconditional plateau construction and forces the missing source upper barycenter inequality.

**Attack.** The theta CDF is strictly increasing and sends `thetaSource.law` to uniform interval
measure.  The generalized inverse of any probability measure on `[0,1]` is nondecreasing and sends
uniform measure to that target, including atomic targets.  Composition preserves order.

**Verdict:** false.  Lean proves the explicit monotone construction and exact pushforward `(1)`
without RH.

### Q-MON-2 — monotone plateau widths orient the first moment

**Conjecture.** Although monotone transport exists, its ordered plateau widths may force its
barycenter below the completed source barycenter.

**Attack.** The width of each quantile plateau is exactly its target atom mass
`lambda_j / M_0`; its location in rank space is determined by cumulative target masses.  Source
CDF uniformization removes the original density before the target quantile is applied.  Therefore
ordered plateau widths and cuts depend on the Xi target law, not theta arithmetic.  Pushforward
integration gives the positive thermal first moment, and the existing second-moment split gives
the opposite comparison `(4)`.

**Verdict:** false.  The defect is the same nonnegative orientation energy as for arbitrary
measurable transport and vanishes only under RH.

### Q-MON-3 — source order is a genuine invariant

**Conjecture.** One-dimensional source order survives probability-integral normalization as an
arithmetic invariant.

**Attack.** Every continuous atomless ordered source is conjugated to uniform rank by its CDF.
Any construction factoring only through that rank and a target quantile is invariant under
order-preserving reparameterization of the source.  It cannot distinguish the theta density from
another atomless source with the same rank coordinate.

**Verdict:** false as a producer; retained as the higher no-go principle below.

## Dependency-closed proof

The corpus proves `mu_Xi` is supported on `[0,1]` and

```text
mu_Xi(R) = M_0 > 0.
```

Hence `bar_mu_Xi = M_0^(-1) mu_Xi` is a probability measure.  Pull it back through the inclusion
`[0,1] -> R`, obtaining probability measure `nu_Xi` on the unit interval.  Define

```text
q_Xi(u) = sup {x in [0,1] : nu_Xi([0,x]) < u}.
```

Nested sublevel sets make `q_Xi` nondecreasing, hence measurable.  For every `x in [0,1]`, right
continuity of the CDF gives the exact generalized-inverse equivalence

```text
q_Xi(u) <= x  iff  u <= nu_Xi([0,x]).
```

Therefore

```text
volume(q_Xi^(-1)([0,x])) = nu_Xi([0,x]).
```

Finite Borel measures on a second-countable linear order are determined by closed lower
intervals, so `(q_Xi)_* volume = nu_Xi`.  Mapping through the subtype inclusion recovers
`bar_mu_Xi` because its restriction to `[0,1]` is itself.

The literal theta CDF is strictly increasing and its bundled unit-interval version sends
`thetaSource.law` to interval volume.  Thus `(2)` is nondecreasing and measurable, and map
composition proves

```text
(Q_mon)_* thetaSource.law = bar_mu_Xi.
```

Multiplication by `M_0` proves `(1)`.  Positive fibres and all identities `(3)` follow from `(1)`.
Substitution into the corpus identity

```text
xiThermalPositiveMoment 1
  = normalizedPrimeArchMoment 1 + xiThermalOrientationEnergy
```

proves `(4)`, nonnegativity, and the RH equality case.  Existing moment-representation rigidity
proves full witness status iff RH.  No hypothesis or unproved premise enters the theorem.

## Higher universal principle

**Rank is gauge, not arithmetic.**  A scalar atomless source law plus its ambient total order has a
universal normal form: uniform rank.  Monotone target quantization sees only this rank and the
target marginal.  It erases the source density that was supposed to supply prime--Gamma
orientation.  This explains why both continuous-carrier and plateau-carrier attacks stalled:
smoothness versus discontinuity changed the representative but not the source information retained.

Route Q must break rank-gauge invariance.  A viable survivor must retain arithmetic labels,
conditional incidence, a second non-comonotone observable, singular boundary indices, or an
equivalent structure not determined by the scalar pushforward law and ambient order.  Merely
asking for monotonicity, canonical quantiles, positive fibres, or all target moments cannot work.

## Route U comparison

Route U's polyphase and contact constructions likewise preserve a kinematic reconstruction while
losing the arithmetic orientation of a scalar remainder.  The Q theorem sharpens the comparison:
even selecting a canonical ordered representative does not restore information erased before the
pushforward.  U should therefore seek a source-labelled von-Mangoldt/Gamma incidence or cofinal
common budget, not another unlabelled scalar normal form.

## External novelty audit

- Classical component: generalized inverse/CDF transport on one-dimensional probability measures.
  Mathlib's public representation API documents uniform-interval realization, while its internal
  proof uses the same generalized-inverse mechanism:
  <https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Kernel/Representation.html>.
- Nearby Xi/theta literature studies harmonic-oscillator integral representations and
  real-rooted Fourier-kernel approximations, not the canonical self-weighted Xi atomic quantile or
  its exact RH-equivalent barycenter defect:
  <https://arxiv.org/abs/math-ph/0612086> and <https://arxiv.org/abs/1502.06844>.
- Nearby probability literature links distributions to Xi functional equations, but not this
  theta-source monotone transport/orientation wall:
  <https://www.maths.tcd.ie/EMIS/journals/EJP-ECP/article/view/3608/0.html>.
- Targeted searches on 2026-08-16 found no external occurrence of the combined theorem: literal
  theta CDF, self-weighted compact Xi thermal measure, explicit monotone quantile reporter, and
  first-moment defect equal to an RH-equivalent orientation energy.  Absence was not established;
  novelty remains unverified and is not claimed.

## Positive survivor

The deeper Cassini/Hurwitz corpus already instantiates the required rank-breaking structure.
It constructs an unconditional sequence of pairwise-separated finite continued-Cauchy
prime--Gamma packets whose evaluations converge to the orientation vector and whose exact source
energies converge to minus the orientation energy.  Replace “label/order law” in Route Q's open
core by this stricter target:

> prove cofinal nonnegative recurrence for one unconditional separated finite prime--Gamma packet
> sequence from source values alone.  Equivalently, find arbitrarily late favorable source scales;
> the stronger theta-specific reverse Cassini--Jensen/jet boundary sign remains sufficient.

Either statement forces the same orientation defect to vanish.  The new monotone theorem rules out
ambient one-dimensional order itself; the surviving packet condition retains actual prime--Gamma
labels and conditional incidence.

## Gates

- [x] 0 -> 1: exact falsifiable monotone-producer conjecture, hostile attack, positive survivor
- [x] 1 -> 2: dependency-closed proof and external novelty audit
- [x] 2 -> 3: unconditional Lean theorem, axiom audit, exact leaf `.olean`, umbrella wiring
- [ ] 3 -> 4: independent significance audit and standalone exposition

## Lean closure

Proved in
`formal/GaloisForLFunctions/RHTower/PrimeArchThetaCanonicalMonotonePlateauOrientationWall.lean`:

1. normalized Xi measure is almost everywhere supported on `[0,1]`;
2. its restriction to the unit interval is a probability measure;
3. explicit generalized inverse is monotone, measurable, and has exact target pushforward;
4. explicit theta reporter is nondecreasing and maps native theta mass to `mu_Xi`;
5. every Xi atom has positive source fibre and every positive thermal moment is reproduced;
6. first-moment defect is nonnegative and zero iff RH;
7. complete moment-witness status iff RH.

The capstone `routeQThetaMonotonePlateauReporter_orientationWall` has no premises.  Axiom audit of
it and both map theorems reports only `propext`, `Classical.choice`, and `Quot.sound`.  Direct
`lake env lean` check and exact leaf `lake build` succeeded.  The leaf `.olean` was built and the
module was wired into `RHTower.lean`; no umbrella or full-project build was run.

## Log

- 2026-08-16 — Q-MON-1 formulated after arbitrary plateau closure.
- 2026-08-16 — Explicit generalized inverse proof completed in scratch; generic automation was
  replaced by a direct order contradiction before promotion.
- 2026-08-16 — Source-order conjecture falsified; rank-gauge no-go and arithmetic-incidence
  survivor extracted.
- 2026-08-16 — Source module checked, exact leaf `.olean` built, axiom-audited, and umbrella import
  wired without an umbrella build.
- 2026-08-16 — Deeper corpus audit replaced generic arithmetic-incidence language by exact existing
  endpoint: eventual sign of an unconditional separated finite prime--Gamma packet sequence,
  equivalently theta-specific reverse Cassini boundary saturation.
