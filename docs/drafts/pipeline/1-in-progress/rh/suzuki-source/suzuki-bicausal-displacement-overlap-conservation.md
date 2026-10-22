# Suzuki bicausal displacement--overlap conservation

- **ID:** suzuki-bicausal-displacement-overlap-conservation
- **Stage:** 1-in-progress
- **Type:** UNIVERSAL LAW / SHARP NO-GO / SUZUKI FRONTIER THEOREM
- **Status:** `[CONJECTURE SHARPENED] [PAPER PROOF IN PROGRESS] [NOT YET LEAN]`
- **Terminal scope:** Decide the source-canonical positive-transport realization of Suzuki's
  rectangular RH criterion: either construct a capacity-one splice, or prove that the available
  capacity data cannot produce one.

## Corpus boundary

The corpus already proves:

1. the exact RH-equivalent completed-lag domination inequality;
2. sharp past/future Mangoldt log-Haar cells of common displacement two, modulo the known
   Ramaré--Zuniga Alterman capacity law;
3. a fully unconditional wider-cell version of the same transport;
4. monotone-branch payment outside the turning seam;
5. impossibility of positive-mass pointwise payment at a strict Suzuki apex;
6. a positive unbounded one-flank prime-block surplus.

It does **not** contain an aggregate mixed-cell overlap theorem, a splice feasibility identity,
or the full two-flank continuum surplus law below. Searches covered `formal/`, Stages 2/3, and
failed Suzuki routes. This card does not re-attempt pointwise apex transport.

## Conjecture C70: displacement--overlap conservation

Let `h>0`, and let a cumulative-mass partition be transported forward by `h` on the increasing
side of a turning point and left unshifted on the decreasing side. If the left aggregate target is

```text
L=(a,s+h]
```

and the right aggregate target is

```text
R=(s,b],
```

where `a<=s` and `s+h<=b`, then

```text
L union R       = (a,b],
L intersection R = (s,s+h].                                    (C70.1)
```

Consequently the target multiplicity is one off the seam and two on a seam of **exactly the same
width `h` as the causal displacement**. For every integrable real profile `Phi`,

```text
integral_L Phi + integral_R Phi
  = integral_(a,b] Phi + integral_(s,s+h] Phi.                  (C70.2)
```

Thus a mixed cell proof is capacity one exactly when its accumulated monotonicity slack dominates
the seam integral. The displacement used to repair one-sided quadrature cannot be made free at a
change of monotonicity: it reappears, with coefficient one, as duplicate target capacity.

For the sharp Mangoldt cells, `h=2`. For the already formalized unconditional Mertens cells, the
relative shift between the past and future partitions is

```text
h = 2 + 2*mangoldtLogHaarMertensRadius
  = mangoldtLogHaarTransportWidth.
```

So the corpus's unconditional widening does not solve the splice: it enlarges the unavoidable
overlap by exactly the same amount.

## Conjecture C71: critical tilted-tent two-flank surplus law

For `beta>0`, `L>0`, define the normalized full tilted tent

```text
r_(beta,L)(x) = exp(beta*x) * (1-|x|/L),   |x|<=L.
```

The continuum log-Haar two-flank surplus, in Suzuki lag coordinate `t=2x`, is

```text
D(beta,L)
  = 2 integral_(-L)^L (1-r_(beta,L)(x)) dx
  = 4L - 4*(cosh(beta*L)-1)/(L*beta^2).                       (C71.1)
```

Proof target: split at zero and integrate `exp(beta*x)*(1-|x|/L)`, or equivalently integrate the
triangular kernel against the bilateral Laplace character. The exact transform is

```text
integral_(-L)^L exp(beta*x)*(1-|x|/L) dx
  = 2*(cosh(beta*L)-1)/(L*beta^2).                            (C71.2)
```

At Suzuki's critical tilt `beta=1/2` and critical width `L=2`,

```text
D(1/2,2) = 16 - 8*cosh(1) > 2.                               (C71.3)
```

The strict inequality follows from the unconditional explicit exponential bounds already present
in the Lean toolchain: `exp(1)<2.7182818286` and `exp(-1)<0.3678794412`, hence
`cosh(1)<7/4`. Therefore the *continuum* Suzuki geometry has strictly more two-flank surplus than
the sharp bicausal seam's worst possible cost `2*apex`.

This overturns the premature conclusion that the positive-transport geometry is intrinsically
under-capacitated. S69's one-block constant is too small, but the complete critical two-flank
geometry is not.

## Sharp hostile test: capacity data alone cannot realize the surplus

The laws

```text
tau_n-2 <= F_(n-1),   F_n <= tau_n
```

alone do not force any positive apex-block slack. An admissible extremal mass configuration may
put a full mass `2` at one node `tau=c`, with `F_before=c-2` and `F_after=c`, and no flank mass in
the tent support. For every strict apex profile, the unique-apex theorem makes every positive-mass
pointwise target fail. Grouping cannot create flank surplus because this model has no flank atoms.

Hence no theorem quantified over all cumulative partitions satisfying only the two-unit capacity
band can prove the Suzuki splice. This is a sharp **information no-go**, not a claim about the
actual von Mangoldt measure.

The surviving actual-arithmetic statement is the normalized two-flank limit

```text
actualMangoldtTwoFlankSurplus(n) / apex(n) -> D(1/2,2).        (C72)
```

It follows mathematically from the prime number theorem / weighted Mangoldt weak convergence, but
that theorem is not formalized in this repository. C72 is not new mathematics and must not be
advertised as such. Its role is diagnostic: once imported with a dependency-closed Lean proof, it
would give eventual surplus `>2*apex`, exactly enough to clear C70's overlap ceiling. A proof still
must show that this scalar surplus can be assigned to the duplicated seam without violating cell
disjointness; that assignment is the remaining source-specific matching theorem.

## Terminal verdict criteria

This card may leave Stage 1 only after one of the following is proved on paper and in Lean:

1. **Closure:** actual Mangoldt critical two-flank surplus is assembled into a capacity-one mixed
   target, the completed Gamma reserve pays the constant channel, and the existing RH equivalence
   discharges RH.
2. **Dead end:** every source-canonical positive transport allowed by a precisely defined class is
   classified, and C70 plus an actual-Mangoldt upper obstruction rules out all members of that
   class. A no-go for one cell choice is insufficient.

No manuscript may call the whole Suzuki program a dead end from C70 alone. C70 kills the claim
that one-sided capacity bounds automatically splice; C71 proves the underlying continuum geometry
still has enough total surplus.

## Gates

- [x] exact prior-corpus and failed-route audit
- [x] exact universal seam statement isolated
- [x] exact critical two-flank transform derived
- [x] capacity-only countermodel identified
- [ ] dependency-closed paper proof of C70
- [ ] dependency-closed paper proof of C71 and strict critical excess
- [ ] exact actual-Mangoldt two-flank definition and Suzuki sample connector
- [ ] decide whether scalar surplus admits a disjoint seam assignment
- [ ] Lean formalization
- [ ] terminal RH proof or class-complete transport no-go

