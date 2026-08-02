# Relative admission-spectrum functoriality

- **ID:** HGT-relative-admission-spectrum
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** current `HTGeometry` contraction/orientation corpus and `RHTower` source transports
- **Statement:** The vanishing spectrum of a family of relative primitive obstructions is independent of the chosen ambient Green primitive and is preserved exactly by every chain transport whose induced map on admitted-primitive quotients is injective.

## Goal

Replace the manuscript's explanatory claim that multiple RH routes are “shadows of one law” by an
exact transfer theorem.  The theorem must distinguish a source-faithful transport from a consumer
that merely preserves a scalar trace.  It must also show why changing Green operator, section, or
primitive representative cannot remove the obstruction.

The theorem is abstract and proves no zero exclusion by itself.  Its scientific use comes from
instantiating the admission spectrum in independent arithmetic carriers and proving that their
explicit source transports either preserve it or necessarily become singular/nonfaithful.

## Gates

- [x] 0 -> 1 in-progress: exact statement, internal frontier audit, falsity attack, complete proof
- [x] 1 -> 2 fully-proven: hostile proof audit and `[PAPER-PROVED]`
- [ ] 2 -> 3 formalized: exact Lean theorem and axiom/lint gates
- [ ] 3 -> 4 publication-ready: at least three explicit route instantiations and one cross-route consequence

## Status labels

- `[CORPUS]` `relativePrimitiveObstruction_eq_zero_iff` already classifies one parameter.
- `[CORPUS]` `greenObservation_traceFactorization_iff_secondary_eq_zero` classifies observer loss.
- `[OPEN CORE]` no current theorem makes the entire parameter spectrum choice-independent and
  functorial under a source-faithful chain square.
- `[PAPER-PROVED]` Theorem RAS below; all quotient, naturality, injectivity, and choice obligations
  are closed without route-specific assumptions.
- `[NOVELTY UNVERIFIED]` external literature comparison is deferred by user instruction.

## Exact theorem

Let `R` be a field.  Let

```text
d : A0 -> A1,       e : B0 -> B1
T0 : A0 -> B0,      T1 : A1 -> B1
```

be linear maps with `e T0 = T1 d`.  Let `S <= A0` and `U <= B0` be admitted primitive sectors,
and suppose `T0(S) <= U`.  Put

```text
QA = A0 / (S + ker d),
QB = B0 / (U + ker e).
```

Then `T0` induces a canonical linear map `QT : QA -> QB`.

For a parameter type `P`, families `x : P -> A1`, `y=T1 x`, and primitive selectors
`h : A1 -> A0`, `k : B1 -> B0` satisfying

```text
d(h(x p)) = x p,
e(k(T1(x p))) = T1(x p),
```

define

```text
oA(p) = [h(x p)] in QA,
oB(p) = [k(T1(x p))] in QB,
SigmaA = {p | oA(p)=0},
SigmaB = {p | oB(p)=0}.
```

### Theorem RAS

1. **Completeness.** `p in SigmaA` iff `x p` has a primitive in `S`; similarly for `B`.
2. **Choice independence.** If `h'` is any other primitive selector on the family, then
   `[h'(x p)]=[h(x p)]` for every `p`.  Hence `SigmaA` is independent of Green choice.
3. **Naturality.** `QT(oA(p))=oB(p)` for every `p`.
4. **Faithful conservation.** If `QT` is injective, then `SigmaA=SigmaB`.
5. **Loss classification.** If `p in SigmaB \ SigmaA`, then `QT` is not injective; more exactly,
   `oA(p)` is a nonzero element of `ker QT`.  Thus a transport can make an unadmitted source
   parameter look admitted only by killing relative source information.

## Complete proof

### Induced quotient map

Take `a in S + ker d`; write `a=s+n` with `s in S` and `d n=0`.  By sector preservation,
`T0 s in U`.  By the chain-square identity,

```text
e(T0 n)=T1(d n)=0,
```

so `T0 n in ker e`.  Therefore `T0 a in U + ker e`.  The universal property of the quotient
gives `QT : QA -> QB`, with `QT([a])=[T0 a]`.

### Completeness

Assume `[h(x p)]=0`.  Then `h(x p)=s+n` for some `s in S` and `n in ker d`.  Applying `d` gives

```text
x p = d(h(x p)) = d s,
```

so `s` is an admitted primitive.  Conversely, if `s in S` and `d s=x p`, then
`h(x p)-s in ker d`; hence `h(x p)` lies in `S+ker d` and its quotient class vanishes.
The target proof is identical.

### Choice independence

If both `h(x p)` and `h'(x p)` are primitives of `x p`, then

```text
d(h(x p)-h'(x p))=0.
```

Their difference lies in `ker d`, which is killed in `QA`.  Their quotient classes are equal.
No injectivity of `d`, preferred section, or homotopy identity is needed.

### Naturality

By definition of the induced quotient map,

```text
QT(oA(p))=[T0(h(x p))].
```

The chain identity and the source primitive equation give

```text
e(T0(h(x p))) = T1(d(h(x p))) = T1(x p).
```

The target primitive equation gives `e(k(T1(x p)))=T1(x p)`.  Their difference therefore lies
in `ker e`, so the two representatives have the same class in `QB`.  Hence
`QT(oA(p))=oB(p)`.

### Faithful conservation and loss classification

If `QT` is injective, naturality yields

```text
oB(p)=0  iff  QT(oA(p))=0  iff  oA(p)=0.
```

Thus the spectra coincide.  If instead `p in SigmaB \ SigmaA`, then `oB(p)=0` and `oA(p)!=0`.
Naturality puts the latter nonzero class in `ker QT`, proving noninjectivity and identifying the
exact information killed.

## Hostile falsity and significance attack

### Attack: this is merely quotient functoriality

Correct at parent-theory level.  The abstract proof is short.  It becomes scientifically relevant
only if explicit arithmetic route transports instantiate `QT`, and at least one cross-route
consequence follows that is not already an RH equivalence.  Publication claim is forbidden until
that is done.

### Attack: Green choice may hide route dependence

Killed by part 2: all ambient primitive selectors differ by `ker d`, already quotiented out.
Route dependence can only enter through admitted sector `S`, source family `x`, or transport `T`.

### Attack: injectivity smuggles in RH

Not intrinsically, but a route-specific proof of injectivity could be RH-equivalent.  Every
instantiation must audit whether injectivity follows from source construction or is merely a renamed
zero-location assumption.

### Attack: all routes may use unrelated parameter families

Then theorem cannot unify them.  Explicit shadow maps are mandatory.  Absence of a chain square is
evidence of genuinely distinct routes, not permission to claim universality.

## Next exact claim

Construct the analytic admission-spectrum instantiation.  Compare the Hedenmalm Borel reflection
family, which has finite source energy throughout a nonzero centered strip, with the polarized
Euler/Hardy reflection family, whose finite-energy spectrum is exactly `{0}`.  Theorem RAS then
forces every transport intertwining those families and collapsing the former spectrum to the latter
to be nonfaithful (equivalently singular before Hilbert completion).  This is the first required
cross-route consequence.

## Log

- 2026-08-02 — created in Stage 1; exact theorem and complete proof recorded; novelty deliberately
  unverified pending later literature audit.
- 2026-08-02 — hostile proof audit passed.  Abstract theorem promoted to Stage 2; significance gate
  remains the explicit cross-route aperture instantiation.
