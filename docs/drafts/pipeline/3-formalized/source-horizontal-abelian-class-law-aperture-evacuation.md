# Source-horizontal abelian class-law aperture evacuation

- **ID:** SH-ABELIAN-APERTURE-EVACUATION
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `rh-current-frontier-map.md`, Frankenstein adaptive-contiguity/vacuum-fusion seam
- **Statement:** Two fixed convergent abelian zeta class laws realize every reflected adaptive
  prime orientation exactly on a canonical two-class aperture, but the aperture has exponentially
  vanishing mass; among two-class prime-primary realizations, its order/socle statistics are
  minimal.

## Goal

Decide whether the missing adaptive observer is absent at coefficient level or whether its real
obstruction is admission. Preserve prime label, horizontal orientation, and exact source weights.

## Gates

- [x] 0 -> 1: exact source-pure statement and falsifiers fixed
- [x] 1 -> 2: dependency-closed proof below
- [x] 2 -> 3: exact Lean theorem and scoped audit
- [ ] 3 -> 4: external priority and significance audit

## Status labels

- `[LOCAL-RESEARCH]` Existing class laws, adaptive odds, and contiguity endpoint are formal.
- `[FALSIFIED]` Exact arithmetic event realization is not missing.
- `[FALSIFIED]` Exact information disintegration is not missing; corpus already proves the KL
  observer chain rule.
- `[PAPER-PROVED]` Canonical realization, exponential evacuation, and statistic minimality below.
- `[LEAN-PROVED]` Exact realization, actual-law evacuation, statistic forcing/minimality, and
  multiplicity-resolved Xi specialization are axiom-audited and umbrella-wired.
- `[LEAN-PROVED]` Strong pivot: admitted mass times adaptive Jeffreys work tends to zero in both
  orientations, including for every `XiZeroCopy`.
- `[BRIDGE]` KL chain rule/data processing are classical; this card does not claim those as new.
- `[NOVELTY UNVERIFIED]` Cross-corpus source-horizontal application has not passed priority audit.

## Frozen theorem

Fix a prime `p`, `0 < a < 1`, and an integer `N >= 1`. Let

```text
theta+ = (sigma,tau) = (1,1-a),
theta- = (sigma,tau) = (1,1+a).
```

Both lie in the convergence chamber. Let

```text
A_N = (Z/pZ)^(N+1),
B_N = Z/p^(2N)Z.
```

Under each class law, admit the two-point event `{A_N,B_N}` and call `A_N` success. Then

```text
P_theta+(A_N | {A_N,B_N}) = q_p(Na),
P_theta-(A_N | {A_N,B_N}) = q_p(-Na),
q_p(u) = p^(u-1)/(1+p^(u-1)).
```

The exact unnormalized admissions are

```text
W_+(N) = p^((a-2)(N+1)) + p^(-2N-1+a),
W_-(N) = p^(-(a+2)(N+1)) + p^(-2N-1-a).
```

The unnormalized admissions are each at most `2 p^(-(N+1))`. Each normalized admission is its
fixed positive class-law normalizer times this expression, hence also tends to zero exponentially.

For statistic minimality, suppose two prime-primary classes have order exponents `o_A,o_B` and
socle exponents `s_A,s_B`, and their two conditional odds under `theta+` and `theta-` are the
displayed adaptive odds. Then subtraction and addition of the two log-odds equations force

```text
s_A - s_B = N,
o_A - o_B = 1-N.
```

Since a nontrivial finite abelian `p`-group has `1 <= s <= o`, both classes are nontrivial and

```text
s_A >= N+1,  o_A >= N+1,  s_B >= 1,  o_B >= 2N.
```

The canonical pair attains all four bounds. Thus it maximizes admission among all two-class
prime-primary realizations for these fixed source parameters and still evacuates exponentially.

## Complete paper proof

For a prime-primary class with order `p^o` and socle order `p^s`, the unnormalized class-law weight
at `(sigma,tau)` is `p^(-sigma o-tau s)`; the common positive normalizer cancels in conditional
odds.

For `A_N`, `(o,s)=(N+1,N+1)`. For `B_N`, `(o,s)=(2N,1)`. Under `theta+`, their weight ratio is

```text
p^(-(N+1)-(1-a)(N+1)+2N+(1-a)) = p^(Na-1).
```

Under `theta-`, it is

```text
p^(-(N+1)-(1+a)(N+1)+2N+(1+a)) = p^(-Na-1).
```

Dividing a positive odds ratio `r` by `1+r` gives the asserted conditional probabilities. Adding
the two weights gives `W_+` and `W_-`. Since `a<1`, every exponent in either sum is at most
`-(N+1)` for `N>=1`, proving the unnormalized exponential upper bound. Multiplication by the fixed
finite class-law normalizer preserves convergence to zero.

For any competing pair, equality of the two log-odds gives

```text
-(o_A-o_B)-(1-a)(s_A-s_B) = Na-1,
-(o_A-o_B)-(1+a)(s_A-s_B) = -Na-1.
```

Subtracting yields `2a(s_A-s_B)=2Na`, hence `s_A-s_B=N` because `a>0`. Adding and substituting
gives `o_A-o_B=1-N`. If `B` were trivial, then `s_B=o_B=0`; the two difference equations and
`s_A<=o_A` contradict `N>=1`. Thus `s_B>=1`. The claimed four lower bounds follow from
`s_A=s_B+N`, `s_A<=o_A`, and `o_B=o_A+N-1`. The canonical statistics attain equality.

No RH statement or equivalent receiver is used.

## Lean realization

`formal/GaloisForLFunctions/RHTower/SourceHorizontalAbelianClassLawApertureEvacuation.lean`
formalizes:

- the canonical elementary/cyclic classes and their exact order/socle statistics;
- all four exact two-observable class weights;
- the actual normalized class-law conditional probabilities in both orientations;
- exact admission identities, exponential upper bounds, and both `Tendsto ... 0` theorems;
- forced statistic differences and canonical lower-bound minimality;
- a `XiZeroCopy` specialization retaining analytic multiplicity.

`formal/GaloisForLFunctions/RHTower/SourceHorizontalAbelianClassLawInformationEvacuation.lean`
then proves the stronger information-current obstruction. For `u >= 0`, adaptive Jeffreys work is
at most `2u log p`. Multiplying this linear bound by either actual exponentially vanishing
admission proves

```text
admission_+(N) * Jeffreys_p(Na) -> 0,
admission_-(N) * Jeffreys_p(Na) -> 0.
```

The Xi capstone states both limits for each multiplicity-labelled divisor copy.

Direct compilation and the exact leaf target pass. `#print axioms` on both conditional identities,
both limit theorems, both statistic theorems, and the Xi capstone reports only `propext`,
`Classical.choice`, and `Quot.sound`.

## Hostile audit and no-go closure

- **Exact killing mechanism:** coefficient-faithful conditional probabilities can be manufactured
  exactly, but only by sending both admitted atoms to growing order/socle. Source mass vanishes.
- **Strongest positive survivor:** canonical pair is statistic-minimal and optimizes two-atom
  admission; exponential evacuation is structural, not a poor choice of classes.
- **New insight:** missing primitive is replenishing source mass across scale. A fixed finite-law
  observer only relocates horizontal information into a rare-event aperture. This is the same
  failure shape as summably negligible Route-U curvature renewal and normalized Gamma-shell
  blindness.
- **Stronger survivor:** linear conditional-information amplification cannot compensate canonical
  geometric admission loss; actual mass-weighted information current vanishes. Any Route-U splice
  must therefore add literal source information influx, not merely reuse KL disintegration.
- **External audit:** conditional relative-entropy chain rules and data processing are classical;
  Cohen--Lenstra-type finite-abelian-group measures are established parent theory. No source found
  for this exact two-observable HGT specialization. Priority remains unverified.
- **Next conjecture:** replace fixed-law observation by a source-generated renewal/cobordism whose
  Radon--Nikodym information influx exactly pays aperture loss. It must prove a nonsummable physical
  charge, not assume uniform admission.

## Log

- 2026-08-12 — C1 “observer construction absent” falsified; paper theorem closed and promoted.
- 2026-08-12 — Lean module compiled, axiom-audited, exact-leaf-built, and umbrella-wired; promoted
  to Stage 3.
- 2026-08-12 — C2 “information conservation identity absent” falsified by existing KL chain rule;
  C3 mass-weighted information evacuation proved in a second Lean module, axiom-audited,
  exact-leaf-built, and umbrella-wired.
