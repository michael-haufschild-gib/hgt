# Framed relative completion index

- **ID:** `ULF-FBG-003`
- **Stage:** 1-in-progress
- **Parents:** `ULF-FBG-001`, `ULF-FBG-002`, `ULF-FBG-005`, `ULF-DSA-003`
- **Exact surviving RH edge:** source construction of a relative framed class whose nuclear price
  is below one and whose completed integer is escape multiplicity

## Big picture

`ULF-FBG-002` constructs source formation as a framed nuclear cycle. Its multiplier projection
has a fixed norm-one defect at every nonzero grade, while its prime-mixed nuclear shadow is a
trace-norm loop of trace one. This proves why unframed completion is information-neutral and why
every closed scalar reader loses the grade.

The next object is not another producer, receiver, or projection. It is the **relative class of
two reciprocal framed completions after their common four-channel `J`-frame is removed**.

Fresh comparison retired the naive version of this programme. Theta normal formation depends on
`delta log p`, while cubic completion depends on `(log p)/delta`; they do not have the same
one-dimensional principal symbol. `ULF-FBG-005` proves the correct gluing: the two variables are
reciprocal legs with product `(log p)^2`, and their compact/split tensor has an exact `O(2,2)`
`J`-Gram equal to the full prime-mixed `T`.

## Required theorem

Construct from literal integer/Poisson formation, before divisor specialization,

```text
mathfrak T_E      Euler/prime reciprocal framed nuclear cycle,
mathfrak T_theta  additive theta-completion reciprocal framed cycle,
K_univ            their common four-channel J-principal frame.              (FRC.1)
```

Prove all of the following as one theorem:

1. both cycles factor through `K_univ`, with theta and completion occupying its reciprocal legs;
2. subtracting `K_univ` gives a canonical relative mapping-cone class `Delta_rel`;
3. `Delta_rel` retains prime/depth labels and unsquared Euler coefficients;
4. it has a source-derived nuclear representative `R_rel` satisfying

```text
||R_rel||_1 <= B_Euler < 1;                                      (FRC.2)
```

5. completion pairs `Delta_rel` with the unsigned horizon cocycle, and after specialization

```text
<Delta_rel,horizon_q> = thetaKakutaniEscapeMultiplicity(q) in Z. (FRC.3)
```

Then any strict-right copy would give an integer equal to one by the existing escape theorem but
strictly below one by `(FRC.2)`, contradiction. Reflection excludes strict-left copies.

## First attack: completion functor on the reciprocal `J`-Gram

The Route-P identity already proves primewise

```text
formation metric anomaly
 = phase-matched completion companion + primitive source weight.             (FRC.4)
```

Both metric terms are nonsummable; their difference is the summable unsquared primitive source.
`ULF-FBG-001/002` supplies degree-one projective normal frame, exact normal/cotangent
transgression, and norm-one prime-infinity projection jump. `ULF-FBG-005` supplies its reciprocal
split completion frame and proves on every finite packet

```text
A_(delta,E)* J A_(delta,E)=T_E.                                  (FRC.5)
```

First unresolved theorem is functoriality of `(FRC.5)` under the actual singular theta
completion. It must preserve the `J`-Gram cancellation before positive closure, absolute value,
or observer trace, while its relative remainder inherits a native Schatten-one bound. Equality
of divergent traces or leading `log(p)^2/p` rates is insufficient.

## Falsifiers

- `K_univ` depends on a chosen Xi zero, divisor ordinate, or analytic multiplicity.
- comparison matches only traces, asymptotics, scalar counterterms, or identifies the reciprocal
  variables `delta log p` and `(log p)/delta`.
- subtraction deletes primitive source remainder or squares Euler coefficients.
- bounded landing from finite zero horizon is used; `ULF-INHD-001` proves it cannot create the
  completion-born class.
- `R_rel` is obtained by pushing the source budget through a singular map without a native
  trace-norm estimate.
- common prime-independent ghost is inserted; its existence is already RH-equivalent.
- target escape unit is the universal projective kink or the conserved `J`-Gram itself. Both exist
  for every nonzero grade and must cancel before the relative pairing.

## Current status

Open. Source framed cycle, exact topology defect, and reciprocal four-channel `J`-Gram are proved.
Route-P scalar principal-part cancellation and summable remainder are Lean-proved. Missing content
is singular-completion functoriality of the `J`-Gram plus a nuclear norm native to the relative
completion topology. No selected divisor may enter their construction.
