# Shifted-Xi projective Wronskian degree renewal

- **ID:** `shifted-xi-projective-wronskian-degree-renewal`
- **Stage:** 3-formalized
- **Route:** U
- **Type:** THEOREM (Lean)
- **Status:** `[LEAN-FORMALIZED] [UMBRELLA-WIRED] [CORPUS-NOVEL] [NOVELTY UNVERIFIED] [NOT RH]`
- **Depends on:** shifted-Xi monic Jacobi recurrence, positive-block differentiability of apex
  values and Jacobi coefficients, and local openness of positive definiteness.

## Exact claim

Write

```text
A_n(y) = P_n(y,1/y),
W_n(y) = A_(n+1)(y) A_n'(y) - A_n(y) A_(n+1)'(y),
alpha_n(y) = shifted-Xi monic Jacobi diagonal,
beta_n(y) = shifted-Xi monic Jacobi edge.
```

For `y>0`, `n>0`, and a positive shifted-Xi moment block through degree `n+3`, the apex values
obey the exact degree renewal

```text
A_(n+2) = (y^(-1)-alpha_(n+1)) A_(n+1) - beta_(n+1) A_n,
```

and their homogeneous projective Wronskians obey

```text
W_(n+1)
  = beta_(n+1) W_n
    + beta_(n+1)' A_n A_(n+1)
    + (y^(-2)+alpha_(n+1)') A_(n+1)^2.                 (R)
```

Identity (R) has no chart denominator and remains meaningful at both projective coordinate axes.

## Proof

Evaluate the monic orthogonal-polynomial Jacobi recurrence

```text
X P_(n+1) = P_(n+2) + alpha_(n+1) P_(n+1) + beta_(n+1) P_n
```

at `X=y^(-1)`. Positive-block identification of the canonical admission polynomials with the
monic orthogonal family gives the stated apex renewal.

Positive definiteness is open near `y`, so the renewal holds on a neighbourhood. The established
shifted-Xi flow theorems make `A_n`, `A_(n+1)`, `alpha_(n+1)`, and `beta_(n+1)` differentiable
there. Set `c=y^(-1)-alpha_(n+1)`. Differentiating `A_(n+2)=c A_(n+1)-beta_(n+1)A_n` gives

```text
A_(n+2)' = c' A_(n+1) + c A_(n+1)'
           - beta_(n+1)' A_n - beta_(n+1) A_n',
c' = -y^(-2)-alpha_(n+1)'.
```

Substitute these two formulas into
`W_(n+1)=A_(n+2)A_(n+1)'-A_(n+1)A_(n+2)'`. The two terms containing
`c A_(n+1)A_(n+1)'` cancel exactly. The remaining terms are

```text
beta_(n+1)(A_(n+1)A_n'-A_nA_(n+1)')
+ beta_(n+1)' A_n A_(n+1)
+ (y^(-2)+alpha_(n+1)') A_(n+1)^2,
```

which is (R).

## Hostile audit

- No zero of `A_n` or `A_(n+1)` is inferred from false RH; counting such contacts would be
  unsupported.
- No sign is assigned to the coefficient-motion terms. Positive `beta_(n+1)` alone does not make
  `W_(n+1)` inherit the sign of `W_n`.
- The theorem is not an RH criterion. It is the exact source-specific degree-transfer law needed
  before any signed phase action can be claimed.
- No numerical computation enters the statement or proof.

## New knowledge and revised open core

The obstruction to a monotone Route-U phase is not merely a bad affine chart. Under degree
renewal, projective orientation is transported by a positive Jacobi multiplier plus a signed
curvature source

```text
K_n = beta_(n+1)' A_n A_(n+1)
      + (y^(-2)+alpha_(n+1)') A_(n+1)^2.
```

Thus the missing all-degree action is a coefficient-motion balance law. Existing arithmetic
actions must control the cumulative signed source `K_n`; raw edge positivity or local angular
compactification cannot do so.

## Lean formalization

```text
formal/GaloisForLFunctions/RHTower/
XiShiftedCanonicalAdmissionCharacteristicApexProjectiveWronskianRenewal.lean
```

The module formalizes both exact identities. Direct
`lake env lean GaloisForLFunctions/RHTower/XiShiftedCanonicalAdmissionCharacteristicApexProjectiveWronskianRenewal.lean`
passes with zero diagnostics. Targeted
`lake build GaloisForLFunctions.RHTower.XiShiftedCanonicalAdmissionCharacteristicApexProjectiveWronskianRenewal`
passes `12027/12027`. Both public theorem audits report only
`[propext, Classical.choice, Quot.sound]`; forbidden-declaration scan is clean. The module is
imported by `GaloisForLFunctions.RHTower`.

## Log

- 2026-08-13 — exact paper proof completed after literal scratch Lean proof closed.
- 2026-08-13 — promoted to Stage 3 after direct Lean, targeted build, axiom, forbidden-token, and
  umbrella-wiring audits.
