# CCM affine Euler-cutoff Fisher transport

- **ID:** `ccm-affine-euler-cutoff-fisher-transport`
- **Stage:** 1-in-progress
- **Type:** THEOREM / FOUR-UNIT CCM SOURCE BRIDGE
- **Scientific status:** `[PAPER PROOF CLOSED] [LEAN OPEN] [NOVELTY UNVERIFIED] [NOT RH]`
- **Parents:**
  - `../2-fully-proven/not_new_scientific_knowledge/dyadic-squarefree-euler-fock-source-factorization.md`
  - `../3-formalized/mobius-incidence-clock-gini-fisher-four-unit-law.md`
  - `mobius-contact-sonin-kadison-four-unit-rh.md`

## Frontier

The proved source unitary uses the unique factorization

```text
n=d m^2,   d squarefree.
```

At inverse temperature `sigma>1`, it factors the normalized Euler law into the independent
squarefree and residual laws

```text
s_sigma(d)=mu(d)^2 d^(-sigma)/S_sigma,
S_sigma=zeta(sigma)/zeta(2 sigma),

r_sigma(m)=m^(-2 sigma)/zeta(2 sigma).
```

The physical Euler cutoff is not the old squarefree cutoff.  At critical scale it is the affine
joint constraint

```text
X_sigma(d)+Y_sigma(m)<=u,

X_sigma(d)=(sigma-1)log d,
Y_sigma(m)=2(sigma-1)log m.
```

This mismatch was the remaining source-side cutoff obstruction before Gamma--Sonin completion.

## Theorem: affine residual invisibility

For every fixed `u>=0`, couple the two laws above and put

```text
Z_sigma=X_sigma+Y_sigma.
```

Then, as `sigma->1+`,

```text
P(X_sigma<=u<Z_sigma) -> 0.                              (A1)
```

Let

```text
T^sq_sigma=-2(X_sigma-E X_sigma),
T^res_sigma=-2(Y_sigma-E Y_sigma),
T^E_sigma=T^sq_sigma+T^res_sigma.
```

The state and centered Fisher tangent cut by the physical affine clock satisfy

```text
||1_(Z_sigma<=u)-1_(X_sigma<=u)||_L2 -> 0,               (A2)

||1_(Z_sigma<=u)T^E_sigma
    -1_(X_sigma<=u)T^sq_sigma||_L2 -> 0.                 (A3)
```

Consequently the rank-two Fisher contact commutator for the actual Euler cutoff has the same
critical Hilbert--Schmidt limit as the squarefree cutoff:

```text
lim_(sigma->1+)
 ||[P^E_(sigma,u),X^E_sigma]||_HS^2
 =squarefreeMobiusCriticalFisherCutoffWardLimit(u).      (A4)
```

In particular,

```text
lim_(u->0+)
 lim_(sigma->1+)
 ||[P^E_(sigma,u),X^E_sigma]||_HS^2/(2u)=4.              (A5)
```

Thus the dyadic square channel does not consume, duplicate, or move the four-unit boundary
density.  Its affine cutoff displacement is asymptotically invisible at the critical source
scale.

## Proof

The residual clock is nonnegative.  Its second moment is

```text
E(Y_sigma^2)
 =4(sigma-1)^2/zeta(2sigma)
    sum_(m>=1)(log m)^2 m^(-2sigma).                    (P1)
```

On `1<sigma<=5/4`, the summand is bounded by `(log m)^2/m^2`, whose series converges.  Hence

```text
E(Y_sigma^2)->0,
E(Y_sigma)->0,
Y_sigma->0 in L2 and in probability.                    (P2)
```

The existing squarefree critical-clock theorem gives

```text
X_sigma => Exp(1),
E X_sigma ->1.                                          (P3)
```

For `u>0` and `0<delta<u`,

```text
{X_sigma<=u<Z_sigma}
 subset {Y_sigma>delta} union {u-delta<X_sigma<=u}.      (P4)
```

The first probability tends to zero by `(P2)`.  The limsup of the second is

```text
exp(-(u-delta))-exp(-u)
```

by `(P3)`, because both endpoints are continuity points of the exponential law.  Let
`delta->0+`; this proves `(A1)`.  At `u=0`, nonnegativity of both clocks makes the mismatch event
empty.  Since the difference of the two indicators is exactly the mismatch indicator, `(A2)`
follows.

On the mismatch event, `0<=X_sigma<=u`.  By `(P3)`, `E X_sigma` is bounded near the critical
point.  Therefore `T^sq_sigma` is uniformly bounded on that event, and `(A1)` gives

```text
||1_(X_sigma<=u<Z_sigma)T^sq_sigma||_L2->0.              (P5)
```

Moreover

```text
E((T^res_sigma)^2)=4 Var(Y_sigma)<=4E(Y_sigma^2)->0.     (P6)
```

Equations `(P5)`--`(P6)` and the triangle inequality prove `(A3)`.

The source unitary sends Euler state and tangent exactly to

```text
psi^E_sigma=psi^sq_sigma tensor psi^res_sigma,

chi^E_sigma
 =chi^sq_sigma tensor psi^res_sigma
  +psi^sq_sigma tensor chi^res_sigma.
```

Equations `(A2)`--`(A3)` therefore give norm convergence of both cutoff state/tangent pairs.
Rank-one operator formation is norm-continuous, and the Fisher contact is the symmetric rank-two
combination.  Its cutoff commutator consequently converges in Hilbert--Schmidt norm to the
squarefree cutoff commutator.  The existing exact squarefree Ward limit proves `(A4)`, and its
proved boundary density proves `(A5)`.

## Hostile audit

1. **Fixed-cutoff error:** false.  The theorem uses critical scaling before `u->0`; it does not
   claim exact finite-`sigma` intertwining.
2. **Tail deletion:** false.  Every residual square channel remains in the affine cutoff.  Its
   entire effect is controlled by its source probability law and vanishing scaled clock.
3. **Target-fed transport:** absent.  No Xi zero, divisor, Weil sign, or boundary graph occurs in
   `(A1)`--`(A5)`.
4. **Hidden RH estimate:** absent.  The only infinite series is absolutely convergent at exponent
   two.  The critical singularity remains entirely in the already-proved squarefree clock.
5. **RH overclaim:** `(A4)` closes the squarefree-to-Euler physical-cutoff seam only.  Gamma--Sonin
   graph-core convergence to `[P_u,D_Xi]` and its nonexpansive completed incidence remain open.

## Lean gates

- [ ] global squarefree-times-square probability equivalence
- [ ] residual critical clock tends to zero in `L2`
- [ ] affine cutoff state mismatch tends to zero
- [ ] affine cutoff centered-tangent mismatch tends to zero
- [ ] rank-two contact commutator transport
- [ ] connector to `tendsto_squarefreeMobiusCriticalFisherCutoffCommutatorEnergy`
- [ ] connector to four-unit boundary density
- [ ] umbrella import and axiom audit

