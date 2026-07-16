# The completed Möbius contraction has the reciprocal projective Ward connection

- **ID:** `mobius-squarefree-reciprocal-projective-transfer`
- **Stage:** 2-fully-proven
- **Type:** THEOREM / HTGEOMETRY--RHTOWER BRIDGE
- **Scientific status:** `[PROVED] [LEAN ALGEBRA CORE] [BRIDGE] [NOT RH]`
- **Lean:** `GaloisForLFunctions.RHTower.MobiusSquarefreeReciprocalTransfer`
- **Parents:** `MobiusFiniteSchurTransfer.lean`; `InfiniteMobiusSignedChannel.lean`;
  `InfiniteMobiusLaplaceMultiplier.lean`; `ProjectiveHorizonWardSeam.lean`;
  `../3-formalized/gamma-moving-base-capacity-congruence.md`.

## Theorem

Let `sigma>1` and put `s=sigma+z`, initially with `Re z>=0`.  The normalized all-prime signed
Möbius shift is a contraction and its causal Laplace multiplier is

```text
tau_sigma(s)=zeta(2sigma)/(zeta(sigma) zeta(s)).          (1)
```

The squarefree higher-trace correction

```text
c_sigma(s)=zeta(2s)/zeta(2sigma)                         (2)
```

is holomorphic and nowhere zero for `Re s>1/2`.  On `Re s>=sigma`, its Dirichlet series gives
`|c_sigma(s)|<=1`.  Therefore `c_sigma tau_sigma` is still a causal contractive multiplier, and
direct cancellation gives

```text
M_sigma(s)
 :=c_sigma(s)tau_sigma(s)
 =1/zeta(sigma) * zeta(2s)/zeta(s)
 =1/(zeta(sigma) Z_sq(s)).                               (3)
```

Write the completed zeta source as

```text
Xi(s)=C(s)zeta(s),
X_sq(s)=Xi(s)/zeta(2s)=C(s)Z_sq(s).                      (4)
```

The Gamma-completed Möbius transfer is then

```text
T_sigma(s)=C(s)^(-1)M_sigma(s)
           =1/(zeta(sigma)X_sq(s)).                     (5)
```

The base normalization is constant in `s`, so its doubled logarithmic connection is

```text
2 d log T_sigma
 =-2 X_sq'/X_sq
 =Q_sq.                                                  (6)
```

Equivalently, the reciprocal projective transition `-X_sq^(-2)` is, up to a nonzero constant,
the square of the completed characteristic transfer of the actual Möbius contraction.  Its
anti-causal component is consequently the already proved current

```text
P_anti(2 d log T_sigma)=P_anti Q_sq=ell_E.               (7)
```

No Xi zero or divisor packet is used to construct `(1)--(6)`.

## Proof

Equation `(1)` is the formalized Laplace multiplier identity for the normalized signed Möbius
shift.  Multiply `(1)` by `(2)` and cancel `zeta(2sigma)` to obtain `(3)`.  Equations `(4)--(5)`
are definitions and cancellation.  Logarithmically differentiating `(5)` proves `(6)`.  The
projective reciprocal-horizon seam theorem and fixed-current localization give `(7)`. `QED`

## What this changes

The Ward current is not an output column selected after inspecting the Xi divisor.  It is the
connection of a source-defined transfer assembled from:

```text
actual Möbius coisometry
  x safe squarefree higher-trace correction
  x Gamma completion
  = reciprocal projective-horizon transfer.              (8)
```

This removes the generic-colligation objection from the route.  The source operator, its finite
contractivity, its critical Fisher score, and its projective connection are now independently
constructed.

## Exact remaining estimate

The Gamma multiplier `C^(-1)` is not bounded in the ordinary vertical `L2` multiplier norm, so
ordinary Hardy or fixed-Fock completion cannot carry `(8)`.  General HT geometry predicts the
correct recipient: the polarized critical Gevrey, multifiltered derived boundary.  The local
Gamma chart comparison is now known to preserve tangent capacity up to bounded congruence.

The sole metric theorem still needed is:

> **[CONJECTURE -- DERIVED MOBIUS--LAURENT WARD CONTRACTION.]** The completed transfer `(5)` extends
> the finite Möbius contractions to the source-polarized critical HT boundary.  On the
> distinguished completed Möbius Fisher score of squared norm four, its logarithmic boundary
> transgression is nonexpansive and has normal component `(7)`.

This gives

```text
||ell_E||_2^2<=4,                                        (9)
```

and the existing off-line Cauchy threshold then proves RH.

## No-go and positive general HT statement

Every finite Möbius multiplier is causal.  Hence no ordinary fixed-polarization Hilbert limit of
those multipliers can create a nonzero anti-causal component.  The anti-causal Ward class must be
a derived boundary defect of the noncommuting source-depth/observable-order limit.

Positively, `(6)--(7)` exhibit a concrete general-HT phenomenon: a family of finite causal
contractions can acquire a nonzero opposite-polarization connection only as the obstruction to
extending its source comparison across a polarized critical completion.  The resulting
connection class, rather than a scalar determinant, is the conservative invariant.

## Gates

- [x] actual Möbius contraction constructed and formalized
- [x] causal multiplier identified with reciprocal zeta
- [x] safe squarefree correction identified and Lean-formalized
- [x] completed transfer identified with reciprocal `X_sq`
- [x] logarithmic connection identified with `Q_sq`
- [x] anti-causal component identified with `ell_E`
- [x] local Gamma capacity distortion bounded
- [ ] construct the derived critical completed transfer
- [ ] prove it is nonexpansive on the distinguished four-unit score
- [ ] RH

