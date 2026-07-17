# Finite RG jets are blind to hypertranscendental generation

- **ID:** `finite-rg-jet-blindness-to-hypertranscendence`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / NONPERTURBATIVE NO-GO
- **Scientific status:** `[PROVED HERE] [BRIDGE] [PARENT-DERIVED]`
  `[NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Statement:** Every finite Taylor jet of an analytically linearizable one-coupling RG map and
  its exact beta field is matched by an algebraic RG germ with an algebraic exact beta field.
  Consequently RG-generation HT cannot be certified from any finite collection of perturbative
  coupling coefficients alone.

## Setup

Translate a hyperbolic fixed point to zero.  Let `R` be an analytic germ with

```text
R(0)=0,              R'(0)=lambda,              0 < |lambda| != 1, (1)
```

and let `Phi` be its normalized Poincare germ:

```text
Phi(0)=0,            Phi'(0)=1,
R(Phi(z))=Phi(lambda z).                                         (2)
```

Write `kappa=Phi^(-1)`.  After choosing a logarithm of `lambda`, the exact local beta field is

```text
beta(t)=(log lambda) kappa(t)/kappa'(t).                          (3)
```

## Algebraic shadow theorem

For every integer `N >= 0`, there is an algebraic analytic germ `R_N` with the same `N`-jet as
`R` and an algebraic exact beta field `beta_N` with the same `N`-jet as `beta`.

More explicitly, let `P_N` be the Taylor polynomial of `Phi` through degree `N+1`.  Then

```text
P_N(z)-Phi(z)=O(z^(N+2)),             P_N(0)=0, P_N'(0)=1.        (4)
```

Let `Q_N` be its local compositional inverse and define

```text
R_N(t)=P_N(lambda Q_N(t)),
beta_N(t)=(log lambda) Q_N(t)/Q_N'(t).                            (5)
```

The polynomial equation `P_N(Q_N(t))=t` makes `Q_N` algebraic over `C(t)`.  Hence both `R_N` and
`beta_N` are algebraic germs.  They satisfy the exact identities

```text
R_N(P_N(z))=P_N(lambda z),
beta_N(R_N(t))=R_N'(t) beta_N(t).                                (6)
```

## Proof of jet agreement

We use the standard contact-order lemma: if two locally invertible germs tangent to the identity
differ by `O(z^M)`, then their local inverses also differ by `O(t^M)`.  Applying it to `(4)` gives

```text
Q_N(t)-kappa(t)=O(t^(N+2)).                                      (7)
```

For the step map, put `t=Phi(z)`.  Since `Q_N(Phi(z))=z+O(z^(N+2))`, equations `(2)` and `(5)` give

```text
R_N(Phi(z))
  =P_N(lambda z)+O(z^(N+2))
  =Phi(lambda z)+O(z^(N+2))
  =R(Phi(z))+O(z^(N+2)).                                        (8)
```

Because `Phi'(0)=1`, contact order in `z` and `t` agrees.  Thus `R_N-R=O(t^(N+2))`.

For the beta field, write `Q_N=kappa+delta`, where `(7)` gives
`delta=O(t^(N+2))` and `delta'=O(t^(N+1))`.  Then

```text
Q_N/Q_N' - kappa/kappa'
  =(delta kappa' - kappa delta')/(Q_N' kappa')
  =O(t^(N+2)),                                                   (9)
```

because `kappa(t)=t+O(t^2)` and both derivatives in the denominator are units.  Hence
`beta_N-beta=O(t^(N+2))`.  In particular the `N`-jets of both pairs agree.

## Sharp interpretation

The theorem does not say that a finite proof can never establish HT.  A finite functional
constraint plus global divisor, singularity, monodromy, or Galois information can do so.  It says
that finite Taylor data alone cannot:

```text
for each finite order N,
the observed RG and beta coefficients admit an exact algebraic completion.   (10)
```

The algebraic completion may depend on `N`; no single algebraic germ is asserted to match all
orders.  This dependence is precisely why successively longer perturbative series cannot by
themselves cross the HT boundary.

## Physical consequence

RG-generation HT is strictly nonperturbative in the jet sense.  A finite-loop beta function, a
finite normal-form calculation, or finitely many derivatives of a nonlinear scaling field cannot
distinguish

```text
an algebraically generated exact flow
from a hypertranscendentally generated exact flow.                (11)
```

The discriminator must see an all-order or global constraint: an infinite critical-preimage tree,
a natural boundary, monodromy, a differential Galois group, or incompatibility with every rational
invariant differential.

For the Abdesselam--Chandra--Guadagni p-adic RG, this kills a tempting but unproductive program:
computing more Taylor coefficients of the unstable scaling field, including its quadratic
curvature, cannot decide its HT status.  Their analytic continuation and complex singularity
geometry, not another perturbative coefficient, are the live objects.

## Anti-theatre and novelty gate

The proof is an elementary application of analytic conjugacy, Taylor truncation, algebraic local
inversion, and contact order.  It is useful field infrastructure, not new mathematics.  Its role is
to remove finite-jet and finite-loop theatre from the research program and to force the next move
onto global differential-Galois geometry.

## Lean boundary

Mathlib already knows that power-series truncation agrees coefficientwise below the cutoff.  A Lean
wrapper of that fact would not formalize the analytic inverse-contact lemma, algebraicity of the
inverse germ, or beta-field agreement, and would add no substantive theorem.  Formalization should
wait until the corpus has a genuine local-germ composition/inversion layer capable of expressing
the complete statement `(4)`--`(9)` unconditionally.

## Parent sources

- T. L. Curtright and C. K. Zachos, *Renormalization Group Functional Equations*,
  <https://arxiv.org/abs/1010.5174>.
- G. Fernandes, *A survey on the hypertranscendence of the solutions of Schroeder's, Boettcher's
  and Abel's equations*, <https://arxiv.org/abs/2102.12168>.

## Gates

- [x] Algebraic shadow constructed at every finite jet order.
- [x] Exact step and beta constraints retained by the shadow.
- [x] Jet-agreement proof given for both the RG map and beta field.
- [x] Scope limited to finite Taylor data rather than finite mathematical proofs in general.
