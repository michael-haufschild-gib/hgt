# CCM prime-source ground incidence and divisor response

- **ID:** `ccm-prime-source-ground-incidence-response`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper), `[BRIDGE]`
- **Scientific status:** `[PROVED HERE] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Parent theories:** concavity of variational spectral floors, Hellmann--Feynman, and Kato
  perturbation theory for a simple isolated eigenvalue
- **Statement:** At fixed aperture, the restricted Weil floor is a concave function of the finite
  prime-power coefficient vector. Its gradient is the distinguished ground-state autocorrelation
  at each prime power, its Hessian is the negative reduced-resolvent Gram form, and the derivative
  of the CCM characteristic function is the Mellin transform of the same incidence response.

## Coefficient-pointed Weil family

Fix an aperture `a>0`, put `lambda=e^a`, and let

```text
N_a={n>=2:log n<2a}.
```

In logarithmic coordinates, write the closed restricted Weil form as

```text
q_b(f,g)
 =q_infinity(f,g)-sum_(n in N_a)b_n V_n(f,g),          (1)
```

where `q_infinity` contains the archimedean and pole terms, each `V_n` is the bounded symmetric
prime-power correlation form, and the actual zeta point is

```text
b_n=Lambda(n).                                         (2)
```

Equivalently one may absorb `n^(-1/2)` into `b_n`; all statements below are invariant under that
fixed coordinate rescaling.

Let `A_b` be the self-adjoint operator associated with `(1)` and define its floor

```text
epsilon(b)=inf_(||f||=1)q_b(f,f).                      (3)
```

## Concavity and source incidence

`[PROVED; BRIDGE]` The function `epsilon:R^(N_a)->R` is concave and locally Lipschitz. If its ground
eigenvalue at `b` is simple and isolated, with normalized real eigenvector `xi_b`, then

```text
partial_(b_n)epsilon(b)=-V_n(xi_b,xi_b).               (4)
```

In the half-interval representation of
`ccm-finite-prime-parity-hankel-carrier.md`, the right side is precisely the distinguished
autocorrelation sample at `log n`, including the fixed `n^(-1/2)` normalization.

### Proof

For every unit vector `f`, the map

```text
b |-> q_b(f,f)
```

is affine. Its pointwise infimum over the unit sphere is concave. Boundedness of the finite family
`V_n` gives local Lipschitz continuity. Under the simple-isolated hypothesis, Kato's bounded-form
perturbation theorem supplies a differentiable local eigenpair. Differentiating

```text
epsilon(b)=q_b(xi_b,xi_b)
```

and using normalization and the eigenvalue equation cancels the two eigenvector-derivative terms,
leaving `(4)`.

Thus the ground floor is a pointed source functional: its first derivative remembers the actual
prime coefficient attached to every distinguished autocorrelation channel.

## Negative reduced-resolvent Hessian

Let `h=(h_n)` be a real coefficient direction and put

```text
V_h=sum_n h_n V_n,
v_h=operator representing V_h,
R_b^perp=(A_b-epsilon(b))^(-1) on xi_b^perp.            (5)
```

Then

```text
D^2 epsilon(b)[h,h]
 =-2 <P_perp v_h xi_b,
        R_b^perp P_perp v_h xi_b>
 <=0.                                                   (6)
```

More generally,

```text
D^2 epsilon(b)[h,k]
 =-2 Re <P_perp v_h xi_b,
            R_b^perp P_perp v_k xi_b>.                 (7)
```

### Proof

Differentiate

```text
A_b xi_b=epsilon(b)xi_b,
<xi_b,xi_b>=1
```

in direction `h`, choosing the local phase with `<xi_b,D_h xi_b>=0`. Since

```text
D_h A_b=-v_h,
D_h epsilon(b)=-<xi_b,v_h xi_b>,
```

projection to `xi_b^perp` gives

```text
D_h xi_b
 =R_b^perp P_perp v_h xi_b.                            (8)
```

Differentiating `(4)` and polarizing proves `(6)`--`(7)`. Positivity of `R_b^perp` follows because
`epsilon(b)` is the simple lowest eigenvalue.

The Hessian is therefore a negative Gram form. Its size is governed by the true even spectral gap,
while its vectors are exactly the prime-source incidence responses.

## Divisor-facing characteristic response

Let

```text
F_b(z)=M_lambda(xi_b)(z)                               (9)
```

be the Mellin characteristic function, after the fixed nonvanishing CCM exponential is removed.
Then

```text
D_h F_b(z)
 =M_lambda(R_b^perp P_perp v_h xi_b)(z).              (10)
```

Equation `(10)` follows immediately from `(8)` and linearity of the Mellin transform. If `F_b(0)`
is nonzero and the normalization is chosen even, differentiation of `log F_b` gives the induced
response of the odd relative trace germ; normalized division by the centred coordinate then gives
the even trace-moment response formalized in `CriticalTraceMomentGerm.lean`.

Thus one static incidence object couples all four required components:

```text
coefficient direction h
  -> prime autocorrelation v_h xi_b
  -> archimedean-plus-prime reduced resolvent R_b^perp
  -> Mellin characteristic response D_h F_b
  -> divisor/trace moments.                            (11)
```

## Positive global topology

The compact-open regular-germ quotient forgets the coefficient direction `h`: the formalized
critical-disc Euler-unit action is dense on every fixed-divisor regular fibre. Equations `(4)`,
`(6)`, and `(10)` give the required pointed lift. The topology for a cofinal CCM argument must
control simultaneously

```text
sum_n h_n V_n(xi_b,xi_b),
||R_b^perp P_perp v_h xi_b||_2,
sup_(z in K)|M_lambda(R_b^perp P_perp v_h xi_b)(z)|,
```

for every compact substrip `K`, together with the divisor/multiplicity point. This is strictly
stronger than compact-open convergence of the local regular germ.

## Route consequence

The open bilinear radial-prolate transfer can now be stated positively as a source-response bound
at the actual von Mangoldt point:

```text
lambda^a
 ||R_b^perp P_perp v_h xi_b||_2 ->0
```

at the appropriate normalized coefficient comparison and for every `a<1/2`, or in the weaker
quadratic Rayleigh-excess form from `ccm-rayleigh-excess-determinant-transfer.md`. A parity proof
uses the same incidence vectors in the `T_a+H_a` and `T_a-H_a` sectors.

The theorem does not supply that cofinal estimate. It proves that the carrier is neither a local
germ invariant nor a free spectral statistic: it is the reduced-resolvent incidence tensor at the
actual weighted prime source.

## Novelty and significance verdict

Concavity, Hellmann--Feynman, the reduced-resolvent Hessian, and eigenvector response are standard
spectral perturbation theory. Their CCM assembly identifies the correct carrier but introduces no
new parent-theory mechanism. This is a bridge, not new scientific knowledge.

## References

- T. Kato, *Perturbation Theory for Linear Operators*.
- M. Suzuki, *Weil's quadratic form via the screw function*, arXiv:2606.09096.
- A. Connes, C. Consani, H. Moscovici, *Zeta Spectral Triples*, arXiv:2511.22755.

## Lean decision

The formal tree proves the local Euler-orbit quotient and trace-moment inverse but has no parameterized
closed Weil form or Kato eigenprojection interface. Formalizing abstract finite-dimensional
Hellmann--Feynman would be wrapper work. No Lean file is added.

## Gates

- [x] concavity of the coefficient-pointed Weil floor proved
- [x] prime autocorrelation gradient proved
- [x] negative reduced-resolvent Hessian proved
- [x] Mellin/divisor response identity proved
- [x] pointed incidence topology specified
- [ ] cofinal radial-prolate reduced-resolvent bound
- [ ] parity-margin preservation at the actual von Mangoldt point
- [ ] locally uniform divisor-carrying CCM determinant limit
