# The CCM Galerkin limit diagonalizes without uniform aperture estimates

- **ID:** `ccm-galerkin-cofinal-diagonal-transfer`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper), `[BRIDGE]`
- **Scientific status:** `[PROVED HERE] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Parent source:** Connes--Consani--Moscovici, *Zeta Spectral Triples*, especially the form-core,
  compact-resolvent, finite determinant, and outlook theorems.
- **Statement:** At fixed arithmetic aperture, simplicity and evenness of the continuous lowest Weil
  eigenvalue force the CCM Galerkin ground vectors and their Fourier determinants to converge
  locally uniformly. Hence any continuous-aperture determinant limit can be transferred to a
  cofinal family of finite real-zero determinants by a diagonal choice of Galerkin dimensions; no
  estimate uniform in both cutoffs is required.

## Setup

Fix `lambda>1`, put `I_lambda=[lambda^(-1),lambda]`, and let `q_lambda=QW_lambda` be the closed,
lower-semibounded CCM Weil form on

```text
H_lambda=L2(I_lambda,d*u).
```

Let `A_lambda` be its self-adjoint compact-resolvent operator. Let `E_(lambda,M)` be the span of the
logarithmic Fourier modes with indices `|m|<=M`. The spaces are nested, invariant under inversion,
and their union is a form core for `q_lambda`.

Assume that the lowest eigenvalue `epsilon_lambda` of `A_lambda` is simple and that its unit
eigenvector `xi_lambda` is even under inversion. Let `epsilon_(lambda,M)` and
`xi_(lambda,M)` denote a unit lowest Ritz pair on `E_(lambda,M)`, with phase chosen whenever possible
so that

```text
<xi_(lambda,M),xi_lambda> >=0.
```

Write

```text
H_lambda(z)=integral_(I_lambda) xi_lambda(u)u^(-iz)d*u,
H_(lambda,M)(z)=integral_(I_lambda) xi_(lambda,M)(u)u^(-iz)d*u.       (1)
```

The finite function differs from the CCM regularized determinant only by the explicit nonvanishing
factor `-i lambda^(-iz)` and a nonzero scalar normalization.

## Fixed-aperture spectral convergence

`[PROVED]` As `M->infinity`,

```text
epsilon_(lambda,M) downarrow epsilon_lambda,
||xi_(lambda,M)-xi_lambda||_2 ->0.                                  (2)
```

Moreover, for all sufficiently large `M`, the finite lowest eigenvalue is simple and its eigenvector
is even.

### Proof

The Rayleigh--Ritz values decrease and are bounded below by `epsilon_lambda`. Since the union of the
Galerkin spaces is a form core, there are unit vectors `v_M` in the union converging to `xi_lambda`
in form norm. Their Rayleigh quotients tend to `epsilon_lambda`, so the variational principle gives
the first assertion of `(2)`.

Let `epsilon_lambda^(2)>epsilon_lambda` be the next eigenvalue and put

```text
gap_lambda=epsilon_lambda^(2)-epsilon_lambda>0.
```

For a unit Ritz ground vector, decompose

```text
xi_(lambda,M)=a_M xi_lambda+eta_M,
eta_M perpendicular to xi_lambda.
```

The spectral theorem gives

```text
q_lambda(xi_(lambda,M))-epsilon_lambda
 >=gap_lambda ||eta_M||_2^2.                                       (3)
```

The left side tends to zero, hence `eta_M->0`. Choosing the phase so that `a_M>=0` proves the second
assertion of `(2)`.

The second Ritz value is at least `epsilon_lambda^(2)` by min--max. Once the first Ritz value is
strictly below `epsilon_lambda^(2)`, it is simple. Because inversion commutes with the form and the
Galerkin projection, that simple vector has definite parity. If it were odd, it would be orthogonal
to the even continuous ground vector, and `(3)` would put its Rayleigh quotient at least at
`epsilon_lambda^(2)`, a contradiction. It is therefore even.

## Fixed-aperture determinant convergence

`[PROVED]` For every compact `K subset C`,

```text
sup_(z in K)|H_(lambda,M)(z)-H_lambda(z)| ->0.                       (4)
```

### Proof

On the fixed finite interval, Cauchy--Schwarz gives

```text
|H_(lambda,M)(z)-H_lambda(z)|
 <=||xi_(lambda,M)-xi_lambda||_2
   (integral_(I_lambda)|u^(-iz)|^2d*u)^(1/2).                        (5)
```

The second factor is bounded uniformly for `z` in `K`. Equation `(4)` follows from `(2)`. In
particular, the entire transforms converge locally uniformly, not merely pointwise.

## Cofinal diagonal theorem

Let `lambda_j->infinity`. Assume the continuous lowest eigenvalue is simple and even for every `j`.
Suppose there are nonvanishing exponential normalizations

```text
G_j(z)=exp(a_j+i b_j z) H_(lambda_j)(z)
```

such that

```text
G_j -> Xi                                                     (6)
```

locally uniformly on the open CCM strip.

`[PROVED]` There are Galerkin dimensions `M_j->infinity` such that the normalized finite
determinants

```text
G_(j,M_j)(z)=exp(a_j+i b_j z) H_(lambda_j,M_j)(z)                   (7)
```

converge locally uniformly to `Xi`. For all sufficiently large `j`, every zero of
`G_(j,M_j)` is real in the spectral variable.

### Proof

Exhaust the strip by compact sets `K_j`. For each fixed `j`, equation `(4)` allows `M_j` to be chosen
larger than `j` and so large that

```text
sup_(z in K_j)|G_(j,M_j)(z)-G_j(z)|<1/j.                            (8)
```

Equations `(6)` and `(8)` prove local uniform convergence along the diagonal. Increase `M_j` further
if necessary so that the finite lowest Ritz pair is simple and even. The CCM finite determinant
theorem then puts all its zeros on the real spectral axis.

In the zeta variable `s=1/2+iz`, those zeros have `Re(s)=1/2`, so their prime-clock reflected energy
is exactly zero. Hurwitz or the formalized logarithmic-boundary transfer theorem now shows that `(6)`
would imply RH.

## What this removes and what it does not

The result removes two artificial burdens from the route:

1. one need not prove Galerkin convergence uniformly as the arithmetic aperture grows;
2. one need not separately estimate the logarithmic horizontal defect of finite CCM zeros.

It does not prove either substantive continuous statement required in `(6)`: simplicity/evenness of
the continuous Weil ground state for a cofinal aperture family, or normalized locally uniform
convergence of its transform to `Xi`. The second still requires a projective comparison with the CCM
seed `k_lambda`, or another direct determinant argument carrying the full divisor.

## Novelty verdict

The proof is an application of standard Rayleigh--Ritz convergence for a form core, the spectral-gap
estimate, Cauchy--Schwarz on a fixed interval, and a diagonal argument. Its application closes a
bookkeeping gap in the CCM outlook, but it does not pass the novelty gate as new scientific
knowledge.

## Lean decision

The abstract ingredients already belong to standard spectral approximation theory. The repository
does not yet expose the closed Weil form, compact resolvent, or CCM determinant as Lean objects.
Formalizing a generic finite-dimensional shadow would not certify the source-specific bridge. No
Lean file is added.

## Gates

- [x] fixed-aperture Ritz eigenvalue convergence
- [x] fixed-aperture ground-vector convergence under simple isolation
- [x] eventual finite simple-even property
- [x] locally uniform convergence of the entire transforms
- [x] cofinal diagonal selection
- [x] automatic zero-energy specialization of the terminal transfer theorem
- [ ] continuous simple-even theorem for a cofinal aperture family
- [ ] continuous normalized determinant convergence to `Xi`
