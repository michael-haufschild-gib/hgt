# Every CCM screw null vector has global logarithmic transformed-trace regularity

> **2026-07-22 domain correction.** This theorem and its matrix detect the raw kernel
> `ker(G_a:L2_0->L2_0)` only. Suzuki's zero-eigenvalue problem lives on the extension of `G_a` to
> `H(S_(a,mu))`, which is not contained in raw `L2`. The former equation `(13)` claiming an RH
> equivalence is retracted; see `suzuki-completed-zero-mode-corona-seam-law.md`.

- **ID:** `ccm-screw-null-global-log-regularity-law`
- **Stage:** 2-fully-proven / not-new
- **Type:** THEOREM (paper), `[BRIDGE]`
- **Scientific status:** `[PROVED] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Parents:** distributional constant-coefficient ODE regularity and
  `ccm-log-symbol-dirichlet-exterior-reconstruction-law.md`

## Statement

Fix `a>0`, let `I=(-a,a)`, and factor the exact corrected aperture symbol as

```text
W_a=b_a c_a,
b_a(xi)=p_a(xi)/(1+xi^2)^(L_a),
degree p_a=2L_a,                                          (1)
```

with `c_a>0` and `c_a(xi)=log|xi|+O_a(1)`. Let `u in L2(R)` be supported in `[-a,a]` and suppose

```text
W_a(D)u=0 in distributions on I.                         (2)
```

Then

```text
v:=c_a(D)u belongs to L2(R),                             (3)
```

and its interior restriction lies in the finite characteristic space

```text
v|_I in F_a={f:p_a(D)f=0 on I}.                          (4)
```

Moreover, if `C_(a,I)` is the coercive logarithmic Dirichlet realization from
`ccm-log-symbol-dirichlet-exterior-reconstruction-law.md`, then

```text
u=C_(a,I)^(-1)(v|_I).                                    (5)
```

Thus every original `L2` screw null vector lies in the factorized category used by the exact finite
Evans Gram determinant.

## Proof

The logarithmic multiplier `c_a(D)` maps compactly supported `L2` functions into tempered
distributions, so `v` is well-defined distributionally. Equation `(2)` says

```text
b_a(D)v=0 on I.                                          (6)
```

Apply the local differential operator `(1+D^2)^(L_a)` to `(6)`. Multiplier commutation and `(1)`
give

```text
p_a(D)v=0 on I.                                          (7)
```

Every distributional solution of a nonzero constant-coefficient ODE on an interval is an
exponential polynomial. Hence `v|_I` is smooth and belongs to `F_a`, proving in particular

```text
1_I v in L2(I).                                          (8)
```

Since `u=1_Iu`, the exterior restriction of `v` is

```text
1_Ev=1_E c_a(D)1_Iu.                                     (9)
```

The logarithmic Dirichlet theorem proves that this cross-boundary block extends boundedly from
`L2(I)` to `L2(E)`. Thus `(9)` belongs to `L2(E)`. Together with `(8)`, this proves `(3)`.

Because multiplication by `c_a` is closed on `L2`, `(3)` implies that `u` belongs to the global
operator domain of `c_a(D)`. Put `f=v|_I`. The supported vector `u` then satisfies

```text
1_I c_a(D)u=f.                                           (10)
```

The coercive Dirichlet problem has a unique supported solution for the forcing `f`, so `(5)`
follows. `QED`

## Exact determinant consequence

Combine `(3)`--`(5)` with the rational Bessel residual theorem. For every aperture with nonempty
characteristic set, the residual, mean-zero condition, and two affine anchors form the finite map

```text
M_a:F_a->R_(L_a) direct_sum C^3.                         (11)
```

Every screw null vector corresponds bijectively to `ker M_a`. Therefore

```text
ker G_a={0}
 iff ker M_a={0}
 iff det(M_a^*M_a)>0.                                    (12)
```

If the characteristic set is empty, equation `(7)` reads `v=0` on `I`; the zero-forcing Dirichlet
uniqueness gives `u=0`, so the same statement holds with the empty determinant interpreted as one.

The former global reformulation

```text
RETRACTED: RH <-> for every a>0, det(M_a^*M_a)>0         (13)
```

is invalid without the additional regularity lift

```text
ker(Gtilde_a:H(S_(a,mu))->H(S_(a,mu))) subset j_a(L2_0).
```

What remains unconditional is `(12)`. A completion-safe RH reformulation uses the
eigenfunction-variable square Evans determinant instead.

## Positive CCM carrier law

Every successful direct screw proof must now carry the cofinal family of exact matrices `M_a`.
Their size is the real-characteristic multiplicity `d_a`, while each entry is obtained only after
the infinite logarithmic Dirichlet reconstruction. The proof obligation is positively stated as

```text
exact polar--Euler--Gamma Dirichlet reconstruction
  + rational Bessel boundary moments
  + mean and affine anchors
  -> a cofinally positive-definite Evans Gram family.      (14)
```

Finite spectral agreement or a raw characteristic polynomial cannot establish `(14)` because they
do not determine the reconstructed entries.

## Scope and classification

Constant-coefficient ODE regularity and bounded cross blocks are standard parent theory. This is a
route bridge, not new scientific knowledge. A faithful Lean formalization requires the logarithmic
multiplier and Dirichlet-form infrastructure absent from the current tree, so no wrapper is added.

The primary-literature comparison reinforces that classification. Suzuki's 2026 screw-form paper
constructs the Friedrichs realization of the restricted Weil form, uses Dirichlet-form methods, and
builds an entire boundary characteristic function from deficiency indices `(1,1)`, but it does not
give the real-characteristic factorization, Carleman exterior reconstruction, or finite residual
Gram `(11)`. Connes--Consani--Moscovici's 2025 spectral-triple paper computes regularized finite
determinants and leaves their normalized convergence to `Xi` as the proof-bearing conjecture. The
present theorem is an exact fixed-aperture reduction, not that convergence theorem.

Primary sources:

- [Suzuki, *Weil's quadratic form via the screw function*](https://arxiv.org/abs/2606.09096)
- [Connes--Consani--Moscovici, *Zeta Spectral Triples*](https://arxiv.org/abs/2511.22755)
- [Connes--Consani--Moscovici, *Zeta zeros and prolate wave operators*](https://arxiv.org/abs/2310.18423)

## Gates

- [x] transformed trace defined distributionally
- [x] interior trace proved exponential-polynomial
- [x] exterior trace proved `L2` by the logarithmic cross block
- [x] global logarithmic operator-domain membership proved
- [x] every screw null vector identified with a Dirichlet reconstruction
- [x] unconditional fixed-aperture finite determinant equivalence proved
- [x] unconditional cofinal determinant equivalence to RH recorded
- [ ] prove `det(M_a^*M_a)>0` for every aperture
- [ ] RH
