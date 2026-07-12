# The derivative-variable CCM spectral family must live on the Suzuki completion

- **ID:** `ccm-spectral-parameter-evans-completion-carrier-law`
- **Stage:** 2-fully-proven / not-new
- **Type:** THEOREM (paper), `[BRIDGE]`
- **Scientific status:** `[PROVED] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Parents:** Suzuki's generalized compact eigenvalue problem, closed-form completions, and
  `ccm-screw-null-global-log-regularity-law.md`

## Statement

Fix an aperture `a>0`. On the zero-mean space let

```text
K_a=(-Delta_N)^(-1)
```

and choose a metric shift `mu<inf spec(A_a)`. Suzuki's positive compact form is

```text
S_(a,mu)=G_a-mu K_a>0.                                  (1)
```

Its completion `H(S_(a,mu))` is isometric, under the closed derivative, to the form Hilbert space
of `A_a-mu I`. The spectrum of `A_a` is therefore the spectrum of the generalized problem

```text
G_a u=lambda K_a u,
u in H(S_(a,mu)).                                        (2)
```

Crucially,

```text
H(S_(a,mu)) is not a subspace of L2(-a,a).                (3)
```

Consequently the exact derivative-variable `L2` Evans map constructed for `ker G_a` does not
automatically extend to the nonzero spectral fibers in `(2)`. Every spectral-parameter realization
that insists on the generalized derivative variable is forced to supply at least one of the
following two carriers:

```text
regularity-lift branch:
  every generalized eigenvector at lambda<=0
  -> L2_0(-a,a) intersect Dom(c_(a,lambda)(D)),
  with continuous mean, support, residual, and affine-anchor maps;

completed-complex branch:
  an Evans/Fredholm complex defined directly on H(S_(a,mu)),
  carrying completed substitutes for the support seam, logarithmic multiplier,
  mean channel, and two affine channels.                  (4)
```

Here `c_(a,lambda)` is the zero-free logarithmic factor of the shifted exact symbol

```text
W_(a,lambda)(xi)=W_a(xi)-lambda.                          (5)
```

Only after one branch of `(4)` is established may the negative Morse charge be identified with
zeros of a finite Evans family built in this derivative variable.

There is a third realization which avoids `(3)`: work with the original eigenfunction
`v in L2(-a,a)` of `A_a`, not its completed derivative. The restricted-Weil multiplier equation
then yields an exact square Evans determinant. This is proved in
`ccm-restricted-weil-square-evans-determinant-law.md`. Thus `(4)` is a sharp law for the
derivative-variable route, not a universal obstruction to spectral-parameter Evans theory.

## Proof

For `v in H_0^1(-a,a)` and `u=Dv`, Suzuki proves

```text
Q_W^a(v)=<G_a u,u>,
||v||_2^2=<K_a u,u>.                                     (6)
```

Completing the core in the positive norm induced by `(1)` makes the closed derivative an
isometric isomorphism from the form Hilbert space of `A_a-mu I` onto `H(S_(a,mu))`. This converts
the ordinary eigenvalue equation for `A_a` into `(2)`, with the same discrete spectrum. Suzuki
also proves `(3)`.

On the dense smooth core, applying the Neumann Laplacian to `(2)` gives

```text
(W_a(D)-lambda)u=0 on (-a,a),                             (7)
```

because `-Delta_N K_a u=u`, while differentiating the screw convolution twice produces the exact
polar--Euler--Gamma multiplier `W_a(D)`. Conversely, `(7)` recovers `(2)` only after retaining the
two affine constants lost by second differentiation.

For `lambda=0` and an original `L2` screw null vector, the global logarithmic regularity theorem
proves that `c_a(D)u` belongs to `L2`, reconstructs `u` from its finite characteristic trace, and
defines the finite map

```text
M_a:F_a -> R_(L_a) direct_sum C^3.                        (8)
```

But `(3)` shows that a general vector in the completed spectral fiber `(2)` is not, merely by its
definition, an `L2` vector to which `(8)` or its shifted analogue can be applied. The operations
used by `(8)`--zero extension, global Fourier multiplication, point anchors, and Bessel residual
extraction--therefore require either the regularity lift in the first branch of `(4)` or continuous
extensions in the second branch. This proves the forced alternative within the derivative-variable
realization. `QED`

## Conditional finite Morse formula

Suppose the regularity-lift branch is proved and the shifted construction yields finite maps

```text
M_(a,lambda):F_(a,lambda)->R_(L_(a,lambda)) direct_sum C^3
```

with

```text
ker(A_a-lambda I) isomorphic to ker M_(a,lambda)          (9)
```

for every `lambda<=0`. Since `A_a` has discrete lower-bounded spectrum accumulating only at
`+infinity`, its negative spectrum is finite and then

```text
kappa(a)
 =sum_(lambda<0) dim ker M_(a,lambda),                    (10)

A_a>0
 iff M_(a,lambda) is injective for every lambda<=0.       (11)
```

Thus `(10)` is a valid target in the derivative variable, but not an unconditional consequence of
the existing screw `L2` Evans matrix. The eigenfunction-variable square determinant supplies the
corresponding unconditional kernel formula by a different route.

## Prime--Gamma resource consequence

If either branch of `(4)` is represented in prime-log Cauchy coordinates, its boundary transport
cannot be replaced by any finite logarithmic cancellation order. Lean proves

```text
not_summable_primeLogHerglotzTransportMassOrder_of_pos
```

for every positive transport and every finite order. The completed carrier must therefore retain
an infinite-order/nonlocal prime--Gamma boundary state; a finite rational or finite log-jet
surrogate cannot supply the required extension.

This is the positive content of the transport wall: the missing spectral domain has a prescribed
resource class.

## Scope and classification

The generalized eigenvalue equivalence and the failure of the inclusion in `(3)` are explicit in
Suzuki's Section 8. The conclusion is a domain-of-definition audit of the proposed Evans reduction,
so it is a bridge rather than new scientific knowledge. A faithful Lean formalization would first
require the closed screw form, its completion, the Neumann inverse, and the logarithmic multiplier;
these are absent from the formal tree. No abstract wrapper is added.

Primary source:

- [Suzuki, *Weil's quadratic form via the screw function*, Section 8](https://arxiv.org/abs/2606.09096)

## Gates

- [x] exact generalized compact eigenvalue problem identified
- [x] metric shift separated from the spectral parameter
- [x] completed spectral domain distinguished from raw `L2`
- [x] invalid automatic extension of the zero-fiber Evans matrix excluded
- [x] positive regularity-lift/completed-complex alternative proved for the derivative variable
- [x] conditional finite Morse formula stated with its missing hypothesis
- [x] eigenfunction-variable square Evans escape identified
- [ ] prove the generalized eigenvectors at `lambda<=0` enter the logarithmic Evans domain
- [ ] or construct the Evans/Fredholm complex directly on `H(S_(a,mu))`
- [ ] identify its determinant line with the restricted-Weil spectral-flow line
- [ ] prove zero negative Morse charge for every aperture
- [ ] RH
