# Restricted summation has an invisible aperture gauge

- **ID:** `ccm-restricted-summation-aperture-gauge`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper), `[BRIDGE]`
- **Scientific status:** `[PROVED HERE] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Parent source:** Connes--Consani--Moscovici, *Zeta Spectral Triples*, Sections 7--8;
  Connes--Consani, *Spectral triples and zeta-cycles*, Sections 3 and 6
- **Statement:** On the aperture `[lambda^(-1),lambda]`, the restricted summation map cannot see
  even zero-integral source corrections supported strictly inside `(-lambda^(-1),lambda^(-1))`.
  Point evaluation is surjective on this kernel, so the source condition `f(0)=0` can be imposed
  exactly without changing the CCM approximant. This removes the apparent two-constraint mismatch,
  but it does not regularize the zero-extended prolate endpoints.

## Setup

For `lambda>1`, define

```text
E(f)(u)=u^(1/2) sum_(n>=1) f(nu),
R_lambda E(f)=E(f)|_[lambda^(-1),lambda].
```

Let `C_even` be any linear class of even functions on `R` containing even smooth compactly
supported functions and on which the displayed sums are defined on the aperture. Put

```text
K_lambda={b in C_c^infinity(R)_even:
          support(b) subset (-lambda^(-1),lambda^(-1)),
          integral_R b=0}.
```

## Theorem

`[PROVED HERE]` The following hold.

1. `K_lambda subset ker(R_lambda E)`.
2. The evaluation map `ev_0:K_lambda->C`, `ev_0(b)=b(0)`, is surjective.
3. Consequently, if `f in C_even` has zero integral, there is a function `f_0` of the same ambient
   regularity as `f`, differing from `f` by a smooth compactly supported function, such that

   ```text
   f_0(0)=0,
   integral_R f_0=0,
   R_lambda E(f_0)=R_lambda E(f).
   ```

In particular, the finite-aperture image depends only on the class of `f` modulo `K_lambda`, and
the condition `f(0)=0` has a representative in every zero-integral class.

## Proof

Choose `a` with `0<a<lambda^(-1)`. Let `phi` be an even smooth bump supported in `(-a,a)` with
`phi(0)=1`. Let `psi` be an even smooth bump supported in `(-a,a)`, with support disjoint from a
neighborhood of zero and with nonzero integral. Then

```text
b=phi-(integral phi/integral psi)*psi
```

is even, smooth, supported in `(-a,a)`, and satisfies

```text
b(0)=1,   integral b=0.                                 (1)
```

For `u in [lambda^(-1),lambda]` and `n>=1`,

```text
nu>=lambda^(-1)>a.
```

Therefore `b(nu)=0` and hence

```text
R_lambda E(b)=0.                                        (2)
```

Scalar multiples of `b` prove surjectivity of `ev_0` on `K_lambda`. If `f` has zero integral, set

```text
f_0=f-f(0)b.
```

Equation (1) gives `f_0(0)=0` and `integral f_0=0`, while (2) gives
`R_lambda E(f_0)=R_lambda E(f)`. This proves all assertions.

## CCM consequence

The global radical construction uses the codimension-two source space

```text
S_0^even={f: f(0)=Fourier(f)(0)=0}
```

and `Fourier(f)(0)=integral f`. The finite-lambda CCM seed `h_lambda` is defined by enforcing the
second condition exactly. Since the compressed-Fourier eigenvalues of `h_(0,lambda)` and
`h_(4,lambda)` are distinct, `h_lambda(0)` is generally nonzero. The theorem shows that this point
defect is not an invariant of the finite-aperture approximant: subtracting `h_lambda(0)b` leaves
`k_lambda=R_lambda E(h_lambda)` exactly unchanged while enforcing both scalar conditions.

This observation kills the tempting normalized constraint-determinant obstruction. The nonzero
two-mode determinant measures a choice of source representative, not a class invariant after
passing through `R_lambda E`.

## Exact limitation

The prolate functions used by CCM are functions on `[-lambda,lambda]` extended by zero. They are
piecewise smooth but generally do not vanish to infinite order at the endpoints. Adding the central
bump above preserves that endpoint regularity; it does not put the source in the Schwartz space.
Thus the remaining analytic issue is not the two scalar conditions. It is the closability of the
global-radical/Poisson argument on zero-extended prolate sources at the exponentially small leakage
scale.

Equivalently, a proof must control the lower tail

```text
1_(0,lambda^(-1)) E(f),
```

which Poisson identifies with the inverted upper tail of `E(Fourier(f))`. That arithmetic summation
tail, not the point constraint, is the first genuine Weil--prolate transfer operator.

## Novelty verdict

The support argument is elementary once the restricted summation map is written down. It usefully
repairs the source-domain bookkeeping in the CCM route, but it fails the anti-theatre and
parent-theory gates for new scientific knowledge. Its correct classification is `[BRIDGE]`.
