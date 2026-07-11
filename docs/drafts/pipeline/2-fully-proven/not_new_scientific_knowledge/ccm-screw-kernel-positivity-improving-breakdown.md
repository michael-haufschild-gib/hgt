# Large-aperture CCM simplicity requires sign-indefinite spectral geometry

- **ID:** `ccm-screw-kernel-positivity-improving-breakdown`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / NECESSITY THEOREM / `[BRIDGE]`
- **Scientific status:** `[PROVED HERE] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Parent source:** Masatoshi Suzuki, *Weil's quadratic form via the screw function*,
  arXiv:2606.09096, equations (1.3), (2.9)--(2.11), and the proof of Theorem 1.4.
- **Statement:** Above an explicit aperture threshold, the exact restricted Weil operator has
  positive cross-couplings between disjoint nonnegative vectors. Therefore a cofinal CCM
  simple-even theorem must use sign-indefinite spectral geometry: parity-separated min--max,
  oscillation/no-crossing, source transversality, or projective comparison.

## Setup

Use Suzuki's additive logarithmic coordinate. For `a>0`, the restricted Weil form on
`C_c^infinity(-a,a)` is

```text
QW^a(f,g)
 = integral_(-a)^a integral_(-a)^a
     K(x-y) f(y) conjugate(g(x)) dx dy,                 (1)

K=-g''                                                     (2)
```

in the distributional sense, where for `t>0`

```text
g(t)
 =-4(e^(t/2)+e^(-t/2)-2)
  +sum_(n<=e^t) Lambda(n)n^(-1/2)(t-log n)
  -(t/2)(psi(1/4)-log pi)
  -(1/4)(Phi(1,2,1/4)-e^(-t/2)Phi(e^(-2t),2,1/4)).     (3)
```

Let `rho>1` be the unique real root of

```text
rho^3-rho-1=0,                                           (4)
```

and put

```text
t_*=log rho.                                               (5)
```

## Exact regular kernel away from prime-power atoms

`[PROVED]` If `t>0` and `t!=log n` for every integer `n>=2`, then

```text
K(t)=e^(t/2)-e^(-5t/2)/(1-e^(-2t)).                       (6)
```

In particular,

```text
K(t)>0  iff  e^(3t)-e^t-1>0  iff  t>t_*.                 (7)
```

### Proof

The prime-power hinge terms in `(3)` have zero classical second derivative away from their atoms
`t=log n`. The linear term also disappears. The exponential term contributes

```text
-(e^(t/2)+e^(-t/2))
```

to `g''`. Expanding the Lerch term gives

```text
(1/4)e^(-t/2)Phi(e^(-2t),2,1/4)
 =(1/4)sum_(k>=0)e^(-(2k+1/2)t)/(k+1/4)^2.              (8)
```

Since `2k+1/2=2(k+1/4)`, its second derivative is

```text
sum_(k>=0)e^(-(2k+1/2)t)=e^(-t/2)/(1-e^(-2t)).          (9)
```

Negating the sum of these contributions and simplifying proves `(6)`. Multiplication of `(6)` by
the positive quantity `e^(5t/2)(1-e^(-2t))` gives `(7)`.

## Sign-indefinite cross-coupling theorem

`[PROVED]` If

```text
a>t_*/2,                                                   (10)
```

there exist nonzero real nonnegative functions `f,h in C_c^infinity(-a,a)` with disjoint supports
such that

```text
QW^a(f,h)>0.                                               (11)
```

### Proof

Choose

```text
t in (t_*,2a) \ {log n:n>=2}.                              (12)
```

This is possible because the excluded set is discrete. By continuity of the regular kernel away
from its atoms and `(7)`, there is an open interval `J` containing `t` on which `K>0` and which
contains no `log n`. Choose sufficiently small disjoint intervals `I_-` and `I_+` centered at
`-t/2` and `t/2`, contained in `(-a,a)`, such that

```text
I_+-I_- subset J.                                         (13)
```

Take nonzero nonnegative smooth bumps `f,h` supported in `I_-`, `I_+`. The diagonal principal-value
singularity never meets the product support, and the prime-power delta atoms are excluded by `(13)`.
Thus `(1)` is an ordinary integral there, and

```text
QW^a(f,h)
 =integral_(I_+) integral_(I_-) K(x-y)f(y)h(x)dy dx>0.  (14)
```

This proves `(11)`.

For a lower-semibounded real symmetric form, positivity preservation of the associated semigroup
implies the first Beurling--Deny inequality

```text
q(f,h)<=0                                                  (15)
```

for all nonnegative form-domain vectors with disjoint support. Adding a scalar multiple of the
`L2` norm does not change the cross pairing of disjoint vectors. Equations `(11)`--`(15)` therefore
show that no scalar shift of the exact restricted Weil operator has a positivity-preserving, hence
no positivity-improving, semigroup for any aperture satisfying `(10)`.

## Positive requirement for large-aperture simple-evenness

Suzuki proves small-aperture simple-evenness by first obtaining an irreducible Dirichlet limiting
form with positivity-improving semigroup and then using perturbation theory. The theorem above shows
that the exact cofinal Weil form enters a genuinely sign-indefinite class. The positive cofinal
target is therefore

```text
parity-reduced restricted Weil operators
  + quantitative separation/no-crossing across growing aperture
  + source-selected overlap with the even prolate seed
  -> simple even ground state.                                    (16)
```

The explicit positive cross-couplings identify what such a theorem must control: sign changes and
parity sectors, rather than an order cone. The divided-difference commutator, an oscillation theorem,
a source-specific transversality law, or the projective comparison with `k_lambda` are all
structurally compatible mechanisms.

## Pipeline position

The theorem is complementary to
`positive-density-transverse-divisor-relocation-law.md`: the full characteristic function supplies
the required transverse localization, while the present theorem specifies the sign-indefinite
spectral mechanism needed to produce its simple-even ground vector. The CCM target remains exactly
the one in
`ccm-growing-aperture-mellin-determinant-transfer.md`.

## Novelty verdict

The calculation is a direct differentiation of Suzuki's explicit kernel followed by the standard
Beurling--Deny criterion. It gives a useful exact classification of the cofinal spectral geometry,
but it is routine parent theory after the kernel is written and is therefore classified as a bridge.

## Lean decision

The formal tree has no object for Suzuki's screw function, its distributional second derivative, or
the restricted Weil form. Formalizing only the abstract disjoint-support criterion would not certify
the source-specific sign computation. No Lean file is added.

## Gates

- [x] exact regular off-diagonal screw kernel computed
- [x] explicit positivity threshold identified
- [x] disjoint positive bump violation proved
- [x] stability under scalar shifts addressed
- [x] cofinal sign-indefinite spectral class identified
- [ ] parity-separated/oscillatory cofinal simple-even theorem
- [ ] projective CCM ground-vector transfer
- [ ] RH
