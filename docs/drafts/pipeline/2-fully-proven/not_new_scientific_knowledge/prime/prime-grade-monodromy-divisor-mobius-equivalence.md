# Prime-grade monodromy is exactly divisor Möbius data

- **ID:** `prime-grade-monodromy-divisor-mobius-equivalence`
- **Stage:** 2-fully-proven / not-new
- **Type:** theorem (paper), `[BRIDGE]`
- **Statement:** The complete residue/monodromy field of the grade-one prime logarithmic source is
  the Möbius transform of the zeta divisor along positive-integer dilations.  The inverse Lambert
  transform recovers exactly the original divisor.  Thus all prime-grade monodromies contain the
  divisor faithfully but contain no additional source--divisor incidence datum.

## Setup

On `Re s>1`, put

```text
A(s) = -zeta'(s)/zeta(s),
Q(s) = sum_p (log p) p^(-s).
```

The prime-power grading gives the Lambert decomposition

```text
A(s) = sum_(k>=1) Q(ks).                              (1)
```

Ordinary Möbius inversion gives

```text
Q(s) = sum_(r>=1) mu(r) A(rs).                        (2)
```

Equivalently, differentiating

```text
P(s)=sum_p p^(-s)=sum_(r>=1) mu(r)/r log zeta(rs)
```

gives `Q=-P'` and (2).  These identities begin in their absolute-convergence half-plane and then
hold wherever the corresponding meromorphic continuations are defined.

Let

```text
nu(z)=ord_z(zeta),
```

positive at a zero and `-1` at the pole `z=1`.  Since `A` has residue `-nu(z)` at `z`, the residue
of the scaled term `A(rs)` at `s=s0` is `-nu(r s0)/r`.  Therefore the grade-one prime monodromy is

```text
M_Q(s0) := Res_(s=s0) Q(s)
         = -sum_(r>=1) mu(r)/r * nu(r s0).             (3)
```

For the zeta divisor and `Re s0>0`, the sum is finite: once `r Re s0>=1`, zeta has neither zeros nor
poles except for the possible point `r s0=1`.

In particular, if `rho` is a nonreal zeta zero with `Re rho>1/2` and multiplicity `m`, then every
`r>=2` puts `r rho` in `Re>1`, so

```text
M_Q(rho)=-m.                                           (4)
```

Thus the grade-one prime channel carries the complete zero residue at every hypothetical
right-half zero; the higher prime-power grades are holomorphic there.

## Exact inverse

The residue of `Q(ks)` at `s=s0` is `M_Q(k s0)/k`.  Hence (1) predicts

```text
-nu(s0) = sum_(k>=1) M_Q(k s0)/k.                      (5)
```

This is not an additional compatibility.  Substituting (3) and regrouping the finite sum gives

```text
sum_(k>=1) M_Q(k s0)/k
  = -sum_(k,r>=1) mu(r)/(kr) * nu(rk s0)
  = -sum_(n>=1) nu(n s0)/n * sum_(r|n) mu(r)
  = -nu(s0).
```

The divisor identity `sum_(r|n) mu(r)=0` for `n>1` cancels every scaled divisor point and leaves
only `n=1`.  Therefore the two maps

```text
nu  |->  M_Q,       M_Q(s0)=-sum_r mu(r)nu(r s0)/r,
M_Q |->  nu,        nu(s0)=-sum_k M_Q(k s0)/k,
```

are mutually inverse on the locally finite dilation-ray data relevant to zeta.

## Finite Euler units and the completed source

Changing finitely many Euler factors changes `Q` by a finite prime Dirichlet polynomial.  That
polynomial is entire, so every residue `M_Q(s0)` is unchanged.  The full prime-grade monodromy field
therefore descends through finite Euler-unit equivalence, as required of a tail invariant.

The archimedean completed-flux channel is holomorphic at every nontrivial strip zero.  Adding it
does not change (3)--(5).  FE and Schwarz transport `nu` to its ordinary symmetric divisor orbit;
the induced transport of `M_Q` is already determined by (3).  No independent self-duality law is
created.

## Positive classification

The all-grade prime monodromy tower is a faithful coordinate for the divisor, and precisely that:

```text
prime-grade residue field  <->  zeta divisor.
```

It does not retain the holomorphic coefficient-ray information that distinguishes the Euler source
from an arbitrary symmetric order-one realizer.  Conversely, any symmetric locally finite strip
divisor with the same zero-free far-right condition admits the same formal Möbius residue transform,
independently of whether it comes from prime coefficients.

Thus all-grade monodromy does not supply the missing incidence compatibility.  It is the divisor
side of the already-classified global compact-open quotient written in prime-grade coordinates.

## Scientific status and surviving open core

This is `[BRIDGE]`, not new scientific knowledge.  Equations (1)--(2) are classical prime-zeta /
Lambert Möbius inversion, and the residue calculation is a direct local consequence.  Its value is
to close a tempting candidate exactly rather than heuristically.

The surviving invariant must use the **holomorphic arithmetic tail and divisor jointly**.  It cannot
factor through:

1. the Euler coefficient field alone;
2. the compact-open regular completed-flux field;
3. the divisor alone; or
4. the complete monodromy field of every prime-power grade.

The next admissible object is therefore a non-residue pairing between the weighted coefficient-ray
class and the global divisor, invariant under finite Euler units but not reconstructed from either
projection separately.
