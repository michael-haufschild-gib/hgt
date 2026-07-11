# The depth-three direct carrier has a cofinal recurrent strip divisor

- **ID:** `depth-three-dirichlet-factor-cofinal-strip-zero-recurrence`
- **Stage:** 3-formalized
- **Type:** THEOREM (paper + Lean) / PRIME-PHASE RECURRENCE LAW
- **Scientific status:** `[PROVED HERE] [BRIDGE; NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Statement:** The Dirichlet factor

  ```text
  D_3(s)=1+2^(-s)+3^(-s)
  ```

  has zeros in `0<Re(s)<1` with arbitrarily large positive imaginary part.  Consequently the
  depth-one/two global horizontal log-modulus monotonicity mechanism cannot extend even to depth
  three.

## An exact balanced torus zero

The continuous strictly positive function

```text
q(sigma)=2^(-sigma)+3^(-sigma)
```

has

```text
q(0)=2>1,
q(1)=5/6<1.
```

The intermediate value theorem therefore gives `sigma_0 in (0,1)` with

```text
2^(-sigma_0)+3^(-sigma_0)=1.                               (1)
```

Define the exponential polynomial

```text
G(w)=1-2^(-sigma_0)2^(-w)-3^(-sigma_0)3^(-w).              (2)
```

Then `G(0)=0`, and this zero is simple because

```text
G'(0)=2^(-sigma_0)log 2+3^(-sigma_0)log 3>0.               (3)
```

This replaces the arbitrary triangle phases by the common exact phase `-1` and makes the limiting
zero and its transversality entirely explicit.

## Kronecker--Hurwitz transfer

Put `alpha=log 3/log 2`.  Its irrationality follows from unique factorization.  The natural orbit
of `alpha` on `R/Z` is dense.  Choose a strictly increasing sequence `k_j` such that

```text
k_j alpha -> (1-alpha)/2 mod Z,
t_j=(pi+2pi k_j)/log 2.                                    (4)
```

Then `t_j->+infinity`, while

```text
exp(-i t_j log 2)=-1,
exp(-i t_j log 3)->-1.                                     (5)
```

For

```text
G_j(w)=D_3(sigma_0+w+i t_j),                               (6)
```

equation `(5)` gives

```text
G_j->G locally uniformly on C.                             (7)
```

Choose a closed disc about `0` whose translate by `sigma_0` lies in `0<Re(s)<1`, on which `0` is the only zero
of `G` and whose boundary is zero-free.  The simple-zero form of Hurwitz's theorem, or Rouché's
theorem applied to `(7)`, gives a zero `w_j` of `G_j` in that disc for every sufficiently large
`j`.  Then

```text
s_j=sigma_0+w_j+i t_j
```

satisfies

```text
D_3(s_j)=0,
0<Re(s_j)<1,
Im(s_j)->+infinity.                                        (6)
```

This proves the theorem.

## Positive carrier law

`CarrierHorizontalRigidity.lean` and `CarrierDepthTwoRigidity.lean` work because the direct
Dirichlet factors at depths one and two are zero-free in `Re(s)>0` and have a uniform lower bound
on their horizontal logarithmic rate.  Equation `(6)` makes both properties false at depth three:
`log|D_3|` is singular at arbitrarily high strip points and cannot be globally strictly monotone
across the strip.

The theorem is positively read as follows:

```text
two independent prime phases + one interior amplitude balance
  -> recurrent cancellation
  -> a cofinal interior strip divisor.                    (7)
```

Thus scalar depth-three completion necessarily transports a recurrent cancellation channel; it is
not an accidental low-height defect.  A successful all-depth coercivity theorem must positively
control that channel by at least one of the following mechanisms:

1. control the direct factor only on the reflected equal-modulus locus arising from a zero of the
   completed sum;
2. use a source-selected region proved to avoid the recurrent direct-factor divisor;
3. retain a second analytic or prime-coordinate direction whose positivity prevents scalar phase
   neutralization.

The third alternative is compatible with the periodic-pencil dimension theorem and with the
formal one-prime reflected-modulus-neutrality theorem.  The resource requirement is therefore:

```text
RH-capable all-depth coercivity
  -> recurrence-sensitive localization or a genuine second source direction.  (8)
```

No claim is made here that either resource has already been constructed.

## Lean formalization

`formal/GaloisForLFunctions/RHTower/DepthThreeDirichletHighZeros.lean` proves the complete theorem
without project axioms or placeholders.  It uses Mathlib's dense irrational rotations on `AddCircle 1`, extracts a strictly
increasing convergent subsequence, transports it through the circle exponential, proves the local
uniform convergence of the translated entire factors, and invokes
`eventually_exists_zero_closedBall_of_tendstoLocallyUniformly`.

The capstone declaration is

```text
RHTower.exists_depthThreeDirichletFactor_zero_high
  (B : R) : exists s : C,
    0 < s.re and s.re < 1 and B <= s.im and depthThreeDirichletFactor s = 0.
```

## Gates

- [x] exact balanced torus zero at a source-defined `sigma_0 in (0,1)`
- [x] simple limiting zero proved
- [x] Kronecker phase approximation identified
- [x] Hurwitz transfer to arbitrarily high zeros
- [x] global all-depth horizontal monotonicity refuted at depth three
- [x] formalized the irrational-rotation subsequence and high-zero theorem in Lean
- [ ] isolate a localized or two-direction coercivity replacement
