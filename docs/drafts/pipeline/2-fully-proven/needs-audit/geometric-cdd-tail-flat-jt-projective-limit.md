# The deep geometric CDD tail has a flat-JT projective limit

- **ID:** `geometric-cdd-tail-flat-jt-projective-limit`
- **Stage:** 2-fully-proven / needs-audit
- **Type:** CANDIDATE THEOREM / QFT-TO-TOPOLOGICAL-GRAVITY BRIDGE / ASYMPTOTIC SOURCE LAW
- **Scientific status:** `[PROVED HERE] [NOVELTY UNVERIFIED] [SIGNIFICANCE GATE OPEN]`
- **Scope:** general hypertranscendental elastic QFT; no RH or distinguished special-function
  input
- **Parent:** `hausdorff-positive-higher-spin-cdd-cone.md`
- **Statement:** After deleting the first `N` geometric CDD shells and normalizing the remaining
  coupling measure by its total mass, the tail converges to the zero-shell extreme ray.  Its
  higher-spin vector therefore converges to the pure `T bar T` direction and its phase germ
  converges locally uniformly to the flat-JT gravitational dressing.

## Goal

Find an exact, non-metaphorical connection between the geometric HT scattering law and a known
topological-gravity source.  The connection must not claim that ordinary `T bar T` already equals
the HT product: an entire one-spin dressing is differentially algebraic and has no CDD divisor.

The correct statement is projective and asymptotic.  The full q-ladder remains HT, but its deep
large-scale shell tail approaches the `T bar T` ray after the unique normalization supplied by
the positive coupling measure.

## Geometric shell measure

Fix `0<q<1` and `C>1`, and put

```text
B_j=C q^(-j)=cosh(eta_j),
r_j=exp(-eta_j)=B_j-sqrt(B_j^2-1),       0<r_j<1.           (1)
```

The sequence `B_j` is strictly increasing and unbounded, so `r_j` is strictly decreasing to
zero.  The paired-shell phase is

```text
Sigma_j(theta)=4 arctan(sinh(theta)/B_j).                   (2)
```

Its Hausdorff source atom is

```text
nu_j=r_j delta_(r_j^2).                                    (3)
```

The full coupling measure and its tail are

```text
nu=sum_(j>=0) nu_j,
nu_>=N=sum_(j>=N) nu_j,
M_N=nu_>=N([0,1])=sum_(j>=N) r_j.                          (4)
```

The elementary estimate

```text
r_j=1/(B_j+sqrt(B_j^2-1)) <= 1/B_j=q^j/C                  (5)
```

proves that every `M_N` is finite and positive and that `M_N` tends to zero.

## Theorem A -- normalized tail measures collapse to the zero-shell ray `[PROVED]`

Define the probability measure

```text
hat(nu)_N=M_N^(-1) nu_>=N.                                 (6)
```

Its support lies in `[0,r_N^2]`.  Since `r_N` tends to zero, for every continuous function `f`
on `[0,1]`,

```text
|integral f d hat(nu)_N - f(0)|
  <= sup_(0<=y<=r_N^2) |f(y)-f(0)| -> 0.                  (7)
```

Therefore

```text
hat(nu)_N -> delta_0                                      (8)
```

in the weak-star topology of finite measures.

This is not a statistical or numerical limit.  It is forced only by positivity and the nested
support intervals.

## Theorem B -- all normalized higher-spin directions except spin one vanish `[PROVED]`

Let

```text
b_m^(N)=integral y^m d hat(nu)_N(y).                        (9)
```

Then

```text
b_0^(N)=1,
0 <= b_m^(N) <= r_N^(2m) -> 0       for every m>=1.        (10)
```

The normalized odd-spin couplings are

```text
hat(alpha)_(2m+1)^(N)
  = 8 (-1)^m b_m^(N)/(2m+1).                               (11)
```

Consequently

```text
hat(alpha)_1^(N)=8,
hat(alpha)_(2m+1)^(N) -> 0          for every m>=1.        (12)
```

Thus the projective direction of the entire deep tail converges coefficientwise to the unique
spin-one current--current deformation.

## Theorem C -- the normalized phase converges to T bar T / flat JT `[PROVED]`

Let the Hausdorff phase kernel be

```text
K(y,theta)
  = 4/sqrt(y) [arctan(sqrt(y)e^theta)
               - arctan(sqrt(y)e^(-theta))],
K(0,theta)=8 sinh(theta).                                  (13)
```

Define the tail phase and its projective normalization by

```text
Sigma_>=N(theta)=integral K(y,theta) d nu_>=N(y)
               =sum_(j>=N) Sigma_j(theta),

hat(Sigma)_N(theta)=M_N^(-1) Sigma_>=N(theta)
                   =integral K(y,theta) d hat(nu)_N(y).    (14)
```

On every compact rapidity set contained in a fixed neighborhood of the origin, `K(y,theta)` is
jointly continuous down to `y=0` and analytic in `theta`.  Since the support of `hat(nu)_N`
shrinks uniformly to zero, `(7)` applied uniformly in `theta` gives

```text
hat(Sigma)_N(theta) -> 8 sinh(theta)                       (15)
```

locally uniformly.  Hence

```text
exp(i hat(Sigma)_N(theta)) -> exp(i 8 sinh(theta)).         (16)
```

Up to the conventional sign and mass normalization of the coupling, the right side of `(16)` is
the universal `T bar T` CDD phase obtained by coupling the matter theory to flat JT gravity.

The unnormalized statement is different:

```text
Sigma_>=N(theta) -> 0,
exp(i Sigma_>=N(theta)) -> 1.                              (17)
```

Thus the tail becomes weak in absolute size while its **projective shape** converges to the
topological-gravity direction.

## Exact relation to the q-boundary product

The tail interaction factor is also

```text
P_>=N(t)
  = product_(j>=N) ((1-q^j t)/(1+q^j t))^2
  = P_q(q^N t).                                            (18)
```

Equation `(18)` is the exact decimation orbit of the affine q-boundary constraint.  Equations
`(8)`--`(16)` identify its tangent direction at the trivial endpoint: after normalization by the
positive first coupling, the orbit approaches flat-JT dressing.

This does **not** identify `q^N` with a physical RG time.  It is a theorem about nested divisor
tails and their coupling-measure geometry.

## Physical interpretation

The geometric HT completion has three simultaneous layers:

```text
each finite shell:             rational/DA paired CDD factor,
projectively normalized tail:  T bar T / flat-JT direction,
full one-sided completion:     hypertranscendental.         (19)
```

Hypertranscendence is therefore not present in the elementary shell or in the projective tail
fixed ray.  It lives in the global boundary completion that assembles all finite scales while
retaining the infrared endpoint.

The theorem gives a precise QFT interpretation of the founding constraint principle.  Ordinary
topological gravitational dressing is the asymptotic tangent of the shell constraint, while the
HT object records the nontrivial global integration of that constraint across all scales.

## What is not proved

1. No flat-JT action for the full geometric measure has been constructed.
2. The normalized phase in `(16)` is a projective local germ.  Since the normalization changes
   atomic multiplicities continuously, it need not be a globally meromorphic CDD product for
   finite `N`.
3. No Wilsonian RG flow, ultraviolet fixed point, or continuum scaling limit is asserted.
4. The result does not prove that all positive Hausdorff CDD measures have a JT-type microscopic
   realization.
5. The result does not make the full HT phase differentially algebraic; the limit and the global
   completion have different differential-algebraic types.

## Anti-theatre and novelty gate

Parent results:

- ordinary `T bar T` multiplies the S-matrix by an exponential `sinh(theta)` CDD phase;
- that phase has a flat-JT topological-gravity construction;
- limits of repeated elementary CDD factors can yield the ordinary `T bar T` exponential;
- Hausdorff moment measures and weak convergence on a compact interval are classical.

The new candidate is not the statement that CDD factors approximate an exponential.  It is the
canonical, source-positive tail theorem `(6)`--`(16)` for the geometric HT divisor: normalization
by its own total coupling mass forces weak convergence to the zero-shell measure, annihilates
every higher-spin direction, and selects the flat-JT ray.

Focused searches in the generalized `T bar T`, CDD, and topological-gravity literature found the
known repeated-identical-factor limit but not this geometric-tail/Hausdorff-measure statement.
That is negative evidence, not a completed novelty proof.

The theorem is significant because it supplies an exact QFT--topological-gravity bridge without
collapsing the HT completion to ordinary `T bar T`.  It becomes Fields/Nobel-scale only if a
positive functor integrates the entire source measure and explains why the q-boundary law selects
this one-sided completion.

## Lean boundary

The proof is an analytic weak-measure and QFT-interface theorem.  Its finite coefficient bounds
are elementary, while the substantive content is the identification with the topological
gravitational dressing and the global/local separation.  The current HTGeometry corpus already
contains the finite shell constraint and endpoint-selection algebra.  Formalizing only `(10)`
would be mechanical and would not close the action-level source interface.

No Lean edit, build, scratch compilation, lint, axiom check, or numerical computation was run.

## Primary literature

- F. A. Smirnov and A. B. Zamolodchikov, *On space of integrable quantum field theories*,
  <https://arxiv.org/abs/1608.05499>.
- S. Dubovsky, V. Gorbenko, and G. Hernandez-Chifflet, *T bar T Partition Function from
  Topological Gravity*, <https://arxiv.org/abs/1805.07386>.
- G. Hernandez-Chifflet, S. Negro, and A. Sfondrini, *Flow equations for generalised T bar T
  deformations*, <https://arxiv.org/abs/1911.12233>.
- F. Hausdorff, *Summationsmethoden und Momentfolgen I*,
  <https://doi.org/10.1007/BF01378337>.

## Gates

- [x] tail measure finite and positive
- [x] normalized tail weak-star convergence proved
- [x] coefficientwise collapse to the spin-one direction proved
- [x] locally uniform phase-kernel convergence proved
- [x] flat-JT / ordinary T bar T endpoint identified at source level
- [x] projective limit separated from literal global meromorphic products and Wilsonian RG
- [ ] formula-level specialist novelty audit
- [ ] positive action or operator-flow integration of the full geometric measure
- [ ] universality theorem for the zero-shell projective attractor beyond the geometric family
