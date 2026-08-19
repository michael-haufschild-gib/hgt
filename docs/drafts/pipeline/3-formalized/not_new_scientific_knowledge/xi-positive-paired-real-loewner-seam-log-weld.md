# Xi positive-paired real boundary is the seam-log Loewner kernel

- **ID:** `xi-positive-paired-real-loewner-seam-log-weld`
- **Stage:** 3-formalized/not_new_scientific_knowledge
- **Type:** THEOREM (paper), `[TOP-DOWN INTERFACE DISCHARGE]`, `[VALUE RELATION]`
- **Scientific status:** `[PROVED] [FORMALIZED] [BRIDGE] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Formal parents:**
  `RHTower/XiHurwitzOrientationPositivePairedSource.lean`,
  `RHTower/CriticalTraceMomentGerm.lean`,
  `RHTower/PrimeArchCentralMomentGerm.lean`
- **Paper parents:**
  `seam-log-derivative-weld-identity.md`,
  `seam-log-markov-pick-rh-equivalence.md`,
  `xi-positive-paired-diagonal-sector-collapse.md`

## Statement

Put

```text
T(z) = continuedPrimeArchSourceRelativeTrace(z)
h(z) = normalizedTraceMomentGerm(T)(z).
```

The formal corpus proves `T(0)=0`, and therefore

```text
h(z)=-T(z)/z                                                   (1)
```

away from `z=0`.  Near the functional-equation centre, `T` is odd and Schwarz-real, so `h` is
even and Schwarz-real.  Hence there is a unique real holomorphic germ `G` with

```text
h(z)=G(z^2).                                                    (2)
```

The seam-log derivative weld identifies this descended germ exactly as

```text
G=G_src,
G_src(u)=2 L'(-u),
L(v)=log(Xi(sqrt(v))/Xi(0)).                                   (3)
```

Let `x,y>0` be distinct real points in a zero-free central source interval.  Then the one-sided
positive-paired source kernel satisfies

```text
ccmPositivePairedReducedKernel(x,y)
  =4*x*y*(G_src(x^2)-G_src(y^2))/(x^2-y^2).                    (4)
```

Its canonical confluent boundary value is

```text
Khat+(x,x)
  =2*(-T'(x)+T(x)/x)
  =4*x^2*G_src'(x^2).                                         (5)
```

Consequently, for any distinct positive nodes `x_1,...,x_n` in that interval,

```text
(Khat+(x_i,x_j))_(i,j)
  =D * L_G(x_1^2,...,x_n^2) * D,
D=diag(2*x_1,...,2*x_n),                                     (6)
```

where `L_G` is the confluent Loewner matrix of `G_src`.  Since `D` is invertible and positive,
the two matrices have the same positivity, inertia, rank, and nullity.

In particular, the following are equivalent:

1. RH.
2. For every finite set of distinct positive nodes in one zero-free central interval, the matrix
   in `(6)` is positive semidefinite.
3. The same condition holds on the countable family of positive rational nodes in that interval.
4. The local seam-log germ `G_src` is matrix monotone of every order there, equivalently it has a
   Pick continuation to the upper half-plane.

The value relation `(4)--(6)`, not the terminal RH equivalence, is the interface discharge proved
here.

## Proof of the source value identity

For real regular `x`, Schwarz reflection of the continued source gives

```text
T(x)=conj(T(x)),
```

so `T(x)` is real.  For distinct positive real `x,y`, the definition of the reduced paired kernel
therefore becomes

```text
K+(x,y)/2
  =(T(y)-T(x))/(x-y)+(T(y)+T(x))/(x+y).
```

Putting the two fractions over the common denominator gives

```text
K+(x,y)
  =4*(x*T(y)-y*T(x))/(x^2-y^2).                               (7)
```

By `(1)--(3)`,

```text
G_src(x^2)=-T(x)/x,
G_src(y^2)=-T(y)/y.
```

Thus

```text
x*T(y)-y*T(x)
  =x*y*(G_src(x^2)-G_src(y^2)),
```

and `(7)` is exactly `(4)`.

Letting `y` tend to `x`, or differentiating `-T(x)/x=G_src(x^2)`, gives

```text
4*x^2*G_src'(x^2)
  =2*(-T'(x)+T(x)/x),
```

which is `(5)`.  Applying `(4)` off the diagonal and `(5)` on the diagonal entrywise proves the
matrix factorization `(6)`.

## Essential confluent-diagonal warning

The existing Lean definition `ccmPositivePairedReducedKernel x x` must **not** be used for `(5)`
when `x` is real.  Its first quotient is syntactically `0/0`, and Lean's totalized field division
sets that term to zero.  The Hilbert/source identity in
`XiHurwitzOrientationPositivePairedSource.lean` accordingly assumes nonzero imaginary part on a
diagonal node.

`Khat+` is the analytic boundary regularization: it is the limit obtained either from distinct
real nodes or from nonreal diagonal nodes tending vertically to the real axis.  Any formalization
must introduce this confluent value explicitly rather than simplify the existing totalized
definition at a real diagonal.

## Proof of the local Loewner criterion

Choose `r>0` so small that `XiC` is nonzero on `|z|<r`; this exists because `XiC(0)!=0`.  Then
`G_src` is real analytic on the interval `J=(0,r^2)`.

If RH holds, the seam-log Markov theorem gives

```text
G_src(u)=integral 1/(1-u*t) dnu(t),
```

with `nu` a finite positive measure on `R_+`.  On a sufficiently small `J`, its divided-difference
kernel is

```text
(G_src(u)-G_src(v))/(u-v)
  =integral t/((1-u*t)*(1-v*t)) dnu(t),                       (8)
```

with the derivative value on the diagonal.  Every finite Loewner matrix is therefore a Gram
matrix.  Equation `(6)` proves condition 2.

Conversely, condition 2 and the positive diagonal congruence in `(6)` make every finite Loewner
matrix of `G_src` positive semidefinite on `J`.  Loewner's theorem says precisely that `G_src` is
operator monotone on `J` and hence extends from `J` to a Pick function on the upper half-plane.

Suppose RH fails.  Write a noncritical Xi zero in seam coordinates as `w`, so both `Re w` and
`Im w` are nonzero; a real seam zero is excluded unconditionally by the real-strip zero-free
theorem.  The weld

```text
G_src(-w^2)=Xi'(w)/(w*Xi(w))                                 (9)
```

shows that the meromorphic continuation of `G_src` has a pole at `-w^2`.  Reflection of the zero
quartet chooses such a pole in the open upper half-plane.  The Pick continuation obtained from
Loewner's theorem is holomorphic there.  It agrees with the canonical germ on `J`, hence with its
meromorphic continuation by analytic uniqueness, contradicting that pole.  Therefore every Xi
zero is critical and RH holds.

Condition 3 is equivalent to condition 2 because rational nodes are dense, the confluent kernel is
continuous on `J x J`, and the positive-semidefinite cone is closed.  If desired, each finite
matrix test can itself be restricted to rational coefficient vectors, making the whole criterion
countable.

## What this closes

The corpus had three apparently separate source surfaces:

```text
positive-paired continued-Cauchy values,
normalized prime--Gamma trace moments,
seam-log Markov/Loewner positivity.
```

They are now one object on the real boundary:

```text
paired Cauchy boundary kernel
  = positive diagonal congruence
      of the Loewner kernel of the square-descended normalized trace germ.
```

Thus a theorem proving finite boundary passivity from prime--Gamma values may feed the seam-log
criterion directly; it does not need a separate moment-identification or a second Cauchy-closure
argument.  Conversely, the real-boundary restriction of the positive-paired source route cannot
provide an independent orientation mechanism beyond the seam-log Loewner wall.

This is the positive form of the no-double-counting conclusion:

> the real-pole positive-paired source core **is** the Markov--Loewner core.

The genuinely different information in the positive-paired route lies off the real boundary, for
example in the exterior scalar sector criterion.  The genuinely open source theorem on the real
boundary is to prove the finite confluent matrices `(6)` positive from the explicit continued
prime--Gamma formula without importing Xi divisor orientation, anti-Herglotzness, real-rootedness,
or an RH-equivalent positive measure.

## Formalization target

1. Prove that `continuedPrimeArchSourceRelativeTrace x` is real for real `x` in
   `CCMContinuedCauchyDomain` using the existing conjugation theorem.
2. Prove `(4)` for nonzero distinct real `x,y` by unfolding
   `ccmPositivePairedReducedKernel` and `normalizedTraceMomentGerm`.
3. Define a confluent real-boundary kernel with diagonal `(5)`; do not reuse the totalized
   `ccmPositivePairedReducedKernel x x` value.
4. Prove the finite diagonal-congruence theorem `(6)`.
5. Connect the square-descended normalized source germ to the existing
   `xiCentralMomentGerm` germ equality.  A full formal Loewner/Pick equivalence can remain a later
   analytic-library task.

No Lean theorem is claimed by this card.

## Literature calibration

The matrix-theoretic step is classical.  Loewner matrices use divided differences off the
diagonal and derivatives on the diagonal; positivity in every finite order characterizes operator
monotonicity and Pick continuation.  Audenaert's anti-Loewner analysis also makes the same positive
square-coordinate transformation systematic.  The contribution here is the exact identification
of that classical kernel inside the two independently developed Xi source interfaces, not a new
Loewner theorem.

## Gates

- [x] exact off-diagonal source identity `(4)` proved
- [x] exact confluent diagonal `(5)` proved
- [x] finite matrix congruence `(6)` proved
- [x] local all-order Loewner positivity shown equivalent to RH
- [x] countable rational-node reduction proved
- [ ] formalize the elementary source identities and confluent kernel
- [ ] prove the boundary matrix positivity from explicit prime--Gamma source data
- [ ] prove RH

## Log

- 2026-07-15 -- Codex: found by top-down collision of the positive-paired Hurwitz source kernel
  with the already formalized normalized trace germ and the paper-proven seam-log weld.  Recorded
  the confluent-diagonal correction and the exact finite matrix congruence.  No computation or
  Lean build was used.

## Lean formalization (complete and unconditional, targets 1--5)

`formal/GaloisForLFunctions/RHTower/XiPositivePairedRealLoewnerSeam.lean` — the boundary trace and
its seam germ, the Loewner datum, the confluent paired kernel `(5)`, its identification with the
reduced CCM paired kernel `(4)`, the finite matrix congruence `(6)`, and the equivalence of local
all-order Loewner positivity with the critical line.
