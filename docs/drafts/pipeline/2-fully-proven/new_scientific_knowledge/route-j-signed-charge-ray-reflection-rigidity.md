# Route J signed charge-ray reflection rigidity

- **ID:** `route-j-signed-charge-ray-reflection-rigidity`
- **Stage:** 2 — fully proven on paper
- **Type:** THEOREM / CROSS-FIBRE SUPERSELECTION
- **Scientific status:** `[CORPUS-NEW SOURCE-SPECIFIC RIGIDITY]`
- **Lean:** `formal/GaloisForLFunctions/RHTower/XiCTaylorSignedAtomicJetControllability.lean`
- **Parent:** `route-j-signed-quarter-turn-jet-controllability.md`

## Result

The four quarter-turn atoms are needed to interpolate an arbitrary complex value--derivative jet,
but an exact scalar horizontal charge has a unique two-atom form. More importantly, its
mesh-normalized weights remember the fibre geometry. If one reflection-invariant source law has
the same nonzero projective leading direction at a fibre `sigma` and its functional-equation
mate `1-conj(sigma)`, exact screening forces

```text
Re sigma = 1/2.
```

This is the first cross-fibre theorem after pointwise signed jet universality. It does not assume
that `sigma` is an Xi zero. Applied to a nonzero divisor charge, it says:

```text
reflection-equivariant coherent signed screen
  -> critical-line fibre;

off-line screen
  -> mandatory reflection-symmetry breaking in its leading source weights.
```

The theorem does not construct the coherent source law. It classifies a large surviving signed
class and exposes the exact datum that any off-line survivor must violate.

## Unique two-atom scalar channel

At `z=u+iy`, put

```text
T=pi/(2u),  r=exp(-Ty)>0.
```

For a scalar jet

```text
G=1,  H=iq,  q real,
```

the odd quarter-turn equations are

```text
-r a_1+r^3 a_3=0,
 Tr a_1-3Tr^3 a_3=0.
```

Since `T` and `r` are nonzero, their determinant is `2Tr^4`, so

```text
a_1=a_3=0.
```

The even equations are

```text
(1+r^2)a_2+(1-r^4)a_4=1,
2Tr^2 a_2-4Tr^4 a_4=q.
```

Their determinant is `-2Tr^2(1+r^2)^2`, hence the unique solution is

```text
a_4 = [1-(1+r^2)q/(2Tr^2)]/(1+r^2)^2,                 (JR1)
a_2 = q/(2Tr^2)+2r^2 a_4.                             (JR2)
```

Thus two even atoms at `2T` and `4T` do not merely provide one representative: every four-atom
quarter-turn realization of `(1,iq)` collapses to this same pair.

For horizontal mesh width `delta>0`, connection correction `c=Im(1/z)`, and charge `m`, take

```text
q=m/delta+c.
```

Then the two atoms satisfy the exact source connections and

```text
delta Im(D/F)=m.
```

Multiplicity enters one affine scalar amplitude. Source arity and finite-dimensional
controllability are therefore not the remaining obstruction.

## Exact projective fingerprint

The value equation factors:

```text
(1+r^2)[a_2+(1-r^2)a_4]=1.
```

Consequently

```text
a_2+(1-r^2)a_4=1/(1+r^2),                             (JR3)
delta a_2+(1-r^2)delta a_4=delta/(1+r^2).              (JR4)
```

Let

```text
delta_n -> 0,
r_n -> r_0>0,
delta_n a_(2,n) -> b_2,
delta_n a_(4,n) -> b_4.
```

Passing to the limit in `(JR4)` gives the charge ray

```text
b_2+(1-r_0^2)b_4=0.                                   (JR5)
```

More generally, let `(b_2,b_4)` and `(c_2,c_4)` be nonzero limiting representatives at two
positive radii `r_0,s_0`. If they have the same projective direction,

```text
b_2 c_4=c_2 b_4,
```

then substituting their two copies of `(JR5)` gives

```text
(s_0^2-r_0^2)b_4c_4=0,
```

so `r_0=s_0`. The normalized leading weight direction therefore determines the damping radius.
The representatives need not be equal. This absorbs different positive mesh normalizations at
the two fibres.

The nonzero condition is forced by a genuine charge. Formula `(JR1)` gives the exact identity

```text
delta a_4
 = delta/(1+r^2)^2
   -(m+delta c)/(2Tr^2(1+r^2)).                        (JR6)
```

If `T_n->T_0!=0`, `r_n->r_0!=0`, and `c_n` has a finite limit, then

```text
delta_n a_(4,n)
 -> -m/[2T_0 r_0^2(1+r_0^2)].                         (JR7)
```

This limit is nonzero for `m!=0`. Thus charge screening supplies the nontrivial projective
coordinate needed by cross-fibre rigidity; it is not an auxiliary nondegeneracy assumption.

## Xi fibre geometry

For the anisotropic centered Xi mesh,

```text
z_n -> i(1/2-sigma),
Re z_n -> Im sigma,
Im z_n -> 1/2-Re sigma.
```

The quarter-turn radius converges to

```text
r(sigma)
 = exp[-pi(1/2-Re sigma)/(2 Im sigma)].                (JR8)
```

For positive ordinates, injectivity of the real exponential gives

```text
r(sigma)=r(tau)
  iff
(1/2-Re sigma)/Im sigma
 =
(1/2-Re tau)/Im tau.                                   (JR9)
```

Take the functional-equation mate

```text
tau=1-conj(sigma).
```

It has the same positive ordinate and the opposite centered vertical coordinate, so

```text
r(tau)=r(sigma)^(-1).
```

If one coherent reflection-invariant source profile has the same projective normalized direction
at both fibres, `(JR5)` and the two nonzero fourth coordinates force
`r(sigma)=r(tau)`. Equation `(JR9)` then gives

```text
(1/2-Re sigma)/Im sigma
 =
-(1/2-Re sigma)/Im sigma,
```

and hence `Re sigma=1/2`.

## What this closes

The theorem closes the reflection-equivariant, asymptotically coherent two-even-atom charge
channel. By scalar-jet uniqueness, it also closes every reflection-equivariant four-quarter-turn
packet whose value and derivative are exactly `(1,iq_n)`.

It does **not** close:

1. coherent signed laws with a different support geometry;
2. laws whose leading normalized weights transform nontrivially under
   `sigma -> 1-conj(sigma)`;
3. singular boundary distributions not represented by finite atomic weights;
4. relation-valued channels without a scalar logarithmic derivative.

These remain Route J work. In particular, calling symmetry breaking “another route” would be
incorrect: it is the newly isolated Route-J survivor.

## Novelty and collision audit

The two-by-two inversion and exponential injectivity are elementary separately. Prony and Hermite
interpolation by exponential sums are classical; Chunaev, *Interpolation by generalized
exponential sums with equal weights* (arXiv:1906.01332), is representative. Targeted primary-source
searches found no statement combining:

1. one-sided completion atoms `1-exp(itz)`;
2. exact Xi horizontal logarithmic charge;
3. the mesh-normalized projective ray `(JR5)`;
4. the explicit Xi fibre radius `(JR8)`; and
5. functional-equation reflection forcing the critical line from a common projective source
   direction.

No external priority claim is made. Corpus novelty is the dependency-closed conjunction and its
use as a Route-J cross-fibre superselection theorem.

## Lean audit

The formal module proves unconditionally:

- unique collapse of every scalar four-atom jet to the two even weights;
- exact two-atom horizontal-charge realization;
- exact affine and scaled projective fingerprints;
- the projective fingerprint limit theorem;
- common-projective-direction radius rigidity, allowing different normalizations;
- explicit Xi fibre-radius convergence and slope classification;
- reflection-invariant profile rigidity forcing `Re sigma=1/2`;
- exact scaled fourth-weight formula, its limit, and nonvanishing for `m!=0`.

Direct command:

```text
cd formal
lake env lean GaloisForLFunctions/RHTower/XiCTaylorSignedAtomicJetControllability.lean
```

passes with no warnings. No `sorry`, `admit`, `axiom`, `opaque`, or `unsafe` declaration occurs.

## Route consequence

`J-SF6` is no longer merely “coherent signed source required.” Its next survivor is:

```text
construct or exclude a divisor-independent coherent signed source whose leading normalized
profile either is not quarter-turn finite-atomic or breaks functional-equation reflection
equivariance; any reflection-equivariant quarter-turn scalar screen already selects the
critical line.
```
