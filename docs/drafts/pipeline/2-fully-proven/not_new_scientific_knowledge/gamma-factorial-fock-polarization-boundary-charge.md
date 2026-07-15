# Gamma's opposite-variance jet clocks have a canonical factorial Fock polarization

- **ID:** `gamma-factorial-fock-polarization-boundary-charge`
- **Stage:** 2-fully-proven/not_new_scientific_knowledge
- **Type:** THEOREM (paper) / POSITIVE SOURCE METRIC / BOUNDARY CHARGE
- **Scientific status:** `[PROVED HERE] [NOT FORMALIZED]
  [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Parent:** `../../1-in-progress/gamma-opposite-variance-weyl-seam.md`
- **Statement:** The analytic derivative clock and algebraic coordinate-multiplication clock in
  Gamma's finite opposite-variance model are exact adjoints for a unique diagonal factorial
  metric.  Their canonical-commutation defect is a positive rank-one top-boundary charge.  This
  supplies a source-selected positive metric, but Taylor translation is still not contractive;
  the missing RH theorem is the all-prime incidence which transports this boundary polarization
  to the reflected Euler--Lorentz fibre.

## The two infinitesimal clocks

On the `N`-dimensional raw-jet space with coordinates `0,...,N-1`, define

```text
(D_N x)_j=x_(j+1)       for j<N-1,
(D_N x)_(N-1)=0,                                        (1)

(A_N x)_0=0,
(A_N x)_j=j x_(j-1)     for 1<=j<N.                     (2)
```

Then the finite Taylor translation and coordinate-multiplication prolongation are

```text
E_N=exp(D_N),
Z_N(z)=zI+A_N.                                           (3)
```

Indeed, nilpotence of `D_N` gives

```text
(E_N)_(i,j)=1_(i<=j)/(j-i)!,                             (4)
```

and `(2)` is the Leibniz term in the differentiated action of multiplication by `z`.

## Canonical factorial metric

Put

```text
<x,y>_(F,N)=sum_(j=0)^(N-1) x_j conjugate(y_j)/j!.       (5)
```

Then

```text
D_N^*=A_N,                                               (6)
E_N^*=exp(A_N),
Z_N(z)^*=conjugate(z)I+D_N.                              (7)
```

For `(6)`, reindex directly:

```text
<D_N x,y>_(F,N)
 =sum_(j=0)^(N-2) x_(j+1)conjugate(y_j)/j!
 =sum_(k=1)^(N-1) x_k conjugate(k y_(k-1))/k!
 =<x,A_N y>_(F,N).                                      (8)
```

Moreover `(5)` is, up to one positive scalar, the unique diagonal positive metric for which
`D_N^*=A_N`.  If its diagonal weights are `w_j`, adjointness forces

```text
w_(j-1)=j w_j,
```

and hence `w_j=w_0/j!`.

Thus the positive metric is selected by the two source realizations themselves; it is not fitted
from a spectral divisor.

## Positive top-boundary charge

Let `P_top` be the coordinate projection onto the highest jet.  A coordinate calculation gives

```text
[D_N,A_N]=D_N A_N-A_N D_N=I-N P_top.                    (9)
```

Indeed, the commutator acts as the identity on coordinates `0,...,N-2` and as multiplication by
`1-N` on the top coordinate.  Since `P_top` is an orthogonal projection for `(5)`,

```text
I-[D_N,A_N]=N P_top >=0.                                (10)
```

The failure of the finite clocks to realize the infinite Weyl relation is therefore not merely
rank one: after the source-canonical polarization it is an exactly positive boundary charge.

## Passivity no-go

The factorial metric does not make Gamma translation contractive.  For `N>=2`, let `e_1` be the
first-derivative coordinate vector.  Then

```text
E_N e_1=e_1+e_0,
||E_N e_1||_(F,N)^2=2>1=||e_1||_(F,N)^2.                (11)
```

Nor does `(6)` identify the two full sides of Gamma's constraint as adjoints:

```text
E_N^*=exp(A_N) != zI+A_N=Z_N(z)                         (12)
```

in general.  Therefore the existence of a canonical positive jet metric does not prove the
reflection-passivity required by the Euler--Lorentz RH block.  Any argument which calls `(5)` the
missing RH metric without constructing the prime--archimedean incidence has only renamed the
open step.

The full boundary colligation makes the obstruction exact.  Relative to the split clock, Gamma
translation has the form

```text
E_(N+1)=[E_N  beta_N;
         0    I],                                        (13)
```

where `beta_N` is the nonzero factorial outgoing channel and the boundary self-symbol is the
identity.  For a pure boundary input `b`, orthogonality of the factorial split gives the Green law

```text
||E_(N+1)(0,b)||_F^2-||(0,b)||_F^2=||beta_N b||_F^2>0.   (14)
```

Thus no positive metric which retains this orthogonal source split can make the raw colligation a
contraction.  Its failure of passivity is not an uncontrolled sign: it is exactly the positive
factorial boundary energy.

## Nontrivial positive successor

The no-go leaves a sharper source target.  Gamma supplies, before any Xi divisor is introduced:

1. the positive factorial metric `(5)`;
2. the exact adjoint pair `(6)`;
3. the positive moving-boundary charge `(10)`;
4. the finite Weyl comparison current obtained by exponentiating the analytic half and retaining
   the algebraic half.
5. the exact boundary-excess identity `(14)`.

The missing theorem is consequently an incidence theorem, not the invention of a metric:

```text
[CONJECTURE -- POLARIZED EULER--GAMMA INCIDENCE]
```

There are source-defined maps from the completed Euler valuation module into the factorial Fock
finite clocks such that:

- the anti-reflection entry of the local Euler--Lorentz logarithm maps to the top-boundary current;
- finite observation intertwines reflection and the opposite-variance comparison seam;
- the pullback of `(10)`, after Gamma--Meixner shape damping, is locally uniformly bounded through
  the singular Mertens-corona limit;
- the cofinal incidence is faithful on every reflected rational-Hurwitz orbit.

If the induced reflected Lorentz block and its inverse are contractions in this one pullback
metric, positive-metric rigidity forces every rapidity to vanish and proves RH.  The conjecture is
strictly source-facing: its input metric and boundary charge are already explicit, while its open
content is the all-prime cofinal incidence.

The accompanying prime--Laplace incidence theorem proves that these maps exist
Hilbert--Schmidtly at every finite clock and are jointly faithful.  It also proves that they do
**not** assemble to a bounded map into the standard factorial Fock colimit: a prime column has
squared norm `w_theta(p)p^(-2x_0)exp((log p)^2)`.  Thus “cofinal” above means a projective
Mackey/relative-graph trace topology, not a single factorial Fock Hilbert space.

Because of `(14)`, the word `contractions` in the last paragraph cannot refer to the raw Gamma
translation.  The incidence must first form the source-canonical characteristic/scattering
transform, Cayley transform of a positive-real boundary impedance, or an equivalent star-Kadison
compression whose loss is `(14)`.  Constructing that transform from the paired incoming/outgoing
source channels is part of the conjecture, not harmless system-theory notation.

## Parent-theory boundary

Weighted creation--annihilation adjoints, truncated canonical-commutation defects, and factorial
Fock metrics are classical oscillator algebra.  Their role here is to prevent the positive metric
from remaining unspecified and to isolate the prime--archimedean incidence as the genuine open
core.  No new-science claim is made for `(5)`--`(10)`.

## Gates

- [x] identify the infinitesimal analytic and algebraic clocks
- [x] derive the unique diagonal factorial polarization
- [x] compute the positive rank-one top-boundary charge
- [x] falsify automatic passivity of finite Gamma translation
- [x] identify its exact positive pure-boundary excess
- [x] replace that no-go by an explicit polarized incidence conjecture
- [ ] formalize only if the Euler--Gamma incidence begins to use this metric
