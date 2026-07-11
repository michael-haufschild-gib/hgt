# Prime exponentials make the local Euler-source image holomorphically determining

- **ID:** `prime-exponential-holomorphic-determining-source-image`
- **Stage:** 2-fully-proven / not-new
- **Type:** `[BRIDGE]` theorem (paper)
- **Scientific status:** `[NOT NEW SCIENTIFIC KNOWLEDGE]`.  The proof is a direct specialization
  of classical Fourier--Borel duality and exponential-system completeness, followed by the standard
  lowest-homogeneous-term argument for analytic functionals.  Its exact Euler-source packaging is
  useful to the project, but it introduces no new parent mechanism.
- **Statement:** On every convex complex domain, the linear span of the prime exponentials
  `p^(-s)` is dense in the compact-open holomorphic-function space, even after deleting any finite
  set of primes.  Consequently, on a bounded convex domain the union of the finite-support
  degree-one Euler logarithmic-flux images near the trivial source is a determining set for
  continuous analytic germs: an analytic functional vanishing on every such source germ is the
  zero germ.

## Goal

Locate the topology in which an all-order completed-source constraint can exist.  The prior
finite-jet theorem only excludes equations in finitely many derivatives.  The theorem here excludes
every continuous analytic equation on the full compact-open holomorphic germ space.  Therefore a
surviving RH-relevant source condition must retain the arithmetic coefficient datum at infinity, or
use a genuinely discontinuous/nonlocal incidence operation.  Adding the fixed archimedean flux is a
translation and does not change the conclusion.

## Gates

- [x] 0 -> 1: exact locally convex statement and dual attack identified
- [x] 1 -> 2: complete paper proof of linear completeness and nonlinear determination
- [ ] 2 -> 3: not selected for Lean; the required analytic-functional/Frechet-holomorphy API is not
  present, and a partial algebraic shell would not certify the theorem
- [x] parent-theory gate: Fourier--Borel/exponential-system completeness
- [x] novelty audit: downgraded to `[BRIDGE]`

## Theorem A: prime-exponential compact-open completeness

Let `D` be a nonempty convex domain in `C`, and let `O(D)` carry the topology of uniform convergence
on compact subsets.  For every finite set `S` of primes,

```text
closure span_C {s |-> p^(-s) : p prime, p notin S} = O(D).
```

### Proof

Suppose the closed span is proper.  Hahn--Banach gives a nonzero continuous linear functional
`L : O(D) -> C` annihilating every retained prime exponential.  Continuity in the compact-open
topology gives a compact `K subset D` and a constant `C_K` such that

```text
|L(f)| <= C_K sup_(s in K) |f(s)|.
```

Define the Fourier--Borel transform

```text
B_L(z) = L(s |-> exp(-z s)).
```

The map `z |-> exp(-z s)` is entire with values in `O(D)`, hence `B_L` is entire.  If
`R_K = max_(s in K) |s|`, then

```text
|B_L(z)| <= C_K exp(R_K |z|),
```

so `B_L` has exponential type.  Since `L` kills the retained prime exponentials,

```text
B_L(log p) = 0
```

for every prime outside `S`.  A nonzero entire function of exponential type has `O(R)` zeros in
`|z| <= R`, counted with multiplicity, by Jensen's formula.  But the displayed zeros already number

```text
pi(exp R) - |S|,
```

which grows like `exp(R)/R`.  Hence `B_L` is identically zero.

Differentiating at zero in the compact-open topology gives

```text
B_L^(n)(0) = L((-s)^n) = 0
```

for every `n`.  Thus `L` annihilates all polynomials.  Polynomials are dense in `O(D)` because a
convex domain is Runge, so `L=0`, contradicting its construction.  The closed span is therefore all
of `O(D)`.  Removing finitely many primes does not affect the prime-counting contradiction.  QED.

## Theorem B: the nonlinear Euler microimage is analytically determining

Now let `D` be bounded and convex and put `E=O(D)`.  For a prime `p` and a parameter `a` sufficiently
close to zero, define

```text
phi_p(a)(s) = (log p) a p^(-s) / (1 - a p^(-s)).
```

For every finite prime set `P`, let

```text
Phi_P(a) = sum_(p in P) phi_p(a_p).
```

Boundedness of `D` makes `sup_D |p^(-s)|` finite, so `Phi_P` is a holomorphic map from a
neighbourhood of zero in `C^P` into `E`.  Let `M` be the union, over all finite `P`, of these local
images.

Consider a continuous analytic germ `H` at zero in `E`.  Concretely, assume that on a neighbourhood
of zero it has a convergent Taylor expansion

```text
H(f) = sum_(k>=0) A_k(f,...,f),
```

where each `A_k : E^k -> C` is continuous, symmetric, and `k`-linear.  If

```text
H(Phi_P(a)) = 0
```

for every finite `P` and all sufficiently small `a`, then `H` is the zero germ.

### Proof

The zero parameter belongs to every source chart, so `A_0=H(0)=0`.  Suppose that `H` is not the zero
germ and let `k>=1` be the first index with `A_k` nonzero.  The differential of `Phi_P` at zero is

```text
d Phi_P(0)(a) = sum_(p in P) a_p v_p,
v_p(s) = (log p) p^(-s).
```

The degree-`k` homogeneous part of the identically zero finite-dimensional germ
`H o Phi_P` is therefore

```text
a |-> A_k(d Phi_P(0)(a), ..., d Phi_P(0)(a)).
```

It vanishes for every finite `P` and every `a`.  Hence the continuous homogeneous polynomial

```text
Q_k(f) = A_k(f,...,f)
```

vanishes on the linear span of the vectors `v_p`.  Theorem A says that this span is dense in `E`.
Continuity gives `Q_k=0` on `E`, and complex polarization gives `A_k=0`, contradicting the choice of
`k`.  Thus every Taylor coefficient vanishes and `H` is the zero germ.  QED.

## Completed-source translation

Let `A` be any fixed holomorphic archimedean/boundary flux on `D`.  If an analytic germ at `A`
vanishes on

```text
A + M,
```

translate by `A` and apply Theorem B.  The germ is zero.  Therefore adjoining the fixed
archimedean channel cannot create a compact-open analytic equation for the completed Euler-source
microimage.

Equivalently, the completed finite-support source image is analytically Zariski dense at the trivial
Euler point in this local Frechet sense.  This statement is stronger than finite-jet openness: it
rules out a single continuous analytic equation depending on all derivatives or on the whole local
holomorphic function.

## Theorem C: coordinatewise coefficient memory still decouples on completion

Let `c00(Primes)` be the finite-support prime coefficient fields and define

```text
T(a)(s) = sum_p a_p p^(-s).
```

Give `C^Primes` the product topology.  Then the graph

```text
Gamma = {(T(a),a) : a in c00(Primes)}
```

is dense in

```text
O(D) x C^Primes.
```

Indeed, a basic neighbourhood of `(f,a)` controls `f` on finitely many compacta and controls only a
finite prime set `S` of the coefficient field.  Fix the coefficients on `S` equal to the prescribed
ones.  Theorem A, applied after deleting `S`, approximates

```text
f - sum_(p in S) a_p p^(-s)
```

by a finite linear combination of the remaining prime exponentials.  The resulting finite-support
field lies in the basic coefficient neighbourhood and its Dirichlet polynomial lies in the basic
holomorphic neighbourhood.

Both factors in the displayed product are complete.  Consequently, the completion of
`c00(Primes)` for the topology induced simultaneously by compact-open convergence of `T(a)` and
coordinatewise convergence of every `a_p` is the full decoupled product

```text
O(D) x C^Primes.
```

Thus merely remembering all prime coordinates does not preserve source--germ compatibility under
completion.  A meaningful arithmetic-at-infinity topology must impose joint weighted tail control;
the product topology is too weak.

## Positive research consequence

The source classifier has two incompatible topologies:

```text
compact-open holomorphic topology:  no nonzero local analytic equation exists;
coordinatewise coefficient topology: completion decouples coefficients from the germ;
weighted arithmetic tail topology:  prime-power support and rank-one ray equations classify the image.
```

The missing RH mechanism must use the second topology and the selected divisor point together.  It
cannot be a continuous analytic functional of the completed-flux germ alone.  In particular, merely
allowing infinitely many Taylor coefficients does not solve the finite-jet problem: continuity in
the compact-open topology still erases the arithmetic source distinction.

This identifies the next object as a pointed source--divisor incidence class in an
arithmetic-at-infinity topology.  The theorem does not supply that class and does not prove RH.

## Scope boundary

- Theorem A is linear and applies to every convex domain, bounded or unbounded.
- Boundedness is imposed in Theorem B only to obtain a common holomorphic parameter neighbourhood
  for each finite Euler chart on the whole domain.
- The source charts are based at the trivial Euler product `a_p=0`, not at the zeta point `a_p=1`.
- The conclusion concerns analytic equations valid on the full degree-one source class.  It does
  not prevent a noncanonical analytic functional from vanishing at the single fixed zeta source.
- Theorem C concerns the linear prime packet, which is the tangent source at the trivial Euler
  point.  It identifies the minimal topology failure and does not assert nonlinear Euler-image
  density.
- The theorem is unpointed.  Coupling the fixed coefficient field to a selected zero remains the
  open core.

## Parent-theory audit

The Fourier--Borel transform of analytic functionals and completeness of exponential systems in
compact-open holomorphic spaces are classical parent theories.  Modern explicit completeness
criteria include B. N. Khabibullin and E. G. Kudasheva, *Completeness of exponential systems in
spaces of functions on a compact or domain and their area*, arXiv:2306.15899.  The zero-counting
argument above is the elementary overcomplete case: the frequency set `{log p}` has exponentially
many points in a disk of radius `R`, whereas a nonzero exponential-type transform has only linearly
many zeros.

The nonlinear conclusion is the standard lowest-nonzero-homogeneous-term argument once the tangent
span is dense.  The exact prime/Euler packaging was not found in the checked sources, but both proof
mechanisms are routine parent theory.  The dual gate therefore classifies this theorem as
`[BRIDGE]`, not as new scientific knowledge.
