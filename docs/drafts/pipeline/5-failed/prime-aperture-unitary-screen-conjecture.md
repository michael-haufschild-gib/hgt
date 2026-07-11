# Prime-aperture superselection screen — terminal route record

- **ID:** `prime-aperture-unitary-screen-conjecture`
- **Stage:** 5-failed
- **Type:** TERMINAL RH ROUTE RECORD
- **Scientific status:** `[CLOSED AS AN RH ROUTE]`; the screen and heat detector survive as separate
  theorems, but their proposed descent is RH-equivalent
- **Source:** user screen/interference proposal, 2026-07-11
- **Statement:** The critical line is the singular superselection screen of the full prime-density
  spectral states, and the additive heat aperture detects the zeta divisor.  These two proved facts
  do not combine into an RH proof: the assertion that every heat-echo defect produces a normal
  reflected-sector defect is exactly RH, and the canonical nonzero tangent fails the required
  covariance at every hypothetical off-line zero.

## Goal

The load-bearing mechanism is superselection, not ordinary optical propagation and not an
uncertainty inequality.  The same arithmetic object has two incompatible descriptions:

```text
particle register: independent prime occupations and Euler tensor factorization,
wave register:     collective Bohr/Mellin superposition and completed reflection.
```

The critical line is the only place where the two descriptions can inhabit one coherent sector.
Off the line they are disjoint representations, so their scalar cancellation cannot be interpreted
as physical interference.  The zeros are proposed to be fiberwise defects inside the allowed
screen sectors.  RH becomes a descent statement: every analytic zero of the completed source must
lift to one of those physical defects, and therefore cannot live in either bulk.

This is an existence constraint, not a force law.  No vertical evolution, Hamiltonian, or
propagation parameter is part of the claim.

## The qualitative change at the critical line

For `s=sigma+it`, define the arithmetic occupation vector

```text
Psi_s = (n^(-s))_(n>=1).
```

`[PROVED; BRIDGE]`

```text
Psi_s in l2(N)  <->  sigma>1/2,
||Psi_s||^2 = zeta(2 sigma).
```

Unique factorization gives the prime-particle tensor form

```text
Psi_s = tensor_p Psi_(p,s),
Psi_(p,s) = sum_(k>=0) p^(-ks)|k>.
```

After local normalization, the infinite tensor product exists in the vacuum sector exactly when
`sum_p p^(-2 sigma)<infinity`, again exactly for `sigma>1/2`. Thus `sigma=1/2` is a genuine change
of quality:

- on the right, the arithmetic source is a normalizable infinite prime-particle state;
- on the line, that state exits Hilbert space and only a boundary/distributional object can remain;
- on the left, functional-equation reflection identifies the object with the conjugate dual of the
  normalizable state at `1-conj(s)`.

This normalizability wall is already implicit in
[critical-line-fisher-signature-wall.md](../2-fully-proven/not_new_scientific_knowledge/critical-line-fisher-signature-wall.md)
and is `[BRIDGE]`, not an RH proof. The new question is whether the completed source admits a
canonical wall category whose defect support is forced to stay on that wall.

## The superselection screen

The paper theorem
[prime-poisson-superselection-screen.md](../2-fully-proven/not_new_scientific_knowledge/prime-poisson-superselection-screen.md)
constructs the missing boundary state without postulating a wall Hilbert vector.  The Bohr spectral
measure of the normalized full density is the product of one-prime Poisson measures

```text
mu_s = tensor_p nu_(p^(-conj(s))).
```

Kakutani's product-measure dichotomy gives the exact measure-class law

```text
mu_s ~ Haar                       iff Re(s)>1/2,
mu_s ~ mu_(1-conj(s))             iff Re(s)=1/2,
mu_(1/2+it) perpendicular mu_(1/2+iu) iff t!=u.
```

For fixed `t`, the normal states `mu_(sigma+it)` converge weak-star as `sigma` decreases to `1/2`,
but the limit is singular to Haar.  Thus the wall object exists as a singular GNS state after the
trace-class vector disappears.  Moreover every height is a separate sector.  This is the precise
quality change requested by the wave--particle analogy:

```text
bulk:   one normal measure class, with ordinary density matrices,
screen: singular and pairwise disjoint height sectors,
left:   reflected description disjoint from the particle bulk.
```

`[PROVED RECUT]` Interference between the reflected descriptions is meaningful only on the screen.
It is not driven there; away from the screen the joint coherent object does not exist.  A scalar
analytic cancellation off the screen would therefore be a fake unless the completed source proves
that every analytic zero lifts to a normal or fiberwise defect in the screen category.

## The direct-overlap barrier

`[PROVED; BRIDGE]` The simplest quantum realization cannot reach the critical strip. If both
`Psi_z` and `Psi_w` are normalizable, then

```text
<Psi_w,Psi_z> = zeta(conj(w)+z),
Re(conj(w)+z)>1.
```

Therefore every honest Hilbert-space overlap of two canonical arithmetic particle states samples
zeta only in its absolutely convergent, zero-free half-plane. To obtain the completed zeta
amplitude in `0<Re(s)<1`, at least one side of the pairing must be distributional, unbounded, or a
derived boundary object.

This kills the naive claim that zeta zeros are ordinary orthogonality of two normalizable quantum
states. Kakutani/von Neumann product-state dichotomy detects the same threshold `sigma=1/2`, but it
does not identify its overlap with `xi(s)` and therefore adds no localization by itself.

The surviving object must be a controlled particle--wave interface pairing. Its defect cannot be a
bounded matrix coefficient; it must live in the failure of the two completions to glue.

## What the uncertainty principle must retain

For `sigma>1/2`, normalize the particle amplitudes by

```text
a_sigma(n) = n^(-sigma)/sqrt(zeta(2 sigma)),
mu_sigma(n) = |a_sigma(n)|^2 = n^(-2 sigma)/zeta(2 sigma).
```

The probability law `mu_sigma` factorizes exactly into independent geometric prime-occupation
laws. Its ordinary characteristic function is

```text
sum_n mu_sigma(n)e^(-it log n)
  = zeta(2 sigma+it)/zeta(2 sigma).
```

This function lies in `Re(s)>1` and is automatically zero-free. A particle-only analysis therefore
sees the squared amplitudes and moves the spectral parameter from `sigma` to `2 sigma`; it cannot
see the zeta nodes at `sigma+it`.

The wave amplitude is instead

```text
A_sigma(t) = sum_n a_sigma(n)e^(-it log n).
```

For `sigma>1`, this is `zeta(sigma+it)/sqrt(zeta(2 sigma))`. In the Goldilocks region
`1/2<sigma<=1`, the particle vector is still normalizable but this pointwise wave measurement is
unbounded; only analytic continuation or a distributional boundary prescription reaches it.

This factor-of-two is the exact wave--particle split. Born probabilities retain the Euler particle
law but lose the interference phases. The continued wave amplitude retains the interference nodes
but no longer comes from a bounded measurement of the Hilbert state.

The full joint datum is the pure density matrix

```text
rho_sigma(m,n) = a_sigma(m)conj(a_sigma(n)).
```

It is a trace-class, prime-factorized rank-one state exactly for `sigma>1/2`. Its off-diagonal
coherences contain the wave interference; its diagonal is the particle law. On the critical line
the trace-class state itself ceases to exist.

`[PROVED CORRECTION]` This density never loses rank in its domain: it has rank one for every
`sigma>1/2`.  Therefore its rank-defect locus cannot be the zeta divisor.  Nor can a nonconstant
one-complex-variable holomorphic family of positive operators repair the problem: every scalar
quadratic form would then be both holomorphic and real-valued on an open set, hence constant.  A
viable completion object must be singular/on-shell, sesquiholomorphic, indefinite, derived, or
fiberwise rather than an ordinary holomorphic positive density.

`[REFUTED]` Standard Heisenberg, support, variance, or entropic uncertainty inequalities are too
weak: they control global concentration and permit isolated wave nodes. Arbitrary coefficient
phase twists preserve `mu_sigma` while moving the wave zero set, so no theorem depending only on
the particle marginal can locate the divisor. Conversely, functional-equation wave data alone is
RH-blind by the Davenport--Heilbronn fake.

`[CONJECTURE]` The required principle is a completion-descent theorem.  The full density determines
the normal product-Poisson states in the bulk and their singular superselection boundary.  The
Euler--Gamma/theta source must construct a fiberwise observable, correspondence, or derived defect
on that boundary such that every analytic `xi` zero yields a nonzero defect in the sector at the
same height.  Since reflected sectors meet only on the self-dual line, this lift would imply RH.
The pro-polarizable wall complex below is one possible source realization, not the definition of
the screen and not a substitute for the missing zero-to-sector lift.

## The arithmetic-orbit obstruction

`[SEARCH]` The Hedenmalm--Lindqvist--Seip Bohr correspondence identifies square-summable Dirichlet
coefficients with `H^2` on the infinite prime torus. For every `sigma>1/2`, the normalized particle
state has the Bohr wavefunction

```text
F_sigma(z) = zeta(2 sigma)^(-1/2)
             sum_n n^(-sigma) z^kappa(n)

           = tensor_p
             ((1-p^(-2 sigma))^(1/2)/(1-p^(-sigma)z_p))
```

as an `H^2(T^infinity)` vector of norm one.

The physical height screen is not the full phase torus. It is the arithmetic Kronecker orbit

```text
chi_t(p)=p^(-it).
```

This orbit is dense but Haar-null. An `H^2` vector has boundary values only up to Haar-null changes,
so its restriction to `chi_t` is not a bounded or canonical operation. For `sigma>1`, direct
evaluation gives the normalized zeta wave. For `1/2<sigma<=1`, analytic continuation selects a
value on a set that the Hilbert-space wave theory does not see.

This is the exact one-register obstruction:

```text
particle/H^2 theory: controls the full-torus state almost everywhere but not the arithmetic orbit,
wave/xi theory:      controls the arithmetic orbit but forgets the positive prime density matrix.
```

Generic boundary, mean-value, or uncertainty theorems cannot decide isolated nodes on a Haar-null
orbit. The needed result is a source-specific arithmetic restriction theorem for this one
prime-factorized pure state, compatible with completion and reflection. Equivalently, it is a
strictly positivity-improving extension of the phase measurement from `sigma>1` down to the
trace-class wall `sigma=1/2`.

The ambient `L^2` escape is already closed. The formal theorem
`RHTower.no_l2_pointEvaluator_on_representatives` proves that point evaluation cannot descend from
an `L^2` equivalence class even as an arbitrary map. The same null-set obstruction applies to
restricting an `H^2(T^infinity)` boundary class to the Haar-null arithmetic orbit. Therefore the
required measurement must come from additional source-selected analytic regularity or a derived
wall object; it cannot be declared on the ambient Hilbert quotient.

## The additive heat aperture

The paper theorem
[additive-heat-aperture-zeta-zero-echo.md](../2-fully-proven/new_scientific_knowledge/additive-heat-aperture-zeta-zero-echo.md)
constructs such a source-selected measurement throughout the right Hilbert strip.  For `x>0`, let

```text
H_x(m,n)=exp(-pi x(m-n)^2),
E_s(x)=<Psi_s,H_x Psi_s>.
```

`H_x` is the strictly positive additive heat kernel on the integer lattice.  `E_s(x)` is absolutely
convergent for every `Re(s)>1/2`, uses the full off-diagonal density, and contains no analytic
continuation or zero divisor.  Large `x` kills unequal indices and leaves the particle law.  Small
`x` opens the aperture toward full wave coherence.

For `1/2<sigma<1`, its exact small-`x` expansion is

```text
zeta(2 sigma) E_s(x)
  = universal_positive(s) x^(sigma-1)
    + C(s) conj(zeta(s)) x^((s-1)/2)
    + conjugate channel
    + |zeta(s)|^2
    + o(1),
```

where the explicit Gamma factor `C(s)` never vanishes in the strip.  Consequently

```text
zeta(s)=0
  iff
the subleading heat-coherence echo is absent.
```

This closes the measurement-existence problem on the normalizable side.  A zero is a missing
asymptotic interference channel of an everywhere-positive finite-aperture observable, not a zero of
the rank-one density itself and not point evaluation of an ambient `L2` class.  The canonical
polyhomogeneous finite part is `|zeta(s)|^2/zeta(2 sigma)`; the explicit Gamma weight yields
completed intensity.

The theorem does not locate the echo defect.  A hypothetical right-half off-line zero would also
delete the subleading channel.  The remaining RH-hard step is exactly the superselection claim:
prove that disappearance of this source echo necessarily creates a reflected-sector defect, which
can exist only on the self-dual screen.

## Prime phase space

To express the interface geometrically, for a finite prime set `P` define the prime character torus
and its unitary real form by

```text
T_P = (C^x)^P,
U_P = (S^1)^P,
delta_P(s) = (p^(1/2-s))_(p in P).
```

Then

```text
delta_P(s) in U_P  <->  Re(s)=1/2.
```

The proposed `|P|`-dimensional wall object is a geometric-origin polarizable complex `M_P` on a
`|P|`-dimensional prime torus. The `|P|` slits are the coordinate loops. A character `z in T_P`
specifies the phase through every slit. The interference pattern is not an intensity function: it
is the cohomology jump locus

```text
Sigma_P = {z in T_P : H^*(M_P tensor L_z) != 0},
```

equivalently the rank-drop locus of the determinant-of-cohomology section.

The retired target was a compatible wall/recollement pro-object `M_infinity` over all finite prime
sets, with the archimedean theta/Gamma place included in the transition and duality data, such that

```text
Div(xi) = delta^*(Sigma_infinity),
Sigma_infinity = Supp H^*(R lim M_P),
Sigma_infinity subset U_infinity.
```

This formulation is now refuted in its standard derived meaning.  Moreover a finite
torsion-translated subtorus is not contained in the unitary real form; only its intersection with
the arithmetic diagonal is localized by the finite-screen lemma.  Thus neither displayed support
identity follows from the finite parent theorem.

## Why ordinary diffraction is insufficient

`[SEARCH]` The Riemann Xi function already has a classical Fourier/cosine representation. Treating
its real restriction as a diffraction amplitude merely puts the observed dark fringes on the real
screen by definition. Off-line zeros are zeros of the complexified amplitude, which a physical
screen does not constrain.

A fixed finite-slit scalar amplitude is also too small. It is an exponential polynomial or a
finite determinant and falls under established Fourier, hyperbolic-polynomial, Lee--Yang, or
Hilbert--Polya frameworks. None supplies a zeta-specific source law.

The proposed route instead asks for a cohomological support theorem on the complexified phase
space. It must prove absence of dark states for every nonunitary radial character, not merely
describe dark fringes on the unitary locus.

## Finite-screen lemma

`[PROVED; BRIDGE]` Let `P` be finite. Let `Z subset T_P` be a proper algebraic subtorus translated
by a unitary character. Then every point of `delta_P(C)` in `Z` lies on the critical line.

Indeed, some nonzero integer vector `m=(m_p)` and some `c` with `|c|=1` give an equation

```text
product_(p in P) z_p^(m_p) = c
```

on `Z`. Along the arithmetic diagonal, taking absolute values gives

```text
exp((1/2-Re(s)) sum_(p in P) m_p log p) = 1.
```

Unique factorization implies

```text
sum_(p in P) m_p log p = log(product_(p in P) p^(m_p)) != 0
```

for nonzero `m`. Hence `Re(s)=1/2`.

For geometric-origin rank-one cohomology jump loci, the finite-dimensional parent theory makes
the irreducible components torsion-translated subtori, hence unitary-translated subtori. Thus a
finite geometric screen has exactly the desired localization mechanism.

## Why the wall must be infinite-dimensional

`[PROVED; BRIDGE]` A fixed finite union of translated subtori cannot reproduce the zeta divisor.
Pulling one defining monomial equation back along `delta_P` gives a vertical arithmetic
progression, or the empty set. A fixed finite union therefore has `O(T)` intersections up to
height `T`, while the Riemann--von Mangoldt formula gives `N(T) asymp T log T`.

Consequently a fixed finite-dimensional screen cannot reproduce the zeta divisor.  The former claim
that the zeros could therefore be new `R^1 lim` cohomology was incorrect:

```text
finite specialized prime complexes: acyclic in the strip,
ordinary derived inverse limit: zero,
possible surviving object: only a separately defined base-change or nonclosed-range defect.
```

The theorem
[acyclic-finite-fibers-derived-limit-zero.md](../2-fully-proven/not_new_scientific_knowledge/acyclic-finite-fibers-derived-limit-zero.md)
proves this correction.  A singular completion may still fail to commute with specialization, but
then finite-stage perfectness and polarization do not automatically control its support.

## Candidate construction

For each finite `P`, start from the exterior tensor product of the local two-term Koszul complexes

```text
K_p(s) = [C --(1-p^(-s))--> C].
```

They are acyclic for `0<Re(s)<1`. Their torsion records the finite Euler factor. Prime deletion
gives the face maps. This alone is insufficient: the raw inverse system only knows the
absolute-convergence Euler product and has no canonical continuation through `Re(s)=1`.

`[RETIRED]` The proposed archimedean theta/Poisson promotion of these finite Koszul faces to
geometric-origin polarizable complexes `M_P` was supposed to supply a self-duality

```text
M_P(z) ~= dual(M_P(conj(z)^(-1))).
```

No such promotion or determinant was constructed.  Even if it were, finite polarizations give
unitary-translated jump components, not support contained in the unitary torus.  The raw specialized
derived limit is zero, so a live replacement must define a global singular completion before
specialization and prove a new base-change and off-unitary coercivity theorem.

## Attacks

### Finite-dimensional reduction

`[REFUTED]` One fixed `n` cannot work. Its support locus is too rigid and its diagonal intersection
has at most linear height growth. The dimension must be unbounded.

### Fourier-kernel reduction

`[SEARCH]` Taking the incident object to be Riemann's theta kernel and the screen pattern to be its
Fourier transform is classical. Real-rootedness of the transform is RH itself; positivity of the
kernel is insufficient. This interpretation is not a new route.

### Determinant or fermionic reduction

`[SEARCH]` An `n`-particle Slater determinant makes dark fringes into rank drops. In a fixed
dimension this reduces to determinantal/hyperbolic-polynomial or Hilbert--Polya theory. The missing
source-built definiteness is unchanged.

### Two-path visibility reduction

`[BRIDGE; DIRECT VERSION CLOSED]` For two scalar path amplitudes `A,B`, perfect darkness
`A+B=0` forces `|A|=|B|`; the usual pure-state distinguishability and visibility satisfy
`D^2+V^2=1`. The functional-equation factor has unit modulus exactly on the critical line, so this
looks like the desired wall theorem.

The existing exact finite carrier shows the gap. It has

```text
g_N(s)=D_N(s)+chi(s)D_N(1-s).
```

Lean proves `|chi(s)|<1` on the high right half-strip and proves a nonzero floor from the
pointwise domination

```text
|chi(s)D_N(1-s)|+epsilon < |D_N(s)|.
```

But `|chi(s)|<1` alone does not give this: the uncontrolled ratio
`|D_N(1-s)|/|D_N(s)|` can exactly compensate for the reflection-factor imbalance. The required
inequality is the already-known approximate-functional-equation domination wall, not a new
uncertainty theorem.

The functional equation itself is multiplicative and supplies no canonical additive two-path
split. Any successful complementarity route must therefore construct an exact source-defined joint
measurement with no arbitrary split, no remainder, and no uncontrolled reflected-amplitude ratio.
Otherwise the two-slit language is only a reformulation of the closed domination route.

### Functional-equation-only fake

`[REFUTED]` Functional-equation self-duality alone cannot provide the polarization. The
Davenport--Heilbronn family has the symmetry and off-line zeros but lacks Euler factorization.
Therefore `M_P` must be constructed from the genuine prime faces, not from Xi after continuation.

### Particle-law and ordinary-uncertainty fake

`[REFUTED BY SEARCH]` Let `chi` be completely multiplicative and unimodular, and form the Helson
zeta function

```text
zeta_chi(s)=sum_n chi(n)n^(-s)=product_p (1-chi(p)p^(-s))^(-1).
```

For `sigma>1/2`, its normalized particle amplitudes have exactly the same probabilities as zeta:

```text
|chi(n)n^(-sigma)|^2/zeta(2 sigma)=n^(-2 sigma)/zeta(2 sigma).
```

Hence the complete particle marginal, prime-occupation independence, Hilbert norm, Fisher metric,
and trace-class wall are identical. Nevertheless, Helson zeta continuations can have prescribed
zeros and poles below `Re(s)=1`, including in the right half of the critical strip. Thus no
uncertainty theorem invariant under diagonal phase twists can imply RH.

The surviving principle must be phase-sensitive. It must use the exact untwisted phase `chi=1`
together with the archimedean theta/Gamma reflection polarization. Particle probabilities,
factorization, normalizability, and generic wave--particle complementarity are jointly
insufficient.

### Shifted Euler-product fake

`[CONJECTURAL FILTER]` A symmetric shifted product such as

```text
Lambda(s+a)Lambda(s-a)
```

has an Euler product and a central functional equation but has divisors shifted away from the
central line. Its local parameters contain nonunitary radial translations `p^(+/-a)`. A valid
polarizable prime-aperture category must reject this object at finite level. If it does not, the
route is false.

### Circular realization

An arbitrary perfect complex can be manufactured with determinant `xi`. That construction is
forbidden. The finite `M_P`, face maps, polarization, and archimedean weld must be defined before
the zeta divisor is read, and the determinant identity must follow from the existing completed
source identity.

### Ambient-Hilbert restriction

`[REFUTED IN LEAN, AT THE QUOTIENT LEVEL]` An `L^2` or boundary-`H^2` class does not determine its
values on a null set. Thus the arithmetic phase screen cannot be obtained by literal point
sampling of the normalizable wave state. A source-selected RKHS or rigged/derived boundary
category is indispensable, and importing an RH-conditional de Branges realization would be
circular.

### Joint-algebra extension

`[REFUTED]` The heat aperture cannot be adjoined as an ordinary sector-preserving observable in the
natural particle representation.  If `D=l-infinity(N)` is the particle diagonal and `x>0`, then

```text
W*(D,H_x)=B(l2(N)).
```

Indeed `P_m H_x P_n` is a nonzero scalar multiple of every matrix unit `E_(mn)`.  The theorem is
recorded in
[additive-heat-diagonal-generates-full-operator-algebra.md](../2-fully-proven/not_new_scientific_knowledge/additive-heat-diagonal-generates-full-operator-algebra.md).
Thus the naive joint algebra has scalar center and destroys the particle superselection
decomposition.

## Retired open cores

The terminal theorem
[heat-echo-superselection-descent-is-rh.md](../5-failed/heat-echo-superselection-descent-is-rh.md)
proves that the first core below is not an intermediate lemma: it is equivalent to RH.  It also
computes the canonical tangent's primewise covariance defect and shows that the tangent is nonzero
but noncovariant at every hypothetical off-line zero.  The remaining proposed realizations do not
supply an independent descent and are retired with this route.

`[RETIRED CORE 1: HEAT-ECHO-TO-SECTOR DESCENT]` The additive heat aperture already constructs the
source zero detector on `1/2<Re(s)<1`.  Lift its missing subleading channel to a fiberwise object
`D_t` in the singular GNS sector of `mu_(1/2+it)`.  Prove both directions needed for a genuine
divisor lift:

```text
xi(rho)=0
  =>
rho=1/2+it and D_t has a nontrivial source defect,

D_t has a nontrivial source defect
  =>
xi(1/2+it)=0.
```

The first implication contains the RH-hard content.  Defining `D_t` only for points already on the
line, or setting its determinant equal to `xi(1/2+it)`, does not address hypothetical off-line zeros.

`[RETIRED CORE 2: ADDITIVE--MULTIPLICATIVE COMPLETION LOCK]` The product-Poisson state is constructed
from multiplicative prime data.  The fixed external phase reference must come from the additive
theta/Poisson structure on the same integers.  Construct their joint object before analytic zeros
are read.  It must distinguish the untwisted source from a Helson phase twist through the exact
measure-class criterion

```text
sum_p |chi(p)-1|^2/p,
```

or through a stronger source law.  Merely using local-unitary invariants, Euler probabilities, or
functional-equation symmetry is already refuted.

The route gate
[prime-screen-bounded-observable-almost-periodicity.md](../2-fully-proven/not_new_scientific_knowledge/prime-screen-bounded-observable-almost-periodicity.md)
proves that the expectation of every bounded continuous prime-screen observable is uniformly
almost periodic in height.  Completed `xi(1/2+it)` instead decays to zero.  Hence the missing object
must contain a noncompact archimedean component or be unbounded, distributional, singular, or
derived; no bounded refinement of the prime density alone can work.

`[RETIRED CORE 3: FIBERWISE FAITHFULNESS]` The height sectors are mutually singular.  Integrating them
against a normal trace would again be blind to isolated or density-zero off-line defects.  The
completion object must therefore be fiberwise faithful: a kernel, signed index, determinant line,
or derived multiplicity that cannot average away a single sector.  It must not be manufactured from
the zero divisor.

`[RETIRED SECONDARY REALIZATION: PRO-POLARIZATION]` The compatible finite-prime complexes `M_P`
cannot create a defect by an ordinary derived limit of their acyclic specializations:

```text
R lim_P (specialized M_P)=0.
```

A different Route A may still start from a global singular completion and study failure of
specialization or a translation-unitary theta convolution defect.  That is a new route and must not
be credited to the retired finite-acyclic pro-object.

`[RETIRED CORE 4: FAKE REJECTION]` Prove that the proposed category admits the zeta local data but
rejects nonunitarily shifted self-dual Euler products before any zero is inspected.

## Parent-theory boundary

- Riemann's Xi Fourier representation, Pólya universal-factor questions, de Bruijn--Newman flow,
  Lee--Yang stability, and Hilbert--Polya determinants are `[SEARCH]`; they do not supply this
  pro-support object.
- The square-summable Dirichlet/Bohr `H^2(T^infinity)` correspondence and its reproducing kernel
  `K_w(z)=zeta(conj(w)+z)` are `[SEARCH]`. They prove the normalizability and direct-overlap
  boundaries but do not define restriction to the Haar-null arithmetic orbit in the Goldilocks
  strip.
- The product-Poisson spectral measures, their normal-to-singular boundary, the exact reflected
  measure-class seam, and pairwise singularity of distinct critical heights are `[PROVED; BRIDGE]`
  in
  [prime-poisson-superselection-screen.md](../2-fully-proven/not_new_scientific_knowledge/prime-poisson-superselection-screen.md).
  They construct the screen and remove the ambient-Haar point-sampling problem, but they do not
  construct the completed defect observable.
- Bounded continuous observables of the prime screen have uniformly almost-periodic height
  expectations, whereas completed Xi vanishes at vertical infinity.  This `[PROVED; BRIDGE]`
  obstruction is recorded in
  [prime-screen-bounded-observable-almost-periodicity.md](../2-fully-proven/not_new_scientific_knowledge/prime-screen-bounded-observable-almost-periodicity.md).
- The additive heat aperture and its exact subleading zeta echo are `[PROVED; CANDIDATE NEW]` in
  [additive-heat-aperture-zeta-zero-echo.md](../2-fully-proven/new_scientific_knowledge/additive-heat-aperture-zeta-zero-echo.md).
  This supplies the full-density measurement on the right Hilbert side but not the
  echo-to-superselection descent.
- Helson zeta functions with prescribed continued zeros and poles are `[SEARCH]`. They prove that
  the particle law, Euler tensor factorization, and trace-class wall do not determine the wave
  divisor; the missing datum is exact completion-locked phase coherence.
- Finite cohomology jump loci being torsion-translated subtori is `[SEARCH]`, from the established
  Simpson--Arapura--Budur--Wang and Hodge-module support-locus theory.
- The arithmetic-diagonal unitary intersection lemma is `[BRIDGE]`, combining that parent theorem
  with unique factorization.
- The source-built zero-to-sector descent, whether realized by a pro-polarizable derived limit or a
  different fiberwise object, is `[CONJECTURE]`. No RH or novelty claim is made before construction
  and proof.

## Current verdict

`[CLOSED AS AN RH ROUTE]` The screen proposal produced two substantive but logically independent
objects.

What is now closed:

1. the density itself is rank one and cannot carry the divisor by rank loss;
2. the critical line is an exact superselection transition of canonical prime Poisson states;
3. height becomes an outer motion between mutually singular sectors at the screen;
4. bounded prime observables cannot supply completed Xi because they are almost periodic;
5. the additive heat aperture is a canonical positive full-density measurement in the Hilbert
   strip; and
6. zeta zeros are exactly the loss of its subleading heat-coherence echo.

The attempted connecting implication is

```text
missing source heat echo
  =>
nonzero reflected-sector defect.
```

Superselection would then force the sector onto `Re(s)=1/2`, but the terminal theorem proves that
this implication is precisely RH.  A hypothetical off-line zero deletes the heat echo while the
two reflected sectors remain disjoint, and every currently constructed source object remains
consistent.  The canonical tangent `zeta(s-1)` is nonzero there but its covariance defect vanishes
only on the critical line.  Thus no independent mechanism performs the required category change.

## Lean surface

The existing formal tree already contains:

- `isMultiplicative_iff_bohr_factorization` for the Euler/Bohr finite-face filter;
- `weld_reflection_euler_prime` for reflection acting as inverse prime holonomy; and
- `no_l2_pointEvaluator_on_representatives` for the ambient-Hilbert sampling obstruction; and
- the completed source-to-Xi relative-resolvent identity.

The finite-screen lemma remains an independent formal target: a nontrivial prime monomial with unit
norm along `delta_P(s)` forces `Re(s)=1/2`. A scratch proof confirmed that its analytic wall and the
normalizability threshold reduce to existing mathlib summability and complex-exponential lemmas.
No tree module is added yet.  The substantive new paper theorem requires polylogarithm boundary
asymptotics absent from the current API, while formalizing another elementary wall selector would
not advance the echo-to-sector open core.

## Gates

- [x] precise screen, slit, phase, jump-locus, infinite-dimensional necessity, fake tests,
  superselection recut, and noncircular source condition isolated
- [x] positive additive heat detector constructed and its zero echo proved
- [x] desired zero-to-sector descent proved equivalent to RH
- [x] canonical nonzero tangent tested and shown to fail sector covariance off the line
- [x] route retired to 5-failed; no tautological Lean wrapper added

## References for the parent boundary

- S. Kakutani, *On equivalence of infinite product measures*, Ann. of Math. 49 (1948).
- H. Hedenmalm, P. Lindqvist, and K. Seip, *A Hilbert space of Dirichlet series and systems of
  dilated functions in L2(0,1)*, Duke Math. J. 86 (1997), arXiv:math/9512211.
- E. Saksman and K. Seip, *Integral means and boundary limits of Dirichlet series*, Bull. London
  Math. Soc. 41 (2009).
- I. Bochkov and R. Romanov, *On zeroes and poles of Helson zeta functions*, J. Funct. Anal. 282
  (2022), arXiv:2106.15949.
- J. Andersson, *Mittag--Leffler type theorems for Helson zeta-functions*, arXiv:2408.15713.
- N. Budur and B. Wang, *Cohomology jump loci of quasi-projective varieties*, Ann. Sci. ENS 48
  (2015), arXiv:1211.3766.
- G. Pareschi, M. Popa, and C. Schnell, *Hodge modules on complex tori and generic vanishing for
  compact Kahler manifolds*, Geometry & Topology 21 (2017).
- C. Schnell, *Holonomic D-modules on abelian varieties*, Publ. Math. IHES 121 (2015).
- Y. Liu, L. Maxim, and B. Wang, *Perverse sheaves on semi-abelian varieties*, arXiv:1804.05014.
