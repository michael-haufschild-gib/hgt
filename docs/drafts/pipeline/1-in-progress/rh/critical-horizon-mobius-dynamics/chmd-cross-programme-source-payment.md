# CHMD: source payment from the shared arithmetic programmes

- **ID:** chmd-cross-programme-source-payment
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Statement:** Derive an actual odd-source estimate paying the reflected-prime collar or primitive oneL defect, retaining the complete Weil form.

## Route and blockers

Odd theta–Doob positivity implies RH. The open sign is the comparison between
complete archimedean-plus-prime jump energy and cosh mass. In secondary odd
coordinates, direct jumps and the sinh source must pay the reflected-prime
collar. In nodal coordinates, both the primitive half-Rayleigh bound and the
oneL defect payment remain open.

The fixed-aperture real Weil completion now lands injectively with closed
range in the signed-radical quotient. This removes a domain mismatch; its
aperture-dependent norm equivalence is not a sign estimate.

## Conjecture ledger

### 1. Eigenvector admission beyond the small-shift interval

**Conjecture.** The actual equation for an odd CHMD eigenvector above one half
improves its weighted tail enough to pair with every shifted theta source.

**Reason to test.** ACT supplies the exact shifted-source law; existing CHMD
pairings require `1 < 2 * exp (-2 * |a|)`. Removing this restriction must come
from a domain estimate on the eigenvector, not formal continuation of a
weighted integral.

**Current check.** Stationary-resolvent positivity and nodal sub-invariance
alone give no improved tail. In physical coordinates the infinite prime
translation sum is not a bounded ordinary-L2 operator. Any proposed decay
bootstrap must retain that sum and prove its domain bounds.

**Learned limitation.** All-shift pairing would not by itself justify
ordinary-L2 Fourier uniqueness. Convolution with theta can annihilate
exponential Xi-zero modes outside ordinary L2. Thus the argument also
needs an independently proved growth class that excludes those modes.
The decay conjecture is unresolved, not disproved.

### 2. Collective prime-tower compensation

**Conjecture to sharpen.** AOT's exact coset Toeplitz/Hankel decomposition can
be combined across primes without spending the archimedean diagonal more
than once. The arithmetic distinction between prime-power and mixed-prime
coordinates may supply the required allocation.

**Reason to test.** AIP compresses prime towers to first-shift correlations;
AOT gives explicit Cholesky squares; BVI distinguishes additive incidences
from identities valid for arbitrary multiplicative models. ACCC warns that
bounding the raw coherent prime comb before its polar cancellation loses
the critical scale.

**Required outcome.** A concrete source-family estimate or a discharged
analytic premise, not a conditional allocation certificate. Lattice
balance alone does not extend to continuum profiles: AOT proves dense
frustration for the latter.

**Failed inference.** The README's final `>= 0` after the tower lower bound
was unsupported. The Lean theorem retains an arbitrary-sign coset Toeplitz
sum. Coefficients `q(2)=1`, `q(2p)=-1`, zero elsewhere, for `p>=5`, expose
the missing direct term while the unit-coset Hankel and its reflected
diagonal vanish. Corrected the README to state the actual retained bound.
The proved Hankel payment survives; blanket tower positivity does not.

### 3. Identify the entire real aperture domain

**Theorem (paper).** The closure of the real smooth aperture core in the
CCM form norm equals precisely the form-domain vectors whose physical
representative is real almost everywhere. Consequently every such vector
has a unique inverse-Doob lift in the completed CHMD aperture graph, and
its full Weil quadratic form is preserved in the signed quotient.

**Dependency-closed proof.** Let `S` be the closed real smooth core. Native
complex inner products of two core vectors are real: the full Weil form,
finite prime translations, polar operator and scalar L2 term all have
real mixed pairings on real sources. Subtracting the bounded remainder
gives the claim for the form-domain inner product. Continuity extends it
to `S`. Thus `iS` is real-orthogonal to `S`.

Let `P` be the real orthogonal projection onto `S`. Every complex smooth
source decomposes into its real and imaginary smooth cores, so `P` selects
the real core. The physical embedding therefore satisfies `J P = Re J`
on the dense smooth core and hence on the whole form domain. Injectivity
of `J` gives `P u=u` exactly when `J u` is real. This proves the asserted
description of `S`; the already proved graph/Weil equivalence supplies
the inverse-Doob lift, and full Weil-form preservation follows from the
existing quotient landing theorem. No arithmetic sign is assumed.

**Role on the route.** This removes a domain-admission premise for rough
real restricted-Weil states. It does not pay the open prime collar.
Formalization in progress.

**Forced strengthening.** Set `r=Pq` and `s=P(-i q)`. The physical identity
gives `q=r+i s` by injectivity; orthogonality gives
`||q||^2=||r||^2+||s||^2`. Mixed Weil pairings of vectors in `S` are real,
again by core density. Therefore `W(q,q)=W(r,r)+W(s,s)` on the diagonal.
The real CHMD lifts of `r,s` consequently realize every complex CCM form
vector and preserve its complete signed energy as a sum of two quotient
energies. This statement has no reality hypothesis on the input vector.

### 4. A residue-packet realization of the primitive defect

**Concrete candidate.** For an actual odd bound eigenstate, construct
zero-mean finite prime packets whose logarithmic moments converge to its
oneL defect coordinate, and prove that their signed residue-gap energies
are paid by its negative nodal cross-pairing.

BVI's `primePacketBilinear_eq_of_primePacketMass_eq_zero` proves
`LogMoment^2 <= -(1/2) sum a_p a_q E_gap(p,q)` for every zero-mean packet.
This is the right direction of inequality for defect payment, provided
the actual source-to-packet map is constructed and the energy comparison
is proved. The THIM module
`NodalDefectMarkovSubinvarianceAndCenteringPronicGramBridge` contains nodal
identities and pronic identities in separate sections; it supplies no
isometry or contraction identifying these two forms. Similar-looking
rank-one corrections alone do not establish that identification.

**Attack discipline.** Do not postulate the map or either comparison as a
new premise. Start from literal theta sources and literal centred prime
rows. Preserve all mixed terms and both source polar moments.

### 5. The aperture completion is the entire supported maximal graph

**Conjecture with paper proof.** A CHMD maximal graph vector belongs to the
aperture-core completion exactly when its physical source vanishes outside
the closed aperture. Thus localized rough nodal lobes have actual CCM form
coordinates, including sources touching the aperture boundary.

**Proof.** The forward implication is established. For the converse, first
take a bounded measurable graph source supported in `[-a,a]`. Mollify it
with the existing normalized smooth kernels of radius at most `1/4`.
Multiplication by theta gives real smooth physical sources in aperture
`a+1`. The existing stationary-energy convolution bound and finite prime
measure bound give a uniform full graph-norm bound. The source coordinates
converge strongly. Weak Hilbert compactness and source-map injectivity
therefore put the original graph vector in the closed aperture-`a+1` core.

For an unbounded supported source, clip its values and choose the compact
representative by multiplying by the aperture indicator. Endpoint
nonsingularity preserves its graph differences. The existing graph-norm
convergence of clipping and closedness give the same larger-aperture
admission. Transport to the CCM domain there. Its physical support still
lies in `[-a,a]`, so the very same weighted Fourier vector belongs to the
aperture-`a` CCM kernel. The real-domain identification gives a graph lift
at aperture `a`; physical-source injectivity identifies that lift with the
original graph vector. This removes the temporary aperture enlargement.

**Forced consequence.** Positive part, negative part and modulus preserve
the completed aperture graph, since they preserve zero outside the
aperture. Their transferred CCM coordinates retain the literal CHMD nodal
cross-pairing. This discharges domain admission for local rough nodal
estimates; it does not assert the still-open arithmetic payment.

**Status.** Dependency-closed mathematical argument; exact API and Lean
formalization pending. No hypothesis of smoothing convergence in the full
graph norm is needed: boundedness plus strong source convergence suffices.

## Proof integrity

Each claim must be checked against its Lean statement. No external search,
numerical experiment, novelty assertion, assumed arithmetic estimate, or
placeholder is part of this work. Failed conjectures remain recorded with
the mathematical reason and the next concrete conjecture.

## Gates

- [x] Route and complete signed target identified.
- [ ] Dependency-closed source-payment advance on paper.
- [ ] Exact theorem formalized and checked directly in Lean.
- [ ] Transitive axiom audit and umbrella import.
