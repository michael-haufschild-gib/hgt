# Poisson boundaries and the origin-mass completion

- **ID:** qii-origin-mass-boundary-density
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** ../1-in-progress/q-ii-source-effectivity-and-linear-degree.md
- **Statement:** Genuine Poisson boundaries are dense in the canonical half-density L2 completion of the all-weight Meyer source; every genuine class therefore has representatives with arbitrarily small origin square mass.

## Corpus basis

`FrankensteinMeyerHalfDensityL2KoszulDescent` already constructs the injective
linear map `deningerMeyerHalfDensityL2LM`, proves its integrability, and
intertwines centered source dilation with ordinary unitary translation.
`DeningerMeyerDilationFlow.deningerMeyerStrongLogFlow_range_le` proves
preservation of the actual Poisson boundary. The actual Xi cap has Mellin
transform Xi. `XiThetaL2Cyclicity` proves the ordinary L2 translation
cyclicity mechanism using Fourier uniqueness and almost-everywhere
nonvanishing of Xi on the critical line.

The intended proof embeds the actual Xi-cap boundary into the half-density
space, identifies its Fourier transform with Xi on the critical line, and
uses cyclicity. Its translates remain genuine boundaries. Density then gives
small origin-mass representatives in each actual source coset.

## Paper proof [PROVED HERE]

Let B be the actual cap-to-Poisson-boundary map and let iota(g)(t)=exp(t/2)g(t)
be the existing injective map into ordinary complex L2. Exact norm integration
and the origin degree identity give

    ||iota(g)||² = integral exp(t)|g(t)|² = Re origin(g * g^sharp).

For the fixed actual Xi cap k, Fourier expansion gives

    Fourier(iota(Bk))(w) = Xi(1/2 - 2*pi*i*w).

The affine map from real w to its displayed complex argument is injective.
Xi is entire and nonzero at 1, so its complex zero set is countable. The
real Fourier profile is therefore nonzero almost everywhere.

For completeness, the L2 cyclicity step needs no positive lower bound on
that profile. If a vector v is orthogonal to every character multiple of a
profile f, then conjugate(v)f is integrable by Cauchy–Schwarz and all its
Fourier coefficients vanish. Fourier uniqueness gives conjugate(v)f=0
almost everywhere. Since f is nonzero almost everywhere, v=0. Hilbert
duality gives density of the character span. Plancherel gives density of
all real translates of iota(Bk).

Every such translate is again the image of an actual boundary: the existing
centered source flow intertwines iota with translation, while source flow
preserves B's range and its scalar centering can be absorbed in the cap.
Consequently iota(B(cap)) is dense in the whole L2 space.

Given any actual source g and epsilon>0, choose a boundary Bf with
||iota(g)-iota(Bf)||<sqrt(epsilon). The actual source h=g-Bf has exactly the
same genuine quotient class as g and positive origin square mass less than
epsilon. Thus the quotient infimum of this mass vanishes on every class.
Any continuous linear L2 reporter killing actual boundaries vanishes by
density. This is an unconditional collapse of this particular Hilbert
quotient, with no assertion of density in the original all-weight topology.

## Positive survivor

The actual full-jet source quotient remains meaningful in its stronger
topology. Its positive ambient origin metric cannot be repaired by taking
the quotient infimum: that repair loses every class. The exact continuous
boundary-annihilating reporter space in this completion is zero. This also
distinguishes the existing half-density L1 completion, where critical Mellin
evaluations can remain continuous, from ordinary half-density L2.

## Lean status

The reusable L2 cyclicity module passed its actual-file check and both standard
axiom audits. The arithmetic density proof is still unverified:

- `HTGeometry/L2TranslationCyclicity.lean`: certified general cyclicity step.
- `ArithmeticCastelnuovoSeveri/PoissonBoundariesAreDenseInOriginMass.lean`: exact Fourier profile, origin
  norm identity, actual boundary density, small representatives, and vanishing
  of every continuous linear boundary-annihilating reporter.

No theorem from these drafts is cited as Lean-certified. External novelty
unverified. No all-weight source closure or RH conclusion is claimed.

## Continuous nonlinear readings

The same density proof classifies every continuous reading F from origin L2
into any Hausdorff space: if F(iota(g)) depends only on the genuine Poisson
class, then F is constant. Indeed every boundary has the zero class, so F
equals F(0) on the dense boundary image; continuity gives equality everywhere.
Conversely a constant reading is class invariant. This does not assume linearity
or a norm on the target. The linear zero-reporter corollary therefore also
extends to arbitrary Hausdorff topological complex vector targets. These
endpoints are now in the unverified boundary-density draft.

## Faithful comparison consequences

The faithful compact-open comparison is already proved by
`DeningerMeyerGlobalXiSynthesis.deningerMeyerCompactOpenXiComparison_injective`.
No continuous map from origin L2 can recover this comparison on every actual
source. Otherwise it would be class invariant, hence constant by density,
contradicting injectivity on a nonzero point source. The same argument excludes
continuous recovery of the faithful full-Hasse convolution operator, even by
a nonlinear map. Nontriviality is unconditional: Hardy supplies a Xi point,
and its actual point source has value one there. This applies the result to
the existing compact-open and operator completions without assuming a positive
Gelfand interface. Draft: `/tmp/QIIOriginHilbertCohomologyObstructionDraft.lean`,
unverified.

The actual candidate now states the quotient-infimum conclusion without implicit
limit interchange: `meyerOriginSquareMass_class_lower_bound_iff` says a real b
bounds the origin square mass of every representative of a fixed genuine class
exactly when b<=0. Nonnegativity supplies all such bounds; a positive b is
contradicted by the proved small representative with epsilon=b. This endpoint
is unchecked together with the arithmetic density leaf.
