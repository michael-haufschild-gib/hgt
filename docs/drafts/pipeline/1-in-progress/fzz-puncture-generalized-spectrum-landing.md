# FZZ puncture generalized-spectrum landing

- **ID:** FZZ-P-GSL
- **Stage:** 1-in-progress
- **Type:** CONJECTURE / OPEN CORE
- **Parent:** FZZ-P in `rh-current-frontier-map.md`
- **Target:** source-derived generalized spectral occurrence plus coefficient-faithful Mellin landing

## Closed input

- Protected charge Jost sectors are all-pass on physical real momentum; individual zeros/poles do
  not carry Xi divisor.
- Charge-summed continuum delay is exact Bose kernel; Mellin transform is `Γ(s)ζ(s)`.
- Every physical integer Mellin moment equals normalized all-order Schwarzschild dressed-log jet;
  finite-state recurrence closure is impossible.
- Divisor-only real-energy completeness is exactly RH-strength.
- Standard self-adjoint `L²` dilation has empty point spectrum; ordinary normalizable point-mode
  completeness is unconditionally false.

## Frozen survivor

Viable carrier must be one of:

1. generalized eigenstate/resonance in source-derived rigged spectral triple;
2. singular boundary/domain extension created by puncture and winding condensate;
3. genuinely interacting nonstandard dilation operator with coefficient-faithful source map.

It must not define states from Xi zeros. Source construction must precede divisor landing.

## Open proof burden

1. Construct carrier from exact FZZ/GFZZ winding-condensate or puncture equations.
2. Prove generalized spectral transform contains collective delay Mellin functional with exact
   coefficients and analytic continuation.
3. Establish dynamical support/orientation law forcing every nontrivial divisor zero into real
   energy parameter without assuming RH-equivalent completeness.
4. Audit multiplicity, generalized-state topology, and reflection covariance.

## Next conjecture loop

Test whether any finite-rank, trace-class, or regular boundary perturbation of standard dilation
can convert collective Mellin zeros into point spectrum. On failure, extract exact minimal
singularity/noncompactness required of puncture interaction.

## No-go closure

- **Latest killing theorem:** `not_FZZPunctureL2DilationComplete`.
- **Positive survivor:** continuous standard dilation spectral resolution plus mandatory
  generalized/singular/interacting replacement.
- **Status:** active; no source-derived coefficient-faithful generalized landing yet.

## Regular rank-one delta

Target-adapted unit-box form factor `v_E=1_(E,E+1)` cannot create embedded mode. Every rank-one
eigen-equation `(x-E)f+alpha v_E=0` with `f∈L²` forces `alpha=0` and `f=0` almost everywhere,
because nonzero `alpha` creates nonintegrable inverse-square pole. Completeness by these modes is
unconditionally false.

Sharp survivor is first-order nodal factor `w_E=(x-E)v_E`: explicit state `g_E=-v_E` is nonzero
in `L²` and solves `(x-E)g_E+w_E=0`. Therefore minimal regular occurrence datum is not “rank-one
mixing” but a source-derived node at target energy. Nodes fitted to Xi copies are circular.

Formal module: `FZZCigarPunctureBoxRankOneNoGo.lean`.

### Updated next conjecture loop

Classify finite-channel equation. Determine whether all regular embedded modes require collective
linear combination of source form factors to vanish at target, and whether FZZ charge/winding
coefficients can produce such node without using divisor locations.

- **Latest killing theorem:** `not_FZZPunctureBoxRankOneComplete`.
- **Strongest survivor:** exact nodal pole cancellation with nonzero `L²` formal state.
- 2026-08-27 — regular rank-one occurrence closed; collective nodal source law becomes open core.

## Finite affine-channel classification delta

For arbitrary finite complex channels with local germs

`vᵢ(x)=(cᵢ+(x-E)dᵢ)1_(E,E+1)(x)`,

all mixing collapses exactly to collective value `C=Σᵢaᵢcᵢ` and transverse jet
`D=Σᵢaᵢdᵢ`. A nonzero embedded `L²` mode exists iff `C=0` and `D≠0`; every state is uniquely
`-D1_(E,E+1)` almost everywhere.

This closes finite-channel local occurrence completely. Unit nodal channel realizes mode at every
real energy, so local nodal engineering is nonselective. Live producer must derive global
coefficient-faithful law `C(E)=0`, `D(E)≠0` at exactly divisor ordinates before selecting any zero.

Formal module: `FZZCigarPunctureAffineChannelClassification.lean`.

### Updated next conjecture loop

Test globally fixed finite source families. In particular, determine whether finite
exponential-polynomial/finite-oscillator collective on-shell amplitudes have too-small zero density
to vanish on full FZZ Mellin divisor. On failure, extract exact infinite-channel/order-growth
requirement and formalize it.

- **Latest classification:** `fzzPunctureAffineChannelPointMode_iff`.
- **Strongest survivor:** source-derived collective simple node with nonzero transverse jet.
- 2026-08-27 — finite affine-channel occurrence solved exactly; global coefficient dynamics becomes
  open core.
