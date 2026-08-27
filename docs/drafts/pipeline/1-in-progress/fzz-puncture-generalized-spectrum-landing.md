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

## Finite exponential-type density attempt

C9 tested whether any nonzero fixed finite-exponential-type source can vanish at all simple critical
ordinates. Corpus theorem
`exists_xiSimpleCriticalZeroCount_linear_of_cofinite_exponentialType_zeros` forces a linear envelope
on simple-critical-zero count under that vanishing. Current unconditional Lean census is only
logarithmic, so it does not contradict linear growth. A superlinear simple-critical census is open.

**Result:** conjecture failed as unconditional route closure; no theorem promoted. It remains a
conditional diagnostic, not an RH advance.

## Sharp fractional nodal threshold delta

For target-centered source `v_α(x)=x^α1_(0,1)(x)`, every continuum solution of
`xf+v_α=0` equals `-x^(α-1)1_(0,1)` almost everywhere. A nonzero embedded `L²` mode exists exactly
when `α>1/2`. Borderline `α=1/2` fails; strict fractional node `α=3/4` succeeds.

This corrects prior language: first order is sufficient but not sharp. Exact local occurrence burden
is source vanishing order strictly above one half. Any such exponent works in every target-centered
chart, so local regularity remains nonselective.

Formal module: `FZZCigarPunctureFractionalNodalThreshold.lean`.

### Updated next conjecture loop

Classify logarithmically corrected critical germs
`x^(1/2)(log(1/x))^(-β)`. Determine exact endpoint `β` threshold and whether literal FZZ/GFZZ
winding source has enough regularity. Then test global source law rather than another fitted node.

- **Latest classification:** `fzzPunctureFractionalPointMode_iff`.
- **Strongest survivor:** source-derived node of local order strictly greater than `1/2`.
- **Sharp excluded wall:** pure square-root and weaker nodes.
- 2026-08-27 — fractional occurrence wall solved exactly; logarithmic critical refinement and
  global coefficient dynamics remain open.

## Critical logarithmic nodal threshold delta

At pure-power wall `α=1/2`, source

`v_β(x)=x^(1/2)(1-log x)^(-β)1_(0,1)(x)`

has unique formal state `-x^(-1/2)(1-log x)^(-β)1_(0,1)`. It is a nonzero `L²` mode exactly when
`β>1/2`. Change `x=e^(-u)` converts energy to `(1+u)^(-2β)`, so double-critical `β=1/2` fails
and `β=3/4` succeeds.

This refines local burden from power order to exact weighted condition: source divided by spectral
distance must lie in `L²`. Critical power can survive with strong slowly-varying damping, but remains
nonselective across target charts.

Formal module: `FZZCigarPunctureCriticalLogNodalThreshold.lean`.

### Updated next conjecture loop

Leave fitted local germ ladder. Extract universal weighted criterion for arbitrary measurable source:
nonzero point mode iff `v(x)/x∈L²` and source is nonzero modulo null sets, with unique state. Then
apply criterion to literal FZZ/GFZZ source candidate from corpus; if unavailable, identify exact
coefficient-faithful object still missing.

- **Latest classification:** `fzzPunctureCriticalLogPointMode_iff`.
- **Strongest survivor:** source-derived collective germ with `v/x∈L²`, including critical
  square-root plus `β>1/2` log damping.
- **Sharp excluded wall:** power-log pair `(α,β)=(1/2,1/2)` and weaker lexicographic decay.
- 2026-08-27 — critical logarithmic wall solved; universal weighted source law becomes next core.
