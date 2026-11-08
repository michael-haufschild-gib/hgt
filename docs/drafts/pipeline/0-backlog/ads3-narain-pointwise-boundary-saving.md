# Arithmetic boundary saving at every Narain target pair

- **ID:** W11-NP
- **Stage:** 0-backlog
- **Type:** CANDIDATE
- **Source:** [Averaged quantitative saving](../3-formalized/ads3-narain-quantitative-boundary-saving.md)

## Conjecture

For every actual target pair `(ρ,σ)`, set
`R_(ρ,σ)(y)=yH_(ρ,σ)(y)+(3/π)log y−B_(ρ,σ)` and `L=log(1/y)`,
with `B=narainScalarConstant`. There are `C,c>0` such that

`|R_(ρ,σ)(y)|≤C√y exp(−cL/[(log L)^(2/3)(log log L)^(5/3)])`

for all sufficiently small positive `y`. Including the vacuum adds
`y` to both the scalar observable and its prescribed main term, leaving
this remainder unchanged.

**Uniform refinement.** For fixed positive heights `Y,Z`, the same `C,c`
and small-height threshold should work for all horizontal target coordinates
`ρ=x+iY`, `σ=w+iZ`. The sharp Fourier-tail envelope is already uniform
in `x,w`. The additional obligation is uniform control of the filled
quotients near their removable center. The exact algebraic candidate

`D_(x,Y)(u)=D_Y(u)+2(2u−1)(1+2u)eisTail(u,x,Y)`

removes that obligation without a spectral Cauchy estimate: `D` denotes
the entire filled numerator divided by `u`. The Fourier tail already
contains `2u` before division. Away from zero the identity is algebraic;
differentiating `uD_(x,Y)=u[D_Y+2(2u−1)(1+2u)eisTail]` at zero
extends it to the center. The sharp tail bound is uniform in `x` at
all ordinates, while the entire `D_Y` is bounded on compact spectral
sets. This gives a concrete uniform compact-bound mechanism. The
divided identity and its bound remain unformalized.

## Corpus mechanism

`filledEisensteinNumerator` equals the filled horocycle constant term
plus `(2u−1)(1+2u)(2u)eisTail(u,x,Y)`.
The mean numerator strip bound is proved. The corpus's
`BlackHoleRingdown.exists_weightedTail_jets_le_sharp` supplies the
exponential envelope for the Fourier tail. Thus the full filled numerator
should retain `C(1+|t|)^N exp(−π|t|/2)`. The exact pointwise quotient
then has the same reciprocal-zeta loss as the averaged transform.

`NarainCentralZero` already removes the central singularity for every
target pair. `NarainPrincipalPart` identifies its universal double pole
and target-dependent constant. `NarainMellin` and `NarainHeatRegularity`
supply the actual Mellin identity, continuity and large-height tail.
The averaged contour construction should therefore extend pointwise:
first the boundary line, then the finite Vinogradov–Korobov rectangle.

Remaining obligations: full numerator strip bound, pointwise weighted
residue, Mellin inversion, contour transport and all tail estimates.
The averaged quantitative chain is itself not yet kernel-checked.
This target gives no exponent above one half and no RH-strength bound.

## Gates

- [ ] 0 → 1: prove and audit the full numerator strip envelope.
- [ ] 1 → 2: dependency-closed actual-source contour argument.
- [ ] 2 → 3: direct Lean checks, axiom audits and umbrella imports.
