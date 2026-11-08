# Central Narain zeros as logarithmic moment sum rules

- **ID:** W11-NJM
- **Stage:** 0-backlog
- **Type:** CANDIDATE
- **Source:** [Central orders](ads3-narain-central-order-classification.md) · [Quantitative saving](../3-formalized/ads3-narain-quantitative-boundary-saving.md)

## Conjecture

For fixed positive target heights, write `A=A_YZ`, `a=3/π`, `B=B_YZ`,
`R(y)=yA(y)+a log y−B`, and `M(u)=narainMellinMean Y Z u`.
Every logarithmic moment below converges absolutely, and for `n≥0`,

`∫₀∞ y^(−3/2)(log y)^n R(y)dy = M^(n)(0)`.

**Boundary-family refinement.** For every real `t` and every `n≥0`,
the same mechanism predicts the absolutely convergent identity

`∫₀∞ y^(−3/2+it)(log y)^n R(y)dy = M^(n)(it)`.

The corpus’s `fourier_real_eq_integral_exp` in
`StripSourceHardyTransfer.lean` fixes the oscillatory kernel exactly.
Evaluating the differentiated Fourier identity at `t/(2π)` cancels
the same `(2πi)^n` factor and gives `∫(−L)^n exp(−itL)H(L)dL`.

The central moments are its specialization at `t=0`. This would identify
the actual Mellin boundary and all its tangential derivatives with source
moments; it does not assert convergence on an open strip to the left of
the boundary. The refinement remains unformalized.

**Right-half-strip refinement.** For `0<Re u<1/2`, the same full-axis
remainder should satisfy the absolutely convergent identity
`∫₀∞ y^(u−3/2)(log y)^n R(y)dy=M^(n)(u)` for every `n`.
At zero height, the proved square-root saving permits `Re u≥0`;
at infinite height, `R(y)=(3/π)log y−B+o(1)` permits `Re u<1/2`.
Cutoff Mellin regularization and the explicit large-height main-term
integrals should identify the transform on this strip. The boundary-family
formula is its continuous tangential limit, but does not by itself prove
the open-strip identity. This refinement remains unformalized.

Thus these moments have first nonzero index `1`, `3` or `5`, according
as zero, one or two target heights equal `Y*=exp(2−4 Re ξ′(1))`.
The zeroth moment always vanishes. The first is
`4√(YZ)[2−4ξ′(1)−log Y][2−4ξ′(1)−log Z]`.

**Leading exceptional moments.** Write `c=2−4ξ′(1)` and
`κ=(logDeriv ξ)''(1)`, real with `κ<0` by the corpus's strict xi
concavity. The central factorization predicts
`μ₃(Y*,Z)=32√(Y*Z)(2−κ)(c−log Z)` and
`μ₅(Y*,Y*)=(2560/3)Y*(2−κ)²>0`.
These exact coefficient laws strengthen the proposed order classification.
In the central factorization `M(u)=u D_Y(u)D_Z(u)U(u)`, `U(0)=4`.
At the exceptional height,
`D(0)=D′(0)=0` and `D″(0)=(8/3)√Y*(2−κ)`.
The third jet has only the derivative allocation `(1,2,0,0)`, with
coefficient `3`; the fifth jet at two exceptional heights has only
`(1,2,2,0)`, with coefficient `30`. These give the displayed constants.
The corpus's `complex_iteratedDeriv_mul_at_add_order` and
`complex_iteratedDeriv_mul_of_left_vanishing_below` in
`ReflectedBiHeatMultiplicityTomography.lean` supply these exact Leibniz
collapses; `complex_iteratedDeriv_mul_eq_zero_before_add_order` supplies
the lower-jet vanishings. Their application and the source-integral
identities remain unformalized.

A further target is at least `1`, `3` or `5` sign changes of the actual
real remainder, respectively. Vanishing moments through degree `k−1`
should exclude fewer than `k` sign changes by polynomial separation.
The stronger [arithmetic oscillation conjecture](ads3-narain-two-sided-oscillation.md)
would give infinitely many sign changes at every height pair; the
height-dependent moment cancellation law remains a separate invariant.

## Fixed-product distinction

Combining the proposed first-moment formula with
`Y=√P exp(v)`, `Z=√P exp(−v)` predicts

`μ₁=4√P[(c−(log P)/2)²−v²]`.

Thus the first central moment can change sign along a fixed-product
family. The [scaling candidate](ads3-narain-average-scaling.md) predicts
that every arithmetic principal coefficient stays fixed on that same
family. Central moments would therefore distinguish the explicit theta
correction even when the arithmetic resonances agree. This joint
consequence remains unformalized; neither moment sign constrains zero
locations by itself.

## Mechanism and boundary

Put `H(L)=exp(L/2)R(exp(−L))` and `G(t)=M(2πit)`.
The proved boundary contour gives `H=FourierInv(G)` with mathlib's
`2π` convention. The proved logarithmic savings give every absolute
moment of `H` at positive infinity. At negative infinity, actual
large-height heat decay gives
`H(L)=exp(L/2)[−aL−B+o(1)]`, so every absolute moment exists there too.
The proved [Schwartz construction](../3-formalized/ads3-narain-boundary-schwartz.md)
supplies all these clock moments directly, using spectral
moments and Landau interpolation without the moment identities below.
Thus `H` and `G` are integrable; continuity of `G` permits pointwise
Fourier inversion, giving `G=Fourier(H)`.
The corpus uses `Continuous.fourier_fourierInv_eq`; its second
integrability premise concerns `Fourier(G)`. Reflection converts the
proved identity `H=FourierInv(G)` into that premise. The inversion
constant and reflection sign must be retained exactly.

Differentiate this Fourier identity using the absolute moments.
The mechanism is already used by `RHTower.deningerFourier_contDiff`
and `deningerFourier_iteratedDeriv_bound` in
`Deninger/DeningerFourierBoundedDerivs.lean`, via
`Real.iteratedFDeriv_fourier`. Mathlib also supplies the scalar formula
`Real.iteratedDeriv_fourier`, requiring integrability of every real-power
weighted source, with no exponential moment assumption. The chain factor `(2πi)^n` cancels the
Fourier differentiation factor and yields

`M^(n)(0)=∫ℝ (−L)^n H(L)dL`.

The substitution `y=exp(−L)` gives the displayed physical moment.
For absolute convergence and the zeroth sum rule, the corpus already
supplies `integrableOn_Ioi_iff_integrable_exp_smul` and
`integral_Ioi_eq_integral_exp_smul` in
`BurnolCoPoissonBerezinFaithful.lean`. Their Jacobian transforms
`y^(−3/2)(log y)^n R(y)` into `u^n H(−u)` under `y=exp u`.
Schwartz moments then give absolute convergence on the full positive
axis, and Fourier inversion at zero gives the vanishing zeroth moment.
These two conclusions need no jet classification.
The corpus's `iteratedDeriv_deningerMeyerStrongLogMellin_eq_integral_jet`
requires decay against every exponential weight. The proved arithmetic
saving does not supply that hypothesis; this boundary argument uses
absolute polynomial moments instead.

No derivatives of `H` are required. The already proved analyticity of
`M` at zero identifies its real-line derivatives with its complex jets;
absolute moments alone are not being used to claim holomorphy of the
integral across the boundary.

The source saving and Schwartz moment domination are proved. The physical
change of variables, Fourier differentiation and exact central-order
classification still need Lean verification.
A sign-change proof from moments alone needs a precise oscillation
definition and a moment-separation theorem; the stronger arithmetic
oscillation theorem would instead supply every finite sign count.
None of these claims supplies an RH-strength rate or cancels an arithmetic pole.

## Gates

- [ ] 0 → 1: audit both clock tails, Fourier differentiation and boundary-jet transport.
- [ ] 1 → 2: actual-source moment identity and sign-change consequences.
- [ ] 2 → 3: direct Lean checks, axiom audits and umbrella imports.
