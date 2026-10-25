# Uniform Vaughan residual power rates are fixed strips

- **ID:** uniform-vaughan-residual-power-rates-are-fixed-strips
- **Stage:** 2-fully-proven
- **Type:** CLAIM (Lean verification pending)
- **Verification:** UNPROVED. The argument below is not a certified result until its Lean proof and transitive axiom audit pass; checked component lemmas are identified separately.
- **Source:** uniform-second-scale-vaughan-gram-at-all-cutoffs.md
- **Statement:** At any fixed `0<ε<1/2`, a fixed power rate in the uniform second-scale centered Vaughan Gram law is equivalent to `zetaZeroAbscissa<1`.
- **Novelty status:** Exact specialization of the Vaughan pieces plus the uniform hyperbola proof. No external novelty claim.

## Exact harmonic invariant at an extreme cutoff

Write `ρ=Re(1/ζ(1+ε))>0`, `Z=1/ρ`, `β=1-2ε`,
`c=subHalfZetaCoeff(ε)≠0`, and `H_N=Σ_(d≤N)μ(d)/d`.
For the centered Gram define

`R_ij(T;U,V)=G^c_ij(T;U,V)/T^β
  - c² H_U² H_V² s_i s_j/β`, where `s=(0,0,-1,1,0)`.

At cutoffs `U=1,V=T`, throughout `1≤n≤T` the first small piece is `n`, and
the small-small piece is `-n`. The latter follows from `μ⋆1=δ`:

`Σ_(b k=d) μ(b) (bk)^(-ε) = d^(-ε) Σ_(b|d)μ(b)`.

Every divisor `b≤n` is included because `V=T≥n`. The both-large piece vanishes,
since `(U+1)(V+1)>T`. With `F_T=ρ-A_T`, their centered forms are therefore

`p_2^c(n)=-ZF_T n`,
`p_3^c(n)=-Z(ρ-1)F_T n=(ρ-1)p_2^c(n)`.

Consequently, for every `T≥1`,

`R_23(T;1,T)-(ρ-1)R_22(T;1,T) = ρ c² H_T²/β`.                 (1)

This is an exact finite identity. It detects the arithmetic harmonic sum in the
error left after removing both the linear mean and the universal smooth Gram term.
In particular the two errors cannot both vanish, since the checked terminal-prime
valuation theorem gives `H_T≠0`.

The corpus's `frequent_harmonic_energy_floor` gives a constant `a>0` with
`T H_T²≥a` cofinally often. Thus the contrast in (1), multiplied by `T`, exceeds
`ρ c² a/β>0` cofinally often. In particular the two residual errors cannot both
be `o(1/T)`. Any uniform power-error estimate with exponent greater than one is
unconditionally excluded. This positive cofinal floor is stronger than finite
nonvanishing and follows from the existing critical harmonic-energy obstruction.

## A uniform power rate forces a strip

Suppose some `δ>0` and `C` give

`∀ U,V, max_(i,j)|R_ij(T;U,V)|≤C T^(-δ)`

for all sufficiently large `T`. Equation (1) gives `H_T²=O(T^(-δ))`, hence
`H_T=O(T^(-δ/2))`. Choose `0<η<min(δ/2,1)`. The finite Abel identity

`M(N)=N H_N-Σ_(k=1)^(N-1)H_k`

then implies `M(N)=O(N^(1-η))`, after absorbing the finite initial range.
The corpus's exact Mertens-rate criterion yields `zetaZeroAbscissa<1`.
Only the two entries `(2,3)` and `(2,2)` at the explicit cutoffs `(1,T)` are needed.

## A strip supplies a uniform power rate

Conversely, the existing fixed-strip criterion supplies `0<η<1` and
`|M(x)|≤C x^(1-η)`. Finite Abel summation and `H_x→0` give
`|H_x|≤C' x^(-η)`.

Repeat the uniform convolution proof from the source card with these power bounds.
The single-truncation floor mean has error `O(y^(1-η/4))`, uniformly in its cutoff:
below `√y` use the rounding bound `√y`; above it use the Mertens tail expansion,
absorbing its logarithm. In the small-cutoff case `min(U,V)≤x^(1/4)`, the second
convolution loses a harmonic factor while all arguments are at least `x^(3/4)/2`.
In the large-cutoff case its exact remainder loses at most `(1+log x)^2` against
`x^(-η/4)`. Both give, after enlarging constants,

`|Σ_(d≤x)a_(U,V)(d)-xH_UH_V|≤C'' x^(1-κ)`, with `κ=η/8`,

uniformly in `U,V`. Zero cutoffs cause no exception.

For `r_(U,V)=a_(U,V)-H_UH_V`, take `D=floor(n^a)` in the generalized
hyperbola bound, where

`a=(ε+κ/2)/(ε+κ)∈(0,1)`.

The head divided by `n^(1-ε)` is
`O(n^(-(1-a)(1-ε))(log n)^4)`, and the tail is `O(n^(-κ/2))`.
Both give a fixed positive power saving. The same argument applies to the truncated
small legs and the actual receiver. Restrict the saving further, if necessary, so
`0<2γ<β`; pronic summation then gives normalized norm error `O(T^(-γ))`.
The unit-pattern and pole remainders have bounded pronic norms, hence power-decaying normalized norms.
The smooth-power energy has normalized error `O(T^(-β))`. Cauchy–Schwarz now gives
a fixed power rate for every normalized centered Gram error, uniformly in both cutoffs.

## Positive survivor and scope

The exact invariant (1) is unconditional. The uniform logarithmic Gram law is an unconditional target on the source card;
its complete Lean verification remains pending. The equivalence identifies the precise
additional content of replacing its logarithmic rate by a power rate; it proves
neither a strip nor impossibility of a strip. Full Q-I remains open.

## Lean status

Paper proof dependency-closed. Lean formalization pending. Required finite ingredients
are the existing weighted Vaughan identity, Möbius divisor inversion, reciprocal
mean factorization, and finite Abel summation. The generic divisor-square hyperbola estimate is checked in
`HyperbolaCancellationWithDivisorBoundedCoefficients.lean`; its logarithmic
transfer is checked in `LogarithmicCancellationSurvivesTheDampedFloorTransform.lean`.
The exact extreme-cutoff identities, strict positivity, cofinal floor, and reciprocal
little-o obstruction, and harmonic-power transfer to Mertens sums are drafted as twelve
audit targets in `/tmp/QIExtremeCutoffTools.lean`.
The twelfth states the paper's explicit eventual exponent-above-one obstruction
for the two convolution entries, deriving it from their reciprocal little-o obstruction.
The source statements in `BaezDuarteMobiusCriticalTailObstruction.lean` have been read;
their new specialization has not yet been compiled.

The undamped uniform power step now has a four-target Lean draft in
`/tmp/QIUniformVaughanPowerTools.lean`, including every gain strictly below
`η/(2+η)` and the exact power/fixed-strip equivalence. Its forward harmonic
input has a two-target draft in `/tmp/QIMertensHarmonicPowerTools.lean`.
Neither draft is checked. The divisor-square damped power transfer now has
a three-target draft in `/tmp/QIDivisorSquarePowerTransferTools.lean`, planned as
`PowerCancellationSurvivesTheDampedFloorTransform.lean`. It targets every prefix
gain `0<γ<κ(1-ε)/(1+κ)`, together with its pronic norm transfer when `ε+γ<1/2`.
The actual receiver transfer has four further drafts in
`/tmp/QIVaughanPowerReceiverTools.lean`: common truncated partial sums, bounded
pattern power norms, convolution fluctuation power norms, and one common gain
for all three actual fluctuating sources under a fixed strip. These are unchecked.
The complete assembly now has four proof drafts in
`/tmp/QIVaughanGramPowerTools.lean`, planned as
`UniformVaughanResidualPowerRatesAreFixedStrips.lean`: all five norm rates, the
full residual Gram power rate from a strip, the converse using only the two
extreme-cutoff entries, and the exact full-matrix equivalence. All remain
unproved pending Lean checks and transitive axiom audits.

The pole entry imposes a stronger rate cap on the full matrix: its smooth coefficient
is zero and its centered energy tends to a strictly positive constant. Hence a full
matrix power exponent cannot exceed `1-2ε`. The separate exponent-one contrast remains
useful for the convolution block. The positive finite-energy invariant and its complete
paper proof are recorded in `the-centred-vaughan-pole-has-positive-finite-energy.md`;
its seven-target Lean draft is unverified.

## Quantitative damped transfer awaiting Lean verification

For common partial-sum bounds `B x^(1-κ)`, set `a=1/(1+κ)` and
`D=floor(n^a)`. The checked hyperbola estimate has head at most
`C D^(1-ε)(1+log D)^4` and tail at most
`(13/ε)B n D^(-(κ+ε))`. Since `n^a/2≤D≤n^a`, both polynomial
exponents are `a(1-ε)=1-ε-κ(1-ε)/(1+κ)`. Absorb the fourth logarithm
into any strict loss from that gain. One constant and threshold work for
the whole coefficient family. A global resulting prefix bound gives
pronic norm at most
`K sqrt(1+1/(1-2(ε+γ))) sqrt(T^(1-2(ε+γ)))`.
These are precise formalization obligations, not checked results.
