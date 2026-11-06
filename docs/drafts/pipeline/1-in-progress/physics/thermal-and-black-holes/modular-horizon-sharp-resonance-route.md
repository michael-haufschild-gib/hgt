# Sharp resonance boundary of the modular horizon

- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Statement:** The normalized modular-horizon response is analytic above the sharp damping line exactly when RH holds. A source-derived bound must establish this analyticity independently of zero locations.

## Exact source

For radial decay `D`, the response is `S_D(ω) = XiC(z+i)/XiC(z)`,
`z = -2ω-2iD-i/2`. Its unnormalized version is the retarded transform of the
totient echo train in `TheEchoTrainOfTheCusp.lean`. Nontrivial zeros produce
frequencies `-γ/2-i(D+(1-β)/2)`.

## Mathematical obligations

1. Classify analyticity and poles at every frequency; retain every zero and multiplicity.
2. Show a concrete nonvanishing Gaussian probe preserves the pole obstruction.
3. Use functional-equation pairs to replace equal damping by a one-sided sharp lower bound.
4. Separate unconditional stability from the sharp bound; identify the exact positive invariant
   retained by reflected pairs.
5. Obtain the sharp bound from the totient echo source or geometric wave dynamics.

## Boundary conditions

The AdS realization uses the modular Eisenstein channel, or its deck-invariant lift to a smooth
congruence cover. A standard Dirichlet quantum Mixmaster billiard selects odd Maaß cusp forms and
excludes this channel. A cosmological realization needs a justified even boundary sector.

## Open core

No source-derived quarter-line estimate is known here. Positivity of the undamped echo train,
causality, and ordinary mode stability do not establish that estimate.

The concrete time-domain target is the Gaussian observation
`G_σ(t) = ∫ exp(-σ(t-u)²) K(u) du`, with its pole-at-one mean removed:

`R_σ(t) = G_σ(t) - (3/π) sqrt(π/σ) exp(1/(16σ)) exp(t/2)`.

The desired estimate is `R_σ(t) = O_ε(exp((-1/4+ε)t))` as `t → +∞`, for a fixed `σ > 0`
and every `ε > 0`. Both the source estimate and its full time-domain equivalence to the sharp
analytic criterion require proof. The exact source, its smoothing, and the spectral probe must
not be replaced by a chosen zero distribution. Gaussian pulses are bilateral; no compact causal
support is asserted.

Existing full-field packet and contour work remains in `modular-horizon-full-field-ringdown.md`.

## Pointwise obstruction and positive replacement

The raw target `K(t)-A exp(t/2) ≤ B exp(bt)` eventually, uniformly in time, fails for every
`A,B,b`: at each positive denominator `c`, the right-hand echo dominates
`(ϕ(c)/c) v^(-1/2)` at `t=2 log c+v`. Echo delays are unbounded.

The replacement is Gaussian observation. Its source integral is absolutely convergent and admits
an exponential majorant from every Laplace weight `a>1/2`. Its spectral multiplier has no zeros,
so smoothing preserves every resonance and its multiplicity. Lean verification is pending.

The source-to-observation transform to verify, for `Re w>1/2`, is

`∫ exp(-wt) G_σ(t) dt = (π/σ)^(1/2) exp(w²/(4σ)) Λ(2w)/Λ(2w+1)`.

Exponential weighting converts the observation into a convolution of two integrable functions.
The mean term follows from the exact identity
`∫ exp(-σ(t-u)²) exp(bu) du = sqrt(π/σ) exp(bt+b²/(4σ))`.
These bridges retain the original totient source; no spectral source is substituted.

The positive invariant behind the sharp threshold is
`rate(q)+rate(reflect q)=2(D+1/4)`, with slower rate
`D+1/4-|Im z(q)|/2`. A one-sided lower bound therefore already forces RH.

## Verification

Pending implementation and kernel dependency audit. No claim of an RH proof or novelty.
