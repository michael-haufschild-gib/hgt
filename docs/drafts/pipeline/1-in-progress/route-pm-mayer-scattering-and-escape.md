# PM: Mayer scattering and energy escape

- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** [PM tasks](../../../reports/review-0111/route-PM.md), [current frontier](../../../reports/rh-current-frontier-map.md#pm).

## Required conclusions

| Task | Required mathematical result | Status |
|---|---|---|
| Mayer 1 | Exact Mayer–Selberg product, oriented/unoriented multiplicities, geometric lengths, and scattering normalization | Genuine closed-geodesic bijection, least lengths, reversal multiplicities, Selberg Euler product and independent scattering/cofactor normalization certified |
| Mayer 2 | Faithful equivalence between actual right-strip zeta zeros and scattering-sector eigenvalue events | Exact finite relative multiplicity, explicit observable remainder +1 eigenfunctions at strip zeta zeros, and faithful full constant-input inverse poles certified; full eigenspace classification remains open |
| Mayer 3 | Actual Hermitian structure including scattering, recovering a classical zero-free region from transfer positivity | Actual boundary positivity recovers width `1/(1000 log abs(t))` for `abs(t)≥4`; form on all eigenfunctions remains open |
| Mayer 4 | Separation of cusp events from scattering events by that form | Open |
| Mayer 5 | Quantitative scattering-sector spectral gap yielding a fixed zero-free strip | Open |
| Mayer 6 | Exclusion of all off-line resonances through partner saturation | Open; RH-complete |
| Escape a | Divergent actual receiver energy produces two-prime Euler laws modulo finite energy | Open |
| Escape b | Positive gauge mass for an actual escape state at some damping below one half | Open |
| Escape c | Exterior tightness excluding escape to infinite height | Open |
| Escape d | Cofinal complete-energy bounds, equivalently visibility of every actual subcritical cofactor limit | Open; RH-complete |

## Certified primitive-orbit product

The [actual primitive-orbit Euler product](../3-formalized/gauss-mayer-primitive-orbit-product.md)
is absolutely convergent near `z=0` for `Re w>1`, and throughout `|z|≤1`
for `Re w>2`, including `z=1`:

```text
D(w,z)D(w,−z) = ∏_c ∏_(m≥0) (1−z^(2ℓ(c)) λ_c^(−w−2m)).
```

The joint product has the same value and summable absolute deviations from
one. The [actual translation length](../3-formalized/gauss-mayer-hyperbolic-translation-length.md)
is the attained displacement minimum `L_c=2 log λ_c`, so each factor is
`1−z^(2ℓ(c)) exp(−(w/2+m)L_c)`. The certified
[inverse-orientation multiplicities](../3-formalized/gauss-mayer-inverse-orientation-multiplicities.md)
regroup these factors with exponent one for self-inverse classes and two
otherwise. The [closed-geodesic identification](../3-formalized/gauss-mayer-closed-geodesic-correspondence.md)
is now certified through the independently defined periodic modular flow.
Its least return times are the actual lengths, and its geometric reversal
fibers give the exact product multiplicities. Thus `D(w,1)D(w,−1)` is the
geometric Selberg Euler product at `s=w/2` for `Re w>2`.
The [actual scattering comparison](../3-formalized/gauss-mayer-primitive-cone-scattering-divisor.md)
now identifies the genuine level-one Poincaré constant coefficient with
`−π^(1/2)Γ((w−1)/2)B(w,1)/(2Γ(w/2)D(w,1))` for `Re w>2`.
The cofactor identity `2ζ(w−1)D+ζ(w)B=0` continues throughout `Re w>0`,
excluding `w=1,2`. Its interpretation as the
[actual boundary inverse entry](../3-formalized/gauss-mayer-actual-boundary-resolvent.md)
is certified, including exact pole multiplicity. The exact finite relation `ord D=ord B+ord ζ`
and actual `R(w)f=f` eigenfunctions at every strip zeta zero are certified. The
[actual remainder boundary inverse](../3-formalized/gauss-mayer-remainder-boundary-feedback.md)
has exact pole order `−ord ζ−ord(1+2ζ(·−1))`. Restoring the latter factor
gives faithful zeta-zero detection. An
[explicit observable eigenfunction](../3-formalized/gauss-mayer-holomorphic-scattering-state.md)
is now certified: the continued lattice state satisfies `(I−L_w)H_w=ζ(w)1`
and `H_w(0)=2ζ(w−1)`, so its evaluation is nonzero at every strip zeta zero. The
[actual period identities](../3-formalized/gauss-mayer-scattering-period-relations.md)
now give inversion reciprocity and the three-term Lewis relation on the
real period segment, throughout `Re w>0`, `w≠2`. The
[actual boundary positivity argument](../3-formalized/gauss-mayer-boundary-positivity-zero-free-region.md)
certifies a classical logarithmic zero-free region from the nonnegative
coefficients `Λ(n)(1−1/n)` of the shifted inverse entry’s logarithmic derivative. The
[full vector channel](../3-formalized/gauss-mayer-vector-scattering-channel.md)
has germ `C(w)/(ζ(w)(w−2))` with `C` holomorphic and nowhere zero on
`Re w>0`. Thus common Fredholm zeros create no additional constant-input
vector poles; the source points have orders `+1` at one and `−1` at two.
The [signed-channel classification](../3-formalized/gauss-mayer-signed-scattering-channel.md)
proves that the negative constant-input germ is everywhere regular and
nonzero on the source half-plane; its full operator residue at one
annihilates the constant input.
The [period Mellin transform](../3-formalized/gauss-mayer-period-mellin-intertwining.md)
identifies the actual axis-subtracted lattice cone with multiplicative
convolution and certifies its two-zeta Gamma product in the absolute
chamber. The [actual Epstein-to-Mayer transform](../3-formalized/gauss-mayer-quadratic-averaging.md)
maps the independently Poisson-defined rectangular field to the actual
period by an absolutely convergent Cauchy integral for `Re w>2`, retaining
both axes and all quadrant multiplicities. The
[continued identity](../3-formalized/gauss-mayer-epstein-continuation.md)
holds on `Re w>0`, `w≠2`, including `w=1`, with absolute convergence and
holomorphic parameter dependence. The
[exact Cauchy Mellin multiplier](../3-formalized/gauss-mayer-cauchy-mellin-symbol.md)
is nonvanishing throughout its convergence strip, preserves both unit
moments on the full source half-plane, and is strictly positive on the
central line for real positive parameters. Its
[strict real-parameter contraction](../3-formalized/gauss-mayer-real-cauchy-contraction.md)
has an explicit frequency-uniform Gamma bound below one, with the deficit
given by a strictly positive squared-energy integral.
[Uniform complex contraction fails](../5-failed/gauss-mayer-complex-cauchy-contraction.md):
the exact Gamma boundary law gives actual amplifying central Mellin
integrals at arbitrarily small positive real parts. The
[sharp high-frequency limit](../3-formalized/gauss-mayer-cauchy-high-frequency.md)
is `2^((1−σ)/2)`, independently of the fixed real Mellin weight, so every
fixed `0<σ<1` eventually amplifies. The
[sharp global central envelope](../3-formalized/gauss-mayer-normalized-cauchy-schur.md)
is strictly `2^((1−Re w)/2)`, with that exact supremum over spectral
heights. The
[exact frequency maximum](../3-formalized/gauss-mayer-cauchy-frequency-maximum.md)
is attained at `u=w/2`; every frequency on `Re u=Re w/2` lies below
that sharp envelope and is strictly contractive when `Re w≥1`.
The [actual Eisenstein lift](../3-formalized/gauss-mayer-actual-eisenstein-lift.md)
identifies the independently defined geometric Fourier model with the
Epstein input and its genuine Mayer image on `Re w>0`, `Im w>0`,
including zeta zeros. Its Gamma and height normalization retains the
source of the existing Maass–Selberg pairing. The
[scattering-subtracted core](../3-formalized/gauss-mayer-finite-energy-scattering-core.md)
has finite central-weight square energy for `0<Re w<2`, `Im w>0`.
Its actual Cauchy image retains the exact scattering coefficient
`2ζ(w−1)/(w−1)`; this correction survives at zeta zeros. Its
[charge-recovery law](../3-formalized/gauss-mayer-scattering-core-charge.md)
gives `a F_w(a)→−Λ(w−1)/Γ_R(w)≠0` at every strip zeta zero, so the
canonical core has strictly positive finite weighted energy. The
[actual logarithmic Cauchy operator](../3-formalized/gauss-mayer-cauchy-l2-operator.md)
is injective on `L²`. Its [sharp operator norm](../3-formalized/gauss-mayer-cauchy-sharp-operator.md)
equals the central Gamma multiplier modulus. Strict contraction at every
spectral height holds exactly for `Re w≥1`; every smaller
positive abscissa admits amplified actual `L²` fields at all large heights.
A height-independent contraction gap exists exactly for `Re w>1`.
Its [exact spectrum](../3-formalized/gauss-mayer-cauchy-continuous-spectrum.md)
is the Gamma multiplier curve together with zero. No nonzero `L²`
eigenvector exists at any eigenvalue, and no bounded inverse exists.
Its literal Cauchy image of the canonical core has finite weighted energy
at most `|m(w,w/2)|²` times the input energy. The
[actual theta factorization and Mellin spectrum](../3-formalized/gauss-mayer-theta-core-mellin.md)
identify the core with a convergent Gaussian-ray correlation and give
`M F_w(u)=Γ(u/2)Γ((w−u)/2)ζ(u)ζ(w−u)/Γ(w/2)` whenever
`Im w>0`, `0<Re u<1`, and `0<Re(w−u)<1`, with absolute convergence.
The [exact core Mellin strips](../3-formalized/gauss-mayer-zero-mellin-strip.md)
are `(0,Re w)` away from zeta zeros and `(Re w−1,1)` at zeros, for
`0<Re w<1`, `Im w>0`. Absolute convergence at `u=0` detects exactly
those zeros; both moments `u=0,w` equal `ζ′(w)`.
Full eigenspace classification and a Hermitian form remain open.

## Operator convention

`MayerFredholm.determinant_eq_zero_iff_eigenvector` concerns the full actual
operator `MayerCutoff.regularized = ζ(w)P + remainderSum`, with eigenvalue
`z⁻¹`. It does not identify the spectrum of the holomorphic remainder alone.
The faithful scattering comparison must preserve this distinction.

`SelbergEisensteinCriticalLine.phiExt` continues the actual constant-term
entry `phiσ` by finite sums of reciprocal Dirichlet L-functions, with equality
on `Re s>1/2`. The independent level-one completed Poincaré constant term is
also certified in `ThetaCuspHawkingBMEisensteinActualZeroFourierCoefficient`:
its two coefficients are `Λ(2s)` and `Λ(2s−1)`. These source results supply
the independently certified scattering/cofactor normalization above.

## Escape receiver boundary

`exists_tendsto_normGram_of_dominant_split` consumes an actual power-row
decomposition with a subdominant remainder; it does not construct that
decomposition from energy divergence. The exact visibility criterion
`riemannHypothesis_iff_forall_gaugeMass_pos` requires every actual cofactor
limit at every subcritical damping. Existence of limits or the conditional
zero-mass law under power growth does not supply positive gauge mass.

## Integrity and placement

No missing source identity, summability bound, positivity, or spectral gap may
be introduced as a premise. Inverse classes retain the proved integral
conjugacy criterion; no extra unoriented quotient is imposed silently.
Gauss–Mayer results belong in `RenormalizedIntersectionTheory`.
Route-specific results without another clear mathematical owner belong in
`RHTower/routePM/`.
