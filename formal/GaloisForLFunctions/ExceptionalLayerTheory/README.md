# Exceptional-layer theory of ζ

## Motivation

An isolated rightmost layer would make the prime error contain a persistent finite
oscillation above an infinite remainder. Exceptional-layer theory asks how the exact
Euler product and functional equation constrain their coexistence. Its target is the
asymptotic abscissa law (AAL), or a reduction of AAL to the finite-stratum problem B13.
The programme studies the actual infinite divisor of ζ; a finite exponential model is
useful only when its error against that divisor is proved.

Write Θ for the supremum of the real parts of nontrivial zeros, and
Θ∞ = inf{σ ≥ ½ : only finitely many zeros have real part greater than σ}.
AAL means Θ = Θ∞; ZAL means Θ∞ = ½. RH is AAL together with ZAL.
B13 is the implication that finitely many off-line zeros imply none.

## Objects and language

| Object | Meaning |
|---|---|
| Exceptional layer | The finite, nonempty set of zeros at Θ when AAL fails, counted with multiplicity |
| Isolation gap | Θ−Θ₂, where all remaining zeros have real part at most Θ₂<Θ |
| Layer polynomial | T(u)=−∑_{Re ρ=Θ} e^{i Im(ρ)u}/ρ, paired to be real |
| Remainder | The infinite divisor after the specified finite subtraction; its exponent must remain explicit |
| Prime current | Gaussian regularizations of ∑Λ(n)n^(−s), including pole and Gamma corrections when needed |
| Observation scale | The joint choice of height, damping and prime cutoff at which a current is read |
| Resonant tower | Logarithmic observation times kπ/γ for a selected ordinate γ |
| Repulsion | A restriction on the remainder imposed by the layer |
| Replication | New zeros at unbounded heights forced by an exceptional zero |
| Masking | A layer's contribution concealing another contribution in a one-sided observable |

Reflection sends ρ to 1−conj(ρ) at the same height. It does not replicate zeros.
Approximate-depth replication and exact-depth replication are different statements.

## Foundations

The following are inherited corpus results, not new claims of this programme.

| Pillar | Mathematical content | Source |
|---|---|---|
| Isolated-layer structure | Failure of AAL yields a finite isolated top and reflected bottom | `ZeroConfigurationGeometry/AsymptoticAbscissaSpectralGapAndTopAnnihilator.lean` |
| Prime-error expansion | ψ(x)−x=x^Θ T(log x)+O(x^E), with Θ₂<E<Θ; the leading polynomial is rigid | `ZeroConfigurationGeometry/PrimeErrorFiniteOscillationRigidityAndSignChanges.lean` |
| Persistent low jets | A rightmost zero gives a nonzero limiting prime moment despite a vanishing diagonal | `ZeroConfigurationGeometry/FiniteExceptionalLayersForcePersistentLowJets.lean` |
| High-strip subtraction | A finite subtraction controls the Gaussian error uniformly over a high strip | `EulerFETransportTheory/OnlyExceptionalGaussianModesRemain.lean` |
| Arithmetic rigidity | Integrable or square-integrable functional-equation defects in the specified Beurling class force the ordinary primes | `EulerFETransportTheory/README.md` |

Before using a pillar, check its exact Lean statement and transitive axioms. In particular,
uniformity in one parameter does not authorize a diagonal limit in two parameters.

## Exponential observation laws

Write `K(y,w)=½Γ(w/2)y^(−w/2)`, `s=σ+it`, and `y=e^(−at)`.
The Gaussian mode of a fixed zero ρ has exponential rate

    r(ρ,σ,a)=a(Re ρ−σ)/2−π/4.

Polynomial upper bounds for the mode and its reciprocal prove decay for
`r<0` and norm tending to infinity for `r>0`. The equality case is not
settled by these bounds. Under failure of AAL, finite F and `½≤θ<σ<1`
exist such that every omitted zero lies left of θ and, for every `a>0`,

    ΣΛ(n)n^(−s)e^(−yn²) + e^(−y)ζ′/ζ(s)
      − K(y,1−s) + Σ_{ρ∈F}K(y,ρ−s) → 0.

Convergence is uniform in `Re s∈[σ,1]`. The complete infinite complementary
divisor is bounded before taking the limit; no finite truncation replaces it.

The pole at 1 crosses its growth threshold before any member of F.
Consequently, some positive speeds make every retained zero mode vanish
while the literal prime current divided by `K(y,1−s)` tends to 1 and its
norm tends to infinity. This rules out extrapolating inverse-height raw-current
passage to arbitrary exponential observations. It also identifies the pole
subtraction needed before attributing high-current excursions to the layer.

These are the programme's first proved interaction laws:
`TheGaussianObservationBoundary.lean` supplies the mode boundary and
complete finite-part passage; `ThePrimeCurrentAtExponentialScales.lean`
supplies the raw expansion and pole dominance. They establish observation
scales, not repulsion or zero replication.

Above the top-layer boundary, the pole-subtracted current recovers the
actual top ordinates at escaping heights. Let β be the top and
`a(β−σ)>π/2`. Dividing the corrected current by `K(y,β−s)` gives

    [ΣΛ(n)n^(−s)e^(−yn²) + e^(−y)ζ′/ζ(s) − K(y,1−s)] / K(y,β−s)
      + Σ_{Re ρ=β} exp(π Im ρ/4) exp(i Im ρ·(at+log(t/2))/2) → 0.

`TheExceptionalLayerAtEscapingHeights.lean` proves this formula, including
the vertical Gamma quotient and the vanishing ratios of every lower layer.
The phase has a logarithmic correction; its coefficients retain multiplicity
and a Gamma weight. This is a high-height reading of low zeros through the
infinite prime current. It does not locate new zeros at those heights.

The profile has a sharp recurrent envelope
`S=Σ_{Re ρ=β} exp(π Im ρ/4)>0`. Its normalized current is eventually
bounded by `S+ε` and returns within ε of the complex value −S in every
sufficiently late interval of a fixed length. The length may depend on the
layer, speed and tolerance. The corrected unnormalized current consequently
has arbitrarily large excursions above every height.
`TheSharpRecurrentLayerEnvelope.lean` proves these assertions. The bridge
from Bohr recurrence to physical height uses
`φ_a(t)−φ_a(R)≥a(t−R)/2` for `t≥R≥2`.

For a top with one positive ordinate γ, conjugation pairs equal
multiplicities but unequal weights `exp(±πγ/4)`. The reverse triangle
inequality bounds its profile away from zero. Consequently the corrected
current's norm tends to infinity at every supercritical speed, at all
sufficiently large heights. `ASingleTopQuartetCannotCancelItsCurrent.lean`
proves the actual-divisor dichotomy: either two distinct positive top
ordinates exist or this pointwise growth holds. Excluding a quartet still
requires an incompatible arithmetic constraint at the same scale.

`LocalFiltersRecoverTheTopDivisor.lean` removes cancellation for arbitrary
finite top layers using finitely many height probes. In every prescribed
window length `L>0`, small fixed shifts have distinct ordinate nodes
`zγ=exp(iγah/2)`. A polynomial vanishing at unwanted nodes extracts the
selected multiplicity, because `Wγ(t+jh)/Wγ(t)→zγ^j`. Consequently every
sufficiently late interval `[t,t+L]` contains an arbitrarily large corrected
current reading. This strengthens bounded-gap recurrence to every positive
window length; a contradictory arithmetic upper estimate remains missing.

`DampingFiltersReadTheExceptionalDivisor.lean` gives same-height detection
using literal prime sums. Geometric damping changes multiply Mellin modes
by exact exponential characters. A polynomial with roots at the pole and
unwanted exceptional points cancels their modes exactly. The selected-mode
quotient tends to its nonzero multiplicity-weighted polynomial value, so the
filtered prime sum grows at every large height. All damping samples can lie
inside any prescribed positive logarithmic window. The observable has no
continued-zeta term; the continued term appearing in its proof is `O(t)` and
vanishes after normalization. The independent arithmetic bounds below remain
insufficient to contradict this growth.

`ExponentiallyNarrowDampingReadsTheDivisor.lean` permits spacing
`h(t)=exp(−κt)`. For a selected zero `ρ₀`, let
`d=1+#{q∈F : ρq≠ρ₀}` and `r=a(β−σ)/2−π/4`. If `0<dκ<r`, the filtered
prime sum divided by `h(t)^d K(y,ρ₀−s)` tends to
`−mρ₀(ρ₀−1)Π_{ρq≠ρ₀}(ρ₀−ρq)≠0`, and its norm tends to infinity.
The full infinite error is controlled before taking this diagonal limit.
Thus exponentially narrowing damping windows still recover the exceptional
divisor at all large heights. The raw equality boundary remains open.

`ArbitraryDampingContractionReadsTheDivisor.lean` removes the contraction-rate
restriction from normalized recovery: every eventually positive `h(t)→0`
gives the same nonzero quotient limit whenever `r>0`.
`ContourBoundsForFiniteDivisorFilters.lean` shifts the complete Euler integral
to a regular line `σ<c<Re ρ₀`. No Gamma pole is crossed, and the full error is
`O(h^d(1+|t|)^(d+1) exp(at(c−σ)/2))`. Choosing `a(c−σ)/2<r` makes its
normalized value tend to zero independently of the spacing. At
`dκ≥a(1−σ)/2`, raw arithmetic decay therefore coexists with nonzero normalized
divisor recovery. Smallness produced by contraction cannot itself exclude
an exceptional layer.

`EulerBoundsForDampingFilters.lean` proves the independent arithmetic bound
`|A(t)|≤C h^d(1+|t|)^d exp(at(c−σ)/2)` for every `c>max(1,σ)` and
`0≤h≤1`. Absolute Euler convergence and Mellin inversion retain the whole
filter before taking norms. Consequently exponential contraction forces the
literal prime filter to zero when `dκ>a(1−σ)/2`, without a finite-layer
assumption. This decay regime is disjoint from exceptional-layer growth:
the remaining rate gap is `a(1−β)/2+π/4`. A sharper arithmetic estimate
must retain additional cancellation of the prime phases.

`ZeroFreeBoundsForDampingFilters.lean` strengthens the arithmetic estimate to
`|A(t)|≤C_b h^d(1+t)^(d+3) exp(a(1−σ)t/2−bt/log(2t))`, eventually in
`t`, for every fixed `b>0`, uniformly in `0≤h≤1`. The local Mellin contour
uses zeta heights between `t/2` and `3t/2`; the actual zero-free region
supplies the saving, and the horizontal edges and Euler tails decay faster.
Thus the prime filter tends to zero also at `dκ=a(1−σ)/2`, unconditionally.
The subexponential saving still leaves the fixed exceptional-layer rate gap.

`VinogradovKorobovBoundsForDampingFilters.lean` improves this saving to
`a t w(2t+1)/4`, where the corpus proves
`w(T)=(log T)^(−2/3)(log log T)^(−5/3)/10^8`. The uniform bound is
`C h^d(1+t)^(d+5) exp(a(1−σ)t/2−a t w(2t+1)/4)`, without a finite-layer
assumption. Thus even the enlarged spacing
`h(t)=exp((−a(1−σ)/2+a w(2t+1)/8)t/d)` forces raw decay.
The improvement remains subexponential; the fixed gap to a selected
exceptional mode is unchanged.

`ComplexGaussianDamping.lean` changes the damping to
`exp(−at) exp(i(−π/2+1/t))`. The literal rotated prime filter still obeys
`C h^d t^N exp(at(c−σ)/2)` for every `c>max(1,σ)`, uniformly for
`0≤h≤1` and `t≥1`. Complex Mellin inversion retains every filter factor;
rescaling the Mellin height bounds the angular cost polynomially.
The selected kernel mode now grows for every `a(Re ρ−σ)>0`: rotation
removes its fixed `π/4` Gamma penalty.

`RotatedContoursForFiniteDivisorFilters.lean` proves the exact rotated
contour identity and complete remainder `O(h^d t^N exp(at(c−σ)/2))`
on every regular line `σ<c<Re ρ` inside the finite-layer gap.
`BoundaryDampingReadsTheDivisor.lean` consequently recovers the same nonzero
normalized divisor limit for every `a>0` and every eventually positive
`h(t)→0`. For `h=exp(−κt)`, literal prime-filter growth holds throughout
`dκ<a(Re ρ−σ)/2`.
The fixed Gamma penalty is removed from the actual prime-filter theorem;
the positive arithmetic gap `a(1−Re ρ)/2` remains.

`BoundaryZeroFreeContours.lean` and
`VinogradovKorobovBoundsForBoundaryDamping.lean` give the independent bound
`|A_h^rot(t)|≤C h^d t^N exp(a(1−σ)t/2−a t w(t³+1)/4)`, where
`w(T)=(log T)^(−2/3)(log log T)^(−5/3)/10^8`.
Constants and the eventual height threshold are uniform over `0<a≤t/4`
and `0≤h≤1`. A full zero-free rectangle includes bounded zeta heights;
the filter kills the pole and preserves every spacing factor on its boundary.
For fixed positive speed, raw decay holds at `dκ≥a(1−σ)/2`, including
equality, and even for spacing
`exp((−a(1−σ)/2+a w(t³+1)/8)t/d)`.
This subexponential saving leaves the fixed gap to exceptional-layer growth.

`PolynomialDampingReadsTheDivisor.lean` replaces the fixed speed by
`A log(t)/t`, giving exact radius `t^(−A)`. Every sufficiently large `A`
recovers the same nonzero divisor for every positive `h(t)→0`, with
normalized contour error `O(1/t)` independent of spacing. For every `κ>0`,
sufficiently large `A` forces raw prime-filter growth at `h=t^(−κ)`.
Unconditional AAL-or-growth and AAL-or-recovery dichotomies supply actual
finite packets. Each fixed grid sample has `t^(A+1) Re ε_j(t)→1` and
Gaussian envelope `exp(−x²/(2t^(A+1)))`, so its damping scale is polynomial.
The independent upper bound becomes
`C h^d t^N t^(A(1−σ)/2) exp(−A log(t)w(t³+1)/4)`, with `C,N` independent
of `A`. Prime cancellation overcoming the fixed power gap remains unproved.

`TheSharpPolynomialObservationBoundary.lean` gives the exact modulus law
`|h^d Kφ|/t^E→C(x)>0`, where `x=Re ρ−σ`,
`E=((A+1)x−1)/2−dκ` and
`C(x)=sqrt(2π)/2·(1/2)^((x−1)/2)·exp(−1/2)`.
For every eventually positive radius `y(t)`, normalization by
`y^(−x/2)t^((x−1)/2)` gives the same ordinate-independent constant.
Above the proved recovery threshold, the literal prime filter has exponent
`E` and limiting coefficient `|−mρ(ρ−1)Π(ρ−ρq)|C(x)`.
Growth, decay and the positive critical modulus are therefore classified;
critical contraction gives the same modulus for every sufficiently large `A`.
Conversely, for `0<x<1/2`, every radius `y≥1/t` and bounded spacing
`0≤h≤1` force selected-mode decay. The short-scale raw-growth shortcut is
closed; relative estimates against a decaying mode and long-sum cancellation
remain open. This does not improve the independent arithmetic upper bound.

`GaussianVaughanBilinearCancellation.lean` supplies independent arithmetic
cancellation for the actual type-II Vaughan contribution. At damping
`ε=α−iξ`, pairing factors `m₁,m₂` cancels the logarithmic height phase;
the remaining phase has constant curvature `λ=|ξ(m₁²−m₂²)|/π`.
On an interval `[P,Q)` of length `N`, its norm is bounded by
`exp(−α(m₁²+m₂²)P²) min(N,8N sqrt(λ)+12/sqrt(λ))` for nonzero curvature.
The zero-curvature branch is the Gaussian endpoint factor times `N`.
Abel summation retains the damping, and Cauchy–Schwarz gives an explicit
pair-energy bound with the original von Mangoldt/Möbius coefficients and
product cutoff. It holds at every height and every interior rotation.
For `λ≤1/1024` and `48≤N sqrt(λ)`, the correlation bound is at most half
the trivial one. Rotation therefore enables arithmetic cancellation as well
as removing the Gamma penalty.

`GaussianVaughanTypeI.lean` controls the complementary Gaussian type-I
fibres. The phase has positive curvature `ξ/π+t/(2πx²)`, including at its
stationary point. With endpoint curvature ratio `H` and minimum `λ`,
every prefix has bound `min(N,8NH√λ+12/√λ)`; Abel summation retains the
initial damping and abscissa weight. The logarithmic coefficient costs
`2 log(Q−1)`. The bound is at most `N/2` when `H√λ≤1/32` and `N√λ≥48`.
`GaussianVaughanPrimeBlocks.lean` combines both exact type-I coefficient
sums with the square root of the type-II energy to bound a complete literal
von Mangoldt block, including lower-half interior Gaussian rotations.

`NonstationaryGaussianCorrelations.lean` improves quadratic correlations
below the first integer resonance to `2π exp(−vP²)/(|u|P)`. For
`P√λ≥1` and `N√λ≥12`, this is at most one sixth of the previous bound.
`NonstationaryGaussianTypeII.lean` aggregates reciprocal integer gaps on
dyadic rectangles, preserving the product cutoff and Gaussian damping.
`GaussianVaughanDyadicSaving.lean` bounds both actual coefficient energies
using Chebyshev and the divisor second moment. Put `θ=ξD²M²` and
`Wσ=DM D^(−σ) M^(−σ)`. For `σ,α≥0`, `ξ>0`, `D,M≥1`, and
`16ξDM²≤π`, the literal type-II rectangle satisfies

    |S|² ≪ Wσ² log(2D)(1+H_{2M}³) exp(−2αD²M²)
             × [1/M+2π(1+log(2M))/θ].

The constant is independent of all parameters and Vaughan cutoffs.
For `t>0`, `t≤32θ` and `M≥t`, this is at most
`C Wσ² (1+log(2D))(1+log(2M))⁴ exp(−2αD²M²)/t`.
Every rectangle containing a quadratic stationary point satisfies the
scale condition; the first-band and short-factor conditions remain.
Other rectangles, infinite tails, pole cancellation and contracting filter
factors still need control before comparison with the selected divisor signal.

`GaussianMomentsReadTheDivisor.lean` preserves the complete divisor reading
while suppressing small products. Multiplying each sample by `ε_j n²/t`
is exactly `(ε_0/t)` times the original filter at abscissa `σ−2`.
Gamma recurrence multiplies each selected mode by `(ρ−σ−it)/(2t)→−i/2`.
The full polynomial-scale recovery holds on every contracting grid, with
an unconditional AAL-or-nonzero-moment-readings theorem. Boundary dampings
eventually satisfy `0<α≤ξ`, uniformly in every positive radius.

`GaussianMomentDyadicSaving.lean` bounds the actual first-moment Vaughan
rectangle by the previous squared envelope times `C(θ/t)²`. For `θ≤t`,
cutoffs `32t≤πU` and `2t≤V` make all active rectangles satisfy the first-band
and short-factor requirements. Every small-product rectangle then obeys

    |S₁|² ≪ Wσ² (1+log(2D))(1+log(2M))⁴ exp(−2αD²M²) θ/t².

This removes the inverse-θ loss without losing the divisor signal.

`GaussianMomentAllScales.lean` extends the saving to every product scale.
For `σ≥0`, `ξ>0`, `t≥1`, `ξ/(2t)≤α≤ξ`, choose `πU≥128t log t`
and `V≥2t`. Every masked rectangle then satisfies

    |S₁|² ≪ Wσ² (1+log(2D))(1+log(2M))⁴ exp(−αD²M²)/t.

Nonstationary cancellation covers `ξD²M²≤4t log t`; above it, Gaussian
decay absorbs the absolute coefficient-energy bound. Half the squared
Gaussian damping remains. The lower sector condition holds eventually
at the boundary angle, uniformly in every positive radius. Exact dyadic
assembly bounds the actual finite type-II convolution by `sqrt(C/t)`
times the sum of square roots of the retained rectangle envelopes.
`GaussianMomentInfiniteTypeII.lean` removes the type-II truncation and
passes the bound to the absolutely convergent infinite convolution. For
`0≤σ<1` and `X=max(1,sqrt(2/α))`,

    |T₁| ≪σ X^(1−σ) (1+log X)^4 / sqrt(t).

The constant is independent of damping, height, Vaughan cutoffs and prime
endpoints under the same sector and cutoff conditions. Grouping rectangles
by `j+k` gives a geometric head and Gaussian tail. The actual coefficient
bound `|(typeIILong U * typeIIShort V)(n)|≤2n²` proves absolute convergence.
`GaussianMomentTypeI.lean` controls ordinary and logarithmic first-moment
fibres uniformly in both endpoints. For `1≤b≤X`, their common shape is

    ≪σ X^(1−σ)(1+log X)^4 [sqrt(αt)+1/(b sqrt(t))].

`GaussianMomentPrimeBound.lean` sums the actual truncated coefficients and
the finite Vaughan head. If additionally `t≥2`, `αX²=2` and `tUV≤X`,
the complete absolutely convergent von Mangoldt moment satisfies

    |M₁| ≪σ X^(1−σ)(1+log X)^6 / sqrt(t).

No zero-location premise enters. Arithmetic control retaining pole/filter
cancellation remains; this pole-scale estimate does not beat the selected
divisor signal or prove B13.

`GaussianTypeIContinuum.lean` and `GaussianMomentTypeIPole.lean` separate
an exact continuous pole term from the actual first type-I convolution.
For `c=Λ_U*μ_V`, `A_UV=Σ_{b≤UV}c(b)/b` and the first Gaussian pole
moment `P₁`,

    |Σ_n (ζ*c)(n)M₁(n) − A_UV P₁|
      ≤ Cσ UV log(UV)t α^(σ/2),

where `Cσ=4Γ(1−σ/2)+16Γ(2−σ/2)`. At `αX²=2`, this is
`≪σ UV log(UV)t X^(−σ)`. Each complete divisor fibre has a
spacing-independent variation bound; the complex Gamma integral
identifies its main term. Absolute rearrangement retains the signed
reciprocal coefficient mass. This closes pole extraction for the first
type-I term.

`GaussianSecondVariation.lean` and `GaussianSecondMomentTypeIPole.lean`
improve the first type-I remainder under the same conditions:

    |Σ_n (ζ*c)(n)M₁(n) − A_UV P₁|
      ≪σ (UV)² log(UV)t² X^(−1−σ).

The complete fibre error is `≪σ bt²X^(−1−σ)`. Two integrations by
parts use the integrable second derivative and the vanishing lattice
endpoints. The arithmetic bound gains a factor `UVt/X` over first
variation, with the signed pole coefficient unchanged.

`GaussianHigherDerivatives.lean`, `GaussianHigherLatticeError.lean`,
`GaussianHigherMomentLattice.lean` and `GaussianHigherMomentTypeIPole.lean`
extend the first type-I estimate to every fixed normalized moment
`M_r(x)=(ε/t)^r x^(2r−σ−it)exp(−εx²)`, `r≥1`. For `0≤σ<1`,
`t≥1`, `Re ε=α>0`, `|ε|≤4αt` and `αX²=2`,

    |Σ_n (ζ*c)(n)M_r(n) − A_UV P_r|
      ≪r,σ (UV)^(2r) log(UV)t^(2r) X^(1−σ−2r).

The explicit constant comes from a recursive Gaussian derivative bound
and the even Bernoulli remainder. All lower boundary derivatives vanish;
the final derivative is integrable at zero. Each increment of moment
order gains two powers of `UVt/X`. Higher-moment logarithmic estimates
and a full filtered reduction remain open; this first type-I improvement
does not establish a bound for centred type II.

`GaussianLogarithmicContinuum.lean` and `GaussianLogarithmicTypeIPole.lean`
extract both signed main terms from the actual logarithmic type-I convolution.
For `B_V=Σ_{b≤V}μ(b)/b`, `D_V=Σ_{b≤V}μ(b)log b/b` and
`L₁=∫₀∞log x·M₁(x)dx`, under the same sector conditions, `αX²=2`
and `V≤X`,

    |Σ_n (log*μ_V)(n)M₁(n) − (B_V L₁ − D_V P₁)|
      ≪σ Vt X^(−σ)(1+log X).

Scaling the logarithm before taking absolute values retains the Gaussian
power saving.

`GaussianLogSecondVariation.lean` and `GaussianLogSecondMomentTypeIPole.lean`
further improve the logarithmic error to

    |Σ_n (log*μ_V)(n)M₁(n) − (B_V L₁ − D_V P₁)|
      ≪σ V²t²X^(−1−σ)(1+log X).

The fractional margin `δ=(1−σ)/2` controls the logarithm in the
singular second-derivative moment. All five moments retain their Gaussian
scale, so the error gains `Vt/X` while both signed main terms remain exact.
`GaussianCentredVaughanCurrent.lean` combines both signed main terms with
actual type II. For `1/2≤σ<1`, `t≥2`, `0<α≤ξ≤2αt`, `αX²=2`,
`1≤U,V≤t²` and `X≥t⁸`, the complete prime moment satisfies

    M₁−P₁ = T_II+B_V L₁−(1+A_UV+D_V)P₁+Oσ(t⁷/X).

The error is at most `(8Dσ+3Cσ+8)t⁷/X≤(8Dσ+3Cσ+8)/t`, using
the two second-order lattice constants. Any two allowed cutoff pairs give centred currents
within twice this error. This removes both type-I remainders and the finite
head uniformly.

`GaussianDampingErrorAnalytic.lean`, `HolomorphicDampingFilters.lean` and
`GaussianFilteredCentredVaughanError.lean` retain every contracting-grid
factor in this reduction. For `β≥σ`, `t≥4`, `2α≤ξ≤αt`,
`X≥2e t⁸`, fixed roots `exp(hω_k)` and `0≤h≤1`,

    |filtered (M₁−P₁−C_UV)| ≪σ,β,ω h^d t^(d+7)/X.

Thus `X≥2e t^(d+8)` gives error `O(h^d/t)`, uniformly in spacing and
quadratic cutoffs. The exact polynomial sample sum is identified with the
existing `rotatedPrimeMomentFilter`. Holomorphy of the actual arithmetic
error and a logarithmic damping half-strip of width `1/(16t)` supply the
Cauchy cancellation. The independent bound for centred type II remains
open; this reduction does not prove B13.

`GaussianVaughanCutoffHorizon.lean` allows power-sized cutoffs. For
`0≤σ<1`, `0<η≤1/2`, and `X≥2e UV`, the same literal filter satisfies

    |F_h E_UV| ≪σ,β,η,ws h^d t^(d+2)(UV)²X^(−1−σ+η).

The product budget `(UV)²t^(d+3)≤X^(1+σ−η)` gives `O(h^d/t)`.
With polynomial-height `V`, the long cutoff approaches
`X^((1+σ)/2)` in exponent. Centred type-II cancellation remains open.

`GaussianVaughanCofactorTail.lean` and
`GaussianFilteredCofactorLocalization.lean` restrict the actual current to
cofactors at most `W`, keeping both continuum terms. The discarded tail has

    |filtered tail| ≪σ,β,k,ws h^d t^d X^(3+2k)/(UW)^(2k).

Together with the product budget, `UW≥X^(1+δ)`, `2kδ≥4`, and
`t^(d+1)≤X` give total reduction error `O(h^d/t)`. The remaining
cofactor exponent approaches `(1−σ)/2` when `V` is polynomial in height.
No sufficient arithmetic cancellation estimate for this core is proved.

## Mechanisms and tools

1. Subtract the actual finite divisor in an explicit formula, retaining all Gamma modes,
   pole terms and the infinite remainder. Track the gap in every error estimate.
2. Read a selected zero through prime-current moments or positive kernels. Derive mixed
   low-height/high-height information from the same arithmetic coefficients.
3. Compare tower excursions with current passage at the same observation scale. A
   conflict requires a proved common scale and compatible normalizations.
4. Use the functional equation together with Euler arithmetic to constrain the remainder.
   A height-reflection identity alone supplies no transport.

Tools sought: exceptional subtraction with joint parameter bounds; isolated-term Turán
estimates for the infinite divisor; positive kernels with an explicitly retained layer;
Gaussian-current laws at zeros and on high strips; Bohr sampling and tower density laws
that preserve the arithmetic relation between the layer and remainder.

`InfinitePowerSumsDetectAMaximalTerm.lean` supplies the infinite Turán tool.
For any nonzero absolutely summable complex family, its maximal modulus R
is attained, and some `1≤k≤64 Σ|z_j|/R` satisfies
`Re Σz_j^k>R^k/8`. A Fejér polynomial gives a summable lower bound,
so the argument retains every term. No separation below R is required.
Applied to reciprocal squares of a zero divisor, this detects a zero
using an order controlled by the divisor's normalized mass. An arithmetic
upper bound for those moments is still needed to deduce repulsion.

`ThePositiveDirichletMomentKernel.lean` proves the arithmetic inequality
for a real Dirichlet character χ. Put `Dχ=ζ′/ζ+L′/L`. For every `k≥0`,
`σ>1` and real t,

    Re[Dχ^(2k+1)(σ)+Dχ^(2k+1)(σ+it)] ≥ 0.

The exact infinite Euler series has weights
`(1+χ(n))Λ(n)(log n)^(2k+1)n^(−σ)(1+cos(t log n))≥0`.
`TheCompletedDirichletDivisor.lean` supplies the complete nontrivial divisor
of `Eχ(s)=ξ(s)q^(s/2)Λχ(s)` for primitive nonprincipal χ. All its zeros lie
in the open critical strip. With multiplicities, every `n≥0` satisfies

    (log Eχ)^(n+2)(s) = (−1)^(n+1)(n+1)! Σρ(s−ρ)^(−n−2).

The sum converges absolutely for `Re s>1`. For real χ, reflection gives

    (Re s−1) Σρ |s−ρ|⁻² ≤ 2 Re(Eχ′/Eχ)(s).

Neither identity assumes a nonzero central value.

`TheDirichletPoleControlsTheInfiniteDivisor.lean` joins Euler positivity
to the complete Gamma ladders. Every paired even nontrivial-zero moment
is at most the corresponding pole moment. Put `α=σ−1`,
`L=1+log q+log(|t|+3)`, and remove exactly one copy of a real zero β₁
from each observation. The remaining reciprocal-square family z satisfies

    Σ|z_j| ≪ α⁻²+L/α,       Re Σz_j^k ≤ 4k(1−β₁)α^(−2k−1).

The mass bound holds uniformly for `1<σ≤2`; the moment bound holds for
every positive k and every `σ>1`. All sums retain the infinite divisor,
and repeated copies of β₁ remain. These arithmetic estimates supply the
inputs for the power-sum detector.

`TheDeuringHeilbronnRepulsionLaw.lean` completes the classical Dirichlet
calibration. There is an absolute C>0 such that a real zero β₁>0 of a
primitive nonprincipal quadratic Lχ repels every distinct zero ρ of ζ or
Lχ with Re ρ≥½ and ρ≠1:

    1−Re ρ ≥ log(1/[C(1−β₁)log(q(|Im ρ|+3))])/[C log(q(|Im ρ|+3))].

The multiplicity-copy version removes only one copy of β₁. Choosing
α=(1−Re ρ)+1/(2L) bounds the normalized mass by O(1+(1−Re ρ)L),
so the detected moment yields the logarithmic repulsion law. All analytic
inputs are proved for the complete divisor. This is classical real-zero
repulsion; it does not prove repulsion from a nonreal exceptional layer of ζ.

## Questions and milestones

| Milestone | Required result |
|---|---|
| M1 | A usable, dependency-audited description of the finite-layer world |
| M2 | A graded repulsion law Θ∞−½ ≤ f(Θ−Θ₂, layer ordinates), with a genuine improvement over existing bounds |
| M3 | Failure of AAL implies finitely many off-line zeros, yielding AAL ⇔ B13 |
| M4 | Exclude an actual isolated exceptional quartet of ζ |
| M5 | Exclude every isolated top layer: prove AAL |

The precise M3 target is finiteness of the off-line remainder, as in §2.5 of the source
report. “Every other zero lies on the line” is stronger: reflection itself supplies a
bottom layer, and additional finite intermediate layers are not excluded by finiteness.
Neither assertion is assumed. M3 alone proves neither AAL nor B13.

Open questions include the correct graded repulsion function; whether a tower's
coefficient-density floor conflicts with the current at its observation scale; and
whether a top quartet forces replicas near multiples of its ordinate. Calibration must
recover the role of a real exceptional zero in the Dirichlet-L setting and distinguish
it from ζ's conjugate nonreal pair.

## Traps and calibration

- FE, reality and order one admit two-scale cosh models. Their layers coexist with
  off-line infinite remainders: these properties cannot prove M3.
- Euler positivity, integral coefficients and linear counting separately admit finite
  layers. A successful exclusion must use the exact FE and Euler product together.
- Positive theta sources and finitely many endpoint or Euler-deletion constraints
  survive off-line surgery. Finite preservation is not arithmetic reconstruction.
- Statistics restricted to either bounded heights or the high tail cannot decide AAL.
- A density lower bound is compatible with rare large current values. A contradiction
  requires matching both the density measure and the scale.
- A family-uniform finite-stratum law for the heat deformation already contains RH.
- A theorem assuming repulsion, transport, recurrence or a decisive current estimate
  does not supply that missing analytic input.

## Position in the corpus

ZeroConfigurationGeometry supplies the abscissa dial and exact finite-layer structure.
EulerFETransportTheory supplies the arithmetic current and FE rigidity; its central
transport question remains shared with this programme. InfiniteRankWeilTheory and
SurfaceOfSpecZ provide tower and prime sampling. ArithmeticCastelnuovoSeveri and
ArithmeticOrientationGeometry interpret these observables as intersection and index
data. Exceptional-layer theory owns interaction laws between a selected layer and the
infinite remainder, rather than duplicating those programmes' receiver equivalences.

## Contribution and success criteria

A contribution must prove a new constraint, identity or obstruction involving the
actual infinite arithmetic object and resolve a named part of the interaction problem.
Definitions, renamed implications, finite toy models, numerical experiments and sharper
constants without a new consequence do not qualify. A negative result must include its
strongest nontrivial positive survivor.

Every claimed theorem requires a complete Lean proof with no unproved analytic inputs,
no added axioms and no trusted computation. New modules belong in this directory and
are imported by `ExceptionalLayerTheory.lean`. The research target remains open until
the stated questions and tools are settled; foundational documentation is not its proof.
