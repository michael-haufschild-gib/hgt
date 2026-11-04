# Signed transport between the critical pole and a terminal window

- **ID:** critical-pole-window-signed-transport
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Parent:** [critical-ratio continuation](critical-ratio-continuation.md)
- **Verdict:** `BRIDGE`. No external novelty claim; no all-R positivity conclusion.

## Exact target and established scope

Let `L=log N`, `c_N≥1`, `c_N⁸/L→R>0`, `B_N` be the complete
tilted-spline matrix, `v_m` its normalized Ramanujan horizon vector,
`E_m(c)` the completed reference conductor energy, and
`x_N(n)=F(n/N)/sqrt(n)`, where `F=logProfile h` and h is C²,
supported in `[-A,0]`, `A≥0`. Set `φ=tiltedUnitSpline` and write

    a=(∫φ)²/∫φ²,  g=2+γ−log(4π)>0,
    M₈(H)=∫ exp(-8y)H(y)²dy,  H(y)=exp(y/2)h(y),
    S_A(h)=a[∫₀¹ F(x)(1/x−½log(1−x²))dx
              −log(2π)∫₀¹F(x)dx−Σ_(k≤K)Λ(k)∫₀^(1/k)F(x)dx],
    δ=exp(-A−1),  K=ceil(1/δ).

The general target is the literal complete-matrix limit

    (sqrt(L)/c_N)⟨B_Nv_m,x_N⟩ → S_A(h)[m=1].

Both general source limits pass their actual-path Lean audits with the
standard three axioms. The
finite-prime formulation avoids interchanging infinite prime sums.
Identifying its finite sum with `∫F(x)ψ(1/x)dx` is not needed by that source.

For support `(δ,η)⊂(1/2,1)`, both prime boundary channels vanish exactly,
and the complete polar/nonpolar limits are checked. These windows lie
in `[-log 2,0]`, inside the existing positive range `A≤181/250`.
They identify interactions, not a new unweighted sign range.

“Checked” here means successful individual actual-path Lean audit with
exactly `[propext, Classical.choice, Quot.sound]`. Written source alone
is not counted as checked.

## Source and competing mechanism

The existing `ccmRestrictedWeilOperator_polarPlus_coeFn` identifies the
finite-aperture continuous pole image. Translation to the terminal edge
and the Mertens limit give the candidate density

    D(y)=exp(-y)−ψ(exp(-y))−log(2π)−½log(1−exp(2y)),  y<0.

Thus `S_A(h)=a∫exp(y)h(y)D(y)dy` is the proposed continuum identification.
Its polar mass is consistent with the checked genus: partial summation
and Mertens give `∫₁ˣ(t−ψ(t))/t²dt→γ+1`, while the boundary logarithm
contributes `1−log 2`; the total is g. This consistency calculation is
paper only, not the discrete transfer proof.

The potential failure was an additional R-dependent aliasing cross term.
The discrete near row instead cancels log N before any estimate. For
conductor one, the full Mangoldt divisor convolution equals log j:

    near coefficient = [archPair−log(N/c)q]−[log c+log(j/N)]q.

For general m the exact decomposition retains the extra divisor jet:

    near coefficient_m(n,j)
      =c_m(j)[nearGammaRemainder−log(c)q−log(j/N)q]+jet_m(j)q.

Truncating the pole first would destroy that divisor identity. The proof
therefore retains the literal full pole, both prime directions, Gamma,
center and replacement channels. Fixed-conductor convergence alone is
not used to infer a growing-packet statement.

## Checked consequences on interior support

- `TerminalPolarSourceAboveHalf` and `TerminalNonpolarSourceAboveHalf`
  give exactly polar complete response, independent of R.
- `ThePoleCorrectorRetainsItsSignedWindowBenefit` gives, for every real t,

      c_N⁻¹⟨B_N(x_N+t sqrt(L)v₁),x_N+t sqrt(L)v₁⟩
        → a Q(H)+(7J(1)/R)M₈(H)+2tS(h)+t²D_R,
      D_R=J(1)/R+a g>0.

  On the established whole-space positive band, optimization gives
  `aQ(H)+(7J(1)/R)M₈(H)≥S(h)²/D_R`. Compensation remains.
- `TerminalPolarSourceIsNonzero` supplies
  `F₀(x)=tiltedUnitSpline(256x−254)`, supported in `[127/128,255/256]`,
  with `S(h₀)>0`. The exact inequality `(2π)²(1−x²)<1` on its support
  proves this without numerical evidence.
- `TheCriticalPoleHasAnIntrinsicCollarCost` gives a fixed κ>0, independent
  of R and its clock, such that at the actual small-band cutoff
  `M_N=N/linearDefectCutoff(c_N)`,

      (c_N⁷/L) DualCollar₇(M_N,N,B_Nv₁−E₁v₁)/E₁(c_N) ≥ κR²

  eventually. Weighted Cauchy–Schwarz, the nonzero source and
  `E₁≤C_E/c⁷` prove the bound first at `floor(N/2)`; monotonicity transfers
  it to the literal cutoff. Every fixed absolute budget fails for some R.
  The positive survivor is the signed response, not an all-R sign theorem.
  See [retired absolute-budget mechanism](../5-failed/critical-absolute-collar-budget-continuation.md).
- `LowConductorCorrectorsCannotImproveZeroSourceWindows` bounds every
  correction through `Q_N=floor(L^(13/32))` by total inverse-energy source
  mass. The limiting gain is at most `2S(h)²R/J(1)`, uniformly even over
  unbounded coefficients. On `ker S` it is zero.
- `TerminalPolarSourceHasANontrivialKernel` supplies a nonzero kernel test:
  put `F₁(x)=F₀(x+1/128)`, `hᵢ(y)=Fᵢ(exp y)`, and
  `h=S(h₁)h₀−S(h₀)h₁`. Disjoint support proves nonvanishing; linearity of
  literal pairings and uniqueness of limits prove `S(h)=0`. No negative
  Weil energy is asserted for this test.

## Complete general-window proof

### Literal normalization and checked channels

`sqrt(L)⟨A v_m,x_N⟩` is the literal double kernel sum with denominator
`sqrt(nj φ(m))`. The complete finite identities retain the scalar
`selfFinitePart(c)+adjunctionEnergy(m)−γ`; its terminal contribution
vanishes. These identities are checked in
`TerminalPolePairingsHaveTheirLiteralChannels` and
`TerminalConductorPairingsRetainTheDivisorJet`.

For m=1, the remaining normalized limits are:

| Channel | Limit |
|---|---|
| Full center | `a∫F(x)[1/x−½log(1−x²)]dx` |
| Near Gamma remainder minus separated cross | `−a(log(4π)+γ)∫F` |
| Near logarithmic row | `−a∫F(x)log x dx` |
| Near center minus log c times actual near Gram | `a∫F(x)[log(2x)+γ]dx` |
| Upward prime row, entering negatively | `aΣ_(k≤K)Λ(k)∫₀^(1/k)F` |
| Exterior, diagonal and replacement errors | `0` |

The middle three rows sum to `−a log(2π)∫F`. Their checked proofs retain
log c times the actual near Gram; ordinary near-Gram convergence would
not suffice. Principal sources are `TerminalNearPairsRetainLogarithmicAccuracy`,
`TerminalWindowsRetainTheJointNearCenter`, `TerminalWindowsReadTheNearLogarithm`,
`TerminalPoleGammaAndCenterHaveOneConstant` and `TerminalWindowsReadThePolarCenter`.

For fixed m≥2, the full-center charge is `−aΛ(m)∫F`; the periodic divisor
jet has mean Λ(m) and gives the opposite charge. This cancellation,
including prime powers, is checked in `TerminalDivisorJetsCancelTheNonpolarCenter`.
The remaining Gamma-center mean is zero.

`TerminalWindowErrorChannelsDisappear` checks ratio, self, pole and
reference-diagonal errors. After squaring the normalization, the first
three are respectively `O_m(c⁻²)`, `O_m(L/N²)` and
`O_m((c⁴L²/N)²)`. The diagonal uses the stronger coordinate estimate
`|⟨v_m,x_N⟩|=O_h(L⁻¹/²)` and costs `O_m((1+log c)/c)`.

### Checked exterior boundary

Actual exterior rows are supported on `n≥N−linearPrimeStrip(c)`, where
`linearPrimeStrip(c)≤(e+1)c`. There are O(c) rows, each O_m(c).
Since n≥N/2 eventually and F is bounded, their normalized pairing is
`O_(F,m)(c/sqrt(N))→0`. No gap below x=1 or prime-distribution estimate
is needed. The finite bound and critical limit in
`TerminalExteriorDownwardSourcesDisappear` pass their actual-path audit;
the limit depends only on the standard three axioms.

### Upward finite-prime transport

Put `M=∫φ²`, let ℓ be a global autocorrelation Lipschitz constant, and
choose `H=ceil(2c)≤3c`. A nonzero receiver has n>δN. Boundary multiples
kn∈[N−H,N+H] therefore satisfy `k≤K_b=ceil(2/δ)` when H≤N.
For each k≥1, injectivity of n↦kn bounds their number by 2H+1. Thus

    Σ_(n≤N)|F(n/N)| upwardBoundaryMass(N,n,H)/n
      ≤ B(2H+1)/(δN) Σ_(k≤K_b)Λ(k)/k.

This bound and its integrated actual-row comparison are checked in
`TerminalPrimeBoundaryMassHasFiniteSupport`.

Set `Cφ=12M+72ℓ`, `C₀=log 4+1+|mertensWindowConstant|`,
`P_b=Σ_(k≤K_b)Λ(k)/k`. The row-comparison error satisfies
`upwardLinearError≤Cφc³` and `|log(4c)+mertensWindowConstant|≤C₀c`.
Consequently

    |c⁻¹Σ_(n≤N)F(n/N)(upwardModeRow−upwardModel)/n|
      ≤ [6Bφ(m)CφC₀/(δM)+63Bφ(m)P_b/δ] c⁴/N.

The clock condition `c≥1`, `c⁴/N→0` also eventually ensures the finite
comparison conditions `4cH≤N`, `2H≤N`. Both the finite quartic bound and
its vanishing consequence in `TerminalUpwardRowReplacementDisappears`
pass their actual-path audits with the standard three axioms.

For the polar shell, the checked Riemann estimate gives
`upwardShellModel(φ,c,N,1,H,p)=acp/N+O_(φ,δ)(1)` uniformly for δN≤p≤N.
Only finitely many multipliers remain. Swapping their sums before taking
limits gives `aΣ_(k≤K)Λ(k)∫₀^(1/k)F`, `K≥1/δ`.
With `P_K=ΣΛ(k)/k`, `T_K=ΣΛ(k)` and `Lip(F)≤L_F`, the normalized error is

    6BℓP_K/(Mδ²c)+a(L_F+B)T_K/N.

For m≥2, `p+(m−1)j` and `(m−1)p+j` sum to `m(p+j)`, so their Ramanujan
coefficients agree. The shell consists of two shifted mean-zero
m-periodic sequences. The checked weighted periodic bound gives

    |normalized nonpolar model|
      ≤4Bmφ(m)(1+3ℓ/(Mδ))P_K/(δc).

Shell estimates, truncated Riemann error `(L_F+B)/N`, finite hyperbola
exchange, both summed model bounds and both model limits are checked in
`TerminalUpwardShellsHaveTheirPolarMean`, `TerminalPrimeMeansAreFiniteRiemannSums`
and `TerminalUpwardModelsHaveFinitePrimeSources`.
`TerminalUpwardSourcesHaveFinitePrimeMeans` adds the actual-row error;
all three principal endpoints pass their actual-path audits with the
standard three axioms. The actual upward limits need only `c→∞` and
`c⁴/N→0`, not a new prime estimate.

### Assembly

For compact C² h, take δ and K from the target. F is bounded, globally
Lipschitz and zero below δ. Continuity of the zero extension gives
`h(0)=F(1)=0`, as required by the full-center theorem. The critical clock
implies `c log c/N→0`, `c⁴/N→0` and `c→∞`. Adding the literal channel
limits yields S_A(h); for m≥2 all remaining sources cancel or vanish.
Both general endpoints in `TheCompleteTerminalSourceIsPolar` pass their
actual-path audit with the standard three axioms.

## Uniformity exposed by the existing conductor bounds

Put `r_m=B_Nv_m−E_m v_m`, `q_N(m)=|⟨r_m,x_N⟩|²/(c_NE_m)`.
For arbitrary δ>0 below the support, choose
`M_N=2 linearPrimeStrip(c_N)`. Eventually `M_N≤δN≤N` if δ≤1;
more generally both required inequalities follow from c_N/N→0.
The receiver prefix is exactly zero and its seventh collar mass is
at most `δ⁻⁷‖x_N‖²`. The dual collar estimate therefore gives

    |⟨r_m,x_N⟩|²≤C_h m²[c_N²/L+c_N³L/N+c_N¹⁰(L/N)²].

The actual conductor floor `c_N⁷E_m≥κm⁷` for m≤c_N yields

    q_N(m)≤(C_h/κ)[c_N⁸/L+c_N⁹L/N+c_N¹⁶L²/N²]/m⁵.

The bracket tends to R. The uniform coordinate bound and
`E_m≤C_φ+2log m+3` restore the reference diagonal without losing
summability. The general fifth-power envelope, its restored complete
version and the support-adapted cutoff estimates are checked in
`EveryTerminalWindowHasSummableConductorSources` and
`TerminalWindowsHaveMovingCollarCutoffs`. All five public endpoints pass
their actual-path audits with the standard three axioms.

Above overlap, the checked receiver-independent estimate is

    Σ_(c_N<m≤Q_N)‖r_m‖²/(c_NE_m)≤L^(-1/64) eventually.

The reference contribution through Q_N also vanishes. Thus fixed-m
limits, dominated convergence below overlap and this upper-packet bound
give

    Σ_(2≤m≤Q_N)|⟨B_Nv_m,x_N⟩|²/(c_NE_m)→0,
    Σ_(1≤m≤Q_N)|⟨B_Nv_m,x_N⟩|²/(c_NE_m)→S_A(h)²R/J(1).

`TerminalConductorSourcesConcentrateAtThePole` checks this for interior
support. `EveryTerminalWindowHasAPolarConductorSource` implements the
same conclusion for every compact window; its audit is pending.
Constants may depend on the fixed aperture; no growing-aperture theorem
is claimed.

## Sharp correction capacity: paper reduction, not yet formalized

The checked `eventually_completeWeil_low_packet_signed_approx` gives,
uniformly over all coefficients b,

    |⟨B_Ny_b,y_b⟩−ΣE_m b_m²−ag(c_N/L)b₁²|≤ηΣE_m b_m²

for every η>0 eventually. Let `p_m=⟨B_Nv_m,x_N⟩`, `0<η<1`, and
`d_m=(1−η)E_m+ag(c_N/L)[m=1]>0`. Completing each scalar square gives

    c_N⁻¹⟨B_N(x_N+y_b),x_N+y_b⟩
      ≥c_N⁻¹⟨B_Nx_N,x_N⟩−Σ p_m²/(c_N d_m).

The nonpolar budget is `(1−η)⁻¹Σ_(m≥2)p_m²/(c_NE_m)→0`.
The polar budget equals

    [(sqrt(L)/c_N)p₁]² / [(1−η)LE₁/c_N+ag]
      →S_A(h)²/[(1−η)J(1)/R+ag].

Letting η decrease to zero bounds every limiting correction gain by
`S_A(h)²/D_R`. The single pole coefficient
`b₁=−S_A(h)sqrt(L)/D_R`, all others zero, attains that value by the
complete mixed and pole-self limits. This is the exact proposed optimum;
no further Gram estimate is missing. `EveryLowPacketCorrectionHasItsPolarCapacity`
implements the finite budget, its limit, the sharp uniform bound and the
attaining pole coefficient; none is yet kernel checked. Its arbitrary-window
use also depends on the pending source audits.

The existing horizon limit is `aQ(H)+7J(1)M₈(H)/R`. Adding the attained
energy difference gives the complete corrected limit
`aQ(H)+7J(1)M₈(H)/R−S_A(h)²/D_R` for every compact window. On the
established positive critical band, choose the canonical clock; every
finite corrected vector then has nonnegative complete energy. Passage
to the limit proves `S_A(h)²/D_R≤aQ(H)+7J(1)M₈(H)/R`, without the old
interior-support restriction. This is a stronger compensated inequality,
not an enlargement to unbounded R. These two corollaries are included
in the pending sharp-capacity formalization.

## Remaining frontier

1. Complete the general moving-packet audit.
2. Formalize the sharp correction capacity and its general-window consequence.
3. Supply additional growing arithmetic receiving channels or control the
   complementary window energy directly. A rank-one correction leaves the
   full aliasing mass on its source kernel.

The all-R positive low packet is not the whole horizon. Independently,
the far-complement proof pays `C_S c S₇` with `g₀L S₇/(8c⁷)`, requiring
`8C_S R≤g₀`. Neither the polar source nor its optimized correction removes
this restriction. The parent target, unbounded R or compensation removal,
remains open.
