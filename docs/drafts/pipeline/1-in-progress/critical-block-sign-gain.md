# Signed low-block gain at the absolute assembly threshold

- **Stage:** 1-in-progress
- **Target:** B7, full-space positivity beyond the size-only optimum.
- **Status:** Conjectural source transfer; benchmark specification pending.

For an absolute two-block comparison with positive constants,

`A(R)=J−αR`, `D(R)=g−βR`, `B(R)=γR`,

the admissible interval ends when `A(R)D(R)=B(R)²`. At its positive
endpoint both diagonal entries remain positive. Replacing `A(R)` by
`J+ηR`, with `η>0`, strictly increases the determinant there; continuity
then gives an interval beyond that endpoint.

The actual growing conductor packet has the checked positive polar
correction `aφ(2+γ_E−log(4π))R`. This makes the comparison a candidate
for a full-space sign improvement, provided the actual far and mixed
estimates admit one sharp common block comparison.

Required source work: retain the constants and free splitting parameters
in the dyadic far reserve, dual-collar residual and Schur payment; certify
the optimum of the specified absolute assembly; prove its active endpoint
has a strict low-block gain. The existing existential small-band constants
do not certify that optimum. An arbitrarily chosen absolute bound would
not settle B7.

Corpus anchors: `TheTopCollarHasADyadicSeventhPowerReserve`,
`LogarithmFreeCriticalConductorResiduals`,
`TheCriticalSchurPairingRetainsTheCollarWeight`, and
`TheSignedCriticalResidualIsCompactBelowOverlap`.

## Uniform transfer conjecture

For `R=c⁸/log N`, the optimized terminal-window limit already proved is

`Q_R(h)=aφ W(halfWeight h)+(7 J₁/R)∫e⁻⁸ʸ(halfWeight h)²
        −generalTerminalPolarSource(A,h)²/criticalPoleWindowCost(R)`.

Conjecture: a positive lower bound for `Q_R` in the exponential norm,
uniform over compact windows, transfers to eventual full-space positivity.
The conductor-one correction is included in `Q_R`; omitting its negative
Schur term would give the wrong limiting form.

Fixed nonconstant periodic and trigonometric sectors have positive scalar
limits (`trig_twisted_sector_inherits`,
`ramComb_layer_criticalCurve_exact`). This does not give uniform control
when the profiles, frequencies and number of sectors vary with `N`.
The missing statement is compactness of possible negative vectors after
retaining the seventh-power aliasing reserve and the conductor-one source.
Neither a finite family limit nor positivity on every fixed twist proves it.

A proved averaging step is the following actual-spline statement. For
integrable `F` supported in `[δ,∞)`, `δ>0`,

`∫F(x)c⁸ aliasDensity(φ,cx) dx → (7/2)J₁(∫φ²)∫F(x)x⁻⁸ dx`.

The four cosine modes vanish by Riemann–Lebesgue; the rational-tail error
vanishes under the integral, and the harmonic bounds are summable in
`k⁻⁸`. A uniform multiplier bound extends this limit to weights converging
in `L¹`. Both statements are formalized in
`ArithmeticHodgeTheoryOfDegenerations/TheAliasingMeanIsStableUnderL1Convergence.lean`:
`tendsto_integrable_tilted_aliasDensity` and
`tendsto_tilted_aliasDensity_of_L1_convergence`. Direct audit passed with
only standard axioms. This does not supply the missing compactness of
negative vectors or the discrete aliasing lower bound along such vectors.

For a fixed terminal interval, a possible lower-bound argument uses
`E_high(x) ≥ 2 B_high(x,v_h) − E_high(v_h)` with smooth recovery profiles
`v_h`. The mass-row expansion separates the bulk from the alias term.
The adjoint synthesis estimate is now formalized in
`AtomicSynthesisRecoversLipschitzTests.lean`. For
`F_N=(√N/c) centredAtomicTest(φ,x,c,N)` and a Lipschitz test `f`,

`|∫F_N f − (∫φ)/√N Σ x_n f(log(n/N))|
 ≤ (c/N) Lip(f) ‖φ‖₁ ‖x‖₂`.

`abs_integral_normalizedCentredAtomicTest_mul_sub_le` passed its direct
audit with only standard axioms. The scaled alias multiplier has
Lipschitz constant `O(c⁹)`, so this error vanishes on the critical curve.
For polynomially bounded coefficient norms and strong physical `L¹` convergence
`F_N→F`, the exact discrete pairing now satisfies

`(∫φ)/√N Σ x_n g(log(n/N)) c⁸ aliasDensity(φ,cn/N)
 → (7/2)J₁(∫φ²)∫F(y)g(y)e⁻⁸ʸ dy`

for every bounded Lipschitz `g` supported in a fixed terminal interval.
`tendsto_criticalCurve_aliasing_pair_of_polynomial_norm_bound` in
`TheAliasingPairsWithStrongPhysicalLimits.lean` passed its direct audit
with only standard axioms. Strong physical convergence remains an input
to this lemma. Still required: the high-frequency row identity,
compactness with the weighted tail retained, and the polar Schur passage.

The below-grid operator comparison follows from the complex Riemann-sum
estimate and `horizonDirichlet_sq_div_le`. For fixed smooth
`h`, `H=halfWeight h`, `U_N=(√N/c) centredAtomicTest(φ,v_h,c,N)` and
`1≤r≤Ne⁻ᴬ`,
`∫|1_{|τ|≤Ne⁻ᴬ} Û_N(τ)−(∫φ)Ĥ(τ)|² ≤ C(c²r³/N²+1/r)`.
Choosing `r=c^(m+1)` proves `c^m` times this error tends to zero for every
fixed `m` on the critical curve. Both the bound and this limit are
formalized in `TheSynthesizedProfileIsRecoveredBelowTheGrid.lean`:
`integral_belowGrid_fourier_error_le` and
`tendsto_criticalCurve_belowGrid_fourier_error`. The direct audit passed
with only standard axioms.

Physical normalization is compatible with polynomial coefficient growth:
`integral_atomicTest_sq_ge_growing` gives
`‖U_N‖₂² ≥ growingMassConstant (∫φ²)c⁻⁸‖x‖₂²`.
Thus `‖U_N‖₂=1` implies `‖x‖₂=O(c⁴)`. The audited discrete pairing
lemma accommodates this growth: its error is bounded by
`O(c¹⁰‖x‖₂/N)`, and every fixed power of `c` is `o(N)` on the critical curve.

For global confinement, retain the raw far reserve before imposing its
small-multiple restriction. The required extension at fixed critical ratio
`R` is `Q_N(z) ≥ (7/8)D_M(z)−C_R c S₇(z)−o(log N/(log log N)^B)P(z)`.
Combined with the prefix defect floor, this would force
`P=O(c(log log N)^5/log N)S₇` for possible negative far vectors.
The raw reserve is formalized; this extension and the signed mixed-source
passage remain unproved.
