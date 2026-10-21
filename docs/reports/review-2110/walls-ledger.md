# The walls ledger

Thirteen proved obstructions on which direct attacks on the Riemann hypothesis stop. The first wall
has five faces: the square-root barrier in prime counting, the axis outside the zero set, the
ground-energy path, the forced dual measure with node criticality, and the Jensen gap. The faces are
one obstruction read in five languages; the dictionary between them is a proved theorem, stated at
the head of Wall 1. Each entry gives the mechanism, the exact place where unconditional methods end,
the Lean evidence, the positive statements the obstruction exposes, and the practical rule.
Companion documents: [per-route obstacles](hard-obstacles.md), [summary and the missing
field](hard-obstacles-summary.md); they cite the faces 1.5, 1.2, 1.4 and 1.3 by the labels 2, 4, 11
and 12. Walls keep their labels; the labels 2, 4, 11 and 12 are not used for separate walls.

**Lean checkpoint** `46cfca88e`. Evidence tags: [L] = committed Lean declaration imported by its
committed umbrella; [S] = Lean source in the working tree whose file or umbrella import is
uncommitted, or a module not imported by its umbrella (compiles standalone, no committed audit);
[P] = paper only. Module paths are relative to `formal/GaloisForLFunctions/`, with
`R:` = `RHTower/`, `H:` = `HTGeometry/`, `B:` = `BiScaleUncertainty/`, `V:` = `BezoutValuationIncidence/`,
`T:` = `TransHorizonIncidenceMechanics/`, `A:` = `arithmetic-positivity-theory/`,
`C:` = `ArithmeticCriticalityTheory/`, `I:` = `ArithmeticIncidencePositivity/`,
`Q:` = `SquareRootThreshold/`. Working-tree [S] items at this checkpoint: none; the working tree
relocates the umbrella import of `Q:ZetaLagFamilyVinogradovKorobovEnvelope` into the import block
of the `SquareRootThreshold` umbrella (position only).

Two general facts frame every wall. First, every graded relaxation of a surveyed route is a zero-free
half-plane or a finite-height verification: a one-sided power bound `O(x^θ)` on a Chebyshev, Mertens or
Möbius–divisor quantity is the statement `Θ ≤ θ` (`R:QuasiRHMeanSquareAbscissa`,
`R:QuasiRHDilationCovarianceAbscissa`, `R:QuasiRHQuotientHeadBoundary` [L]); a horizon-uniform bound on
the damped Möbius receiver at one fixed damping `ε ∈ (0, 1/2)` already gives the zero-translation law
`ζ(ρ) = 0, Re ρ > 1/2 + ε ⟹ ζ(ρ − ε) = 0` (`pmPowerDamped_zero_translation`,
`R:PMPowerDampedMobiusCriterion` [L]). There is no producer target weaker than RH on these routes.
Second, a new attempt must name the wall it passes and the concrete input that passes it before
anything is built; Wall 1 in each of its faces and walls 16 and 17 are RH-strength targets in
disguise, walls 3, 6, 7, 10 and 15 state what a class of evidence cannot do, walls 5, 8, 9, 13 and 14
constrain the shape of any construction.

## Wall 1: the zero width

Every face of this wall is a reading of the one number

`zetaZeroWidth = sup_ρ |Re ρ − 1/2| = Θ − 1/2 ∈ [0, 1/2]`,

the half-width of the strip containing the nontrivial zeros, and RH is `zetaZeroWidth = 0`. The
prime-counting face measures it as the exponent of every one-sided prime estimate; the axis face as
the strip itself and as the de Bruijn–Newman heat time; the ground-energy face as the decay rate of
the restricted Weil ground energy; the dual-measure face as the only point of the Weil cone; the
Jensen face as the Balazard–Saias–Yor integral. Progress on any face is progress on the width, and
an improvement counts once.

**The dictionary** (`Q:TheWallsMeasureOneZeroWidth` [L]; every statement unconditional, no premises).

- *One number in four languages.* `zetaZeroWidth = zetaZeroAbscissa − 1/2`
  (`zetaZeroWidth_eq_zetaZeroAbscissa_sub_half`), and for `σ ≥ 0` the statements `zetaZeroWidth ≤ σ`,
  `Θ ≤ 1/2 + σ`, `XiZeroHalfPlaneBound σ` and `∀ ρ ∈ zetaZeroConfig.carrier, Re ρ ≤ 1/2 + σ` are
  equivalent (`zetaZeroWidth_le_iff_zetaZeroAbscissa_le`, `zetaZeroWidth_le_iff_xiZeroHalfPlaneBound`;
  `Q:LagRateBoundsTheDeBruijnNewmanHeatTime`, `R:CrossRouteReceiverBridges` [L]).
- *Face 1.1 reads the width exactly.* For `0 ≤ σ < 1/2`, `zetaZeroWidth ≤ σ` iff the integrated
  Chebyshev deficit `D(T) = ∫₀ᵀ(eᵗ − ψ(eᵗ))dt` obeys the one-sided bound `D(T) ≤ B(1 + T)e^{(1/2+β)T}`
  for every `β > σ`, and iff it obeys the mirror lower bound
  (`zetaZeroWidth_le_iff_forall_deficitPrimitive_le`, `…_ge`); iff the mean-square band, the Laplace
  energy and the spectral band grow at every rate above `σ`
  (`zetaZeroWidth_le_iff_forall_meanSquareBandRate`, `…_laplaceEnergyRate`, `…_spectralBandRate`;
  `B:BandSpectrumZeroWidthLaw` [L]); iff the completed Suzuki formation energy is subpower at
  exponent `1 + 2σ` (`zetaZeroWidth_le_iff_suzukiCompletedFormationEnergy_subpower`); and, for a
  generic width, iff the lag family is `≥ −Ce^{σv}` at all large lags
  (`zetaZeroWidth_le_iff_lag_primeWindow_ge_neg_exp` [L]). The infimum of the cumulative
  Möbius–divisor Abel energy exponents is `1 + 2·zetaZeroWidth`
  (`one_add_two_mul_zetaZeroWidth_eq_sInf_mobiusDivisorAbelMeanSquareEnergy_exponents`;
  `R:QuasiRHMeanSquareAbscissa` [L]). The window ceiling is pinched, not exact: its excess exponent
  `θ* = inf{θ ≥ 0 : c(L) ≤ e^{L/2} + B(1 + L)e^{θL}` eventually`}` satisfies
  `zetaZeroWidth ≤ θ* ≤ zetaZeroWidth/2 + 1/4` (`windowCeilingExcessExponent`,
  `zetaZeroWidth_le_windowCeilingExcessExponent`,
  `windowCeilingExcessExponent_le_half_zetaZeroWidth_add_quarter`; `B:PrimeWindowCeilingWidthLaw` [L]).
- *Face 1.2 is the width.* `zetaZeroWidth ≤ σ` is the strip `|Re ρ − 1/2| ≤ σ`; the heat flow
  contracts it, `newmanConstant ≤ zetaZeroWidth²/2` (`newmanConstant_le_half_sq_zetaZeroWidth`), and
  `zetaZeroWidth = 0 ⟺ newmanConstant = 0` (`zetaZeroWidth_eq_zero_iff_newmanConstant_eq_zero`).
- *Face 1.3 bounds the width from above and feeds face 1.1 directly.* A floor
  `μ(A) ≥ −Ce^{2σA}` at all large apertures gives `zetaZeroWidth ≤ σ`
  (`zetaZeroWidth_le_of_ccmRestrictedWeilGroundEnergy_ge_neg_exp`) and gives the lag floor
  `P_v ≥ −C'e^{σv}` at all large lags for every width `2w < log 2`, with no exceptional set and
  without passing through the zeros, by the Rayleigh bridge `2‖κ_w‖²μ(v/2 + w) ≤ Re P_{w,v}`
  (`lag_primeWindow_ge_neg_exp_of_ccmRestrictedWeilGroundEnergy_ge_neg_exp`). At the endpoint
  `zetaZeroWidth = 0 ⟺ μ(A) → 0` (`zetaZeroWidth_eq_zero_iff_tendsto_ccmRestrictedWeilGroundEnergy_zero`).
  The three graded statements are ordered: ground-energy floor at rate `2σ` ⟹ lag floor at rate
  `σ` ⟺ `zetaZeroWidth ≤ σ` ⟺ every reading of face 1.1 at rate `σ`.
- *Face 1.4 is a support condition.* Prime-blind positivity on a node set `S` is the existence of
  a full-cone Weil-positive weight vanishing off `S`
  (`primeBlindPositiveOn_iff_exists_weilPositiveFull_eq_zero_off`); since the cone is `{Λ}`, it is
  Weil positivity of `Λ` together with `supp Λ ⊆ S`
  (`primeBlindPositiveOn_iff_weilPositiveFull_vonMangoldt_and_support`), and
  `zetaZeroWidth = 0 ⟺` prime-blind positivity on the prime powers
  (`zetaZeroWidth_eq_zero_iff_primeBlindPositiveOn_primePowers`).
- *Face 1.5 is the width at the endpoint only.* Every zero right of the line contributes
  `2π m_ρ log|ρ/(1 − ρ)|` to the Balazard–Saias–Yor integral
  (`two_pi_mul_log_norm_div_le_integral_log_norm_zeta_criticalLine`), and the integral vanishes iff
  the width does (`integral_log_norm_zeta_criticalLine_eq_zero_iff_zetaZeroWidth_eq_zero`). The
  Blaschke weight of a zero decays with its height, so the face carries no exponent.
- *Endpoint.* `zetaZeroWidth = 0 ⟺ |D(T)| ≤ Be^{T/2}` (`zetaZeroWidth_eq_zero_iff_deficitPrimitive_bound`),
  and through `riemannHypothesis_iff_zetaZeroWidth_eq_zero` every RH criterion of faces 1.1–1.5 is a
  statement about the width.

**The open arrow.** The dictionary has one missing direction: `zetaZeroWidth ≤ σ ⟹ μ(A) ≥ −Ce^{2σA}`
for `σ > 0` (at `σ = 0` it is `RH ⟹ μ ≥ 0`, proved). Its obstruction is a normalization: the
off-line zero sum of the Weil form on a test of aperture `A` is controlled by `e^{2σA}` times an `H¹`
norm of the test, while `μ(A)` is the `L²`-normalized bottom of the spectrum. This arrow is the
graded form of the no-crossing problem of face 1.3; every other reading is exactly the width.

**Walls without a width face.** Walls 3, 5–10 and 13–17 carry no parameter tied to the width: 3 and 7
are quantifier statements on one lag family, 5, 14 and 15 are structural impossibilities, 6 and 16
are threshold classifications at damping `1/2`, 8, 9 and 13 are rigidity and selectivity laws, 10
is a transport dichotomy, 17 an exponent law on the pronic Gram. The admission at one damping `ε` of
wall 16 yields the translation closure `ζ(ρ) = 0, Re ρ > 1/2 + ε ⟹ ζ(ρ − ε) = 0` and bounds no
width.

### Face 1.1: the square-root barrier in prime counting

Every producer route eventually needs an unconditional statement of the form "a prime or Möbius sum
up to `x` has error `x^{1/2+ε}`", which is RH itself: `ψ(x) − x = O(x^{1/2+ε})`, `M(x) = O(x^{1/2+ε})`,
`Σ_{n≤x} μ(n)/n = O(x^{−1/2+ε})` each imply RH by Landau's theorem and follow from RH by the explicit
formula. Unconditional methods stop at Vinogradov–Korobov savings `exp(−c(log x)^{3/5})`; a power
saving `x^θ`, `θ < 1`, is already the zero-free half-plane `Re s > θ`. One-sided producers (Robin,
Nicolas, Lagarias, sieve-weight positivity) trigger only at the full exponent `1/2`. The lag–frequency
law explains why the exponent is forced: a test function vanishing at the nodes `log n` near lag `y`
carries spectral content at frequency `≍ e^y` with amplitude `e^{−y/2}`, the square-root size, so every
blind family loses a logarithmic margin against the pole weight `e^{y/2}`.

**Sharpest corpus forms.** Three statements put the whole of RH into one prime quantity with no height
parameter and no averaging.

- One inequality per dyadic window. For all but countably many widths `0 < w < log 2/2`, RH holds iff
  the window functional `P_v` of the unmodulated difference test `κ_w(t + v/2) − κ_w(t − v/2)` is
  nonnegative at every lag `v ≥ V`; each test reads `Λ(n)` only on `|log n − v| ≤ 2w ⊂ (X/2, 2X)`,
  `X = e^v` (`zeta_onLine_iff_lag_primeWindow_nonneg`, `Q:OneParameterLagFamilyDecidesTheCriticalLine`;
  `Q:LargeDyadicPrimeWindowsDecideTheCriticalLine` [L]). The strongest unconditional lower bound is of
  Vinogradov–Korobov strength: for every `ex < 3/5`, `P_v ≥ −|φ(0)| − C_w exp(v/2 − v^ex)` for
  `v ≥ V₀(w, ex)` (`zeta_lag_envelope_vinogradovKorobov`, `Q:ZetaLagFamilyVinogradovKorobovEnvelope`
  [L]: the Vinogradov–Korobov zero-free width at the height cut `G = exp(v^θ)`, `θ = (ex + 3/5)/2`,
  in the width–height tradeoff `|φ(v)| ≤ e^{v/2}(W e^{−ηv} + S₂/(1 + G)²)`); with an explicit lag,
  `P_v ≥ −|φ(0)| − C_w exp(v/2 − √v/10)` for `v ≥ max(230², 1/(100η₀²))`
  (`zeta_lag_envelope`, `Q:ZetaLagFamilyUnconditionalEnvelope` [L]); the pole-free window has the
  all-aperture floor `Q⁰ ≥ −2B₂(10 + 68e^A)`, `A = v/2 + w`, with the continuous main term paid exactly
  and the discrete prime discrepancy unpaid at scale `e^{v/2}`
  (`Q:PolarGroundEnergyAndPoleFreeLagAbscissaBridge` [L]).
- The window ceiling. For tests supported in intervals of length `L = log X`, the exact ceiling
  `c(L) = sup (A − W)/‖c‖²` of the prime side satisfies `c(L)/e^{L/2} → 1` and the floor
  `f(L)/e^{L/2} → −1` unconditionally; RH follows from `c(L) ≤ e^{L/2} + B(1 + L)` eventually, and
  from the mirror floor bound; the excess exponent `θ*` of `c(L) − e^{L/2}` satisfies
  `width ≤ θ* ≤ width/2 + 1/4` (`riemannHypothesis_of_windowCeiling_le`,
  `B:PrimeWindowCeilingRHCriterion`; `B:PrimeWindowCeilingPolarAsymptotics`;
  `B:PrimeWindowLiouvilleMirror`; `B:PrimeWindowCeilingWidthLaw` [L]). RH is absolute precision
  `O(log X)` at the scale `√X` on a finite prime quantity. Window extremes are invariant under every
  unimodular completely multiplicative twist of the prime atoms (Liouville sign, vertical shifts,
  Dirichlet characters), so they read the atoms only through their sizes and never detect GRH
  (`B:PrimeWindowTwistInvariance` [L]).
- The linear band. `∫₀^L Ẽ² = O(L)` for the normalized Chebyshev error is RH in both directions, the
  band's exponential rate is the zero width, its slope bounds `Σ m_ρ²/|ρ|²`, and the band of one
  universal cubic-spline probe is RH-equivalent (`riemannHypothesis_iff_meanSquare_band`,
  `B:BandSpectrumZeroWidthLaw`; `B:BandSlopeZeroEnergyLaw`; `riemannHypothesis_iff_splineProbe_band`,
  `B:CubicSplineUniversalProbe`; `riemannHypothesis_iff_packet_band_of_universal`, `B:PacketBandLaw` [L]).

**Receivers in the corpus** [L]. `R:RobinCriterionRiemann`, `R:LagariasCriterionRiemann`,
`R:NicolasInequalityRiemannConverse`, `R:RobinColossallyAbundantReduction` (Robin on all integers iff
on colossally abundant integers), `R:PrimeLagLowerBoundRH`, `R:ChebyshevDeficitPrimitiveOneSidedRH`
(`±∫₀ᵀ(eᵗ − ψ(eᵗ))dt ≤ Be^{T/2}` forces RH), `B:DeficitPrimitiveOneSidedWidth` (width-`α` form),
`R:MertensSquareRootOmega` and `R:MertensFrontierOneSidedOmega` (graded one-sided `Ω±` laws at the zero
frontier), `R:MertensRemainderExponentLaw` (the exponent of any one-sided Mertens estimate is the zero
abscissa), `V:PowerSavingIncrementCriterion` (uniform strict-half-power control of first-octave Möbius
increments is RH), `V:DampedChebyshevTangentFormOfTheReceiver` (an integrable-damping pronic norm bound
implies RH), `T:MoebiusAndLiouvilleReceiversAreEquivalent` (`riemannHypothesis_of_liouville_cofinal_receiver`),
`R:FermiNymanRawMobiusTailFloor` (raw Möbius approximant error `(N+1)H_N²/6`),
`R:LittlewoodOmega` (`Ω±(√x log log log x)`: no `O(√x)` target, no eventual fixed sign).

**Where unconditional methods stop** [L]. `R:MoebiusAbelSmoothedSaving`, `R:Sieve/VinogradovRouteTSaving`,
`V:VinogradovKorobovCofinalMobiusDiscrepancy` (VK shape, never a power); `R:QuasiRHHighDilationPositiveEnvelope`
(the positive absolute envelope of the signed covariance grows at the wrong exponent `J^{m+1}`: the
missing input is signed cancellation, not a majorant); `T:GlobalRenormalizedDefectSignAtLargeHorizons`,
`T:QuadraticLongWindowThreshold` (every finite law of the trans-horizon Möbius source is owned, none
bounds the coefficient-weighted complete energy below the first period);
`R:BeurlingRegularIntegersOffLineZeros` (a Beurling system with regular integer count and zeros at any
`β ∈ (1/2, 1)`: regularity of the integers does not supply square-root cancellation).

**Rule.** Before trying a producer, name the prime sum it needs and the exponent it needs. If the
exponent is `1/2`, or the precision is `O(log X)` at scale `√X`, the route is a restatement of RH; at
any other exponent it is a bound on `zetaZeroWidth`, and the dictionary says which other face it moves.

### Face 1.2: the axis outside the zero set

Hermite–Biehler and shift arguments compare `ξ` with a shifted, differenced, heat-flowed or
`1 + λξ'/ξ` copy; each is real-rooted exactly when the axis `Re w = a` lies outside the zero set. Axis
`a = 1` is unconditional, axis `1/2 + δ` is the statement `Θ ≤ 1/2 + δ`. De Bruijn's strip theorem
shrinks a strip of width `Δ` to width `√(Δ² − δ²)` under the shift, never to zero.

**In the corpus** [L]. `R:DeBruijnNewmanHalfBound` (`newmanConstant ≤ 1/8` unconditionally, the strip
width); `R:DeBruijnNewmanNonnegative` (`not_real_rooted_of_neg`: Newman's conjecture, `H_t` has a
non-real zero at every `t < 0`, so the de Bruijn–Newman constant lies in `[0, 1/8]` and RH is the
equality `Λ = 0`; the strip gives the upper end, the arithmetic of the Gaussian-damped series the lower
end, and nothing moves either); `R:XiCosineShiftLaguerrePolya` (`cos(hD)Ξ` is Laguerre–Pólya for `h ≥ 1/2` unconditionally and
for every `h > 0` under RH); `R:StrictHermiteBiehlerGivesRH`, `R:XiHermiteBiehlerCount`,
`R:KreinChamberIsLagarias` (`Re ξ'/ξ > 0` is Lagarias's criterion, not an input);
`R:SuzukiShiftedXiLeakageRH` (shifted-`Ξ` leakage is RH-equivalent);
`Q:OneParameterLagFamilyMeasuresTheAbscissa`, `Q:NegativityRateEqualsMaximalDepth` (for every `σ ≥ 0`,
`Re ρ ≤ 1/2 + σ` iff the lag functional is eventually `≥ −Ce^{σv}`; the negativity rate equals the
maximal depth); `B:PrimeWindowCeilingWidthLaw`, `B:DeficitPrimitiveOneSidedWidth` (window excess and
deficit-primitive bounds at exponent `θ` give zero width `≤ θ`). The zero width
`zetaZeroWidth = sup |Re ρ − ½|` is read on the prime side as the exact negativity rate of the lag
family and on the heat side as the de Bruijn–Newman time: `H_t` is real-rooted for
`t ≥ zetaZeroWidth²/2`, RH iff `zetaZeroWidth = 0` (`Q:LagRateBoundsTheDeBruijnNewmanHeatTime` [L]).
The strip width `1/8` is the only unconditional value of the heat time. The lag family, the window
ceiling and the shift constructions measure the strip; none moves its edge.

**Rule.** Any argument built from `ξ` shifted, differenced, heat-flowed or multiplied by `1 + λξ'/ξ`
has a dominance parameter. State what unconditional fact pushes that parameter past the strip edge
`1/2`; the corpus knows none.

### Face 1.3: the ground-energy path

The restricted Weil ground energy `μ(A)` at aperture `A` is the quantitative form of "no margin"
(face 1.4): a positivity producer must prove `μ(A) ≥ 0` at every aperture, and `μ(A)` decays to `0`
under RH and to `−∞` off it at the rate `2·zetaZeroWidth`.

**Floors and limits** [L]. `μ(A) ≥ 1/30` for `A ≤ 21/200` (`one_thirtieth_le_ccmRestrictedWeilGroundEnergy`,
`C:ExplicitSmallApertureCCMGroundEnergyFloor`); `μ(A) ≥ 1/125, 1/50, 1/250, 1/250, 1/500` for
`A ≤ 29/200, 39/200, 6/25, 13/50, 7/25` (`C:MarkovWindowPastPlasticThreshold`,
`C:QuadraticGaugeWindowWeilPositivity`, `C:ParityFoldedCurvedGaugeWeilPositivity`,
`C:QuarticGaugeParityFoldedWeilPositivity`, `C:FoldBoundaryQuarticGaugeWeilPositivity`);
`μ(A) ≥ 1/1000` for `A ≤ 29/100` (`C:PastPlasticFoldWeilPositivity`); `μ(A) ≥ 1/5000` for
`A ≤ 3/10` (`one_div_5000_le_ccmRestrictedWeilGroundEnergy_threeTenths`,
`C:ThreeTenthsSharpGaugeWeilPositivity`); the logarithmic window floor
`μ(A) ≥ −log(2A) − 3A/2 − 2·archConstantReal − 4A³` for `2A < log 2`, Suzuki's main term
(`C:WindowGaugeLogarithmicGroundEnergyFloor`); the polar ground energy `μ₀ ≥ 1/20` through
`(log 2 + 1/50)/2` and `μ₀(A) ≥ −(10 + 68e^A)` at every aperture
(`Q:PolarGroundEnergyAndPoleFreeLagAbscissaBridge`), the latter being the dictionary's floor at the
unconditional width `1/2`. Limits: `μ(A) < ε` for all large `A` and
`μ(A) ≤ K exp((11/2)A − πe^{2(A−2)})` for `A ≥ 3`, unconditionally
(`C:RestrictedWeilGroundEnergyCriticalAtInfinity`, `C:GaussianCriticalityRestrictedWeilGroundEnergy`).

**Receivers** [L]. RH iff `μ(A) → 0` (`riemannHypothesis_iff_tendsto_ccmRestrictedWeilGroundEnergy_zero`);
RH iff `μ₀ ≥ 0` at all apertures, iff `μ₀(A) ≥ −C_σ e^{2σA}` eventually for every `σ > 0`, with no
attainment premise on continuous apertures; an eventual floor `μ(A) ≥ −Ce^{2σA}` forces zero width
`≤ σ` (`Q:GroundEnergyAbscissaAndLagGridAttainmentBridge`). Contact aperture: a near-top zero
`½ + z₀` with data `(w, η, V ≥ V₀(w, η, Re z₀))` makes `μ(A) < 0` for every `A ≥ V/2 + w` (the
explicit-lag visibility law through the Rayleigh bridge,
`Q:NearTopZerosForceNegativeGroundEnergyBeyondAnExplicitAperture`); every certified aperture is the
bound `V > 2(A − w)` on the visibility lag of every near-top zero. Criticality of every term: the
odd form admits no Hardy weight (`riemannHypothesis_iff_nonneg_and_no_hardyWeight`,
`C:OddFormCriticality`), every prime rate `Λ(n)n^{−1/2}` is the least admissible rate
(`C:JumpRateCriticality`), the capacity ratio of plateau truncations tends to `1`
(`C:CapacityRatioApertureCriticality`), the smeared-gauge form has no uniform variance floor
(`C:SmearedGaugeVarianceCriticality`). Under RH `μ` decreases to `0` without crossing; off RH it
tends to `−∞`.

**Spectral realization at finite aperture** [L]. The published CCM logarithmic Dirac package is
formalized unconditionally as a dichotomy: on the literal finite restricted-Weil matrix at aperture
`λ = e^a`, either the boundary channel meets the ground level and the canonical ground vector `ξ`
carries a `T`-self-adjoint completion with `det_reg(D_log − z) = −iλ^{−iz}ξ̂(z)` and only real zeros of
`ξ̂`, or every ground vector is boundary-blind and the odd response channel carries a metric-self-adjoint
completion with real spectrum (`R:CCMLogDiracDeterminantTheorem`, `R:CCMLogDiracRankOneDeterminant`,
`R:CCMCircleDiracZetaDeterminant`, `H:ComplexShiftLerch`). The passage from real-rooted ground
transforms at each aperture to `Ξ` needs locally uniform convergence in a strip, which is an unproved
premise (`R:CCMRestrictedWeilFullFormRealRootedGround`); `R:CCMRestrictedWeilEvenPolarGroundOperator`
realizes the constrained form as a self-adjoint operator with compact resolvent without supplying a
sign. Connes–Consani's archimedean trace domination on the window `[2^{−1/2}, 2^{1/2}]` (their Theorem
1, closed in print by numerics) reduces to a sign of `Σ_k √λ_k(‖ϑ(g)v_k^−‖² − ‖ϑ(g)v_k^+‖²)` over the
even prolate modes and is open in Lean [P].

**Rule.** Progress on this face is measured by the aperture through which `μ(A) ≥ 0` is proved for
all profiles; identities count as zero. A floor `μ(A) ≥ −Ce^{2σA}` is a bound `zetaZeroWidth ≤ σ`
and a lag floor at rate `σ`; the converse, a floor from the width, is the open arrow of the
dictionary and is where the no-crossing problem sits in graded form.

### Face 1.4: the forced dual measure and node criticality

Every certificate of prime-blind or Weil positivity yields a positive spectral measure on the line; by
uniqueness of the Weil cone and atomicity of the boundary measure that measure is the critical-zero
counting measure. A producer of positivity is a spectral realization of the zeros, every linear or
convex reformulation has exact duality whose only certificate is the zero measure, and near-null tests
with pole `≈ −archimedean part` and `|pole|/mass → ∞` exist under RH, so no estimate with a margin can
certify positivity. Node criticality is the support condition of the same statement: prime-blind
positivity on a node set `S` (the pole-plus-archimedean part of the Weil functional nonnegative on
every nonnegative combination of autocorrelations vanishing at `±log n`, `n ∈ S`) is the existence of
a full-cone Weil-positive weight vanishing off `S`, hence RH together with `S ⊇ {prime powers}`.
Deleting one prime-power node, even `log 4`, makes it false; non-prime-power nodes are redundant. Any
argument insensitive to a single node cannot work: sampling density, Nyquist, Beurling–Malliavin,
generic uncertainty principles.

**The cone** [L]. `R:WeilConeUniquenessUnconditional` (`eq_vonMangoldt_of_weilPositiveFull`);
`R:WeilConePoleWeightRigidity`; `R:WeilPositivityBeurlingPerturbationRigidity`,
`R:WeilPositivityResidueRigidity`; `R:EvenSectorPoleWeightUniqueness`, `R:EvenSectorTwistedArcNull`;
`R:ArchimedeanUnitNodeEnergy`.

**The nodes** [L]. `primeBlindPositiveOn_iff` (`R:PrimeBlindNodeCriticality`);
`riemannHypothesis_iff_primeBlindPositive_unconditional` (`R:TwistedArcMinimumPrincipleProof`);
`R:WeilPositivityPrimeBlindDuality`; `B:PrimePowerZeroPoleNodeCriticality` (`ZeroPoleBlindPositiveOn N ↔
RH ∧ PP ⊆ N`: incidence, not density; primes alone never suffice); `R:ArchimedeanUnitNodeEnergy` (every
single node is RH-equivalent); `B:PoleInvisibilityOnGappedBlindGrids`, `B:SquareRootDensityPoleInvisibility`,
`B:ExactSingleIntegerBlindSymbolSlack` (sub-square-root-density and single-tower node sets fail, with
sharp slacks); `R:EvenSectorBlindMinimumSmallAperturePositivity`
(`riemannHypothesis_iff_evenBlindMinimum_nonneg_beyond_primeTwo`, blind minimum `≥ 1/20` below aperture
`(log 2 + 1/50)/2`); `C:ExtraJumpVisibilityThresholdAtInfinity` (the prime `2` is visible at infinity
in the shifted gauge iff `e^{−2a} < 3/4`); `R:PrimeBlindCarlsonThreshold`.

**The price of a node** [L]. The blind cone reads the Euler product. Deleting one prime power `m` from
the prime-power blind cone costs exactly `Λ(m)/√m` in both directions, attained only by the narrow
pairs `g ± g(· − log m)` (`B:PrimePowerNodeDeletionPrice`, `B:PrimePowerDeletionPeriodizationDefect`:
the defect is the energy of a periodization along `log m`); prices add across towers, `log 6` paying
nothing (`B:PrimePowerDeletionPriceAdditivity`), and add over any finite set of primes
(`B:PrimePowerDeletionPriceEulerAdditivity`), also on the full integer grid with every composite imposed
(`B:PrimePowerDeletionStaircaseTrains`, `B:PrimePowerDeletionSlabTrains`); inside a tower they interact,
`{2, 4}` costing `(√17 − 1)log 2/4`, strictly between `log 2/√2` and `log 2/√2 + log 2/2`
(`B:PrimePowerTowerDeletionInteraction`); whole towers cost the local Euler factors
`±Σ_p 2log p/(√p ∓ 1)`, approached, not attained (`B:PrimeTowerDeletionLocalEulerFactor`), and lose
`≥ 9/10` at the upper end once the composite `pq` is imposed (`B:PrimeTowerDeletionCompositeCharge`).
Two prices are attained together only on windows longer than `log(m₁m₂)` (`B:PrimeTwoThreeDecouplingLength`;
`B:PrimePowerDeletionPairThreshold`); the second window `(log 3, log 4)` has exact ceiling
`λ₂₃ = (w₃ + √(w₃² + 4w₂²))/2 ≈ 0.90 < w₂ + w₃` (`B:PrimeWindowCeilings`). Node `4` is redundant in the
dyadic blind grid but changes the second cosine coefficient; node `6` has zero atom and positive polar
collar mass yet gives strict blindness gains (`C:SignChangingTwoMomentAndAtomPoleIntegralLaw`).
Incidence inside one dyadic window: the only divisor edges are doublings and triplings, the only
crossing prime-power edges consecutive powers of `2` or `3`, each `< 2 log 3/X`
(`I:DyadicWindowIncidence`); the same-side ratio atom dominates the crossing product atom on every
lattice pair (`I:PrimePowerIncidenceDominance`).

**Rule.** A positivity producer must come with the Hilbert space and the self-adjoint operator whose
spectrum it realizes. If the argument only manipulates test functions and inequalities, its certificate
is the zero measure and the argument is circular. Before a positivity argument on blind tests, check
whether it survives removal of one prime-power node or thinning of the node set. If it does, it proves
something false. A mechanism must read the Euler-product prices above, not a density.

### Face 1.5: the Jensen gap between `|ζ|²` and `log|ζ|`

RH is the vanishing of the Balazard–Saias–Yor integral `(1/2π)∫ log|ζ(1/2 + it)| dt/(1/4 + t²)`, which
equals the positive sum `Σ_{Re ρ > 1/2} m_ρ log|ρ/(1 − ρ)|`; equivalently `(s − 1)ζ(s)/s²` is outer on
`Re s > 1/2`. Every unconditional tool controls square means or mollified square means; the criterion
needs the mean of the logarithm, and Jensen's inequality goes the wrong way. The face sees the width
only at the endpoint: each zero right of the line is a separate nonnegative term whose Blaschke weight
decays with the height, so the integral bounds no exponent.

**In the corpus** [L]. `integral_log_norm_zeta_criticalLine_eq_tsum_rightZeros`
(`R:BalazardSaiasYorZeroSum`): the unconditional identity as a convergent multiplicity-weighted sum over
all zeros right of the line; `R:ZetaCriticalLineJensenInequality` (the integral is nonnegative and RH
follows if it is `≤ 0`); `R:ZetaCriticalLineJensenEquality` (circle averages converge to it);
`riemannHypothesis_iff_forall_mollified_meanSquare_le` (`R:BalazardSaiasYorMollifierClass`): the
mollified form `inf_M (1/2π)∫|ζM|² dt/(1/4 + t²)/|M(1)|² = 1`; Dirichlet-polynomial mollifiers stay at
ratio `≥ 49/48`; `R:BaezDuarteBlaschkeFloor` (`d_N² ≥ 1 − exp(−2Σ log|ρ/(1−ρ)|)`).
The quantitative form in Báez-Duarte coordinates: every finite row at level `N ≥ 2` has residual
`≥ κ/log N`, and `κ·readout² ≤ (log N − κ)·energy` (`V:ReadoutEnergyUncertaintyPrinciple`,
`V:PronicBaezDuarteCriterion` [L]); the literal `−μ_N` row aligns the readout (`→ 1`) and keeps centred
pronic energy `≥ κ/(4 log N)` (`V:LogHarmonicReadoutAndTheMobiusRowEnergyFloor` [L]).
`R:FermiNymanWitnessGermRigidity`: the FZZ-P Haar problem is exactly outerness of `Ξ(s)/s²`.

**Rule.** An attempt that bounds a square mean, a mollified moment or a Gram form of `|ζ(1/2 + it)|²dt`
must say how the logarithm is reached. Outerness needs equality in Jensen, which no mean-value estimate
provides; in Báez-Duarte coordinates the residual cannot be made `o(1/log N)` by any finite row.

## Wall 3: local zero clustering

A localized explicit formula at height `γ₀` with a test of log-length `λ log γ₀` excludes a zero at
real part `β` only if the window around `γ₀` contains few zeros. Unconditionally a window of width
`1/(λ log γ₀)` may contain `≍ log γ₀` zeros, and Turán's loss `(n/(8e(M + n)))^n` with `n ≍ log γ₀` is
`γ₀^{−c log log γ₀}`, larger than any power gain. Zero-density estimates count in strips, never inside
one window.

**In the corpus** [L]. `exists_xiZeroCount_window_le` (`R:XiZeroCountLocalCeiling`): the sharp local
ceiling `N(t + H) − N(t) ≤ (H/2π)log(t + H) + 2C log(t + H)`; `R:XiLogDerivLineOneWindowLower`: fixed-width
windows contain `≥ log T` zeros; `R:ZetaRightZeroWeightedCount`, `T:WindowedQuarterZeroDensityAndCHMDBoundStateCount`,
`A:InghamHuxleyHeightBoxZeroMajorant`, `A:SelbergExponentialNearLineAndThreeRegimeZeroDensity`
(density majorants over height ranges, none excluding one fixed off-line zero);
`R:TuranSumOneSidedBoundary`; `R:JointAncestryShellPowerSumCriterion` (RH iff zeros approach the line
and a power-sum growth bound holds on dyadic shells); `R:DeBruijnClusterPersistence` (clusters persist
under the heat flow).

**Lag-side form.** Positivity of the one-parameter lag family on a finite lag range `[0, V]` forces
every near-top zero to hide in a collapsed cluster: a loud record has two companions within `2r` or an
exponentially tight twin, isolated tight pairs cannot hide, and clusters hiding a record have
geometric-mean radius `O(r e^{−cVr/p})` with multiplicity `p + 1 ≤ 80 log(180Γ) + 1`
(`Q:ZetaLagPositivityForcesCloseCompanions`, `Q:ZetaHidingRequiresLoudTwins`, `Q:ZetaIsolatedTwinsCannotHide`,
`Q:ZetaTwinsAreExponentiallyTightUnlessTripled`, `Q:ZetaNearTopClustersCollapseBeyondTheThreshold`,
`Q:ZetaNearTopZerosHideOnlyInCollapsedClusters` [L]). For the problem's own family `P_v` the collapsed
cluster door is closed: a zero `1/V`-near the top with `η = |h_w(γ₀ − iδ₀)| > 0` makes some `P_v < 0`,
`v ∈ [0, V]`, once `V ≥ V₀(w, η, δ₀) ≍ (log Γ₀)² log log Γ₀/δ₀`, `Γ₀ ≍ η^{−2/3}`, with no attainment and
no height condition (`Q:OneParameterLagFamilySeesNearTopZeros`,
`Q:OneParameterLagFamilySeesNearTopZerosAtAnExplicitLag`,
`Q:OneParameterLagFamilyRecordsAreVisibleAtAnExplicitLag` [L]). These are zero-side visibility laws:
they bound the first negative lag by the data of a hypothetical off-line zero and supply no sign of
`P_v`. The residual barrier is the pair-correlation barrier: twins closer than `log log γ/V`.

**Rule.** A window argument needs an unconditional bound on the number of zeros in a window of width
`1/log γ₀` better than `O(log γ₀)`; none exists. On the lag side the same wall reads: a hypothetical
off-line zero can hide from any finite lag range only inside an approximate multiple zero.

## Wall 5: no Frobenius, no `F₁`

The function-field proofs use that the zeros are Frobenius eigenvalues on a finite-dimensional
cohomology, with the identity `f(x)^q = f^{(q)}(x^q)` on fixed points and, in Deligne's case, a
tensor-power amplification exact by the known pole of `H²_c`. For `ζ` there is no archimedean object
whose fixed points are the primes, and every analytic imitation of the amplification is circular:
rescaling moves the pole, moments of `Ξ` are zero-blind, the amplified Chebyshev error `E(x)^{2k}` has
Landau abscissa `2k(Θ − 1/2)`, function-field positive cones with `q ≥ 2` have periodic zeros.

**In the corpus** [L]. `R:StepanovCount`, `R:StepanovCharacterSum` (the auxiliary-polynomial count and
the elementary Weil bound; the vanishing uses the Frobenius identity); `R:FunctionFieldFE` (closure of
Frobenius eigenvalues under `ω ↦ q/ω`; purity `|ω| = √q` is not formalized);
`R:CCMFUCompactAutocorrelationDeningerAmplification` (amplified responses grow without bound at late
translations; the arithmetic side of the amplification is the open weld); `R:TwinRigidityZetaPower`
(a degree-`d` twin of `ζ^d` with all zeros critical is `ζ^d`: tensor powers add no freedom);
`R:DeningerCarrierNoIntegralLattice`, `R:FrobeniusTorsionLaw` (three distinct prime actions are
incompatible with a nonreal `ρ` in any finite-rank lattice; torsion is unitary).

**Rule.** An amplification or positivity argument must identify the object on whose fixed points the
primes sit. Without a fibration making `Spec ℤ` a fibre over a one-dimensional base, every tensor-power
or Rankin trick returns the Landau abscissa.

## Wall 6: the probability cone

Positivity statements derived from the Euler product hold exactly where the Dirichlet series converges
absolutely, `Re s > 1`; continuation into the strip is not positivity-preserving. `log ζ(σ + it)` is
positive definite for `σ > 1` only; the Eisenstein series is a positive sum for `u > 1` only; random
Euler products are zero-free almost surely on `Re s > 1/2`, but `ζ` is one point of the torus.

**In the corpus** [L]. `H:PrimeDirichletPositiveDefinite` (positive definiteness needs absolute
summability); `R:FiniteEulerStageNearLineStrip` (finite Euler stages are zero-free near the line only
up to a truncation-determined height); `R:SelbergPositiveEisenstein`;
`R:JointAncestryEndpointBudgetProducer` (the native prime-product form is nonnegative on finite prime
sets of budget `Σ_P p^{−(σ−1/2)} ≤ ((log y)/(128·10⁸))^{3/2}/(log log y)⁴`; the level-one RH receiver
needs budget `y^{1/2}`); `R:SteinhausEulerVerticalBarrier`, `R:SteinhausEulerQuadraticApprox`.
The receiver form of the same line: on the damped class `|c(d)| ≤ Kd^{−ε}` one constant bounds every
Möbius-type receiver when `ε > 1/2`, and for `ε ≤ 1/2` a nonnegative weight has bounded receiver iff
its dyadic masses satisfy `Σ_k M_k²/2^k < ∞`, so without signs there is no cancellation at all
(`T:HalfDampingIsTheExactThresholdOfTheParityPair`, `T:DyadicMassesGovernPositiveReceivers`,
`T:ReceiverOfMultiplicativeWeightsIsDecidedAtThePrimes` [L]).

**Rule.** When a positivity or definiteness statement is proved, check the half-plane on which it is
proved. If it is `Re s > 1`, or damping `ε > 1/2`, the strip statement must be obtained some other way.

## Wall 7: statistical and almost-all results

Families, Bohr–Jessen–Bagchi value distribution, universality, Kac–Rice densities, almost-all
short-interval theorems and lag grids give statements true for a positive proportion, for almost all
members, or on sets of density one. RH is a statement about one function at every height. Around an
off-line zero the return set has density zero, so the statistical and the pointwise statement are
separated exactly by the zeros one wants to exclude.

**In the corpus** [L]. `R:ZetaStrongRecurrenceReceiver`, `R:ZetaTypicalHeightApproximationExcludesZeroTargets`
(any target with a zero inside the disc is approximated by `ζ` only on a density-zero set of heights);
`R:ZetaDiscRecurrenceIffUniformHeadTargetDensity` (`zetaDiscStronglyRecurrentOn_iff_headTargetUniformlyDense`,
`riemannHypothesis_of_forall_headTargetUniformlyDense`); `R:ZetaDiscRecurrenceOnZeroFreeDiscs`: every
locally zero-free right-strip point has a recurrent closed disc with cutoff-uniform Dirichlet-head
target approximation, and RH iff every right-half-strip point has some strongly recurrent closed disc.
Recurrence is therefore closed exactly on zero-free discs, and the open statement is literally "exclude
a zero from the disc". `R:FiniteEulerProductKroneckerWeylLimitLaw`, `R:FiniteEulerProductUniversalityOnDiscs`,
`R:UniformEulerTargetDensityOnZeroFreeDiscs` (positive-density visits of finite Euler products, the
statistical half); `R:ZetaWeakRecurrenceLadderCollapse` (weak recurrence relocates off-line zeros, it does
not remove them); `R:WeilPositiveAlmostAllShortIntervals`; `R:XiReciprocalSlicePositiveDensity`;
`R:XiCardGateUnification`.
Lag grids: `exists_chain_hidden_from_grid` (`Q:ChainsHideFromLagGrids`), a summable nonresonant chain
with strictly increasing unattained depths is nonpositive at every integer lag and unbounded on the
continuum; `Q:GridHiddenChainsHaveAnExplicitContinuumLag` (the continuum sees it at lag `O(log M)`);
`Q:LagGridsSeeAttainedTops` (RH iff grid nonnegativity together with attainment of a rightmost zero in
every nonempty off-line set); `Q:LagGridAliasingPotentialLaw` (grids need no loud zero aliasing onto
the record). For the continuum family the attainment premise is replaced by a horizon condition: if
`P_v ≥ 0` on `[0, V]`, then from every zero inside the horizon (`V₀(z₀) ≤ V`) a zero beyond it is
reached, deeper by `> 1/V`; hence some `P_v < 0` on `[0, V]` whenever all zeros deeper than `z₀ + 1/V`
lie inside the horizon (`one_param_horizon_law`, `one_param_visible_of_horizon`,
`Q:OneParameterLagFamilyHorizonLaw` [L]). What remains unattainable is the depth of the zeros beyond
every finite horizon.

**Rule.** An attempt that averages over `τ`, over characters, over a random model or over a lag grid
must name the step that upgrades "almost all" to "all". The upgrade is where the off-line zero hides;
on the lag family it is the condition on the zeros beyond the horizon.

## Wall 8: infinitesimal admixture

The Weil functional is affine in the weight system. Deforming an unconditionally positive producer
toward `Λ` does not dilute the RH content: for every `t > 0` positivity of `tΛ + (1 − t)λ₀` at all
apertures is RH, because an off-line pair costs `t·2Re f̂(γ₀ − iε)² ≈ −te^{2aε}‖f‖²` against an
archimedean slack of size `log γ₀·‖f‖²`.

**In the corpus** [L]. `R:LebesgueAtomArchimedeanWeilDensity` (the explicit positive system whose
deformation was tried); `R:WeilConePoleWeightRigidity`, `R:WeilPoleWeightForcedOne` (the full cone fixes
the pole weight at one; even super-residue deformations `β > 1` are impossible);
`R:WeilConeVonMangoldtZetaPencil` (the pencil `βΛ + γ[n ≥ 2] + v` meets the cone only at `Λ`);
`R:WeilPositivityBeurlingPerturbationRigidity`; `R:WeilLittleOVonMangoldtRigidity` (an `o(Λ)` deviation
leaves the cone); `R:WeilFullConeMinorantRigidity` (`λ ≤ Λ` or `λ ≥ Λ` full-positive forces `λ = Λ`);
`R:TrivialWeightBoostedWeilCone` (a boosted archimedean datum admits trivial weights: positivity after
changing the datum is not positivity of the fixed form).

**Rule.** Do not try to reach `Λ` from an unconditionally positive system by a small deformation. The
cone is a point, and every direction out of it is RH-equivalent at any amplitude.

## Wall 9: the temperedness gate

`ζ(s − a)ζ(s + a)`, `a` real and nonzero, has an Euler product, the functional equation `s ↦ 1 − s`,
polynomial growth and nonnegative coefficients `2Λ(n)cosh(a log n)`, yet its zeros lie on
`Re s = 1/2 ± a` and its poles at `1 ± a`. It fails only coefficient size. Any producer using only
Euler product, functional equation, growth and nonnegativity would prove a false statement.

**In the corpus** [L]. `R:NonTemperedShiftedZetaPairCountermodel` (`not_ramanujan_shiftedPairCoeff` and
the full list of positive properties); `R:BeurlingRegularIntegersOffLineZeros`;
`R:TwinRigidityZetaPower`, `R:TwinRigidityOffLineZero`; `R:WeilConePoleWeightRigidity`.
Selectivity theorems, which pass the gate: the full odd window positivity of `ζ` past the plastic
threshold fails for the shifted pair at every radius `> t*/2` and already at radius `13/125 < 21/200`
for large `a` (`I:ShiftedPairOddWindowSelectivity`, `I:ShiftedPairHankelSelectivity` [L]); on even
tests the shifted pair has a negative window at every positive radius for large `a`
(`C:EvenWindowShiftedPairSelectivity` [L]); the weighted prime majorant `ΣΛ(n)(n^a + n^{−a})n^{−1−ε}`
diverges for `ε ≤ |a|` while `ζ`'s converges for every `ε > 0`
(`A:CompactCriticalPolynomialWindowAndTemperednessBridge` [L]); for the shifted pair with `a < 1/2`
every local Euler factor of the damped receiver sits left of the line, so no finite prime set sees
its off-line zeros (`T:LocalEulerFactorsAndPronicDilationContraction` [L]). Window positivity of `ζ`
is selective against large shifts; small shifts still pass every prime-free window, and no window
statement has been tested against a Beurling system.

**Rule.** List the properties of `ζ` a proposed argument uses. If `ζ(s − a)ζ(s + a)` has all of them,
the argument is wrong somewhere. A positivity statement counts only after its selectivity is proved.

## Wall 10: the oscillation–transport dichotomy

Exponential-sum methods give power savings for oscillating sums; zero-detecting sums
(`ψ(x/j) − ψ(x/(j+1))`, `Σ μ(m)m^{−s}` with its transported poles, the sawtooth `Σ Λ(d){x/d}`) do not
oscillate. Transport either keeps the `1/ζ` structure and the transported poles, with no power saving,
or acquires a phase that destroys the pole structure, with no zero information.

**In the corpus** [L]. `R:MoebiusAbelSmoothedSaving` (VK-shaped saving because the sum is
non-oscillating); `R:Sieve/VinogradovRouteTSaving`, `R:Sieve/MontgomeryVaughanArbitraryLogPhaseReceiver`
(oscillating objects with fixed small exponents carrying no pole information);
`V:VaughanTypeIIShortAndAllHorizonMobiusL2Energy`, `V:LinearBandVaughanTypeIIBilinearEstimate` (the
Type-II short side is the negative literal Möbius sieve above `1`; the saving lives on the bilinear
piece; the unsigned all-horizon energy `M·invSum(M)³` carries no sign);
`R:MobiusLaplaceCriticalDilationNoGo` (absolute-value Neumann attacks fail at the critical dilation
weight `k^{−1/2}`); `R:FermiNymanRawMobiusTailFloor`; `R:CCMFUSuzukiMobiusQuotientTail` (tail past
quotient cutoff `Q` is `O_ε(M^{Θ+ε+1/2}Q^{1/2−Θ−ε})`: the head keeps all signs).

**Rule.** Classify the sum a method bounds. If it oscillates, say how the bound is transported back to
a non-oscillating zero detector without introducing a phase; if it does not oscillate, the method is a
zero-free-region argument in disguise.

## Wall 13: cone mismatch

Maximum principles, transfer-operator positivity and pointwise gauges act on pointwise cones; the
positivity to be proved lives on the Bochner cone (autocorrelations, positive-definite functions,
nonnegative spectral measures). The two cones differ in both directions, and the Bochner cone is
exactly the cone of positive-definite zonal kernels on `ℍ`.

**In the corpus** [L]. `R:WeilConeMismatchWitnesses` (`weilTest_self_re_neg_twoSignedWeilTest`: a
smooth Weil autocorrelation negative at lag `3`; a nonnegative two-hump profile that is no
autocorrelation; nonnegative tests blind at every `log n` are positive only on a set of measure
`≤ log 2`); `R:HyperbolicPointPairMehlerFockDictionary`
(`isPositiveDefinitePointPair_iff_re_selbergTransform_nonneg`: positive definiteness on `ℍ` iff
`Re h_k(1/2 + iτ) ≥ 0` iff the Abel transform is Bochner-positive, with the horocyclic Kontorovich–Lebedev
decomposition); `R:TwistedArcMinimumPrincipleProof`, `R:BlindCoreMayerTransferHalf` (transfer-operator
positivity is pointwise positivity at real `s`); `C:FiniteJumpFormAllegrettoPiepenbrink` (on a
connected finite kernel the two cones coincide: form nonnegativity iff a strictly positive
supersolution exists, the finite model the continuum does not obey).

**The pointwise route and its reach.** No nonnegative gauge is a folded supersolution: every admitted
nonnegative profile is a strict subsolution near the origin (source `−2∫M dm`) and at infinity (source
`−2∫₀^∞ M cosh(r/2)`); one added jump repairs infinity iff `e^{−2a} + e^{−2ℓ} < 1` and never the origin;
finite signed superpositions nonnegative on the half-line and positive theta convolutions fail at
infinity; a supersolution, if one exists, is sign-changing with `∫M dm ≤ 0` and `∫₀^∞ M cosh ≤ 0`
(`C:ShiftedGroundStateOriginFailure`, `C:ShiftedGroundStateInfinityFailure`,
`C:DoobSourcePoleMomentLawAtInfinity`, `C:FoldedSourceOriginJumpMomentLaw`,
`C:ExtraJumpVisibilityThresholdAtInfinity`, `C:SignedSuperpositionInfinityFailure`,
`C:ThetaConvolutionFoldedInfinityFailure`, `C:SignChangingTwoMomentAndAtomPoleIntegralLaw` [L]).
Window gauges with the parity fold, quartic profiles, a two-point fold cost and hub–Schur
redistribution (a Poincaré inequality for the folded jump form, `hub_energy_ge`, and the Schur step
`A(t − c)² + Bt² ≥ c²AB/(A + B)` that lets a potential negative in places be paid by its Schur
average) give the full real and complex form `Ẑ(F) ≥ (1/1000)∫F²` on `[−29/100, 29/100]` and
`Ẑ(F) ≥ (1/5000)∫F²` on `[−3/10, 3/10]` [L] (`C:PastPlasticFoldWeilPositivity`,
`C:FoldedJumpHubSchur`, `C:ThreeTenthsSharpGaugeWeilPositivity`). On odd tests the folded surplus with
its ground-state transform, the sharp micro-fold (Harnack across every prime-power shift: `2Λ(n)/√n·∫F F(· + log n)
≤ 2·stripSurplus` for `log n/2 < r ≤ log n/2 + 1/12`, with constant `λ ≈ 1.88`) and the strip shared by
a convex `θ`-split give `Ẑ(F) ≥ (1/100)∫F²` through `347/1000`, `(1/200)∫F²` through `7/20`,
`(1/1000)∫F²` through `353/1000`: the odd sector passes the first prime with the atom `Λ(2)/√2` paid
and no pole-free margin (`I:OddWindowPastFirstPrime`, `I:SharpMicroFoldHarnack`,
`I:AtomFreeOddWindowSevenTwentieths`, `I:SharpFoldOddWindowPastSevenTwentieths` [L]; the
Schur-absorbed ground state, which lends potential from a hub to the inner edge of the strip, is
`I:SchurAbsorbedGroundState` [L]). Every such certificate is window-bounded: on even tests the
conductances across the first prime turn negative past `log 2/2`, and on odd tests the inner edge of
the prime strip at `≈ 0.355` needs potential `0.0030` against `0.0017` available
(`I:SchurFoldWindowNumeratorBounds` [L] certifies the numerator at `356/1000` without a capstone). The
meeting of the pointwise and Bochner cones is thus not confined to the window sector `|supp| ≤ log 2`
of the mismatch witnesses, but no pointwise or Schur certificate reaches arbitrary support, and the
maximum-principle route has no nonnegative candidate at all.

**Rule.** When a positivity statement is proved by a maximum principle, a transfer operator or a
pointwise gauge, identify the cone it lives on and the support through which it holds. A Bochner-cone
statement at arbitrary support needs a transfer from pointwise positivity compatible with blindness;
every known transfer stops at an explicit radius.

## Wall 14: the size law

The primes cannot enter a spectral model as a finite-rank, trace-class or finite-deficiency
modification of an archimedean reference. The zero count has the archimedean density `θ'(t)/π`, and
its fluctuation `S(T)` is unbounded with `∫|S| = ∞`, incompatible with a trace-class perturbation of a
reference of archimedean density. Quantum graphs with `ℚ`-independent bond lengths decouple, and
unitary producers carry Euler factors only with modulus one.

**In the corpus** [L]. `R:ZeroCountRemainderNotIntegrable` (`not_integrableOn_rvmRemainder`:
`∫_A^T |S| ≥ cT/log T`); `Q:ZetaZeroCountRemainderIsUnbounded` (`rvmRemainder_unbounded`: for every `B`
and `T₀` some `T ≥ T₀` has `|S(T)| > B`, through the localized explicit formula of the bump
autocorrelation, the sparse-height off-line correction and Kronecker–Weyl visits on the prime torus:
`Q:ZetaWindowPrimePolynomialReadsZeroCountRemainder`, `Q:ZetaOffLineCorrectionSmallOutsideSparseHeights`,
`Q:ZetaWindowPrimePolynomialOnThePrimeTorus`); `R:QuantumGraphPrimePowerDecoupling`;
`R:UnitaryEulerFactorRigidity`; `R:ArithmeticDilationTraceClass` (the trace-class realizations the
corpus has are of absolutely summable matrices, the absolute-convergence regime of Wall 6);
`R:BurnolFirstJetShellScaleLaw` (positive damping shells tend strongly to zero while their trace tends
to `log(c)/4`); `R:SourceInverseTraceIdealNoGo` (the Xi inverse is `S₂` but not `S₁`);
`R:HermitianPencilEulerFactorObstruction`.

**Rule.** A Hilbert–Pólya style model must say in which Schatten class, or with what deficiency
index, the primes modify the archimedean operator. Trace class, finite rank and finite deficiency are
excluded; the modification must be as large as the zero fluctuation.

## Wall 15: support versus positivity

Positivity of currents, positive-definite functions and Schur products never constrains where zeros
lie. The Poincaré–Lelong current `i∂∂̄ log|ξ|² = Σ[ρ]` is positive for any zero set; the positive
definiteness of `Ξ` bounds `|Ξ(t)| ≤ Ξ(0)` and says nothing about zeros. An orientation of the zero
set relative to the critical axis is a reality or unitarity structure, and reflection-even data cannot
recover a reflection-odd sign.

**In the corpus** [L]. `H:EntirePoincareLelong`; `R:EulerShiftPairIncidenceCurrent`
(`xi_isPoincareLelongOfSmooth`: the collision charge is a multiplicity count);
`R:XiHorizontalCollisionExchangeOrientationNoGo` (the oriented extension vanishes under pair exchange;
the survivor is the squared displacement); `Q:WeilFormDeterminesTheConfiguration` (`eq_of_weil_eq`: the
all-aperture signed form determines a tempered configuration); `Q:CrystallizationHidesOffLineZeros`
(`exists_offLine_superset_hiding`: finite-aperture positivity is not monotone in the zero set);
`R:TranslationAveragedDensityDepthBlindness` (full translation averages are independent of a zero's
transverse depth); `B:PrimeWindowTwistInvariance` (window extremes see atoms only through sizes);
`R:XiCosineShiftLaguerrePolya`, `R:DeBruijnNewmanHalfBound` (the real-rootedness results that exist are
strip statements).

**Rule.** When a construction yields a positive current, a positive-definite function or a positive
measure, ask what in it changes sign when a zero is reflected across the critical line. If nothing
does, the construction cannot locate zeros.

## Wall 16: the parity barrier at half damping

The damped Möbius receiver (the pronic energy `E_T(c) = Σ_{n≤T} A_c(n)²/(n(n + 1))` of the centred
prefix of `c ∗ 1`, the PM and BVI receiver) is bounded for `c = μ(d)d^{−ε}` at `ε = 1/2` and must be
bounded at arbitrarily small `ε > 0` for RH. Below half damping the receiver cannot be decided by any
sign-blind data: parity pairs exist at every `0 < ε ≤ 1/2`, two weights with identical Ramanujan
amplitudes, identical complete-period divisor-sum statistics and identical pronic Gram data, one with
bounded and one with divergent receiver. This is the sieve parity problem in the receiver's own
coordinates, and it is sharp at `ε = 1/2`.

**In the corpus** [L]. `T:ParityPairAtHalfDamping` (the Möbius weight and its nonnegative parity twin
`c'_ε(d) = (ρ_ε/U_ε) d μ²(d) ∏_{p|d} 1/(p^{1+ε} − 2)`); `T:CharacterFourParityPairAtEveryDamping`,
`T:RealCharacterParityPairsAndTheParityBarrier` (`parity_barrier`: for `0 < ε ≤ 1/2` no function of the
amplitudes decides receiver boundedness on the damped class); `receiverBounded_amplitudeInvariant_iff`
(`T:HalfDampingIsTheExactThresholdOfTheParityPair`: amplitude-invariance holds iff `ε > 1/2`; the
whole difference lives in the trans-horizon tail `nΣ_{d>n} c(d)/d` and the head drift, both of order
`n^{1−ε}`); `T:CriticalWienerConvolutionsPreserveTheReceiver` (the Liouville weight and the smooth
power form a pair); `T:UnimodularCharacterCompletionsAreParityPartnersOfTheSmoothPower`;
`T:FermiRowsAgreeInEveryTranslatedMomentAndSplitTheReceiver`,
`T:EvenFlipOfTheFermiSquarefreeWeightBreaksTheReceiver` (rows indistinguishable by every translated
moment of every degree and shift, with opposite trans-horizon growth: the even flip is the Fermi
transform of the even part, `T:EvenFlipIsTheFermiTransformOfTheEvenPart`).

**What separates a pair.** The first pronic moment is the von Mangoldt pairing
`Σ_n A_c(n)/(n(n + 1)) = −Σ_e Λ(e)W_c(e)`, supported on prime powers (`T:FirstPronicMomentIsTheVonMangoldtPairing`);
it orders every pair with a positive member and is blind exactly when the parity lives on composite
moduli (`T:FirstPronicMomentOrdersPositivePairs`, `T:FirstMomentBlindParityPairOfTheNegatedMoebiusWeight`);
the `k`-th logarithmic moment reads `Λ_{k+1}`, supported on `ω(e) ≤ k + 1`, and the logarithmic moments
are a complete receiver invariant (`T:SecondVonMangoldtMomentSeparatesTheBlindPair`,
`T:LogarithmicMomentHierarchySeparatesEveryPositivePair`, `T:LogarithmicMomentsAreACompleteReceiverInvariant`);
cubic translated moments pin odd rows and pin squarefree rows up to the even flip
(`T:CubicMomentsPinTheParityOfOddRows`, `T:CubicMomentsPinSquarefreeRowsUpToTheEvenFlip`). The receiver
is a local critical-line detector: a local factor `δ₁ − aδ_p` preserves the growth class iff
`|a| < √p`, sparse prime flips preserve it, and a bounded `±1` pattern must flip a prime set of
divergent critical-line mass (`T:LocalEulerFactorsAndPronicDilationContraction`,
`T:SparsePrimeFlipsPreserveTheReceiver`). Pole laws: a finite or critical-Wiener kernel repairs a
positive drift only when its value at the pole `K(1 − ε) = Σ_j k(j)j^{−(1−ε)}` vanishes, the paid
perturbations of the smooth power and of every coprime weight form that hyperplane, multiplicative
weights pretending to one are paid exactly when some local factor vanishes at the pole, and the even
flip shifts the pole value by `(1 − 2^ε)K_e(1 − ε)` (`T:FiniteKernelsRepairAPositiveDriftOnlyAtItsPole`,
`T:CriticalWienerKernelsRepairAPositiveDriftOnlyAtItsPole`, `T:FinitePerturbationsOfTheSmoothPowerAreDecidedAtThePole`,
`T:FinitePerturbationsOfCoprimeWeightsAreDecidedAtThePole`,
`T:MultiplicativeWeightsPretendingToOneArePaidOnlyByAVanishingLocalFactor`,
`T:AVanishingFiniteLocalFactorPaysAWeightPretendingToOne`,
`T:TheEvenFlipShiftsThePoleValueByTheEvenPartOfTheKernel` [L]; a double pole needs a double zero,
`T:APoleOfOrderTwoNeedsAZeroOfOrderTwo` [L]).

**Rule.** Any bound on the Möbius receiver below half damping must read the signs of the coefficients:
first-order data at prime moduli (`k ↦ pk`) or odd-degree additive moments (`k ↦ k + v`). Magnitude
data, two-point data and, for squarefree rows, all translated moments are blind. The Type-II input the
cancellation routes need is a signed one; its loss is not controlled by any data invariant under the
parity involution.

## Wall 17: coherent blocks and the one-modulus large-sieve ceiling

The bilinear form `Σ_{p∼P} Σ_{q∼Q} a_p b_q 𝒢^{ec}(p, q)` on the pronic Gram must be bounded with no
character or modulus average at exponent `θ = 2 log P/log X = 2` (the receiver); the large sieve is of
diagonal quality only at `θ ≤ 1`. Between them every Type-II input in the sense of an `ℓ²` bound on
coefficients fails, because coherent blocks of primes near a multiple have packet energy matching the
large-sieve loss exactly.

**In the corpus** [L]. `V:BrownianBridgeLawOfThePrimeBlockAndCodimensionNoGo` (any `J` linear side
conditions admit a nonzero packet with `Q ≥ (k² − 1)/(24(2P + 1))·Σ_p a_p² p`, `(J + 3)k ≤ |S|`);
`V:CoherentPrimeBlocksAndTheTypeIIWindowNoGo` (unit-jump prime blocks are affine on clean regions and
carry window energy `≥ (k/2304)·kΣ_W w`: the large-sieve loss `P²/X` is attained at every window below
`P²`, so no Type-II input reaches any `θ > 1`); `V:ExactTypeIILossOfTheReceiverGram` (exact loss
`Θ(N²/X)`); `V:TypeIIBarrierSurvivesTheRankTwoSideConditions` (killing both harmonic and `Λ` readouts
leaves `B(c, c') ≥ (Σc(d)d)(Σ|c'|/n²)/200` on coherent/anti-coherent windows);
`V:CoherentNearMultipleObstructionToCrossScaleDispersion` (the rank-two plus large-sieve threshold
`Q ≥ P^{5/3}` is sharp up to `√log`); `V:CrossScaleParityBlindnessOfThePronicGram` (the cross-scale Gram
sees the large scale only through residue masses mod the small moduli plus two readouts: it is
parity-blind). What is reached: the unbalanced regime `Q ≥ P²` by the exact rank-two law
(`V:ExactRankTwoCrossScaleLawOfTheReceiverGram`); diagonal quality for `Q ≥ P^{5/3}` with arbitrary
coefficients at one modulus (`V:LargeSieveDispersionOfTheCrossScaleRemainder`,
`V:LargeSieveDispersionInSelbergCoordinates`, `V:LargeSieveDispersionForBoundedRows`); Type-I gains,
flat rows at either scale reaching `θ ≤ 4/3` and smooth large-scale rows `θ ≤ 3/2`
(`V:KuzminLandauGainForFlatSmallScaleRows`, `V:FlatLargeScaleRowsAndTheTypeIGain`,
`V:SmoothLargeScaleRowsAndTheCancellationOfBothKernels`); bounded partial sums giving receiver-quality
dispersion `Q_N(c) ≤ 11B² + 4Σc_n²/n` (`V:SummatoryFunctionBoundForTheDyadicPronicGram`); the exact
second- and third-order cross-scale laws with the Bernoulli kernels `𝔅`, `𝔅₃`, their reciprocity form
in Kloosterman fractions `kq̄/p` with cosecant–Bernoulli weights, and the signed residue law
(`V:SecondOrderCrossScaleLawAndTheBernoulliKernel`, `V:ThirdOrderCrossScaleLawAndTheCubicBernoulliKernel`,
`V:ReciprocityFormOfTheBernoulliKernel`, `V:TwoSidedSignLawOfTheSecondOrderKernel`,
`V:SharpConstantAttainedByPrimesInTheUnitClass`). Replacement hypotheses proved sufficient: block
equidistribution of the large-scale row at scale `H = o(P/log²P)`
(`V:BlockEquidistributionSufficesForCrossScaleDispersion`); twisted short-interval square-root
cancellation over prime intervals of length `4P²/(aK)` (`V:TwistedShortIntervalCancellationGivesWindowDispersion`,
with the window spectrum and numerator split `V:DiscreteGallagherInequalityAndTheWindowSpectrum`,
`V:NumeratorSplitOfTheWindowEnergy`, `V:OneNumeratorClustersAreShortIntervalSums`); and the exact
residue discrepancy `Δ_p(c')` at rate `π²/72` (`V:ResidueDiscrepancyIsTheExactCrossScaleLoss`). The
dual norm reduces every Type-II bound for bounded small-scale coefficients to the single-modulus
statistics `Σ_{p∈S}|Λ_p(c')|/p`, low-frequency exponential sums `Σ_a W_p(a)Σ_n (c'(n)/n²)e(an/p)` of the
large-scale row, with no bilinear structure left (`V:DualNormOfTheCrossScaleFunctional` [L]).

**Rule.** A dispersion claim on the pronic Gram must say which coefficient class it covers and at
which exponent; `ℓ²` classes stop at `θ = 1` by the coherent-block law, Type-I classes at `θ ≤ 3/2`.
The receiver needs cancellation of the actual Möbius or prime row at `θ = 2`, that is, of the
single-modulus low-frequency statistics of an arithmetic row, with the signs of Wall 16 read.

## How the walls bind the routes

| Wall | Routes it binds | Status and the open unit |
|---|---|---|
| 1 The zero width (faces 1.1–1.5) | 1.1: WL, MC, PM, CTF, PBM, RB, FU, RP, LI, SRT, CHMD (discrepancy pairing); BVI, EGC, DR, MSC. 1.2: LA, TT, TH, HCF, XN, SZ, HJ, SEC, DR. 1.3 and 1.4: RW, HF, CHMD, EWU, OWU, PA, TH, HCF, TG, WD, LI, SZ, ACT, AIP, MC, BVI, RB, BiScale, all candidates. 1.5: PA, SZ, PM, CTF, BAG, FEL | [L]. One open unit in five currencies: the lag `V` beyond which `P_v ≥ 0`, the window remainder below `O(e^{L/2})`, the aperture through which `μ(A) ≥ 0` for all profiles, the Báez-Duarte residual below `κ/log N`, the heat time below `1/8`; every graded improvement of one face is `zetaZeroWidth ≤ σ` and transfers to the others by the dictionary, the one direction not transferred being width ⟹ ground-energy floor. Best unconditional, at Vinogradov–Korobov strength for every `ex < 3/5`: `P_v ≥ −|φ(0)| − Ce^{v/2−v^ex}` (`Q:ZetaLagFamilyVinogradovKorobovEnvelope` [L]); `|c(L) − e^{L/2}| ≤ Ce^{L/2−κL^ex}`, `|floor(L) + e^{L/2}| ≤ Ce^{L/2−κL^ex}` and `|D(T)| ≤ Ce^{T−κT^ex}` for the integrated Chebyshev deficit (`B:PrimeWindowCeilingVinogradovKorobovRemainder` [L]: the polar Schur bound holds for every nonincreasing error profile `E` with gain `E(L/4) + e^{−L/4}`, so the window remainder carries exactly the strength of the prime number theorem that enters; the polar weight loses at the midpoint only against power errors); explicit-constant de la Vallée Poussin forms `Q:ZetaLagFamilyUnconditionalEnvelope`, `B:PrimeWindowCeilingDeLaValleePoussinRemainder` [L]; `μ(A) ≥ 1/5000` through `3/10` on all profiles [L]; `newmanConstant ∈ [0, 1/8]`; residual floor `κ/log N` on every finite row. Contact aperture: a near-top zero `½ + z₀` with data `(w, η, V ≥ V₀(w, η, Re z₀))` makes `μ(A) < 0` for every `A ≥ V/2 + w`. |
| 3 Local clustering | LA, TH, HCF, XN, WD, JAS, SRT | [L]. Lag side: hiding needs collapsed clusters; the pair-correlation barrier remains. |
| 5 No Frobenius | HF, IRK, PTR, W1C, TG | [L]; purity `|ω| = √q` not formalized. |
| 6 Probability cone | PA, JAS, PBM, DR, WBF; PM/BVI at `ε > 1/2` | [L]. |
| 7 Almost all versus all | BAG, JAS, LA, WL, MC, FU, TT, HCF, GTA, EWJ, FEL, PCS, RFHM; SRT grids | [L]. BAG closed on zero-free discs; SRT attainment replaced by the horizon condition. |
| 8 Admixture | RW, EWU, OWU, HF | [L]. |
| 9 Temperedness gate | every positivity route; RB | [L]. Window positivity is selective against large shifts; Beurling selectivity untested. |
| 10 Oscillation–transport | WL, MC, FU, RP, LI, PBM, PM, CTF, RN, EGC | [L]. |
| 13 Cone mismatch | RW, HF, EWU, OWU, CHMD, TT, RN, ACT, AIP, MSC | [L]. Pointwise/Schur certificates reach `3/10` (all) and `353/1000` (odd). |
| 14 Size law | FU, RP, TG, RN, SZ, HF, CHMD, OWU, APF, EWJ, PCS, IRK, SC, SEC, PTR, W1C, WBF | [L]. CCM's finite-aperture realization is unconditional; convergence to `Ξ` is the premise. |
| 15 Support versus positivity | TT, WD, XN, TG, RN, HF, CHMD, OWU, ACT, AIP, BSH, CDC, HJ, IRK, FEL, RFHM, SC, SEC, PTR, W1C, EGC | [L]. |
| 16 Parity at half damping | PM, MC, CTF, BVI, THIM | [L]. Sharp at `ε = 1/2`; separating observables classified. |
| 17 Coherent blocks | BVI, MC, PM, CTF | [L]. Type-II `ℓ²` stops at `θ = 1`, Type-I at `3/2`; receiver at `θ = 2`. |

A new mechanism has to supply one of: square-root cancellation of a prime sum at one modulus with
the signs read (face 1.1, Walls 16, 17); equality in Jensen for `log|ζ|` (face 1.5); a Frobenius-type
fibration (Wall 5); a Bochner-cone positivity certificate at arbitrary support compatible with node
criticality (face 1.4, Wall 13); or a definite spectral realization of the zeros whose prime part is
as large as `S(T)` and whose finite-aperture ground transforms converge to `Ξ` (faces 1.3, 1.4, Wall
14). The first, second, fourth and fifth are the statement `zetaZeroWidth = 0` in four of the
currencies of Wall 1; the kills recorded in the [retired-mechanism ledger](../rh-killed-routes.md) are
rediscoveries of these walls.
