# The route unification ledger

The [route ledger](../rh-current-frontier-map.md) lists thirty live routes and seventeen standalone
candidates. Read against the Lean corpus, they are far fewer: a route is fixed by the quantity its
receiver measures, not by the language in which it is stated, and the corpus proves that most
receivers measure one of three graded quantities. This ledger records the clusters, the proved
dictionaries that identify their members, the readings that are one-directional or endpoint-only,
and the arrows that are missing. It is the companion of the [walls ledger](walls-ledger.md): what
that ledger does for obstacles (Wall 1 is one number in six languages), this one does for routes.
Companion documents: [per-route obstacles](hard-obstacles.md), [summary and the missing
field](hard-obstacles-summary.md).

**Lean checkpoint** `9e1fa313a`. Evidence tags: [L] = committed Lean declaration imported by its
committed umbrella; [S] = Lean source in the working tree whose file or umbrella import is
uncommitted; [P] = paper only. Module paths are relative to `formal/GaloisForLFunctions/`, with
`R:` = `RHTower/`, `B:` = `BiScaleUncertainty/`, `V:` = `BezoutValuationIncidence/`,
`T:` = `TransHorizonIncidenceMechanics/`, `A:` = `arithmetic-positivity-theory/`,
`C:` = `ArithmeticCriticalityTheory/`, `I:` = `ArithmeticIncidencePositivity/`,
`Q:` = `SquareRootThreshold/`. Working-tree [S] items: the three dictionary modules
`Q:TheRoutesMeasureOneAperture`, `Q:TheRoutesMeasureOneZeroWidth`,
`Q:TheZeroIndexedRoutesMeasureOneSide` (files and umbrella imports uncommitted; every theorem closed,
standard axioms), `Q:TheZeroWidthIsALandauExponent` and `Q:TheZeroWidthIsAnUnboundedApertureProperty`
(same status), and the rename of the duplicate declaration `RHTower.norm_mobiusMertensPartialSum_eq`
of `R:LiouvilleSummatoryRH` (now `norm_mobiusMertensPartialSum_eq_abs_sourcePartialSum_moebiusR`, its
consumer `R:SignedArithmeticAbscissaRH` updated), which collided with the declaration of the same
name in `R:CausalMobiusThetaTail` inside the `RHTower` umbrella.

## The principle: a route is its unit

Every receiver of a route is a statement about one of three quantities, and the corpus proves the
equivalence of the receivers that read the same quantity:

- the **zero width** `zetaZeroWidth = sup |Re ρ − ½| = Θ − ½` (the number of Wall 1), read by the
  prime-side and zero-side routes as an exponent, an abscissa, a zero-free region or a real-rooting
  threshold;
- the **aperture** `A` through which the full zero form `Ẑ(F) = Re W_ζ(F, F)` is nonnegative on every
  real `C²` test supported in `[−A, A]` (the unit of face 1.3), read by the positivity routes as a
  ground energy, a variation inequality, a capacity inequality, a blind minimum, a window
  certificate or a lag functional;
- the **side** of one zero, `Re ρ = ½`, read by the zero-indexed candidates through per-zero
  indicators.

Two further families carry no graded dictionary and are grouped by what their receivers share: the
damped Möbius receiver (damping `ε` and Gram exponent `θ` as units) and the almost-all routes (the
quantifier gap of face 1.6). The three units are linked only by the arrows recorded at the end: a
certificate at one aperture says nothing about the width
(`Q:TheZeroWidthIsAnUnboundedApertureProperty` [S]), a floor on the ground energy at every large
aperture bounds the width (face 1.3), and the converse is the open arrow of the width dictionary.
Progress is counted once per unit, in the unit's own currency, and identities count as zero.

| Cluster | Unit | Live routes | Candidates | Dictionary |
|---|---|---|---|---|
| A, the width | `zetaZeroWidth ≤ σ` | WL, MC, PBM, SZ, TT, TH, HCF, PA, BAG, HF (window ceiling), SRT (minimal), FU, RW/HF (source tomography); endpoint only: LA, WD, XN, LI, RB, CTF, PM | DR, EGC, FEL | `Q:TheWallsMeasureOneZeroWidth` [L], `Q:TheRoutesMeasureOneZeroWidth` [S], `Q:TheZeroWidthIsALandauExponent` [S] |
| B, the aperture | `ZetaWindowPositive A` | RW, ACT, OWU, EWU, SRT (window, lag), TT (odd sector), JAS (level one), HF (prime-blind), CHMD (odd bound states) | AIP, APT windows | `Q:TheRoutesMeasureOneAperture` [S] |
| C, the side | `Re ρ = ½` per zero | TG, RN, GTA, XN, WD (zero-indexed receivers) | HJ, SEC, CDC, BSH, IRK, W1C, PCS, PTR, APF, EWJ, SC, RFHM, WBF, EGC | `Q:TheZeroIndexedRoutesMeasureOneSide` [S], `R:XiZeroLocalCriticalPhaseUniversalityLaw` [L] |
| D, the receiver | damping `ε`, Gram exponent `θ` | MC, PM, CTF, FU, RP, LI | MSC, BVI | `T:MoebiusAndLiouvilleReceiversAreEquivalent`, `V:PronicBaezDuarteCriterion`, Wall 16 [L] |
| E, the quantifier gap | density one versus all | BAG, JAS, LA, WL, MC, SRT (grids) | EWJ, FEL, PCS, RFHM | face 1.6 [L] |

## Cluster A: the width routes

**One number.** `zetaZeroWidth = zetaZeroAbscissa − ½`, and for `σ ≥ 0` the statements
`zetaZeroWidth ≤ σ`, `Θ ≤ ½ + σ`, `XiZeroHalfPlaneBound σ` and `∀ ρ, Re ρ ≤ ½ + σ` are one statement
(`Q:TheWallsMeasureOneZeroWidth` [L]). Every reading below is an equivalence with `zetaZeroWidth ≤ σ`
unless marked as one-directional or endpoint-only; the module of each new reading is
`Q:TheRoutesMeasureOneZeroWidth` [S], a composition of the width dictionary with a receiver the corpus
proves for `XiZeroHalfPlaneBound σ`.

| Route | Reading of `zetaZeroWidth ≤ σ` | Theorem | Source receiver |
|---|---|---|---|
| WL | one-sided deficit bound `D(T) ≤ B(1 + T)e^{(½+β)T}` for every `β > σ`; mean-square, Laplace and spectral band rates; one-sided packet growth at exponent `σ` for every `C²_c` test; the spline-weighted prime inequality at exponent `1 + σ`; abscissa of `Σ(Λ(n) − 1)n^{−s}` | `zetaZeroWidth_le_iff_forall_deficitPrimitive_le`, `…_meanSquareBandRate` [L]; `zetaZeroWidth_le_iff_forall_packet_upper`, `zetaZeroWidth_le_iff_spline_prime_sum_le`, `zetaZeroWidth_le_iff_vonMangoldtMinusOne_converges` [S] | `B:PacketOneSidedGrowthLaw`, `B:CubicSplineUniversalProbe`, `R:VonMangoldtMinusOneAbscissa` [L] |
| MC | infimum of the Möbius–divisor Abel energy exponents is `1 + 2·zetaZeroWidth`; the dyadic weighted prime-window power bound at exponent `σ` | `one_add_two_mul_zetaZeroWidth_eq_sInf_…` [L]; `zetaZeroWidth_le_iff_exists_dyadicWeightedPrimeWindowPowerUpper` [S] | `R:QuasiRHMeanSquareAbscissa`, `R:CCMGeneralizedVonKoch` [L] |
| PBM, DR | `Σ((Λ(n) − 1)/log n)n^{−s}` and `Σ(1_ℙ(n) − 1/log n)n^{−s}` converge at every real `s > ½ + σ` | `zetaZeroWidth_le_iff_logZetaRegCoeff_converges`, `zetaZeroWidth_le_iff_primeRegCoeff_converges` [S] | `R:RegularizedLogZetaAbscissa` [L] |
| SZ | zero-freeness right of Suzuki's shifted line; completed formation energy subpower at exponent `1 + 2σ` | `zetaZeroWidth_le_iff_suzukiZetaZeroFreeRightOf` [S]; `zetaZeroWidth_le_iff_suzukiCompletedFormationEnergy_subpower` [L] | `R:SuzukiLagariasMeromorphicInner` [L] |
| TT | natural Wold energy finite at every radius `t < ½ − σ`; raw directed covariance bounded above at every such radius (`σ < ½`) | `zetaZeroWidth_le_iff_forall_woldNatResidualSquareEnergy`, `zetaZeroWidth_le_iff_forall_directedCovariance_bddAbove` [S] | `R:PaperWoldDirectedCovarianceWidthSpectrum` [L] |
| HCF | the complete Gaussian Hedenmalm Hankel tail cone above `σ` at any temperature | `zetaZeroWidth_le_iff_hedenmalmGaussianHankelTailCone` [S] | `R:HedenmalmGaussianHankelApertureWidthSpectrum` [L] |
| TH | thermal projective moments bounded by the zeroth mass times `σ^m` | `zetaZeroWidth_le_iff_forall_thermalProjectiveMoment_le` [S] | `R:XiThermalProjectiveMomentSpectrum` [L] |
| PA | vertical type of the canonical Poisson trace at most `σ` | `zetaZeroWidth_le_iff_xiPoissonTraceVerticalTypeAtMost` [S] | `R:XiSpectralApertureConservationUniversalityLaw` [L] |
| RW, HF | critical Mellin defect and inverse-tilted dyadic source holomorphic above `½ + σ` | `zetaZeroWidth_le_iff_criticalMellinDefectAnalyticAbove`, `…_inverseTiltedDyadicSourceAnalyticAbove` [S] | `R:CCMSourceDivisorEnergySpectrum` [L] |
| HF (window) | window excess exponent pinched: `zetaZeroWidth ≤ θ* ≤ zetaZeroWidth/2 + ¼` | `zetaZeroWidth_le_windowCeilingExcessExponent`, `windowCeilingExcessExponent_le_half_zetaZeroWidth_add_quarter` [L] | `B:PrimeWindowCeilingWidthLaw` [L] |
| SRT (minimal) | lag family `≥ −Ce^{σv}` at all large lags (generic width); grid form up to attained tops | `zetaZeroWidth_le_iff_lag_primeWindow_ge_neg_exp`, `zetaZeroWidth_le_iff_attainedTop_and_grid_primeWindow_ge_neg_exp` [L] | `Q:OneParameterLagFamilyMeasuresTheAbscissa`, `Q:LagGridsAndTransportLawsReadTheZeroWidth` [L] |
| BAG | every point of the strip right of `½ + σ` carries a closed disc on which `ζ` is strongly recurrent | `zetaZeroWidth_le_iff_forall_exists_zetaDiscStronglyRecurrentOn` [S] | `R:ZetaRecurrenceAtEveryPointModuloItsZeros` [L] |
| the divisor | the projective reflection radius of the Xi divisor is the width | `zetaZeroWidth_eq_xiProjectiveReflectionRadius` [S] | `R:XiProjectiveReflectionSourceTemperatureSpectrum` [L] |
| FU | one-sided power bounds on the completed Abel moment give `Θ ≤ ½ + max(0, c)` (one direction) | route ledger [L] | — |
| LA, XN, WD | one direction: Lagarias at width `σ`, `Re(ξ'/ξ)(s) ≥ 0` for `Re s > ½ + σ`, `ξ(s) ≠ 0` | `re_logDeriv_xi_nonneg_of_zetaZeroWidth_le` [S] | `R:XiLogDerivReStripBound` [L] |
| LA, TT, SZ, TH, HCF | one direction: `cos(hD)Ξ` is Laguerre–Pólya for every `h > zetaZeroWidth`; heat time `newmanConstant ≤ zetaZeroWidth²/2` | `laguerrePolya_cosineShiftXi_of_zetaZeroWidth_lt` [S]; `newmanConstant_le_half_sq_zetaZeroWidth` [L] | `R:XiCosineShiftLaguerrePolya`, `Q:LagRateBoundsTheDeBruijnNewmanHeatTime` [L] |

**Endpoint-only readings.** The following receivers are RH at the endpoint and carry no exponent:
the Balazard–Saias–Yor integral and its Blaschke floor on the Báez-Duarte residual (PA, FEL, CTF, PM;
face 1.5), Li positivity (LI), Robin and Nicolas (RB), `d_N → 0` (CTF, PM), the de Bruijn–Newman
constant (LA, WD: `zetaZeroWidth = 0 ⟺ newmanConstant = 0`), the Krein chamber (`R:KreinChamberIsLagarias`),
the Ward cap and the Newton discs (WD, XN). Each zero right of the line contributes to them with a
weight that decays with its height, so no exponent exists; their graded form is the width through
the one-directional readings above. The Landau-exponent form of the whole cluster, `zetaZeroWidth`
as the infimum of the admissible rates of the lag family, the deficit and the band, is
`Q:TheZeroWidthIsALandauExponent` [S].

**What the cluster says.** WL, MC, PBM, SZ, TT, TH, HCF, PA, BAG, the window face of HF and the
minimal receiver of SRT are one route: a one-sided bound at exponent `σ` on their respective
quantities is `zetaZeroWidth ≤ σ`, and an improvement of any of them below the Vinogradov–Korobov
strength `exp(−c(log x)^{3/5})` is an improvement of all of them. DR's receiver is PBM's. The routes
differ in their producers, the prime quantity each proposes to bound, and nowhere in what they
would prove.

## Cluster B: the aperture routes

**One predicate.** `ZetaWindowPositive A`: `Ẑ(F) ≥ 0` for every real `C²_c` test vanishing outside
`[−A, A]`; `ZetaEvenWindowPositive A` and `ZetaOddWindowPositive A` are its parity sectors. The
dictionary is `Q:TheRoutesMeasureOneAperture` [S].

- *RW is window positivity.* `0 ≤ μ(A)` iff `ZetaWindowPositive A'` for every `0 < A' < A`
  (`ccmRestrictedWeilGroundEnergy_nonneg_iff_forall_lt_zetaWindowPositive`); window positivity at the
  closed aperture gives `0 ≤ μ(A)` (`ccmRestrictedWeilGroundEnergy_nonneg_of_zetaWindowPositive`), and
  `0 ≤ μ(A)` gives `Ẑ ≥ 0` on smooth sources compactly inside `(−A, A)`
  (`fullZeroForm_nonneg_of_ccmRestrictedWeilGroundEnergy_nonneg`). The passage from smooth interior
  sources to `C²` window tests is the continuity of the complete Weil energy under mollification
  (`A:FactorialRampFullWeilSmoothingLimit` [L]) and the mollification radius `1/(4(k+1))`; the passage
  from all smaller apertures to `A` itself is Suzuki's continuity of `μ`
  (`R:SuzukiGroundEnergyContinuity` [L]).
- *Parity.* `ZetaWindowPositive A ⟺ ZetaEvenWindowPositive A ∧ ZetaOddWindowPositive A`
  (`zetaWindowPositive_iff_even_and_odd`; `Ẑ(F) = Ẑ(F_e) + Ẑ(F_o)`).
- *OWU is the odd window.* `ZetaOddWindowPositive A` iff every odd window test satisfies the
  capacity inequality `sinhPairing g² ≤ 2·markovForm N g` at the prime cutoff `N = ⌈e^{2A}⌉`
  (`zetaOddWindowPositive_iff_sinhCapacity`).
- *ACT is paid by the odd window.* The ACT test `Φ(ω_a u)` of an even profile is an odd window test,
  and on odd tests the pole term is `−2|F̂(i/2)|² ≤ 0`, so the pole-free Markov energy dominates `Ẑ`
  (`shiftedGroundState_markovEnergy_nonneg_of_zetaOddWindowPositive`): at a fixed aperture the odd
  window implies the single-shift inequality; the converse at fixed aperture is not available, and
  both are RH over all apertures (`C:SingleShiftCompleteness` [L]).
- *EWU is dominated.* `0 ≤ μ(A)` gives `0 ≤ evenBlindMinimum A`
  (`evenBlindMinimum_nonneg_of_ccmRestrictedWeilGroundEnergy_nonneg`, the dominance chain of
  `R:EvenSectorBlindMinimumSmallAperturePositivity` [L]); the blind minimum reads only the blind tests,
  so the converse at fixed aperture is open, and the two agree at the endpoint
  (`riemannHypothesis_iff_forall_evenBlindMinimum_nonneg` [L]).
- *SRT's window and lag.* The real window transfers to complex tests of the same aperture and back
  (`re_W_nonneg_of_zetaWindowPositive`, `zetaWindowPositive_of_re_W_nonneg`), and
  `0 ≤ μ(v/2 + w)` gives `0 ≤ Re P_{w,v}` by the Rayleigh bridge
  (`re_lagPrimeWindowRHS_nonneg_of_ccmRestrictedWeilGroundEnergy_nonneg`;
  `Q:GroundEnergyAbscissaAndLagGridAttainmentBridge` [L]).
- *Endpoint.* RH iff every aperture is window positive iff every ground energy is nonnegative
  (`riemannHypothesis_iff_forall_zetaWindowPositive`,
  `riemannHypothesis_iff_forall_ccmRestrictedWeilGroundEnergy_nonneg`); the collected statement is
  `theRoutesMeasureOneAperture`.

**Readings of the same unit already in the corpus** [L]. AIP and APT prove window certificates
`Ẑ(F) ≥ c∫F²` directly in the predicate's own language (`C:ThreeTenthsSharpGaugeWeilPositivity`,
`I:OddWindowPastFirstPrime`, `I:SharpFoldOddWindowPastSevenTwentieths`); the common compact core of
SZ, RW and CHMD is one quadratic form (`R:SuzukiCCMMixedScrewWeilBridge`); TT's odd positivity is
OWU's; JAS's level-one positivity is the arithmetic prime-product form of the same functional. HF's
prime-blind positivity is the same form graded by the node set rather than by the aperture
(`ZeroPoleBlindPositiveOn N ⟺ RH ∧ PP ⊆ N`, face 1.4), and CHMD's odd bound-state space is graded by
the number of off-line zeros (`R:CrossRouteReceiverBridges`); neither is an aperture reading.

**What the cluster says.** The unit of RW, ACT, OWU, EWU, AIP, APT and the window face of SRT is
the aperture `A` through which `ZetaWindowPositive A` is proved: `3/10` on all profiles
(`μ(3/10) ≥ 1/5000`), `353/1000` on the odd sector, both selective against the shifted pair. By the
dictionary these are the same certificate in every language: the ground energy floor, the capacity
inequality on odd tests through `353/1000`, the EWU blind minimum through `3/10`, the complex window
of SRT through `3/10`, and the lag functional at the lags `v ≤ 2(3/10 − w)`. The open unit of the
cluster is one: the even sector through the first prime window, where the folded conductances
across `log 2` turn negative (Wall 13), and the no-crossing of `μ` beyond it.

## Cluster C: the zero-indexed candidates

**One Boolean.** At every point `ρ` of the Xi divisor the following are the statement `Re ρ = ½`
(`theZeroIndexedRoutesMeasureOneSide`, `Q:TheZeroIndexedRoutesMeasureOneSide` [S]): the vanishing of
the Hurwitz two-seed residual `2^{ρ−2} − 2^{−ρ̄−1}` (HJ), of the first-prime seam charge and of the
Hurwitz orientation defect (HJ, SEC), the time-one Gamma factorial-Fock jet boundedness at any safe
base point (SEC), the radially calibrated dagger confluence (CDC), the Deninger half-density mate
gain being one (BSH), the non-invertibility of the completed rotation-algebra relation (IRK), and
the reality of the weight-one Clifford energy (W1C). Each global form is RH
(`riemannHypothesis_iff_forall_xiDivisorSupport_of_indicator` and its instances). The Berry–Keating,
prime-clock, prime-mark, Arakelov, finite-unitary and Gamma–Mertens charts of the same Boolean are
`R:XiZeroLocalCriticalPhaseUniversalityLaw` [L]; PCS's reflection-odd wall class
(`xiReflectionOddPrimeCoShiftClassVanishes_iff_riemannHypothesis`,
`R:PrimeCoShiftReflectionOddSingularCohomology` [L]) and PTR's lossless-stack limit
(`riemannHypothesis_iff_XiC_limit_losslessProductPort`, `R:PhotonicLosslessProductPortRH` [L]) are
global forms whose per-zero `iff` is not stated; APF, EWJ, SC, RFHM, WBF, EGC, TG, RN and GTA are of
the same family without a per-zero indicator in the corpus.

**What the cluster says.** HJ, SEC, CDC, BSH, IRK, W1C, PCS and PTR are one route, the per-zero
orientation, and its open unit is the same in every language: the production of the indicator's sign
from the prime source before the zero is known (the O6 family of the summary; Wall 15, Wall 14). A
construction that evaluates its indicator on `XiDivisorSupport` has already assumed the side it wants
to prove; the dictionary shows that changing the indicator changes nothing.

## Cluster D: the damped Möbius receiver

MC, PM (FZZ-P), CTF and the supporting framework BVI share one receiver, the pronic energy of the
centred prefix of `c ∗ 1` on the damped class, with two units: the damping `ε` (bounded at `ε = ½`,
needed at every `ε > 0`) and the Gram exponent `θ` (`ℓ²` Type-II classes stop at `1`, Type-I at
`3/2`, the receiver at `2`). The identifications are [L]: Möbius and Liouville receivers are
equivalent at every damping (`T:MoebiusAndLiouvilleReceiversAreEquivalent`); the Báez-Duarte residual
is `(1 − Λ-readout)² + centred pronic Gram` with floor `κ/log N` (`V:PronicBaezDuarteCriterion`); the
FZZ-P Haar approximation is RH-equivalent and is implied by horizon-uniform pronic energy at a
cofinal sequence of dampings; the zero-translation law at one fixed damping. FU and RP (completed
Abel moment, history floor) and LI (paired Li history) share the history structure and the
one-sided-bound receiver of face 1.1, but their quantities are not the pronic energy. This cluster is
not graded by the width: admission at one damping `ε ∈ (0, ½)` gives the translation closure
`ζ(ρ) = 0, Re ρ > ½ + ε ⟹ ζ(ρ − ε) = 0` and bounds no width (Wall 16), while the cumulative
mean-square exponent of the normalized Abel action is `2Θ` (`R:QuasiRHMeanSquareAbscissa` [L]), which
puts the *energy* reading of MC in cluster A. The cluster's open unit is the single-modulus signed
statistic of the Möbius row at `θ = 2` with the signs of Wall 16 read.

## Cluster E: the quantifier gap

BAG, JAS, the near-double pairs of LA, the exceptional lags of WL and MC, and the grid form of SRT
share no object and one gap: a statement true at density one must become true everywhere (face
1.6). BAG is the clearest case and is now also a width reading: recurrence on a disc about `z₀` is
exactly `ζ(z₀) ≠ 0` (`R:ZetaRecurrenceAtEveryPointModuloItsZeros` [L]), so BAG's remaining
statement is "exclude a zero from the disc" and its graded form is cluster A's
`zetaZeroWidth_le_iff_forall_exists_zetaDiscStronglyRecurrentOn` [S]. For the lag grids the gap is
the attained top (`Q:LagGridsSeeAttainedTops` [L]); for the continuum lag family it is the horizon
condition (`Q:OneParameterLagFamilyHorizonLaw` [L]).

## The arrows between the units

- *Aperture to width.* A floor `μ(A) ≥ −Ce^{2σA}` at all large apertures gives `zetaZeroWidth ≤ σ`
  and the lag floor at rate `σ` (face 1.3, `Q:TheWallsMeasureOneZeroWidth` [L]); the exponent form is
  `zetaZeroWidth ≤ polarGroundEnergyRate` (`Q:TheZeroWidthIsALandauExponent` [S]). A certificate at
  one bounded aperture, however large, is consistent with every width
  (`Q:TheZeroWidthIsAnUnboundedApertureProperty` [S]).
- *Width to aperture, open.* `zetaZeroWidth ≤ σ ⟹ μ(A) ≥ −Ce^{2σA}` for `σ > 0` is the open arrow
  of the width dictionary; at `σ = 0` it is `RH ⟹ μ ≥ 0`, proved.
- *Side to width.* `RH ⟺ ∀ ρ, Re ρ = ½` is the endpoint of both; no graded per-zero reading
  exists, because a single off-line zero already breaks every indicator.
- *Receiver to width.* The damping unit does not bound the width (Wall 16); the energy exponent of
  the Abel action does (cluster A).

## Not the same route

Pairs that look alike and are not, with the theorem that separates them:

- ACT's single-shift inequality at aperture `A` and OWU's capacity inequality at aperture `A`
  differ by the pole term `−2|F̂(i/2)|²` on odd tests: OWU implies ACT at every aperture, the
  converse holds only at the endpoint (`shiftedGroundState_markovEnergy_nonneg_of_zetaOddWindowPositive` [S],
  `C:SingleShiftCompleteness` [L]).
- EWU's blind minimum at aperture `A` and RW's ground energy at aperture `A` differ by the blind
  restriction: `μ(A) ≤ evenBlindMinimum A`, equality of signs only at the endpoint [L].
- HF's prime-blind positivity on a node set and the aperture: the first is graded by the support
  of the weight, the second by the support of the test (face 1.4).
- CHMD's odd bound-state dimension and the width: the first counts off-line zeros, the second
  measures their depth (`R:CrossRouteReceiverBridges` [L]).
- PM's admission at a fixed damping and the width: the first gives the translation closure, not a
  half-plane (Wall 16).
- The lag reading of an aperture certificate: `μ(v/2 + w) ≥ 0` gives `P_v ≥ 0` only for
  `v ≤ 2(A − w)`; the lag unit of SRT is the lag `V` beyond which `P_v ≥ 0`, which no aperture
  certificate reaches.

## The merge

Counting routes by their units, the thirty live routes and seventeen candidates are seven:

| Unified route | Members | Open unit, in the unit's currency |
|---|---|---|
| The width (A) | WL, MC (energy), PBM, SZ, TT, TH, HCF, PA, BAG, FU, HF (window), SRT (minimal), DR; endpoint members LA, WD, XN, LI, RB, CTF, PM, FEL, EGC | `zetaZeroWidth = 0`; best unconditional reading of every member: Vinogradov–Korobov strength, no power |
| The aperture (B) | RW, ACT, OWU, EWU, AIP, APT, SRT (window, lag), TT (odd), JAS (level one), SZ (common core), CHMD (odd eigenstates), HF (prime-blind) | `ZetaWindowPositive A` for all `A`; proved through `3/10` (all profiles), `353/1000` (odd) |
| The side (C) | HJ, SEC, CDC, BSH, IRK, W1C, PCS, PTR; APF, EWJ, SC, RFHM, WBF, EGC, TG, RN, GTA, XN, WD as zero-indexed constructions | a source-defined indicator evaluated before the divisor |
| The receiver (D) | MC (receiver), PM, CTF, BVI, MSC; FU, RP, LI by history | bounded receiver at every damping; signed single-modulus statistic at `θ = 2` |
| The quantifier gap (E) | BAG, JAS, LA (pairs), SRT (grids) | the step from density one to every height |
| The arithmetic realization | HF (cohomology), RN, TG, PTR, W1C, IRK, APF, SC, WBF as constructions | a space, operator or geometry producing the primes with the right trace (Walls 5, 14) |
| The orientation of currents | WD, XN, TT (Cassini), GTA, LA (Jensen), RN | a reflection-odd sign from reflection-even data (Wall 15) |

The last two are families of constructions rather than receivers and overlap with clusters A–C in
their receivers; they are listed because their open units are constructions, not estimates. A route
appears under several headings when its receiver reads several units; what the table rules out is a
route whose receiver reads none of them. No merge changes a route's producer, and the route ledger
is the record of producers; this ledger is the record of what the producers would prove.

## Open arrows of the dictionaries

- The graded converse of EWU at fixed aperture (`0 ≤ evenBlindMinimum A ⟹ ZetaEvenWindowPositive A'`).
- The graded converse of ACT at fixed aperture, or a proof that the pole term separates them at
  some aperture.
- Per-zero `iff` forms for PCS and PTR; any per-zero indicator for APF, EWJ, SC, RFHM, WBF, EGC.
- Graded readings of Robin, Li and the Báez-Duarte residual: none exists, because their weights
  decay with the height of the zero; the obstruction is face 1.5.
- The converse of Lagarias at width `σ` (`Re(ξ'/ξ) ≥ 0` on `Re s > ½ + σ ⟹ zetaZeroWidth ≤ σ`)
  and of the cosine-shift law (`cos(hD)Ξ` Laguerre–Pólya ⟹ `zetaZeroWidth ≤ h`).
- The open arrow of the width dictionary, width to ground-energy floor, which is the only arrow
  whose closure would be progress on RH rather than on the ledger.
