# The walls ledger

Fifteen named obstructions on which direct attacks on the Riemann hypothesis have died, each with
the mechanism, the exact place where unconditional methods stop, concrete appearances in the Lean
corpus, and the practical rule. The wall names and numbers come from the loop logs
(`rh-goal-loop-opus-2026-09-29.md` rows 341–376 for walls 1–10, `producer-loop-opus-2026-10-12.md`
rows 239–451 and `jas-goal-loop-2026-10-09.md` rows 337–388 for walls 11–15). Every Lean module
named below exists in the working tree and is imported by its committed umbrella, except where a
module is tagged [S] (source present, not umbrella-imported) or a statement is recorded as paper
only. Module paths are relative to `formal/GaloisForLFunctions/`.

Two general facts frame all of them. First, the corpus proves that every intermediate relaxation on
the surveyed routes is a zero-free half-plane or a finite-height verification (route-ladder survey,
rows 371–376), so "weaker than RH" producer targets do not exist. Second, a new attempt should name
the wall it passes and the concrete input that passes it before anything is built.

## Wall 1: the square-root barrier in prime counting

Every producer route eventually needs an unconditional statement of the form "a prime or Möbius sum
up to x has error of size x^{1/2+ε}". That statement is RH itself. Equivalent forms:
ψ(x) − x = O(x^{1/2+ε}), or M(x) = Σ_{n≤x} μ(n) = O(x^{1/2+ε}), or Σ_{n≤x} μ(n)/n = O(x^{−1/2+ε}).
Each implies RH by the Mellin integral (Landau), and RH implies each by the explicit formula.

Everything unconditional stops far short of this. Sieves, the de la Vallée Poussin and
Vinogradov–Korobov zero-free regions, and exponential-sum methods give savings of the shape
exp(−c (log x)^{3/5}), weaker than any power saving. A power saving x^{θ} with θ < 1 is already a
zero-free half-plane Re s > θ, and no such half-plane is known. One-sided producers, such as Robin's,
Nicolas's and Lagarias's inequalities or sieve-weight positivity, need the full exponent 1/2 before
they trigger at all; the parity barrier forbids lower-bound sieves from reaching a main term minus
O(1) at the √x scale.

The sharpest prime-side form of the wall in the corpus is one inequality per dyadic window: for one
generic bump width 0 < w < log 2/2, RH holds iff the window functional of the unmodulated difference
test κ_w(t + v/2) − κ_w(t − v/2), which reads Λ(n) only on |log n − v| ≤ 2w ⊂ (X/2, 2X), X = e^v,
is nonnegative at every lag v ≥ V. The pole and archimedean terms of the test pay the main term
exactly; what is left is a one-sided bound at exponent zero on a smoothed, √X-normalized prime
window at every scale, with no height parameter.

In the Lean corpus:

- `RHTower/RobinCriterionRiemann`, `RHTower/LagariasCriterionRiemann`,
  `RHTower/NicolasInequalityRiemannConverse`, `RHTower/PrimeLagLowerBoundRH`: the one-sided
  arithmetic inequalities are proved equivalent to RH; each converse runs through a one-sided
  bound on ψ(x) − x at exponent 1/2.
- `SquareRootThreshold/OneParameterLagFamilyDecidesTheCriticalLine`,
  `SquareRootThreshold/LargeDyadicPrimeWindowsDecideTheCriticalLine`:
  `zeta_onLine_iff_lag_primeWindow_nonneg`, RH ⟺ the one-parameter window inequality at every
  late lag, for all but countably many widths; the prime side of one test is one dyadic window.
  `SquareRootThreshold/SharpArchimedeanHorizonOfTheZetaSymbol`: `not_exists_PX_ge_of_lt_two`, no
  height-uniform lower bound on the prime symbol with coefficient below 2√X, so height-uniform
  symbol bounds give positivity only below the horizon √X ≤ (¼ − ε) log T.
- `RHTower/MertensRemainderExponentLaw`: a one-sided bound G(T) ≤ B e^{(b−1)T} on the Mertens
  remainder forces every zero to have real part ≤ b, and the remainder is Ω±(e^{(b−1)T}) for every
  b < Θ. The exponent of any one-sided prime estimate is the zero abscissa.
  `RHTower/QuasiRHMeanSquareAbscissa`, `RHTower/QuasiRHDilationCovarianceAbscissa`: cumulative
  mean squares of the normalized Chebyshev, Mertens and Möbius–divisor actions have exact exponent
  2Θ, and the positive absolute envelope of the signed high-dilation covariance grows at the wrong
  exponent, so the missing input is signed cancellation, not a larger majorant.
- `BiScaleUncertainty/BandSpectrumZeroWidthLaw`: `riemannHypothesis_iff_meanSquare_band`, the
  linear band ∫₀^L Ẽ² = O(L) of the normalized Chebyshev error is RH in both directions.
  `RHTower/CramerChebyshevMeanSquare`: `dyadic_chebyshev_mean_square_of_riemannHypothesis`,
  Cramér's ∫_X^{2X}(ψ(x)−x)² ≤ CX² under RH. `BiScaleUncertainty/CramerLiminfLaw`:
  `cramer_liminf_law_zeroEnergy`, under RH the band liminf is at least the zero energy
  Σ m_ρ²/|ρ|². `BiScaleUncertainty/PacketBandLaw`: `riemannHypothesis_iff_packet_band_of_universal`,
  the linear band of one universal packet is RH-equivalent. `RHTower/LittlewoodOmega`:
  `frequently_littlewood_lt_chebyshevError_of_riemannHypothesis`, the Ω±(√x log log log x)
  oscillation that forbids an O(√x) target or an eventual fixed sign.
- `RHTower/FermiNymanRawMobiusTailFloor`: the raw Möbius approximant of the Haar target is exact on
  (1/(N+1), 1] yet has error energy at least (N+1)H_N²/6 with H_N = Σ_{d≤N} μ(d)/d; convergence is
  square-root cancellation of H_N.
- `RHTower/PMLogMobiusBoundaryMultiplicity`, `RHTower/FermiNymanLogMobiusHead`: the log-Möbius
  head error is (ψ(x) − 2ψ(x/2))/log N, whose energy in dx/x² needs mean-square size x^{1/2}.
- `BezoutValuationIncidence/PowerSavingIncrementCriterion`:
  `mobiusFirstOctavePowerSaving_iff_riemannHypothesis`, uniform strict-half-power control of the
  first-octave Möbius increments M(n) − M(N), N < n ≤ 2N, is RH-equivalent: the Möbius receiver in
  Fermi cells is the same cancellation. `BezoutValuationIncidence/DampedChebyshevTangentFormOfTheReceiver`:
  `riemannHypothesis_of_integrable_tangent_energy`, a pronic norm bound on the damped Chebyshev
  tangent, integrable in the damping and uniform in the cutoff, implies RH; the bound is unproved.
- `TransHorizonIncidenceMechanics/GlobalRenormalizedDefectSignAtLargeHorizons`,
  `TransHorizonIncidenceMechanics/QuadraticLongWindowThreshold`:
  `eventually_moebius_renormalizedDefect_nonpos_all`, `moebius_defect_nonpos_of_quadratic_window`,
  the renormalized Möbius sieve defect is nonpositive at every prefix beyond 10N² + 8N for every
  N ≥ 2 and strictly negative eventually at every M ≥ 2N, uniformly in power damping. Every finite
  law of the trans-horizon source is owned; none bounds the coefficient-weighted complete energy
  below the first period, which is the receiver.
- `RHTower/MoebiusAbelSmoothedSaving`, `RHTower/Sieve/VinogradovRouteTSaving`: the best
  unconditional savings in the corpus are Vinogradov–Korobov shaped (a logarithmic power or a fixed
  exponent at most 1/100 on a bilinear piece), never x^{1/2}.
- `RHTower/BeurlingRegularIntegersOffLineZeros`: a Beurling prime system with a regular integer
  count and zeros at any prescribed β ∈ (1/2, 1). Regularity of the integers does not supply the
  square-root cancellation; only the arithmetic of ℕ can.

The lag–frequency law explains why the exponent is forced: under Poisson summation in t = e^y, a
test function vanishing at the nodes log n near lag y must carry spectral content at frequency
about e^y with amplitude e^{−y/2}. That amplitude is square-root size. Prime lattices sit exactly at
√-cancellation, so every blind family loses a logarithmic margin against the pole weight e^{y/2},
and the Zeta23 proportion method caps at the Nyquist density.

Rule: before trying a producer, name the prime sum it needs and the exponent it needs. If the
exponent is 1/2, the route is a restatement of RH.

## Wall 2: the Jensen gap between |ζ|² and log|ζ|

RH is equivalent to the Balazard–Saias–Yor equality: the Poisson average of log|ζ| on the critical
line, (1/2π)∫ log|ζ(½+it)| dt/(¼+t²), equals Σ_{Re ρ>½} log(|ρ|/|1−ρ|), a sum of positive terms over
off-line zeros, so RH is the vanishing of that integral. Equivalently, (s−1)ζ(s)/s² is an outer
function on Re s > ½. The obstruction is that every unconditional tool controls square means or
mollified square means of ζ, while the criterion needs the mean of the logarithm. Jensen's inequality
goes the wrong way: for any p > 0, |F|^p is subharmonic, so Poisson averages of |F|^p dominate
|F(s₀)|^p and the inequality is strict unless F is constant. Concavity of log bounds the log-mean
from above by the log of a square mean, which is the direction that cannot close.

In the Lean corpus:

- `RHTower/ZetaCriticalLineJensenInequality`: Σ_{ρ∈Z} log(|ρ|/|1−ρ|) ≤ the BSY integral for every
  finite set Z of off-line zeros; the integral is nonnegative and RH follows if it is ≤ 0.
- `RHTower/ZetaCriticalLineJensenEquality`, `RHTower/BalazardSaiasYorZeroSum`: the circle averages
  of log|G| converge to the BSY integral, and
  `integral_log_norm_zeta_criticalLine_eq_tsum_rightZeros` states the unconditional identity
  ∫ log|ζ(½+it)|/(¼+t²) dt = 2π Σ_ρ m_ρ log|ρ/(1−ρ)| as a convergent, multiplicity-weighted sum over
  all zeros right of the line.
- `RHTower/ZetaMollifiedCriticalLineJensen`, `RHTower/BalazardSaiasYorMollifierClass`,
  `RHTower/BalazardSaiasYorCriterionEquivalence`: the mollified form
  RH ⟺ inf_M (1/2π)∫|ζM|²dt/(¼+t²)/|M(1)|² = 1. Dirichlet-polynomial mollifiers never reach the
  floor (ratio ≥ 49/48), and the Báez-Duarte class reaches it only under RH.
- `RHTower/BaezDuarteBlaschkeFloor`: d_N² ≥ 1 − exp(−2 Σ log(|ρ|/|1−ρ|)), the Báez-Duarte distance
  floor in BSY form.
- `RHTower/FermiNymanWitnessGermRigidity`: the dyadic Haar system factors as a unimodular dyadic
  factor times the classical symbol, so FZZ-P is exactly the outerness statement for Ξ(s)/s².

Rule: an attempt that bounds a square mean of ζ, a mollified moment, or a Gram form of
|ζ(½+it)|²dt has to say how the logarithm is reached. Outerness needs equality in Jensen, which no
mean-value estimate provides.

## Wall 3: local zero clustering

Localized explicit formulas at a height γ₀ with a test function of log-length λ log γ₀ combine with
Turán's power-sum theorems to exclude a zero at real part β if the window around γ₀ contains few
zeros. Unconditionally a window of width 1/(λ log γ₀) may contain of order log γ₀ zeros, and Turán's
loss (n/(8e(M+n)))^n with n ≍ log γ₀ is γ₀^{−c log log γ₀}, larger than any power gain from
Vinogradov–Korobov sums. Zero-density estimates count zeros globally in strips, never inside one
window, so clustering cannot be excluded where it would matter.

In the Lean corpus:

- `RHTower/XiZeroCountLocalCeiling`: `exists_xiZeroCount_window_le`,
  N(t+H) − N(t) ≤ (H/2π) log(t+H) + 2C log(t+H), the sharp local ceiling; sub-mean-gap blocks have
  at most O(log T/ε) zeros. `RHTower/XiLogDerivLineOneWindowLower`:
  `exists_xiZeroCount_window_ge_log`, windows of one fixed width contain at least log T zeros, so a
  window argument cannot assume fewer than order log T zeros.
- `RHTower/ZetaRightZeroWeightedCount`: `exists_windowZeros_count_le`, the zeros with
  Re w ≥ ½ + v in a window of heights (U/4, U/2) number at most ((U/4)A e^{−v log U/2400} + K log U)/(πv):
  the exponential near-line density in window form, a count over a height range of length ≍ U, not
  inside one window of width 1/log U. `TransHorizonIncidenceMechanics/WindowedQuarterZeroDensityAndCHMDBoundStateCount`,
  `arithmetic-positivity-theory/InghamHuxleyHeightBoxZeroMajorant`,
  `arithmetic-positivity-theory/SelbergExponentialNearLineAndThreeRegimeZeroDensity`: Ingham–Huxley
  and Selberg density majorants in height boxes; none excludes one fixed off-line zero.
- `RHTower/TuranSumOneSidedBoundary`: Turán's problem for Σ λ(k)/k; a one-sided bound ε'/√x is
  pushed through Landau's theorem to the pole at −½ of ζ(2s+2)/(sζ(s+1)). The one-sided estimate is
  again the abscissa.
- `RHTower/JointAncestryShellPowerSumCriterion`: RH ⟺ (zeros approach the line) ∧ a power-sum
  growth bound |P_k(N)| ≤ N^{εk} for all k on dyadic shells. The power sums are the Turán objects and
  the growth bound is the RH content.
- `RHTower/JointAncestryQuasiRHChainExclusion`: off-line chains are excluded below σ = ½ + Θ only
  under a quasi-RH hypothesis Re ρ ≤ ½ + α, α < ½; without it the window argument does not start.
- `RHTower/DeBruijnClusterPersistence`: zero clusters persist under the de Bruijn–Newman heat flow;
  the flow does not disperse a cluster.

Rule: a window argument needs an unconditional bound on the number of zeros in a window of width
1/log γ₀ that is better than O(log γ₀). None exists, and the corpus has no mechanism producing one.

## Wall 4: the axis outside the zero set

Hermite–Biehler and shift arguments compare ξ with a shifted or differenced copy of itself:
ξ(w) + cξ(2a−w), ξ(s+h) − ξ(s−h), cos(δD)Ξ, or ξ + λξ'. Each is real-rooted exactly when the axis
Re w = a lies outside the zero set, that is when every zero has real part at most a. Axis a = 1 is
unconditional because zeros have β < 1; axis ½ + δ is the statement Θ ≤ ½ + δ. De Bruijn's strip
theorem shrinks a strip of width Δ to width √(Δ²−δ²) under the shift, never to zero from an
unconditional start. These constructions are bookkeeping of the strip containing the zeros, not a
mechanism that moves zeros.

In the Lean corpus:

- `RHTower/DeBruijnNewmanHalfBound`: H_t has only real zeros for t ≥ 1/8 unconditionally, since all
  zeros of Ξ have |Im z| < ½ and the heat flow contracts the strip; the bound is the strip width.
- `RHTower/XiCosineShiftLaguerrePolya`: cos(hD)Ξ is Laguerre–Pólya for h ≥ ½ unconditionally and for
  every h > 0 under RH; the threshold is exactly the strip.
- `RHTower/StrictHermiteBiehlerGivesRH`, `RHTower/XiHermiteBiehlerCount`: strict Hermite–Biehler for
  the pair (ξ ± iξ') gives RH, and ξ + λξ' has the same zero count as ξ to the right of the line;
  the inequality Re ξ'/ξ > 0 is Lagarias's criterion, not an input.
- `RHTower/KreinChamberIsLagarias`: the Krein chamber value of the split Hankel–Krein construction
  is ∂_σ|ξ|² = 2|ξ|² Re(ξ'/ξ), again Lagarias's criterion; it cannot be made topological.
- `RHTower/SuzukiShiftedXiLeakageRH` [S, not umbrella-imported]: the shifted-Ξ leakage criterion is
  RH-equivalent.
- `SquareRootThreshold/OneParameterLagFamilyMeasuresTheAbscissa`,
  `SquareRootThreshold/NegativityRateEqualsMaximalDepth`: for every σ ≥ 0, Re ρ ≤ ½ + σ iff the
  one-lag window functional is eventually ≥ −C e^{σv}; the negativity rate of the lag family equals
  the maximal depth. The lag family measures the strip; it does not move its edge.

Rule: any argument built from ξ shifted, differenced, heat-flowed or multiplied by 1 + λξ'/ξ has a
dominance parameter (the shift, the time, the axis, the lag rate). State what unconditional fact
pushes that parameter past the strip edge ½; the corpus knows none.

## Wall 5: no Frobenius, no F₁

The function-field proofs of RH (Weil, Stepanov, Bombieri, Deligne) use that the zeros are
eigenvalues of Frobenius acting on a finite-dimensional cohomology, with an algebraic identity
f(x)^q = f^{(q)}(x^q) on the fixed points, and in Deligne's case a tensor-power amplification whose
total is exact by the known pole of H²_c and the finite rank of H¹_c. For ζ there is no archimedean
object whose fixed points are the primes, and every analytic imitation of the amplification is
circular: rescaling moves the pole; moments of Ξ are zero-blind; the amplified Chebyshev error
E(x)^{2k} has Landau abscissa 2k(Θ−½), so a k-uniform bound is RH; function-field positive cones
with q ≥ 2 have periodic zeros of period 2π/log q and cannot approximate ζ beyond height about 9.

In the Lean corpus:

- `RHTower/StepanovCount`, `RHTower/StepanovCharacterSum`: Stepanov's auxiliary-polynomial count for
  hyperelliptic curves and the resulting elementary Weil bound. The vanishing to high order uses the
  Frobenius identity on points of the curve.
- `RHTower/FunctionFieldFE`: the closure of Frobenius eigenvalues under ω ↦ q/ω, with the purity
  statement |ω| = √q explicitly not formalized.
- `RHTower/CCMFUCompactAutocorrelationDeningerAmplification`: amplified spectral responses grow
  without bound at late translations; the arithmetic side of that amplification is the open weld.
- `RHTower/TwinRigidityZetaPower`: a degree-d twin of ζ^d with all zeros critical is ζ^d, so tensor
  powers add no freedom.

Rule: an amplification or positivity argument must identify the object on whose fixed points the
primes sit. Without a fibration making Spec ℤ a fibre over a one-dimensional base, every tensor-power
or Rankin trick returns the Landau abscissa.

## Wall 6: the probability cone

Positivity statements derived from the Euler product hold exactly where the Dirichlet series
converges absolutely, Re s > 1. Examples that are true for σ > 1 and fail for σ ≤ 1: t ↦ log ζ(σ+it)
is positive definite (Fourier transform of Σ Λ(n)n^{−σ}/log n at log n); the sawtooth transform
Ψ(σ+it) = ∫{e^u}e^{−(σ+it)u}du is positive definite for every σ > 0 but only yields a low-height
zero-free region; the Eisenstein series E(z,u) is a positive sum for u > 1 and is defined only by
continuation for ½ < u < 1, where it is not positive. Random Euler products are zero-free almost
surely on Re s > ½, but ζ is one point of the torus (see Wall 7).

In the Lean corpus:

- `HTGeometry/PrimeDirichletPositiveDefinite`: an absolutely summable atomic Fourier series with
  nonnegative coefficients is positive definite; the hypothesis is absolute summability, which for
  ζ's prime measure holds only for σ > 1.
- `RHTower/FiniteEulerStageNearLineStrip`: finite Euler stages Λ_X(s) = A_X(s) + A_X(1−s) are
  zero-free near the line only up to a height determined by the truncation weight W(X, u₀); the
  zero-free range of a finite product is a finite height.
- `RHTower/SelbergPositiveEisenstein`: the Eisenstein source at s = 2 is a positive real sum with
  E(z) ≥ y²; positivity is proved at a point of absolute convergence.
- `RHTower/JointAncestryEndpointBudgetProducer`: `eventually_jasConstProductPositive_logLogBudget`,
  the native prime-product form is nonnegative on finite prime sets whose budget
  Σ_P p^{−(σ−1/2)} is at most ((log y)/(128·10⁸))^{3/2}/(log log y)⁴; the level-one RH receiver needs
  budget y^{1/2}. Positivity is proved where the prime mass is small, which is the absolute-convergence
  regime in disguise.
- `RHTower/SteinhausEulerVerticalBarrier`, `RHTower/SteinhausEulerQuadraticApprox`: finite Euler
  products under the Steinhaus phase rotation; every statement is about a finite head.

Rule: when a positivity or definiteness statement is proved, check the half-plane on which it is
proved. If it is Re s > 1, continuation to the strip is not positivity-preserving, and the strip
statement must be obtained some other way.

## Wall 7: statistical and almost-all results

Families, Bohr–Jessen–Bagchi value distribution, Voronin universality, Kac–Rice densities and
almost-all short-interval theorems give statements true for a positive proportion, for almost all
members, or on sets of density one. RH is a statement about one function at every height. Bagchi's
strong recurrence (ζ(s+iτ) returns to ζ(s) on a disc for τ in a set of positive density) implies RH,
but around an off-line zero the return set has density zero, so the statistical statement and the
pointwise one are separated exactly by the zeros one wants to exclude. Family averaging (Deuring–
Heilbronn, GRH for almost all characters) couples members only near s = 1, where the product is
anchored at the pole. Sampled statements have the same gap: a lag grid loses exactly the non-attained
top depths, so a grid criterion needs attainment of a rightmost zero while the continuum does not.

In the Lean corpus:

- `RHTower/ZetaStrongRecurrenceReceiver`: near an off-line zero, the set of self-return shifts on
  [0, T] has measure o(T); strong recurrence fails exactly there.
- `RHTower/ZetaTypicalHeightApproximationExcludesZeroTargets`:
  `not_pos_upperDensity_zetaTargetReturnSet`, any target with a zero inside the disc is approximated
  by ζ on that disc only on a density-zero set of heights; this unifies the self-return law and the
  head-zero obstruction.
- `RHTower/ZetaDiscRecurrenceIffUniformHeadTargetDensity`:
  `zetaDiscStronglyRecurrentOn_iff_headTargetUniformlyDense`, Bagchi's fixed-base recurrence on a
  disc is equivalent to positive-density approximation of the base ζ by its moving heads, uniformly
  in all large head cutoffs; `riemannHypothesis_of_forall_headTargetUniformlyDense`;
  `eventually_edPolyReturnSet_inter_headTargetReturnSet_eq_empty`, the head's own self-return
  heights never pay the Abel pole. `RHTower/ZetaDiscUniformCarlsonTail`,
  `RHTower/ZetaTypicalHeightPairRecurrenceAndHeadZeroObstruction`: Carlson-good heights are
  disc-uniform and of density one, finite-head almost periods give ζ returns at typical translated
  base heights, and a head zero inside the disc separates head returns from ζ returns up to density
  zero. The unconditioned half is closed; the fixed-base half is the wall.
- `RHTower/FiniteEulerProductKroneckerWeylLimitLaw`: `exists_pos_density_eulerTargetReturnSet`,
  phased finite Euler products visit every approximable target at positive lower density, the Haar
  measure of the approximating phases; this is the statistical half of universality for finite
  products, and it says nothing about the fixed base height of ζ.
- `RHTower/ZetaWeakRecurrenceLadderCollapse`: weak recurrence (return shifts beyond every height,
  no density) transports every off-line zero to arbitrarily large ordinates, so the asymptotic
  abscissa equals the abscissa; recurrence relocates zeros, it does not remove them.
- `SquareRootThreshold/LagGridsSeeAttainedTops`, `SquareRootThreshold/ChainsHideFromLagGrids`:
  `zeta_onLine_iff_topAttained_and_grid_primeWindow_nonneg`, RH ⟺ grid nonnegativity together with
  attainment of a rightmost zero in every nonempty off-line set; `exists_chain_hidden_from_grid`, a
  summable nonresonant chain with strictly increasing unattained depths is nonpositive at every
  integer lag and unbounded on the continuum. Aliasing turns heights tending to infinity into
  exponents accumulating at a real point, defeating Landau.
- `RHTower/WeilPositiveAlmostAllShortIntervals`: windows missing the support of a Weil-positive
  system have logarithmic measure O(X^{−ε/2}); an almost-all statement with an exceptional set.
- `RHTower/XiReciprocalSlicePositiveDensity`: reciprocal slice positivity holds at a positive
  proportion of heights, derived from separated simple critical zeros; a proportion, not all heights.
- `RHTower/XiCardGateUnification`: the uniqueness and density theorems of two zero-geometry cards
  share one gate, a positive proportion of simple critical zeros.

Rule: an attempt that averages over τ, over characters, over a random model or over a lag grid must
name the step that upgrades "almost all" to "all". The upgrade is where the off-line zero hides.

## Wall 8: infinitesimal admixture

The Weil functional is affine in the weight system: W_λ = (pole and archimedean part) − Σ λ(n)ℓ_n.
Deforming an explicit Weil-positive producer (for example Lebesgue measure on (1,∞) minus one atom)
toward Λ along λ_t = tΛ + (1−t)λ₀ does not dilute the RH content: the positivity set in t is an
interval containing 0, and for every fixed t > 0 positivity at all apertures is equivalent to RH,
because an off-line pair contributes t · 2 Re f̂(γ₀−iε)² ≈ −t e^{2aε}‖f‖² against an archimedean
slack of size log γ₀ · ‖f‖². Any λΛ with λ > 0 carries full RH content; the fluctuation ⟨d(ψ−x), ·⟩
costs an H¹-type norm against a log-Sobolev slack and the comparison fails at the critical exponent ½.

In the Lean corpus:

- `RHTower/LebesgueAtomArchimedeanWeilDensity`: the explicit system λ₀ (Lebesgue on (1,∞) minus an
  atom) has positive Weil density for ζ's archimedean datum; this is the unconditional producer whose
  deformation toward Λ was tried.
- `RHTower/WeilConePoleWeightRigidity`: a full-cone Weil-positive system βΛ + e has β = 1 (the pole
  fixes the Λ-coefficient), so no scaled Λ can be positive.
- `RHTower/WeilPoleWeightSummableDeviationRigidity`: pole weights other than one fail near Λ, with
  unbounded pole terms of both signs at bounded mass.
- `RHTower/WeilConeVonMangoldtZetaPencil`: the pencil βΛ + γ[n ≥ 2] + v meets the Weil cone only at
  Λ (β = 1, γ = 0, v = 0).
- `RHTower/WeilPositivityBeurlingPerturbationRigidity`: perturbing the prime measure by any finite
  signed measure supported in [ε, ∞) destroys Weil positivity unless the perturbation is zero.
- `RHTower/WeilLittleOVonMangoldtRigidity`: a full-positive weight deviating from Λ by o(Λ) is Λ;
  even an infinitesimal relative deviation leaves the cone.

Rule: do not try to reach Λ from an unconditionally positive system by a small deformation. The
cone is a point, and every direction out of that point is RH-equivalent at any amplitude.

## Wall 9: the temperedness gate

The function ζ(s−a)ζ(s+a), a real and nonzero, has an Euler product, the functional equation
s ↦ 1−s, polynomial growth and nonnegative coefficients Λ_a(n) = 2Λ(n)cosh(a log n), yet its zeros
lie on Re s = ½ ± a. It fails only the Ramanujan condition on coefficient size. Hence any producer
that uses only Euler product, functional equation, growth and nonnegativity of coefficients would
prove a false statement, so a producer must use temperedness (coefficient size) in an essential way.
The Weil form is tight at Λ: adding a²Λ(n) log² n breaks positivity at once, and the negativity
growth rate of W_a is 2(Θ − ½ + |a|), which gives nothing by continuity in a.

In the Lean corpus:

- `RHTower/BeurlingRegularIntegersOffLineZeros`: an explicit positive prime density whose zeta is
  rational with zeros at any β ∈ (½, 1); the generalized-integer count is regular, and still the
  zeros are wherever one puts them.
- `RHTower/TwinRigidityZetaPower`, `RHTower/TwinRigidityOffLineZero`: with real coefficients,
  a(1) = 1, absolute convergence, functional equation and finite order, all zeros critical forces
  T = ζ^d, and every nonzero functional-equation-compatible entire finite-order perturbation of ζ^d
  has an off-line completed zero; the rigidity needs the coefficient data, not only the analytic
  shape.
- `RHTower/WeilConePoleWeightRigidity`, `RHTower/WeilConeVonMangoldtZetaPencil`: the Weil cone
  rejects every rescaling or admixture of Λ, the Lean form of "tight at Λ".

The non-tempered pair itself is formalized in `RHTower/NonTemperedShiftedZetaPairCountermodel`:
nonnegative Dirichlet coefficients c_a(n) = Σ_{de=n} d^a e^{−a} with c_a(1) = 1
(`lSeries_shiftedPairCoeff`), the logarithmic Euler product −F_a'/F_a = Σ Λ(n)(n^a + n^{−a}) n^{−s}
with nonnegative prime-power-supported weights (`neg_deriv_shiftedZetaPair_div`), the completed
functional equation Λ(s−a)Λ(s+a) = Λ(1−s−a)Λ(1−s+a) for every s (`shiftedCompletedPair_one_sub`),
polynomial growth on a strip (`exists_norm_shiftedZetaPair_le`), off-line zeros at ½ ± a + iγ above
every height from Hardy's critical zeros (`exists_offLine_zero_shiftedZetaPair`), and the failure of
every Ramanujan bound c_a(n) ≤ C n^ε with ε < |a| (`not_ramanujan_shiftedPairCoeff`). The pair has
its poles at 1 ± a rather than at 1; the list of positive properties is what the gate is about.

Rule: list the properties of ζ a proposed argument uses. If ζ(s−a)ζ(s+a) has all of them, the
argument is wrong somewhere, because its conclusion is false for that function.

## Wall 10: the oscillation–transport dichotomy

Exponential-sum methods (Vaughan's identity, van der Corput, Vinogradov) give power savings for
oscillating sums such as Σ_{m≤x^θ} μ(m)e(x/m) or Σ_{p≤√(kx)} log p · e(kx/p). Zero-detecting sums are
non-oscillating: ψ(x/j) − ψ(x/(j+1)), Σ μ(m)m^{−s} with its transported poles, the sawtooth
Σ Λ(d){x/d}. Transport (a Möbius sum with a smooth weight g(x/m)) either keeps the 1/ζ structure and
the transported poles 1 + θ(ρ−1), in which case it is non-oscillating and has no power saving, or
acquires a phase (an incomplete-gamma factor e(m^{1/θ−1})) that destroys the pole structure, in which
case the power saving says nothing about zeros. The sawtooth {x/d} only relocates the one-sided
counting problem; in the range p > √x it reduces to prime counting at √x precision.

In the Lean corpus:

- `RHTower/MoebiusAbelSmoothedSaving`: the Abel-smoothed Möbius sum Σ μ(n)e^{−nx} is bounded by
  shifting the Perron contour into the Vinogradov–Korobov region below height 12 log(1/x); the
  saving is of VK shape because the sum is non-oscillating and the poles are the zeros.
- `RHTower/Sieve/VinogradovRouteTSaving`, `RHTower/Sieve/VinogradovUsefulCoordinates`,
  `RHTower/Sieve/MontgomeryVaughanArbitraryLogPhaseReceiver`: power savings for bilinear and phased
  sums, with exponents fixed and small; these are the oscillating objects and they carry no pole
  information.
- `BezoutValuationIncidence/VaughanTypeIIShortAndAllHorizonMobiusL2Energy`,
  `BezoutValuationIncidence/LinearBandVaughanTypeIIBilinearEstimate`: the Type-II short side of
  Vaughan's identity is the negative literal Möbius sieve above 1, and the bilinear piece has a
  linear-band saving with a logarithmic block cost; the saving lives on the bilinear (oscillating)
  piece, and the unsigned all-horizon energy bound M·invSum(M)³ carries no sign.
- `RHTower/MobiusLaplaceCriticalDilationNoGo`: the critical Möbius–Laplace renewal equation has
  dilation weight k^{−1/2} whose prime restriction is not summable, so absolute-value Neumann-series
  attacks fail and any argument must keep the conditional signed cancellation.
- `RHTower/FermiNymanRawMobiusTailFloor`: the sawtooth form of the Möbius sum in the Haar system
  carries the harmonic floor (N+1)H_N²/6.

Rule: classify the sum a method bounds. If it oscillates, say how the bound is transported back to a
non-oscillating zero detector without introducing a phase; if it does not oscillate, the method is
a zero-free-region argument in disguise.

## Wall 11: node criticality

Prime-blind positivity on a node set S (the pole and archimedean part of the Weil functional is
nonnegative on every nonnegative combination of autocorrelations whose symmetric values vanish at
±log n for n ∈ S) is equivalent to RH together with S containing every prime power. Deleting one
prime-power node, even log 4, makes the positivity false: some nonnegative autocorrelation blind at
every other node has negative pole plus archimedean part. Non-prime-power nodes are redundant. So any
argument insensitive to a single node cannot work: sampling-density or Nyquist arguments,
Beurling–Malliavin, generic uncertainty principles, support counting. A proof must see why log 4
matters and log 6 does not, which is multiplicative structure.

In the Lean corpus:

- `RHTower/PrimeBlindNodeCriticality`: `primeBlindPositiveOn_iff`, PrimeBlindPositiveOn S ⟺ RH ∧
  every prime power lies in S.
- `RHTower/TwistedArcMinimumPrincipleProof`: `riemannHypothesis_iff_primeBlindPositive_unconditional`,
  RH ⟺ prime-blind positivity with no further hypothesis. `RHTower/WeilPositivityPrimeBlindDuality`:
  `exists_weilPositive_iff_primeBlindPositive`, prime-blind positivity is the prime-free half of
  full Weil positivity.
- `RHTower/ArchimedeanUnitNodeEnergy`: for a single node m ≥ 2, the energies of combinations blind at
  every other node with unit mass at m are bounded below iff RH; every single node is RH-equivalent
  (`riemannHypothesis_iff_bddBelow_unitNodeEnergies`).
- `BiScaleUncertainty/PoleInvisibilityOnGappedBlindGrids`,
  `BiScaleUncertainty/SquareRootDensityPoleInvisibility`,
  `BiScaleUncertainty/ExactSingleIntegerBlindSymbolSlack`: on any node set with arbitrarily distant
  fixed logarithmic gaps (`not_zeroPoleBlindPositiveOn_of_gapped`), on the powers of one integer
  (`not_zeroPoleBlindPositiveOn_powers`, with the sharp slack −symbolPeriodMean q) and on every
  sub-square-root-density set including the smooth integers over a finite prime set
  (`not_zeroPoleBlindPositiveOn_smooth`), zero-pole positivity fails; only the full integer-log grid
  is RH-equivalent.
- `RHTower/EvenSectorBlindMinimumSmallAperturePositivity`:
  `riemannHypothesis_iff_evenBlindMinimum_nonneg_beyond_primeTwo`, the even blind minimum is at
  least 1/20 below the aperture (log 2 + 1/50)/2 and RH is its nonnegativity beyond the first prime.
- `ArithmeticCriticalityTheory/ExtraJumpVisibilityThresholdAtInfinity`:
  `exists_foldedGenerator_add_extraJump_gt_potential_log_two`, in the shifted gauge the prime 2 is
  visible at infinity iff e^{−2a} < 3/4; each node enters the gauge at a threshold of its own.
- `ArithmeticIncidencePositivity/PrimePowerIncidenceDominance`,
  `ArithmeticIncidencePositivity/DyadicWindowIncidence`: the prime atoms of the jump form are the
  divisibility relations of the integers read by ratio and by product; on lattice pairs the
  crossing atom never exceeds the same-side atom, and inside one dyadic window the only divisor
  edges are doublings and triplings and the only crossing prime-power edges are consecutive powers
  of 2 or 3, each below 2 log 3/X. The node structure is multiplicative and sparse per window.
- `RHTower/PrimeBlindCarlsonThreshold`: blindness at log ℕ at the Carlson decay rate π/2 forces the
  Fourier transform to vanish; the threshold is where blind spectra live.

Rule: before a positivity argument on blind tests, check whether it survives removal of one
prime-power node or thinning of the node set. If it does, it proves something false, so it cannot be
right.

## Wall 12: the forced dual measure

Every certificate of prime-blind or Weil positivity yields a positive spectral measure on the line
(Hahn–Banach, Krein extension, LP duality). By uniqueness of the Weil cone and atomicity of the
boundary measure, that measure must be the critical-zero counting measure itself. So a producer of
positivity is a spectral realization of the zeros, and conversely every linear or convex
reformulation of the positivity problem has exact duality whose only certificate is the zero measure.
Degree-4 Positivstellensatz lifts with test-dependent weights reduce to the same bilinear problem.
Near-null tests with pole ≈ −archimedean part and |pole|/mass → ∞ exist under RH, so no estimate with
a margin can certify positivity; exact cancellation is required. The quantitative form of "no margin"
is the restricted Weil ground energy μ(A) at aperture A: it is at least 1/30 for A ≤ 21/200 and tends
to 0 as A → ∞ unconditionally, and RH is the statement that it never crosses zero in between.

In the Lean corpus:

- `RHTower/WeilConeUniquenessUnconditional`: `eq_vonMangoldt_of_weilPositiveFull`, the only
  full-cone Weil-positive weight system is Λ; no hypothesis on the system or on ζ.
- `RHTower/WeilConePoleWeightRigidity`: the full cone fixes the pole weight at one.
- `RHTower/WeilPositivityBeurlingPerturbationRigidity`, `RHTower/WeilPositivityResidueRigidity`: the
  prime measure and the residue are pinned by positivity.
- `RHTower/EvenSectorPoleWeightUniqueness`, `RHTower/EvenSectorTwistedArcNull`: source uniqueness in
  every finite even cone, and the twisted-arc null family that removes the imaginary spectrum.
- `RHTower/ArchimedeanUnitNodeEnergy`: the energy floor at a single node is RH, the dual statement
  that no certificate has slack.
- `ArithmeticCriticalityTheory/ExplicitSmallApertureCCMGroundEnergyFloor`,
  `ArithmeticCriticalityTheory/WindowGaugeLogarithmicGroundEnergyFloor`,
  `ArithmeticCriticalityTheory/RestrictedWeilGroundEnergyCriticalAtInfinity`,
  `ArithmeticCriticalityTheory/GaussianCriticalityRestrictedWeilGroundEnergy`:
  `one_thirtieth_le_ccmRestrictedWeilGroundEnergy` (μ(A) ≥ 1/30 for A ≤ 21/200, so every contact
  aperture exceeds 21/200), `windowFloor_eq_suzukiMainTerm` (μ(A) ≥ −log(2A) − 3A/2 − 2·archConstantReal − 4A³
  for 2A < log 2, Suzuki's main term), `exists_ccmRestrictedWeilGroundEnergy_lt` (μ(A) < ε for all
  large A, unconditionally), `exists_ccmRestrictedWeilGroundEnergy_le_doubleExp`
  (μ(A) ≤ K exp((11/2)A − πe^{2(A−2)}) for A ≥ 3), and
  `riemannHypothesis_iff_tendsto_ccmRestrictedWeilGroundEnergy_zero` (RH ⟺ μ(A) → 0). No uniform
  positive gap exists at large aperture; under RH the restricted operators are asymptotically
  critical, off RH the ground energy tends to −∞.
- `ArithmeticCriticalityTheory/OddFormCriticality`, `ArithmeticCriticalityTheory/JumpRateCriticality`,
  `ArithmeticCriticalityTheory/CapacityRatioApertureCriticality`:
  `riemannHypothesis_iff_nonneg_and_no_hardyWeight` (the odd form admits no Hardy weight),
  `riemannHypothesis_iff_isLeast_primeRate` (every prime rate Λ(n)n^{−1/2} is the least admissible
  rate), `tendsto_capacityRatio_spanPlateau` (the capacity ratio of plateau truncations tends to its
  critical value 1): every term of the form is critical, so a certificate must cancel exactly.

Rule: a positivity producer must come with the Hilbert space and the self-adjoint (or unitary)
operator whose spectrum it realizes. If the argument only manipulates test functions and
inequalities, its certificate is the zero measure and the argument is circular.

## Wall 13: cone mismatch

Maximum principles, transfer-operator positivity (Mayer's operator of the Gauss map at s = ½,
Perron–Frobenius) and modular constructions act on pointwise cones: functions nonnegative on an arc
or a domain. Prime-blind positivity lives on the Bochner cone: autocorrelations f ⋆ f̃, positive
definite functions, nonnegative spectral measures. The two cones meet only on nonnegative cores, the
window sector |supp| ≤ log 2, which carries no RH content. In the odd sector the two cones coincide
(copositive equals positive semidefinite), and there the obstruction is that the pointwise minimizer
is the sign-changing odd eigenfunction, on which no maximum principle has a sign. Transfer-operator
positivity is a real-s statement; the Bochner statement needs complex spectral parameters.

In the Lean corpus:

- `RHTower/TwistedArcMinimumPrincipleProof`: the twisted arc minimum principle (no finite
  combination of twisted arc moments is strictly positive on the whole bottom arc) is the
  pointwise-cone statement, and it closes the (N1) side of the Weil criterion but not positivity.
- `RHTower/BlindCoreMayerTransferHalf`: periodization of a blind core is the Mayer transfer operator
  at s = ½; the inversion law is the symmetry t ↦ 1−t of the profile. Positivity of this operator
  is pointwise positivity.
- `RHTower/EvenSectorTwistedArcNull`, `RHTower/CHMDStage3TwistedArcGroundStateAndSechAnnihilation`:
  the arc constructions reach the null face (Ξ²-divisible tests) and the sech reference, not the
  interior of the Bochner cone.
- `RHTower/WeilConeMismatchWitnesses`: the two cones are different in both directions, with explicit
  witnesses from one smooth bump. The Weil test b(u) − b(u−3) has autocorrelation −∫b² < 0 at lag 3
  (`weilTest_self_re_neg_twoSignedWeilTest`: Bochner, not pointwise); the nonnegative profile
  b(u−3) + b(u+3) is the autocorrelation of no Weil test, since autocorrelations are bounded by their
  value at 0 (`twoHumpProfile_ne_weilTest_self`: pointwise, not Bochner); and a nonnegative test blind
  at every log n is positive only on a set of measure ≤ log 2 (`nonneg_primeBlind_window`, from
  `DilationFreeSetMeasure`): the cones meet only in the window sector.
- `ArithmeticCriticalityTheory/PlateauGaugeWindowWeilPositivity`,
  `ArithmeticCriticalityTheory/PoleConductanceWindowWeilPositivity`:
  `fullZeroForm_ge_of_support_le` (Ẑ(F) ≥ (3/40)∫F² for supports below e^{−2}/2) and
  `fullZeroForm_ge_of_support_le_sharp` (Ẑ(F) ≥ (1/30)∫F² on [−21/200, 21/200]) are pointwise-gauge
  (maximum-principle) arguments, and they close exactly the window sector below the first prime,
  where the cones meet. `ArithmeticCriticalityTheory/MeanZeroProfileVariationInequalityPastPrimeTwo`:
  `reflectedDifferenceEnergy_add_le_poleFree_of_support_le_seven_twentieths`, past the first prime
  the inequality is proved only on the pole-free (μ_a-mean-zero) sector, with the even blind
  minimum as margin.
- `ArithmeticCriticalityTheory/ShiftedGroundStateOriginFailure`,
  `ArithmeticCriticalityTheory/ShiftedGroundStateInfinityFailure`,
  `ArithmeticCriticalityTheory/DoobSourcePoleMomentLawAtInfinity`: every nonnegative admitted gauge
  profile is a strict folded subsolution near the origin (source −2∫M dm) and at infinity (source
  −2∫₀^∞ M cosh(r/2)); the pointwise supersolution route, which is the maximum principle for the
  jump form, has no nonnegative candidate, and any supersolution is sign-changing.
  `ArithmeticCriticalityTheory/FiniteJumpFormAllegrettoPiepenbrink`: on a connected finite kernel
  the two cones coincide (form nonnegativity iff a strictly positive supersolution exists), which
  is the finite model the continuum does not obey.
- `ArithmeticIncidencePositivity/CrossingConductanceSignLaw`: the pointwise sign of the archimedean
  crossing kernel ω(|x−y|) + 2 sinh(x/2) sinh(y/2): negative conductance on every crossing pair with
  sum below the threshold s₀ ∈ (log 5, log 6) and on axis collars of width < 3e^{−3s/4} beyond it.
  The pointwise cone of the jump form has an explicit negative region; positivity of the form is a
  Bochner statement about profiles, not a pointwise statement about pairs.
- The Mehler–Fock (Bochner–Godement) dictionary that identifies the Bochner cone with
  positive-definite zonal functions on the arc remains on paper; what is formalized is the
  cone mismatch it was used to establish.

Rule: when a positivity statement is proved by a maximum principle, a transfer operator or a
pointwise gauge, identify the cone it lives on. A Bochner-cone statement needs a transfer from
pointwise positivity that is compatible with blindness, and the only known such transfer stops at
the window sector.

## Wall 14: the size law

The primes cannot enter a spectral model as a finite-rank, trace-class or finite-deficiency
modification of an archimedean reference. The zero counting function has the archimedean density
θ'(t)/π, and the fluctuation S(T) is unbounded with ∫|S| = ∞, which is incompatible with a
trace-class perturbation of a reference whose spectrum has the archimedean density. Quantum graphs
with ℚ-independent bond lengths and unitary or Hermitian coupling decouple: a secular determinant that
factors over the prime-power blocks forces the scattering matrix to be block diagonal, so the graph
realizes an Euler product only when the blocks do not interact, and a unitary producer carries Euler
factors only with modulus one. Compact models fail on Weyl density.

In the Lean corpus:

- `RHTower/QuantumGraphPrimePowerDecoupling`: `eq_zero_of_det_eq_prod_principalBlock` and
  `eq_zero_of_secular_eq_prod`, a unitary scattering matrix whose secular determinant factors over
  blocks is block diagonal.
- `RHTower/UnitaryEulerFactorRigidity`: `abs_diag_eq_one_of_det_eq_prod_diag`, a unitary S with
  det S = ∏ S_ii has |S_ii| = 1, so the Euler factors of a unitary producer are pure phases.
- `RHTower/ArithmeticDilationTraceClass`: the trace-class realizations the corpus does have are of
  absolutely summable arithmetic matrices, that is of the absolutely convergent regime (Wall 6).
- `RHTower/ZeroCountRemainderNotIntegrable`: with N(T) the zero count and M(T) = (T/2π) log(T/2πe) +
  7/8 the smooth Riemann–von Mangoldt term, the remainder S = N − M (the classical argument up to
  O(1/T)) satisfies ∫_A^T |S| ≥ c T/log T for all large T (`exists_integral_abs_rvmRemainder_ge`),
  hence is not integrable on (0, ∞) (`not_integrableOn_rvmRemainder`). Since the spectral shift of a
  trace-class perturbation is integrable (Krein), the primes are not a trace-class modification of a
  reference with counting function M. The proof uses only monotonicity of N, the local ceiling on
  zeros in windows of length 1/log T, the Riemann–von Mangoldt remainder, and M' ≤ log T.
- `RHTower/BurnolFirstJetShellScaleLaw`: `not_tendsto_traceNorm_burnolFirstJetDampingShell_zero`,
  positive Burnol damping shells at scale ratio c > 1 tend strongly to zero while their trace tends
  to log(c)/4; trace-norm limits do not pass, so trace masses of the prime part do not vanish.
- `SquareRootThreshold/ZetaZeroCountRemainderIsUnbounded`: S(T) is unbounded, unconditionally
  (`rvmRemainder_unbounded`: for every B and T₀ some T ≥ T₀ has |S(T)| > B;
  `not_isBoundedUnder_abs_rvmRemainder`). This excludes finite-rank perturbations. Mechanism: the
  localized explicit formula of the bump autocorrelation K_ℓ at height T reads
  Re Π_ℓ(T) = ∫_1^{2T} S(t) ψ_ℓ'(t − T) dt − Corr_ℓ(T) + o(1)
  (`ZetaWindowPrimePolynomialReadsZeroCountRemainder`, by Abel summation against dS). The off-line
  correction is quadratic in the displacement (`RHTower/ImaginaryShiftQuadraticFourierDefect`) and
  small outside a set of heights of measure o(U) in [U/4, U/2], by the Selberg-type window count
  (`ZetaOffLineCorrectionSmallOutsideSparseHeights`). Kronecker–Weyl for the prime phases gives
  heights of positive density in every window where Re Π_ℓ exceeds any level below its aligned
  value, which is ≫ ℓ e^{ℓ/4} (`ZetaWindowPrimePolynomialOnThePrimeTorus`). A bound |S| ≤ B would cap
  Re Π_ℓ by Bℓ² ∫|ψ_1'| + o(1).

Rule: a Hilbert–Pólya style model must say in which Schatten class, or with what deficiency index,
the primes modify the archimedean operator. Trace class, finite rank and finite deficiency are
excluded; the modification must be as large as the zero fluctuation.

## Wall 15: support versus positivity

Positivity of curvatures, currents and positive-definite functions never constrains where zeros
lie. The Poincaré–Lelong current i∂∂̄ log|ξ|² = Σ[ρ] is positive for any zero set; the positive
definiteness of Ξ (it is the Fourier transform of a positive kernel) bounds |Ξ(t)| ≤ Ξ(0) and says
nothing about the location of zeros; Schur products of the local factors Γ_ℝ and (1 − p^{−s})^{−1}
are positive definite in t for the same reason. An orientation of the zero set relative to the
critical axis is a reality or unitarity structure, and the corpus's divisor selectors (positive
renewal mass, reflection, finite deletion) characterize the divisor exactly but are
orientation-blind. A definite majorant topology that would induce positivity is RH itself. The
orientation does live in the complete signed Weil form, which determines the configuration; every
positive reading of that form discards it.

In the Lean corpus:

- `HTGeometry/EntirePoincareLelong`: ∫ log‖f‖ Δφ = 2π Σ_a ord_a(f) φ(a) for every nonzero entire
  function; the right side is positive for any zero set.
- `RHTower/EulerShiftPairIncidenceCurrent`: `xi_isPoincareLelongOfSmooth`, the Poincaré–Lelong
  current of Ξ pushed through the center/shift map gives the horizontal-collision charge; the charge
  is a multiplicity count, orientation-free.
- `RHTower/XiHorizontalCollisionExchangeOrientationNoGo`: the direct signed extension of the
  collision charge (weight by oriented real displacement) vanishes identically under exchange of
  the pair; the positive survivor is the squared displacement, which cannot choose a sign.
- `SquareRootThreshold/WeilFormDeterminesTheConfiguration`: `eq_of_weil_eq`, two tempered
  configurations with the same Weil form on compact C² tests are equal, zeros and multiplicities
  included; the signed form carries the orientation. `SquareRootThreshold/CrystallizationHidesOffLineZeros`:
  `exists_offLine_superset_hiding`, adding off-line zeros to a configuration can restore
  finite-aperture positivity, so a positivity reading at finite aperture is not monotone in the zero
  set and cannot serve as an orientation detector.
- `RHTower/XiCosineShiftLaguerrePolya`, `RHTower/DeBruijnNewmanHalfBound`: the real-rootedness
  results that do exist are strip statements (Wall 4), not consequences of positivity.

Rule: when a construction yields a positive current, a positive-definite function or a positive
measure, ask what in it changes sign when a zero is reflected across the critical line. If nothing
does, the construction cannot locate zeros.

## How the walls are used

The producer loops apply three checks before building anything: name the wall the idea passes,
name the concrete input that passes it, and name the prime sum and exponent the idea ultimately
needs (Wall 1). The kills recorded in the [retired-mechanism ledger](../rh-killed-routes.md) are
rediscoveries of walls 1, 4, 5, 6, 7, 9, 12, 13 and 15. The structural reason, proved in the corpus,
is that the Weil cone is the single point Λ, that prime-blind positivity is node-critical, that the
ground-energy path has no uniform gap, and that every graded relaxation of a route is a zero-free
half-plane. A new mechanism therefore has to supply one of: square-root cancellation of a prime sum
(Wall 1), equality in Jensen for log|ζ| (Wall 2), a Frobenius-type fibration (Wall 5), a
Bochner-cone positivity transfer compatible with blindness (Wall 13), or a spectral realization of
the zeros on a definite Hilbert space whose prime part is as large as S(T) (Walls 12 and 14).
