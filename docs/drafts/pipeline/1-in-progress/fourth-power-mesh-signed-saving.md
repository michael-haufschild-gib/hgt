# Fourth-power mesh signed saving

- **ID:** fourth-power-mesh-signed-saving
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** ../../../reports/review-3010/opus.md, Question 2
- **Statement:** For every ε > 0 there is C ≥ 0 such that, for every integer J ≥ 2,
  `mobiusDivisorDilationPowerMeshCovariance 4 J ≤ C * (J : ℝ) ^ (3 + ε)`.

## Goal

Prove or refute this exact statement unconditionally and formalize the answer.
Criteria, weaker estimates, and obstructions do not resolve the question.

## Gates

- [x] Exact quantifiers checked in `QuasiRHPowerMeshMeanSquareAbscissa.lean`.
- [ ] Dependency-closed proof or refutation.
- [ ] Lean theorem; foreground `lake --old env lean` audit; standard axioms only;
  owning umbrella import.

## Mathematical state

`RHTower.xi_zero_three_quarters_strip_iff_powerMeshCovariance_subpower` identifies
the target with `∀ ρ : ℂ, xi ρ = 0 → 1/4 ≤ ρ.re ∧ ρ.re ≤ 3/4`.
The covariance differs from the literal tail square energy by a diagonal in
`[0, (9/25)J]`. The head costs at most `(9/25)J³` on this mesh.
Consequently the unpaid term is signed high-dilation cancellation, not either
of these already bounded contributions.

## Checked inputs and remaining gaps

- `mobiusHighDilationClippedAbelKernel_eq_full_add_terminal`: even `q = 1`
  retains a weighted Möbius prefix of length `M / 2` and a terminal sum.
  The quotient restriction `q < j` does not shorten that Möbius prefix.
- `mobiusDivisorFiniteClockEnergy_source_cancellation`: prime insertion pays
  a negative copied square but retains a signed mixed term. Its sign and
  cumulative size over growing prime cores remain unpaid.
- `mobiusDivisorFiniteClockEnergy_insert_cost_le`: the available absolute
  insertion cost contains `4^(P.card-1)`, hence gives no uniform growing-core
  estimate at the required exponent.
- `eventually_mobiusDivisorPrimeReleaseCoefficient_oriented_pos`: for each
  fixed nonempty core `P`, the large-prime release coefficient has sign
  `(-1)^(P.card+1)`. Unqualified insertion monotonicity therefore fails.
  `mobiusDivisorPreparedPrimeCube_unconditional` arranges all signs on a
  prescribed finite prime cube, but bounds neither total helper energy cost
  nor the cutoff threshold uniformly over growing cores.
- `twoScaleSquareCutoffMultiplier_lt_one`: the quarter-threshold contraction
  controls a common-head cutoff error. The full receiver-energy recurrence
  is an additional, unproved statement.
- `MobiusProductFibre.pair_sign`: grouping a nonzero Möbius pair by its product
  gives the single Liouville sign of that product. Cancellation between
  distinct product fibres remains necessary.
- `ArithmeticIndexDescent.exists_fullPolarNonfirst_gamma_approximation`
  retains the complete Gamma energy and both pole moments after removing a
  fixed detail head. Its source omits the coarse prime form and first-prime
  mixed block; the estimate does not bound the complete Weil form.

These facts are existing results, not a proof, refutation, or retirement of
the target. No saving for the complete signed source has been established.

## Verification

`lake --old env lean GaloisForLFunctions/RHTower/QuasiRHPowerMeshMeanSquareAbscissa.lean`
passes. A separate importing scratch file checked `#print axioms` for the
three-quarters equivalence, covariance comparison, and diagonal bound; all
depend only on `propext`, `Classical.choice`, and `Quot.sound`.
The requested upper bound and its negation remain unproved.

## Exact arithmetic content of the covariance

Write `M = j⁴`, `D = j³`, `F = primeFreeDivisorDefect`, `K(q) = mobiusHighDilationClippedAbelKernel M D q`.
Then `mobiusDivisorDilationTail M D = Σ_{q<j} F(q) K(q)`
(`mobiusDivisorDilationTail_pow_eq_Icc_pred_smallQuotient`), and by
`mobiusHighDilationClippedAbelKernel_eq_full_add_terminal` each `K(q)` is
`(√(q+1) − √q)·(Σ_{D<d≤M/(q+1)} μ(d)√d)` plus a terminal clipped Möbius sum over `(M/(q+1), M/q)`.
So the tail is a `j`-term combination of weighted Möbius sums over the hyperbola cells
`(M/(q+1), M/q]`, with divisor-side coefficients `F(q)`. The `q = 1` cell alone is
`F(1)·Σ_{j³<d<j⁴} μ(d)(√min(M, 2d) − √d)` with `F(1) = 2γ − 1 ≠ 0`: a smoothed Mertens
sum over `(M^{3/4}, M)` of trivial size `M^{3/2}`, target `M^{5/4+ε}`.
The full covariance target is equivalent to the `3/4` strip. An upper bound for
the full signed sum does not separately bound its `q = 1` summand.
`powerMeshEnergy_exponent_eq_sInf` identifies the Abel-energy exponent as
`8Θ − 3`; it does not state an exact covariance exponent. The comparison with
covariance has an additional `O(J³)` head cost. Thus a covariance bound with
exponent below `5` would give a fixed strip, but the comparison alone does not
identify the covariance exponent below `3`.

## Conjecture ledger

| # | Mechanism | Verdict | Lesson |
|---|---|---|---|
| L1 | Bound the `q = 1` cell by a Mertens estimate | equivalent estimate unproved | needs `M(x) ≪ x^{3/4+ε}`; `zetaZeroAbscissa_le_of_moebius_power_bound` transfers this to the required strip |
| L2 | Mesh averaging: treat `M(j⁴)`, `j ≤ J`, as decorrelated samples | unproved cancellation | `exists_powerGap_pow_samples` transfers sampling gaps; it is not a Mertens mean-square estimate. The proved Abel-energy exponent is `8Θ − 3` in the mesh index. |
| L3 | Plancherel: mean square of the tail via `∫|1/ζ(σ+it)|²/|s|²` | analytic bound unproved | the required reciprocal-zeta integrability must be established independently |
| L4 | Pair the divisor fluctuation `ΔF(q) = log q + 2γ − τ(q)` with `M(M/q)` | signed correlation unproved | the full hyperbola sum is `ψ(M) − M` (`psiDefect_eq_mobius_primeFreeDivisorDefect`); independence is not supplied by the identity |
| L5 | Voronoi expansion of `Δ(q)` and stationary phase in `q` | oscillatory estimate unproved | the remaining `Σ_d μ(d) d^{1/4}·(phase)` still needs a signed estimate at scale `M` |
| L6 | Refute: show the covariance exceeds `J^{3+ε}` | unproved | would exhibit a zero with `Re ρ > 3/4`; the inspected inputs establish no such zero |
| L7 | Zero density (`exists_zeroHeightBox_ncard_le_gm_unconditional`, 30/13) with VK region | no strip | density counts zeros; one zero at `σ > 3/4` is not excluded (`DensityEnvelopeNoGo`) |
| L8 | Dirichlet-polynomial mean values and large values (`dirichlet_meanValue_theorem`, `largeValues_dirPoly`) | no strip | they produce density estimates, which is L7 |
| L9 | Vaughan Type I/II decomposition of `μ` on `(j³, j⁴)` | signed block bound unproved | `zetaZeroAbscissa_lt_one_iff_uniform_pmUndampedVaughan_power`: the saving would produce a fixed strip; the exponent still matters |
| L10 | Short-window Möbius saving | window estimate unproved | `zetaZeroAbscissa_lt_one_of_moebiusPowerWindowSaving` supplies the transfer, not the saving |
| L11 | Positive normalisation or Cauchy–Schwarz on the channels | sign-blind | `not_mobiusDivisorDilationPositiveMeshEnergy_le_pow`: envelope `≍ J^5`, never `≤ CJ^4` |
| L12 | Complete Weil positivity at a growing overlap `c_N → ∞` as a strip producer | open elsewhere | a slowly growing schedule is compatible with every zero (visibility needs `log N ≲ c^{1+2δ}/A(c)`); an explicit rate is review Question 1 |
| L13 | Prime grouping / successor pairing of channels | insufficient | first pairing contracts the diagonal only (`MobiusDivisorPrimePairEnergy.sum_mobiusDivisorPrimePair`); the ordered covariance is untouched |
| L14 | Any argument using only `μ ∗ 1 = δ`, `|F(q)| ≤ 24√q`, partial summation, Perron | cannot decide | `regular_integers_do_not_constrain_zeros`, `overRegular_integers_do_not_constrain_zeros`: these inputs hold for Beurling systems with `N(x) = ρx + O(x^θ)` for every fixed `θ > 0`, or with `N(x) − ρx → const`, that have a zero at any `β ∈ (1/2, 1)`; the equivalence proof transfers, so the covariance bound fails there |

The equivalent Möbius and `ψ` estimates remain valid research targets; assuming
them would leave the required arithmetic input unproved. The inspected absolute
bounds and identities do not establish `Θ ≤ 3/4`. No proof or refutation of the
requested covariance bound has been obtained.

## Proof mechanisms and candidate replacement

- **Exponential cost is an estimate, not a lower bound.** In
  `MobiusDivisorLocalizedInteractions`, repeated `|a-b| ≤ |a|+|b|`
  produces `4^(P.card-1)`. `mobiusDivisorSelectionEnergy_mixed_eq_filter_cutoff`
  removes all processed primes outside the child quotient cutoffs when `pq ≥ M`.
  Whole-block cancellation can therefore exploit information discarded by
  summing individual insertion bounds.
- **Fixed-core cancellation does not control simultaneous growth.**
  `tendsto_mobiusDivisorSelectionHead_div_sqrt_zero` cancels the common unsigned
  leading term using `Σ_{d|prod(P)} μ(d)=0`. Its threshold depends on `P`.
  `exists_mobiusDivisorPaidPrimeExhaustion` does give exhaustive paid insertions,
  each at its own cutoff; it does not bound cutoff transport or the complete
  endpoint. `mobiusDivisorSelectionHead_add_terminal_leaves` retains the latter
  as the head plus the entire signed singleton sum.
- **One uniform positive input is already available.**
  `mobiusDivisor_physicalCutoff_synchronized_energy_lower` has a common physical
  cutoff for every prime core. The exact insertion comparison still contains
  `mobiusDivisorPhysicalCorrelation_annulus_eq`, a signed annulus depending on
  that core. Its sign is not a consequence of the positive moment.

**Research hypothesis:** a complete-block estimate can couple these annular
terms to the quotient fields before taking absolute values, retaining both
cutoff transport and terminal completion. A sufficient pointwise output is
`|mobiusDivisorSquareRootAbelMoment M|² ≪_δ M^(5/2+δ)` for every `δ>0`;
this would give the requested mesh bound. No such block estimate is proved.
The concrete test is whether the annular differences cancel when the core
changes: fixed-core telescoping alone does not justify that cancellation.
For the full-ray correlation `C_P(Y)`, `mobiusDivisorDilationMean_insert` gives
`C_(P+p)(Y) = (1+1/p) C_P(Y) - p^(-3/2) C_P(pY) - sqrt(p) C_P(Y/p)`.
Thus a closed block comparison must retain correlations at both multiplied
and divided ratios, together with their finite-cutoff boundary terms.

The finite law already exists in `MobiusDivisorCriticalClockProductTransport`.
Write `h_P(t)=H_P(exp t)/exp t`,
`A_P(T)=∫_{t≤T}(T-t)h_P(t)² dt`,
`B_P(a,T)=∫_{t≤T}(T-t)h_P(t+a)h_P(t) dt`, and
`ρ_P=squarefreeDensity·∏_{p∈P}p/(p+1)`. For a fresh prime `p`, `a=log p`,
`mobiusDivisorCriticalClockTriangularPairing_density_cancellation` proves

`ρ_(P+p) A_(P+p)(T) - ρ_P A_P(T) + 2ρ_P√p/(p+1) B_P(a,T-a)
 = -ρ_P/(p+1)·(A_P(T)-A_P(T-a)) ≤ 0`.

Thus the copied diagonal and clock-boundary surplus are already paid; the
arithmetic estimate must control the cumulative signed `B_P` terms with the
changing core and complete endpoint retained.

Two exact facts constrain that estimate:

- `MobiusDivisorPrimeBlockEnergyEscape` proves superpolynomial full-ray energy
  beyond every cutoff `y^A`, even for the natural core of all primes at most
  `y`. A bound on those full-ray energies cannot supply the finite estimate.
- For `g(t)=exp(-3t/2)·criticalContinuousAbel(exp t)` and
  `R(u)=∫g(t+u)g(t)dt`, the proved source moments are
  `∫g=0`, `∫tg=-divisorHarmonicBoundary/3`, and
  `∫u²R(u)du=-2(divisorHarmonicBoundary/3)²<0`.
  `MobiusDivisorCriticalFiniteCorrelationSign` also gives a negative original
  finite-cutoff pairing; `MobiusDivisorCriticalCorrelationTailSign` gives
  negative boundary correlations beyond every lag. These statements do not
  assert negativity at prime lags, but rule out universal correlation positivity.

**Refined hypothesis:** use the zero-mass cancellation in the actual finite
prime-weighted block, retaining its quotient and terminal terms together.
Polynomial signed moments alone do not bound the exponentially weighted
finite-clock remainder. A uniform bound for that remainder is still missing.

## Terminal structure and a recursive hypothesis

Write `T(x)=criticalContinuousAbel x`, `P_M=criticalMovingSquareCore M`,
`h_M=mobiusDivisorSelectionFibre M P_M ∅`, and
`S(M)=Σ_{p∈selectionPrimes M\P_M} p·T(M/p)²`.
The exact terminal identity is `T(M)=h_M−Σ√p·T(M/p)`.
The quotient envelope gives `S(N²)≤(9/25)N⁵`; see
[terminal leaves](../3-formalized/terminal-leaves-fit-the-fourth-power-mesh.md).
The canonical head nevertheless satisfies
`h_M∼−(divisorHarmonicBoundary/3)M^(3/2)/log²M`.
Thus a target-scale bound on every intermediate retained energy fails along
the natural increasing-prime order. The full signed head correction must
be retained before estimating the endpoint.

**Unproved recursive hypothesis:** for every `δ>0`, uniformly in integer `M≥2`,
`T(M)² ≪_δ M^(1/4+δ) S(M)+M^(2+δ)`.
If `T(x)²≪x^a`, `a>2`, the quotient range `M/p<√M` gives
`S(M)≪M^(1+a/2)`. The proposed estimate would improve `a` to
`5/4+δ+a/2`. Choosing `δ` small and iterating from `a=3` reaches any
exponent above `5/2`. A subpower loss instead of `M^(1/4+δ)` would drive the
same recursion to the stronger RH scale `a=2`. Neither estimate is proved.

An existing source-specific cancellation illustrates the required distinction:
`mobiusSquareShortBilinearKernel_terminal_moebius_row` collapses an entire row
by divisor inversion, although that kernel has a negative principal minor.
The proof uses complete divisor coverage; interior rows lose that coverage.
It does not supply the proposed recursive estimate.

## Where the cyclic energy still needs arithmetic cancellation

At conductor `Q=N+1`, write `a_j=chebyshevConductorCoeff j`,
`ζ_k=exp(2πik/Q)`, and `B_Q(k)=Σ_{1≤j<Q} a_j(1−ζ_k^j)`.
The exact cyclic difference gives `(1−ζ_k)P(ζ_k)=B_Q(k)`.
The new [cyclotomic tail theorem](../3-formalized/cyclotomic-tail-fits-three-quarters-scale.md)
proves that modes with `min(k,Q−k)>⌈√Q⌉` already cost at most `288 N√Q`.
This uses only `|a_j|≤6/√j`; no signed prime estimate enters.
Moreover `Q≤orderOf(ζ_k)·min(k,Q−k)`: fixed primitive conductors eventually
lie in the paid far part. The remaining low angular frequencies have growing
primitive conductors.

**Unproved low-mode hypothesis:** uniformly for `1≤k≤⌈√Q⌉`,
`|B_Q(k)| ≪_ε Q^(1/4+ε)√k`. Conjugate symmetry and the root-gap bound
would then give near energy `≪_ε Q^(3/2+2ε)log Q`, hence the target.
This is a candidate arithmetic estimate, not a producer of that estimate.
Its proof must retain cancellation in the whole coefficient prefix before
taking absolute values; better estimates of the far modes cannot supply it.

The existing one-sided strip law also permits a lower bound
`T(M)≥−C_ε M^(5/4+ε)` in place of a square bound. Its observer-history
two-zone estimate still requires a bound for the actual Chebyshev error
throughout the remaining interval; that hypothesis is not discharged.

A separate [quantitative blind-repair hypothesis](quantitative-blind-repair-for-the-quarter-strip.md)
asks whether modular null witnesses can remove node and pole readings while
preserving negative energy with mass cost `exp((1/2+ε)A)`. The existing
minimum principle proves uniqueness; neither it nor qualitative divisor
inversion proves this cost bound.

## Inputs of `ℤ` absent from the Beurling models, tested as producers

| # | Input | Where it enters | Verdict for the `3/4` strip |
|---|---|---|---|
| Z1 | Integer count `N(x) = x + O(1)` | distinguishes `ℤ` from the continuous models, which reach only `N − ρx → const` with zeros in `(1/2, 2/3)` (`overRegular_integers_do_not_constrain_zeros`) | positive integer residues force real zeros (Herglotz), so complex zeros need negative residues; a rational model with many poles near `0` and zeros interlaced cannot keep the prime density nonnegative for `β` near `1`, but non-interlaced designs are not excluded. Whether `O(1)` regularity constrains zeros is open; nothing in the corpus uses it |
| Z2 | Functional equation (Poisson summation) | Beurling zetas have none | `LambdaPositiveFunctionalEquationOffLine` preserves a nonnegative generalized logarithmic density but introduces poles at `1/2±c`; it does not preserve holomorphy of the actual completion. With entire completion and simple pole, `completedPositiveSystem_one_iff` instead identifies a real multiple of ζ. That rigidity theorem supplies no zero-strip bound. |
| Z3 | Exponential sums `Σ n^{−it}` (van der Corput, Vinogradov) | growth of `ζ` left of `1` | enters zero-free regions only through the `3-4-1` positivity at `σ ≥ 1`; `ζ` is unbounded on every line `σ ≤ 1`, so the region is always `1 − c/(log t)^a`; Lindelöf itself gives no strip |
| Z4 | Dirichlet characters, large sieve, level of distribution | `TheShellsHaveLevelOfDistributionOneHalf` | bounds the trivial point only by the total over conductors; Bombieri–Vinogradov adds Siegel–Walfisz, i.e. log savings |
| Z5 | Ramanujan sums / successor shells in the complete Weil form | `TheShellsRepayEveryConductor`, review Question 1 | Growing-overlap synthesis is RH-complete at its proved rates. A bounded Denjoy–Carleman rate `K` also gives positivity on tests supported in `[-R,R]` when `24e Bφ ceil(1+exp(2(R+1))) < K` (`nonneg_of_atomicFamilies_nonneg_of_rate`). This is a bounded-window receiver; no inspected theorem converts it into an all-height `3/4` strip. |
| Z6 | Finite-field cancellation (cubic and sextic Gauss sums over `ℤ[ω]`) through Eisenstein-series Gram matrices: the Chen–Gupta–Li / `tmp/hgt-openai-math/quasirh-source` detector | external claimed producer `OAI.riemannZeta_ne_zero_of_seven_eighths_lt_re` in `OAI/NumberTheory/DirichletL/Nonvanishing.lean`; source present, dependency and kernel audit incomplete, frontier status `[E]` | its displayed exponent model has boundary `x/2 + gram/2 − (x/3 − 5/6 + L/6) + reflectedLoss/2`; with the unit Gram term alone the minimum is `29/36` at `x = 0`, `L = 1/6` (`unitGramBoundary_sharp_minimum`, `gramProfileBoundary_gt_three_quarters`). The slot-length source fixes the sum to `1/6`; the checked exponent proof identifies this as the balance point of the principal gain and reflected allowance. No theorem tying that budget to the number of Eisenstein units has been verified. Reaching `3/4` needs a new principal normalization, unit term, or reflected allowance, not sharper estimates of the displayed terms |

Consequence for the statement on this card: by
`zetaZeroAbscissa_le_iff_mobiusDivisorDilationPowerMeshCovariance_subpower` at `s = 2`, `b = 7/8`,
the external theorem is equivalent to `mobiusDivisorDilationPowerMeshCovariance 4 J ≤ C J^{4+ε}`.
The `J²` saving over the envelope `J⁵` splits as one power delivered by the detector, pending its
audit, and one power that is exactly the gap `7/8 → 3/4`, below the detector's model floor `29/36`
(mesh exponent `31/9`).
