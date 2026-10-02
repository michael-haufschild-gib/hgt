# MC: complete signed correlation at the current cutoff

- **ID:** MC-COMPLETE-CORRELATION-2026-10-01
- **Stage:** 1-in-progress
- **Type:** HARD OPEN CANCELLATION PROBLEM
- **Route:** MC

## Fixed target

Prove, without an input cancellation hypothesis, a uniform quadratic ceiling for the fully completed actual Abel source. Write `c_M(d)=mobiusDivisorDilationChannel M d`. The concrete conjecture is

`∃ C>0, ∀ M, ∑_(r=1)^M mobiusDivisorGcdCross M r ≤ C M²`.

The inspected source already proves the exact identity

`∑r GcdCross(M,r) = (∑d c_M(d))² - ∑d c_M(d)²`,

and the literal diagonal bound `∑d c_M(d)²≤(9/25)M²`. Thus the proposed new inequality would control the complete signed square. Neither identity nor the diagonal estimate is a research deliverable; the signed off-diagonal estimate is the hard target. The precise receiver is now verified in source: `CCMFUSuzukiMobiusDivisorAbelProducer.riemannHypothesis_iff_mobiusDivisorSquareRootAbelBounded`, where boundedness means `∃B≥0, ∀M≥2, |mobiusDivisorSquareRootAbelMoment M/M|≤B`. `MobiusDivisorQuadraticCompletionSPEWeld` contains the audited source-to-square-root conversion. No new receiver theorem is needed.

## Corpus basis

- `MobiusDivisorAbelGcdCross.sum_mobiusDivisorGcdCross` retains every common-divisor component, every sign and every cutoff.
- `mobiusDivisorGcdCross_mul` factors a common dilation into `r μ(r)²` times the primitive coprime cross term with both exact coprimality masks. These masks must remain.
- `MobiusDivisorUniformSuccessorTransport.mobiusDivisorSelectionEnergy_empty_le_nine_twentyFifths_sq` gives the already-known quadratic diagonal ceiling.
- `MobiusDivisorFiniteClockCountingCancellation` gives exact prime-insertion mixed work and a negative copied-square term. At full processing the zero-offset triangular clock is identically zero; it cannot bound the retained head. Offset one retains the entire head square.

## First proof attack

Keep the actual finite clock. Regroup the signed cross work by its common divisor and primitive cofactor pair, then test whether joint summation over the exact squarefree/coprime common-divisor source pays the potentially positive primitive cross terms. Do not demand a false componentwise sign and do not replace the joint source by arbitrary vectors. The difficult step is uniform control when the primitive cofactor range grows with `M`, not the fixed-core average.

The common-divisor factorization is currently exact only at aligned cutoffs `r*M`; the preexisting homothety/finite-clock source must be inspected before using it at a general cutoff. If a truncation identity is needed for the proof, build it as an ingredient, but do not report the identity itself as solving the signed estimate.

## Lessons carried forward

- Finite local descent and quantitative local payments do not imply exhaustive completion.
- Literal terminal-window cores, and now natural initial-prime cores in the verified scratch proof, have superpolynomially delayed limiting physical energy. A uniform bounded infinite-clock coefficient is unavailable. This does not refute the current-cutoff estimate.
- The new objective is not to sharpen the energy-escape constants or create another receiver. Hold this signed complete-source target through failed sub-conjectures; derive an actual cancellation law or a rigorous obstruction to a proposed mechanism.

## Status

Open conjecture. No new complete signed-correlation bound, RH proof or RH falsification. Search coverage for complete/empty energy was partial with a snapshot; candidate lemmas and source arguments were inspected against the listed source files.


## First sub-conjecture audit

Separate signs for the common-divisor pieces are false on the actual source: `MobiusDivisorGcdCrossObstruction` proves the `r=1` component positive at `M=11`, while the complete sum there is negative. Prime homothety makes those positive components unbounded. This strengthens the reason to retain their joint sum; it does not refute the target quadratic upper bound.

The tempting fixed-core density replacement is also insufficient. After common-divisor averaging and the exact Mellin pairing, the local coprime-mask factor is

`1 - 2*sqrt(p)/(p+1)*cos(t log p)`

which equals `p/(p+1)*|1-p^(-1/2-it)|²`. Thus its full product is exactly the density-weighted Euler energy already shown to escape for natural initial-prime cores. This algebraic observation needs its own source-signature check before use in Lean, but it explains why an infinite-clock density main term cannot simply be declared uniformly bounded.

Continue on the same hard target: retain finite support in the joint common-divisor sum and control its signed cofactor interaction. Do not replace this missing estimate by another fixed-core limit, componentwise sign assumption or abstract-vector norm bound. The current proof attempt has not produced the quadratic off-diagonal ceiling.

## C12.1: processed-core covariance and coprime inversion audit

`MobiusDivisorArityHeadCoreDiagonal` already proves every same-processed-core adjacent residual pair dissipative. `MobiusDivisorArityHeadProcessedCoreParity` identifies every positive pair as an opposite-parity pair of processed cores. `MobiusDivisorArityHeadProcessedCoreSignedMeasure` expresses the residual-oriented field as the alternating sum of the positive individual core coordinates. Positivity of those coordinates therefore does **not** prove a sign for their sum or for its mixed covariance. No new positivity theorem follows from this inspection.

The proposed collective coprime-column inversion also fails to supply an estimate. The exact existing theorem `mobiusDivisorCoprimeHead_eq_supported_abel` returns

`H_r(M) = Σ_(k<M) (sqrt(k+1)-sqrt(k)) Σ_(n≤k, primes(n)⊆primes(r)) psiDefect(k/n)`.

The outer pairing still has its literal Möbius signs. Estimating the displayed signed Chebyshev defect by the desired half-power bound would insert the missing cancellation as a premise. Neither the inversion nor the core-coordinate orientation closes C12. These are failed deductions from existing results, not new formalized no-go theorems.

## C12.2: square-root split and a possible inductive cancellation law

The next proposed mechanism retains the joint interaction while making every child cutoff smaller. The inspected `MobiusFriableLargestPrimeDecomposition` already proves the exact Mertens split below the first square seam, with complete smaller-cutoff cofactors. Applied to the literal continuous Abel channels, the paper-level split is as follows. For an integer `Y` with `x<Y²`, put

`H_Y(x)=mobiusDivisorContinuousHead (Nat.primesLE Y) x`,

`S(x)=mobiusDivisorFullHead x`, and

`B_Y(x)=Σ_(Y<p≤x, p prime) sqrt(p) S(x/p)`.

Every active nonsmooth index has exactly one prime above `Y`, so exact homothety suggests `S(x)=H_Y(x)-B_Y(x)`. The general continuous-cutoff version is **not newly audited in Lean** here. Floor endpoints must be retained if it is needed in a proof. Merely formalizing this split would not be progress on the hard estimate.

The substantive conjecture to attack is an unconditional ceiling on the signed excess

`S(x)² - Σ_(Y<p≤x, p prime) p*S(x/p)²`,

at scale `x²`, with `Y` just above `sqrt(x)`. This must come from the joint smooth-head/child covariance, not separate absolute estimates on `H_Y` and `B_Y`. At the level of a proposed induction, a bound `|S(u)|≤C*u` at the smaller arguments makes the child square sum at most `C²*x²*Σ_(Y<p≤x) 1/p`. A strict eventual ceiling below one for this reciprocal-prime mass would make a **proved** excess bound useful. Neither that analytic input nor the excess bound is claimed newly established here; do not spend a turn adding an induction receiver while leaving the excess untouched.

**Progress judgment:** this continuation found no new unconditional signed bound and did not move the cancellation frontier. It identified the exact unsupported steps in the orientation and inversion attempts. The next work must attack the signed excess itself, or obtain another actual estimate for the original C12 sum. RH remains unproved and unfalsified.

## C12.3: exact terminal split located; no covariance estimate obtained

The next corpus search located the already-formalized finite-cutoff version of C12.2 in `MobiusDivisorAdaptiveTerminalCriticalSource`. Its source was read. For every core covering all active primes with `p²≤M`, each remaining singleton is exactly

`-sqrt(p) * criticalContinuousAbel(M/p)`.

`adaptive_terminal_head_source` and `adaptive_terminal_energy_source` give the head and full energy with those literal fractional child cutoffs. `criticalContinuousAbel_nat_eq_dilation_sum` identifies the complete integer head. Thus the finite split does not need a new formalization. The missing signed-excess inequality remains missing: neither the exact identity nor bounds on the child squares control the square of the smooth head minus their aggregate.

The inspected `MobiusFriableDelayEquation` only proves identities and uniqueness for explicit delay profiles. Its imported profile file explicitly does not assert the analytic friable-sum theorem. Applying those profiles to the literal source without an error estimate would add an unjustified premise. No induction contraction was obtained.

## C12.4: critical primitive sign mechanism tested

A different attempted route to one-sided source control was to extend finite-clock positivity of the inverse-cube primitive to the critical inverse-square primitive. The exact proof in `MobiusDivisorTruncatedMomentCancellation` uses divisor weight `sqrt(d)/d²=d^(-3/2)` and bounds **all odd-parity divisor weight** below one. For an inverse-square primitive, dilation instead gives `d^(-1/2)`. The singleton-prime part alone then has unbounded total mass as the core grows, so the same unit-versus-negative-mass argument cannot establish a sign or a uniform lower bound. This failure concerns the proposed argument; it is not a proof that the complete critical primitive lacks a lower bound.

The full-source Mellin and prime-feedback statements must also remain distinct. `MobiusDivisorCriticalSourceSimpleJet` gives a simple zero of the complete source transform at its first convergence boundary. `MobiusDivisorCriticalPrimeNegativeEscape` concerns the **sum of prime dilations** of that source, not the source itself. Its negative linear escape therefore does not falsify the desired full-head bound. No estimate for the square-root prime window was inferred from that all-prime statement.

**Outcome:** no new unconditional signed bound, no new mathematical theorem, and no Lean changes in this continuation. The searches supplied partial snapshot coverage, not a corpus-wide absence certificate. Source checks prevent duplicate split/receiver work and invalid sign transfers, but do not constitute progress on RH. Continue with the joint covariance in the existing terminal-source coordinates; an actual estimate is required.

## C12.5: direct arithmetic pairing attempt

The attempted pairing started with literal squarefree pairs `(d,e)`, keeping the current cutoff and common-divisor masks. Redistributing prime factors while preserving `d*e` cannot reverse the cross-term sign: `mu(d)*mu(e)` is `(-1)` to the total number of prime factors of `d*e`, counted with multiplicity. This invariant rules out that particular cancellation map. It is a paper screening observation, not a newly audited Lean theorem or a retirement of MC.

Deleting a prime from one coordinate reverses its sign but loses the deleted label. For example, all pairs `(2,p)` with odd prime `p` would collapse to `(2,1)`. Preserving that label by inserting `p` into the other coordinate instead gives `(2p,p)`, but requires `2p≤M` and does not make the new unsigned weight dominate the old one. More generally, `(d,p*b) -> (p*d,p*b)` requires `p*d≤M`; the unpaired boundary cannot be discarded. No bounded-multiplicity payment covering the complete positive cross source was obtained.

Product-changing near matches avoid the fixed-product parity invariant, but the available source results do not exhaust the source. The inspected statement `MobiusCofactorLayerExtraction.exists_layer_extraction` constructs equal-cardinality positive/negative subsets of size at least `c*R`; it does not cover every atom or promise the same supply after arbitrary prior deletions. `MobiusMultiplicativeRectangleCubature` controls the cost of constructed rectangles and explicitly leaves the arithmetic covering and uncovered residual open. Iterating either result without a depletion/coverage theorem would be an unsupported step.

**Remaining hard task:** construct a product-changing collective transport with controlled collisions, weight changes and uncovered signed residual, or directly bound the complete C12 covariance. No new bound, proof, falsification or Lean edit resulted from this attempt. The deep pairing search completed its stages (`partial=false`) with snapshot coverage; no corpus-wide completeness claim is made.

## C12.6: divisor summation by parts does not yet control the covariance

Write `u_M(d)=divisorUnsignedDilationChannel M d` and `m(d)=Σ_(n≤d) μ(n)`. Since `u_M(M)=0`, ordinary finite summation by parts gives the paper identity

`S(M)=Σ_(1≤d<M) m(d)*(u_M(d)-u_M(d+1))`.

This preserves the literal source, but no estimate for this signed pairing was obtained. Replacing it by an absolute variation bound requires control of the Mertens prefixes and discards the cancellation still needed. The nonnegative-channel theorem is insufficient: it says nothing about the signs of these differences.

Moreover, monotonicity in the dilation index is false on the actual channels. The inspected `MobiusDivisorQuadraticFirstDefect.divisorUnsignedDilationChannel_two_clipped_reversal` proves `u_M(2d)-u_M(d)≥sqrt(d)/100` when `d>0`, `7d≤M`, and `10000*(M-7d)≤d`. This is an existing theorem, not a new obstruction. Separately, `MobiusDivisorMonotoneWeightObstruction` already disproves diagonal dominance for arbitrary positive decreasing **time** weights. That counterexample does not settle the fixed half-order weight in C12; the two index variables must not be conflated.

Both new deep searches returned partial snapshot coverage. Candidate lemmas and source arguments were inspected; irrelevant projective-Möbius hits and conditional correlation bounds were not treated as source cancellation. No new theorem, covariance ceiling, RH proof or RH falsification resulted. No Lean source changed or was rebuilt. The next attack must estimate the actual signed difference pairing or the existing terminal-source excess, rather than add another Abel identity or assume a Mertens bound.

## C12.7: logarithmic insertion / Selberg attempt

The proposed mechanism was to sum the signed prime interactions with logarithmic weights and use the literal Selberg relation to control their joint sign. The inspected `SelbergSymmetryCore.abs_psiDefect_selberg_core` bounds

`|F(N)*log N + Σ_(k≤N) Λ(k)*F(N/k)| ≤ 384*N`, where `F=psiDefect`.

This is not a critical-scale covariance estimate. Applying the half-order time weights to its absolute error leaves an allowance of order `M^(3/2)` for a linear Abel expression. Multiplying by the unknown signed head does not supply the quadratic ceiling. Retaining the exact Tatuzawa–Iseki right side instead retains its Möbius-weighted divisor source; no new bound for that signed expression was obtained. This only rejects the attempted deduction from the coarse Selberg bound, not a proof using the exact relation.

The arity-head history law already retains the head–singleton interaction and every nonempty copied-child square. It does not supply a sign for the accumulated charge. The inspected cutoff-22 successor-average counterexample also cannot be promoted to a statement about all large-energy states. No such promotion was made.

## C12.8: source-specific large-energy descent conjecture

A concrete alternative sub-conjecture, still **unproved**, is:

There is a universal `C≥9/25` such that, for every cutoff `M` and every incomplete processed core `P⊆selectionPrimes M`,

`C*M² < E(M,P) → ∃p∈selectionPrimes M \ P, E(M,insert p P)≤E(M,P)`.

Here `E` is the literal selection energy, not a coarea envelope or limiting energy. Nonincrease suffices; no lower bound on payment size is requested. The paper motivation is finite: a single merger has energy at most twice the preceding energy by `(a+b)²≤2(a²+b²)`. Below the threshold one may insert a remaining prime; above it the conjecture would provide a nonincreasing insertion. Every step removes one remaining prime, so the complete endpoint would stay below `2*C*M²`. This is a proposed sufficient mechanism, not a newly formalized receiver or a proved source bound.

The terminal case exposes the unresolved arithmetic precisely. With head `H`, leaves `b_p`, and complete source `S=H+Σb_p`, one insertion changes energy by `2*H*b_p`. If `H≠0` and every remaining leaf has its sign, every insertion increases energy and `|S|≥|H|`. Excluding such states at arbitrarily large normalized energy requires actual source cancellation; positivity of channel magnitudes and small-energy terminal-core existence do not exclude them. Existing fixed-core eventual descent and prepared-helper results have core-dependent onsets and do not prove this all-cutoff statement. No uniform drift bound has been obtained.

**Turn outcome:** no new mathematical frontier result, Lean theorem, or RH proof/falsification. Four searches (terminal excess, logarithmic generator, possible oscillatory transform, large-energy descent) returned partial snapshot/pending coverage; their candidate/source fields were inspected. The generic `GammaRCubeVoronoiL2` isometry does not by itself represent or estimate the literal divisor source. No missing analytic representation was assumed. Continue attacking the signed source estimate; do not turn C12.8 into another conditional module while its arithmetic premise is open.

## C12.9: actual last-two-prime test

The next attempt tested C12.8 on a core with exactly two unprocessed primes. If its four literal fibres are `a,b,c,d` at labels `∅,{p},{q},{p,q}`, the two insertion costs are `2*(a*b+c*d)` and `2*(a*c+b*d)`. Neither sign has been proved at arbitrary cutoff. A freely chosen four-coordinate counterexample would not refute the arithmetic conjecture, so none was treated as such.

`MobiusDivisorTwoPrimeLocalCriterion` concerns the **first two processed primes**: its four oriented coefficients are nonnegative unsigned channels. Its factor-two comparison cannot be applied to the **last two unprocessed primes**, whose fibres already contain signed sums over the processed core. `MobiusDivisorCoprimeHeadDeletion` supplies the exact masked, clipped two-scale renewal relation; deleting its coprimality restriction or replacing its head by a nonnegative unsigned channel would invalidate the test.

At the paper level, retaining both masks writes the four coordinates as copies of the same coprime head at `x,x/p,x/q,x/(pq)`. Iterating the inverse deletion relation expresses that coprime head through the complete source at `x/(p^i*q^j)`, with coefficients `p^(i/2)*q^(j/2)` and literal finite support. A critical bound on those complete-source values would bound the four coordinates, but it is not an available premise. This observation supplies no new signed estimate or unconditional counterexample and was not added as another Lean identity/receiver.

A current exact-name scan of `MobiusDivisorSquareRootAbelBounded` found the original criterion, equivalence handoffs, and a use under `CompletedSourceObserverJetLinearActionBounded`; the inspected occurrences do not establish an unconditional producer. This was a scoped source check, not a claim that every possible RH declaration has been audited. The two-prime deep search completed its stages with snapshot coverage (`partial=false`).

**Outcome:** C12 and C12.8 remain open; no new mathematical frontier result, Lean change, build, or RH proof/falsification. The attempted transfer from initial to terminal fibres failed because it removed already-processed signed interactions. Continue on the actual signed products; fixed-core eventual descent and an abstract four-vector calculation cannot replace their uniform arithmetic control.

## C12.10: cross-core copying, normal-breadth capacity, and degree cancellation

The copied-core bilinear identity scales the inherited sector by the new prime. It does not include the newly born background or its cross interaction with that sector. Consequently it gives no payment for the complete C12 covariance. Likewise, the existing exact dyadic cofactor kernel is positive, but its outer coefficients still have both Möbius signs. Neither positivity statement was promoted to a sign for the complete sum.

The next attempted mechanism was normal-breadth composite transport, an explicitly open MC branch in the frontier map. The actual proof of `Sieve.lowBreadth_cell_matching` spends a strict cardinal surplus: all low-breadth sources together have size at most half the lower bound for targets of either sign. Deleting the entire source set still leaves enough targets. This argument does not extend to the bulk normal-breadth sector merely by reusing its target-count theorem. Extracting another balanced subset removes the same number of both signs and therefore leaves the residual sign imbalance unchanged.

`RouteEProductTruncatedReservoirMass` does allow variable breadth. Its explicit lower bound retains the collision loss `choose(b,2)/(W*S)` and the product-tail loss `b*(log U+C)/(S*log T)`, where `S` is the reservoir harmonic mass. These are weighted allocation labels. They do not establish the number of distinct physical targets, all-subset capacity after depletion, or the cutoff seam estimate. `MobiusWholeAnchorCapacityDisplacement` already retains band decoding, literal parity reversal, displacement, and physical-column capacity conservation. Recovering a reservoir label from a target cannot increase the cardinality of the target set. No new Hall estimate was obtained.

An attempted alternative kept a symmetric opposite-sign incidence `U` and sought cancellation through its weighted degrees. The exact identity

`Σ_n μ(n)*degree_U(n) = 0`

is already formalized as `routeE_sum_sign_mul_rowMass_eq_zero`. The same file, `RouteESignedNormalizerFluxCircularity`, also proves

`Σ_n μ(n) = Σ_n μ(n)*(1-degree_U(n))`.

Thus replacing the source by its signed degree defect is an exact rewriting, not an independent estimate. Row normalization moves the same imbalance into signed incoming-mass flux. `MobiusBoundaryOppositeSignTransport` and `RouteEDegreeNormalizedGibbsBoundaryVariation` already supply the unused-capacity and reciprocal-degree-variation consumers. `RouteESignCompletePhysicalDegree` makes the arithmetic issue explicit for the graph joining all opposite-sign shell endpoints: twice a vertex's degree is squarefree shell mass minus its sign times the shell Möbius sum. Bounding that degree through an unproved shell cancellation bound would insert the missing source estimate again. No estimate for the actual restricted prime-replacement degrees or their signed defect was proved.

**Outcome:** no new mathematical frontier result or unconditional source bound; no Lean changes, builds, numerical experiments, new no-go theorem, or route retirement. All five searches terminated. The cross-core search completed its stages with snapshot coverage; the all-arity, normal-breadth, depletion, and degree searches were partial, with snapshot or pending coverage. Candidate and source-argument fields were inspected. Suggested ingredient sets were not treated as proofs. This is a record of failed deductions, not a claim of corpus-wide absence or RH progress.

**Next attack:** return to the complete signed covariance or the terminal-source excess of C12.2. New work must estimate their actual arithmetic cross terms, preserving masks and current cutoff. Adding a variable-breadth counting schedule, degree identity, or conditional flow receiver would leave the hard problem unchanged.

## C12.11: cutoff drift retains an unpaid mixed arithmetic product

This continuation tested whether the actual cutoff evolution could bound C12 without a prime-selection schedule. Put

`A_M = mobiusDivisorSquareRootAbelMoment M`,
`R_M = psiRemainder M + 2*gamma`,
`h_M = sqrt(M+1)-sqrt(M)`,
`c_d = mobiusDivisorDilationChannel M d`, and
`f_d = mu(d)*primeFreeDivisorDefect(M/d)`.

For `M≥1`, the existing `CCMFUSuzukiCompletedRieszGraphEnergy.mobiusDivisorSquareRootAbelMoment_succ_sub` gives `A_(M+1)-A_M=h_M*R_M`. The existing `MobiusDivisorAbelDiagonalBound` also gives the exact channel and diagonal successor laws. Subtracting the diagonal law from the squared source law therefore yields the paper identity

`C_(M+1)-C_M = 2*h_M*(A_M*R_M-Σ_d c_d*f_d) + h_M²*(R_M²-Σ_d f_d²)`,

where `C_M` is the complete C12 off-diagonal and all sums retain `1≤d≤M`. The newly entering channel at `d=M+1` is zero. This identity is an algebraic consequence of inspected theorems, not a new audited Lean declaration.

The attempted proof required an independent one-sided bound on the mixed term `A_M*R_M`, or on its accumulated interaction with the displayed diagonal terms. The existing unsigned channel and divisor-defect estimates control the arithmetic diagonal contributions. They do not control this product of the completed source with its forcing. Taking absolute values and using only the available linear Chebyshev envelope and the unsigned sum of channels loses a power of the cutoff. No uniform one-step quadratic-budget inequality, nor an adequate signed block estimate, was proved or refuted.

The completed graph-energy theorem already proves square summability of `(A_(M+1)-A_M)/M`. It does not bound `A_M/M`. The same file proves exact zero total harmonic charge, but its harmonic-to-square-root clock ratio is unbounded; the signed clock-acceleration pairing remains. Neither existing result closes the mixed-product estimate. `CriticalAbelRoutePAsymptoticBridge.criticalContinuousAbel_fixed_amplitude_two_sided` gives two-sided fixed-amplitude oscillation of the actual continuous normalized source. An eventual source sign cannot be inserted into the cutoff proof. Oscillation alone was not claimed to refute the desired quadratic bound or every possible one-sided drift estimate.

The related short quadratic work also retains the same type of arithmetic difficulty. `CCMPrimeDeficitDivisorSource` expresses its full source through divisor counts, but leaves a double sum with coefficient `mu(a)*mu(b)` and kernel evaluated at `T-log(a*b)`. A complete unweighted lcm-fibre cancellation cannot be substituted: the short cutoff truncates the divisor fibres, and the kernel varies with `a*b=gcd(a,b)*lcm(a,b)` even at fixed lcm. No tail or gcd-dependent weight was discarded, and no short-work bound was obtained.

**Outcome:** previous turn classified as no mathematical progress; this turn also supplied no new frontier theorem, RH proof, or RH falsification. Three deep searches terminated with partial snapshot coverage; candidate lemmas and source arguments were inspected. No numerical experiment, Lean edit/build, new receiver, or new no-go claim. The remaining task is the actual signed mixed-product/covariance estimate, not its already-known successor, graph-energy, or divisor-source representation.

## C12.12: weighted lcm panels and the physical boundary kernel

The complete-lcm attempt retained the actual truncation and both endpoint weights. The existing `finiteLcmPairCrossFibre_moebius_inversion` in `EulerDeletionTruncatedDivisorPairCorrelation` inverts finite divisor-prefix products; the selected cross-beta theorem at line 4319 retains both variables and every nonclock lcm label. Neither bounds the sum of surviving fibres. `physicalCenteredLcmFibre_initialSum_eq_mertensPanelSquares` in `EulerDeletionCenteredLcmMertensPanelInversion` makes the unresolved sign explicit:

`Σ_(q≤N) physicalCenteredLcmFibre(q,t,H,t,H)`

`= Σ_(m≤N) Mertens(N/m) * (H*phi(m)/m - coprime_count(m,(t,t+H]))²`.

The nonnegative panels therefore still have signed arithmetic coefficients. The all-shift polarity theorem collapses complete *unweighted* lcm fibres, including an external weight on the physical index. It does not permit dropping divisor-dependent discrepancy weights or completing the truncated divisor carrier without its boundary. No signed panel estimate was proved.

The next attempted mechanism was a cutoff-uniform operator estimate for the actual short-source boundary kernel. The inspected `CCMPrimeDeficitBoundaryReflection` already identifies that kernel with the exponential ramp throughout the thick shell and gives the exact reflection integral with the literal Möbius tail. `CCMPrimeDeficitResidualReflection` already retains the full residual force at arbitrary cutoff. These are existing source identities, not new cancellation.

A diagnostic paper test shows why arbitrary coefficient control cannot substitute for a Möbius estimate here. Put `m=6r`, `k=2r`, `T=2*log(8r)`, and restrict both indices to the `r` integers in `(6r,7r]`, for `r≥1`. Then

`1 < exp(T)/(a*b) < 2`,

so the existing before-second-entry source formula gives

`H(T-log(a*b)) = (8r)²/(a*b)-1 ≥ 15/49`.

Consequently the all-one coefficient vector on this band has quadratic work at least `(15/49)*r²`, whereas its coefficient square sum is `r`. A uniform bound of this kernel by a fixed constant times coefficient square sum is unavailable. This is a symbolic test of the proposed auxiliary estimate, not a numerical experiment, an audited new Lean theorem, or a counterexample for the literal Möbius vector. The existing negative two-point determinant alone would not establish this norm obstruction; those are different claims.

On this restricted band the same entry formula gives the paper expression

`(8r)²*(Σ_a mu(a)/a)² - (Σ_a mu(a))²`.

Neither signed sum, nor their required quadratic difference, was bounded at the critical scale. This band test also does not bound its interactions with the rest of the physical shell. A general Voronoi isometry from the search results does not supply an arithmetic representation or the missing estimate for this source. No such representation was assumed.

**Outcome:** no mathematical frontier advance, new Lean source, build, RH proof, or RH falsification. Both deep searches terminated with partial snapshot coverage and a still-running background index refresh; candidate lemmas and source arguments were inspected. No route is retired on the basis of this unaudited auxiliary test. The hard target remains cancellation of the *complete* signed physical covariance. Another complete-panel identity, arbitrary-vector operator bound, or conditional reflection receiver would leave that target open.

## C12.13: whole-block source induction — still no arithmetic estimate

Previous continuation is classified as **no mathematical progress**. This attempt returned to the literal successor source and tested whole-block control instead of a pointwise sign for `A_M*R_M`. Here `A_M` and `R_M` are as in C12.11. For positive `k`, write

`g_k=(A_(k+1)-A_k)/k = h_k*R_k/k`.

This is the existing `completedRieszGraphIncrement (k-1)`. The inspected proof of `summable_sq_completedRieszGraphIncrement` uses a summable PNT absolute-error majorant, not a critical-scale dyadic estimate.

For `M≤N≤2M`, telescoping and Cauchy–Schwarz give the paper bound

`|A_N-A_M|² ≤ (Σ_(M≤k<N) k²)*(Σ_(M≤k<N) g_k²)`

`≤ 4*M³*Σ_(M≤k<2M) g_k²`.

Square summability makes the last sum tend to zero, but supplies no `O(1/M)` rate. This calculation therefore does not give the required `O(M)` increment bound. In the signed squared-source calculation, the same missing information remains as `2*A_M*(A_N-A_M)` together with the increment square; it cannot be discarded.

A sufficient rate would follow from `Σ_(M≤k<2M) R_k² ≤ C*M²`, since `h_k=1/(sqrt(k+1)+sqrt(k))` and hence `g_k²≤R_k²/(4*k³)`. That mean-square estimate is **unproved here**, not a new formalized receiver or an available hypothesis. Stating it does not advance C12.

The exact Tatuzawa–Iseki identity was tested as a producer. It retains

`R_N*log N + Σ_(d≤N) Lambda(d)*R_(N/d)`

as a Möbius-weighted transform of `floorSummatory psiDefect`. The existing `abs_floorSummatory_psiDefect_le` bounds this *floor transform* by `24*sqrt(N)`; it is not a bound on `psiDefect N`. Passing through the Möbius inverse and taking absolute values loses the cancellation needed for the proposed mean square. The Selberg `O(N)` remainder does not repair that loss. No signed bilinear estimate for the inverse, nor a cancellation estimate for the retained prime-dilation term, was obtained.

Both searches terminated with partial coverage (first pending, second snapshot); candidate and source-argument fields were inspected. Generic dyadic pair expansions and Schwartz Abel-energy results do not establish this literal source estimate. No whole-corpus absence assertion is made.

**Outcome:** no new frontier theorem, Lean change/build, numerical experiment, RH proof, or RH falsification. Goal remains active. The unresolved work is an arithmetic bound for the complete signed interaction or the actual forcing mean square; further telescoping identities or consequences under that bound would only repackage the gap.

## C12.14: logarithmic copied-square payment retains a parent-energy cost

Previous turn is classified as **no mathematical progress**. This attempt kept the finite cofactor carrier and tested the negative copied-square term in `MobiusDivisorFiniteClockCountingCancellation`, rather than replacing the source by a limiting density.

The existing energy has weight `1+log r`; it dominates the raw finite selection energy and equals the complete squared source after all primes are processed. The offset is essential: the same file proves that offset zero loses the completed head. At a prime insertion, put `w=1+log r`, `L=log p`, `a=F(M,r,P)`, and `b=sqrt(p)*F(M,p*r,P)` for the actual interpolated fibres. The exact local change is

`r*(-2*w*a*b - L*b²)`.

The attempted absorption retains the negative copied square but gives

`-2*w*a*b-L*b² = (w²/L)*a²-L*(b+(w/L)*a)² ≤ (w²/L)*a²`.

Thus it charges the old fibre; it does not prove nonincrease. Equivalently, the scalar weighted merge admits the factor `1+w/(w+L)` against its two pre-merge weighted squares. Repeated worst-case factors over the complete prime schedule do not yield a subpower allowance. No arithmetic estimate for the actual signed aggregate was obtained to improve this step. These are paper checks of the attempted proof, not new Lean declarations or an impossibility theorem for every use of the clock identity.

The exact gcd scaling and coprime-head formula also retain their coprimality masks and signed head products. Their regrouping cannot supply the missing sign by itself. The inspected inclusive gcd Gram has a positive totient-square factorization and retains literal late-prime diagonals; it was not substituted for the desired unweighted complete covariance.

`eventually_exists_mobiusDivisorReceivingPairNeutralization` does steer the actual head and prime-two coordinates into a square-root-scale ball with controlled prefixes. Its statement requires an unused prime pool and a quadratic admission bound for those two receiving coordinates, and leaves other fibres unprocessed. Applying it repeatedly without proving renewed capacity and control of every remaining fibre would omit the hard source interaction. No such exhaustion argument was proved.

The existing `riemannHypothesis_iff_mobiusDivisorSquareRootAbelSubpower` confirms that a subpower bound on the complete normalized Abel source would suffice; no need to force a sharp constant as an intermediate objective. This does not make the finite-clock mixed term controlled. The pair search terminated with partial snapshot coverage; candidate lemmas and source arguments were inspected.

**Outcome:** no new mathematical frontier theorem, Lean source/build, numerical experiment, RH proof, or RH falsification. No route retirement or new no-go claim. The failed step is absorption of the *complete signed* prime/cofactor interaction; the negative copied squares alone do not supply the proposed proof.

## C12.15: nonlinear amplification does not supply its own upper bound

Previous turn is classified as **no mathematical progress**. This attempt tested whether the exact quadratic and higher-convolution identities could rule out a growing source mode without first bounding each linear component.

The inspected `MobiusMertensSelfConvolutionCriterion` concerns **additive** self-convolution of Mertens prefixes, not multiplicative convolution or a pointwise square. `MobiusMertensEvenConvolutionExactOrder.mertensEvenConvolutionOrder_eq` already gives its exact one-sided order

`Lambda_k = 2*k*(1+Theta)-1`, for `k≥1`.

The independently available crude upper bound in `MobiusMertensEvenConvolutionOrderLowerEdge` is `4*k-1`. Combining those two inequalities gives only `Theta≤1`; increasing the convolution order does not turn this into the critical bound. The sharper upper theorem in `ExactOrder` explicitly uses a Mertens growth bound. No independent `3*k-1` upper edge, or new restriction on `Theta`, was proved.

The actual finite Euler renewal provides another quadratic test. Its kernel is nonnegative and its finite resolvent terminates exactly, but the delayed values of the actual deficit remain signed. `ccmEulerRenewalCriticalMass_unbounded` already rules out a cutoff-uniform positive critical-mass contraction for every **fixed positive** Euler modulus. That statement was not extended to changing moduli. Choosing the factorial of the square-root cutoff removes the residual, but `ccmPrimeDeficitEulerAction_factorial_half` then identifies the retained action with the full deficit itself. No separate bound for that action was obtained.

The inspected source sign theorem in `MobiusRenewalEnergySign` gives a negative complete pairing near the ordinary convergence boundary; its formula retains minus the unknown Gamma–Hankel energy. It is not an upper estimate on that energy. Likewise, a generic contraction would have to satisfy the actual source-transport requirements before its Gram inequalities could be used; no such transport was constructed.

**Outcome:** no new frontier theorem, Lean change/build, numerical experiment, RH proof, or RH falsification. The search terminated with partial snapshot coverage; candidate/source fields were inspected. No general impossibility claim about nonlinear methods or route retirement is made. The remaining requirement is still an independent arithmetic upper bound on the complete signed source, not amplification of its already-classified growth order.

## C12.16: finite renewal remainder and critical boundary cancellation

Previous turn is classified as **no mathematical progress**. The renewal attempt first distinguished the coprime head (indices coprime to a modulus) from the core-supported head (divisors of a finite prime product). The two are not interchangeable. `MobiusDivisorDilationMeanUniformRenewal` bounds the physical mean uniformly in its next dilation, with a constant depending on the retained core. It does not supply a changing-core bound.

The literal remainder in `MobiusDivisorFixedCorePrimeCorrelationLimit` is the sum over `T ≤ M/r` of `2*sqrt(p)*r*F(M,r,P)*F(M,p*r,P)`. Its existing normalized absolute bound is `2*((3/5)*2^(P.card-1))²/T`. Letting the quotient depth grow does not resolve the changing-core issue: for every `T≤M`, the remainder still includes the `r=1` product of the retained head and its child. At the last terminal prime, write `S=criticalContinuousAbel M` and `b=sqrt(p)*criticalContinuousAbel(M/p)`. The already-proved terminal energy formula gives pre-completion energy `(S+b)²+b²`, final energy `S²`, and release `2*S*b+2*b²`. The unknown complete source is present in this retained product. No uniform estimate for it was proved. This is a diagnosis of the attempted deduction, not a new no-go theorem.

The canonical square-root core cannot be bounded separately: `criticalMovingSquareCore_energy_escape` already disproves a uniform quadratic bound for it. Its exact extension balance retains the signed late-prime sum. The attempted joint estimate remains C12.2's terminal excess; no bound on its actual covariance was obtained.

Boundary moments do not provide that estimate by themselves. `MobiusDivisorCriticalAbelSignedBoundaryMoments` already proves zero mass for `S(y)/y^(5/2)` and first logarithmic moment `-divisorHarmonicBoundary/3`. These concern the complete signed integral. Replacing the finite prime-weighted child sum by that integral requires control of the retained cutoff and arithmetic discrepancy. Neither such a control nor a pointwise source bound was derived; no prime-sum asymptotic is asserted here.

The second test used the literal coupled floor--Möbius error. `CoupledFloorMobiusCriticalBoundaryCancellation` proves square-integrability for each fixed `0<omega<1/2` after exponential normalization. The underlying bound in `ShiftedEulerFloorMobiusTailCoupling` is `|E_omega(X)|≤C(omega)*X^(1-omega)`, with the displayed proof constant `2+2/(1-2*omega)+1/((1+omega)*2*omega)`. The exact MC source is instead obtained from `(E_omega(X)-1)/omega` as `omega→0`, followed by the square-root mesh and Gamma boundary. Both the fixed-cutoff derivative and this mesh landing are already formalized in `SuzukiCoupledErrorCriticalDerivative` and `CCMFUSuzukiCompletedRieszGraphEnergy`. The positive cofinal schedule and its RH-equivalent boundedness receiver also already exist in `CoupledFloorMobiusAffineRieszHandoff`. Thus fixed-parameter integrability cannot be inserted as a bound for the growing-cutoff critical quotient. No new receiver was added.

**Next hard attempt:** estimate the signed lower-minus-upper floor incidence inside its critical difference quotient, with cutoff and parameter moving together, before taking absolute values. The existing fixed-parameter envelope, positive cofinal landing, and boundary moments are inputs to inspect, not the missing uniform cancellation estimate. Any proposed argument must pay for undoing the exponential normalization and division by `omega`; merely asserting uniformity would restate the gap.

**Outcome:** no mathematical frontier advance, Lean source/build, computation, RH proof, or RH falsification. Four searches terminated: the finite-covariance search completed with snapshot coverage; renewal, terminal-joint and coupled-boundary searches were partial. Candidate lemmas and source arguments were inspected against relevant source. Background indexing was active; no whole-corpus absence claim is made. Goal remains active and unmet.

## C12.17: the uniform parameter derivative exists in the wrong time weight

Previous turn is classified as **no mathematical progress**. Tested the C12.16 proposal by keeping the floor and tail together in the critical quotient and then asking whether a positive-shift norm could control its critical derivative.

The exact finite-cutoff result remains `suzukiCoupledError_critical_derivative_base_one`: `(E_omega(X)-1)/omega` tends to `2*psi(X)-2*X`. Combining the two incidences does not give an inequality for this signed derivative. Positivity of the shifted Jordan--Euler coefficients concerns the summatory term before subtracting its main term. No positivity, monotonicity, or derivative comparison for the centered error was proved.

**Correction to the scope of the missing estimate:** it would be wrong to say that every uniform parameter-derivative bound is missing. `MobiusCausalBoundaryEnergy.exists_uniform_boundary_bound` already dominates the complete parameter derivative by one square-integrable frequency majorant for all sufficiently small positive `omega`. `tendsto_boundary_deriv_energy` already gives strong boundary `L²` convergence. `MobiusCenteredSchurBoundary` also supplies uniform bounds and strong limits for the floor and centered Schur parts separately. These are existing results, not new progress.

Their spectral coordinate is `z=i*tau`, with zeta evaluated at `1+z` and `1+2*omega+z`. The exact limiting derivative in `MobiusCausalFlatLimit` is

`-1/(1+z)^2 - 2*zeta'(1+z)/((1+z)*zeta(1+z)) - 2/z`.

Thus cancellation of the zeroth-order ratio does not cancel the logarithmic derivative. The known boundary is the ordinary line `Re(s)=1`; its uniform `L²` control does not supply the exponential time weight needed for half-power cancellation. At integer clock `t=log X`, differentiating the actual normalized carrier gives the source proportional to `(2*psi(X)-2*X-log X)/X`, consistently with that ordinary-line normalization. This last observation is a paper check of existing formulas, not a new Lean theorem.

Attempted propagation from positive shifts therefore stops at a definite unresolved estimate: the half-power weighted signed covariance. Applying the ordinary-line majorant on a left-shifted line would violate its `0≤Re(z)` domain and presuppose new zero-free/source-decay information. No such shift or uniform weighted estimate was established. Existing critical-prefix convergence and its Mertens-deviation decomposition likewise retain the signed endpoint-minus-future-tail error; convergence without a critical rate cannot pay the increasing clock weight.

**Next hard attempt:** retain the half-power time weight in the finite-cutoff coupled quadratic form from the outset, and estimate its complete mixed floor/tail contribution arithmetically. Do not repeat the fixed-parameter carrier argument, the already-proved ordinary-line derivative bound, or another conditional receiver. The required result is still a new signed estimate for the actual complete source.

**Outcome:** no mathematical frontier advance, new Lean source/build, computation, RH proof, or RH falsification. Both deep searches terminated with partial snapshot coverage and active background indexing; candidate/source fields were inspected. Own search scratch removed. Goal active and unmet.

## C12.18: weighted channel coupling leaves cross-divisor arithmetic

Previous turn is classified as **no mathematical progress**. Tested whether the literal coupled feature could pay for the half-power weight through its floor/boundary mixed term.

`MobiusCoupledFeatureIncidence` defines `B_d(t)=k(t-log d)-c*1_[0,log d)(t)` for causal `k` and `c=1/(1+omega)`. The two pieces at a single divisor have disjoint supports. Multiplication by a positive time weight preserves that orthogonality. Consequently there is no same-divisor mixed cancellation to spend. The existing signed-coisometry theorem retains the norm of the signed projected feature; it does not bound that projection at the required weight.

For real profiles and `0≤a=log d≤b=log e≤T`, direct support splitting gives the paper-level weighted pair expression

`integral_b^T exp(t)*k(t-a)*k(t-b) dt - c*integral_a^b exp(t)*k(t-a) dt + c²*(exp(a)-1)`.

It must still be summed with the actual two Möbius coefficients. Neither a sign for this complete signed sum nor a subpower bound was proved. The expansion is a check on the attempted argument, not a new formalized identity or a frontier theorem. In particular, the weight changes the boundary square from `log d` to `d-1`; the ordinary unweighted channel-norm formula cannot be reused unchanged.

Also tested whether chronological orthogonality could bound the same cross-channel arithmetic after localizing the source. This localization is already stronger than needed as an auxiliary step: `EulerDeletionTwoLogClockLocalization.source_twoLogClockProjection_error_norm_sq_le` bounds the complete high-clock error by `3*(log2(N+1)+1)` using only `|mu|≤1`. The retained field remains the literal paired quotient. `EulerDeletionLogClockSingleQuotient` and `EulerDeletionNestedProjectionCovariance` retain all complete signed reverse tails; their positive layer squares have no new arithmetic upper estimate here. A small number of retained chronological stages is not a bound on their energies.

The first-tail consequence makes the unresolved interaction explicit. `EulerDeletionFirstTailPairCorrelation` already identifies its strict off-diagonal with

`Q_N = sum_(1≤h<N) sum_(N<a≤2N-h) mu(a+h)*mu(a)*(1/(a+h)-1/(2N+1))`.

The full first-tail energy is the nonnegative diagonal plus `2*Q_N`. The predictable-drift theorem bounds that energy by the unknown drift energy, not conversely by an independently known quantity. Replacing physical weights by complete-period averages or dropping the signed reverse tails would change the problem. The Ramaré physical packet identity likewise retains its full rough/prime/harmonic cross terms and supplies no cancellation estimate by itself.

**Next hard attempt:** attack the actual weighted cross-divisor/shifted-pair sum, keeping its fixed starting point and both moving endpoints. The required improvement is arithmetic cancellation in this complete sum; further support decompositions, coisometry identities, or low-clock receivers are already available and will not be added as substitutes.

**Outcome:** no mathematical frontier advance, Lean edit/build, computation, RH proof, or RH falsification. Both searches terminated with partial snapshot coverage; candidate and source-argument fields were inspected. No route retirement or new impossibility theorem. Goal active and unmet.

## C12.19: gcd inversion returns the energy; logarithmic prime cross remains open

Previous turn is classified as **no mathematical progress**. Tested the complete first-tail pair sum by writing `a=r*u`, `b=r*v`. Its coefficient is `mu(r)^2*mu(u)*mu(v)` only with all three masks `(r,u)=(r,v)=(u,v)=1`; its domain remains `N<r*u<r*v≤2*N`, and its weight remains `1/(r*v)-1/(2*N+1)`. The retrieved truncated-divisor correlation identities concern different summands and cannot be substituted for this source.

The next test used the signed common-multiple diagonalization in `EulerDeletionCoprimeKernelDiagonalization`. At each physical prefix `t`, put `H_q(t)=sum_(N<a≤t,q|a) mu(a)` and let `C_r(t)` be the complete pair sum with exact gcd `r`. Expanding the coprimality mask gives, on paper, `C_r(t)=sum_e mu(e)*H_(r*e)(t)^2`. Summing over every `r` collapses the divisor coefficient to the unit indicator and returns `H_1(t)^2`. Integrating with the existing first-tail cell weights therefore returns the original unknown energy. This is an exact reorganization, not a cancellation estimate or a new no-go theorem.

The already-formalized all-gcd head estimates in `EulerDeletionGcdHeadSubpower` concern the initial residue head and retain its harmonic coefficient; they do not bound this later first-tail source. Neither the prime-supported completed floor columns nor a complete-period covariance can replace the physical first-tail weights.

**Next conjecture, still unproved:** control the aggregate logarithmically weighted prime cross term directly. For `N<t≤2*N`, write `F(t)=H_1(t)`, `H_p(t)=sum_(N<a≤t,p|a) mu(a)`, `G_p(t)=F(t)-H_p(t)`, and use the first-tail weighted inner product. Test the one-sided estimate

`sum_(p≤2*N prime) log(p)*<G_p,H_p> ≤ C_epsilon*N^epsilon`

for every positive `epsilon`, with no source hypothesis. This concerns the complete actual source at the current cutoff, not arbitrary coefficient arrays or a fixed finite prime core.

Reason for this test: squarefree support gives `sum_p log(p)*H_p(t)=sum_(N<a≤t) mu(a)*log(a)`. Thus its pairing with `F` splits into the nonnegative prime-multiple energies plus precisely the proposed cross term. Abel summation on the dyadic interval relates the logarithmic source pairing to `log(N)*||F||^2` with a bounded Volterra error. The prime-multiple fields have exact smaller-cutoff coprime predecessors; undoing the mask requires retaining the whole prime-power renewal, not replacing a coprime predecessor by an unmasked one. This suggests an induction with summable weights `log(p)/p^(1+epsilon)`, but endpoint errors and the induction estimate have not been audited in Lean. These observations are proof planning, not a new cancellation theorem.

The corpus already supplies `Sieve.GcdLogSelbergDiagonal.log_gcd_eq_sum_vonMangoldt_indicator`. Positivity of its common-multiple square sum controls only the prime-multiple part. It supplies no upper bound on the cross term. Completing individual cross squares loses the needed prime-sum scale; this loss has not been repaired. The next attempt must prove an arithmetic bound for the displayed aggregate, not formalize another conditional RH receiver or another gcd identity.

**Outcome:** no mathematical frontier advance, Lean edit/build, numerical work, RH proof or falsification. Three deep searches terminated with partial snapshot coverage and active background indexing; candidate and source-argument fields were inspected. No whole-corpus absence claim. Goal remains active and unmet.

## C12.20: the logarithmic cross term keeps all parity layers

Previous turn is classified as **no mathematical progress**. Continued the C12.19 conjecture rather than replacing its missing estimate by a receiver. Let `K_N(a,b)=1/max(a,b)-1/(2*N+1)` on `N<a,b≤2*N`. Symmetrizing the prime incidence on paper gives the exact proposed cross term as

`C_N = sum_(N<a<b≤2*N) mu(a)*mu(b)*K_N(a,b)*log(a*b/gcd(a,b)^2)`.

Only squarefree pairs survive. Writing `a=r*u`, `b=r*v`, their reduced product `q=u*v` is squarefree and their sign is `mu(q)`. Hence the same paper expansion is `C_N=sum_q mu(q)*log(q)*A_N(q)`, where `A_N(q)` sums the original positive physical weights over `u*v=q`, `u<v`, and squarefree `r` coprime to `q`, subject to `N<r*u<r*v≤2*N`. Both endpoints and the common-factor mask remain. In particular `v/u<2`, so a prime reduced product has no contributing pair. The divisor-comparable sign law cannot bound this dyadic-window term: distinct elements of this window are never divisor-comparable.

Attempted to use the logarithm to move cancellation across factor layers. For squarefree `q`, `mu(q)*log(q)=-sum_(p|q prime) log(p)*mu(q/p)`. Thus `C_N=-sum_m mu(m)*B_N(m)`, with the positive prime average `B_N(m)=sum_(p prime,p∤m) log(p)*A_N(m*p)`. This transports the unknown signs to the cofactors; it does not remove them. The `m=1` term vanishes because `A_N(p)=0`. Prime cofactors contribute positively to `C_N`, semiprime cofactors negatively, and the remaining layers must all be retained. No sign, domination across all layers, or subpower upper bound for this complete weighted sum was established. These are paper checks on the conjecture, not new Lean results.

Individual square completion also fails to close the estimate: `<G_p,H_p>=||F||²/4-||H_p-F/2||²`, so summing its upper bound costs `theta(2*N)*||F||²/4`, not the logarithmic coefficient needed by the proposed induction. The positivity of the log-gcd form controls only `sum_p log(p)||H_p||²` and does not improve this cross bound. None of these deductions falsifies C12.19.

Source checks: `EulerDeletionLogPrimeAbel` already retains the entire logarithmic Abel history. `EulerDeletionLogPrimeForcing` explicitly retains harmonic compensation in the physical carrier; its forcing has linear squared-energy scale and cannot be dropped as a subpower error. Its source is not the raw first-tail window, so importing the compensated renewal would require carrying that correction. `LogarithmicCoprimeEnergy` and `CCMPrimeDeficitCoprimeBalance` retain a signed coprime cross; the latter bounds the sum of critical energy and cross work, not either separately. No such identity was used as an upper estimate.

**Next hard step:** continue C12.19 at its actual arithmetic bottleneck, the signed complete cofactor sum `-sum_m mu(m)*B_N(m)`. A proof must control its aggregate across all factor layers with the physical cutoff retained. Reindexing again, imposing an unproved sign, or bounding only a fixed factor layer will not close it. No auxiliary identity or conditional induction module is to be added as a substitute.

**Outcome:** no mathematical frontier advance, new Lean source/build, numerical work, RH proof or falsification. The deep search terminated with partial snapshot coverage and active background indexing; candidate lemmas and source arguments were inspected. Own search scratch removed. Goal active and unmet.

## C12.21: full-prime normalization is not the missing cross estimate

Previous turn is classified as **no mathematical progress**. Kept the complete C12.19/C12.20 aggregate and tested whether logarithmic allocation of prime incidence or the all-prime Ramaré allocation could control all factor counts at once.

`RouteEFixedOrderTwoGradeOverpayment.routeE_prime_double_overpayment` controls the literal prime/`2p` numerator pair only in its far-denominator domain `2048*p≤q`, with receiver order between one and two. Its completed cofactor moment is signed, but the theorem does not compare all numerator grades. In C12.20 the two reduced factors instead have ratio strictly below two. No substitution of this far-cone overpayment for the dyadic mixed term is valid. No new near-ratio or all-grade comparison was proved.

`MobiusHaarRamareFullPrimeCofactor.mobius_ramare_full_prime_cofactor` already counts every squarefree source term exactly once using the cofactor `mu(m)/(1+omega(m))` and retains `p∤m`. `EulerDeletionRamarePacketDilation` gives the literal `1/p` packet energy factor, but its unequal-prime covariance keeps the full ratio-shifted cofactor product. `EulerDeletionRamarePhysical` also retains the forced harmonic correction. None supplies orthogonality between prime packets.

The scalar all-prime cofactor is not a substitute for a small complete signed packet field. `Sieve.FullPrimeCofactorBoundary` defines `a(n)=mu(n)/(1+omega(n))` and already proves, for its real Dirichlet series `F`,

`F(sigma) -> 0` and `F(sigma)*log(norm(zeta(sigma))) -> 1` as `sigma -> 1+`.

Paper test of an attempted separate cofactor bound: an absolute summatory bound `sum_(n≤x) a(n)=O(x^theta)` with `theta<1` would make its Abel representation differentiable near one. The zero limit would then force `F(sigma)=O(sigma-1)`, contradicting the displayed nonzero logarithmic boundary invariant and the zeta pole. This is not a new Lean theorem; the module itself flags the separate Abel exclusion as unformalized. Its positive boundary invariant is already formalized. No separate cofactor cancellation bound is assumed in the current argument, and no route is retired here.

The logarithmic allocation `sum_(p|n) log(p)/log(n)=1` on nontrivial squarefree support avoids that particular Ramaré coefficient, but it returns the exact logarithmic prime–cofactor source from C12.19. Removing a prime flips the coefficient sign while changing the physical cutoff; collecting the resulting cofactors does not by itself compare the positive and negative total weights. Neither a joint upper bound, a uniform comparison over factor counts, nor a controlled cutoff-boundary contribution was established.

**Next hard step remains unchanged:** prove a one-sided subpower estimate for the complete logarithmic prime cross, or its exactly equivalent C12.20 cofactor sum, with all signs and physical endpoints retained. Separate packet estimates, degree normalization, and a fixed-grade payment cannot be substituted for this aggregate estimate.

**Outcome:** no mathematical frontier advance, Lean edit/build, numerical experiment, RH proof or falsification. One deep search terminated with partial snapshot coverage and active background indexing; candidate and source-argument fields were inspected. Own search scratch removed. Goal active and unmet.

## C12.22: joint spectral factorization has not bounded the physical cross

Previous turn is classified as **no mathematical progress**. Tested whether the complete C12.19 pair sum could gain cancellation from a joint modular/Fourier factorization, rather than from separate prime packets. No applicable upper estimate was obtained.

`Sieve.KloostermanZeroRowSpectralComparison` makes an important direction explicit: at modulus `q+1`, complete-column main energy is `(q+1)` times the zero-row term plus a nonnegative transverse remainder. The zero row is the Ramanujan amplitude. An upper bound on that row is not an upper bound on the complete-column energy. No identification of the first-tail logarithmic kernel with a controlled full transform, and no bound on its retained transverse contribution, was proved. The retrieved complete-column correlation identity likewise changes no inequality by itself.

`EulerDeletionTopFrequencyBand` isolates first harmonics of top denominators in a complete period. Its statement does not control a finite time-window transform. The first-tail kernel must retain its physical endpoints; complete-period separation cannot be inserted as a bound for that kernel.

Also tested whether removing a prime from a near-ratio pair would let the existing far-cone payment apply to its cofactors. The exact Route E edge in `RouteEFixedOrderCofactorLinearization` is `(b+a)^(-r)-(b+2*a)^(-r)`. The present pair kernel is `1/max(a,b)-1/(2*N+1)` with a logarithmic reduced-product weight. Prime removal changes the index domain and does not turn one kernel into the other. No weighted conversion with a controlled boundary error was established. Dyadic telescoping of reciprocal kernels alone would retain unmatched top-window indices and the same signed source; it is not the required arithmetic payment.

The current-corpus correlation consumers in `Sieve.MoebiusUnweighted` explicitly require shifted-correlation hypotheses. No such hypothesis was discharged here. C12.19 remains a conjecture; no theorem, source sign, or all-factor cancellation bound is claimed.

**Next hard work:** stay with the actual complete weighted cross and seek a source-specific estimate for its mixed terms. Any prime-removal or spectral argument must estimate the resulting full interaction and its physical boundary, not merely identify it or select a favorable row. Further receiver identities will not be added as progress.

**Outcome:** no mathematical frontier advance, Lean edit/build, numerical experiment, RH proof or falsification. One deep search terminated with partial snapshot coverage and active background indexing; candidate lemmas and source arguments were inspected. Own search scratch removed. Goal active and unmet.

## C12.23: coupled logarithmic renewal still lacks a signed estimate

Previous turn is classified as **no mathematical progress**. Continued the complete-source estimate by retaining both sides of Tatuzawa--Iseki, rather than discarding prime forcing. Write `f=psiDefect`, `G=floorSummatory f`, and `H_N=sum_(n<=N) mu(n)*log(N/n)*G(floor(N/n))`. The exact corpus identity is

`f(N)*log(N) + sum_(k<=N) Lambda(k)*f(floor(N/k)) = H_N`.

Multiplication by `f(N)` gives the proposed energy comparison

`log(N)*f(N)^2 + f(N)*sum_(k<=N) Lambda(k)*f(floor(N/k)) = f(N)*H_N`.

Neither the mixed history product nor the forcing pairing has a proved favorable sign. Nonnegative `Lambda` does not make the mixed history product nonnegative. The established `|G(k)|<=24*sqrt(k)` is a bound for the floor transform, not for `f(k)`. Absolute estimation of `H_N` gives the existing linear bound from `SelbergSymmetryCore`, not a critical bound on either displayed product. Moving the floor transform to the other factor before estimating also leaves an unproved critical inverse/coercivity estimate. `FloorTransformWienerClass` explicitly excludes both the unweighted transform and its Mobius inverse from its sufficient subpower absolute-weight class; that exclusion is not a no-go for this particular signed source.

The actual compensated physical renewal in `EulerDeletionLogPrimeForcing` retains a harmonic correction of linear squared-energy scale. No joint cancellation estimate paying for that correction was obtained. Separately, `EulerDeletionAveragedDivisorCovariance.signedFloorTailRamp_not_factor_through_natDiv` prevents treating the EDQ omitted-tail ramp as a function of the quotient alone across a quotient collision. Thus the first-tail problem cannot be replaced by the quotient-only Tatuzawa expression without retaining its boundary contribution. No bound on that contribution or on C12.19's logarithmic prime cross was proved.

**Unchanged hard target:** the one-sided subpower bound on the complete C12.19 cross, with prime-power histories and physical cutoff retained. The coupled renewal supplies no sign producer. Future attempts must estimate those mixed terms themselves; neither another identity module nor a conditional energy receiver addresses this gap.

**Outcome:** no mathematical frontier advance, new Lean source/build, numerical experiment, RH proof or falsification. Both deep searches terminated with partial snapshot coverage and active background indexing; candidate lemmas and source arguments were inspected. No whole-corpus absence claim. Goal remains active and unmet.

## C12.24: single-prime cross-scale pairing does not pay the complete cross

Previous turn is classified as **no mathematical progress**. Tested direct parity reversal in the C12.19 pair sum, keeping the physical cutoff rather than passing through the floor transform. The proposed mechanism was to match a positive pair with its sign-reversed prime deletion and pay cutoff crossings by telescoping across scales.

Here is the paper test at prime two. Start with odd squarefree `a<b<2*a`, put `q=a*b/gcd(a,b)^2`, and keep their common sign `mu(a)*mu(b)`. The four two-adic states are `(a,b)`, `(a,2*b)`, `(b,2*a)`, and `(2*a,2*b)`, with relative signs `+,-,-,+`. The state `(a,2*b)` lies outside every ratio-two window. The remaining states contribute in the successive, disjoint integer-cutoff ranges

`ceil(b/2) <= N < a`, `a <= N < b`, and `b <= N < 2*a`.

Their logarithmic weights are respectively `log(q)`, `log(2*q)`, and `log(q)`. Thus sign reversal does not give same-cutoff cancellation: entry into the negative middle window is precisely an endpoint change. This is a symbolic check of the proposed mechanism, not a new Lean result or a global sign claim.

Also tested whether averaging these three windows would automatically repair it. For the continuous diagnostic kernel `J_x(a,b)=1_(b/2<=x<a)*(1/b-1/(2*x))`, logarithmic cutoff averaging gives

`I(a,b)=integral J_x(a,b) dx/x = (log(2*a/b)-1)/b + 1/(2*a)`.

The three-state average, divided by `mu(a)*mu(b)`, is

`(3/2)*log(q)*I(a,b) - log(2*q)*I(b,2*a)`.

As `b/a` approaches one, `a*I(a,b)` approaches `log(2)-1/2>0`, whereas `a*I(b,2*a)` approaches zero. The negative crossing window therefore does not automatically dominate the positive windows. This calculation concerns the stated continuous diagnostic; it is not an estimate for the discrete kernel with endpoint `2*N+1`, and no unproved family of actual pairs or global counterexample is asserted. Its lesson is to retain and estimate the crossing mass rather than declare it telescoping.

Current-corpus checks support no stronger conclusion. `MobiusPrimeInsertionDipoleJet.dyadic_insertion_telescopes` applies to the specific combination of two jet profiles; the complete first-tail source has not been represented as a controlled sum of those combinations. `RouteEFixedOrderTwoGradeMomentPayment` controls coprime moments at exponent at least two, not the present near-diagonal max kernel. The existing fractional transport and degree-normalized consumers in `MobiusBoundaryOppositeSignTransport` still require a small unused-capacity/variation term; neither the pairing nor prime sign reversal proves that estimate.

**Remaining hard work:** a complete, weighted comparison between opposite-parity pair mass, including near-equal pairs, all factor counts, and cutoff crossings. The single-prime telescope tested here does not supply it. No finite packet or conditional transport receiver will be added as a substitute for that collective estimate. C12.19 remains unproved and is not retired.

**Outcome:** no mathematical frontier advance, Lean edit/build, numerical experiment, RH proof or falsification. Both searches terminated with partial coverage (snapshot and pending respectively); candidate lemmas and source arguments were inspected. Goal active and unmet.

## C12.25: complete cutoff averaging retains the unknown signed energy

Previous turn is classified as **no mathematical progress**. Tested whether averaging the complete C12.19 cross over cutoffs could pay the crossing contributions from C12.24. No source estimate for the averaged cross was obtained.

For positive cutoff weights `w_N`, finite interchange in the first-tail pair formula leaves the kernel

`Kbar(a,b)=sum_N w_N*1_(N<min(a,b), max(a,b)<=2*N)*(1/max(a,b)-1/(2*N+1))`.

The averaged energy is still `sum_(a,b) mu(a)*mu(b)*Kbar(a,b)`. Positivity of `Kbar` does not orient the signed off-diagonal. The analogous log-prime cross keeps `log(a*b/gcd(a,b)^2)` as well. No estimate on the complete weighted pair sum, including its near-equal pairs, was proved by this interchange.

Kept two different averaging operations separate. `EulerDeletionCutoffAverage` averages source vectors and retains the exact inner coefficients and harmonic compensation. That theorem is not an upper bound on an average of squared source norms. In a common Hilbert carrier, the latter also contains the nonnegative cutoff variance. No bound on that variance was established. The retrieved first-tail anchor theorem already consumes an energy bound; it does not supply one.

Checked whether the existing all-order Selberg gcd-logarithmic asymptotic could supply the missing bound. `Sieve.SelbergGcdLogPowerAsymptotic` controls the specific origin-based form with coefficient `mu(a)*mu(b)*gcd(a,b)/(a*b)`, logarithmic endpoint tapers, and each fixed power of `log gcd`. The physical kernel uses `1/max(a,b)=min(a,b)/(a*b)` before its endpoint subtraction. Their ratio is `min(a,b)/gcd(a,b)`, which is not cutoff-uniform on near-equal coprime pairs. This is a kernel-domain check, not a comparison of signed forms or a new no-go theorem. No Mobius-specific quadratic-form comparison correcting that mismatch was proved.

The existing cubic-source Mellin--Plancherel theorem retains the full polynomial `sum_(n<=N) mu(n)*n^(-sigma-it)` under a positive Gamma weight. Its multiplier positivity certifies an energy representation, not an upper bound on the polynomial's weighted mass. No such uniform upper estimate or applicable signed log-gcd inequality was established here. Averaging has therefore not removed the original collective cancellation problem.

**Remaining hard target:** bound the complete logarithmic prime cross (pointwise, or with a sufficient proved cutoff-average estimate), including the corresponding variance and physical boundaries. Another average identity, positive multiplier, or receiver is not a substitute for that arithmetic estimate.

**Outcome:** no mathematical frontier advance, Lean edit/build, numerical experiment, RH proof or falsification. Two deep searches terminated with partial coverage (snapshot and pending); candidate lemmas and source arguments were inspected. One targeted lexical search returned the existing conditional first-tail energy theorem. All search commands terminated. Goal active and unmet.

## C12.26: coupled critical mollifier error remains uncontrolled

Previous turn is classified as **no mathematical progress**. Route remains MC. The cutoff-average attempt gave no signed estimate, so this attempt uses the other explicit MC source `E_X(s)=zeta(s)*sum_(n<=X) mu(n)*n^(-s)-1` from `MoebiusMollifiedZetaField`. At any actual zeta zero, `E_X=-1` for every cutoff. Its pole-cleared Gaussian window is `mobWindowField X H tau` in `MoebiusMollifiedErrorThreeLines`.

**Conjecture under test, not proved:** for each fixed admissible Gaussian window and every positive epsilon, the whole critical-line squared norm of this pole-cleared error is `O(X^epsilon)`. The target is the coupled signed error itself. No separate moment hypothesis on the zeta factor or the Mobius polynomial is assumed, and no conditional RH receiver is to be added.

The checked corpus supplies exact vanishing of the Dirichlet head, a right-edge estimate, and a three-lines consumer. Its critical bound comes from Cauchy--Schwarz on separate fourth moments and retains a factor of order X (up to height and logarithmic factors); this is not the conjectured subpower norm. Parameter changes alone will not be treated as a cancellation theorem. The attempted next step is to retain the exact convolution cancellation inside the coupled moment and estimate its remaining complete signed tail.

The explicit three-lines expression was checked, including its whole-line Gaussian tail. With a fixed physical window and a logarithmically growing height truncation sufficient to suppress that Gaussian tail, the displayed critical allowance remains of order `X^(1+o(1))`, whereas its right-edge allowance is of order `X^(-2)`. Its interpolation exponent is `lambda=(sigma-1/2)/(5/2)`, so this allowance does not decay on the stated range `1/2<sigma<=1`. This diagnoses the missing signed moment; no sharper parameter-bound module was added.

Direct paper expansion of the source gives another necessary check. On `X<n<=2*X`, every proper divisor of n is at most X, so the already-proved full divisor cancellation gives `mobTailCoeff X n=-mobCoeff n`. The first surviving block is therefore the actual Mobius source with its sign reversed, not a positive or automatically small error. The existing Dirichlet-series identity is stated only for `Re(s)>1`; it cannot be substituted term by term on the critical line without a separate argument. No lower bound for the whole Gaussian norm from this block alone is claimed, since other blocks retain their cross terms.

Also tested amplification of the vanishing head by powers of `E_X`. In the absolute-convergence half-plane, the k-th power starts beyond `X^k`; at a zeta zero its value remains `(-1)^k`. A critical-line estimate for this power requires the corresponding higher coupled moment, which was not proved. Reusing separate-factor bounds or discarding the interactions between tail blocks does not supply that estimate.

**Unresolved hard step:** prove the stated subpower norm for the complete coupled critical error from its arithmetic coefficients, retaining the pole compensation and every tail interaction. Neither this conjecture nor C12.19 has been discharged or retired. The next continuation should attack this coupled moment, not add a new conditional RH receiver.

**Outcome:** no mathematical frontier advance, Lean edit/build, numerical experiment, RH proof or falsification. Two deep searches terminated with partial snapshot coverage and active background indexing; candidate lemmas and source arguments were inspected against the source. Goal active and unmet.

## C12.27: exact coupled covariance and cutoff increments remain uncontrolled

Previous turn and this continuation are classified as **no mathematical frontier progress**. C12.26 remains the active hard conjecture. Tested whether exact product-fibre cancellation, Gaussian damping, or pole-compensated physical inversion bounds its complete signed covariance. None supplied the required subpower estimate.

The checked `Sieve.MollifiedTwistedMeanValueError` splits the exact diagonal `n*k=m*h` from the unequal products, but its upper bound takes absolute coefficient masses. `Sieve.MollifiedTwistedDiagonalDirConvEnergy` identifies the diagonal with the full finite convolution energy; this does not estimate the unequal-product contribution. The displaced direct-head mean-square theorem likewise pays the product length times coefficient energy. It concerns a finite direct head and a linear Levinson mollifier; it is not a bound for the whole raw-Mobius coupled source.

The Gaussian finite-polynomial expansion retains the signed pair kernel with factor `exp(-H^2*log(n/m)^2/8)`. At fixed H, this factor is close to one for near-equal n,m. The retrieved uniform upper bound replaces the off-diagonal by an absolute coefficient square times `exp(-H^2/(8*M^2))`; that factor tends to one as M grows. The twisted first-moment theorem also requires `24*n<=H^2` and an admissible high-height interval. Neither theorem supplies a fixed-window second-moment estimate as the Mobius cutoff tends to infinity. No critical-line infinite Dirichlet-series substitution was made.

For the next direct estimate, expanded the cutoff increment on paper, retaining the full zeta multiplier. Set `s(t)=1/2+it`, `w(t)=exp(-2*(t-tau)^2/H^2)`, `J=integral w*|zeta(s(t))|^2`,

`A(u)=integral w*zeta(s(t))*exp(-it*u)`,

`B(v)=integral w*|zeta(s(t))|^2*exp(it*v)`.

For `Q_n=integral w*|zeta(s(t))*P_n(s(t))-1|^2`, finite expansion gives

`Q_n-Q_(n-1) = mu(n)^2*J/n + 2*mu(n)/sqrt(n)*(sum_(1<=m<n) mu(m)/sqrt(m)*Re B(log(n/m)) - Re A(log n))`.

This is an elementary paper identity, not a new Lean result or cancellation theorem. The diagonal sum is at most `J*(1+log X)`. The complete signed increment sum, including its linear subtraction, is the unresolved quantity. Divisor-head cancellation does not bound the near-equal pairs appearing here. Replacing them by absolute values recovers a power loss. No dissipative sign or sufficient bound for their accumulated contribution was proved.

Checked the proposed physical compensation against `FermiNymanRawMobiusTailFloor` and `FermiNymanLogMobiusAuxiliaryVariance`. Exact raw floor inversion retains the harmonic tail `H_N/t`; the logarithmic source retains a Chebyshev-profile variance. The scalar normalization limit alone gives no critical rate for these terms. These are distinct physical sources, so no unproved identification with Q_n or transfer of their lower bounds to the Gaussian norm is asserted. First-moment control, even if strengthened, would still require a separate argument to control this squared norm.

**Hard step still open:** a source-specific upper estimate on the complete signed cutoff-increment sum, or equivalently on C12.26's coupled covariance. The next attack must estimate that sum, with all near-equal products and the linear subtraction retained; another diagonal identity, conditional receiver, or absolute mean-value estimate does not discharge it. C12.19 also remains open.

**Outcome:** no new bound, Lean edit/build, numerical experiment, RH proof or falsification. Four deep searches and one lexical search terminated; two deep results were partial, and deep coverage was snapshot-based with compiler freshness limitations. Candidate lemmas and source arguments were inspected; no global absence claim is inferred from the search. Owned search JSON files cleaned. Goal active and unmet.

## C12.28: complete prime-current work does not yet close the increment estimate

Previous continuation and this attempt are **no mathematical frontier progress**. Stayed with C12.26's full coupled error and C12.27's signed increments. Tested the exact prime-divisor recurrence as a possible source of the required one-sided covariance estimate.

Source basis: `Sieve.MoebiusLogRecursion.moebius_pmul_log` proves `mu*log=-(Lambda convol mu)` with pointwise multiplication on the left. Its finite divisor swap retains every prime power. `EulerDeletionLogPrimeAbel` proves the complete logarithmic Abel-history identity in its physical carrier. Neither statement is a norm estimate. The following application to finite critical-line polynomials is a paper calculation, not a new Lean theorem.

Write `L_X(s)=sum_(n<=X) mu(n)*log(n)*n^(-s)` and keep `E_X=zeta*P_X-1`. Finite interchange gives

`zeta(s)*L_X(s) = -sum_(d<=X) Lambda(d)*d^(-s)*(E_(floor(X/d))(s)+1)`.

For integer X>=1 set `T_X=sum_(1<=m<X) log((m+1)/m)*E_m`. Finite Abel summation gives `zeta*L_X=log(X)*E_X-T_X`. With the fixed Gaussian weight w from C12.27, define the full signed prime work

`W_X=Re integral w*conj(E_X)*sum_(d<=X) Lambda(d)*d^(-s)*(E_(floor(X/d))+1)`.

Consequently `log(X)*Q_X=Re integral w*conj(E_X)*T_X-W_X`. The `+1` terms are part of W_X and were not discarded or estimated separately as a negligible error.

**Conjecture tested, still unproved:** for every positive epsilon, `W_X>=-C_epsilon*X^epsilon` at each fixed Gaussian window. This is another one-sided formulation of the same hard source estimate, not new knowledge. A logarithmic-history comparison could use such a lower bound, but no conditional receiver was added. No sign or subpower lower bound for W_X was established.

The attempted proof keeps the prime phases through the pairing. Nonnegativity of Lambda does not orient these complex mixed products. Cauchy--Schwarz on the shorter-cutoff terms pays a sum with weights `Lambda(d)/sqrt(d)`; it does not provide the required critical cancellation. Splitting small and large prime powers leaves the large-prime/cofactor correlation coupled to the same near-equal products. No estimate overcoming this loss was proved. Replacing the prime sum by a separate scalar normalization or omitting the constant terms is not a valid closure.

Also checked the corresponding compensation warning in `EulerDeletionLogPrimeForcing`: its physical harmonic forcing has energy comparable to the cutoff, so that physical recurrence cannot be shortened by declaring its forcing subpower. No identification of that carrier with the present Gaussian field, or transfer of its lower bound, is asserted. Pole clearing provides holomorphy; it supplies no sign for W_X. No Hardy support or spectral-coercivity theorem was proved in this attempt.

**Remaining work:** prove the source-specific lower bound for the entire W_X, or directly bound the complete covariance in C12.26. The recurrence only locates the same missing cancellation. C12.19, C12.26 and their signed source bounds remain open; no route is retired.

**Outcome:** no new bound, Lean edit/build, numerical experiment, RH proof or falsification. Two deep searches terminated with partial snapshot coverage and compiler freshness limitations; candidate lemmas and source arguments inspected against relevant sources. Owned search JSON files cleaned. Goal active and unmet.

## C12.29: physical-kernel comparison has not bounded the complete prime work

Previous turn and this attempt are **no mathematical frontier progress**. Tested whether the corpus's exact physical correlation bounds give the missing lower estimate for C12.28's W_X. No comparison with sufficient direction and size was proved; the Gaussian prime work and the physical short reconstruction must not be identified without such a proof.

Checked `LogarithmicSawtoothCorrelationBound`, `CCMPrimeDeficitShortQuadraticWork`, `CCMPrimeDeficitShortSourceMatrix`, `CCMPrimeDeficitCoefficientAction`, and `CCMPrimeDeficitBoundaryDiagonal`. The reciprocal sawtooth bound controls its specified scalar integral. The short reconstruction controls its remainder and retains the complete signed quadratic form. The source matrix is indefinite, and stationarity at the Mobius vector does not give a maximum or minimum. The thick-shell diagonal is controlled at critical scale, but its signed off-diagonal remains. None of these facts alone provides a lower bound for W_X.

Tested the actual Mobius vector rather than proposing arbitrary-coefficient positivity. Let `H=logarithmicDilationSum ccmPrimeDeficitDilationSource`. On `0<=u<log 2`, its source definition gives `H(u)=exp(u)-1`. Thus for a square terminal scale `exp(T)=U^2` and any band I with `U/sqrt(2)<a<=U` for every a in I, finite expansion gives

`sum_(a,b in I) mu(a)*mu(b)*H(T-log(a*b)) = U^2*(sum_(a in I) mu(a)/a)^2 - (sum_(a in I) mu(a))^2`.

This is a paper diagnostic, not a new Lean theorem. Positivity of each kernel entry does not orient this difference for signed Mobius coefficients. No critical lower estimate for this difference was proved. Its interactions with the complementary indices remain in the complete form, so it is neither a global counterexample nor a bound for the complete source. Separately bounding the two moments also does not produce the required cancellation.

**Unresolved:** C12.28's whole prime-current lower bound and C12.26's complete coupled norm. This physical comparison attempt has not reduced those obligations. Do not repeat the already-insufficient scalar-kernel, diagonal, stationarity, or arbitrary-PSD arguments as new progress.

**Outcome:** one deep search terminated with partial snapshot coverage and compiler freshness limitations; candidate lemmas and source arguments inspected. Owned JSON cleaned. No new bound, Lean edit/build, numerical experiment, RH proof or falsification. Goal active and unmet.

## C12.30: finite convolution packets retain the common-factor covariance

Previous turn and this attempt are **no mathematical frontier progress**. Tested the finite Heath--Brown decomposition inside the complete prime work of C12.28, retaining the alternating packet terms rather than estimating separate source sectors.

`Sieve.HeathBrownIdentity` gives the exact arithmetic-function defect `D_L=1-M_L*zeta`, its vanishing below L+1, and vanishing of `D_L^k` below `(L+1)^k`. Its finite prime-coefficient identity is valid on that stated coefficient range. This does not identify a sharply truncated convolution polynomial with an unrestricted product on the critical line. Product cutoffs and all packet cross terms must remain. No critical-line infinite-series interchange, omitted convolution tail, or norm contraction of a defect power was used.

Checked `Sieve.TypeIIEnergyBound`, the sparse square-root-scale mean value, and the same-frequency cofactor Montgomery estimate. The type-II correlation bound uses a specific curved near-diagonal phase with positive displacement and range hypotheses. That phase was not obtained for the present fixed-window source. The cofactor estimate retains the exact convolution but its upper bound still contains range-length costs. No packet-specific cancellation removing those costs was proved.

The direct common-factor test exposes why ordinary logarithmic phases do not themselves help in that variable: for positive a,b,d, `log(a*d)-log(b*d)=log(a/b)`. Thus the critical covariance kernel B from C12.27 satisfies the paper scaling relation

`B(log((b*d)/(a*d)))/sqrt((a*d)*(b*d)) = (1/d)*B(log(b/a))/sqrt(a*b)`.

The checked `MobiusReciprocalPrimitiveRatio` source establishes the matching arithmetic sign factorization: `mu(d*a)*mu(d*b)=mu(d)^2*mu(a)*mu(b)` when d is coprime to both a and b, and zero otherwise. The surviving common-factor weight is nonnegative; the remaining arithmetic signs belong to the primitive coprime pair. This comparison is not a bound on that pair sum. The linear subtraction in the full coupled error is still retained. No global no-go for other bilinear reorganizations is asserted.

Grouping all alternating packet terms by their total coefficient returns the exact original source. Separating their norms loses that cancellation. I did not find an intermediate grouping with a proved subpower covariance bound. Increasing the defect order therefore has not discharged the higher mixed-moment obligation already noted in C12.26.

**Hard target unchanged:** control the complete signed primitive-pair covariance, including all product cutoffs and the linear subtraction, or prove C12.28's whole prime-work lower bound. No new receiver or identity-only Lean module was added.

**Outcome:** one deep search terminated with partial snapshot coverage and compiler freshness limitations; candidate lemmas and source arguments inspected against the relevant source. Owned JSON cleaned. No new bound, Lean edit/build, numerical experiment, RH proof or falsification. Goal active and unmet.

## C12.31: collective additive shifts still lack the critical signed estimate

Previous turn and this attempt are **no mathematical frontier progress**. Tested additive-shift grouping of C12.27's complete covariance. For the quadratic term, write the pair as `(a,a+h)` and keep the literal endpoint `a<=X-h`, the ratio kernel `Re B(log((a+h)/a))/sqrt(a*(a+h))`, and the original linear subtraction. No bound on this complete signed aggregate was proved.

The current corpus's `Sieve.AveragedChowlaInterface` defines `AveragedChowlaUniform` and uses it as an explicit premise in its reduction. Exhaustive source-text search for that named predicate in RHTower found its definition, references and premise-taking consumers, not a proof of the required Mobius instance. This is a statement about those references, not a global absence claim about all differently named results. No correlation premise was assumed in this attempt.

There is also a scale mismatch: at comparable shift and interval lengths, an aggregate estimate of size `o(N^2)` weighted by a kernel of size `1/N` only gives `o(N)`, not the required `O(N^epsilon)` for every epsilon. Variable endpoints and nonconstant weights would need their own retained partial-sum estimates. `Sieve.ShiftSumBound.abs_shift_sum_le`, retrieved in the search, consumes such correlation bounds; it does not establish them.

Checked `Sieve.FejerCorrelation`: its identity retains the signed Fejer-weighted aggregate as a window mean square, with explicit translation error. Nonnegativity of that square gives no needed upper estimate. Replacing the fixed-start source by an average of windows, or completing endpoints and dropping the translation terms, does not discharge the target. No uniform bound for the actual window mean square at the requisite scale was proved.

The existing `EulerDeletionFirstTailPairCorrelation` confirms the analogous exact fixed-start shift kernel and preserves every endpoint. Its available upper comparison uses the still-unbounded predictable drift. The additive-triangle source likewise isolates the one-sided aggregate correlation bound as an input. Neither was treated as independent cancellation.

**Remaining hard problem:** prove a collective signed shift estimate for the actual Mobius coefficients with the full ratio weights and boundary terms, or establish the original coupled covariance/prime-work bound directly. Separate absolute correlation bounds, positivity identities and another conditional receiver would not finish this step. No route retired and no new identity-only Lean module added.

**Outcome:** one deep search terminated with `partial=false` and snapshot coverage, with compiler freshness limitations; candidate lemmas and source arguments inspected. Owned JSON cleaned. No new bound, Lean edit/build, numerical experiment, RH proof or falsification. Goal active and unmet.

## C12.32: complete logarithmic renewal and signed energy coercivity

Previous activity and this attempt produced **no mathematical frontier progress**. Tested the full signed logarithmic renewal with every prime-power delay and the Abel-history term retained. No coercive inequality for the actual source was proved.

The checked `Sieve.MoebiusLogRecursion.sum_moebius_mul_log_eq` supplies the finite arithmetic identity. Its paper Abel form, with `M(x)=sum_(n<=x) mu(n)` and `f(t)=exp(-t/2)*M(exp t)` for t>=0, is

`t*f(t) = integral_(0..t) exp(-(t-u)/2)*f(u) du - sum_(2<=d<=exp t) Lambda(d)/sqrt(d)*f(t-log d)`.

For `0<eps<1/2`, put `sigma=1/2+eps` and `g(t)=exp(-eps*t)*f(t)`. The tested energy pairing on `[0,T]` retains

`P_sigma(T)=sum_(2<=d<=exp T) Lambda(d)/d^sigma * integral_(log d..T) g(t)*g(t-log d) dt`.

The Abel-history kernel is `exp(-sigma*u)`. A cutoff-independent lower bound `P_sigma(T)>=-C_sigma*integral_(0..T) g(t)^2 dt-B_sigma` would make the coefficient t coercive beyond a fixed initial interval. This is an **unproved source estimate**, not a new theorem or an assumed input. No receiver module was added. Direct Cauchy--Schwarz instead incurs `sum_(d<=exp T) Lambda(d)/d^sigma`; it does not give the required cutoff-independent constant.

Second pass: subtract the continuous prime main term while keeping its boundary. Writing `a=1-sigma>0`, that term acts by `h(t)=integral_(0..t) exp(a*(t-u))*g(u) du`. Its exact paper energy identity is `integral_(0..T) g*h = h(T)^2/2-a*integral_(0..T) h^2`. Neither its negative term nor the remaining signed prime-error pairing was controlled in terms of the source energy. Replacing this forward integral by a backward integral requires a separate infinite-tail identity and retains a finite-cutoff tail; no tail bound was assumed. Dropping that term would not establish coercivity.

`ChebyshevPsiPowerLogPNT.exists_chebyshevPsi_power_log` controls the cumulative error by `C*x*exp(-c*(log x)^(1/10))`. It is not a total-variation bound for the signed prime measure. After the critical exponential weight, even the cumulative envelope retains `exp((1-sigma)*u-c*u^(1/10))`. Integration by parts would still require control of the actual shifted-source correlations and their boundary terms; no such estimate was obtained. Thus subtracting the continuous main term did not remove the hard signed covariance.

The search also returned the exact compensated renewal and logarithmic Abel-history identities, and the critical Laplace renewal sum. None supplies the missing lower pairing estimate. The physical forcing's already-recorded linear energy cannot be discarded or transferred to this carrier without proof. Existing Mertens mean-square exponent laws remain consumers. These checks do not count as frontier movement.

**Remaining hard problem:** control the complete actual-source prime-delay pairing, including its continuous-main-term boundary and signed prime-error contribution, or prove C12.26/C12.28 directly. No route retired; no identity-only or conditional Lean module added.

**Outcome:** two deep searches terminated with partial snapshot coverage and compiler freshness limitations; candidate lemmas and source arguments inspected. No bound, Lean edit/build, numerical experiment, RH proof or falsification. Goal active and unmet.

## C12.33: reciprocal-harmonic boundary coupled to the prime remainder

Previous turn and this attempt made **no mathematical frontier progress**. Tested the exact harmonic boundary-minus-tail identity against C12.32's continuous prime contribution. No cutoff-uniform bound for the coupled boundary and prime remainder was proved.

Checked `Sieve.MoebiusHarmonicTailIdentity`: the harmonic sum `m(N)=sum_(n<=N) mu(n)/n` equals `M(N)/N` minus the literal absolutely convergent Mertens tail. Its limiting zero is proved. The real-cutoff arbitrary-log-rate theorem also holds, but multiplying an inverse-logarithmic bound by `exp((1-sigma)*T)` does not give a bounded critical normalization for `1/2<sigma<1`. No critical rate was inferred from convergence.

The direct paper substitution into C12.32 is, with `a=1-sigma`,

`g(t)=exp(-sigma*t)*M(exp t)`,

`q(t)=exp(a*t)*m(exp t)`,

`h(t)=q(t)-g(t)`.

Finite Abel summation identifies this h with the forward continuous-main-term integral. At each `t=log n`, g and q have the same jump `mu(n)*n^(-sigma)`, so h is continuous. Between jumps, `g'=-sigma*g` and `q'=a*q`. Keeping all jumps gives the paper identity

`integral_(0..T) (sigma*g(t)^2+a*q(t)^2) dt = (q(T)^2-g(T)^2)/2 - sum_(1<=n<=exp T) mu(n)*n^(-sigma)*h(log n)`.

The diagonal jump squares cancel exactly. This does **not** bound the remaining signed jump work. Expanding that work yields the actual triangular pair sum with terms `mu(n)*mu(m)*n^(-2*sigma)*(n/m-1)` for `m<n`; no upper bound for the complete right side was obtained. Discarding the endpoint difference or applying separate absolute bounds loses the needed cancellation. This paper diagnostic is not new Lean knowledge and was not formalized as another receiver.

Second-pass corpus check found `CoupledFloorMobiusCriticalBoundaryCancellation`, which does prove a strong L2 boundary cancellation for its own source. The read definitions use normalization `exp(-(1+omega+delta)*t)` and common coefficients `mu(d)*d^(-1-2*omega)`, with `0<omega<1/2`. Neither an identity with the present g/q source nor an estimate transferring its norm to the present critical weight was proved. Its theorem therefore does not discharge the current pairing. The order-three reciprocal Laplace isometry likewise preserves its full covariance without supplying a saving.

The existing critical harmonic-tail obstruction also rules out replacing the target by vanishing `N*m(N)^2`; the subpower/strict-half target remains unchanged. No vanishing critical boundary was assumed. Current searches returned Mertens energy consumers, not an applicable producer for this paired current; this is not a global absence claim.

**Remaining hard problem:** estimate the complete signed jump/boundary work together with the prime-error pairing, or directly establish C12.26/C12.28. The diagonal cancellation alone leaves the same arithmetic off-diagonal problem. No route retired and no auxiliary identity/no-go module added.

**Outcome:** two deep searches terminated with `partial=false`, snapshot coverage and compiler freshness limitations; candidate lemmas and source arguments inspected. No new bound, Lean edit/build, numerical experiment, RH proof or falsification. Goal active and unmet.

## C12.34: large-source inverse attack at the half-power threshold

Previous turn and this attempt made **no mathematical frontier progress**. Tested whether a power-size excursion of the complete Mobius source forces a contradictory prime-correlation pattern. No inverse statement at the half-power threshold, or contradiction from such a pattern, was proved.

Checked `MoebiusPretentiousGap.exists_primeCosPlusSum_ge_logLog`: the actual lower bound is `log log x - 11 log log |t| - C`, on its stated large-frequency range. Also checked the finite smooth-source Halasz dichotomy, the scalar `(1+M)exp(-M)` shell-cost conversion, the explicit GHS master inequality, and the range-restricted twisted-series mean-value inequality. The finite smooth-source bound is a reciprocal-weight sum over all subsets of the prime core, not the sharply truncated critical polynomial. The GHS master requires complete multiplicativity, so it cannot simply be applied to mu; its displayed recursion errors are also of linear size before logarithmic division. The twisted-series result requires sigma>1 and retains its truncation error and length cost. None excludes an `N^(1/2+eps)` Mertens excursion for `0<eps<1/2`. No critical-line continuation of these inequalities was assumed.

The unconditional Menon window estimate and the retrieved large-value-count statements retain an average over starts or a population bound. A bound allowing an exceptional start/frequency is not exclusion of the individual source value needed here. I did not prove an amplification from one actual source excursion to enough separated large values to contradict those estimates. Powers or repeated packets cannot be treated as independent samples; their product cutoffs and common-factor terms remain.

Second pass tested the actual coefficients against `SteinhausPrimeCorrelationBudget`. For N>=1, a prime p, `Z_N=sum_(1<=n<=N) mu(n)^2/n` and the normalized vector `a_n=mu(n)*n^(-1/2-it)/sqrt(Z_N)`, its literal prime correlation has the paper form

`sum_(n<=N/p) a_n*conj(a_(p*n)) = -p^(it)/(sqrt(p)*Z_N) * sum_(n<=N/p, p does not divide n) mu(n)^2/n`.

Thus the available squared-correlation budget removes these exact phases. Its right side is the frequency cost `sum n*|a_n|^2`, not the complete signed physical covariance. No implication from a large critical polynomial value to a violation of this budget was obtained. The formula is a diagnostic, not a new theorem or a global no-go for phase-sensitive inverse methods. Coprimality and the finite endpoint were retained.

**Remaining hard problem:** prove an inverse estimate strong enough to exclude an individual half-power excursion using the full arithmetic phase/cofactor information, or establish the complete signed covariance directly. Current prime-distance and correlation-norm estimates did not do so. No route retired and no auxiliary inverse receiver/no-go module added.

**Outcome:** one deep search terminated with `partial=false`, snapshot coverage and compiler freshness limitations; candidate lemmas and source arguments inspected. No new bound, Lean edit/build, numerical experiment, RH proof or falsification. Goal active and unmet.

## C12.35: full prime-packet covariance and coherent terminal blocks

Previous turn and this attempt made **no mathematical frontier progress**. Returned to the actual first-tail prime fields of C12.19 and tested a collective Gram estimate. No bound for the full arithmetic combination was proved.

The raw first-tail field for a prime `N<p<=2N` is exactly the negative step `H_p(t)=-1_(p<=t)`, since no other multiple of p lies in the window. These fields overlap. For an integer `N<K<2N`, the paper test with `P={p prime:N<p<=K}`, `S=sum_P log p` and first-tail weights `1/(t(t+1))` gives

`||sum_P log(p)*H_p||^2 >= S^2*(1/K-1/(2N+1))`,

while `sum_P log(p)*||H_p||^2 <= S/N`.

These finite diagnostics retain the common late part of every step. They are not an upper estimate for the complete Mobius source, and no new obstruction module was added. The checked theta PNT concerns the prime mass, not cancellation with its composite complement. Thus a matrix-norm bound over arbitrary prime-packet directions would be a stronger requirement than the actual complete-source inequality and cannot be justified by treating these raw fields as orthogonal.

Checked `EulerDeletionUpperHalfPrimePhaseCovariance` and `EulerDeletionUpperHalfPrimePacketCovariance`: their orthogonality is for centered periodic prime phases over a full p*q period; incomplete weighted prefixes retain a p*q cost. `EulerDeletionUpperHalfPrimePhysicalEnergy` retains the paired source endpoint alongside the suppressed residual packets. These are not the raw H_p fields above. Neither full-period orthogonality nor the residual packet norm removes that endpoint or proves the first-tail Gram estimate.

Checked `EulerDeletionRamarePacketDilation`: individual cofactor energies have an exact 1/p factor, but the unequal-prime covariance remains the integral of one cofactor against another at argument `(p/q)*v`. This preserves the source-specific cross term; it does not supply a Bessel bound. No carrier identification or discarded boundary was used to substitute these formulas for C12.19.

Second pass retained the complete log-weighted combination `L_N=sum_(p<=2N) log(p)*H_p`. Its prime sector is `-(theta(t)-theta(N))`; the complementary composite sector must cancel it inside the full source. Projecting out the coherent prime sector merely leaves its signed interaction with that complement. No critical estimate for that interaction or for the remaining perpendicular component was obtained. Existing full-source logarithmic/stretched-exponential savings do not yield the all-epsilon subpower ceiling, and were not relabeled as such.

**Remaining hard problem:** control the complete signed cofactor combination, including prime/composite cancellation at the current cutoff. Neither a generic Gram bound, one-prime dilation factor, nor periodic-residual covariance has discharged C12.19 or the coupled covariance target. No route retired and no auxiliary identity/conditional receiver added.

**Outcome:** one deep search terminated with `partial=false`, snapshot coverage and compiler freshness limitations; candidate lemmas and source arguments inspected. No new bound for the complete source, Lean edit/build, numerical experiment, RH proof or falsification. Goal active and unmet.

## C12.36: complete Liouville source and the square contribution

Previous turn and this attempt made **no mathematical frontier progress**. Tested whether complete multiplicativity supplies a one-sided half-power bound for the Liouville source that survives its exact square-dilation relation to Mobius. The analytic-unit wall alone is already equivalent to the original wall and supplies no estimate.

The first current corpus search terminated with `partial=false` and snapshot/compiler freshness limitations. Checked source statements: `LiouvilleDirichletSeries` gives complete multiplicativity and the square-indicator divisor convolution; `LiouvilleEvenIndexPositiveRecurrence` rules out origin growth below exponent 1/2 and supplies cofinal positive additive correlations, not an upper bound. `Sieve.LiouvilleCesaroUnconditional` retains x^sigma with sigma>=1. The current target must retain the square forcing and prove a new upper estimate for the complete signed source. No Liouville sign conjecture, continuation wall or critical covariance estimate is assumed.

The second deep search returned partial results with snapshot/compiler freshness limitations; candidate lemmas and source arguments were inspected. The checked product-fibre law retains a single Liouville sign on each fibre, and taking fibre absolute values keeps its whole unsigned mass. The dyadic Gram identity is positive but has no upper bound. Complete multiplicativity does make the GHS chain applicable to Liouville; its explicit recursion errors remain linear in the cutoff before division by a logarithm. None supplies the desired half-power ceiling.

The direct paper attempt retained the even-prime-power contribution instead of suppressing the square forcing. Write `L(x)=sum_(n<=x) lambda(n)` and `g(t)=exp(-sigma*t)*L(exp t)`, with `1/2<sigma<1`. Complete multiplicativity and the divisor identity for log give

`lambda(n)*log n = -(Lambda * lambda)(n) + 2*(Lambda_square * lambda)(n)`,

where `Lambda_square(m^2)=Lambda(m)` and is zero off squares. Finite Abel summation then gives the paper identity

`t*g(t) = integral_(0..t) exp(-sigma*(t-u))*g(u) du - sum_(d<=exp t) Lambda(d)*d^(-sigma)*g(t-log d) + 2*sum_(m^2<=exp t) Lambda(m)*m^(-2*sigma)*g(t-2log m)`.

After pairing with g on a finite interval, the absolute square-delay contribution is at most `2*sum_m Lambda(m)*m^(-2*sigma)` times the g energy; this coefficient is finite because `2*sigma>1`. The Abel-history contribution is bounded by `1/sigma` times that energy. These estimates do not control the remaining prime-delay work

`P_sigma(T)=sum_(d<=exp T) Lambda(d)*d^(-sigma)*integral_(log d..T) g(t)*g(t-log d) dt`.

The attempted lower bound `P_sigma(T)>=-C_sigma*integral_(0..T)g(t)^2 dt-B_sigma`, uniform in T, remains unproved. A pointwise induction loses the sign when applied to the negative prime-delay coefficients; taking absolute values restores the nonsummable critical prime mass. Removing the square term is therefore not the missing estimate.

Second pass used the exact dilation anticorrelation `lambda(n)*lambda(p*n)=-1` for primes p and n>=1. On the critical coefficient vector `a_n=lambda(n)/sqrt(n)`, its finite correlation is `sum_(n<=N/p) a_n*a_(p*n)=-p^(-1/2)*sum_(n<=N/p)1/n`. This is only the matched-multiple slice. The product of partial sums in P_sigma contains all pairs `a<=exp t`, `b<=exp(t)/d`; the matched slice `a=d*b` leaves the unmatched pairs. Summing over d reconstitutes the log recursion, not a sign estimate for those unmatched pairs. No transfer from coefficient anticorrelation to the full partial-sum pairing was proved.

These are paper diagnostics, not new Lean theorems, and no identity/conditional receiver module was added. No one-sided Liouville sign assumption, deleted square forcing, or critical-line continuation was used.

**Remaining hard problem:** prove a lower bound for the complete prime-delay work, or a direct all-epsilon half-power bound for the complete source, including the unmatched pairs. Square forcing and exact prime anticorrelation have not discharged that problem. No route retired.

**Outcome:** two research searches terminal (first `partial=false`, second partial). No frontier bound, Lean edit/build, numerical experiment, RH proof or falsification. Goal active and unmet.

## C12.37: noncomparable pairs after the divisor sign law

Previous turn and this attempt made **no mathematical frontier progress**. Targeted the complete noncomparable section of the Hilbert/Gamma source, using the proved divisor-comparable sign law as a retained negative contribution. The target was a subpower upper bound for the full residual, not an unconditional nonpositivity claim for that residual.

Checked `MobiusDivisorMonotoneSignLaw`: its complement injection depends on `m+n=m*(e+1)` being the next multiple after `n=m*e`. Checked `MobiusHilbertDivisorBoundary`: the divisor sector already cancels twice the diagonal up to a constant, but the noncomparable excess is a remaining input. Checked finite coprimality-matrix factorization: its middle diagonal is Mobius-signed, and no positive matrix bound on the actual source follows just from this factorization. No new estimate has yet been proved.

The attempted extension maps a nonzero pair to `(g,l)=(gcd(m,n),lcm(m,n))`. Writing `m=g*a`, `n=g*b` with coprime a,b gives `l=g*a*b`; the squarefree conditions imply `mu(m)*mu(n)=mu(g)*mu(l)`. The Hilbert-weight discrepancy is exactly

`1/(m+n)-1/(g+l) = (a-1)*(b-1)/(g*(a+b)*(1+a*b)) >= 0`.

Thus the map preserves the sign, but enlarges the kernel contribution in both positive and negative source directions by different amounts. It is many-to-one and may send l beyond N. The divisor sign theorem cannot be applied after suppressing those multiplicities or dropping the finite-cutoff error. No signed bound for their combined contribution was obtained.

The current corpus searches found the exact lcm-fibre collapse and its weighted finite-carrier inversion in `EulerDeletionTruncatedDivisorPairCorrelation`. The unweighted complete fibre coefficient is `mu(q)`. For q<=N every divisor of q is in the source cutoff, so the paper flat-kernel split reads

`sum_(m,n<=N, lcm(m,n)>N) mu(m)*mu(n) = M(N)^2-M(N)`.

This keeps the actual source fluctuation inside the lcm overflow; it gives no small upper bound. Distinct terminal primes already give positive overflow pairs. Neither this diagnostic identity nor the unweighted fibre collapse was substituted for the physical Hilbert weight.

Second pass retained that weight through `1/(m+n)=integral_(0..infinity) exp(-(m+n)*t) dt`. Applying the checked finite lcm inversion to `a_n=mu(n)*exp(-n*t)` rewrites each fibre as

`sum_(d|q) mu(q/d)*(sum_(n|d,n<=N) mu(n)*exp(-n*t))^2`.

The squares are nonnegative, but their Mobius multipliers retain the sign problem. The cancellation at t=0 does not bound the weighted integral. Taking absolute values loses the needed cancellation, while summing the fibres with all signs returns the original energy. No upper estimate for the signed within-fibre variation or the overflow was proved.

**Remaining hard problem:** the all-epsilon subpower upper bound for the complete noncomparable excess, including its kernel variation and cutoff overflow. The divisor-comparable sign law alone does not control those terms. These paper diagnostics are not new frontier theorems; no route retired or auxiliary identity/receiver module added.

**Outcome:** two deep searches terminated with partial results and snapshot/compiler freshness limitations; candidate lemmas and source arguments inspected. No frontier bound, Lean edit/build, numerical experiment, RH proof or falsification. Goal active and unmet.

## C12.38: cofinal finite-energy returns from actual source zeros

Previous turn and this attempt made **no mathematical frontier progress**. The cofinal-return attack first rechecked the average-of-cutoffs proposal; C12.25 already records the uncontrolled cutoff variance, so that argument is not repeated as progress. The distinct test was whether actual zeros of the infinite Mobius Laplace profile can anchor bounded-energy returns of the finite source at strict-half exponents. `MobiusCriticalProfileReturnSeparation` already distinguishes exact point zeros from energy returns; the missing task was a quantitative collar and truncation estimate, not that distinction itself.

Checked `MobiusCofinalCubicEnergyCriterion` and the Fatou subsequence receiver in `MobiusLaplaceMellinPlancherelBridge`: a fixed finite energy ceiling must recur at arbitrarily large integer cutoffs for exponents approaching the critical line from the right. The known exact point returns alone do not discharge this condition. No bounded-energy return has yet been constructed.

The paper collar attempt used the literal series `F(x)=sum_n mu(n)*exp(-n*x)` and a small positive zero x0. The geometric coefficient envelope gives `|F'(x)|<=C*x0^(-2)` for `x0/2<=x<=3*x0/2`, hence `|F(x)|<=C*|x-x0|*x0^(-2)`. For `1<r<2` and `0<h<=x0/2`, this only yields

`integral_(x0-h..x0+h) x^(r-1)*|F(x)|^2 dx <= C_r*x0^(r-5)*h^3`.

A bounded collar energy can therefore be obtained by shrinking h sufficiently. This controls only that collar, whose relative width from this envelope tends to zero at the origin. It does not bound the whole weighted energy. No density or spacing estimate for the actual zero collars sufficient to cover the remaining region was proved.

The finite-section discrepancy obeys the paper absolute tail estimate

`|F(x)-F_N(x)| <= exp(-(N+1)*x)/(1-exp(-x))`.

Taking N of order `x0^(-1)*log(1/x0)` can make this discrepancy small on the collar. Below the collar, the available elementary estimate is only `integral_(0..x0/2) x^(r-1)*|F_N(x)|^2 dx <= N^2*(x0/2)^r/r`. Its upper envelope is unbounded on that choice of cutoffs for `1<r<2`. This is a failure of the attempted estimate, not a lower bound on the actual energy or a no-go theorem for source-zero methods.

Second pass kept the checked exact Lambert renewal law `sum_(k>=1) F(k*x)=exp(-x)`. At a source zero it fixes the signed sum over k>=2, not the squared energy below the zero. Pairing the renewal identity with F on a compact positive interval leaves the full signed dilation correlations. A zero at the interval endpoint supplies no lower bound for those correlations. Absolute dilation norms have weights `k^(-r/2)`, whose sum diverges in the target range; no contraction or signed replacement was proved. The checked scale-current oscillation theorem was not misread as either an upper bound or a refutation of critical weighted regularity.

**Remaining hard problem:** construct actual bounded-energy returns with control of the entire origin-side region, or prove the complete signed dilation/covariance estimate directly. Local zero collars and tail approximation have not advanced that frontier. No route retired or auxiliary identity/receiver module added.

**Outcome:** two deep searches terminal with partial results and snapshot/compiler freshness limitations; candidate lemmas and source arguments inspected. No frontier bound, Lean edit/build, numerical experiment, RH proof or falsification. Goal active and unmet.

## C12.39: normal-breadth matching through physical subset expansion

Previous turn and this attempt made **no mathematical frontier progress**. Rechecked the normal-breadth source target and C12.10: increasing the low-breadth cutoff, reusing target counts, extracting balanced pairs, or normalizing degrees is not an estimate of the remaining imbalance. Attempted an all-subset expansion bound for the actual opposite-sign physical graph, using collision/codegree control and retained target depletion.

Current source checks retain the exact scopes: `LowBreadthMarkerTransport` uses a strict target-count surplus; `RouteEMarkerHallLawAll` counts each sign against the prime-count scale, not the full normal-breadth source; `MarkerPairBudget` bounds shifted pairs of prime markers. No all-subset physical expansion estimate has yet been proved.

For a source subset A, let `r_A(v)` count its incident edges at the distinct physical target v, `I_A=sum_v r_A(v)`, and `K_A=sum_v r_A(v)^2`. The direct paper second-moment attempt gives `|Gamma(A)|>=I_A^2/K_A` when K_A>0. After a target set D is removed, Cauchy--Schwarz gives the weaker sufficient lower bound

`|Gamma(A) outside D| >= max(0,I_A-sqrt(|D|*K_A))^2/K_A`.

The desired near-cover requires these actual physical quantities to control every subset, not only each vertex. I did not obtain such arithmetic estimates. The displayed depletion bound is only a sufficient attempt; arbitrary deletion is stronger than the actual augmenting-path problem, and its weakness does not refute matching.

Checked `MarkerLossDevice` and `HallInjectionLiftedMarkers`: their second moment counts prime markers with the same reciprocal start. Their discarded set is a set of starts, not an arbitrary set of already occupied physical targets. The resulting injection covers prime sources and retains the small-cofactor condition. Thus their pair budget cannot be inserted as K_A for the normal-breadth physical graph without a new counting argument.

Checked `WindowMatching`: its construction uses a common target pool in the same window and bounds the whole source cardinality by that pool. For this complete cell graph, `I_A=|A|*|T|` and `K_A=|A|^2*|T|`, so the second-moment expression gives exactly |T|. It supplies no extra capacity beyond the already known pool count. This is a diagnostic of the attempted extension, not a new general no-go theorem.

Second pass retained nonunique marker decoding at larger cofactors. An equality `a*p=b*q` with distinct prime markers forces `a=q*k`, `b=p*k` for a common k. Such labels represent the same physical target. The checked injection avoids this through cofactors smaller than every marker; dropping that condition reintroduces these collisions. A subpower divisor bound on multiplicity alone only divides label mass by a subpower factor and does not prove near-complete physical coverage. No source-specific all-subset overlap/depletion estimate was derived from it.

The weighted cut-deficiency theorem in `MobiusBoundaryOppositeSignTransport` also retains the full missing requirement: global unused capacity must pay every weighted Hall cut. In particular a cut consisting of one entire sign class already retains its excess over all opposite-sign capacity. No small source imbalance was assumed to establish that cut. Expanding balanced extracted packets does not discharge it.

**Remaining hard problem:** an arithmetic bound for every physical cut (or a direct complete signed covariance estimate), together with aggregate displacement and the unmatched/seam contribution. No near-complete normal-breadth transport or critical source bound was constructed. No route retired or auxiliary combinatorial receiver added.

**Outcome:** one deep search terminated with partial results and snapshot/compiler freshness limitations; candidate lemmas and source arguments inspected. No frontier bound, Lean edit/build, numerical experiment, RH proof or falsification. Goal active and unmet.

## C12.40: complete signed Menon ladder covariance

Previous turn and this attempt made **no mathematical frontier progress**. This attempt retained the mixed terms between the full harmonic Ramare ladder blocks instead of converting the source into target counts or separate block norms. The hard target remains a collective source estimate with support errors, unrepresented coefficients and all off-block covariances retained.

Current corpus checks: `GrowingReciprocalMarkerMenonRate` is a schedule calculation, not itself a mean-square producer. `MenonHarmonicFullLadderError` handles the full-range support error. `MenonHarmonicRamareLadderWeighted` and `MenonHarmonicRamareLadderLevelMoment` already implement harmonic-mass splitting and unconditional level/moment bounds. These results are retained as existing work, not relabeled as a half-power source estimate. No new bound has yet been obtained.

For a covered squarefree integer n, write `c_j(n)=card(P_j intersect primeFactors(n))/card(P intersect primeFactors(n))`, where the P_j partition the designated prime set P. Keeping the literal moving cofactor support gives block j the coefficient `mu(n)*c_j(n)/n`. The c_j are nonnegative and sum to one. Consequently the full sum over block pairs at the same integer contributes `mu(n)^2/n^2`, not a reduced diagonal; for unequal n,m the total block-pair weight is again one. Labels attached to the same physical integer are coherent. This paper expansion was not treated as orthogonality or as a new theorem.

The second corpus search found the stronger existing exact prime-label calculation in `Sieve/RouteERamareIntegerIncidence` and `Sieve/RouteERamareTernaryAntiscaleCapstone`. The latter already splits the unweighted prime off-diagonal into the positive same-integer collision `2*W*sum_n(1-1/omega_P(n))` and the distinct-integer signed sum, with incidence multiplier `1-card(P(n) intersect P(m))/(omega_P(n)*omega_P(m))` and the complete Mellin pair kernel. Its shared-incidence part is exactly the prime-block diagonal. Thus the attempted recombination does not advance the frontier even at the identity level. These unweighted statements were not silently substituted for a harmonic or critical-weight estimate.

Second pass attempted prime averaging before the cofactor sum. For a fixed cofactor and one literal prime interval `(L,U]`, the paper Stieltjes formula uses `A(t)=t^(-1)*exp(2*pi*i*w*log(t))/log(t)` and `E(t)=theta(t)-t`. The prime polynomial differs from its continuous prime integral by `A(U)*E(U)-A(L)*E(L)-integral_(L..U) A'(t)*E(t) dt`. Summing these errors retains the signed cofactor weight and the moving endpoints L and U. The checked `RouteETerminalPrimeStieltjesTransport` proves this type of endpoint/derivative transport for its stated terminal phase; it does not bound the complete cofactor-weighted error here. No cancellation estimate for that signed error was proved. Absolute power-log error bounds do not supply the required half-power source ceiling.

The checked `MobiusHaarRamareCoprimalityBudget` pays the excluded prime-divisor fibre by at most the number of admitted cofactors. Restricting to small cofactors can therefore make that particular raw correction small, but leaves the complementary source. It does not justify deleting long cofactors or the rough remainder. `Sieve/FullPrimeCofactorBoundary` also retains the previously recorded logarithmic boundary invariant of `mu(n)/(1+omega(n))`; no independent half-power bound on that cofactor was assumed. The rough shell's Brun estimate and ladder support-error estimates remain at their stated normalization, without a coefficientwise comparison being used as a signed quadratic norm comparison.

**Remaining hard problem:** bound the complete distinct-integer signed covariance, including the rough-source cross term and moving prime-error/cofactor interaction. Neither reconstruction of the covariance nor separate block estimates discharged it. No route retired or auxiliary identity, conditional receiver, or no-go module added.

**Outcome:** two deep searches terminal (one partial, one complete), with snapshot/compiler freshness limitations; candidate lemmas and source arguments inspected against relevant source. No new frontier bound, Lean edit/build, numerical experiment, RH proof or falsification. Goal active and unmet.

## C12.41: accumulated physical seam work in the insertion recurrence

Previous turn and this attempt made **no mathematical frontier progress**. Kept the full Route MC source and tested cancellation across adjacent prime-insertion steps, retaining every partition weight, physical dilation interval and endpoint. The scalar breadth-patch coboundary is already exact in `MobiusWoldPatchSeamCoboundary`; `RouteESignedInverseLoadFlux` already identifies the signed normalizer flux with the unresolved source remainder. Repackaging either identity is not a new estimate. The hard target remains an independent bound for the source-specific signed accumulation in `GibbsSignedCovarianceAccumulation`.

Checked the exact recurrence and energy polarization in that module. Its order-gauge theorem already proves that changing insertion order changes the accumulated forcing by exactly the change in baseline. Pairing or averaging orders alone cannot produce an endpoint estimate. The positive dissipation is the squared sum of the two normalized currents, not a strictly positive loss: opposite signs can suppress it. The current cofinal-parity card records the all-clock antiscale obstruction for 0<r<1, so no uniform all-clock energy bound was assumed.

The distinct paper attempt retained a moving lower physical cutoff. With `Q_S(x)=J_S(x)^2/Z_S(x)`, put `E_r(S,a)=integral_(a..infinity) x^(r-1)*Q_S(x) dx`, and let `D_r(S,p,a)` be the integral of the existing nonnegative same-sign dissipation over the same interval. The checked pointwise polarization gives, by the substitution u=p*x,

`E_r(S union {p},a)+D_r(S,p,a)=E_r(S,a)+p^(-r)*E_r(S,p*a)`.

For decreasing a_j and S_j=S_(j-1) union {p_j}, this retains the exact new-strip term

`C_j=integral_(a_j..a_(j-1)) x^(r-1)*Q_(S_j)(x) dx >= 0`,

and hence `E_r(S_j,a_j)=E_r(S_(j-1),a_(j-1))+p_j^(-r)*E_r(S_(j-1),p_j*a_(j-1))-D_r(S_(j-1),p_j,a_(j-1))+C_j`. The C_j cannot be deleted when telescoping. These formulas are paper diagnostics from the existing recurrence, not newly audited Lean results.

For literal distinct primes, the elementary positive envelope is `Q_S(x)<=Z_S(x)<=1/(exp(x)-1)`. The existing dissipation formula also gives `D_(S,p)(x)<=4*Z_S(p*x)`, since both normalized currents have absolute value at most one. On the paper schedule `a_j=3*log(p_j)/p_j` after the finite initial range, the shifted lower endpoint `p_j*a_(j-1)` is at least `3*log(p_(j-1))`. Thus for each fixed r>0 the positive shifted-energy terms and the nonnegative dissipations both have summable exponential upper envelopes. No prime-gap estimate is needed for this conclusion: `p_j^(-r)<=1`, the preceding primes are distinct integers, and a polynomial factor in the shifted endpoint is absorbed by its exponential decay. This pays only the late prime insertions, not the new strips C_j.

The same schedule is suitable for absolute finite/infinite-source tail removal near the lower endpoint, but this does not make C_j small. The raw envelope for their sum integrates x^(r-2) near zero, which fails to supply a finite ceiling when 0<r<=1. This is a failure of that upper estimate, not a lower bound on actual strip energy. The source-specific sum of the C_j remains uncontrolled. Choosing a fixed `a_j*p_j` instead would keep insertion work active, but the elementary omitted-integer tail would then retain linear source scale; its signed control would be another missing estimate, not a free change of schedule.

**Remaining hard problem:** a source estimate for the accumulated moving physical-strip energy (or the complete signed covariance directly), with the finite/infinite-source seam retained. The insertion identity, order invariance, and positive dissipation have not supplied it. No route retired and no auxiliary receiver, identity or no-go module added.

**Outcome:** two research searches terminal (one complete, one partial), with reported snapshot/pending coverage and compiler freshness limitations. Candidate lemmas and source arguments inspected. No new frontier bound, Lean edit/build, numerical experiment, RH proof or falsification. Goal active and unmet.

## C12.42: source differential energy and dilation virial

Previous turn and this attempt made **no mathematical frontier progress**. Attacked the physical-strip energy using the literal Mobius--Laplace source and its exact Lambert dilation identity. Tested a source-specific coercive bound after differentiation and integration by parts, retaining compact positive integration endpoints and every signed dilation term. `CCMUnitRieszMobiusCausalVirial` is an existing finite logarithmic-moment identity; `MobiusRenewalEnergySign` gives a negative complete renewal pairing but explicitly no source-energy upper bound. Neither is a new producer or a substitute for the missing estimate.

Let F(x) be the real literal infinite source. On a compact interval 0<a<b, the geometric coefficient envelope permits differentiation of the Lambert sum and termwise integration: derivatives are dominated by the convergent sum of `k*n*exp(-k*n*a)`. Thus the following paper calculation never assumes energy integrability at zero. Write

`E=integral_a^b x^(r-1)*F(x)^2 dx`, `B=b^r*F(b)^2-a^r*F(a)^2`,

`A0=integral_a^b x^(r-1)*exp(-x)*F(x) dx`, `A1=integral_a^b x^r*exp(-x)*F(x) dx`,

`K=sum_(k>=2) integral_a^b x^(r-1)*F(x)*F(k*x) dx`,

`T=sum_(k>=2) integral_a^b x^r*F(x)*k*F'(k*x) dx`.

The checked exact Lambert law gives `K=A0-E`. Its derivative and integration by parts give `T=(r/2)*E-A1-B/2`. Consequently centering the dilation derivative at r/2 yields

`T+(r/2)*K=(r/2)*A0-A1-B/2`.

The energy cancels from this centered identity. Keeping it uncentered leaves exactly the unknown T with coefficient r/2, not an independently bounded work term. No estimate improving that coefficient while controlling B was obtained. A compactly supported smooth cutoff removes B only by replacing it with `integral chi'(x)*x^r*F(x)^2`; the lower transition retains the same uncontrolled physical-strip energy from C12.41. No zero-endpoint or vanishing-boundary assumption was inserted. These are paper diagnostics, not new Lean theorems.

Second pass retained a finite coefficient source `F_N`. The corpus's `MoebiusMollifiedZetaField` and `TruncatedMoebiusResidual` identify the literal truncated divisor coefficient and its vanishing head. In the Laplace variable the paper identity is

`sum_(k>=1) F_N(k*x)=exp(-x)+R_N(x)`,

`R_N(x)=sum_(n>N) c_N(n)*exp(-n*x)`, `c_N(n)=sum_(d|n,d<=N) mu(d)`.

The corresponding derivative work retains `integral x^r*F_N(x)*R_N'(x) dx`; centering also retains `(r/2)*integral x^(r-1)*F_N(x)*R_N(x) dx`. Support above N does not make these signed mixed terms small near x of order 1/N. In particular, for N<n<=2N, every proper divisor of n is <=N, so `c_N(n)=-mu(n)`. The first tail is the negative next literal Mobius block, and its pairing with the prefix is still part of the original cancellation problem. No sign or cutoff-uniform upper estimate for the combined tail work was proved. This is not a new vanishing-head result; C12.26 already records that head cancellation alone is insufficient.

The retrieved `MobiusIntegerCuspConfinement` was also checked: it pays the region below (N+1)^(-2), proves convergence above each fixed positive delta, and localizes the unresolved energy to the intervening moving region. It does not bound that region. Ordinary-line multiplier derivative estimates from `MobiusFixedCurrentVonMangoldt` were not transferred to the critical physical energy.

**Remaining hard problem:** source-specific control of the complete finite tail/derivative covariance, or an independent estimate of the moving physical-strip energy. Differentiation, centering and localization have not supplied coercivity. No route retired or auxiliary identity, receiver or no-go module added.

**Outcome:** two deep searches terminal with partial results and snapshot/compiler freshness limitations; candidate lemmas and source arguments inspected. No frontier bound, Lean edit/build, numerical experiment, RH proof or falsification. Goal active and unmet.

## C12.43: collective one-prime removal and retained source covariance

Previous turn and this attempt made **no mathematical frontier progress**. Attacked the actual signed Gamma--Hankel / prefix--tail covariance through the corpus's exact single-prime removal laws. The target remained the subpower ceiling for the complete literal Hilbert source, with every finite-cutoff seam retained. Entrywise positivity of the one-prime tent is not positivity or an upper bound for its Mobius-weighted quadratic form. `MobiusMertensPrimeWindowReversalEnergyUniversalityLaw` already identifies every prime-window palindromic energy with the original energy; changing its prime label supplies no saving.

Checked the complete `MobiusMertensPrimeRemovalTentLaw`: its flattened double sum retains both prime-free Mobius coefficients and the exact window kernel. Its universal two-prime sign wall prevents an argument that iterates entrywise kernel positivity. The actual one-prime finite-source calculation is as follows. Put `a_p(n)=mu(n)*1_(p does not divide n)`, `L=floor(N/p)`, `u(x)=sum_(n<=L) a_p(n)*exp(-n*x)` and `v(x)=sum_(L<n<=N) a_p(n)*exp(-n*x)`. With `D_p u(x)=u(p*x)`, the literal source is exactly `F_N=(I-D_p)u+v`. All sums are finite, and the Hilbert inner product is the integral over x>0. Thus

`||F_N||^2=||v||^2+(1+1/p)*||u||^2-2*<u,D_p u>+2*<v,(I-D_p)u>`.

The retained prefix--tail term has the paper expression

`<v,(I-D_p)u>=sum_(L<r<=N,s<=L) a_p(r)*a_p(s)*(p-1)*s/((r+s)*(r+p*s))`.

Its kernel is positive; its arithmetic coefficients are signed. Taking absolute values or using Hilbert-space Cauchy--Schwarz does not give the missing half-power saving. Nor do the equal prime-window representations give orthogonality between prime labels. No source-specific collective upper estimate for these cross terms was proved. These formulas are diagnostics from the checked source law, not new formalized results.

Second pass used the stronger existing physical correlation producer in `MobiusDivisorPrescribedPrimeSelfCorrelation`, rather than assuming a sign for that term. Write `K_P(Y)=mobiusDivisorDilationMean P Y`, `rho_P=squarefreeDensity*product_(p in P) p/(p+1)`, `E_P=rho_P*K_P(1)` and `C_P(Y)=rho_P*K_P(Y)/Y`. The exact density-weighted renewal law at a fresh prime p gives

`E_(P+p)=E_P-2*sqrt(p)/(p+1)*C_P(p)`.

The corpus's uniform positive gap is `K_P(1)+K_P(Y)/Y>=c`, with one c>0. Substituting it yields only

`E_(P+p)<=[1+2*sqrt(p)/(p+1)]*E_P-2*sqrt(p)/(p+1)*rho_P*c`.

This pays an absolute source margin; it does not supply a contraction proportional to the whole energy. The corresponding self-correlation drop is already proved in Lean, but does not bound the release correlation at every subsequent distinct prime. No stronger source-dependent coercivity was established here.

Checked the direct prescribed-debt reduction proof, including its retained constants. For a fixed core and prescribed missing prime, a sufficiently distant pair with its ratio in a core-dependent interval gives a relative limiting-energy payment at least `c_P/p`. Its onset is `(C_P/c_P+1)^2` in the proof, and both the admissible interval and error constants change after insertion. Iterating existence of arbitrarily distant pairs does not ensure a divergent sum of these payments, a common physical cutoff, or an absolute energy ceiling. No uniformity was inferred from a fixed-core theorem. `MobiusDivisorCurrentClockPayment` supplies an actual current-cutoff payment only for its admitted two-coordinate source; `MobiusDivisorExhaustiveClockCheckpoints` controls the chosen current checkpoints, explicitly not the earlier cutoffs after completion. Neither discharges the complete-source covariance.

**Remaining hard problem:** an independent bound for the complete signed removal covariance, with changing-core correlations and the physical cutoff controlled together. The exact window, positive moment and local debt payment have not solved that estimate. No route retired or auxiliary receiver, identity, numerical-bound or no-go module added.

**Outcome:** two deep searches terminal with partial results, background-indexer/snapshot coverage and pending/stale compiler metadata; candidate lemmas and source arguments inspected against source. No frontier bound, Lean edit/build, numerical experiment, RH proof or falsification. Goal active and unmet.


## C12.44: coupled finite-clock prime correlations

Previous turn and this attempt made **no mathematical frontier progress**. Kept the original finite logarithmic cutoff in the joint prime-delay law and attempted a collective estimate for the complete signed source. The desired ingredient was cumulative control of the interacting prime correlations, not positivity at each lag: `MobiusDivisorCriticalFiniteCorrelationSign` already proves a negative complete-source finite pairing. All old/new cutoff terms in `MobiusDivisorCriticalClockProductTransport` remained in the argument.

First paper test: let h be the literal processed critical clock head, zero at nonpositive times. For distinct fresh primes p<q put `a=log p`, `b=log q`, `alpha=p^(-1/2)`, `beta=q^(-1/2)`, and `S_a h(t)=h(t-a)`. The checked source law gives the double insertion `(I-alpha*S_a)(I-beta*S_b)h`. Put `E_T(h)=integral_0^T h(t)^2 dt` and `C_h(l,U)=integral_0^U h(t+l)*h(t) dt`, with C=0 when U<=0. The complete mixed second difference at the SAME upper time T is

`Delta_p Delta_q E_T = 2*alpha*beta*[C_h(b-a,T-b)+C_h(a+b,T-a-b)]`

`  -2*alpha^2*beta*C_h(b,T-a-b)-2*alpha*beta^2*C_h(a,T-a-b)`

`  +alpha^2*beta^2*E_(T-a-b)(h)`.

The zero convention for E at a nonpositive cutoff is also retained. This follows by expanding the four literal shifted heads and changing variables in each finite integral; no improper critical-energy admission is used. It is a paper diagnostic, not a new audited Lean theorem. The sum-lag, difference-lag and both singly copied correlations have different finite endpoints. The density cancellation theorem does not remove them.

In the causal late sector `a+b>=T`, the double-shifted head vanishes throughout the original interval and the formula reduces to `2*alpha*beta*C_h(b-a,T-b)`. This is an actual short-source correlation, not an automatically favourable sign. The corpus's `MobiusDivisorCofinalNegativeMixedCurvature` already supplies negative mixed changes for its stated selection-energy source; it does not supply a bound for the full block or identify selection energy with the clock integral above. `MobiusDivisorLateBlockMixedTransport` likewise retains the exact signed late-block mass and pre-block double fibre. Neither statement was substituted for an estimate of the coupled clock source.

Second test summed a whole block rather than selecting individually favourable pairs. If L is a finite set of fresh primes with `log p+log q>=T` for every distinct p,q in L, causality gives the exact source `h_L=h-V`, where `V=sum_(p in L) p^(-1/2)*S_(log p)h`. Hence

`E_T(h_L)=E_T(h)-2*<h,V>_T+||V||_T^2`.

The complete pair contribution is the Gram norm of V. Its signed off-diagonal sum is bounded below by minus its copied diagonal, since `||V||_T^2>=0`; collecting negative pair curvatures does not make that full norm a negative payment. An upper bound still requires control of the actual old-head/block pairing together with the block norm. Optimizing freely chosen prime weights would change the literal source, whose weights here are fixed. No such replacement was made.

For a core covering the primes below the square-root cutoff, this whole-block residual returns to the already recorded smooth-head/complete-child source in C12.3. The first/second prime differences and the local inward-payment results therefore have not proved its missing signed excess estimate. `MobiusDivisorArityHeadTwoChannelDissipation` requires an oriented nonnegative field, established there only for its stated sparse blocks; this condition was not assumed for the complete changing core. The admitted boundary autocorrelation and its analytic continuation were also kept separate from exponential admission of the critical clock energy.

**Remaining hard problem:** control `||V||_T^2-2*<h,V>_T` jointly with the literal moving smooth head, or prove the corresponding complete finite-source covariance bound directly. Separate pair curvature, diagonal payment, and boundary-transform continuation have not done this. No route retired or auxiliary identity, receiver or no-go module added.

**Outcome:** one deep search terminal and complete as a retrieval request; refresh remained pending behind the background indexer, and compiler coverage still contained pending/stale entries. Candidate lemmas and source arguments were inspected against source. No frontier bound, Lean edit/build, numerical experiment, RH proof or falsification. Goal active and unmet.


## C12.45: exhaustive residual after cofactor-layer extraction

**In progress.** Previous turn made no mathematical frontier progress. Changed from prime-correlation identities to the corpus's literal moment-matched extraction. Target: a complete-source bound after covering the unused composite atoms, with disjoint ownership and all residual signed moments retained. Checked `MobiusCofactorLayerExtraction` and `MobiusCofactorLayerCofinal`: they select equal numbers of actual signs, with a summable Gamma-norm majorant for fixed admitted order and cofactor exponent; the cofinal theorem explicitly leaves the residual source. The proposed extension is an exhaustion using greatest-prime cofactor ownership, not a repeated application to an arbitrary depleted source. No residual bound or closure-under-depletion theorem is assumed.

**Outcome: no mathematical frontier progress.** Tested balanced depletion, largest-prime ownership, fractional coverage, unequal-count weighted packets, and cross-scale transfer. None produced a complete-source estimate. The following are paper diagnostics of the failed attempts, not new Lean theorems.

1. Removing disjoint equal-cardinality literal-sign packets from a finite shell preserves its signed count. Hence the number of unused squarefree atoms is at least the absolute original shell charge. Positive-density extraction does not prove a half-power residual-cardinality bound. The existing window theorem concerns original candidate pools; it does not give the required supply in every window after depletion. Greatest-prime ownership prevents duplicates but does not establish that supply. Fixed-order extraction also does not provide uniform constants for order or cofactor exponent growing with the shell.
2. For integer R >= 1, let Pi_q(x) count odd primes p <= x larger than every prime factor of the odd squarefree integer q. Unique largest-odd-prime ownership gives the complete finite shell charge

   `M(4R)-M(2R) = sum_(q odd squarefree, 1<=q<=4R) mu(q) * (2 Pi_q(2R/q)-Pi_q(R/q)-Pi_q(4R/q))`.

   The two branches are n=2qp and n=qp, of signs mu(q) and -mu(q). Both moving endpoints and the largest-prime mask are retained. For any fixed q, the bracket is asymptotic to `-R/(q log R)` by the current corpus's prime-counting PNT; already q=1 prevents a separate half-power bound for each cofactor. No cancellation bound across the complete q sum was proved. This does not assert that pooled rounding preserves each individual cofactor's charge.
3. Averaging balanced extractions with inclusion probabilities pi_n gives `sum mu(n) pi_n=0`. For a common positive inclusion target lambda, `lambda * |sum mu(n)| <= sum |pi_n-lambda|`. Thus a sufficiently uniform inclusion law needs an arithmetic discrepancy estimate; positive coverage alone does not supply it. No such law was constructed.
4. To avoid equal-count conservation, tested Taylor expansion of the exponential in the literal atom `n^2 exp(-nt)`, keeping n^2 in the coefficient. Its leading moment is `sum mu(n)n^2`, followed by `sum mu(n)n^2(n-X)^j`. Unequal-count packets move the obligation to these actual weighted signed moments. For fractional packets cancelling the leading weighted moment, common inclusion requires control of `sum n^2 |pi_n-lambda|`. Neither original prime-window supply nor ordered rounding proves this complete-source control. `MobiusWeightedMertensVector` gives centered decay above absolute convergence; `MobiusPowerSumBoundaryLaplace` concerns a positive power-sum source. Neither was treated as the missing moment estimate.
5. Borrowing opposite signs from adjacent scales retains cumulative flux and the final unmatched endpoint. The corpus already gives the exact frozen-prefix Abel integral, the comparable/separated mixed-Gram signs, and the strictly positive logarithmic Fourier multiplier. Absolute transport cost is already an RH-threshold receiver. No estimate of the actual cross-scale flux or complete signed Gram was derived; local negative Gram entries were not substituted for such an estimate.

**Remaining hard problem:** prove cancellation across the complete masked largest-prime cofactor sum, or otherwise bound the literal residual source after extraction. The next attack will retain the full cofactor sum and its moving endpoints rather than repeat selection or rounding on depleted pools. No route retired, auxiliary receiver, identity, or no-go module added.

**Audit:** four research requests terminated: initial residual extraction complete, largest-prime, unequal-packet and cross-scale requests partial. Candidate lemmas and source arguments inspected; refresh pending behind the background indexer and compiler coverage pending/stale. No Lean edit/build, numerical experiment, RH proof or falsification. Goal active and unmet.

## C12.46: joint largest-prime cofactor cancellation

**In progress.** Previous turn made no mathematical frontier progress. Revalidated C12.45's complete shell identity and its fixed-cofactor obstruction. Target is the signed sum over all cofactor masks, with moving prime-count endpoints retained. First attempt: split at the square-root seam, combine the resulting complete Mertens children with the literal friable head, and test whether the exact largest-prime recurrence gives a contractive bound for their joint error. The arithmetic head is not identified with an abstract delay profile, and no separate half-power bound for each prime-count term is assumed.

**Outcome: no mathematical frontier progress.** The square-root split immediately returned to C12.2/C12.3's unproved smooth-head/child excess. Did not add another split or induction receiver. The next tests kept the complete prime-count error and tried joint density subtraction, harmonic Abel control, and discrete reciprocal prime cells.

Let `H(x)=integral_(2..x) dt/log t` for x>=2, zero below 2; let `E(x)=pi_odd(x)-H(x)`. For odd squarefree q set `L_q=max(2,Pplus(q))`, and define `H_q(x)` and `E_q(x)` to be the differences `H(x)-H(L_q)` and `E(x)-E(L_q)` when x>L_q, zero otherwise. Then `Pi_q=H_q+E_q` exactly. The shell charge of C12.45 therefore splits into the two full signed sums of `2 H_q(2R/q)-H_q(R/q)-H_q(4R/q)` and `2 E_q(2R/q)-E_q(R/q)-E_q(4R/q)`. No lower cutoff, long cofactor, or density term was discarded. The current terminal Stieltjes theorem retains endpoint and derivative Chebyshev errors; its unconditional subexponential PNT envelope does not prove a half-power bound for this joint expression. The friable Taylor coefficient and explicit delay profiles do not prove an arithmetic remainder estimate.

For q<=sqrt R and large R the largest-prime mask is inactive and its lower endpoint cancels. Put

`D_R(u)=2 E(2R/u)-E(R/u)-E(4R/u)`, `w_R(u)=u D_R(u)`.

The checked `abs_coprimeMobiusHarmonic_le_two`, at modulus 2, bounds `A(k)=sum_(odd n<=k) mu(n)/n` uniformly. Finite Abel summation gives

`sum_(odd q<=Q) mu(q) D_R(q) = A(Q) w_R(Q) - sum_(1<=k<Q) A(k) (w_R(k+1)-w_R(k))`.

Tested control by continuous total variation of w_R on [1,sqrt R]. At u=cR/p, c in {1,2,4}, an odd prime p gives jump `-a_c*c*R/p`, with `a_1=-1,a_2=2,a_4=-1`. Distinct c cannot share a jump position: a power-of-two ratio cannot be a ratio of distinct odd primes. The absolute jump mass is bounded below by a positive constant times R, using the corpus's square-root prime-window mass and partial summation. Thus this particular continuous-variation majorant is too large. **This is not a lower bound for the discrete variation of the sampled values w_R(k), and not growth of the signed source.** No new no-go theorem or route retirement is claimed.

Retaining the discrete difference instead leaves the prime counts in the actual cells `(cR/(k+1), cR/k]`, minus their H-masses, paired with A(k). The cells for each c partition their own prime window; overlaps between c and the signed cofactor factors remain. No cancellation estimate for this discrete pairing was obtained. Merely making the prime-error feedback quadratic does not improve a power exponent under dilation convolution: on log scale two factors `exp(beta*v)` and `exp(beta*(T-v))` yield `T*exp(beta*T)`, not a smaller exponential rate. This tests the proposed bootstrap, without identifying a model profile with the arithmetic error.

The reciprocal-phase corpus check retains distinct scopes. `StadlmannReciprocalPhaseApplications` sums complete unit residue systems at one modulus. `ReciprocalPhaseStability` controls phase derivatives, not Mobius coefficients. The Farey source large sieve retains its length-plus-modulus-squared cost, and the physical Kloosterman carrier retains its actual Kloosterman kernel. No exact completion with controlled remainder was constructed for the individual reciprocal prime samples above; their zero-frequency discrepancy was not assumed to vanish after density subtraction.

**Next hard attack:** retain and estimate the signed discrete prime-cell pairing, jointly with the density and masked long-cofactor contributions. The continuous-variation failure is not a reason to discard that discrete interaction. No complete-source bound, Lean edit/build, numerical experiment, RH proof or falsification. Three searches terminal (two partial, one complete); candidate lemmas/source arguments inspected, background refresh pending and compiler snapshot freshness limited. Goal active and unmet.

## C12.47: discrete prime-cell covariance

**In progress.** Previous turn made no mathematical frontier progress. Revalidated C12.46. Target: the actual discrete Abel pairing of odd Mobius harmonic prefixes with prime-count errors on `(cR/(k+1),cR/k]`, c=1,2,4, together with the density and long masked-cofactor terms. The continuous-variation diagnosis does not establish a discrete-variation lower bound. First test keeps the mixed prime-cell terms in a second-moment estimate; no independent random-prime model, complete-residue replacement, or separate half-power estimate is assumed.

**Outcome: no mathematical frontier progress.** Tested the exact physical overlap of reciprocal cells and then prime-power inversion before taking norms. Neither yielded the required signed upper bound.

For a prime p the cell condition `cR/(k+1)<p<=cR/k` is exactly `kp/c<=R<(k+1)p/c`. Hence averaging a product of two raw cell indicators over a finite R-window gives the length of the intersection of that window with `[kp/c,(k+1)p/c)` and `[lq/d,(l+1)q/d)`. The full squared discrepancy retains this prime-pair overlap, both prime/density cross terms and the density square, all weighted by the actual harmonic prefixes. Disjoint k-cells for one fixed p,c do not eliminate the p!=q terms or the mixed c,d scales. No upper bound for their complete signed sum was derived.

The checked `EulerDeletionUpperHalfPrimePhaseCovariance` gives zero covariance over a complete p*q period for its centered remainder phases and a p*q incomplete-prefix budget; these are not the raw prime-count cells. Its beta-packet extension keeps geometric suppression. `EulerDeletionMobiusVarianceHarmonicBound` is a complete-period residue-source estimate. `Sieve/PrimeWindowMeanSquare` counts prime divisors of integers, whereas the current cell counts prime values in a moving reciprocal interval. `Sieve/PrimeSieveAffineMeanSquare` retains coefficient length weights and sieve errors. No identification that transfers any of these bounds to the current centered prime-cell pairing was proved.

Second test used the literal prime-count coefficient jet `mu(n)*omega(n)`. Current `EulerDeletionPrimeCountEndpointTransfer` already proves its complete vector-valued prime-power convolution and harmonic identity. Taking its norm still retains every mixed prime-power packet term. The coefficient-prefix energy estimate explicitly requires control of the same signed coefficient prefixes and full tail; it was not used as an independent cancellation producer.

Checked the related logarithmic renewal in its original physical carrier:

`logSource N = -dilationPackets N - forcing N`,

with forcing coefficients `Lambda(q)*m(floor(N/q))`. `EulerDeletionLogPrimeForcing.linear_energy_bounds` proves that this correction has squared norm comparable to N. Therefore the proposed small-remainder step fails for that literal correction. Its complete squared residual is

`||dilationPackets||^2 + 2 Re<dilationPackets,forcing> + ||forcing||^2`.

No signed bound for the cross term and packet norm together was obtained. This renewal carrier was not identified with the reciprocal prime-cell expression without a proved transfer. The prime-count endpoint variance is a lower bound; it does not upper-bound the undamped source. The corpus's actual damping amplification also prevents assuming a uniform contraction along the prime-count damping path.

**Remaining hard problem:** estimate the complete signed prime/cofactor interaction, including cell means, moving endpoints, and the physical tail. Next attempt will keep the compulsory harmonic correction inside the joint packet pairing and seek arithmetic cancellation there; another periodic covariance bound or inversion identity would not discharge it. Two searches terminal and complete as retrieval requests, with pending background refresh and stale/pending compiler coverage. Candidate lemmas and source arguments inspected. No new theorem, Lean edit/build, numerical experiment, RH proof or falsification. Goal active and unmet.

## C12.48: full compensated logarithmic pairing

**In progress.** Previous turn made no mathematical frontier progress. Revalidated C12.47 and the exact physical log-renewal target. Test whether the joint dilation/correction pairing gives a contraction for the complete source at smaller cutoffs. The correction's linear squared energy is retained; no separate small-error estimate, sign of a mixed term, or identification with the earlier reciprocal-cell carrier is assumed.

**Outcome: no mathematical frontier progress.** Retaining the compulsory correction does not itself give a smaller-cutoff contraction. Tested a joint centering in the actual physical cells, rather than bounding the forcing separately. Write `c_N=sum_(d<=N) mu(d) log(d)/d`. The checked initial-cell identity gives `k*c_N+psi(k)`; its squared physical contribution is `w_k*(c_N+psi(k)/k)^2`, with `w_k=k/(k+1)`. With `W=sum_(k=1..N) w_k` and `a_N=W^(-1)*sum w_k*psi(k)/k`, the initial-cell energy is exactly

`W*(c_N+a_N)^2 + V_N`, where `V_N=sum w_k*(psi(k)/k-a_N)^2`.

This is a paper diagnostic, not a new audited theorem. The disjoint physical tail is nonnegative in the full squared norm and cannot cancel this initial variance. Its source numerator still includes every omitted divisor term from `physical_log_moebius_cell_eq_chebyshev_add_divisor_tail`. The existing Fermi/Nyman variance theorem has its own logarithmic coefficients and continuous weighting; no equality of its carrier with this one is assumed.

Expanded the actual finite variance before estimating. For `1<=a,b<=N`, put

`A_a=sum_(k=a..N) 1/(k+1)`,

`K_N(a,b)=1/max(a,b)-1/(N+1)-A_a*A_b/W`.

Finite interchange gives `V_N=sum_(a,b<=N) Lambda(a)*Lambda(b)*K_N(a,b)`. The diagonal is bounded by `sum_(a<=N) (log a)^2/a`; the required upper estimate is therefore in the complete centered off-diagonal prime-power covariance. Positivity of Lambda and positive semidefiniteness of the centered Gram do not upper-bound that covariance by its diagonal. No such bound, nor a bound on the normalization component, full tail, or Abel-history interaction, was proved.

Checked the potential chronological projection shortcut at source level. `EulerDeletionNestedProjectionCovariance` retains the entire signed reverse tail inside each squared history layer and the entire earlier/later covariance in the drift increment. `EulerDeletionChildFibreContrast` removes the *local innovation* at a composite terminal stage; the literal signed physical cells remain. Hence neither prime-only local corrections nor orthogonality between history layers eliminates the cross terms within those layers. No comparison from that carrier to the required prime-profile upper bound was constructed.

**Next hard attack:** estimate the actual centered off-diagonal prime-power covariance while retaining its normalization and complete-tail obligations. Repeating compensation, variance decomposition, or conditional transfer would not advance MC. No route retired, Lean module added, or frontier result claimed. Two deep searches terminated with `partial=false`; the lexical variance search returned three declarations. Background refresh and compiler freshness limits retained; candidates/source arguments inspected. No Lean edit/build, numerical experiment, RH proof or falsification. Goal active and unmet.

## C12.49: source-specific divisor coercivity for prime covariance

**In progress.** Previous turn made no mathematical frontier progress; C12.48 revalidated. Attack the actual centered prime-power covariance through the exact divisor relation for Lambda. Seek a source-specific energy estimate that retains the density subtraction, rather than invoke the unavailable absolute-weight inverse theorem. The initial variance is only one required component: normalization, Abel history and complete physical tail remain obligations. No arbitrary-source inverse bound or favorable mixed-term sign is assumed.

**Outcome: no mathematical frontier progress.** Three source-specific estimates were attempted; none produced the required upper bound.

1. Put `f=psiDefect`, `G=floorSummatory f`. The checked corpus proves `|G(N)|<=24 sqrt N`. Squaring before Mobius inversion retains

   `Q_N=sum_(d<=N) mu(d) G(floor(N/d))^2 = f(N)^2 + C_N`,

   where `C_N` is the complete off-diagonal coprime sum of `f(floor(N/a))*f(floor(N/b))`. The existing coprime diagonalization supplies precisely this mechanism. Its available absolute bound is `|Q_N| << N(1+log N)`. It does not lower-bound `C_N`; such a lower bound at `N^(1+epsilon)` for every positive epsilon would be the missing source-specific step. `CCMPrimeDeficitCoprimeBalance` likewise bounds energy **plus** signed cross work. No cross sign, inverse coercivity, or transfer from the square-root transform bound was established. The positive monotone density inversion found by search has n^(-2) weights and a different generalized-prime density; it was not substituted for this inverse.

2. Tested the exact prime-divisor representation of `log n` through its second moment under the uniform measure on `1..N`. Its centered kernel is

   `floor(N/lcm(a,b))/N - floor(N/a)*floor(N/b)/N^2`.

   Same-prime-power terms and all floor errors remain. This is different from C12.48's maximum-index kernel `K_N(a,b)`. Current `Sieve/TuranKubilius` bounds distinct prime-divisibility covariances and retains the accumulated pair-count error; `JointTuranKubilius` retains the corresponding lcm terms for products of counts. No comparison to the actual centered prime-count profile was proved. Neither a change of measure nor prime-divisibility independence was assumed.

3. Kept the actual stationary action as a saddle problem, rather than require its signed Hessian to be positive. For `X=exp T`, split indices at `U=floor(sqrt X)`, write `F=ccmPrimeDeficitDilationSource`, `H=ccmPrimeDeficitDivisorSource`, `g_i=F(T-log i)`, and `H_ij=H(T-log(i*j))`, with zero entries when `i*j>X`. The long/long block vanishes. Writing the blocks as `[[A,B],[B^t,0]]` and the actual Mobius vector as `(x,y)`, source inversion gives `Ax+By=g_short` and `B^t x=g_long`. The action is `2<x,g_short>-<x,Ax>`; changing the long extension cannot change it. These constraints do not by themselves bound that value.

   The naive full-vector coercivity of `B^t` already fails at `X=U^2`: its short coordinate `a=U` has no long partner, hence is in its kernel. This is not an obstruction to an action estimate: `H(0)=0`, and the exact inversion at `T-log U` makes the actual action unchanged along that coordinate. A useful proof must estimate the action after retaining this cancellation, not infer an upper bound from stationarity or invert `B^t` in the unmodified Euclidean norm. No such estimate was derived. These are paper diagnostics, not new audited theorems or a route retirement.

**Next hard attack:** the literal constrained short action, including its mixed block and the source's elementary main terms. Seek a uniform half-power bound for its value on the exact arithmetic constraints; do not add another stationarity, null-direction, or conditional-receiver module. Three deep searches terminal with `partial=false`; source statements and candidate/source-argument scopes inspected, background refresh pending and compiler freshness limited. No Lean edit/build, numerical experiment, RH proof or falsification. Goal active and unmet.

## C12.50: reflected bound for the constrained short action

**In progress.** Previous turn made no mathematical frontier progress; C12.49 revalidated. Attack the value of the literal short reconstruction through its exact reflected residual force/count pairing. Retain original endpoints, the mixed short/long constraints, and prime forcing. A null direction of the tail-constraint matrix is not treated as a negative result for the action; no Euclidean coercivity or sign of the reflected pairing is assumed.

**Outcome: no mathematical frontier progress.** The reflection and shift-positivity attempts did not upper-bound the actual source.

In the checked reflected identity write `r_m=mu_{>m}*1` and `b_m=mu_{>m}*log=r_m*Lambda`. The count profile is the cumulative r_m sum; its paired force is `exp(s)*sum_(a<=exp s) r_m(a)/a - sum_(a<=exp s) b_m(a)`. Both sides of the reflection use the original cutoff. For `X=exp T<2(m+1)^2`, whenever both residual factors are active, their arguments lie below `2(m+1)`. Then `r_m(a)=mu(a)` and `b_m(a)=0`. The remaining defect is the literal signed boundary form

`sum_(a,b>m, ab<=X) mu(a)*mu(b)*(X/(ab)-1)`.

This paper observation supplies no new upper bound: the existing shortened-cutoff and boundary-diagonal modules already retain the off-diagonal sum. Taking absolute values gives a boundary cost, not the missing bound for the retained action. Moving the cutoff with the integration variable does not invoke the fixed-cutoff identity without additional terms; those terms were not shown to vanish or bounded. No moving-seam cancellation is assumed.

Next tested positivity in the finite Laplace carrier from the current Hilbert/Laplace corpus. Put `F_N(x)=sum_(n<=N) mu(n) exp(-nx)`, `E_N=integral_(0,infinity) F_N(x)^2 dx`, and `C_N(s)=integral_(0,infinity) F_N(x+s)*F_N(x) dx`. For the shifted logarithmic pairing J_N^+ with coefficients `mu(n)*log(n+1)`, the finite Frullani calculation gives

`J_N^+=integral_(0,infinity) exp(-s)*(E_N-C_N(s))/s ds >= 0`,

because right translation on the half-line is contractive. This is a paper diagnostic, not an added Lean theorem. It gives the wrong direction for the proposed estimate. The unshifted pairing J_N with coefficients `mu(n)*log n` satisfies the exact arithmetic sign `J_N=-W_N`, where W_N pairs F_N with the complete von-Mangoldt-weighted dilation sum. A lower bound on a shifted logarithmic pairing does not give the required lower bound on W_N, equivalently an upper bound on J_N. The correction from log(n+1) to log n was not dropped.

The unshifted finite formula is `J_N=integral (exp(-s)*E_N-C_N(s))/s ds`. Its small-shift cancellation is the next actual arithmetic target; contraction alone does not upper-bound the integral. Current `MobiusRenewalEnergySign` proves a negative pairing with the first-atom remainder, not an energy ceiling. `MobiusLogDivisorParaproduct` is exact finite algebra. Neither was promoted to the missing upper estimate. This additive physical shift carrier is not identified with earlier logarithmic-dilation autocorrelations without proof.

**Next hard attack:** directly bound the complete small-shift correlation deficit for F_N, retaining its coefficient cutoff and the unshifted correction, rather than seek another generic positivity statement. No route retired, auxiliary identity/receiver/no-go module added, or frontier theorem claimed. Both deep searches terminal (first partial, second complete); candidate/source-argument scopes inspected with pending refresh and compiler freshness limitations. One guessed filename was absent; corrected through `rg --files`, with no file created there. No Lean edit/build, numerical experiment, RH proof or falsification. Goal active and unmet.

## C12.51: finite Lambert control of the small-shift deficit

**In progress.** Previous turn made no mathematical frontier progress; C12.50 revalidated. Test the exact Lambert relation against the finite Laplace source's small-shift deficit, retaining the literal coefficient cutoff, omitted divisor tail and dilation/translation commutator. No passage from the infinite Lambert identity to a finite energy estimate, independence assertion, or unproved exchange at the critical boundary is assumed.

**Outcome: no mathematical frontier progress.** The finite Lambert and compensated-image attempts did not bound the complete small-shift correlation deficit. The following are paper diagnostics, not new Lean results.

For `F_N(x)=sum_(n<=N) mu(n) exp(-n*x)`, write `T f(x)=sum_(k>=1) f(k*x)`. At each fixed positive x, absolute regrouping gives

`T F_N(x)=exp(-x)+R_N(x)`,

where `R_N(x)=sum_(j>N) c_N(j) exp(-j*x)` and `c_N(j)=sum_(d|j,d<=N) mu(d)`. On the first omitted interval `N<j<=2N`, `c_N(j)=-mu(j)`. For `D_s f(x)=f(x+s)-exp(-s)*f(x)` and

`K_(N,s)(x)=sum_(k>=1) [F_N(k*x+k*s)-F_N(k*x+s)]`,

the exact relation is `T(D_s F_N)=D_s R_N-K_(N,s)`. Additive shift and integer dilation do not commute. Even for `1<j<=N`, the exponential coefficient of the left side is `sum_(d|j) mu(d) exp(-d*s)`, not zero. Neither omitted-tail nor commutator pairing was bounded or discarded.

Full-half-line energy admission needs a separate correction. With `m_N=sum_(n<=N) mu(n)/n` and `M_N=sum_(n<=N) mu(n)`, the fixed-N expansion is

`T F_N(x)=m_N/x-M_N/2+O_N(x)` as x decreases to zero.

Thus pointwise absolute convergence does not justify an unmodified L2 estimate for the Lambert image. Subtracting `m_N*exp(-x)` from F_N cancels the pole of its Lambert image. The current `abs_coprimeMobiusHarmonic_le_two` at modulus 1 bounds this input correction uniformly, but supplies no subpower bound for the corrected image: its expression retains `m_N/(exp(x)-1)`, and the corresponding squared term integrated from scale `1/N` has size comparable to `N*m_N^2`. This is a cost of an attempted separated-term majorant, not a lower bound on the complete corrected image. No cancellation between that term and the divisor tail is assumed.

Rechecked the already screened `VisibleCoprimeMobiusLaplaceAddition` identity. At fixed x>0 let `v_a=Phi(a*x)`, with Phi the complete Mobius Laplace source. Its divisor rows satisfy `sum_k v_(d*k)=exp(-d*x)`. Consequently the positive squarefree-weighted divisor-square form is bounded by `sum_d exp(-2*d*x)`. This does not itself control `v_1^2`: for arbitrary finite vectors supported on 1 and k distinct primes, values 1 and -1/k make that form equal to 1/k. This diagnostic does not refute coercivity on the actual dilation source. The signed coprime identity follows from the same divisor rows and does not supply the missing source-specific inequality. No general positivity, actual-source counterexample, or energy ceiling is claimed.

**Hard problem still open:** upper-bound the full small-shift source deficit, or equivalently obtain the required lower bound on complete prime renewal work. Further work must estimate an actual signed cross term or construct source-specific coercivity; bounding a positive transformed form without controlling its inverse does not advance MC. No auxiliary identity, conditional receiver or no-go module added. Three searches terminal (two partial deep searches and one focused lexical search); available candidate/source-argument scopes inspected, irrelevant symmetry ingredients rejected, snapshot/compiler freshness limitations retained. No Lean edit/build, numerical experiment, RH proof or falsification. Goal active and unmet.

## C12.52: extend arithmetic pair cancellation beyond divisibility

**In progress.** Previous turn made no mathematical frontier progress; C12.51 revalidated. Start from the current monotone-kernel sign law for actual divisor-comparable Mobius pairs. Attack the remaining complete pair sum, retaining cutoff overflow and the signed weight of every factorization. A sign law for selected pairs is not taken as a bound on the whole source; a generic positive transformed form is not substituted for a source estimate.

**Outcome: no mathematical frontier progress.** Revalidation found that the initial gcd/lcm-transfer idea and weighted fibre inversion were already attempted in C12.37. Repeating their identities is not new progress. The current `MobiusHilbertDivisorBoundary` still leaves the noncomparable excess as an upper-bound premise.

The further paper test retained all three prime states in an lcm fibre: left only, right only and shared, as in `finiteLcmPairCrossFibre_eq_primeChannels`. A useful diagnostic is the complete Hilbert fibre over a support of `k=2*l+1` formal prime labels whose positive scales are asymptotic to R. Assigning each label to at least one endpoint, the only contributions of order `R^(-(l+1))` are:

* disjoint endpoint supports of sizes l and l+1, with coefficient `-2*binom(2*l+1,l)`;
* one shared label and two endpoint supports of size l+1, with coefficient `(2*l+1)*binom(2*l,l)/2`.

All other assignments have an endpoint of size at least l+2 and are of smaller order. Thus the leading coefficient in this formal scale model is

`(2*l+1)*binom(2*l,l)*(1/2-2/(l+1))`.

The shared-label term cannot be dropped: its relative size grows with the number of labels, and the displayed leading coefficient has both signs as l varies. This is a paper scale-model diagnostic, not an audited actual-prime asymptotic, a Lean counterexample, or a bound on the cutoff energy. It prevents relying on an unproved uniform favourable fibre sign. No route is retired on this basis.

The current `MobiusProductFibreVariation` gives a different exact grouping: every nonzero pair with fixed product has its product's Liouville sign, so there is no cancellation within that product fibre. Its absolute variation has a power-size lower bound. This was not treated as divergence of the signed source. `MobiusProductFibrePrimeBalance` supplies an exact two-placement kernel sign depending on the factor ratio; literal prime insertion reverses the arithmetic coefficient and leaves the child diagonal and other channels. Neither statement bounds the complete covariance.

Also checked `EulerDeletionAllShiftLcmPolarity`: its complete-cell collapse requires weights external to the divisor pair. The Hilbert weight depends on both divisor indices. The physical centered-lcm corpus retains that dependence and even has a negative initial-grade witness. No unproved carrier identification or positivity transfer was made.

**Remaining hard attack:** estimate cancellation between complete signed fibres, with the original source cutoff, all overlaps and all prime-factor counts retained. Neither another fibre identity nor a fixed-count sign certificate discharges this. No such upper bound was obtained; no auxiliary identity, receiver or no-go module added. Both deep searches terminal (one complete, one partial); candidate/source-argument scopes checked with background-refresh and compiler-freshness limitations. No Lean edit/build, numerical experiment, RH proof or falsification. Goal active and unmet.

## C12.53: joint prime-factor-count cancellation

**In progress.** Previous turn made no mathematical frontier progress; C12.52 revalidated. Attack the full alternating prime-factor-count sum at the original integer cutoff. Test whether the actual source's Boolean energy and factor-count generating family supply a uniform estimate at full parity. Retain mixed grades and the natural product cutoff; do not infer endpoint control from a subset average, fixed-grade estimate or initial alternating derivatives.

**Turn outcome: no mathematical frontier progress; uniform interpolation estimate remains open.** The current `MobiusDivisorAllOrderBooleanSign` controls initial Boolean jets, not every later core. `MobiusDivisorPrimeDilationBooleanJet` retains a signed background/copy cross term at every order. `UniformPrimeSubsetEnergy` supplies exact subset averages and a variance inequality, not an upper bound at complete elimination. No later-core sign was inferred from the initial-core theorem.

Tested the literal finite polynomial

`P_N(z,x)=sum_(n<=N, squarefree n) z^omega(n)*exp(-n*x)`.

At z=-1 this is F_N(x). Averaging its squared norm over a single phase z on the unit circle preserves every pair with equal factor count, rather than just equal integer index. After integration over x, that average is `sum_k sum_(omega(m)=omega(n)=k) 1/(m+n)` over the same squarefree cutoff. If A_k counts the k-th grade and D is the largest grade, it is at least `sum_k A_k^2/(2*N)`, hence at least `(sum_k A_k)^2/(2*N*(D+1))`. The corpus's squarefree lower density makes this an unsigned mass of order at least N/(D+1). This paper diagnostic does not upper-bound the value at parity and is not a new Lean result.

A distinct attempt uses finite polynomial interpolation. Exactly, for degree at most D,

`P(-1)=sum_(j=0..D) (-1)^j*binom(D+1,j+1)*P(j)`.

The total absolute coefficient cost is `2^(D+1)-1`. For the actual squarefree cutoff, distinct prime factors imply `n>=(D+1)!` for a largest-grade n; the elementary factorial lower bound gives D=o(log N). Thus interpolation's coefficient cost itself is subpower. This is a paper step, not a formalized frontier theorem. The missing input is uniform control of the interpolated positive-integer-parameter family. Applying interpolation to separate main terms plus errors retains both sums; the interpolated main terms were not proved to vanish, and fixed-parameter error estimates do not give a uniform bound when D grows. No such estimate was assumed.

The prospective analytic family at a positive integer parameter j has squarefree coefficients `j^omega(n)` and Euler factors `1+j*p^(-s)` in its absolute-convergence region. A finite linear combination with the displayed interpolation coefficients matches Mobius coefficients through the original cutoff; outside that range the higher-factor-count coefficients remain. Moving a Mellin contour would require bounds on this entire combination and its pole contributions, plus the omitted tail. Neither separate estimates for each parameter nor the formal identity at z=-1 discharges those obligations. No contour shift or boundary convergence was claimed.

Checked the current squarefree convolution-half/Selberg--Delange files: they concern a different coefficient family, retain their named Tauberian premise, and provide no uniform full-parity estimate here. `DampedMobiusSumsZeroFree` gives a necessary thin-positive-partner condition and a zero-free receiver under its explicit power-bound and boundary-limit inputs; it is not a cancellation producer. `Sieve.OmegaSpectralFibre` retains the full weighted polynomial integral in its budget. None was promoted to the missing bound.

**Next hard work:** bound the combined, growing-order interpolation remainder and main contribution for the actual smoothed source, retaining all high-count tails. The original subpower covariance goal is unchanged. No auxiliary identity, receiver or no-go module added; no route retired. Both deep searches terminal with partial results and freshness limitations; candidate/source-argument scopes inspected, unrelated proposals rejected. No Lean edit/build, numerical experiment, RH proof or falsification. Goal active and unmet.

## C12.54: growing-order interpolation tail and pole balance

**In progress.** Previous turn made no mathematical frontier progress; C12.53 revalidated. Keep the same growing-order interpolant and derive its complete higher-factor-count coefficients. Test a bound on the combined smoothed remainder and pole contribution; do not estimate parameter values separately or assume that matching the low coefficients gives convergence across the pole at one.

**Turn outcome: no RH/frontier bound; paper structure clarified.** No new Lean theorem. The following coefficient, real-axis and pole calculations are paper diagnostics for the same interpolant.

Write `a_D(k)=sum_(j=0..D) (-1)^j binom(D+1,j+1) j^k` and `e_D(k)=a_D(k)-(-1)^k`. Its exact exponential generating series is

`sum_k e_D(k) t^k/k! = (-1)^D exp(-t)*(exp(t)-1)^(D+1)`.

For D>=1, the unsigned factor equals `(exp(t)-1)^(D-1)*(exp(t)+exp(-t)-2)`, whose power-series coefficients are nonnegative. Hence `(-1)^D e_D(k)>=0` for all k, and e_D(k)=0 for k<=D. The resulting smoothed even/odd approximants bracket the Mobius source; their extra coefficients begin only beyond the corresponding factor-count threshold. This is a coefficientwise sign, not an upper energy estimate, and was not promoted to one.

For fixed nonnegative integer j, the prospective analytic continuation of the squarefree parameter series is

`F_j(s)=zeta(s)^j*G_j(s)`,
`G_j(s)=prod_p (1+j*p^(-s))*(1-p^(-s))^j`.

The local linear term cancels, so the correction product has its usual fixed-j absolute product convergence for Re(s)>1/2. On real 1/2<sigma<1, each correction factor lies in (0,1], giving 0<G_j(sigma)<=1. The current corpus's `re_riemannZeta_ofReal_neg` supplies the zeta sign. Consequently the combined H_D satisfies the paper bounds

`D+1 <= H_D(sigma) <= ((1+abs(zeta(sigma)))^(D+1)-1)/abs(zeta(sigma))`.

Thus raw H_D cannot converge there to negative 1/zeta(sigma), although this DOES NOT refute an N^epsilon budget when D=o(log N): the displayed upper bound is exp(O_sigma(D)). No vertical bound follows from this real-axis statement, and no maximum-principle premise was assumed.

For D>=1, at s=1 the highest parameter j=D has a nonzero pole of order D, with leading coefficient `(-1)^D G_D(1)`. Lower parameters cannot cancel that order. Thus the Mellin main contribution is not identically zero; its highest logarithmic term is `(-1)^D G_D(1) x^(-1) log(1/x)^(D-1)/(D-1)!`. This does not estimate the full growing-D main polynomial at the moving physical scale. Its cancellation with the remaining contour contribution is still unbounded.

Also tested an alternative using convolution powers after deleting primes <=y. Put `E_y(s)=prod_(p<=y)(1-p^(-s))`, `Z_y=zeta*E_y`, and `Q_D(w)=sum_(j=0..D)(1-w)^j`. The finite polynomial carrier `A_(y,D)=E_y*Q_D(Z_y)` obeys

`zeta*A_(y,D)=1-(1-Z_y)^(D+1)`.

In the absolute-convergence region its residual begins at products of D+1 nontrivial rough factors, so the arithmetic coefficient prefix matches Mobius below that support threshold. This is a different coefficient family from j^omega and was not identified with it. The finite-support mechanism is already present in `CCMPrimeDeficitEulerResolvent`; it supplies no critical contraction. The fixed-modulus mass obstruction in `CCMPrimeDeficitEulerCriticalMass` was not extended without proof to moving y,D. The needed joint estimate for the geometric remainder, all pole terms and physical tail remains open.

**Next hard work:** control the complete vertical/pole balance at growing order, rather than infer it from the real-axis bound or coefficient matching. Pole removal changes the physical kernel and must retain a valid source-recovery estimate; no such transfer is silently assumed. No auxiliary identity, receiver or no-go module added, and no route retired. Both deep searches terminal with partial results/freshness limitations; candidate/source-argument scopes inspected. One JSON read was attempted before its research process exited, failed on the incomplete output, and was retried only after that same handle reported terminal. No Lean edit/build, numerical experiment, RH proof or falsification. Goal active and unmet.

## C12.55: joint vertical interpolation estimate

**In progress.** Route MC's complete-source subpower bound remains open. C12.54 clarified the positive higher-grade error and the surviving pole but proved no frontier estimate. Keep the whole growing-order interpolant, its pole and the physical coefficient tail together. Test whether high-order coefficient matching and the signed parameter sum provide a vertical bound strong enough for the actual source; a real-axis estimate or separate fixed-parameter continuation is insufficient. Before writing Lean, obtain a dependency-closed proof of a bound that reduces the unresolved complete-source cancellation.

**Paper candidate obtained; NOT Lean verified.** The proposed absolute vertical majorant now has a concrete adverse test on the complete interpolant, not just on one parameter. The paper argument below predicts a growing-height-sector lower bound and highest-parameter dominance. This is progress on diagnosing this particular attempted estimate, not an RH bound. Do not cite it as a corpus theorem until formalized. No claim is made here about the signed Mellin integral after its pole contribution is included.

Fix `1/2<sigma<1`, put `q=1/sigma`, and retain

`F_j(s)=zeta(s)^j product_p (1+j*p^(-s))*(1-p^(-s))^j`,
`H_D(s)=sum_(j=0..D) (-1)^j binom(D+1,j+1) F_j(s)`.

Define the positive-height interval

`J_D=[7*pi*sigma/(12*log D), 5*pi*sigma/(8*log D)]`.

The candidate conclusion is that, for some positive c and all sufficiently large integer D, uniformly in t in J_D,

`|H_D(sigma+i*t)| >= exp(c*D^q/log D)`;
`H_D(sigma+i*t) / ((-1)^D F_D(sigma+i*t)) -> 1` uniformly on J_D.

The second statement is the positive structural survivor: the full signed interpolation is asymptotically dominated by its highest parameter on this moving sector. The sector has width `pi*sigma/(24*log D)`, so this is not merely an isolated large value. The argument is as follows.

1. **Continuous parameter and legitimate differentiation.** Near the nonzero real value zeta(sigma), choose any local logarithm of zeta. For real a>=0 define F_a there using that logarithm and principal logarithms of `1-p^(-s)`; the latter factors have positive real part because `|p^(-s)|<1`. On bounded a intervals the corrected local products converge uniformly, since their linear terms cancel and `sum_p p^(-2*sigma)<infinity`. Their logarithmic derivative in a has a locally uniform quadratic tail. At the integer parameters this is exactly F_j above, independently of the chosen zeta logarithm.

   On `0<=a<=D`, `t in J_D`, no factor `1+a*p^(-s)` vanishes. Vanishing would require `a=p^sigma` and `t*log p=(2k+1)*pi`; its smallest possible positive phase gives `a>=D^(8/5)>D`. This retains every prime and makes `L_(D,t)(a)=log|F_a(sigma+i*t)|` differentiable on the full parameter interval.

2. **The actual parameter derivative.** With `x_p=p^(-s)` and `K(w)=Re(w/(1+w)-w)`,

   `a*L'_(D,t)(a)=sum_p K(a*x_p)+a*C(s)`,
   `C(s)=log|zeta(s)|+sum_p (Re log(1-x_p)+Re x_p)`.

   C(s) is bounded uniformly on the shrinking height interval: the zeta value is bounded away from zero near sigma, and the remaining prime sum is bounded by a fixed multiple of `sum_p p^(-2*sigma)`. No zero-free assertion outside this small neighborhood is used.

3. **Positive central prime sector with both tails retained.** For `w=v*exp(-i*phi)`, v>0, write b=cos(phi). Direct algebra gives

   `K(w)=[v^2*(1-2*b^2)-b*v^3]/[1+2*b*v+v^2]`.

   If `pi/2<=phi<=2*pi/3`, then `K(w)>=v^2/[2*(1+v)^2]`. Take `D^(9/10)<=a<=D`, `R=a^q`, and `u=p/R`. The actual phase is

   `t*log p = (t*log a)/sigma + t*log u`.

   Its first term belongs to `[21*pi/40,5*pi/8]`. Thus, on any fixed compact interval `delta<=u<=A`, every actual phase lies in `[pi/2,2*pi/3]` for all sufficiently large D, uniformly in a and t. All these prime contributions are nonnegative. On `1<=u<=2`, v=u^(-sigma) belongs to `[1/2,1]`, so K>=1/32. PNT gives at least `c0*R/log R` primes in `(R,2R]` eventually.

   The primes below delta*R are not omitted: choose `delta<2^(-q)`, so v>2 there and `|K(w)|<=2*v`. The prime power-sum asymptotic bounds their total by `C_sigma*delta^(1-sigma)*R/log R` eventually. Likewise choose `A>2^q`; then v<1/2 above A*R and `|K(w)|<=2*v^2`. The prime-tail estimate bounds that total by `C_sigma*A^(1-2*sigma)*R/log R`. The positive prime-power tail with coefficients Lambda(n)/log n majorizes the prime-only tail and is sufficient here; it is not identified with that tail. Choose delta small and A large to make both adverse budgets smaller than half the central gain. The term a*C(s) is negligible because `a/(R/log R)->0`, uniformly for a>=D^(9/10).

   Consequently, with constants depending only on sigma,

   `L'_(D,t)(a)>=c1*a^(q-1)/log a` for `D^(9/10)<=a<=D`, uniformly in t in J_D.

4. **Low parameters cannot hide an adverse initial value.** Uniformly on `0<=a<=D`, the elementary product estimate gives

   `|L_(D,t)(a)|<=C_sigma*(1+a^q)`.

   To retain a lower bound on all local factors, split primes at `D^(6/(5*sigma))`. Below this point their phase is at most `3*pi/4`, so `|1+a*x_p|` is a fixed positive multiple of `1+a*p^(-sigma)` or larger. Above it `a*p^(-sigma)<=D^(-1/5)`, eventually at most 1/2. Now split again at `(2*a)^q`: the low part is bounded by the sum of `1+log(1+a*p^(-sigma))+a*p^(-sigma)`, and the high part by a constant times `a^2*sum p^(-2*sigma)`. Replacing primes by integers suffices for the resulting O(1+a^q) bound. The correction `a*(log(1-x_p)+x_p)` contributes O(a). This estimate also handles a=0 separately via F_0=1.

   Integrating the derivative lower bound from `D^(9/10)` to D therefore gives `L_(D,t)(D)>=c2*D^q/log D`. The initial possible loss is only `O(D^(9*q/10))`.

5. **Full signed-sum comparison.** For `D/2<=j<D`, integration over [j,D] gives

   `|F_j/F_D|<=exp(-c3*(D-j)*D^(q-1)/log D)`.

   For `D^(9/10)<=j<D/2`, monotonicity plus integration over [D/2,D] gives `|F_j/F_D|<=exp(-c4*D^q/log D)`. For smaller j the bound in step 4 and the lower bound on L(D) give the same form eventually. The total binomial weight in the lower half is at most `2^(D+1)`, which is absorbed because q>1. In the upper half, set h=D-j and use `binom(D+1,h)<=(D+1)^h/h!`. The total relative contribution is at most

   `exp((D+1)*exp(-c3*D^(q-1)/log D))-1`,

   which tends to zero. This bounds all lower terms relative to F_D without relying on their phases. The highest coefficient is exactly (-1)^D, proving the proposed dominance and growth once the preceding estimates are formalized.

**Consequences and limits of the paper candidate.** Since Gamma is continuous and nonzero near sigma, the same sector would give an exponentially large lower bound for the absolute Gamma-weighted vertical L2 integral of H_D. For the safe matching cutoffs `N_D=(D+2)!-1`, every squarefree n<=N_D has at most D distinct prime factors, and `log N_D=O(D*log D)`. The displayed vertical growth exceeds every fixed power of N_D. Thus the cheap interpolation coefficients by themselves cannot support the hoped-for absolute vertical estimate. None of this gives a lower bound for the signed Mellin inversion, whose oscillation and pole terms may cancel, nor does it refute RH or the full route MC.

**Formalization obligation / next work.** Audit and formalize the full uniform parameter-derivative estimate and dominance statement, not merely the local rational identity. Then test the actual signed pole/contour balance using what that audited result permits. Current source inputs read: `PrimeRpowSumAsymptotic.tendsto_primeRpowSumIoc`, the quadratic logarithmic tail estimate in `HTGeometry/EulerLogTail`, PNT/counting source, and `PrimeTailBoundaryAsymptotic.tendsto_primeTailSum_div` with its prime-power scope retained. These source signatures have not been checked in a new Lean scratch file this turn; no new Lean result is claimed. No route retired, no auxiliary module added. Three research searches terminal (two partial, one complete), with snapshot/compiler freshness limitations retained. No numerical computation, Lean edit/build, RH proof or falsification. Goal active and unmet.

## C12.56: formal audit of the complete parameter work

**Complete prime-work theorem audited; derivative and dominance still open.** The preceding turn produced a paper candidate that changes the attempted estimate; it did not prove an RH source bound or add a verified frontier theorem. The complete prime-work proof passed in `/tmp/mc_source_1003u_kernel.lean` and has been promoted to `formal/GaloisForLFunctions/RHTower/MobiusFactorCountPrimeWork.lean`. The leaf build and final `lake --old env lean GaloisForLFunctions/RHTower/MobiusFactorCountPrimeWork.lean` both passed. A separate scratch axiom audit of all three public declarations returned only `propext`, `Classical.choice`, `Quot.sound`. The umbrella import is wired; no umbrella build was run.

**Paper simplification during the audit.** Weighted prime asymptotics are not needed to pay the two adverse tails. At sigma=3/4, keep `D^(9/10)<=a<=D` and `7*pi/(16*log D)<=t<=15*pi/(32*log D)`. Every prime in `[a^(13/10),a^(7/5)]` has phase in `[pi/2,2*pi/3]`: its lower phase is at least `819*pi/1600>pi/2`, and its upper phase is at most `21*pi/32<2*pi/3`. The central interval `(a^(4/3),2*a^(4/3)]` lies inside this positive range eventually and contributes at least 1/32 per prime.

The complete low-prime loss is bounded by `2*a*sum_(n<=a^(13/10)) n^(-3/4)`, hence by `10*a^(53/40)` using the current integer head estimate. The complete high-prime loss is bounded by `2*a^2*sum_(n>a^(7/5)) n^(-3/2)`, hence by `6*a^(13/10)` using the current integer tail estimate and the ceiling cutoff. Both exponents are strictly below 4/3, so both losses are little-o of `a^(4/3)/log a`. PNT is needed only for the central prime count. This is a simpler proof mechanism for the full prime-work lower bound, not a constant optimization or an estimate on a selected prime subfamily.

Current source inputs for that assembly are `Sieve.NearDiagonalOffsetBookkeeping.head_contribution_le`, `tail_contribution_le`, and `HTGeometry.AbelianZetaGas.PrimeWindowCount.eventually_primeCount_window_ge` with its actual interval cardinality law. The original prime-power tail argument is superseded for this specialization. Passage to the continuous-parameter derivative and full H_D dominance remain to be completed in Lean. No RH conclusion follows from the prime-work theorem.

The scratch audit has now completed the finite prime-sum assembly and its uniform asymptotic lower bound. The promoted theorem `eventually_mobiusFactorCountPrimeWork_lower` retains every prime up to arbitrary N with `floor(2*a^(4/3))<=N`, uniformly for the displayed a,t ranges. Its only assumptions are those explicit parameter ranges; it consumes no unproved cancellation or RH premise. The remaining obligations are identification and integration of the actual Euler-product parameter derivative, control of its low-parameter initial value, and domination of all lower interpolation parameters. The complete H_D growth claim is still a paper candidate, and the signed Mellin/pole balance and final RH energy bound remain open.

Formal lint was run and returned 12 unrelated unreachable-module errors (`CCMApertureChainProfile`, `CCMApertureTranslationChains`, `CCMEulerEventualCarrier`, `CCMExponentialRampPrimeMoment`, `CCMExponentialRampSourceDissipation`, `CCMExponentialRampTerminalEntropy`, `CCMRestrictedWeilPolarShiftLower`, `CCMRetainedChainKernelLower`, `MoebiusMollifiedCriticalMoment`, `MoebiusMollifiedErrorThreeLines`, `ThetaMovingShellFirstOrderPhase`, `ZetaZeroDensityPowerSaving`). It reported no error for the new module. These other files were not changed. The complete direct proof and public-declaration axiom inspection passed without added axioms or heartbeat changes. This closes an analytic component of C12.55, not the final signed cancellation problem or RH.

## C12.57: actual Euler-parameter growth

**Completed analytic stage.** C12.56's complete prime-work theorem now proves positive parameter growth of the actual corrected finite Euler product, uniformly in its prime truncation; final audits are recorded below. Define its log modulus directly, including the zeta term. Prove the logarithmic derivative identity and a truncation-independent bound on the quadratic correction; integrate only after proving all affine factors stay separated from zero. The next hard targets are the low-parameter initial-value bound, full binomial interpolation dominance, then the signed Mellin/pole cancellation that absolute contour growth leaves unresolved.

**Paper factor separation.** For `0<=a<=D` in C12.56's height interval, split at `p=D^(7/5)`. Below that cutoff the phase is in `[0,21*pi/32]`, hence its cosine is at least -1/2 and `|1+w|>=(1+|w|)/2`. Above it `|w|<=D^(-1/20)<=1/2` eventually, so `|1+w|>=(1+|w|)/3`. Thus every affine factor is uniformly separated, with no selected prime family or omitted tail. This will support differentiation and the low-parameter estimate. It is not yet a Lean theorem.

**Improved low-parameter paper argument.** Factor separation also bounds the derivative directly: `|z/(1+a*z)-z| <= 3*min(a*|z|^2,|z|)` for every prime base z and a>=0. On 0<=a<=A<=D, split at A^(4/3). The current integer head estimate pays low primes by 15*A^(1/3), and the current integer tail estimate pays high primes by 9*A^(1/3). Thus the absolute full log-modulus derivative is at most B+24*A^(1/3), uniformly in the prime truncation, with the same bounded zeta/Euler correction B. Since L_N(0)=0, the mean-value theorem gives |L_N(A)|<=B*A+24*A^(4/3). This directly supplies the initial value at A=D^.9 and low integer parameters. The factor separation, derivative identity and uniform correction are currently being checked in one foreground Lean scratch process; no completed C12.57 result is claimed yet.

**C12.57 integration status.** The scratch audit has now accepted the full finite log-modulus growth argument, including its initial value, with lower bound D^(4/3)/(4096 log D), uniform in N>=floor(2D^(4/3)) and the moving height interval. The actual finite Euler product is zeta(.75+it)^j times the product over p<=N of (1+j*p^(-s))*(1-p^(-s))^j. Its nonvanishing and log-norm identity are being checked before promotion; a generic imported name collision was resolved by a task-specific name. No final module audit for C12.57 yet.

**Next full-sum comparison (paper).** Combine the uniform derivative, low-parameter estimate and highest-parameter growth to prove a single gap for every integer 0<=j<D: L_N(D)-L_N(j)>=c*(D-j)*D^(1/3)/log D. Above D/2 this follows by integrating the derivative; between D^.9 and D/2 it follows from monotonicity plus the upper-half increment; below D^.9, the low-parameter bound is negligible compared with the highest value. This retains every interpolation parameter. Then choose(D+1,j+1)<= (D+1)^(D-j) and the normalized lower terms are bounded by a geometric sum with ratio r_D=(D+1)*exp(-c D^(1/3)/log D), tending to zero. This supplies the full signed dominance once formalized, while leaving signed Mellin/pole cancellation open. The latest deep dominance search returned partial snapshot coverage; its suggested Maass-cusp-decay/Li-term ingredient group concerns different carriers and is rejected. No such premise is imported.

**C12.57 promotion.** The full scratch proof, including the literal finite Euler-product identity and nonvanishing, passed. Promoted to `formal/GaloisForLFunctions/RHTower/MobiusFactorCountEulerGrowth.lean`, wired immediately after the prime-work import. Leaf `lake --old build GaloisForLFunctions.RHTower.MobiusFactorCountEulerGrowth` passed (new leaf 130s; dependency diagnostics were replayed). An initial build invocation from the repository root correctly failed for missing lakefile; rerun used formal/. The required direct source audit is now running; public-declaration axioms remain to inspect afterward. Latest lint returned 11 unrelated unreachable modules, none the new module: CCMApertureChainProfile, CCMApertureTranslationChains, CCMExponentialRampPrimeMoment, CCMExponentialRampSourceDissipation, CCMExponentialRampTerminalEntropy, CCMRetainedChainKernelLower, MoebiusMollifiedCriticalMoment, MoebiusMollifiedErrorThreeLines, SoninAnnularDilationNilpotent, ThetaMovingShellFirstOrderPhase, ZetaZeroDensityPowerSaving.

## C12.58: full signed interpolation dominance

**Completed full signed dominance.** `MobiusFactorCountInterpolationDominance.lean` now proves a uniform gap between the highest parameter D and every integer j<=D, and uses it to control the complete signed sum. A midpoint m=(D+j)/2 simplifies the high-parameter case: the first interval is nondecreasing and the second lies above D/2. The low-parameter estimate controls the remaining j below D^.9. Scratch, leaf, direct-source and public-axiom audits all passed; final details follow below.

**C12.57 final audit complete.** `lake --old env lean GaloisForLFunctions/RHTower/MobiusFactorCountEulerGrowth.lean` passed. Separate `/tmp` axiom audit of all seven public declarations returned only `propext`, `Classical.choice`, `Quot.sound`. No added premises beyond explicit parameter ranges, no new axioms, no heartbeat changes, no computation/experiment, no umbrella build. This is new audited Euler-parameter growth and initial-value control; full signed dominance and RH remain open. All owned 1003v search/build handles are terminal and scratch files are cleaned after recording the result. C12.58 continues in its separate scratch.

**C12.58 full-sum proof passed in scratch and leaf build.** Promoted to `formal/GaloisForLFunctions/RHTower/MobiusFactorCountInterpolationDominance.lean`, wired after EulerGrowth. For every epsilon>0, eventually in integer D, uniformly in the moving height sector and every N>=floor(2D^(4/3)), the norm of H_(N,D)-(-1)^D*F_(N,D) is at most epsilon*|F_(N,D)|. Consequently |H_(N,D)|>=exp(D^(4/3)/(4096logD))/2 throughout the sector. All j=0..D are retained. Scratch proof and leaf `lake --old build` passed; direct source audit is running and all four public declarations still need the separate axiom audit. The latest lint reports 13 unrelated unreachable modules, none this module; it is not a global pass. No umbrella build.

**Consequence and next hard problem.** Large vertical growth is now proved for the full signed finite Euler interpolation. It cannot be attributed to omission of lower parameters. This does not give a lower bound for its signed Mellin inversion: the pole contribution, contour oscillation and completed high-coefficient tail remain coupled. The latest partial corpus search returned exact inversion/Mellin identities and premise-taking decay-to-continuation bridges, but no producer of that coupled cancellation estimate. The next test will retain this coupling and examine the quadratic prime counterterm at the interpolation evaluation -1; no new contraction is assumed.

**C12.58 direct source audit passed.** Final `lake --old env lean GaloisForLFunctions/RHTower/MobiusFactorCountInterpolationDominance.lean` exited zero. Separate axiom audit is now running. A later redundant poll correctly reported the already-closed handle missing; no duplicate source audit was started.

## C12.59: quadratic counterterm with square-supported error

**Hard target, not proved.** Retain the full Mellin/pole balance and test a modified completion whose error is supported on non-squarefree integers. Current corpus inputs read: `SquarefreeMoebiusNormalization.LSeries_sqrtPart_moebius` represents zeta(2s)^(-1) by a square-supported series on Re(s)>1/2; its squarefree product laws have the stated Re(s)>1 scope. `SteinhausEulerQuadraticApprox` gives a uniform cubic remainder for the first two local prime-power terms, for every phase on Re(s)>=1/2; it asserts no deterministic Mobius cancellation. The retrieved safe-correction certificate is an identity, not a signed-energy producer. Both latest searches were partial/snapshot; no source assumption was dropped.

For integer j put c_j=j(j+1)/2 and consider F_(j,N)(s)*zeta(2s)^(-c_j). The local counterterm is supported on squares, has constant coefficient one, and c_(-1)=0. Therefore it preserves every squarefree coefficient of F_(j,N). For n<=N the completed coefficient is a polynomial in j of degree at most Omega(n), and evaluation at j=-1 is mu(n). Interpolation at 0..D consequently leaves an error only at nonsquarefree n with Omega(n)>D. This differs from scalar damping of the samples, which already spoils the constant coefficient and whose exact finite-polynomial repair simply undoes the damping. No Lean theorem for this new completion is claimed.

**What the first estimate fails to control.** Near height zero, |zeta(2s)|>1 makes the quadratic multiplier damp j^2, potentially paying the interpolation coefficients and j^(1/sigma) Euler growth. That local observation is not a global vertical bound: away from the local sector its reciprocal may amplify j^2. Replacing it on a height window around T by zeta(2s-2iT)^(-c_j) preserves squarefree coefficients, but window-dependent completion is not a single analytic Mellin transform. Center integration retains the square error. Formally writing s=sigma+it and u=t-T, a square coefficient b_j(d) carries d^(-2sigma)*exp(-2iu log d); thus averaging windows produces the Fourier weight at 2log d, rather than automatically deleting d>1. Exact square deletion by a Fourier cutoff prevents arbitrary compact localization to the damping sector. Neither a bound for the signed square-supported error nor a controlled window reconstruction was proved. This is the next coupled cancellation problem, not a new decay premise.

**Support refinement to retain in the next attempt.** For integer j and primes p<=N the local factor (1+j*x)*(1-x^2)^(c_j) has prime exponent at most j(j+1)+1. Consequently, among low j, error indices with Omega(n)>D require many small primes once this exponent cap is filled; the crude threshold 2^(D+1) is not sharp there. This can help separate low-parameter leakage from high j, but it does not itself control signed truncated norms or the Mellin-window commutator. No frontier bound is claimed from this refinement.

**C12.58 final verification.** All four public declarations passed separate `/tmp` axiom inspection: only `propext`, `Classical.choice`, `Quot.sound`. Scratch, targeted leaf build and required direct source audit passed; umbrella wired. Latest lint has 13 unrelated unreachable-module errors (CCMApertureChainProfile, CCMApertureTranslationChains, CCMEulerAnnularRange, CCMEulerBoundaryQuotient, CCMExponentialRampPrimeMoment, CCMExponentialRampSourceDissipation, CCMExponentialRampTerminalEntropy, CCMRetainedChainKernelLower, MoebiusMollifiedCriticalMoment, MoebiusMollifiedErrorThreeLines, ThetaMovingShellFirstOrderPhase, ThetaTailNormalizedRowCurvature, ZetaZeroDensityPowerSaving), with no error for this module. No unrelated module changed, no full build, no added axioms, no heartbeat changes, no numerical experiment. Owned 1003w/1003x scratch and completed search outputs are cleaned.

**C12.59 result so far: no new cancellation bound.** The quadratic square-supported completion isolates a different error but does not yet control it. Localizing its damping to a moving height center changes the reconstruction: center-dependent square twists can feed the square error back into the original frequency. Therefore the low-parameter support gap cannot by itself justify discarding that error after window integration. No bound on this coupled window/error term has been proved. Continue with that exact signed term, not a generic squarefree-projection norm or a presumed globally damping zeta factor. The hard MC subpower-energy problem and RH remain open; the goal stays active.

## C12.60: translated-window reconstruction and the coupled residual

**1003y scope and progress classification.** Route MC remains the full signed Mellin/pole cancellation problem behind subpower Mobius energy. C12.58 is audited progress on the complete interpolation, but supplies no bound on its inverse transform. This continuation examined C12.59's square-supported correction, including its reconstruction rather than discarding the error. No new MC cancellation bound or Lean theorem was obtained.

**Corpus check.** The square-supported/Mellin deep search completed with `partial=false`: snapshot 64377 files, compiler metadata largely pending (48546) or stale (2660), only 43 compiled snapshots. Its suggested coordinate-metric quadratic-inverse/Mellin ingredient chain has different carriers and is inapplicable. The narrower Squarefree search also completed: 64378 files, 48547 compiler-pending, 2660 stale. Its applicable inputs are the previously read square-dilated Mobius series and squarefree convolution identities; the Selberg--Delange result explicitly requires `ZetaBinomialHalfKatoInversion`. A later signed-interpolation/pole search returned partial/pending coverage. It found the current interpolation and conditional Mellin continuation receivers, not a source bound. No freshness or applicability assumption is silently promoted to a theorem.

**Larger interpolation degree does not settle reconstruction.** Choosing D at least log(X)/log(2) makes every coefficient below X have Omega at most D, so polynomial interpolation recovers that prefix even for a fixed center-dependent square correction. This repairs one coefficient-range issue. It does not justify center integration: the square twist changes the frequency seen after that integration. A narrowing Gaussian height window also spreads its inverse Fourier kernel in log scale; its Fourier decay at frequency L is proportional to exp(-constant*width^2*L^2), not exp(-constant*L^2/width^2). Thus width of order 1/D gives no large decay at log-frequency of order D. The earlier high-Omega support observation alone cannot pay the resulting error.

**Exact paper calculation of the translated-window multiplier.** Work first on a line sigma>1, with a finite prime completion and an integrable window psi for which the displayed integrals exist. Let c_j=j(j+1)/2 and r_sigma(u)=zeta(2*sigma+2*i*u)^(-1). For fixed t, the substitution u=t-T gives

    integral_T psi(t-T) F_j(sigma+it)
      * zeta(2*(sigma+it)-2*i*T)^(-c_j)
    = B_j(sigma) * F_j(sigma+it),
    B_j(sigma) = integral_u psi(u) * r_sigma(u)^(c_j).

This is an ordinary multiplier on the uncorrected sample. It is not square deletion. The same scalar identity on another vertical line requires the stated integrability, not a Dirichlet-series continuation claim. For a normalized nonnegative window supported where |r_sigma|<=q<1, |B_j|<=q^(c_j). In particular B_0=1 while B_1 cannot equal one. At D=1 the constant coefficient of the averaged interpolation is 2-B_1, already different from one. No numerical experiment is used in this argument.

**Prefix moment rigidity (paper, not yet Lean).** Write w_j=(-1)^j choose(D+1,j+1). When the desired prefix contains a squarefree integer of each factor count k=0,...,D, and those primes belong to the completion, coefficient recovery after translated-window averaging requires

    sum_(j=0)^D w_j B_j j^k = (-1)^k   (k=0,...,D).

Subtract ordinary interpolation. The Vandermonde matrix on the distinct nodes 0,...,D is invertible, and each w_j is nonzero. Consequently every B_j must equal one. Conversely these equalities give all those moments. For any signed window supported in |r_sigma|<=q<1, the j=D equality forces integral |psi| >= q^(-D(D+1)/2). Thus the damping cannot be converted to exact coefficient recovery with a small total-variation normalization. This is a constraint on this translated-window construction, not a no-go for MC or an RH result. This local mechanism is not marked retired or formally closed; its positive reconstruction statement still has paper-only status.

**Retained positive statement and next hard attack.** The complete reconstruction is H_D=H_D^window+Q_D, with Q_D=sum_j w_j(1-B_j)F_j. The absolute lower-parameter estimates used in C12.58 suggest a stronger paper consequence: if all |B_j|<=1 and B_D tends to zero, H_D^window=o(|F_D|) on its moving sector, while Q_D/((-1)^D F_D) tends to one. The public full-sum theorem alone does not prove this for arbitrary multipliers; its absolute term comparison must be retained. Hence an absolute bound on the window part leaves a large reconstruction term. The remaining target is the signed inverse transform of the entire reconstructed expression together with its pole contribution and completed coefficient tail. Neither a small norm of the window part nor a presumed zero reconstruction cost is an admissible substitute. No estimate of that signed integral is proved here.

**Validation and ownership.** No Lean source changed, so no build or repeated audit was run. No subagents, numerical computations, new axioms, heartbeat changes, umbrella build, or commit. All three owned search processes terminated before parsing and cleanup. The active RH goal remains unmet.

## C12.61: pole cancellation with the physical boundary energy retained

**1003z target.** Continue MC's full signed Mellin/pole problem. C12.60 changed the next action by exposing the translated-window reconstruction cost, but produced no source cancellation estimate. This turn tested degree averaging, additional interpolation nodes, and a pole-cancelling multiplier that preserves the critical-line norm. No RH result or new Lean theorem is claimed.

**Current corpus.** The contour search completed with `partial=false`, snapshot 64382 files, 48550 compiler-pending and 2660 stale files. Its suggested principal-L detector and Ingham zeta-square contour ingredients have different integrands and poles; matching their contours does not cancel H_D's growing-order pole. The Blaschke/boundary search was partial with pending coverage. Directly read `HardyBlaschkeMultiplier`: the inner symbol is an L2 isometry; inverse Hardy preservation explicitly needs a vanishing Cauchy transform. Read the opening of `MobiusCenteredMertensLimit`: its critical boundary is `1/(it*zeta(1+it))`, not the half-line Mobius energy target. `EulerDeletionPrimitiveHardy` is a Schur transfer of an existing input energy. None is used as an unconditional MC bound.

**Degree-averaging test, not a theorem.** A positive distribution on degrees above the maximum factor count preserves the exact arithmetic prefix. Gaussian averaging might appear to cancel the (-1)^D factor in the proved dominant sample. The initial estimate fails before supplying a bound: a Gaussian with variance large enough to pay exp(c*D^(4/3)/log D) must also control the growth of samples far from its center. The existing lower bound supplies no such upper-tail control, and shifting a parameter contour would require control of the entire parameter function at large imaginary arguments. Neither step was proved. Truncating the degree average introduces endpoints whose contributions must remain. No Gaussian cancellation estimate, saddle asymptotic, or blanket no-go is asserted.

**Additional-node test.** Exact evaluation of all polynomials of degree at most D at -1 imposes moment constraints even if extra nonnegative integer nodes are used. The test polynomial a*(a-1)*...*(a-D+1) vanishes at the first D nodes and forces a nontrivial contribution from nodes j>=D. The previously proved individual growth sectors depend on j; they cannot be combined into a pointwise lower bound at one common height for an arbitrary oversampled signed sum. They can inform an absolute sum-of-sample-norm cost, but that would not settle the coupled contour integral. No oversampling impossibility theorem is claimed.

**Pole filter, exact paper energy accounting.** Let

    Hf(x)=integral_(x to infinity) f(y) dy/y,
    Af=f-Hf,             B(s)=(s-1)/s.

For finite Laplace sums the Mellin transform of A is multiplication by B on Re(s)>0, by absolutely convergent Fubini. Moreover |B(1/2+it)|=1. Thus B^K removes a pole of order at most K at s=1 without changing the full critical-line norm of a finite L2 source. This alone supplies no bound on that norm.

For a>0 and the smooth exponentially decaying sources under consideration, h=Hf satisfies h'=-f/x and

    (x*|h(x)|^2)' = |h(x)|^2-2*Re(f(x)*conj(h(x))).

Integration, with the infinity endpoint retained and shown zero by exponential decay, gives

    integral_a^infinity |f|^2
      = integral_a^infinity |Af|^2 + a*|Hf(a)|^2.

Iteration yields the complete identity

    integral_a^infinity |f|^2
      = integral_a^infinity |A^K f|^2
        + a*sum_(r<K) |H(A^r f)(a)|^2.

For finite Laplace sums, the zero-endpoint term is also zero (only finite powers of log x occur), giving the global isometry. The identities on [a,infinity) also apply on paper to the full Mobius Laplace source: absolute exponential convergence and its differentiated series hold away from zero. No unproved behavior at zero is needed for this truncated identity. These calculations are paper-only, not audited Lean declarations.

**Literal boundary term, not a generic transfer premise.** Repeated Fubini expands

    H(A^r f)(a) = integral_a^infinity f(y)*L_r(log(y/a)) dy/y,
    L_r(u) = sum_(m=0)^r (-1)^m*choose(r,m)*u^m/m!.

The boundary energy therefore retains actual signed Mobius sums against these explicit kernels. Bounding the filtered contour while omitting this nonnegative sum would discard the energy that the filter moved out of the observed interval. No claim of Laguerre completeness or an independent subpower boundary estimate is used.

**Attempt to bound the boundary term from the divisor identity.** For f(x)=sum_n mu(n)*exp(-n*x), the exact Lambert relation is sum_(k>=1) f(k*x)=exp(-x), since mu*1 is the convolution unit. It is not the Bose kernel. H and A commute with dilations. Absolute convergence for a>0 therefore gives, for every fixed r,

    sum_(k>=1) H(A^r f)(k*a) = H(A^r(exp(-id)))(a).

After multiplying by sqrt(a), this is a known forcing vector equal to a sum of boundary vectors at k*a with weights 1/sqrt(k). Squaring retains every mixed dilation pairing; there is no orthogonality or nonnegative-cross-term statement. The reverse triangle estimate is noncontractive, and the corpus's divisor-comparable sign law does not control all those pairs. Thus the literal divisor identity has not yet bounded the retained boundary energy. This is the unresolved source calculation, not permission to assume a coercivity inequality.

**Outcome and next action.** No complete-source bound was proved. The pole filter makes the missing physical boundary contribution explicit; it does not evade the earlier Mellin-multiplier warning in the frontier map. Continue attacking the signed arithmetic pairings in that full boundary contribution, or a contour cancellation retaining the same contribution. Do not formalize a premise-taking recovery wrapper or count this coordinate change as solving MC. No route or local mechanism is marked formally retired. No Lean edits/builds, computations, subagents, heartbeat changes, added axioms, or commit. Both owned searches ended before parsing; their outputs are cleaned after recording this result. RH goal active and unmet.

## C12.62: full pairings, divisor geometry and rational readouts

**1004a classification: no frontier progress.** The retained boundary energy from C12.61 remains unbounded. This turn attempted to use the actual divisor-comparable sign law and then rational additive readouts. Neither produced a complete-source cancellation bound; no Lean source was added.

**Divisor geometry checked against source.** Read the proof mechanism in `MobiusDivisorMonotoneSignLaw`: its complement map is injective because m+n is the next multiple of m after n when m divides n. It does not assert a sign for arbitrary two-variable kernels, including individual boundary terms from C12.61. Read `MobiusHilbertDivisorBoundary`: the comparable section cancels at least twice the Hilbert diagonal up to 3, but the remaining noncomparable section must itself supply roughly a diagonal-sized positive contribution. The existing theorem bounds E_N by noncomparable-minus-diagonal plus 3; it does not upper-bound that excess. Positive definiteness of a Gram kernel does not make its Mobius off-diagonal nonpositive, contrary to a proposed search ingredient. The global sub-orthogonality source was checked: it is explicitly a hypothesis, with no producer.

**Full-pair reindexing did not add cancellation.** Writing m=d*a and n=d*b with gcd(a,b)=1 gives mu(m)mu(n)=mu(d)^2*mu(a*b) when all three squarefree/coprimality conditions hold, and zero otherwise. The d-weight is positive. Grouping further by a*b makes each product fibre have a common Mobius sign, not a cancellation inside that fibre. This returns to the already recorded C12.52 obstacle; no new result is credited. The visible coprime-dilation identity was also rechecked in `VisibleCoprimeMobiusLaplaceAddition.visibleCoprimeMobiusLaplaceSum_eq_add`: its specialization is sum_(gcd(k,l)=1) f(k*x)f(l*x)=f(2*x). It is the same mechanism screened in C12.51, so it is not a new advance or a source coercivity theorem.

**Rational-readout attempt.** Read `MobiusRamanujanTwoLevelConservation` in full. At every finite coefficient cutoff and for arbitrary complex weights, complete primitive prime-power readouts above p^2 vanish, while the p and p^2 readouts sum to minus the original source. The vanishing concerns complete unsquared sums, not the individual readouts' square norms. Therefore it cannot supply a tower of independent nonzero copies or a square-energy ceiling.

For the exponentially convergent infinite source at x>0, elementary coefficient regrouping gives the following paper form of the first layer. Define f_p(x)=sum_(p does not divide n) mu(n)*exp(-n*x). Then f_p(x)=f(x)+f_p(p*x), so f_p(p*x)=sum_(k>=1) f(p^k*x). Orthogonality of the nonzero residues modulo p gives

    sum_(a=1)^(p-1) sum_n mu(n)*exp(-n*x)*exp(2*pi*i*a*n/p)
      = -f(x)-p*sum_(k>=1) f(p^k*x).

This retains the entire prime-dilation tail. The p^2 primitive layer is the opposite tail term, in agreement with the corpus's two-level law. Applying Cauchy--Schwarz requires an upper bound on the actual rational-readout square energy; no such localized estimate was produced. Ordinary Fourier Parseval controls the whole circle by sum_n mu(n)^2*exp(-2*n*x), whose elementary upper bound has scale 1/x. It supplies no pointwise half-power bound at the original angle. No growing-modulus pole asymptotic, independence of rational arcs, or uniform residue estimate is assumed.

**Search/validation record.** Four owned deep searches completed before parsing: pair/divisor and coprime-dilation searches returned `partial=false`; sub-orthogonality and rational-arcs searches returned partial results. Snapshots ranged from 64395 to 64398 files, compiler-pending 48559 to 48561, stale 2660, compiled snapshots 43. Candidate/source scopes were inspected. Proposed PSD-to-negative-off-diagonal, reciprocity-to-dilation, and unrelated prime-boundary ingredient chains do not prove the target and were rejected. No build was run because no Lean code changed. No subagents, computations, added axioms, heartbeat changes, umbrella build, commit, or formally retired route. Search outputs cleaned after recording.

**Next hard work.** The unsolved quantities are still actual noncomparable/boundary cross pairings, or a localized rational-readout square estimate that controls those pairings without losing the prime-dilation tail. Rewriting the same coprime identity or importing global Parseval again would repeat a failed step. Require a new signed arithmetic estimate before adding a formal interface. RH goal active and unmet.

## C12.63: coupled primitive-level energy with the physical endpoint retained

**1004b in progress.** Route MC still requires a complete-source subpower Hilbert-energy bound. C12.62 made no frontier progress. Use the corpus's exact two-level reconstruction to test a signed mixed-energy estimate, retaining both the prime-dilation history and lower integration endpoint. Global circle Parseval and positivity of an unrelated Gram are not accepted as source estimates. No new claim is formalized until an actual cancellation inequality survives this endpoint audit.

**Outcome: no frontier progress.** The two-level mixed-term calculation did not yield a complete-source ceiling. The following endpoint audit is paper-only and is not credited as an RH cancellation theorem.

For x>0 let h(x)=sum_(p does not divide n) mu(n)*exp(-n*x), D_p h(x)=h(p*x), and f=h-D_p h. Exponential convergence justifies these identities and all integrals below for a>0. The complete primitive readouts from the checked corpus are

    U_p=-h-(p-1)*D_p h,       V_p=p*D_p h,       U_p+V_p=-f.

Use the real L2 pairing on [a,infinity), set G=||D_p h||_a^2 and I=integral_a^(p*a) h(x)^2 dx. Changing variables retains exactly ||h||_a^2=p*G+I. Consequently

    <U_p,V_p>_a
      = -sqrt(p)/2 * ||h+sqrt(p)*D_p h||_a^2
        -p*(p-1-sqrt(p))*G + sqrt(p)/2*I.

For p>=3 both displayed bulk terms are nonpositive, but the literal boundary interval contributes with positive sign. Full-line admission, which would remove this interval in a limit, has not been proved for the infinite source and was not assumed. More fundamentally, even a nonpositive mixed term would not bound ||U_p+V_p||: the two individual energies can be large. A sign-only argument therefore does not supply the size estimate required by MC.

At p=2, U_2(x) is the actual negative-real-axis readout sum_n mu(n)*(-exp(-x))^n. On L2([a,infinity)), D_2 has norm at most 1/sqrt(2), so both I+D_2 and I-D_2 have convergent Neumann inverses. The identity f=-(I-D_2)*(I+D_2)^(-1)*U_2 gives two-way energy comparison with constants independent of a. This preserves the hard source-energy obligation at a different angle; no bound on U_2 was obtained. It is not a new producer and no transfer module was added.

**Actual prime averaging checked, including the extra diagonal.** For the finite source f_N and its p-divisible part A_p, the complete primitive mixed pairing is

    C_p=p*<f_N,A_p>-p^2*||A_p||^2.

Thus the logarithmic prime-cut cross is

    sum_p log(p)*(C_p/p+(p-1)*||A_p||^2)
      = sum_p log(p)*<f_N-A_p,A_p>.

The positive correction cannot be omitted. Expanding the right side gives the signed pair weight log(m*n/gcd(m,n)^2), with the actual integration kernel and cutoff retained. This repeats the C12.19--20 obstruction, now seen from the primitive readouts; it earns no novelty credit. No estimate across its even and odd reduced-product factor layers was proved. Conditional negativity of the arithmetic distance and positivity of the log-gcd square sum do not upper-bound this actual nonzero-total source pairing.

**Other current source scopes checked.** `MobiusDivisorCriticalClockProductTransport` retains signed mixed work even after its exact density/boundary cancellation. `MobiusDivisorBernoulliPrimeEnergy` gives an averaged symmetric-difference kernel and a lower bound by the mean head square, not an upper bound on the completed source. `MobiusDivisorAllOrderBooleanSign` proves its sign at the empty core and a separate conditioned late-core statement; it does not establish that sign through arbitrary successive prime processing. None was used with a stronger scope.

**Next hard attack.** Bound the actual complete logarithmic prime-cut cross, or the corresponding full rational mixed energy with its boundary and diagonal terms, in size. The next attempt must address cancellation across reduced-product factor layers. Another sign test, a p=2 transfer, or the same gcd reindexing will not suffice. The concrete source obligation remains unproved; no route is retired.

**Validation record.** Three searches terminated before parsing. Two-level and dilation searches were partial; prime-cut search returned partial=false. Snapshots contained 64399, 64406 and 64409 files; compiler-pending counts were 48561, 48566 and 48568, with 2660 stale and 43 compiled snapshots. Candidate/source arguments were inspected; the proposed weighted-inversion chain retains its summability premise and gives no critical-energy bound. No Lean edits or builds, computations, added axioms, subagents, heartbeat changes, umbrella builds or commits. Owned search outputs cleaned after this record. RH goal remains active and unmet.

## C12.64: complete reduced-product layer cancellation

**1004c in progress.** C12.63 made no frontier progress. Route MC's open task is an upper bound on the complete signed pair energy, including the changing physical cutoff. Test a joint opposite-parity pairing of reduced-product layers against the actual weights. Prior single-prime telescopes, fixed-grade matching and factor-count interpolation are retained as failed closure attempts, not rediscovered as advances. Any proposed pairing must control its complete unmatched boundary and all multiplicities.

**Outcome: no complete-source bound or Lean frontier advance.** Two proposed producers were tested on paper. The second fails in a literal cofactor fibre, which changes the next attack from independent cofactor fitting to a coupled signed moment-capacity inequality. No existence theorem for the proposed complete pairing is claimed.

**Largest-two-prime merge.** Write a squarefree source index as d*p*q, where p<q are its two largest prime factors. A prime replacement ell near p*q gives opposite sign at d*ell and retains the full cofactor d. If q<p^2 and ell>=p*q, the image has largest prime greater than the square of every prime in d, so the input and image sectors are disjoint. An injective replacement within each d would be globally injective: the largest output prime identifies d as its complementary factor. The replacement may depend on d. This is a conditional description of the proposed construction, not a supplied arithmetic matching.

The existing prime/semiprime and semiprime/triprime matching sources do not provide this uniform construction: their specified targets, supply and ownership are different. In particular, their logarithmic cell displacement and fixed-order packet bounds cannot be promoted to a complete subpower Hilbert-energy ceiling. Even a matching of the whole balanced-top-two sector would retain the unmatched large-gap sector and the physical cutoff crossings. Neither retained contribution was bounded. No density heuristic was substituted for those obligations.

**Attempt to cover all inputs before global rounding.** Proposed choosing fractional prime targets for every cofactor to match its complete input moments through a growing degree, then pooling all actual signs for rounding. Read the current `MobiusOrderedMomentRounding` and `MobiusMomentSimplexSelector.exists_pooled_selection`: the corpus already has global rounding with bounded prefix discrepancy and power-moment error independent of the number of cofactor families. `MobiusCofactorLayerExtraction` and `MobiusCofactorLayerCofinal` supply selected literal packets with a residual; they do not assert full-input fractional feasibility. The missing step is before rounding.

**Literal singleton-fibre test.** Let r<p<q be consecutive primes, with q<p^2 for membership in the proposed balanced sector. At cutoff X=r*p*q, the cofactor-d=r source whose two larger prime factors exceed r contains only p*q: it is the least product of two distinct primes greater than r. This remains a singleton in the half-open product band (p*q/2,p*q]. Every proposed prime replacement ell differs from p*q. If nonnegative target weights lambda_ell matched moments of orders 0,1,2 exactly, then

    sum lambda_ell = 1,
    sum lambda_ell*ell = p*q,
    sum lambda_ell*ell^2 = (p*q)^2,

and hence sum lambda_ell*(ell-p*q)^2=0. Each available target has strictly positive squared displacement, contradicting total mass one. Thus target abundance alone cannot justify exact full-input moment fitting independently for every cofactor. This is a paper rejection of that proposed step, not a formalized no-go for the coupled route.

**Positive content retained.** For a source atom at m and approximate moment errors E_k=sum lambda_t*t^k-m^k, the exact variance is

    sum lambda_t*(t-m)^2 = E_2-2*m*E_1+m^2*E_0.

This identifies the nonnegative cost that any approximate local repair must carry. Its aggregate over the actual seam fibres has not been bounded. A disjoint target construction, fractional feasibility, growing-degree remainder and complete residual are all still obligations; none is hidden in a rounding theorem.

**Revised hard conjecture.** Fit the signed source across cofactors jointly. For disjoint actual source/target sets A,B and polynomials P of degree at most K, the necessary capacity inequality for weights 0<=lambda_b<=1 satisfying

    sum_(a in A) mu(a)*P(a) + sum_(b in B) lambda_b*mu(b)*P(b) = 0

is

    -sum_(a in A) mu(a)*P(a) <= sum_(b in B) max(0,mu(b)*P(b)).

Applying it to both P and -P retains both sides of every signed moment. The singleton obstruction need not survive this joint problem because other signed cofactors remain; it does rule out deducing the joint construction by the proposed independent fits. Next work must prove the actual capacity estimate, with its cutoff and residual, or learn from an actual separating polynomial. A fixed-degree PNT estimate or uniform subset average is not a growing-degree certificate. No new conditional receiver or easy rounding module is to be added as a substitute.

**Source/search audit.** Three searches terminated before parsing. Layer and pair-code requests returned partial=false; moment-cover request was partial. Snapshots had 64415, 64415 and 64418 files; pending compiler counts 48573, 48573 and 48576, with 2660 stale and 43 compiled snapshots. Retrieved candidate/source scopes were inspected. `CoprimeFiberStabilization` concerns its specific dyadic-triadic divisor count, not the current signed source. `MobiusFriableLargestPrimeDecomposition` keeps the friable source in its exact largest-prime split. `MobiusProductFibrePrimeBalance` repeats the local law already recorded in C12.52. Proposed incidence-algebra/Mobius-transform and packet-extraction ingredient chains supply no full covariance estimate. No computations, Lean edits/builds, subagents, added axioms, heartbeat changes, umbrella builds or commits. Paper observations above are not Lean-audited; no route is formally retired. Owned search outputs cleaned after recording. RH goal active and unmet.

## C12.65: joint signed polynomial capacity and the unremoved source

**1004d in progress.** Previous turn made no complete-source advance. Keep MC's original energy ceiling as the target. Test the joint polynomial-capacity inequality exposed in C12.64, allowing signed interaction across cofactors. Any fractional fit must retain its unused target coefficients and moving-cutoff source; a small fitted packet is not a bound on that residual. The singleton-fibre audit rules out proving this joint step by independent exact local fits.

**Outcome: no complete-source estimate or Lean frontier advance.** Joint feasibility was not proved. Even if a selected packet has zero moments through degree K, subtracting it leaves every corresponding moment of the full source unchanged in the residual. In particular, its constant moment retains the original signed charge. Repeated extraction therefore needs an independent bound for the depleted residual; original target abundance does not supply it. Moving targets to a much larger index does not make the packet cheap on the original physical interval: for coefficients of modulus at most one supported at n>=R, the absolute Laplace tail is at most exp(-R*x)/(1-exp(-x)). At x comparable to 1/N, sufficiently distant targets have negligible effect on the original finite source. No claim that this refutes a coupled construction with a proved residual budget is made.

**Weighted-source scope.** The retrieved Abel estimates either assume Mertens cancellation or express bounds in terms of the still-unknown zero abscissa. `CoprimeLogMoebiusOneRate`, `SmoothPrimeCoprimeLogUniformRate`, and `MoebiusLogPowerHomogeneousBound` concern their explicit harmonic/logarithmic kernels. Their fixed-degree constants and retained harmonic boundaries do not give a growing-degree certificate for ordinary physical moments. `CCMCoherentSignedMomentLocalCapacity` bounds a different displacement moment by its actual unknown energy. It is not a polynomial target-capacity producer.

**Prime recurrence was screened against earlier work.** Reopening the logarithmic prime-dilation pairing returned C12.28/C12.32, including their signed prime correlations, continuous-main-term boundary and Abel history. No new lower estimate was obtained, so this repetition receives no progress credit. The retrieved prime-deficit energy split merely names its signed cross term. The arity-energy source explicitly excludes the empty head and retains signed interaction charge; its quadratic-logarithmic initial bound does not control the complete source.

**Second attempt: positive finite divisor-incidence comparison.** Read the literal finite incidence matrix and its invertibility in `MobiusCoprimeMatrixFactorization`, the exact positivity classification in `DivisorStationaryKernelPositivity`, and finite circle diagonalization in `MobiusAdditiveDilationDiagonalization`. None gives quantitative control of the inverse in the Hilbert kernel. The following finite paper diagnostic keeps the cutoff and is not a newly audited Lean theorem.

For N>=1, on coordinates 1 through N write Z(n,d)=1_(d divides n), H(m,n)=1/(m+n), and T=Z^(-1). For b=Z*a, inversion and finite regrouping give

    sum_(n<=N) a_n exp(-n*x)
      = sum_(k<=N) b_k F_(floor(N/k))(k*x),
    F_M(x)=sum_(d<=M) mu(d) exp(-d*x).

Let C_N be the optimal constant in a^T H a <= C_N*||Z*a||_2^2. The first column T*e_1 is the full Mobius vector, while Hilbert-space Cauchy--Schwarz on all columns gives

    E_N <= C_N <= S_N,
    S_N=sum_(k<=N) E_(floor(N/k))/k
       =trace(T^T*H*T).

Consequently a subpower bound for this matrix comparison still contains the original MC obligation. Conversely a subpower bound for all E_M bounds S_N by the convergent sum of k^(-1-epsilon), with every cutoff retained. Invertibility, determinant one and positive definiteness alone do not supply that quantitative bound. No matrix receiver was formalized.

**Next concrete signed sum.** Finite expansion gives

    S_N=sum_(m,n<=N) B(m,n)/(m+n),
    B(m,n)=sum_(k divides gcd(m,n)) mu(m/k)*mu(n/k).

The prime-exponent factor of B is 1 at (0,0), 2 at equal positive exponents, -1 when the exponents differ by one, and zero otherwise. Hence its diagonal is 2^omega(n), but the complete off-diagonal still contains both signs. The physical set m,n<=N is not a product of independent prime-exponent boxes. A tensor-product estimate that drops this cutoff or every positive multi-prime interaction would change the sum. These are paper identities and an unresolved estimate, not new cancellation knowledge. Next test: estimate the full signed off-diagonal of this actual finite trace by a subpower budget, retaining all prime layers and cutoff faces. Do not replace that estimate by the already-known equivalence or by another single-prime sign test.

**Audit.** Five research requests terminated before parsing: capacity, weighted-Mertens and renewal searches were partial; incidence and trace searches returned partial=false. Snapshots contained 64423 through 64434 files, compiler-pending 48580 through 48586, stale 2660 and compiled snapshots 43. Candidate and source scopes were inspected; suggested incidence-to-unrelated-cusp-energy chains supply no bridge and were rejected. No numerical experiment, Lean edit/build, subagent, added axiom, heartbeat change, umbrella build or commit. No route formally retired. Owned search outputs cleaned after recording. RH goal remains active and unmet.

## C12.66: full finite divisor-inverse trace

**1004e in progress.** Previous turn made no frontier advance. Attack the actual signed trace from C12.65, preserving its complete physical cutoff. First test whether summing the common-divisor coordinate removes the cofactor masks without losing the needed sign; then test the remaining full reduced-product layers. A new matrix identity alone is not a result on the MC frontier.

**Outcome: no complete-source bound.** The trace regrouping does remove a coprimality mask, but it does not cancel the reduced-product signs. The following finite calculations are paper diagnostics, not Lean-audited frontier theorems.

For coprime positive a,b and positive g, the prime-exponent factors from C12.65 give

    B(g*a,g*b)=mu(a)*mu(b)*2^#{p prime : p divides g and p does not divide a*b}.

This is also zero on both sides if a or b is not squarefree. Define

    A_q(Y)=sum_(1<=g<=Y) 2^#{p|g : p does not divide q}/g.

Then the complete trace is

    S_N=sum_(a,b<=N, gcd(a,b)=1)
          mu(a)*mu(b)/(a+b)*A_(a*b)(floor(N/max(a,b))).

The old squarefree/coprime restriction on g has disappeared, but A_q is positive and every factorization of the same squarefree q still has sign mu(q). A uniform unsigned bound for A_q cannot supply the missing cancellation between q layers. Its exact prime recurrence, for p prime not dividing q, is

    A_q(Y)=A_(q*p)(Y)+(1/p)*A_(q*p)(floor(Y/p)).

Both the prime-dependent weight and its changing endpoint must remain in any attempt to pair these layers. No uniform Euler-product asymptotic with a usable signed remainder was proved or assumed. The retrieved coprime-squarefree harmonic source gives lower bounds under a restricted reciprocal-prime-mass hypothesis, not such a remainder for all actual products q.

**Complete divisor rows do not pay the noncomparable excess.** Finite divisor inversion gives sum_(m|n) B(m,n)=1 and diagonal B(n,n)=2^omega(n). More directly, summing the already-proved Hilbert divisor bound over k with weight 1/k gives, with H_N the harmonic sum and D_N^tr=sum_(n<=N)2^omega(n)/(2*n),

    T_N^tr <= (3/2)*H_N-D_N^tr,
    S_N <= C_N^tr-D_N^tr+3*H_N.

Here T_N^tr is the one-sided comparable section and C_N^tr the complete noncomparable section of B/(m+n). In particular, positivity of S_N forces C_N^tr>=D_N^tr-3*H_N. The diagonal has an elementary harmonic-square upper budget; the missing estimate is an upper budget for the signed excess. This inherits the original MC gap and receives no novelty credit. The source statement checked was `mobiusHilbertDivisorSection_le`; its sign was not extended to arbitrary two-variable kernels.

**Prime-chain summation test.** Summing one complete prime-exponent chain in the uncut kernel gives the positive expression

    K_p(a,b)=(p^2-1)*a*b/((a+b)*(p*a+b)*(a+p*b)).

This does not justify iterating entrywise positivity. For a nonempty finite prime set P, put h_P(x)=sum_(d|prod P)mu(d)*exp(-d*x) and rho_P=prod_(p in P)(1-1/p). The fully summed common-prime chains give the kernel rho_P^(-1)*integral h_P(a*x)*h_P(b*x) dx. Expanding its finite rational sum at b=R, a=1 yields

    lim_(R->infinity) R^2*integral h_P(x)*h_P(R*x) dx
      =-prod_(p in P)(1-p)*prod_(p in P)(1-1/p^2).

The first inverse-power term vanishes because sum_d mu(d)=0. For even nonzero |P| the displayed limit is negative. Thus the proposed positivity-preserving iteration fails already for finite even prime cores. This is a paper screening result, not a bound or a falsification for the complete Mobius source. The positive one-prime formula and the exact far-ratio leading term are retained; no formal no-go module or route retirement is claimed.

The physical cutoff cannot be replaced by those complete exponent chains. It clips the two neighboring exponent directions at potentially different levels. Even before further prime processing, the resulting endpoint correction depends on which direction survives. No estimate of the complete signed endpoint contribution, or its interaction with the reduced-product layers, was obtained. Existing original-core Boolean signs and fixed-core renewal formulas were not promoted to a sign valid after arbitrary processing.

**Next hard work.** Keep the finite trace and attack its actual noncomparable excess through the displayed A_q recurrence, jointly over all reduced products and their cutoff faces. A fixed-product sign, an unsigned harmonic estimate, or the uncut one-prime kernel does not discharge this task. No further transfer or diagonalization module is warranted before that arithmetic estimate.

**Audit.** Two deep searches terminated before parsing; both returned partial snapshot coverage. File counts were 64435 and 64439, compiler-pending 48587 and 48589, stale 2660 and compiled snapshots 43. Candidate/source scopes were inspected. Suggested mappings from divisor inversion to unrelated Hilbert-basis diagonalization, or from squarefree density to an unrelated full Gram, supply no source estimate. One unmatched shell glob was corrected by searching explicit known files. No Lean edits/builds, numerical experiment, subagents, added axioms, heartbeat changes, umbrella builds or commits. Owned search files cleaned after recording. Goal active and unmet.

## C12.67: signed finite prime history and its complete trace

**1004f in progress.** Previous turn produced no complete-source estimate. Entrywise positivity after one prime cannot be iterated. Test the actual finite-cutoff signed insertion work in the trace, including the copied-column energy and all mixed columns. An intermediate source with a selected prime set is not the completed Mobius source; any later payment must be proved before claiming an upper bound.

**Outcome: no complete-source bound or Lean frontier advance.** The finite trace has an exact signed insertion law, but its cumulative mixed work was not bounded. Prefix-by-prefix subpower control would demand a false estimate for a literal late-prime state. The following calculations are paper-only; no separate no-go or receiver module was added.

For a finite prime set P, define F_(P,M)(x) by retaining mu(d)*exp(-d*x) for d<=M whose prime factors all belong to P, and put

    E_P(M)=integral_0^infinity F_(P,M)(x)^2 dx,
    S_P(N)=sum_(k<=N) E_P(floor(N/k))/k.

For p not in P the literal source update is

    F_(P+p,M)(x)=F_(P,M)(x)-F_(P,floor(M/p))(p*x).

After squaring and summing every column, with no tail or copied square discarded,

    S_(P+p)(N)-S_P(N)=(1/p)*S_P(floor(N/p))-2*R_P(N,p),
    R_P(N,p)=sum_(k<=floor(N/p)) (1/k)*integral_0^infinity
               F_(P,floor(N/k))(x)*F_(P,floor(N/(p*k)))(p*x) dx.

Thus for a complete prime history P_j and inserted primes p_j, the required lower budget is for the combined quantity

    2*sum_j R_(P_j)(N,p_j)-sum_j S_(P_j)(floor(N/p_j))/p_j.

A lower bound by -C_epsilon*N^epsilon would bound the final trace, since the empty-state trace is H_N/2. This is an unproved arithmetic target, not an assumed estimate or a new theorem. Separate Cauchy--Schwarz estimates do not supply it. When p>sqrt(N) in an ascending history, the child cutoff is fully processed and equals the smaller complete source; before that seam the child still has its prime restriction. Replacing every child by a complete smaller source would be incorrect.

**Literal late-prime prefix.** For N>4 and P consisting of the primes in (N/2,N], no product of two P primes is active. Write L_N(x)=sum_(p in P)exp(-p*x). Only column k=1 changes from the empty state, giving

    S_P(N)=H_N/2-2*sum_(p in P)1/(p+1)+sum_(p,q in P)1/(p+q).

On 1/N<=x<=2/N, L_N(x)>=exp(-2)*|P|, while exp(-x)<=1. Once exp(-2)*|P|>=1, the first column alone has energy at least (exp(-2)*|P|-1)^2/N. The corpus's fixed-ratio prime-band supply therefore makes this a power-size intermediate energy, of order at least N/log^2(N). It is not a lower bound for the completed trace or for RH's source. It rules out paying this natural descending prefix by a uniform subpower allowance before the complementary arithmetic source has been included.

**Retained completion and failed precision step.** Let Q contain all primes at most N/2. Every composite d<=N has all prime factors in Q, so F_(Q,N)=F_N+L_N. For every k>=2 the Q-column is already the complete column at floor(N/k). Consequently the exact batch relation is

    S_Q(N)=S_complete(N)+||L_N||_2^2+2*<F_N,L_N>.

The last mixed term is part of the complete cancellation. An estimate of the two large terms separately, or mere relative antiparallel alignment, does not bound their retained difference at MC's scale. `MobiusPrimeInsertionMacroscopicPacket` already uses unconditional Mertens saving to obtain asymptotic antiparallel alignment for its specified packets; it does not give the necessary full residual rate. That known mechanism was not counted as a new solution or transferred between carriers without proof.

**Source scopes checked.** `MobiusDivisorLatePrimeFibres` gives its own exact signed head overlap. `MobiusDivisorPrimePairEnergy` contracts the original diagonal at the first pairing only. Retrieved moving-prime insertion bounds fix the processed core or bound its cardinality and retain their stated cutoff dependence. None is a bound for all columns of the trace above with a growing complete history. No numerical finite witness was used.

**Next hard work.** Estimate the displayed complete signed history balance across the square-root seam, with both fully processed smaller children and still-restricted children present. The late-prime calculation explains why individual signs, separate copied-energy budgets and uniform bounds on intermediate states are insufficient. No complete-history compensation theorem has been proved; no route is retired.

**Audit.** Two research requests terminated before parsing and returned partial results. The first reported pending coverage at generation 1187062; the second snapshot had 64442 files, compiler-pending 48590, stale 2660 and compiled snapshots 43. Available candidate and source scopes were inspected without inferring global absence from retrieval. No Lean edits/builds, numerical experiments, subagents, new axioms, heartbeat changes, umbrella builds or commits. Owned search outputs cleaned after recording. Goal active and unmet.

## C12.68: collective prime history across the square-root seam

**1004g in progress.** C12.67 did not advance the complete-source bound. Attack the signed insertion balance jointly across the square-root seam. Fully processed short children and restricted long children must occur in one estimate; neither separate copied-energy control nor a uniform bound on every intermediate prime prefix is available. Search and inspect the current largest-prime source decomposition before proposing the estimate. Do not count finite regrouping alone as a frontier result.

**Outcome: no complete-source bound or Lean frontier advance.** The square-root induction returns to C12.2--3's unproved smooth-head/child covariance. The next test, averaging prime orders before estimating the signed work, removes the processed-set mask in a finite formula but does not supply a sign or a subpower budget. All calculations below are paper diagnostics, not new audited Lean theorems.

**The large-prime block has no ordering gain.** Choose Y with N<Y^2, let H be the source with primes at most Y processed, and put g_p(x)=F_(floor(N/p))(p*x) for Y<p<=N. All these children are complete and independent of the order within this block. Write G=sum_p g_p and D=sum_p ||g_p||^2. For any order, the mixed pairing at p is <H-sum_(q before p)g_q,g_p>, so its total doubled work is

    2*<H,G>-||G||^2+D.

The copied energy is D; the final energy is exactly ||H-G||^2. Randomizing this order only allocates each cross-prime pairing symmetrically. It does not reduce or remove its aggregate. The attempted induction did not bound this joint excess. `MobiusFriableLargestPrimeDecomposition` supplies the exact complete children, not an estimate of H-G; no analytic friable asymptotic was inferred from its finite identity.

**Complete-history order average.** For the single Hilbert column average over all permutations of the primes at most N. For each squarefree pair m,n, other than (1,1), put

    U=primeFactors(m) union primeFactors(n), r=|U|,
    c=|primeFactors(m) intersect primeFactors(n)|,
    d=|primeFactors(m) symmetricDifference primeFactors(n)|.

The last prime of U is uniform in U. If it belongs to the intersection, this pair enters through the copied square; if it belongs to the symmetric difference, it enters through the mixed term. Hence the averaged copied energy A_N and doubled mixed work W_N are exactly

    A_N=sum_(m,n) mu(m)*mu(n)/(m+n) * c/r,
    W_N=-sum_(m,n) mu(m)*mu(n)/(m+n) * d/r,
    E_N=1/2+A_N-W_N.

Zero coefficients allow restriction to squarefree indices; no arithmetic sign is replaced by its modulus. Every physical cutoff remains m,n<=N. The same formulas may be summed at floor(N/k) with weight 1/k for the trace. A_N is nonnegative because it is an average of copied squares, not because its displayed summands have one sign. No bound for A_N-W_N was established.

**Conditional-negative-kernel test retains the unknown charge.** For nonempty finite sets define J(S,T)=|S intersect T|/|S union T|, with J(empty,empty)=1 and J(empty,T)=0 for nonempty T. Choosing a uniform random prime ordering realizes J as the probability that the first prime of S and T agrees; the empty set has its own label. Thus J is an average of partition Gram kernels, and D(S,T)=1-J(S,T) is conditionally negative on coefficient vectors with zero total sum. This is a finite paper proof, not an external theorem assumption.

At each x the actual coefficients a_n=mu(n)*exp(-n*x) have total F_N(x), which is not zero. Centering at the empty-set coordinate gives a'=a-F_N(x)*e_1 and the exact correction

    W_density(a')=W_density(a)+2*F_N(x)*(F_N(x)-exp(-x)).

The resulting nonnegativity retains 2*E_N-2*<F_N,exp(-x)> after integration. It therefore does not upper-bound E_N or pay the complete work. Conditional negative type was not applied to the uncentered source, and the unknown charge was not discarded. This diagnoses the proposed positivity argument; it does not falsify the desired arithmetic inequality.

**Scope audit.** `MobiusDivisorBernoulliPrimeEnergy` proves a different retained-label symmetric-difference kernel and a lower bound by its mean head square. `MobiusHalfSelectionGrowthObstruction` excludes fixed diagonal budgets for that specific divisor-source average. These are not silently identified with the present restricted Laplace columns or permutation average. The retrieved generic covariance inequalities, thermal Plucker variances and half-selection results do not estimate A_N-W_N. Proposed search ingredient chains lack this bridge.

**Next hard attack.** Stop rearranging prime orders. Test cancellation in additive slices of the actual finite trace kernel B(m,n), retaining the simultaneous m,n cutoffs. For h>=2 finite reindexing gives

    C_N(h)=sum_(m+n=h, 1<=m,n<=N) B(m,n)
          =sum_(k divides h) sum_(a+b=h/k, 1<=a,b<=floor(N/k)) mu(a)*mu(b),
    S_N=sum_(h=2..2N) C_N(h)/h.

This is only the source to attack. `MobiusMertensSelfConvolutionCriterion` and `MobiusLaplaceAdditiveTriangleSubpower` already provide additive/Cesaro receivers; their cancellation hypotheses must be proved, not repackaged. No pointwise additive-correlation bound, clipped-triangle bound or RH equivalence beyond the inspected statements is asserted here.

**Audit.** Four deep searches terminated before parsing; all returned partial snapshot coverage. File counts were 64444, 64445, 64449 and 64449; compiler-pending 48591, 48592, 48595 and 48595, stale 2660 and compiled snapshots 43. Available candidate/source scopes were inspected. Generated ingredients proving real-valuedness of an additive convolution or positivity of unrelated thermal variances do not provide cancellation. An initially guessed directory was corrected through `rg --files`; no nonexistent path was edited. No Lean edit/build, numerical experiment, subagent, new axiom, heartbeat change, umbrella build or commit. No formal no-go retirement. Owned search outputs cleaned after recording. RH goal active and unmet.

## C12.69: additive slices of the complete divisor-inverse trace

**1004h in progress.** Previous turn made no frontier progress. Attack the one-sided signed estimate in the finite additive slices C_N(h), retaining every simultaneous cutoff. The existing additive-triangle and second-Cesaro theorems are receivers, not cancellation producers. First test whether divisor inversion on each additive slice gives a stronger arithmetic constraint than the prime-order rearrangements. No pointwise Chowla estimate or unproved uniform correlation bound is available as a premise.

**Outcome: no complete-source estimate or Lean frontier advance.** Additive regrouping did not bound the signed trace. Clipping retains a terminal Mertens-square sum, and the shift attempt returns to C12.31's unproved upper mean-square estimate. The next attempt uses the exact finite divisor inverse to keep the entire new integer interval coupled to the old source. The following identities and screening argument are paper-only.

**Additive cutoff audit.** Write T_M(H)=sum_(1<=a,b<=M, a+b<=H) mu(a)*mu(b), and let T(H) have no separate a,b cutoff. For M<=H<=2M,

    T_M(H)=T(H)-2*sum_(M<a<=H-1) mu(a)*Mertens(H-a).

There are no pairs with both indices above M in this range. The subtracted term has no established sign or critical bound. Thus a one-sided inequality for T(H) cannot simply be applied to the clipped expression. For the trace cumulative sum U_N(H)=sum_(2<=h<=H) C_N(h), finite regrouping gives

    U_N(H)=sum_(k<=N) T_(floor(N/k))(floor(H/k)),
    U_N(2N)=sum_(k<=N) Mertens(floor(N/k))^2,
    S_N=U_N(2N)/(2N)+sum_(h=2..2N-1) U_N(h)/(h*(h+1)).

The endpoint contains the original Mertens square with k=1. No critical upper bound for these cumulative sums was proved. On a prime slice h=p the extra divisor sum has only its k=1 contribution (the k=p inner sum has a+b=1 and is empty), so that slice retains the complete clipped binary Mobius convolution. This does not exclude cancellation jointly across different slices; it prevents treating the divisor sum itself as that cancellation.

**Joint-shift test.** Source checks of `Sieve.AveragedChowlaInterface`, `Sieve.FejerCorrelation`, and the retrieved `Sieve.MoebiusUnweighted` statements confirm the retained correlation hypotheses and translation terms. The Fejer square is nonnegative but supplies no upper ceiling of the needed size. The curved type-II estimates concern their specified phase and range conditions; that phase was not produced for the present nonoscillatory Hilbert kernel. Fixed-ratio coprime sign supply is not a bound for this whole clipped covariance. No averaged-Chowla premise or quantitative rate was inserted. This repeats the earlier unresolved step and receives no progress credit.

**Two-variable forcing keeps the omitted interval.** For the actual arithmetic kernel B of C12.65,

    sum_(m|a,n|b) B(m,n)=1_(a=b).

Indeed, expanding B leaves two complete Mobius divisor sums, so only their common diagonal survives. Truncating both divisor coordinates at M defines R_M(a,b). For M<a<=2M the first omitted row already satisfies R_M(a,1)=-mu(a). For M<a,b<=2M,

    R_M(a,b)=B(a,b)-1_(a=b).

All proper divisors lie at most M, and the full single-divisor row sums give the displayed boundary correction. This is not an independently controlled forcing: it still contains the original source on its first omitted interval. No infinite completion or unsigned replacement of this boundary was made.

**Exact coupled integer-block recurrence.** Let M<=N<=2M, M>=1. Write Z_M for divisor incidence, T_M=Z_M^(-1), and B_M=T_M*T_M^T; here the matrix notation T_M is separate from the clipped triangle above. Let D have rows M<n<=N, columns 1<=d<=M, and D(n,d)=1_(d|n). No two distinct integers in the new interval divide one another. Consequently

    Z_N = [Z_M  0; D  I],
    Z_N^(-1) = [T_M  0; -D*T_M  I],
    B_N = [B_M  -B_M*D^T; -D*B_M  I+D*B_M*D^T].

The new diagonal block minus I is positive semidefinite; this is a lower-energy structural statement, not the required upper estimate. Put H_M(m,n)=1/(m+n) and

    phi_(M,N,m)(x)=exp(-m*x)-sum_(M<n<=N, m|n) exp(-n*x),
    K_(M,N)(m,n)=integral_0^infinity phi_(M,N,m)(x)*phi_(M,N,n)(x) dx.

The exact full trace recurrence is

    S_N-S_M=tr((K_(M,N)-H_M)*B_M)+sum_(M<n<=N)1/(2*n).

It retains every old/new mixed term through the actual B_M. The arithmetic inequality to attack is a subpower upper bound for this signed trace increment, uniformly for M<=N<=2M. No such bound has been proved or assumed; this recurrence is not a frontier deliverable on its own.

**Screened generic comparison; retained harmonic term.** A coefficient-independent subpower Loewner comparison of K_(M,2M) with H_M cannot supply the estimate. For m=1 and 1/(2M)<=x<=1/M, each of the M new atoms is at least exp(-2), so |phi_(M,2M,1)(x)|>=M*exp(-2)-1 once this is positive. Thus K_(M,2M)(1,1) grows at least linearly in M, whereas H_M(1,1)=1/2. This is an analytic family argument, not a numerical witness or a bound for the Mobius trace.

In a continuous approximation to the literal multiple sum, its main term is A_(M,N)(x)/m, where A_(M,N)(x)=integral_M^N exp(-t*x) dt. Contracting this rank-one term with B_M retains the positive quantity

    nu_M=sum_(k<=M) (1/k^2)*(sum_(r<=floor(M/k)) mu(r)/r)^2.

The coefficient integral of A_(M,2M)^2 has size M by scaling. Neither M*nu_M nor the mixed contribution of the literal rounding errors has a proved subpower ceiling here. A bound on each rounding error before Mobius inversion does not bound their signed aggregate. Next work must keep this harmonic term, its pairing with the old source, and every rounding error together in the displayed trace increment. Do not replace the actual B_M by an arbitrary positive matrix or add a generic block-inverse receiver.

**Audit.** Four research requests terminated before parsing: triangle, shifts and two-variable searches were partial; the block search returned partial=false. Snapshot file counts were 64453, 64453, 64455 and 64457; compiler-pending 48597, 48597, 48599 and 48600, stale 2660 and compiled snapshots 43. Candidate/source scopes and proposed ingredients were inspected; an unrelated Schur inverse, an arity energy that excludes the head, and a conditional correlation consumer do not control this trace. Existing divisor incidence and positivity classification were checked in source. No Lean edits/builds, numerical experiments, subagents, new axioms, heartbeat changes, umbrella builds or commits. No formal no-go retirement. Owned search outputs cleaned after recording. RH goal active and unmet.

## C12.70: harmonic boundary and signed rounding in the integer-block recurrence

**1004i outcome: no complete-source estimate and no Lean frontier advance.** C12.69's actual block recurrence was tested with a harmonic energy correction and then with cutoff averaging. Neither gives the missing signed covariance estimate. The formulas below are paper work for the next source-specific attack, not audited Lean results, a route retirement, or an RH proof/falsification.

**Harmonic correction tested with its exact error.** For real X>=1, let T_X denote the divisor inverse on integers at most X, v_X(d)=1/d, h_X=T_X^T v_X, and nu_X=||h_X||^2. Set

    c=1-log 2,
    e(t)=H_floor(2t)-H_floor(t)-log 2,
    r_X(d)=e(X/d)/d, z_X=T_X^T r_X.

The old coordinates of h_(2X) are c*h_X-z_X. The new coordinates are 1/n for X<n<=2X. Thus

    nu_(2X)=c^2*nu_X-2*c*<h_X,z_X>+||z_X||^2
              +sum_(X<n<=2X)1/n^2.

The continuous approximation suggests dissipation, since 2*c^2<1. It is not legitimate to drop z_X: writing m(y)=sum_(n<=y)mu(n)/n, the exact scalar divisor identity gives

    m(2y)=c*m(y)-sum_(d<=y)mu(d)*e(y/d)/d,
    z_X(k)=(c*m(X/k)-m(2X/k))/k.

All proper divisors of a new integer n<=2y lie at most y; swapping that finite divisor sum proves the first equality. The second follows by applying the same equality at y=X/k. An estimate obtained by substituting the desired decay of m(2X/k) would be circular. The energy correction X*nu_X therefore does not establish contraction on its own.

**Averaging test retained the actual finite window.** The corpus has exact complete-period residue covariance and a gcd-square upper bound, but they do not identify the covariance on one physical dyadic interval. The issue is visible without an asymptotic approximation. Define the zero-mean dyadic step function

    h(t)=({t}-1/2)-({2t}-1/2)/2
        =floor(2t)/2-floor(t)-1/4.

For integer M>=1 and M/2<=x<=M with x>=1, exact divisor-floor cancellation gives

    sum_(d<=M)mu(d)*h(x/d)
       =-1/2-Mertens(floor(2x))/2+Mertens(M)/4.

Indeed sum_(d<=M)mu(d)*floor(x/d)=1, while the corresponding sum with 2x equals 1-Mertens(floor(2x))+Mertens(M); omitted indices M<d<=2x have floor(2x/d)=1. Thus the finite-window dyadic source retains the first omitted Mertens increment. Its squared covariance has not been bounded. This identity is not a claim that the harmonic rounding error e(t) equals h(t)/t exactly, nor that a complete-period bound can be substituted for this window.

**Next conjecture: pay the complete centered rounding work.** To remove the continuous rank-one term exactly before estimating, define

    A_X(x)=integral_X^(2X) exp(-t*x) dt,
    b_X(x)=sum_(j>=0)c^j*A_(2^j*X)(x).

Here 0<c<1/2. The positive geometric series gives b_X=A_X+c*b_(2X), integral b_X=1, b_X(x)=X*b_1(X*x), and finite square integral. These statements follow from geometric domination at zero and exponential decay at infinity; they have not been promoted to a formal module. Write

    q_X(x)=T_X^T*( (exp(-d*x))_d - b_X(x)*v_X ),
    R_X(d,x)=sum_(X<n<=2X,d|n)exp(-n*x)-A_X(x)/d,
    C_X(d,x)=R_X(d,x)-b_(2X)(x)*r_X(d),
    U_X(x)=T_X^T*C_X(.,x).

Every C_X(d,.) has integral zero, since integral R_X(d,.)=r_X(d). The block inverse now gives the exact old-coordinate update q_(2X)=q_X-U_X; new coordinates are exp(-n*x)-b_(2X)(x)/n. For fixed a>0 set P_X=integral||q_X||^2+a*X*nu_X. Then

    P_(2X)-P_X=J_X-W_X,
    J_X=sum_(X<n<=2X)integral(exp(-n*x)-b_(2X)(x)/n)^2
          +2*a*X*sum_(X<n<=2X)1/n^2,
    W_X=2*integral<q_X,U_X>-integral||U_X||^2
          +a*X*((1-2*c^2)*nu_X+4*c*<h_X,z_X>-2*||z_X||^2).

J_X is bounded uniformly by scaling and the square integrability of b_1. Also S_floor(X)<=2*integral||q_X||^2+2*X*||b_1||_2^2*nu_X, so the complete trace is controlled by this positive potential up to a fixed factor. Using real X retains all cutoffs under repeated halving; there is no omitted odd-integer step.

The hard conjecture to attack is a one-sided subpower lower budget for this literal W_X, for every real X>=1 and every positive exponent. **No such budget has been proved.** Zero integral of C_X alone does not bound U_X or its pairing with q_X. All harmonic, mixed and squared rounding terms remain. The next attempt must prove this signed work estimate from the actual Mobius coefficients, rather than treating the geometric centering construction as frontier progress or formalizing another conditional receiver.

**Corpus and audit.** Four deep searches terminated before parsing; all were partial. The first reported only pending coverage generation 1187483. The remaining snapshots covered 64459, 64465 and 64466 files, with 48601, 48607 and 48608 compiler-pending files; each had 43 compiled snapshots and 2660 stale entries. Candidate/source statements and proposed ingredients were inspected. The hyperbola search's proposed chain incorrectly bridges a prime reciprocal sum named mertensS to signed mertensM; no such transfer was used. The potential search's sigma>1 shift contraction and unrelated Bures flow do not supply a critical source estimate. Complete-period covariance hypotheses were retained. Source reads included FloorTransformHarmonicInverse, MoebiusHarmonicTailIdentity, BurnolDyadicCoboundaryContraction, EulerDeletionCoprimeHeadSubpower, EulerDeletionMobiusPeriodCovariance, EulerDeletionPeriodAveragingObstruction and GcdSquareHarmonicBound. No source inequality, conditional input or periodic carrier was silently upgraded. No Lean edits/builds, computations, subagents, added axioms, heartbeat changes, umbrella builds or commits. Owned search outputs cleaned after recording. RH goal active and unmet.


## C12.71: complete centered rounding work on the actual divisor inverse

**1004j outcome: no unconditional source estimate and no Lean frontier advance.** Revalidated C12.70 and the current MC frontier. Tested its full signed W_X against the divisor-comparable sign law, exact cell inversion, and the logarithmic prime recursion. Neither a sign nor a subpower lower budget for W_X was proved. The following paper identities change the next calculation, but are not counted as a solved hard problem or an audited Lean theorem.

**Comparable-section test.** The checked theorem `sum_divisorPairs_antitone_weight_nonpos` requires one nonnegative antitone weight of m+n. The centered rounding kernel depends on the individual floor cells floor(X/m), floor(2X/m), floor(X/n), floor(2X/n), as well as its mixed profiles. The theorem does not directly apply to that kernel. No representation by admissible weights with a controlled residual was established, and no noncomparable section was discarded.

**Literal shell retained after inversion.** Put F_y(s)=sum_(n<=y)mu(n)*exp(-n*s), m(y)=sum_(n<=y)mu(n)/n, G_y=F_(2y)-F_y, and Q_y=F_y-b_y*m(y), using C12.70's homogeneous b_y. For k<=X and y=X/k, exact finite divisor cancellation gives

    (T_X^T R_X)_k(x)=-G_y(k*x)-A_y(k*x)*m(y),
    U_X(k,x)=-G_y(k*x)-b_y(k*x)*m(y)+b_(2y)(k*x)*m(2y)
             =Q_y(k*x)-Q_(2y)(k*x).

The identity uses sum_(a|n,a<=y)mu(a)=-mu(n) for y<n<=2y. Thus the zero-integral remainder still contains the literal new source. In particular, it is not an independently small quadrature error after inversion. The positive potential has the scalar decomposition

    P_X=sum_(k<=X) p(X/k)/k,
    p(y)=integral Q_y(s)^2 ds+a*y*m(y)^2.

This is a scope check, not an upper estimate. The generic incidence-inversion and late-prime-selection bounds returned by search supply no missing source inequality.

**Joint logarithmic test with the same centered source.** Define

    L_Y(x)=sum_(n<=Y)mu(n)*log(n)*exp(-n*x),
    ell(Y)=sum_(n<=Y)mu(n)*log(n)/n.

The corpus's actual identity mu*log=-(Lambda*mu), together with b_(Y/d)(d*x)=b_Y(x)/d, gives

    L_Y(x)-b_Y(x)*ell(Y)
      =-sum_(d<=Y)Lambda(d)*Q_(Y/d)(d*x).

Thus prime dilation respects this centering exactly. Finite Abel summation, however, retains its entire scale history:

    log(Y)*Q_Y(x)=integral_1^Y Q_t(x)/t dt
       +integral_1^Y (b_t(x)-b_Y(x))*m(t)/t dt
       -sum_(d<=Y)Lambda(d)*Q_(Y/d)(d*x).

No separate small bound for the second integral was used. The earlier C12.32 prime-delay lower bound remains unproved; applying the same identity under a new name would not advance it.

**Continuous prime term cancelled before estimating.** Define the literal discrepancy

    D_Y(x)=sum_(d<=Y)Lambda(d)*Q_(Y/d)(d*x)
             -integral_1^Y Q_(Y/t)(t*x) dt.

Finite interchange and the substitution u=n*t show

    integral_1^Y Q_(Y/t)(t*x) dt
      =integral_1^Y exp(-u*x)*m(u) du
         -b_Y(x)*integral_1^Y m(u)/u du.

Consequently the large b_Y history cancels exactly in the coupled equation:

    log(Y)*Q_Y(x)=integral_1^Y (F_t(x)/t-exp(-t*x)*m(t)) dt-D_Y(x).

This is more precise than separately bounding the history and the prime main term. It still supplies no bound for D_Y or for the C12.70 work W_X.

**Endpoint test of the discrepancy.** Away from the reciprocal endpoints t=Y/n, the function t -> Q_(Y/t)(t*x) is differentiable. On crossing t=Y/n upward it loses exactly

    mu(n)*v_Y(x), where v_Y(x)=exp(-Y*x)-b_Y(x)/Y.

Every such jump has the same profile. With E(t)=psi(t)-t, the corresponding full finite coefficient sum satisfies

    sum_(n<=Y)mu(n)*E(Y/n)=-L_Y(0)-Y*m(Y).

This follows by swapping the complete Lambda convolution. In a Stieltjes decomposition the appropriate endpoint conventions and boundary values must still be retained; no full integration-by-parts theorem is claimed here. The key issue is that the jump contribution is not a source-independent PNT error: it contains the logarithmically weighted Mertens sum. A cumulative bound on E does not control its variation or the resulting signed jump/continuous pairing. No desired critical estimate was inserted for L_Y(0), m(Y), D_Y or Q_Y.

**Next hard attack.** Keep the common endpoint profile and the full continuous part of D_Y together in the energy pairing. Test whether their arithmetic cancellation pays the negative terms of W_X. A bound on either isolated piece, another conditional receiver, or a repetition of C12.32 is insufficient. The target remains the actual one-sided subpower work estimate; no conjecture about that estimate has been declared false merely because this attempt did not prove it.

**Audit.** Three deep requests terminated before parsing, all partial. Snapshot files 64471, 64472 and 64476; compiler-pending 48611, 48612 and 48614; stale 2660 and compiled snapshots 43 each. Candidate/source arguments and proposed ingredient chains were inspected. `MobiusCenteredSchurBoundary` concerns the zeta line Re(s)=1 in the relevant limit; `DivisorSourceHarmonicBoundary` concerns the prime-free divisor defect. Neither was transferred to the half-power Mobius source. `MobiusPrimeRenewalDefectBoundary` is an exact split plus a conditional consumer. The centered prime-deficit diagonal bound retains its own signed cross term; its carrier was not identified with Q_Y. Unrelated cusp-energy source assumptions were not used. Source scopes for the divisor sign law and `Sieve.MoebiusLogRecursion` were checked directly. No computations, Lean edits/builds, new axioms, heartbeat changes, subagents, full/umbrella builds or commits. No formal route retirement. Owned search outputs cleaned after recording. RH goal active and unmet.


## C12.72: joint prime-discrepancy pairing and logarithmic-source feedback

**1004k in progress.** Previous turn made no frontier advance. Revalidated C12.71 and current MC target. Attack the endpoint and continuous prime-discrepancy terms together. Check whether their exact joint form supplies an independent energy estimate rather than a relabelling of the logarithmic Mobius source.

**Outcome: no mathematical frontier advance.** The joint Abel expansion closes exactly onto the original logarithmically weighted Mobius source. Fixed-order logarithmic estimates and the short inverse identity do not provide the missing source bound. The following are paper diagnostics, not new audited Lean results or a retirement of MC.

**Endpoint and continuous terms together.** Keep C12.71's F, Q, b, m, L, D and E=psi-id. Put

    J(u)=L_u(0)+u*m(u),   v_Y(x)=exp(-Y*x)-b_Y(x)/Y.

For each n<=Y set u=Y/n and f_n(t)=exp(-n*t*x)-b_Y(x)/(n*t). Ordinary finite Abel summation, with inclusive prime sums, gives

    sum_(d<=u)Lambda(d)*f_n(d)-integral_1^u f_n(t)dt
      =E(u)*f_n(u)+f_n(1)-integral_1^u E(t)*f_n'(t)dt.

The lower boundary is f_n(1), since E(1)=-1 and Lambda(1)=0; the formula also gives zero when u=1. Summing over n keeps every reciprocal-cutoff jump. In the continuous terms, u=n*t changes each finite inner coefficient to

    sum_(n<=u)mu(n)*E(u/n)=-J(u).

Consequently the exact combined expression is

    D_Y(x)=Q_Y(x)-v_Y(x)*J(Y)
      -x*integral_1^Y exp(-u*x)*J(u)du
      +b_Y(x)*integral_1^Y J(u)/u^2 du.

This removes the prime discrepancy but does not estimate it: J contains the original signed logarithmic source. Pairing this formula with Q_Y retains its endpoint product and both integrals. No favorable sign or subpower upper bound for their sum was obtained. Substitution into the previous recurrence supplies no independent input.

**Growing logarithmic order test.** The checked `Sieve.MoebiusHarmonicArbitraryLogRate` obtains fixed-order bounds from the existing saving exp(-(log N)^(1/3)/108). With u=log N, its absorption argument requires p*log u <= u^(1/3)/108. To make this particular (log N)^(-p) factor as small as N^(-1/2+epsilon) would instead require p*log u >= (1/2-epsilon)*u. For fixed epsilon<1/2 these requirements are incompatible at large u. This rejects adaptive substitution into that proof, not every possible uniform moment theorem. `MoebiusLogPowerHomogeneousBound` and `MoebiusShiftedLogRayAsymptotics` retain order-dependent thresholds or fixed ray/order; formal power-series Selberg identities supply no growing-order norm estimate. The RH decay-moment hit explicitly assumes RH.

**Short inverse attempted as an actual cancellation mechanism.** The corpus already proves `LogarithmicMobiusShortReconstruction.moebius_eq_short_square_correction` (declaration namespace RHTower), including the terminal product condition. With U=floor(sqrt N), summing that identity yields on paper

    M(N)=2*M(U)-N*m(U)^2+R_N,
    R_N=sum_(a,b<=U)mu(a)*mu(b)*fract(N/(a*b)).

Every a*b is at most N. The desired gain must concern the combined expression R_N-N*m(U)^2. Bounding the rounding entries by one costs U^2; the presumed power m(U)=O(U^(theta-1)) puts the main term at N^theta and gives no strict power improvement. Neither observation disproves cancellation of the combined arithmetic form. The existing short quadratic work bounds its elementary remainder, not its complete signed work. Tail-deformation symmetry and stationarity of the reconstruction action supply no extremum for this indefinite form. These issues were already present in the earlier short-work checks; their rediscovery is not new knowledge.

The Selberg diagonal lives on 1/lcm(a,b), not 1/(a+b); neither its bound nor its logarithmic variants were transferred without a comparison theorem. The corpus's squarefree product sign counts retain the signed imbalance. Character orthogonality is over full residue classes and does not erase this fixed physical product-cutoff form. No proposed search ingredient chain established the missing transfer.

**Next hard attack.** Test quantitative control of the negative part of the short product-cutoff form using the actual short Mobius vector's divisor-annihilation constraints. In particular, for b>U and b<=N,

    sum_(a<=U)mu(a)*floor(N/(a*b))=1,

because floor(N/b)<=U and the complete Mobius floor sum equals one. Try to use these constraints inside the signed form while retaining their nonzero forcing. Generic positivity is unavailable; a new receiver, another stationarity identity, or solving the constraints by an uncontrolled Mobius inverse would not count as progress. The target remains an unconditional bound on the actual source, hence on C12.70's complete work, not a spectral statement for arbitrary replacement coefficients.

**Audit.** Five deep searches terminated before parsing. Four partial; the bilinear request reported partial=false. Snapshot file counts 64480, 64480, 64486, 64487, 64487; compiler-pending 48617, 48617, 48622, 48622, 48622; each had 43 compiled snapshots and 2660 stale entries. Candidate statements, source arguments and proposed ingredient sets were inspected with these freshness limits. New direct reads included the short reconstruction, finite-entry profile, reconstruction action/tail symmetry, short quadratic work, Vaughan type-II coefficient bounds and product sign extraction. No computations, new axioms, Lean edits/builds, heartbeat changes, subagents, full/umbrella builds or commits. Owned search outputs cleaned after recording. RH goal active and unmet.

## C12.73: actual short-vector constraints and signed quadratic control

**1004l in progress.** Previous turn made no frontier advance. Revalidated the current MC Hilbert subpower target and C12.72's retained short quadratic form. Attempt to use the exact divisor-annihilation constraints of the actual Mobius vector to control that form's negative part, with every forcing and boundary contribution retained. No generic positivity or uncontrolled inverse estimate is assumed.

**Outcome: no frontier estimate.** The constraint/Gram attempt retains Mertens values in its transformed matrix. The subsequent reciprocal-phase attempt has the correct actual arithmetic phase, but leaves bounded-frequency signed cancellation open. These are paper diagnostics; no new Lean theorem is claimed.

**The constraints were used with their forcing intact.** For U=floor(sqrt N), the long rows satisfy sum_(a<=U)mu(a)*floor(N/(a*b))=1 when U<b<=N. More generally the short floor rows F(k,a)=floor(k/a), 1<=k,a<=U, satisfy F*mu=1. Their consecutive differences are the divisor incidence matrix Z(k,a)=1_(a|k), so Z*mu=e_1. This uses the actual complete-floor identity found in `FermiNymanRawMobiusTailFloor` and `BaezDuarteMobiusPrefixApproximation`; the omitted-floor-tail formula remains mandatory outside its cutoff.

Tested a positive weighted Gram comparison with F^t W F (or Z^t W Z). Its value on mu is known, respectively sum_k w_k or w_1, but the comparison with the target signed matrix still needs proof. To see the retained arithmetic content exactly, restrict for this test to N=U^2. Let

    A(a,b)=floor(U^2/(a*b)),
    T(k,a)=1_(a|k)*mu(k/a)=Z^(-1)(k,a).

Then, on paper, for 1<=r,s<=U,

    (T^t A T)(r,s)
      =M(floor(U/r))+M(floor(U/s))-M(floor(U^2/(r*s))).

Proof: put u=floor(U/r), v=floor(U/s), X=U^2/(r*s). The unequal short inverse identity mu=A_u+A_v-A_u*A_v*1 holds through floor X, since (u+1)*(v+1)>X. Summing gives exactly the displayed entry. No cutoff coefficient was dropped. In particular entry (1,1) is 2*M(U)-M(U^2), the original short-source work. Congruence transfers the Gram comparison into this Mertens matrix; it does not prove that comparison. No bound on the inverse matrix, negative spectral projection or forcing cost was obtained. The corpus's harmonic floor-transform stability explicitly assumes a critical source bound, and was not used to produce one. The coprime-energy square-dilation identity is signed and retains its cross term.

**An actual oscillatory phase, with the integer boundary paid.** Return to arbitrary integer N>=2 and U=floor(sqrt N). Define

    S_h(N)=sum_(a,b<=U)mu(a)*mu(b)*exp(2*pi*i*h*N/(a*b)).

The pointwise sawtooth series, with its midpoint value at integers, gives the finite-source identity

    R_N=(1/2)*M(U)^2
      -(1/pi)*lim_(H->infinity)sum_(1<=h<=H) Im(S_h(N))/h
      -(1/2)*sum_(a,b<=U, a*b|N)mu(a)*mu(b).

The last sum is exactly -mu(N), not an uncontrolled divisor error: apply the existing short-square coefficient identity at N, where N>U and N<(U+1)^2. Thus

    M(N)=2*M(U)-N*m(U)^2+(1/2)*M(U)^2+(1/2)*mu(N)
      -(1/pi)*lim_(H->infinity)sum_(1<=h<=H) Im(S_h(N))/h.

The finite a,b sums justify exchanging them with the pointwise Fourier limit. This is a conditional-convergence identity, not a quantitative truncation estimate. The existing `SawtoothFourierSeries` supplies the noninteger series; integer phases have zero sine terms and the correction above. The Bernoulli primitive in `RoutePTerminalModularPowerSaving` has 1/h^2 coefficients, whereas this source has 1/h. Its absolute tail estimate cannot be transferred.

**Tried the bilinear estimate on this phase.** The generic Cauchy/correlation expansion in `Sieve.BilinearCauchySchwarz` applies, but the ready-made Vaughan difference-phase theorem concerns log(1+r/u), not this reciprocal phase. On a balanced rectangle a,b comparable to U, N comparable to U^2, two b values with gap Delta give a reciprocal difference phase with second derivative of size h*Delta/U^3. The checked second-derivative test therefore gives the paper correlation envelope

    C*(sqrt(h*Delta/U)+U^(3/2)/sqrt(h*Delta)),

in its admissible curvature range, together with the trivial length bound and the diagonal. Summing that envelope through Cauchy gives the scale

    |S_h(block)| <= C*(U^(3/2)*h^(1/4)+U^2*h^(-1/4)+U^(3/2))

for the corresponding balanced block/range. This screens the method; constants, all dyadic blocks and Fourier truncation were not formalized, because it does not close the hard estimate. At fixed h the second term is U^2. Gaps Delta much smaller than U/h have little phase variation; taking absolute values of their correlations discards the actual Mobius cancellation needed there. This is a failure of that majorant, not a lower bound on the actual sum or a falsification of the desired estimate. Complete-residue Kloosterman bounds do not apply to this physical rectangle without a completion argument.

Keeping the signs and summing Fourier modes jointly is therefore essential for this attempted route. No estimate for the combined low-frequency work with -N*m(U)^2+(1/2)*M(U)^2 was obtained. The next attack will keep this combination and its moving product cutoff together, and try to control its actual near-equal-cofactor correlations. Another individual-mode power bound or matrix congruence alone does not settle it. The global Hilbert subpower target and C12.70 complete-work target remain unproved.

**Audit.** Three deep searches terminated before parsing: constraints partial=false; Gram and phase partial=true. Snapshots covered 64489, 64490, 64494 files, compiler-pending 48623, 48624, 48627; each had 43 compiled snapshots and 2660 stale entries. Candidate/source statements and proposed chains inspected. Unrelated aperture Gram positivity, monomial-frame inverse estimates and residue-class orthogonality were not transferred. Relevant source scopes included LogarithmicCoprimeEnergy, MoebiusResidualTailForm, the paired source in EulerDeletionNestedProjectionCovariance, FloorTransformHarmonicInverse, DivisorTerminalModularMean, RoutePTerminalModularPowerSaving, SawtoothFourierSeries, and the generic bilinear/second-derivative tests. No computations, Lean edits/builds, new axioms, heartbeat changes, subagents, full/umbrella builds, commits or route retirement. Owned JSON outputs cleaned after recording. RH goal active and unmet.

## C12.74: coupled low-frequency work and arithmetic completion

**1004m in progress.** Previous turn made no frontier advance. Revalidated C12.73 and the current MC energy target. Attack the joint reciprocal-phase sum with its rank terms and literal coefficient cutoffs retained. Individual-mode curvature and generic Gram positivity did not close it; seek cancellation in the actual complete arithmetic source.
