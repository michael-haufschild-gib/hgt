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

**Outcome: no frontier estimate.** Joint Abel summation retains an uncontrolled continuous argument. Integrating the short source makes the Fourier tail summable but leaves the complete low-frequency arithmetic work unbounded. Cutoff reflection and coprime-row control do not supply the missing bound. These are paper diagnostics, not new audited Lean theorems, a route retirement, or an RH proof/falsification.

**Joint modes retain their winding.** With the exact S_h(N) of C12.73 and 0<r<1, put

    L_N(r)=sum_(a,b<=U)mu(a)*mu(b)*[-log(1-r*exp(2*pi*i*N/(a*b)))].

The corpus's Abel logarithm identity gives Im L_N(r)=sum_(h>=1)r^h*Im S_h(N)/h. Each logarithm is unambiguous since its argument has positive real part. The finite product C_N(r)=prod_(a,b<=U)(1-r*exp(2*pi*i*N/(a*b)))^(mu(a)*mu(b)) satisfies exp(-L_N(r))=C_N(r). Its continuous argument starting at zero is -Im L_N(r). Replacing it by the bounded principal argument drops an integer multiple of 2*pi, precisely a term still needing control. Off-diagonal pairs make even product exponents; this does not eliminate the unwrapped argument. At resonant endpoint phases the real logarithm may diverge while the sine series retains its prescribed midpoint value. C12.73's integer correction cannot be omitted. Completing fixed numerators N/(a*b) to full residue or cyclotomic orbits would change the literal a,b<=U source; no estimate of that change was obtained.

**First integration, with all new weights paid.** For integer N>=2, U=floor(sqrt N), define

    I(N)=sum_(n<=N)mu(n)*(N-n),
    M_U=sum_(a<=U)mu(a), m_U=sum_(a<=U)mu(a)/a,
    W_U=sum_(a<=U)a*mu(a), B2(t)=fract(t)^2-fract(t)+1/6.

Integrating the existing short coefficient identity with this fixed U gives, on paper,

    I(N)=2*N*M_U-2*W_U-(N^2/2)*m_U^2+(N/2)*M_U^2-W_U^2/12
          +(1/2)*sum_(a,b<=U)a*b*mu(a)*mu(b)*B2(N/(a*b)).

Indeed sum_(k<=N/z)(N-z*k)=N^2/(2*z)-N/2+(z/2)*(fract(N/z)-fract(N/z)^2). The corpus's Bernoulli series, converted to the displayed B2 normalization, changes the final term into

    (1/(2*pi^2))*sum_(h>=1)h^(-2)*
      sum_(a,b<=U)a*b*mu(a)*mu(b)*cos(2*pi*h*N/(a*b)).

This finite-source Fourier exchange is absolutely convergent. The tail beyond H has the elementary envelope O(U^4/H); H=U pays it at O(U^3). The linear short terms also have envelope O(U^3). Neither fact controls the joint rank terms and modes 1<=h<=U: separate bounds still allow U^4. On balanced rectangles integration introduces the factor a*b of size U^2, so the C12.73 individual-mode estimate does not close the gap. No critical-scale estimate of I(N), nor a new RH transfer theorem for it, was proved. Elementary short-difference unsmoothing alone would also lose a power; faster Fourier decay must not be mistaken for cancellation of the original source.

**Cutoff increments keep the same signed work.** Let N=exp T, H=ccmPrimeDeficitDivisorSource, and A_m=ccmPrimeDeficitTruncatedAction m T. The exact residual-square identity gives, for integers m>=1,

    A_m-A_(m-1)
      =2*mu(m)*sum_(m<b<=floor(N/m))mu(b)*H(T-log(m*b))
        +mu(m)^2*H(T-2*log m).

This follows by removing the m-th coefficient from the actual tail, with the diagonal retained. Terms outside the displayed cutoff vanish by causality. Summing through floor(sqrt N) recovers D(T), since A_0=0 and every surviving pair has a coordinate below that cutoff. It gives no contraction or sign. In the alternative residual-force formula, r_m=mu_(>m)*1 and ell_m=r_m*Lambda; prime work starts only at 2*(m+1)^2. Its absence before that time estimates no retained A_m. Changing m restores exactly the displayed increments. The narrow-window cubic estimate and thick-shell diagonal estimate already in the corpus remain valid, but do not control this full cumulative sum.

**Coprime-row candidate checked at its endpoint.** The retrieved square-index estimate pays its stated block only. Write Q(t)=ccmPrimeDeficitMobiusCenteredWork t and R(t)=ccmPrimeDeficitDilationRemainder t. The full coprime row at a=1 is sum_(b<=exp T)Q(T-log b)=R(T). Hence its contribution to the complete quadratic form is Q(T)*R(T), not Q(T)^2. The full coprime form is Q(T)*R(T)+sum_(a>=2)Q(T-log a)*Row_a(T). Bounds on nontrivial rows therefore do not isolate the desired endpoint square. Subtracting the coprime cross terms restores the same unknown square; the explicit exponential/logarithmic work also remains mandatory for D(T). No coercive comparison on the actual source was established.

**Next hard test.** Keep the integrated source's rank terms and its whole low-frequency block together. The concrete unproved estimate is an O_epsilon(U^(3+epsilon)) bound for

    -(N^2/2)*m_U^2+(N/2)*M_U^2-W_U^2/12
      +(1/(2*pi^2))*sum_(1<=h<=U)h^(-2)*
        sum_(a,b<=U)a*b*mu(a)*mu(b)*cos(2*pi*h*N/(a*b)).

Attack the signed low-frequency quadratic form using its actual coefficient constraints; do not replace it by a principal argument, absolute mode sum, or unpaid inverse estimate. This is a conjectured source bound, not an established recurrence. Original MC Hilbert subpower growth and C12.70's complete signed-work inequality remain open.

**Audit.** Six deep searches terminated before parsing: joint, winding, Riesz, cutoff and action partial=true; rows partial=false. Snapshot file counts 64497, 64497, 64498, 64503, 64504, 64506; compiler-pending 48629, 48629, 48629, 48633, 48633, 48635. Each had 43 compiled snapshots and 2660 stale entries. Candidate statements, source arguments and proposed chains inspected. Unrelated reflection symmetries, opposite-debt controllers and source identities were not promoted to estimates. Additional source scopes: divisor clock product transport, Bernoulli Fourier tail, residual pairing/prime force/causality/reflection, coefficient action, shortened-cutoff window, boundary oscillator/impulse work/variation, coprime rows/head/square control and centered energy. No computations, Lean edits/builds, added axioms, heartbeat changes, subagents, full/umbrella builds, commits or route retirement. Owned JSON outputs cleaned after recording. RH goal active and unmet.

## C12.75: the joint integrated short-source form

**1004n in progress.** Previous turn made no frontier advance. Revalidated C12.74 and the current MC map. Attack the complete low-frequency form with all three rank terms retained. The hard target is cancellation in the actual short Mobius vector, not another Fourier representation or tail estimate. Test whether its source constraints give a usable bound for the full signed form, including any constants and losses needed for a scale recurrence.

**Outcome: no frontier estimate.** Neither the primitive bootstrap nor the current averaged bilinear estimates close the full signed quadratic bound. A product-cutoff extension of the comparable-pair sign law was also tested, but its required arithmetic sign remains unproved. No new Lean theorem or RH conclusion.

**The integrated kernel was kept joint.** With K_N(z)=sum_(k<=N/z)(N-z*k), C12.74's complete rank-plus-Bernoulli term is exactly -sum_(a,b<=U)mu(a)*mu(b)*K_N(a*b). This equality retains the rank terms; it does not allow bounding just the oscillating piece. Already on product ranges N/2<a*b<=N, K_N(a*b)=N-a*b. Thus the bounded modes include ordinary and first weighted short Mobius moments. They are not a high-curvature source. A full rectangle contained in that range has contribution N*(sum mu(a))*(sum mu(b))-(sum a*mu(a))*(sum b*mu(b)); a clipped rectangle retains its hyperbolic boundary. No estimate for those actual signed moments and boundary together was obtained.

Tested a scale bootstrap through I(x)=integral_0^x M(t)dt. For integer N,h>=1, its exact difference is

    I(N+h)-I(N)=h*M(N)+sum_(N<n<=N+h)mu(n)*(N+h-n).

The last absolute value is at most h*(h-1)/2. Consequently a hypothetical local bound |I(t)|<=B gives |M(N)|<=2*B/h+(h-1)/2. If B is of size N^beta, this elementary recovery has size N^(beta/2), not N^(beta-1). In particular a putative N^(3/2) primitive bound does not give N^(1/2) by this finite-difference step. The corpus's RieszTauberian theorem likewise retains an explicit increment estimate; it is not a cost-free unsmoothing theorem. This does not refute a Mellin-analytic RH consequence of a critical primitive bound. It does show why feeding this elementary recovery back into the proposed quadratic induction supplies no proved contraction. No recurrence with a better exponent, controlled constants, and all boundary terms was established.

**Averaged cancellation is not the missing rate.** Inspected the definitions, not just the headers: AveragedMeanSquare means

    eta(x,h)=sum_(a in outerBlock) |sum_(b in innerFibre(a))mu(b)|^2
               /(h^2*sqrt(x)) -> 0.

It does not assert a variance bound of order h*sqrt(x). The unconditional all-length theorem applies when h tends to infinity and h<=sqrt(x). Its proof budget contains positive inverse-logarithmic terms, including 3000/log(headNu) and an inverse log(log x) term. Choosing the window does not turn this displayed budget into a critical power saving.

At x comparable to U^2, discarding the outer Mobius sign and applying Cauchy gives an envelope of order h*U*sqrt(eta) for one admissible unweighted product band. Even if eta were uniformly controlled over all relevant bands and clipping were paid, applying this estimate absolutely over O(U/h) bands, with integrated kernel weights of order U^2, would leave an envelope of order U^4*sqrt(eta). Reaching U^(3+epsilon) by that majorant would require eta of order U^(-2+2*epsilon), which the retrieved statement does not provide. This is a diagnosis of that absolute-band argument, not a lower bound for the actual signed form, nor a claim that arbitrary clipped weighted fibres satisfy the retrieved theorem. The original rectangular coefficient cutoffs and their boundary costs have not been removed. Proposed frequency-to-average chains still assume their frequency/off-diagonal input at the stated scale.

**Product-cutoff comparable pairs were tested with their exact coefficient.** Define, on paper,

    P(X)=sum_(m|n, m<n, m*n<=X)mu(m)*mu(n).

Nonzero terms have m,n squarefree. Writing n=m*r makes m,r squarefree and coprime, with pair sign mu(r). Adding the diagonal gives a bijection onto cube-free integers q=m^2*r. Hence

    P(X)=sum_(q<=X, q cube-free)liouville(q)
          -#{m<=sqrt(X): m squarefree}.

This is an exact paper classification, not a sign theorem. The contemplated inequality P(X)<=0 therefore requires an upper bound for the complete cube-free Liouville sum. The existing MobiusDivisorMonotoneSignLaw concerns m+n<=K. Its proof sends a complementary omitted term to j=n/e and uses the fact that j*(e+1) is the next multiple after j*e; this makes that map injective. For the product boundary the conditions become j^2*e>K and j*e<=N, and distinct e may survive at the same j. No matching capacity bound for those collisions was proved. In the original short square a,b<=U, distinct comparable pairs already satisfy a*b<=U^2/2, so that law also leaves the large balanced-product region untouched.

The cube-free coefficient has local polynomial 1-z+z^2=(1-z)*(1+z^3)/(1-z^2). Its formal arithmetic factorization is mu convolved with the nonnegative sequence counting a^2*b^3, b squarefree. Thus changing to this source has not supplied independent cancellation. No one-sided RH transfer for this particular source, global sign, bound, or counterexample was asserted or formalized. This test does not retire route MC or prove a new no-go.

**Next hard attack.** Retain the outer mu(a) in the physical product-band pairing instead of estimating the absolute inner sums. Seek a signed estimate for its cumulative low-frequency work with the three C12.74 rank terms retained. The exact Ramaré denominator identity in NonRoughRamareBilinear is available; any use must retain the rough source, cross-prime terms and physical rectangular cutoff. Replacing the denominator by its mean, repeating the qualitative averaged estimate, or proving only another receiver would not settle this target. The Hilbert subpower bound and complete retained action remain open.

**Audit.** Five deep searches terminal before parsing: low, hyperbola, average, product partial=true; bootstrap partial=false. Low/bootstrap snapshots: 64510 files, 48638 compiler-pending; average: 64512 files, 48640 compiler-pending; each reported 43 compiled snapshots and 2660 stale entries. Hyperbola/product coverage was pending (generations 1188571/1188638), so no completeness claim for those searches. Candidate/source statements and proposed chains inspected; unrelated geometric bilinear forms, Riesz boundary-zero facts and Liouville-constant results were not used as arithmetic estimates. Sources checked included the short reconstruction, RieszTauberian, averaged mean-square definitions and all-length budget, exact balanced fibres, MR interface/reduction, and divisor-comparable sign-law proof. No numerical computations, Lean edits/builds, axioms, heartbeat changes, subagents, full/umbrella builds, commits or formal route retirement. Owned JSON outputs cleaned after recording. RH goal active/unmet.

## C12.76: exact prime allocation in the complete signed work

**1004o completed attempt — no frontier advance.** Previous turn made no frontier advance. Revalidated C12.75 and read the exact non-rough Ramaré identity. Tested the full signed product work using its literal prime-count denominator on both coordinates, retaining the rough source, unequal-prime terms and physical cutoff. No critical-scale source estimate resulted. The following are paper diagnostics, not new Lean theorems or a retirement of route MC.

**Double prime allocation retains the difficult pairs.** For a finite prime set P put w(n)=omega_P(n), r(n)=mu(n)*1_(w(n)=0), and b(m)=mu(m)/(1+w(m)). The exact square-multiple cancellation gives, for n>=1,

    mu(n)=r(n)-sum_(p in P, n=p*m, p not dividing m)b(m).

For any symmetric joint kernel K(a,b), inserting this on both coordinates leaves rough/rough, both rough/prime terms, and the complete double-prime sum

    sum_(p,q in P) sum_(m<=U/p, p not dividing m)
      sum_(l<=U/q, q not dividing l) b(m)*b(l)*K(p*m,q*l).

At fixed original active a,b, the equal-prime allocation has weight

    G_P(a,b)=|P(a) intersect P(b)|/(w(a)*w(b));

the unequal-prime allocation has weight 1-G_P(a,b). Thus coprime a,b>1 remain entirely in the unequal-prime term. Entrywise bounds on G do not estimate this signed form. At fixed product a*b, the existing MobiusProductFibreVariation sign law says every nonzero mu(a)*mu(b) has the same Liouville sign. Positive prime allocation preserves that sign and its total weight. For K_N(a*b) it supplies no within-product cancellation. Factoring the actual reciprocal phase h*N/(a*b) as h*N/(p*q*m*l) likewise leaves its value and bounded-mode scale unchanged. No new phase gain or off-diagonal bound was obtained.

**Joint boundary subtraction was tested, not a separate cofactor estimate.** Taking every prime through U makes the rough source just n=1, but the cofactor becomes exactly mu(m)/(1+omega(m)), whose slow boundary was already recorded in C12.21. In the absolute-convergence region sigma>1, write E(u,sigma)=product_p(1-u*p^(-sigma)) and A(sigma)=integral_0^1 E(u,sigma)du. Retaining every deleted-prime factor gives

    sum_p p^(-sigma)*integral_0^1 E(u,sigma)/(1-u*p^(-sigma))du
      =-integral_0^1 partial_u E(u,sigma)du
      =1-E(1,sigma).

Separating the first prime mass P(sigma)=sum_p p^(-sigma) leaves the exact remainder

    P(sigma)*A(sigma)
      +sum_p p^(-2*sigma)*integral_0^1 u*E(u,sigma)/(1-u*p^(-sigma))du
      =1-E(1,sigma).

Consequently subtraction of the common boundary recombines to the original Mobius series E(1,sigma). It does not produce a bound for the finite physical source. Absolute prime-square control of product_p((1-u*p^(-s))*exp(u*p^(-s))) does not continue the separate prime mass P(s) into Re(s)>1/2. No branch choice, zero-free region or contour shift was assumed. No critical estimate for the recombined remainder was proved.

**Completed nonlinear cofactors were checked as a second attack.** Read the current RouteECofactorCutoffStability, RouteEDyadicCofactorKernel and RouteECompletedDoublePairParity results. Their actual nonlinear kernel is positive, but its coefficient is mu(a)*mu(q*d), with coprimality retained. The already proved completed a,2a pair has the sign of its odd core in the far cone. Neither fact is a common sign for the full sum.

For the absolutely completed moment at s>=2, finite Euler products followed by absolute convergence give the paper expression

    C_s(a)=sum_((d,a)=1)mu(d)/d^s
          =zeta(s)^(-1)*product_(p|a)(1-p^(-s))^(-1).

For odd a, 2*C_s(2*a)-C_s(a)=((1+2^(-s))/(1-2^(-s)))*C_s(a). Hence the completed core-moment aggregate retains a positive arithmetic weight times the original outer mu(a)*a. This is not a bound on that weighted sum or on the full nonlinear kernel. It supplies no independent cancellation; no approximation was extended from the far cone to the whole source. The full nonlinear signed aggregate, near-scale region and prime/cutoff dependence remain unpaid.

**Next hard work.** Estimate the complete signed nonlinear aggregate across numerator and prime simultaneously, retaining the original cutoff and the interaction with the remaining source. Neither completing one cofactor, separating prime packets, nor bounding a positive kernel entry addresses that aggregate. A useful next result must be an actual bound on this joint source, not another equivalence or normalization identity. The subpower Hilbert estimate and unconditional RH proof/falsification remain open.

**Audit.** Three deep searches terminal and partial: exact Ramaré allocation, boundary subtraction and completed cofactors. Their snapshots reported respectively 64517/64521/64525 files and 48642/48645/48648 compiler-pending entries, with 43 compiled snapshots and 2660 stale entries. Two subsequent lexical searches located the exact cofactor-series and Route-E kernel/moment declarations. The broad boundary search was mostly unrelated; the completed search's Mobius module filter excluded the named Route-E files, corrected by the exact lexical search and direct source reads. Candidate/source arguments and proposed chains were inspected, with no completeness or applicability claim for unrelated results. One read used an abbreviated missing Sieve path; rg --files located the actual RHTower/Sieve file before reading it. No numerical computation, Lean edit/build, axiom, heartbeat change, subagent, umbrella build, commit or new formal no-go. Owned search processes terminal; outputs cleaned after recording. Goal active/unmet.

## C12.77: joint prime forcing of the complete signed source

**1004p completed attempt — no frontier estimate.** C12.76 made no frontier advance. Revalidated its exact unpaid terms. Tested summing prime forcing before estimating the complete numerator–prime aggregate. Neither that sum nor the logarithmic energy argument below produced the required source bound. All new formulas below remain paper diagnostics; no Lean theorem or RH result was added.

**The physical large-prime restriction remains.** In the completed-pair source, q is prime and a,d<q. Thus q is the unique prime factor of b=q*d above sqrt(b), and q>a. Let P retain the original allowed denominator primes, including their cutoff and any oddness restriction. Summing their log(q) contributions at fixed a,b selects the weight

    kappa_P(a,b)=sum_(q in P, q|b, q>a, b/q<q)log(q).

For squarefree b, 0<=kappa_P(a,b)<=log(b), but the omitted log(b)-kappa_P(a,b) still multiplies the signed mu(a)*mu(b) and the original kernel. The full identity mu*Lambda=-mu*log cannot replace this selected prime by all divisors at no cost. Coprimality and the original a,b cutoffs were retained. On completing the prime sum, the checked MoebiusLogRecursion and DeningerMobiusConnection give the logarithmically weighted source again. In the compensated carrier, EulerDeletionLogPrimeForcing.compensated_renewal retains logSource=-dilationPackets-forcing. Its known forcing-energy growth does not bound the cross term. No sign or estimate for the omitted source was obtained.

**A proposed general logarithmic coercivity fails before reaching the arithmetic estimate.** Let H_(m,n)=1/(m+n), D_(n,n)=log(n), and V_(n,m)=Lambda(n/m) when m divides n, zero otherwise, on 1..N. Set A=D+V. The exact logarithmic convolution gives A*mu=0. Although A is triangular with eigenvalues log(n), this supplies no coercivity in H. For S=(H*A+A^t*H)/2, already at N=3 the submatrix on indices 2,3 is

    [ log(2)/4,              (log(2)+log(3))/10 ]
    [ (log(2)+log(3))/10,   log(3)/6           ].

Writing u=log(2), v=log(3), its determinant is

    -(3*v-2*u)*(2*v-3*u)/600 < 0,

since 2*v>3*u follows from 3^2>2^3 and monotonicity of log. Hence a correction supported only on the first coordinate cannot make this form nonnegative: its negative vector can have first coordinate zero. This is an analytic finite diagnostic, not a numerical experiment or a newly formalized no-go. It rejects the attempted arbitrary-coefficient bound; it does not reject a bound using the complete actual Mobius constraints or retire route MC.

**Using the actual harmonic constraint controls the opposite direction.** The corpus proves |sum_(n<=N)mu(n)/n|<=2. For the finite Stieltjes field

    R_N(t)=sum_(n<=N)mu(n)/(n+i*t),

finite Abel summation with g(u)=u/(u+i*t), |g|<=1 and integral_1^N |g'(u)|du<=pi/2 gives |R_N(t)|<=2+pi. Define the full signed logarithmic Hilbert work

    L_N=sum_(m,n<=N)mu(m)*mu(n)*(log(m)+log(n))/(2*(m+n)).

The rational kernel identity gives

    L_N=(1/(2*pi))*integral_R log|t|*|R_N(t)|^2 dt.

For completeness, its real scalar entry follows from

    Re[1/((m-i*t)*(n+i*t))]
      =(m/(m^2+t^2)+n/(n^2+t^2))/(m+n).

Rescaling each scalar integral leaves pi*log(m); the log|u| part vanishes by u->1/u. All sums are finite and the logarithmically weighted rational integrals converge. The negative part |t|<1 is therefore bounded uniformly, giving on paper L_N>=-(2+pi)^2/pi. This is a possible auxiliary statement, not novelty-audited or Lean-verified, and was not counted as a frontier advance.

The exact prime interaction is

    W_N=sum_(d<=N)Lambda(d)*sum_(m<=N/d,n<=N)mu(m)*mu(n)/(d*m+n)
       =-L_N.

Thus the obtained direction is an upper bound for W_N. The energy argument needs a lower bound. Its unpaid part is exactly the positive integral over |t|>=1 of log|t|*|R_N(t)|^2. Uniform pointwise control of R_N does not control that expanding integral. No reversal of this inequality or critical decay of R_N was assumed.

**Next hard attack.** Use the exact finite divisor constraints on this positive high-frequency integral rather than a positivity assertion for arbitrary coefficients. For N>=1 they give

    sum_(k<=N)(1/k)*R_(floor(N/k))(t/k)=1/(1+i*t).

This relation retains every truncated field and follows coefficientwise from mu*1=delta. A useful next step must estimate the actual high-frequency mass jointly across these dilations; merely formalizing this relation or a new RH receiver would not advance MC. The complete prime-work lower bound and subpower Hilbert upper bound remain open.

**Audit.** Three deep searches terminal/partial (joint forcing, logarithmic energy, Stieltjes work), plus one exact lexical search. Snapshots respectively reported 64529/64536/64539 files and 48650/48654/48656 compiler-pending entries; 43 compiled snapshots and 2660 stale entries each. Candidate/source scopes and proposed chains inspected. Actual reads included MoebiusLogRecursion, MobiusLogDivisorParaproduct, VonMangoldtWeightAdditive, DeningerMobiusConnection 1-155, the compensated renewal and harmonic bound, and the mollified three-lines statement; the latter retains X-dependent growth and was not used as a critical estimate. An unmatched LogarithmicMobiusInverse glob was corrected by exact corpus search and rg. No numerical computation, Lean edit/build, added axiom, heartbeat change, subagent, umbrella build, commit or route retirement. All owned search processes terminal; outputs cleaned after recording. Goal active/unmet.

## C12.78: the finite Stieltjes divisor constraints and high-frequency mass

**1004q completed attempt — no frontier estimate.** Previous turn made no frontier advance. Revalidated C12.77. Tested the complete Stieltjes energy against its finite divisor identities, frequency localization, and reciprocal-source regularity. The missing upper bound was not proved. A further Liouville sign candidate is stated below with its failed induction step explicit; it is not assumed. All new calculations below are symbolic paper arguments, not numerical experiments or new Lean theorems.

**The squared divisor constraint contains the unknown diagonal.** Let E_N be the actual Hilbert energy and R_N(t)=sum_(n<=N)mu(n)/(n+i*t). Its rational Gram identity is integral_R |R_N(t)|^2 dt=2*pi*E_N. The exact divisor sum for N>=1 is

    sum_(k<=N)R_(floor(N/k))(t/k)/k=1/(1+i*t).

Consequently the normalized diagonal in the squared identity is sum_(k<=N)E_(floor(N/k))/k, and the complete unequal-dilation cross term is exactly one half minus that sum. This is cancellation of a sum already containing the unknown energies, not an upper bound for any of them. The checked Hardy Cauchy-transform orthogonality concerns opposite Hardy subspaces. These dilated rational fields have their poles on the same side; that orthogonality cannot delete their mutual cross terms.

**Frequency localization leaves the balanced arithmetic region.** For T>0 put theta_T(n)=arctan(2*T/n)-arctan(T/n). Direct integration of the rational Gram gives

    integral_T^(2*T) |R_N(t)|^2 dt
      =sum_(m,n<=N)mu(m)*mu(n)*(theta_T(m)+theta_T(n))/(m+n).

This kernel is not a function of m+n alone, so the existing antitone divisor-comparable theorem cannot be substituted. When m,n,t are comparable to T, its shape in the scaled variables is fixed. The phase of 1/(n+i*t) does not acquire a growing oscillation parameter as T grows. The harmonic pointwise bound gives an estimate proportional to the band length, not a subpower bound. No estimate for the complete signed balanced region, or a valid reduction of that region to a controlled carrier, was obtained.

**The infinite dilation limit has a compulsory boundary.** To state this without ambiguity, use S_N(z)=sum_(n<=N)mu(n)/(n+z), so R_N(t)=S_N(i*t), and m_N=sum_(n<=N)mu(n)/n. The current harmonic theorem gives m_N->0. For Re(z)>=0 the pointwise limit is the absolutely convergent expression

    S(z)=-z*sum_(n>=1)mu(n)/(n*(n+z)).

Absolute double summation then gives

    sum_(k>=1)S(z/k)/k=-z/(1+z),

whereas the finite divisor identity has right side 1/(1+z). The lost constant is exactly retained by

    sum_(k<=N)m_(floor(N/k))/k=1,
    sum_(k<=N)(S_(floor(N/k))(z/k)-m_(floor(N/k)))/k=-z/(1+z).

The latter has a uniform summable majorant of order |z|/k^2 for fixed z. In the uncompensated identity the iterated limit of the k>K tail, first N->infinity and then K->infinity, is 1. Subtracting m_N as a constant makes the finite field approach -m_N at infinite frequency, destroying its L2 decay when m_N is nonzero. Using a decaying compensator instead requires retaining the resulting dilation forcing. None of these operations bounds the original energy.

The Poisson-range classification in DeningerMobiusPoissonRangeClassification explicitly requires regularity of the canonical preimage; pointwise inversion does not supply it. MobiusReciprocalGammaFrequency gives a norm representation without an arithmetic bound. CriticalMellinBoundaryStieltjes retains its endpoint term. These source scopes do not justify an unproved reciprocal boundary regularity or a residue-free contour shift for the present source.

**Further candidate: a sign for the complete Liouville Stieltjes source.** Revalidated C12.36 and the actual complete multiplicativity and square-indicator convolution in LiouvilleDirichletSeries. Define, on paper,

    H_lambda(x)=sum_(n>=1)lambda(n)/(n*(n+x)),  x>0.

This is absolutely convergent. The square convolution gives the exact equation

    sum_(k>=1)H_lambda(x/k)/k^2
      =sum_(j>=1)1/(j^2*(j^2+x)).

The candidate is H_lambda(x)>=0. The right side is positive, but the inverse of I+T, T f(x)=sum_(k>=2)f(x/k)/k^2, has alternating Neumann terms. Its bounded-function contraction does not prove that its inverse preserves positivity. This is a proposed source sign, not a theorem or a substituted assumption. Its prospective one-sided Mellin argument would also require a full analytic audit before claiming an RH implication; no new conditional receiver was formalized.

An explicit stronger finite-prime test avoids guessing the sign of the inverse. For a finite prime set P let

    H_P(x)=sum_(n>=1 with all prime factors in P)lambda(n)/(n*(n+x)).

For p outside P, exact prime-power splitting gives

    H_(P union {p})(x)=sum_(e>=0)(-1)^e*p^(-2*e)*H_P(x/p^e).

For P empty H_P(x)=1/(1+x); for one prime the terms alternate with decreasing magnitude, proving positivity on paper. Writing g_P(x)=x^2*H_P(x) turns the update into sum_e(-1)^e*g_P(x/p^e). A nonnegative increasing g_P would give a nonnegative updated value, but that class is not preserved by this operator in general: g(x)=1_(x>=1) updates to 1 on [1,p) and 0 on [p,p^2). This does not disprove positivity for the actual g_P. It shows precisely why the attempted monotonicity induction has not closed. No sign for all finite prime sets or for H_lambda was proved.

**Next hard attack.** Prove or refute positivity for the actual finite-prime H_P family by establishing an invariant under the displayed prime-power update, retaining all exponents and the exact base kernel. Generic monotonicity is insufficient, and proving another one-prime result would not address the gap. If that candidate survives, justify the all-prime limit and its full RH connection; otherwise retain the actual counterexample and seek a weaker signed estimate. Route MC's original subpower energy target remains unchanged and open.

**Audit.** Four deep searches terminal: Stieltjes, band and Liouville partial=true; reciprocal partial=false. Snapshots reported respectively 64541/64544/64546/64548 files and 48658/48661/48663/48665 compiler-pending entries, with 43 compiled snapshots and 2660 stale entries. Candidate/source arguments and proposed chains inspected; unrelated positive-measure Stieltjes transforms, geometric Mobius maps and the Liouville constant were not used as arithmetic positivity. Source reads and harmonic zero-limit scope checked. No Lean edit/build, numerical experiment, added axiom, heartbeat change, subagent, full/umbrella build, commit or formal route retirement. All owned searches terminal and JSON outputs cleaned. Goal active/unmet.

## C12.79: actual finite-prime Liouville positivity and its induction constraints

**Turn 1004r, 2026-10-02. Route MC. No frontier estimate or new Lean theorem.** Continued C12.78's exact source candidate, rather than assuming that an Euler product or positive square forcing proves its sign. The hard target remains the complete signed half-power estimate. All results below are paper deductions, not audited Lean results. The positivity conjecture is neither proved nor refuted.

**The finite-prime candidate is not stronger than full-source positivity.** Let B_P be the squarefree positive integers whose prime factors all lie outside P. Absolute rearrangement gives

    H_P(x) = sum_(d in B_P) d^(-2) H_lambda(x/d).

Indeed the coefficient at n on the right is sum_(d|n,d in B_P) lambda(n/d). A prime outside P cancels its two adjacent exponent contributions, while primes inside P retain lambda. Absolute summation is bounded by zeta(2)^2. Thus H_lambda>=0 implies H_P>=0 for EVERY finite prime set P. Conversely, exhausting all primes and dominating each summand by 1/n^2 gives H_P(x)->H_lambda(x). Consequently the two global positivity assertions are equivalent. This corrects C12.78's description of the finite-prime assertion as stronger. It does not establish either assertion or their proposed RH transfer.

**Exact Mellin test, with every prime retained.** For 0<Re(s)<1,

    M_P(s) = integral_0^infty x^(s-1) H_P(x) dx
           = pi/sin(pi*s) * product_(p in P) (1+p^(s-2))^(-1).

If H_P>=0, its normalized vertical Mellin trace must be positive definite. In particular, with q_p=p^(sigma-2), 0<sigma<1,

    |M_P(sigma+i*t)|/M_P(sigma)
      = sin(pi*sigma)/|sin(pi*(sigma+i*t))|
        * product_(p in P) (1+q_p)/|1+q_p*exp(i*t*log p)| <= 1,

    (log M_P)''(sigma)
      = pi^2/sin(pi*sigma)^2
        - sum_(p in P) (log p)^2*q_p/(1+q_p)^2 >= 0.

Every factor in the normalized modulus product is >=1. Adding primes therefore makes this necessary test harder, not easier; the complete prime family is its maximal case. The second displayed inequality is the variance condition and is only necessary. No violating actual prime set, proof of all moment-matrix inequalities, or sufficient positivity invariant was obtained. A positive-definite dyadic squared correlation from LiouvilleDyadicGramLaw is a different source and cannot replace this linear sign condition.

The logarithm of each normalized prime factor is the absolutely convergent signed series

    sum_(k>=1) (-1)^k*q_p^k/k * (exp(i*k*t*log p)-1).

Odd grades have negative coefficients. Treating this expression as a positive compound-Poisson construction is unjustified. This observation is not a proof that its product with the exact sine factor fails positive definiteness; no such assertion is made.

**An actual-family failure of a stronger induction cone.** The tempting invariant 1<=Dg_P/g_P<=2 for g_P=x^2 H_P would in particular make J_P=x H_P increasing. This cannot hold for every finite P. From lambda=mu*squareIndicator,

    sum_(n<=N) lambda(n)/n
      = sum_(d<=sqrt N) d^(-2) m_mu(floor(N/d^2)) -> 0,

using the corpus's bounded harmonic Mobius prefixes and their zero limit, then dominated convergence with sum d^(-2)<infinity. Abel summation of this convergent harmonic Liouville series gives J_lambda(x)->0 as x->infinity. But H_lambda(0)=zeta(4)/zeta(2)>0 and continuity gives J_lambda(x)>0 for small positive x. If all J_P were increasing, their pointwise limit J_lambda would be increasing, a contradiction. Hence some actual finite-prime member fails that stronger cone. This does NOT refute H_P>=0 or the weaker candidate that g_P itself increases. Those remain the hard sign questions; there is no generic-operator-to-actual-source inference here.

**Next hard attack.** Keep the actual all-prime sign candidate. Seek a source-specific bound on the negative part after prime insertion, allowing the decline of x H_P required above and retaining all prime-power grades. The positive square forcing and finite-prime equivalence are constraints on such a proof, not cancellation estimates. Do not formalize another positivity receiver, one-prime observation or the stronger-cone failure as a substitute for the missing all-prime argument.

**Audit.** Two deep searches terminal and partial=true; first snapshot 64557 files, compiler-pending 48672; second compiler-pending 48673, both 43 compiled snapshots and 2660 stale. Lexical Liouville search also terminal. Candidate lemmas, source arguments, ingredient sets and scope inspected. Read the actual Liouville dyadic Gram law and positive-recurrence statements; neither proves the proposed sign. No Lean edit/build, numerical experiment, added axiom, heartbeat change, subagent, full/umbrella build, commit or formal route retirement. Goal active/unmet.

## C12.80: the actual square forcing under the complete signed inverse

**Turn 1004s, 2026-10-02. Route MC. No frontier estimate or new Lean theorem.** C12.79 changed the admissible induction conditions but did not solve a hard cancellation bound. This turn tested source-specific comparison for the same H_lambda; its global sign remains unproved and unrefuted. The deductions below are paper work, not Lean-audited results or a retirement of the sign candidate.

Put

    (T h)(x) = sum_(k>=2) k^(-2) h(x/k),
    f(x) = sum_(j>=1) 1/[j^2(j^2+x)],
    q = sum_(k>=2) k^(-2) = zeta(2)-1 < 1.

The strict inequality follows by comparing 1/k^2 with 1/[k(k-1)]. The source convolution gives (I+T)H_lambda=f. On bounded functions T is positive and has norm q, hence the exact expansion

    H_lambda = sum_(r>=0) (-T)^r f,
    |H_lambda(x)-sum_(r=0..K)(-T)^r f(x)| <= zeta(2)*q^(K+1).

Choosing K proportional to log x can make this remainder smaller than the critical target. It does not bound the retained alternating sum. Uniform convergence in the unweighted norm supplies no weighted half-power bound.

**The proposed positive two-step forcing fails for the actual f.** Let g=f-Tf. Then

    H_lambda = sum_(r>=0) T^(2r) g.

A proof g>=0 would establish positivity, but g is eventually negative. Indeed x*f(x)->zeta(2), whereas

    x*(Tf)(x) = sum_(k>=2) k^(-1) [(x/k)*f(x/k)] -> infinity.

For the latter conclusion restrict to 2<=k<=sqrt(x); the bracket is eventually at least zeta(2)/2 uniformly there, and the harmonic sum diverges. At zero, continuously extending f, g(0)=(1-q)*zeta(4)>0. Thus the actual forcing has both signs. No generic test function is substituted.

**Its two positive pieces cannot be estimated separately.** There is a unique rho in (1,2) with zeta(rho)=2, by the positive real Dirichlet series, its strict decrease, divergence at 1, and zeta(2)<2. Set s_*=2-rho in (0,1). On the Mellin weight x^(s_*-1) dx, T preserves the integral of every nonnegative integrable function because sum_(k>=2) k^(s_*-2)=1. Both f and Tf are integrable in this weight. Therefore g has integral zero, and g_+=max(g,0), g_-=max(-g,0) have equal strictly positive finite masses. For

    U_+ = sum_(r>=0) T^(2r) g_+,
    U_- = sum_(r>=0) T^(2r) g_-,

the sums converge pointwise (even uniformly) by q<1, but each weighted integral is infinite by nonnegative interchange and the mass-preservation identity. Their difference is exactly H_lambda. In contrast H_lambda is absolutely integrable against every x^(s-1) dx with 0<s<1, directly from |lambda(n)|<=1 and the convergent series sum n^(s-2). This identifies an actual cancellation that positive-part bounds discard; it is below the required critical range and is not claimed as a frontier advance.

**Even an explicit positive supersolution does not give inverse order.** For h_0(x)=zeta(2)/(1+x)^2,

    (I+T)h_0(x) = zeta(2)*sum_(n>=1) 1/(n+x)^2 >= zeta(2)/(1+x) >= f(x).

The first inequality is the decreasing integral comparison; the second uses j^2>=1. Nevertheless H_lambda<=h_0 everywhere is false. At zero h_0(0)>H_lambda(0)=zeta(4)/zeta(2). On real 0<s<1 the exact Mellin transforms are

    M_H(s)=pi/sin(pi*s)*zeta(4-2*s)/zeta(2-s),
    M_h0(s)=zeta(2)*Gamma(s)*Gamma(2-s),

and both tend to zeta(2) as s increases to 1. If h_0-H_lambda were nonnegative everywhere, Fatou would give its ordinary integral <=0, contradicting its strict positivity near zero. This is an order-comparison failure on the literal square source, not a disproof of H_lambda>=0.

**Source audit and next hard attack.** The LiouvilleChainFree inequalities retain sigma>1 and the displayed full Perron/sieve terms. LiouvilleCesaroUnconditional has x^sigma with sigma>=1. Neither supplies critical cancellation or a sign. ThetaRateMobiusSourceTransfer assumes all-deletion complete monotonicity and rate control; it does not produce them. A suggested complex negative-zeta interpolation argument was not established: the retrieved real-axis negativity theorem has a different domain and was not used. No claim about such level sets is made.

The remaining task is to control the SIGNED renewal sum above, preserving the equal-mass cancellation, or prove the original exact prime-power sign invariant. A promising decomposition must retain its source forcing and cannot invoke inverse positivity, split U_+ and U_-, or label a logarithmic truncation of this same unknown sum as a bound. Do not formalize these comparison failures as a substitute for that hard estimate.

**Audit.** Three deep searches terminal, all partial=true, compiler-pending 48677/48677/48678; all reported 43 compiled snapshots and 2660 stale entries. One lexical search terminal. Candidate/source arguments and ingredient-set scope inspected; no proposed retrieval chain treated as proof. No Lean edit/build, numerical experiment, added axiom, heartbeat change, subagent, full/umbrella build, commit or formal route retirement. Goal active/unmet.

## C12.81: critical forcing after reference subtraction; the required one-sided target

**Turn 1004t, 2026-10-02. Route MC. No frontier bound or new Lean theorem.** Previous turn ruled out positive-part comparison but did not control the full inverse. This turn retained the same source, subtracted an explicit reference, and checked whether positivity was an unnecessarily strong target. All deductions here are paper work. Neither the signed inverse bound nor RH is proved.

Write A=I+T, h_0(x)=zeta(2)/(1+x)^2, r=H_lambda-h_0, and R=f-Ah_0, using C12.80's exact f and T. Then A r=R. Elementary integral comparisons give, for every x>0,

    R(x) = zeta(2) * [1/x - sum_(n>=1) 1/(n+x)^2]
           - (1/x) * sum_(j>=1) 1/(j^2+x),

    0 <= R(x) + pi/(2*x^(3/2)) <= (zeta(2)+1)/x^2.

Indeed the first bracket is between zero and 1/[x(1+x)], and
0<=pi/(2*sqrt x)-sum_j 1/(j^2+x)<=1/x. These are full-sum comparisons, with neither a square tail nor an endpoint omitted. Separately C12.80 already gives R<=0 on the whole positive axis.

**The negative forcing has an explicit positive Laplace density.** Exactly

    -R(x) = integral_0^infty exp(-x*t) psi(t) dt,
    psi(t) = zeta(2)*t/(exp(t)-1) - sum_(j>=1) exp(-j^2*t)/j^2 >= 0.

The sign follows from sum_j exp(-j^2*t)/j^2<=zeta(2)*exp(-t) and t>=1-exp(-t). Thus -R is completely monotone and has the required critical decay. This is a bound for the FORCING, not its signed inverse. C12.80's literal supersolution failure already shows that A inverse need not preserve positivity even for this particular completely monotone forcing: A inverse(-R)=h_0-H_lambda is not everywhere nonnegative.

**Why a generic critical-forcing estimate does not settle the inverse.** Initially on 0<Re s<1,

    M_R(s) = pi/sin(pi*s)*zeta(4-2*s)
             - zeta(2-s)*zeta(2)*Gamma(s)*Gamma(2-s),
    M_r(s) = M_R(s)/zeta(2-s).

The physical bound above makes M_R analytic on 0<Re s<3/2, with the displayed apparent singularity at s=1 removable. If rho is a zeta zero with Re rho>1/2, then at s=2-rho the second summand vanishes while the first is nonzero: zeta(2*rho) is zero-free in Re>1 and the sine factor does not vanish. Reference subtraction therefore does not cancel such a pole. Bounding r at the critical exponent still requires the missing arithmetic estimate; analytic continuation of its numerator is insufficient.

**Global sign would impose an additional simplicity conclusion.** Assume, only to audit the proposed target, that H_lambda is eventually nonnegative. The real Mellin continuation is regular before 3/2 (including its removable point at 1); the real-strip zeta sign and Landau's positive-tail transfer extend the Mellin integral throughout 0<Re s<3/2. This excludes every zero with Re rho>1/2 and hence implies RH. Its real boundary singularity is simple:

    M_H(s) ~ C/(3/2-s),  C=-pi/[2*zeta(1/2)]>0.

For an eventually nonnegative source, the modulus of each vertical Mellin value is bounded by the real Mellin value plus a bounded compact-head correction. A critical zero rho=1/2+i*gamma of multiplicity m gives a pole of order m at 2-rho, because zeta(1+2*i*gamma) is nonzero on Re=1. The real simple-pole bound forces m<=1. Thus the proposed sign would also prove simplicity of all critical zeros. This implication is a paper deduction, not a newly formalized receiver; no logical strictness beyond RH is asserted. The goal itself does not require that extra conclusion.

**Keep the epsilon-dependent target instead.** The sufficient lower bound to attack is

    for every 0<epsilon<1/2, some C_epsilon>=0 satisfies
    H_lambda(x) >= -C_epsilon*(1+x)^(-3/2+epsilon)  for all x>0.

Equivalently one can use r, since h_0 decays as x^-2. Adding this positive comparison to H and applying the same positive-tail Landau argument only up to 3/2-epsilon excludes zeros with Re rho>1/2+epsilon; all epsilon give RH without a simplicity conclusion. Conversely the corpus's RH-to-Mertens bound and lambda=mu*squareIndicator give L_lambda(X)=O(X^(1/2+epsilon)). The zero harmonic lambda sum must be retained when estimating H:

    H_lambda(x) = -(1/x) * integral_1^infty L_lambda(t)/(t+x)^2 dt.

This follows by subtracting the zero sum lambda(n)/n before Abel summation. The displayed integral gives the corresponding two-sided x^(-3/2+epsilon) bound for 0<epsilon<1/2. Applying absolute values to the original 1/[n(n+x)] representation before this subtraction would leave an x^-1 term. This audit identifies the correct one-sided target; it does not prove it unconditionally.

**Next hard step.** Establish that lower bound for the exact signed solution of A r=R, retaining the explicit positive density psi and its full arithmetic inverse. The critical decay and complete monotonicity of -R have now been derived on paper; the missing result concerns r, not R. Do not replace that result by an inverse-order assertion, an RH-equivalent resolvent assumption, or formalization of another receiver.

**Audit.** Both deep searches terminal and partial=true. Renewal search coverage pending with background indexer running; boundary snapshot 64576 files, compiler-pending 48682, 43 compiled snapshots, 2660 stale. Candidate/source arguments and ingredient sets inspected. Read the symmetric hyperbola identity, LandauIntegralTransfer's actual positive-measure hypotheses, real-strip zeta negativity, the existing sharp-Hilbert simplicity conclusion, and mathlib's closed Re>=1 nonvanishing statement. None supplies the required inverse lower bound. No Lean edit/build, numerical experiment, added axiom, heartbeat change, subagent, full/umbrella build, commit or formal route retirement. Goal active/unmet.

## C12.82: joint arithmetic density inversion and complete prime-root constraints

**Turn 1004u, 2026-10-02. Route MC. No frontier estimate or new Lean theorem.** Tested the literal arithmetic inverse of C12.81's critical forcing, retaining the transition and tail. This did not produce the required epsilon-dependent lower bound. The work below is paper analysis, not a formal RH result or route retirement.

**Critical expansion does not pay the joint remainder.** Absolute inversion on bounded functions gives

    r(x)=sum_(n>=1) mu(n)/n^2 * R(x/n).

For x>=1, inserting C12.81's exact critical expansion only on n<=x gives

    r(x) = -pi/(2*x^(3/2))*sum_(n<=x) mu(n)/sqrt(n)
           + E_head(x) + E_tail(x),
    |E_head(x)| <= (zeta(2)+1)*floor(x)/x^2,
    |E_tail(x)| <= sup|R| * sum_(n>x) 1/n^2.

Both absolute remainders have scale x^-1. The head half-harmonic sum and the transition/tail must remain coupled; neither has been shown small enough. An asymptotic expansion for R does not justify summing its leading term over all n, where absolute convergence would fail.

**The exact density inverse returns the harmonic Liouville profile.** For every t>0, all series in

    B_psi(t)=sum_(k>=1) mu(k)/k * psi(k*t)
            =zeta(2)*t*exp(-t)-Q_lambda(t),
    Q_lambda(t)=sum_(n>=1) lambda(n)/n * exp(-n*t)

are absolutely convergent. The Bose part collapses by the corpus's exact identity sum mu(k)/(exp(k*t)-1)=exp(-t). The square part uses sum_(k*j^2=n)mu(k)=lambda(n), retaining its weight 1/n. Hence

    r(x)=-integral_0^infty exp(-x*t)*B_psi(t) dt.

Absolute interchange follows from sum |mu(k)|/k^2*(-R(x/k))<infinity. No harmonic boundary or square contribution is lost. The desired rate for the signed inverse is still unproved; this identity does not supply a small-t bound on Q_lambda.

**The located monotone-inversion theorem does not apply.** HTGeometry/MonotoneMobiusPositivity proves a lower bound for sum mu(k)/k^2*g(x/k) when g is nonnegative and NONDECREASING. Here -R is positive and decreasing. Reversing the dilation variable changes the operator, and subtracting its value at zero retains a nondecaying constant after inversion. No monotonicity premise or critical estimate was inferred from complete monotonicity. PositivePrimeDensityMobiusInversion has the same actual hypothesis. Chronological Bose remainders were not applied outside their local window or with the remaining signed arithmetic sum discarded.

**Prime multiplication: retain all additive channels.** Rechecked C12.36 before proceeding: lambda(n)*lambda(p*n)=-1 alone controls only matched pairs, not the whole Hilbert form. To keep the other channels, set F_N(z)=sum_(1<=n<=N)lambda(n)z^n. For every prime p and p-th root omega=exp(2*pi*i/p), the exact finite identity is

    sum_(j=0..p-1) F_N(omega^j*z) = -p*F_floor(N/p)(z^p).

For squarefree q, the corresponding primitive-root sum is

    sum_(a mod q, gcd(a,q)=1) F_N(exp(2*pi*i*a/q)*z)
      = mu(q)*sum_(d|q) d*F_floor(N/d)(z^d).

This follows from the full Ramanujan divisor expansion and complete multiplicativity; all cutoffs remain. It is a possible way to test a collective source estimate, not such an estimate itself. Basic Cauchy on a prime row gives

    |F_N(z)+p*F_floor(N/p)(z^p)|^2
      <= (p-1)*sum_(j=1..p-1)|F_N(omega^j*z)|^2.

The factor p-1 and the signed child term cannot be dropped. The angular mean of the radial Hilbert energy is exactly (1/2)*sum_(n<=N)1/n, by Fourier orthogonality and lambda(n)^2=1. This does not bound its value on the positive real ray: arithmetic concentration and the full cross-scale terms remain unpaid. No false transfer from matched prime edges or angular average to pointwise source energy was made.

**Next hard attack.** Test whether the complete prime-root constraints control the signed cross-scale contribution on the actual Liouville vector, rather than estimating each row or angle separately. This is an attempted new estimate for the same MC source, with the square forcing retained. Do not spend another turn building a density representation or a conditional receiver: the current inverse representations already return the original unknown source exactly.

**Audit.** Three deep searches terminal, all partial=true. Inverse snapshot 64579 files, compiler-pending48684; density search coverage pending; prime-graph snapshot64585 files, compiler-pending48687. Available snapshots report43 compiled snapshots and2660 stale. Candidate/source arguments and ingredient-set scope inspected. Read MonotoneMobiusPositivity's full monotonicity requirement, PositivePrimeDensityMobiusInversion's matching hypotheses and the actual Lambert source law. No Lean edit/build, numerical experiment, added axiom, heartbeat change, subagent, full/umbrella build, commit or formal route retirement. Goal active/unmet.

## C12.83: complete root averaging damps the source but does not bound its inverse

**Turn 1004v, 2026-10-02. Route MC. No frontier estimate or new Lean theorem.** Attempted to use C12.82's simultaneous prime-root constraints to control the actual Liouville source on the positive ray. Neither separated-angle energy nor the signed complete Ramanujan average supplied the missing bound. The following is paper analysis of this attempt, not a formal result or route retirement.

**The existing completed-cofactor result has a different source and conclusion.** `PMRamanujanComplementaryCancellation` retains all cofactors at denominator cutoff P^2 and proves relative cancellation of a growing sector by its complement. Its complete energy still has a positive-power bound; it does not prove a critical absolute bound for the Liouville root polynomial. `PMPowerDampedMobiusRamanujanQuadratic` gives an exact Gram identity and prefix comparison, not a uniform ceiling. `PMPowerDampedMobiusRamanujanCofactors` retains the exact cofactor floors/fractional parts. These results cannot be substituted for a bound on C12.82's different coefficients and cutoff-dependent child polynomials. `LiouvilleSignedCofactorDilation` likewise retains the full nondivisible residual and explicitly supplies no rate.

**Separated-angle energy does not remove the row cost.** The inspected `Sieve/LargeSieveSeparated` theorem has coefficient

    N + delta^(-1)*sum_(1<=k<=M) 1/k,   M >= 1/(2*delta).

It is not a source-specific estimate for the real ray. The prime-row Cauchy identity from C12.82 still pays p-1 and retains its signed child. No removal of that cost, pointwise control from angular mean, or sign for the complete cross-scale contribution has been proved. A sharper large-sieve theorem was not assumed from memory.

**Exact signed average and its loss of arithmetic weight.** Write c_q(n) for the Ramanujan sum, and take real a>1. Multiplicativity and the prime values c_p(n)=p-1 for p|n and -1 otherwise give

    zeta(2a)/zeta(a) * sum_(q squarefree) mu(q)*c_q(n)/q^a
      = b_a(n),
    b_a(n)=product_(p|n) (1-(p-1)*p^(-a))/(1+p^(-a)).

For each n this q-series converges absolutely. Each factor lies in [0,1]. At a decreasing to 1,

    b_a(n) -> b(n)=product_(p|n) 1/(p+1).

For F(t)=sum_n lambda(n)*exp(-n*t), t>0, the normalized sum of the *completed primitive-root rows* therefore converges to

    D(t)=sum_n lambda(n)*b(n)*exp(-n*t).

Interchange is justified at fixed a,t: the absolute q-series at coefficient n is bounded by a constant depending on a times rad(n), hence by that constant times n; the exponential n-sum converges. The limit a->1 uses 0<=b_a(n)<=1. This is a grouping of complete rows, not an absolutely summable measure of individual angular evaluations. Its total coefficient variation is proportional to sum_(q squarefree) phi(q)/q^a, which diverges for 1<a<=2, already on prime q. Consequently it does not give a bounded signed angular measure in that range.

**The small damped source is real, but does not transfer.** For every eta>0,

    sum_n b(n)/n^eta
      = product_p (1+p^(-eta)/((p+1)*(1-p^(-eta)))) < infinity.

Thus |D(t)|<=C_eta*t^(-eta) by an absolute estimate. This is not cancellation of the original lambda coefficients: b(n) has removed their large-prime mass. To track recovery exactly, put

    b'(d)=mu(d)^2*product_(p|d) p/(p+1).

Prime-power coefficients give lambda*b'=lambda*b pointwise (the right-hand multiplication here is pointwise). Consequently, with all positive integer cofactors retained,

    D(t)=sum_d b'(d)*F(d*t),
    H_D(x)=sum_d b'(d)/d^2 * H_lambda(x/d).

Both rearrangements are absolute at the displayed positive physical parameters. In the initial Dirichlet region Re s>1,

    L_(lambda*b)(s)=L_lambda(s)*B(s),
    B(s)=product_p (1+(p/(p+1))*p^(-s))
        =zeta(s)/zeta(2s)*U(s),
    U(s)=product_p (1+(p/(p+1))*p^(-s))/(1+p^(-s)).

U is an analytic nonvanishing Euler product on Re s>0: on each compact subregion its factors differ from 1 by O(p^(-1-Re s)), and neither numerator nor denominator vanishes there. The damped Dirichlet series is exactly U. The apparent improvement has canceled the original inverse-zeta factor. Recovering L_lambda requires its inversion again; no half-power estimate has been obtained.

There is also an explicit change at the harmonic boundary. The absolutely convergent positive series sum_n b(n)/n equals zeta(2), so

    H_D(x) >= (2-zeta(2))/(1+x) > 0.

This follows by separating n=1 and bounding the remaining absolute terms with n+x>=1+x. Its positive 1/x scale is not the critical decay of H_lambda, whose harmonic coefficient sum is zero. Positivity of this full cofactor average therefore cannot be transferred to inverse positivity. This is a diagnostic of the attempted averaging, not a new RH producer.

**Hard problem retained.** The needed result remains the actual full-source lower bound

    H_lambda(x) >= -C_epsilon*(1+x)^(-3/2+epsilon)

for every 0<epsilon<1/2. Equivalently, with C12.81's explicit positive critical forcing -R, the signed inverse sum sum_d mu(d)/d^2*(-R(x/d)) needs the corresponding upper budget (up to the already controlled reference). Root averaging and the damped positive source do not supply it. Continue on this joint signed estimate, retaining the transition and all cofactors; do not count another representation, damped bound, or conditional receiver as frontier progress.

**Audit.** Three deep searches terminal: root search partial=true, 64589 files/compiler-pending48690; completed-cofactor search partial=false, 64590/48691; joint-constraint search partial=true, 64598/48698. Each available snapshot reports43 compiled snapshots and2660 stale. Candidate/source arguments and ingredient scopes inspected; unrelated dilation/heat-trace suggestions were not used. All owned search outputs removed after inspection. No Lean edit/build, numerical experiment, added axiom, heartbeat change, subagent, full/umbrella build, commit, formal route retirement or RH result. Goal active/unmet.

## C12.84: the actual critical-forcing cores have both signs at late scales

**Turn 1004w, 2026-10-02. Route MC. Previous turn: no frontier estimate. This turn: no RH bound or new Lean theorem.** Tested adjacent inverse scales and then the stronger proposal of bounding the finite initial-prime inverse from above uniformly in its cutoff. The paper argument below excludes that stronger proposal and identifies a signed late-prime correction. Neither is a bound on the required complete source. Formalization remains outstanding; this is not a completed no-go card or route retirement.

Put g=-R, with the exact forcing and positive density psi from C12.81, and

    G(x)=sum_(n>=1) mu(n)/n^2*g(x/n)=h_0(x)-H_lambda(x),
    G_P(x)=sum_(d|product P) mu(d)/d^2*g(x/d),
    P_y={p prime : p<=y},  G_y=G_(P_y).

Here g(0)=g_0=zeta(2)^2-zeta(4)>0, 0<=g(x)<=g_0, and
g(x)=pi/(2*x^(3/2))+O(x^-2). In particular G_P is uniformly bounded in P,x by g_0*zeta(2).

**Adjacent-scale pairing does not supply the missing cofactor cancellation.** Pairing the factors 1 and 2 gives the exact absolutely convergent identity

    G(x)=sum_(n odd) mu(n)/n^2*[g(x/n)-g(x/(2n))/4].

For a fixed finite prime set P, its complete paired kernel satisfies

    G_P(x)=pi/(2*x^(3/2))*product_(p in P)(1-p^(-1/2))+O_P(x^-2).

Thus fixed prime pairing preserves a nonzero critical leading term; the remaining coprime cofactors still need a signed estimate. This asymptotic is not uniform in P and was not applied to a growing core. Moment-matched extraction does not pay the remaining mass: the inspected `MobiusCofactorLayerCofinal.layer_cofinal_reduction` explicitly retains an equivalent residual-source bound, and the selected packets have equal counts of the two signs. `LowBreadthMarkerTransport` covers the specified lower-tail breadth class, not the normal-breadth residual.

**Paper obstruction to a uniform one-sided initial-core bound.** Fix 1<sigma<3/2 and put alpha=2-sigma, so 1/2<alpha<1. The Mellin integral of g is absolutely convergent on this line, and M_g(sigma)>0. Finite dilation gives exactly

    M_(G_y)(s)=M_g(s)*product_(p<=y)(1-p^(s-2)).

At the real point sigma the product is positive and at most 1. At t_y=pi/log y, however,

    |product_(p<=y)(1-p^(-alpha)*exp(i*t_y*log p))|
      >= exp(c_alpha*y^(1-alpha)/log y)

eventually, for some c_alpha>0. This is the same whole-initial-prime mechanism already present in `RoutePDampedInitialPrimeEscape`: primes between sqrt(y) and y do not contract; the terminal fixed-ratio prime window contributes positive exponential gain; all smaller-prime losses are O_alpha(y^((1-alpha)/2)*log y) in the logarithm and are absorbed. The source file's `damped_initial_exponential` proves the squared-product version for 1/2<=alpha<1. Its sign convention is immaterial to the norm. Since t_y->0, continuity gives |M_g(sigma+i*t_y)|>=M_g(sigma)/2 eventually. Consequently |M_(G_y)(sigma+i*t_y)| grows faster than every fixed power of y.

Let

    P_y^+=integral_0^infinity x^(sigma-1)*max(G_y(x),0) dx,
    P_y^-=integral_0^infinity x^(sigma-1)*max(-G_y(x),0) dx.

Both are finite for each fixed y, because each finite dilation retains g's critical decay. They satisfy

    0 < P_y^+ - P_y^- = M_g(sigma)*product_(p<=y)(1-p^(-alpha)) <= M_g(sigma),
    P_y^+ + P_y^- >= |M_(G_y)(sigma+i*t_y)|.

Hence BOTH signed masses grow faster than every fixed power of y. The uniform boundedness |G_y|<=g_0*zeta(2) bounds their mass below y^A by a fixed polynomial for every A>0. Both signs therefore retain superpolynomial weighted mass beyond every such horizon. This is a statement about the actual critical-forcing cores, not arbitrary coefficients or just squared energy.

In particular, for any 0<epsilon<1/2 there is no constant C that bounds G_y(x) from above by C*(1+x)^(-3/2+epsilon) for all x,y. Choose sigma between 1 and 3/2-epsilon: that upper envelope would give a finite uniform bound for P_y^+, contradicting the preceding argument. The analogous uniform lower envelope also fails. This excludes an attempted stronger finite-core certificate; it does NOT refute the target bound for G itself.

**Positive survivor: fixed-scale convergence and the sign of late insertions.** The same cores converge uniformly in absolute value:

    |G_y(x)-G(x)| <= g_0*sum_(n>y)n^-2 <= 2*g_0/y,   y>=2,

uniformly in x>=0. Indeed the finite-core and full coefficients agree unless n has a prime factor greater than y; every such n exceeds y. Large weighted excursions can thus escape to large x without contradicting pointwise convergence.

There is also a uniform positive small-argument interval. Write L=integral_0^infinity t*psi(t)dt, which is finite and positive by the explicit exponential density bound. Then

    G_P(0)=g_0*product_(p in P)(1-p^-2) >= g_0/zeta(2),
    |G_P(u)-G_P(0)| <= L*zeta(3)*u.

Choose u_0=g_0/[2*L*zeta(2)*zeta(3)] and c_0=g_0/[2*zeta(2)]. For every finite P and 0<=u<=u_0, G_P(u)>=c_0. The exact prime insertion

    G_(P union {p})(x)-G_P(x)=-p^-2*G_P(x/p),  p notin P,

therefore has negative sign whenever p>=x/u_0. Telescoping every subsequent prime and using absolute convergence gives, for y>=max(2,x/u_0),

    c_0*sum_(p>y)p^-2 <= G_y(x)-G(x)
      <= g_0*zeta(2)*sum_(p>y)p^-2.

This is a definite sign for the complete late-prime correction. It does not estimate the earlier joint insertion work at the physical scale. In particular, an unsigned core-tail norm cannot stand in for their relative cancellation at the critical scale. Paper proof of this survivor is recorded here; its Lean status is OPEN, and no source-specific half-power bound follows from it.

**Other shortcuts checked, not adopted.** The exact stationary Fourier inversion has a specially matched multiples transform and retains its stationary cutoff; its first-harmonic collapse is not an identity for g. A squared truncated inverse retains its full product-kernel quadratic form. The elementary Stieltjes kernel 1/(x+a*b) is already indefinite on two distinct positive indices: its determinant is -x*(a-b)^2 divided by a positive denominator. That defeats a generic Gram-positivity argument, not an actual-Mobius estimate. No generic counterexample was called a counterexample to MC.

**Next hard step.** The full bound remains G(x)<=C_epsilon*(1+x)^(-3/2+epsilon). Keep the initial core and complete signed correction coupled near the physical scale. The late-prime sign above pays only that late sector; it supplies no bound for the earlier core. Do not seek a cutoff-uniform one-sided estimate over the entire positive ray: the actual-core Mellin argument rules that strengthening out on paper. Do not formalize another conditional receiver or use balanced extraction as a bound on unused atoms.

**Audit.** Four deep searches terminal. Inverse search partial=true:64605 files/compiler-pending48702, compiled43/stale2660. Transport search partial=true with coverage pending. Quadratic search partial=false:64606 files/pending48702, compiled43/stale2660. Sign-escape search partial=true with coverage pending. Candidate/source arguments and ingredient sets inspected; relevant source statements read. The existing damped initial-prime theorem concerns a different physical head; only its literal Euler-factor estimate is reused in the paper argument above. No claimed new theorem has been Lean-audited. Owned search outputs cleaned; no Lean edits/builds, numerical experiments, new axioms, heartbeat changes, subagents, full/umbrella build, commit or RH result. Goal active/unmet.

## C12.85: macroscopic transition loads of both signs and their first signed moments

**Turn 1004x, 2026-10-02. Route MC. No half-power bound or new Lean theorem.** Previous turn produced paper evidence changing the next action: a globally uniform one-sided finite-core envelope is unavailable. This turn tested extending its actual late-prime sign through the transition p comparable to x. That extension fails on the actual source: both signs contribute macroscopic transition loads. Their first continuous average cancels, but no critical remainder estimate was obtained. All new deductions below remain PAPER / Lean OPEN; no route or no-go card is declared complete.

Continue with C12.84's g=-R, G=h_0-H_lambda, and G_P its finite-prime inverse. Let G_(p-) denote the core containing every prime strictly below p. Its literal insertion at physical scale X is

    I_p(X)=G_(p)(X)-G_(p-)(X)=-p^-2*G_(p-)(X/p).

**The full inverse is absolutely integrable and has zero signed mass.** The inspected `Sieve.MoebiusHarmonicArbitraryLogRate.deningerMertensM_log_pow_rate` supplies the unconditional Mertens bound for each fixed logarithmic order. The square convolution lambda=mu*squareIndicator transfers it to L_lambda(T): split square cofactors at T^(1/4), use the chosen Mertens rate below that point, and bound the remaining square-cofactor sum by O(T^(3/4)). Hence L_lambda(T)=O_A(T/log^A T) for each fixed A.

Retaining the zero harmonic lambda sum from C12.79 gives the exact Abel identity already used in C12.81,

    H_lambda(x)=-(1/x)*integral_1^infinity L_lambda(t)/(t+x)^2 dt.

Split this integral at sqrt(x) and x. The last interval must retain its logarithmic weight: its bound is O(log^(1-A) x), not a divergent integral with the logarithm replaced by a constant. Increasing the fixed order A as needed gives

    H_lambda(x)=O_A(1/(x*log^A x)),
    integral_1^infinity |G(x)|*|log x|^k dx < infinity

for each fixed nonnegative integer k. Boundedness near zero handles the other endpoint. These are unconditional integrability statements, not half-power bounds or estimates uniform in k.

Initially for 0<Re s<1, absolute inversion gives

    M_G(s)=M_g(s)/zeta(2-s).

At s=1 the right side has a simple zero, since M_g(1)>0 and 1/zeta(2-s)=1-s+O((s-1)^2). The preceding absolute logarithmic moments justify taking the left limit and its derivative under the integral. Therefore

    integral_0^infinity G(x) dx = 0,
    integral_0^infinity G(x)*log x dx = -M_g(1) < 0.

The already proved-in-paper uniform small-argument positivity gives G>=c_0 on [0,u_0]. Its zero total mass and continuity then force a closed interval [a_-,b_-] contained in (u_0,infinity) on which G<=-delta for some delta>0. This also recovers C12.80's negative-value conclusion without a numerical test. Choose another fixed positive interval [a_+,b_+] inside (0,u_0), on which G>=c_0.

**Exact transition profile for every fixed interval.** For fixed 0<a<b, set

    J_[a,b](X)=sum_(X/b<p<=X/a, p prime) I_p(X).

Uniform convergence of the initial cores gives

    |G_(p-)(u)-G(u)| <= 2*g_0/p,
    J_[a,b](X)=-sum_(X/b<p<=X/a) p^-2*G(X/p)+O_(a,b)(X^-2).

The error retains every prime in the interval; it follows by summing p^-3, not by discarding a cofactor class. G is continuously differentiable on compact positive intervals: the density representation bounds the derivative terms by L/n^3, a summable majorant. Partial summation using the inspected `Sieve.PrimeCountingBigO.primeCounting_sub_logIntegral_isBigO` therefore yields

    X*log X*J_[a,b](X) -> -integral_a^b G(u) du.

Thus the interval [a_+,b_+] produces a negative transition block of size at least c_+/(X*log X), while [a_-,b_-] produces a positive one of size at least c_-/(X*log X), eventually with c_+,c_->0. Both blocks are literal initial-prime insertions at p proportional to X. Their size exceeds X^(-3/2+epsilon) for every fixed epsilon<1/2. C12.84's late insertion sign cannot be extended across the entire transition, and separate absolute estimates of these blocks cannot pay the target. The complete core and the other signed bands must remain in the estimate.

**Why the signed moments do not finish the argument.** On a fixed compact interval [a,b], the prime-density substitution and expansion of 1/(log X-log u) give the leading coefficients -integral_a^b G and -integral_a^b G*log u. Sending a down to zero and b to infinity in the coefficients yields zero for the first and M_g(1)>0 for the second. This is NOT a uniform expansion for a moving interval, nor an estimate for the complete original insertion history. The core replacement and prime-discrepancy errors, small-prime endpoint, and moving tail must all be controlled at the requested power. Fixed-order inverse-log decay and fixed signed moments do not provide those bounds.

In particular, choosing the logarithmic order as a function of X is not justified by the fixed-order corpus theorem. Even bounds on analytically continued signed Mellin derivatives would not on their own estimate the moving physical endpoint. No optimal-truncation claim or exchange of an expanding cutoff with an asymptotic expansion was made. C12.71--72 already show that an exact prime-discrepancy reconstruction can return the original unknown logarithmic source; that identity is not a new input here.

**Related formal deletions checked for applicability.** `RoutePCompleteRegionCriticalDeletion` bounds the complete centered-divisor label region by sqrt(M)*(1+log sqrt(M)) and leaves the moving ramps plus smooth remainder; its remaining normalized bound is explicitly equivalent to RH. `RoutePHyperbolicPairDeletion` pays d*e<=M at M^2 normalization for its signed dilation-channel square and retains every complementary pair. Neither theorem is a bound for G's Stieltjes transition or for its moving endpoint. No change of source or normalization was silently made. The already existing exact terminal split in C12.2--3 was also rechecked; its smooth-head/child covariance still needs an estimate.

**Hard target and next action.** Keep the same objective G(X)<=C_epsilon*(1+X)^(-3/2+epsilon). The actual transition has both positive and negative loads larger than this allowance. Its zero signed mass identifies leading cancellation, not a quantitative remainder. Attack the complete signed moving-endpoint/core contribution after that cancellation; do not add another fixed-window asymptotic, first-moment receiver, or per-band sign certificate and call it an RH advance.

**Audit.** Two deep searches terminal: transition partial=false with64611 files/compiler-pending48705, compiled43/stale2660; joint search partial=true with coverage pending. Candidate/source arguments and ingredient sets inspected. Read the actual route-P remainder definitions, the critical simple-jet scope, Liouville Dirichlet identity, fixed-order Mertens theorem and prime-counting error theorem. No new claim was Lean-audited. Exact owned JSON outputs cleaned. No Lean edits/builds, computations, axioms, heartbeat changes, subagents, full/umbrella build, commit or RH result. Goal active/unmet.


## C12.86 — proper-prime-power removal and the actual parameter endpoint (2026-10-02, 1004y)

**Route/status.** MC, with the C12.81 actual positive forcing `g=-R` and complete inverse `G=h0-H_lambda`. C12.85 gave signed transition-block asymptotics and fixed Mellin moments, not the required half-power bound. This attempt tests whether removing proper prime powers leaves a controllable signed prime evolution. No critical bound, new Lean theorem, RH proof or falsification was obtained. The deductions below are PAPER, Lean OPEN; this is not a completed no-go card or route retirement.

**Corpus basis.** Read `MobiusEnergyAnalyticUnitWallUniversalityLaw`, `PrimeZetaLogAsymptotic`, `SquarefreeCarlemanDeterminant`, `Sieve/PrimePowerWeightTail`, and the actual endpoint transfer/variance modules `EulerDeletionPrimeCountEndpointTransfer` and `EulerDeletionPrimeCountEndpointVariance`. The Carleman source supplies the analytic, nonzero proper-prime-power unit above real part one half. The tail theorem concerns a different von-Mangoldt/logarithmic weight and is not the needed operator estimate. Endpoint jet energy/variance is a lower bound; neither its scalar subtraction nor its exact prime-power convolution gives the missing upper bound. No such premise was silently promoted to a theorem.

**Exact signed separation, on paper.** For bounded continuous functions on `[0,infinity)`, write

```
D_n f(x) = n^(-2) f(x/n)
P = sum_prime p D_p
K = sum_prime p sum_(k>=2) D_(p^k)/k
G = exp(-P-K) g
V = exp(-P) g = exp(K) G.
```

All these operator sums and exponentials are legitimate in the unweighted sup norm: `sum_p p^-2` converges and the operators commute. The logarithm of each Euler factor `I-D_p` gives the displayed identity. On `B_a`, with norm `sup_x (1+x)^a |f(x)|`, one has `||D_n||<=n^(a-2)`. For `1<a<3/2`, the series for `K` converges in operator norm, since its first prime exponent is `2(2-a)>1`; its later prime powers are bounded by a geometric tail. Hence `exp(K)` and `exp(-K)` are bounded inverse operators on `B_a`. Two-sided critical decay of `G` and `V` is equivalent. The first-prime generator `P` has divergent positive weighted mass on that space, so this argument supplies no weighted generator bound.

The distinction between two-sided and one-sided estimates is essential. `exp(K)` is positive, so a one-sided upper bound for `G` transfers to `V`; `exp(-K)` is signed and does not give the converse order inequality. The existing Mellin/Landau reasoning can instead use a proved one-sided upper bound for `V`, because the added unit cannot cancel an off-line pole. That is a transfer argument, not a source estimate.

The exact coefficients of `V` are

```
V(x) = sum_n a(n) n^(-2) g(x/n)
a(n) = product_(p|n) (-1)^(v_p(n))/v_p(n)!.
```

On every squarefree integer, `a(n)=mu(n)`. Thus the complete squarefree source survives the separation. For `Re u>1`,

```
exp(-P(u)) = U(u)/zeta(u)
U(u) = exp(sum_p sum_(k>=2) p^(-k*u)/k)
     = zeta(2*u) * product_p (1+p^(-u))*exp(-p^(-u)).
```

The last expression identifies the unit with the corpus's Carleman determinant. `U` is holomorphic and nowhere zero for `Re u>1/2`. Consequently

```
M_V(s) = M_g(s) U(2-s)/zeta(2-s), initially 0<Re s<1.
```

At a hypothetical zero `rho` with `Re rho>1/2`, the C12.81 noncancellation of `M_g(2-rho)` and the nonvanishing of `U(rho)` remain intact. Removing proper prime powers has not paid any of the hard squarefree interaction.

**Continuous parameter attempt and its exact limit.** Set `V_tau=exp(-tau*P)g`. This is an entire parameter family in the unweighted sup norm, with

```
partial_tau V_tau(x) = -sum_p p^(-2) V_tau(x/p).
```

For `0<tau<1`, put `w=1-s` and use the local nonzero pole unit `Z(u)=(u-1)zeta(u)`, with `Z(1)=1`. For positive small `w`,

```
M_Vtau(1-w) = w^tau A_tau(w)
A_tau(w) = M_g(1-w) * exp(tau*K(1+w)) / Z(1+w)^tau
A_tau(0) = M_g(1)*exp(tau*K(1)) > 0.
```

A local analytic branch of the nonzero unit suffices here; no global zeta logarithm is assumed. The derivative in `w` is unbounded at zero. Therefore `V_tau` cannot have a two-sided bound `O((1+x)^(-a))` for any `a>1`: that bound would make its Mellin transform holomorphic near `s=1`. This does **not** refute a one-sided upper bound; a negative nonintegrable tail is compatible with such an upper bound. No eventual-sign assertion is inferred from this Mellin calculation alone.

Subtracting finitely many fractional Taylor terms leaves the first omitted noninteger singularity. Here `A_tau` cannot be a polynomial: along real `w` down to `-1/2`, `Z(1+w)` stays positive and tends to a finite nonzero value, whereas `M_g(1-w)` diverges positively by the critical forcing tail; `exp(tau*K(1+w))>=1`. A polynomial germ could not have that real continuation. Even an exact subtraction of the real branch would not remove off-line singularities. At `tau=1` the real branch becomes an ordinary zero automatically, while those possible off-line poles remain.

**Still-hard target, without a replacement premise.** A common one-sided bound

```
V_tau(x) <= C_epsilon (1+x)^(-3/2+epsilon)
for tau0 <= tau < 1, uniformly in x,
```

would pass to the endpoint, and the nonzero-unit/Landau argument would then exclude off-line zeros. No such estimate has been proved. Bounds for each fixed parameter, unweighted parameter continuity, or the endpoint jet's variance lower bound do not supply a uniform constant. The signed derivative reverses order under `P`, so an ordinary positive-semigroup comparison does not apply. The next attempt must control this actual joint squarefree derivative/remainder with the growing physical cutoff retained, rather than remove another analytic unit or accept parameterwise asymptotics as endpoint control.

**Audit.** Three deep corpus searches were run directly and reached terminal exit zero. The prime-power query was partial: 64,622 files, 48,712 compiler-pending, 43 compiled and 2,660 stale, method invalidation pending. The Carleman/unit query was partial: 64,624 files, 48,714 compiler-pending, 43 compiled and 2,660 stale, no method invalidation pending. The parameter query was partial with coverage pending, background index refresh and a reranking deadline; candidate declarations and source arguments were inspected, with no generated proof ideas or ingredient sets. Its continuity results and unrelated endpoint inequalities do not imply source control. Exact owned JSON files were cleaned after terminal completion. No Lean edit/build, numerical mathematical computation, subagent, commit, or umbrella build. Goal active and unmet.


## C12.87 — the full endpoint derivative and the retained signed exponential (2026-10-02, 1004z)

**Route and prior-turn classification.** MC. C12.86 changed the admissible next attack by exposing the real fractional branch, but did not advance the critical source estimate or produce a Lean theorem. This turn tests a direct one-sided estimate on the *actual* parameter derivative before attempting to integrate it. The one-sided endpoint bound remains the hard open problem. All new arguments below are PAPER/Lean OPEN; no route/no-go retirement or RH conclusion is claimed.

**Corpus checks.** Re-read the current MC ledger and C12.86. The derivative search suggested `MobiusFirstPrimeDilationCancellation.primeDilationGammaContribution_eq`; reading its source shows it controls the comparable `d,p*d` channel of a quadratic Gamma form, not the complete linear parameter derivative here. The suggested positive-part clamp identity supplies no arithmetic estimate. The current `Sieve/MoebiusHarmonicArbitraryLogRate` and `Sieve/PrimeCountingBigO` provide fixed logarithmic Mertens rates and the PNT error used below. The Mellin-convolution search still requires Mellin-convergent inputs; unrelated uniform cusp remainders do not bound this source. Checked `SquarefreeConvolutionHalfSelbergDelangeFactorization`: `moebiusBinomialHalf_mul_self` is genuine coefficient algebra, but it does not give a sign for a summatory half. `SquarefreeConvolutionHalfSelbergDelange` explicitly retains fractional Tauberian propositions. No half-source asymptotic or sign was assumed from the theorem names.

**Conjecture tested.** Can the positive part of `partial_tau V_tau` at the endpoint itself be paid at the critical scale? For the actual C12.86 source the answer is negative on paper, for a specific arithmetic reason, not because a generic operator fails to preserve order.

Write `V=V_1=exp(K)G`, `m=int_0^infinity g(u)du>0`, and `c=m*U(1)>0`. Then

```
partial_tau V_tau(x)|_(tau=1)
    = -sum_prime p p^(-2)*V(x/p)
    = c/(x*log(x)^2) + O(1/(x*log(x)^3)).
```

In particular this derivative is eventually positive and exceeds every fixed multiple of `(1+x)^(-a)` for any `a>1`. The conclusion concerns the derivative only. It does not refute a uniform one-sided bound for the values `V_tau`, or the desired bound for `V_1`.

**Complete paper derivation, retaining both prime tails.** First the C12.85 Abel formula can be differentiated under its absolutely convergent integral:

```
H_lambda(x) = -I_2(x)/x,
I_j(x) = int_1^infinity L_lambda(t)/(t+x)^j dt,
H_lambda'(x) = I_2(x)/x^2 + 2*I_3(x)/x.
```

The fixed-order Mertens rates and `lambda=mu*squares` give, for every fixed `A`,

```
G(x)  = O_A(x^(-1)*log(x)^(-A)),
G'(x) = O_A(x^(-2)*log(x)^(-A)).
```

For example take the input logarithmic exponent larger than `A+1` so that the tail integral for `I_2` is finite; split below and above `sqrt(x)` and `x`. Both `G` and `G'` are bounded at zero by their absolutely convergent defining series. These are fixed-order estimates, not a half-power improvement.

Let `b(n)>=0` be the coefficients of `U`, so that

```
V(x) = sum_n b(n)/n^2 * G(x/n),
sum_n b(n)/n^q < infinity for every q>1/2.
```

Split at `n=x^(3/4)` and use, for instance, the finite `q=3/5` moment. Below that cutoff the logarithm of `x/n` remains at least one quarter of `log x`; above it the coefficient tail is `O(x^(-21/20))`. For the derivative use the global bound on `u*G'(u)` to gain the extra `x^-1`, rather than the insufficient bound on `G'` alone. Thus the same displayed fixed-order bounds hold for `V,V'`. Differentiation is justified by `sum b(n)/n^3<infinity`. In particular

```
int |V(u)|*(1+|log u|^j) du < infinity  for each fixed j,
int |u*V'(u)| du < infinity,
int V(u) du = 0,
int V(u)*log u du = -c.
```

The last two identities follow either from the C12.85 moments or from the Mellin derivative at one. Fubini retains the dilation's `log n` term; it vanishes only because `int G=0`. Its absolute summability follows from a coefficient moment with exponent strictly below one.

Now split the prime sum into `p<=sqrt(x)`, `sqrt(x)<p<=x^(3/2)`, and `p>x^(3/2)`. For every fixed `A`, the small-prime part is `O_A(1/(x*log(x)^(A-1)))`, using the fixed-order bound for `V(x/p)` and even the crude harmonic integer majorant. The large-prime part is `O(x^-3/2)` by boundedness of `V` and the integer reciprocal-square tail. Neither part is silently omitted.

On the central range apply the corpus's PNT error to

```
W_x(t)=t^-2*V(x/t),
W_x'(t)=-t^-3*(2*V(x/t)+(x/t)*V'(x/t)).
```

Stieltjes integration by parts bounds the full prime-counting remainder by

```
O(x^-1*exp(-c1*sqrt(log x)))
```

for a positive PNT constant `c1`: after substituting `u=x/t`, its variation integral is bounded by `x^-1*int |2V(u)+uV'(u)|du`. Endpoint terms have the same bound since `uV(u)` is bounded. The main integral is

```
(1/x) * int_(x^-1/2)^(x^1/2) V(u)/(log x-log u) du.
```

On that complete central interval expand the reciprocal denominator through its linear term. The remainder is bounded by `2*|log u|^2/(log x)^3`. Replacing the first two truncated moments with the full ones costs a smaller fixed inverse-log error, by the already proved absolute logarithmic moments and the bounded head. The zero mass removes `1/(x log x)`; the first moment gives `-c/(x log(x)^2)`. Taking sufficiently large *fixed* `A` pays both discarded prime tails and proves the displayed derivative asymptotic. No growing-order expansion or Mellin contour shift is used.

**Learning and positive survivor.** The actual endpoint tangent has a definite positive tail, with coefficient `c=(int g)U(1)`. This is the nontrivial positive statement exposed by the failed derivative-payment conjecture. It remains a paper result whose Lean formalization is open, not a completed negative result. It forces any successful parameter argument to retain cancellation over the whole parameter interval; bounding each tangent's positive part at the target scale cannot work.

**Next conjecture tested in the same turn: complete signed truncation.** In the unweighted sup norm put `q=sum_p p^-2<1` and

```
Q_K(x)=sum_(k=0..K) (-1)^k/k! * (P^k g)(x).
||V-Q_K||_infinity <= g(0)*exp(q)*q^(K+1)/(K+1)!.
```

This pays the factorial tail at a critical physical scale with `K` of order `log x/log log x`. It does not bound the retained signed sum. Indeed its exact coefficient formula is

```
Q_K(x) = sum_(Omega(n)<=K) a(n)/n^2 * g(x/n),
a(n) = product_p (-1)^(v_p(n))/v_p(n)!.
```

There is no missing factorial damping on a squarefree coefficient: the ordered prime permutations cancel `k!`, leaving precisely `mu(n)`. For a schedule `K(x)~b*log x/log log x` with fixed `b>3/2`, every squarefree `n<=x` is retained eventually, since `n` with `k` distinct prime factors is at least `(k+1)!`. The hard ordinary squarefree head is therefore still present in full.

A finite prime cutoff can also be made explicit without dropping a source term. For `P_y=sum_(p<=y)D_p`, the unweighted exponential difference is `O(1/y)` by the bounded-operator exponential identity and `sum_(p>y)p^-2<=2/y`. The same factorial bound applies to its finite polynomial. Taking `y=x^b`, `b>3/2`, pays that prime tail as well. The remaining polynomial is finite but keeps every prime-product term at its actual argument, including products beyond `x`; no numerical evaluation was performed. No bound for its full signed value follows from paying these two tails. This is a concrete localization of the still-open estimate, not a claimed mathematical frontier advance or a new receiver module.

**Outstanding hard work.** Prove one-sided critical control of that entire signed polynomial (or of the equivalent complete parameter integral), with the normal squarefree head and all products beyond the physical cutoff retained. An upper bound on the endpoint tangent is now excluded by the actual-source asymptotic; parameter continuity, a small factorial tail, or a convolution-half identity cannot replace the signed estimate. No such estimate was obtained this turn.

**Execution audit.** Four searches reached terminal exit zero. Derivative: partial, 64,631 files, 48,718 compiler-pending, 43 compiled/2,660 stale, semantic retrieval timeout. Moments: complete retrieval with the same snapshot counts and background refresh. Interval: partial, 64,633 files, 48,719 compiler-pending, same compiled/stale counts, semantic deadline. Half: partial, 64,635 files, 48,720 compiler-pending, same compiled/stale counts, semantic timeout. All four had no method invalidation pending. Candidate lemmas, source arguments and proposed ingredient sets were inspected; no proposal was treated as a proved source estimate. All four owned JSON outputs were cleaned after terminal completion. No Lean edit/build, numerical mathematical computation, subagent, commit or umbrella build. Goal active/unmet.


## C12.88 — arithmetic order of complete Neumann remainders (2026-10-02, 1005a)

**Active paper/formalization checkpoint.** Route MC; hard target remains the complete one-sided critical inverse bound. Prior turn supplied a paper endpoint-tangent obstruction, no critical bound or Lean theorem. Current square-forcing and quadratic-error attempts must not replace a signed estimate with delayed support or positive forcing. Corpus searches and source reads confirm that the Liouville recurrence is a lower result, the prime-error observable retains weighted Liouville sums, and the Euler renewal reconstruction retains unbounded positive critical mass.

A source-specific order law emerged from the complete arithmetic inverse. Put `Z=zeta`, `R=Z-1` in the Dirichlet-convolution ring. Then `mu*R^2=Z-2+mu`, with coefficient `1+mu(n)>=0` at every n>1 and coefficient zero at0,1. As R is nonnegative, `mu*R^k>=0` coefficientwise for every k>=2. For `S_K=sum_(j=0..K)(-R)^j`, the exact remainder is `mu-S_K=mu*(-R)^(K+1)`. Consequently `S_(2m+1)<=mu<=S_(2m+2)` for every m>=0, coefficientwise. This gives genuinely one-sided complete inverse bounds against any nonnegative summable physical weight, without assuming the inverse itself is positive. It does not yet control the size of the upper polynomial when its depth grows with the physical cutoff.

**Lean result.** The dependency-closed algebra/order proof is now formalized in `MobiusNeumannOrderBounds.lean`, namespace `RHTower.MobiusNeumann`. Its seven unconditional theorems are `tailCoeff_nonneg`, `residual_two`, `residual_two_nonneg`, `residual_nonneg`, `remainder`, `odd_prefix_le`, and `le_even_prefix`. Natural-number indices are parameters, with no unproved mathematical premise. The separate transfer to an infinite physical weighted sum is a paper consequence under its summability conditions, not a theorem claimed from this leaf. In particular the degree-zero prefix is not asserted to be an upper bound.

**Validation.** Scratch proof, `lake --old build GaloisForLFunctions.RHTower.MobiusNeumannOrderBounds`, and final `lake --old env lean GaloisForLFunctions/RHTower/MobiusNeumannOrderBounds.lean` all exited zero. A separate `/tmp` import and `#print axioms` audit of all seven theorems exited zero and reported only `propext`, `Classical.choice`, and `Quot.sound`. No heartbeat change, added axiom, admitted proof, numerical mathematical computation, or full/umbrella build. The leaf is imported by the RHTower umbrella. Global `scripts/formal_tools.py lint` exited one on 11 other unreachable modules: `CCMApertureChainProfile`, `CCMApertureTranslationChains`, `CCMExponentialRampPrimeMoment`, `CCMExponentialRampSourceDissipation`, `CCMExponentialRampTerminalEntropy`, `CCMRetainedChainKernelLower`, `MoebiusMollifiedCriticalMoment`, `MoebiusMollifiedErrorThreeLines`, `ThetaMovingShellFirstOrderPhase`, `ThetaTailJointCorrelation`, and `ZetaZeroDensityPowerSaving`. No lint error named the new leaf.

**Frontier assessment.** This is a new audited arithmetic order statement found by the current corpus search, not a critical source estimate. Small unweighted remainder and complete coefficient bracketing alone leave the retained growing-depth signed polynomial uncontrolled. Next attack: prove its actual one-sided critical bound with the full ordinary squarefree head and physical tail retained. RH remains unproved and unfalsified; goal active.

**Growing-depth test, paper status only.** The arithmetic order allows an actual positive lower estimate for the error of a shallow even polynomial; it does not make that polynomial small. Write

```
U_K(x) = sum_n S_K(n)/n^2 * g(x/n),   K>=2 even,
E_K(x) = U_K(x)-G(x)
       = sum_n (mu*R^(K+1))(n)/n^2 * g(x/n) >= 0.
```

All these sums converge absolutely at every fixed K and x. The actual g from C12.81 is bounded, positive on a common head interval, and bounded by a constant times `(1+x)^(-3/2)`. Splitting its unsigned integer dilation sum at n=x therefore gives `|G(x)|<=C/x` for x>=1. No critical bound is used here.

Put `r2=mu*R^2`. Besides nonnegativity, `r2(m)=1` for every positive multiple m of4, since mu(m)=0 there. Choose A>0 so that g is at least c0>0 on `[1/(2A),1/A]`. For d<=sqrt(x), retain only multiples of4 in `A*x/d<=m<=2*A*x/d`. For sufficiently large x their count and the maximum denominator give, uniformly in d,

```
sum_m r2(m)/m^2 * g(x/(d*m)) >= c1*d/x
```

with c1>0 independent of d,x,K. There are no negative discarded terms. Expand `mu*R^(K+1)=r2*R^(K-1)` and retain every ordered tuple of K-1 factors from `{2,...,B}`. If `B^(K-1)<=sqrt(x)`, their products all satisfy the required restriction, hence

```
E_K(x) >= (c1/x) * (sum_(n=2..B) 1/n)^(K-1).
```

Choose a fixed B so large that its displayed harmonic sum exceeds both1 and `2*C/c1`. It follows that `U_K(x)>=C/x` uniformly over every even K with `2<=K<=1+log(x)/(2*log B)`, for all sufficiently large x. Thus a sublogarithmic Neumann depth cannot give the required critical upper envelope. This is a paper diagnostic of this particular approximation, not a falsification of G's desired bound or a completed route retirement.

Conversely, for `q=zeta(2)-1` in (0,1), positivity of the exact error coefficients gives

```
0 <= E_K(x) <= g(0)*q^(K+1)/zeta(2).
```

Here the coefficient sum is evaluated in the absolute-convergence chamber using the already checked Dirichlet inverse, not by continuation. Therefore a sufficiently large logarithmic depth pays the error at the critical scale. This identifies the necessary/sufficient order of approximation depth, without bounding U_K itself. In the simple schedule obtained from this sup bound, q>1/2 and a target exponent>1 imply `2^(K+1)>x`; every coefficient with n<=x is then exactly mu(n), because K+1 nontrivial factors have product at least `2^(K+1)`. The full ordinary head is still present. The hard next conjecture is an upper bound for this retained signed head together with its physical tail. The depth diagnostic and weighted transfer are not claimed as Lean theorems; only the arithmetic order result above has passed Lean.

**Search/execution audit.** Six searches finished with exit zero: square-forcing, Liouville lexical, quadratic reconstruction, Neumann order, growing-depth, and depth lexical. The four deep snapshots respectively reported 64,638/64,649/64,652/64,661 files and 48,723/48,730/48,732/48,739 compiler-pending entries, each with43 compiled snapshots,2660 stale entries and no method invalidation pending. All four were partial; semantic deadlines/reporting limits and background refresh were retained in the assessment. The two lexical responses did not expose coverage fields. Candidate lemmas, source arguments, proof ideas and proposed ingredient sets were inspected. The growing-depth proposal only reassembled the existing floor-tail identity. The checked Gaussian Neumann source requires its absolute chamber and Gaussian ratio; the growing-depth current-payment theorem leaves nonnested cores and accumulated action open. Neither controls U_K. The quadratic short reconstruction was already in the corpus and receives no novelty credit. Owned temporary search/proof/audit files are removed after terminal completion; no commit or unrelated source edit.

## C12.89 — critical comparison and complete signed centering (2026-10-02–03, 1005b–c)

**Outcome: no critical estimate.** Route MC, same hard target `G(x)<=C_epsilon*(1+x)^(-3/2+epsilon)`. C12.88 made verified arithmetic-order progress, not a critical estimate. The interrupted 1005b attempt had not made a verified frontier advance; 1005c revalidated it and completed the following paper diagnostics. These do not constitute a completed no-go or a formal route retirement. No new Lean theorem or RH result is claimed.

Use physical dilation `D_n h(x)=n^-2*h(x/n)`, `A=sum_(n>=1)D_n`, `T=A-I`, with the arithmetic `R=zeta-1` from C12.88. Testing a critical comparison barrier `B`: an exact representation

```
A B-g=T^2 h
```

would give `B-G=(mu*R^2)h` whenever the inversions and interchanges converge. If h were nonnegative, C12.88's positive coefficients would sign this gap. The proposed representation has not been constructed for the actual source.

**Why the nonnegative-source candidate fails in its stated regular class.** Take `|B(x)|<=C*(1+x)^(-a)`, a>1, and the actual bounded g with `g(x)=O((1+x)^(-3/2))`. Splitting the integer dilation sum at n=x gives `A B-g=O(1/x)`. If h is continuous, nonnegative and positive somewhere on `(0,infinity)`, it is bounded below on an interval `[b,c]` with0<b<c. For every integer `2<=r<=sqrt(x)`, retain integers m>=2 with `x/(c*r)<=m<=x/(b*r)`. For all large x these contribute at least `c1*r/x` to `sum_m m^-2*h(x/(r*m))`, uniformly in r. Multiplication by r^-2 and summing r gives

```
T^2 h(x) >= c2*log(x)/x
```

for c2>0. This contradicts that comparison identity. Continuity/nontriviality on an interval is essential to this elementary lower-tail argument; no assertion is made for arbitrary point-supported functions. The obstruction concerns this positive representation, not the desired inequality for G.

**Signed-centering survivor: exact necessary moments.** A second pass keeps h signed. Assume its Mellin integral is absolutely convergent on a left neighborhood of1 and permits the limit and first derivative at1; for example, an absolute first logarithmic moment together with a slightly stronger integrable head bound suffices. Assume B has the critical decay above and a bounded head. Set `b0=int B`, with b0>0 for a nonzero positive barrier. In the absolute-convergence chamber s<1, the full comparison identity forces

```
M_h(s) = (zeta(2-s)*M_B(s)-M_g(s))/(zeta(2-s)-1)^2.
```

Put w=1-s>0. The corpus pole unit gives `zeta(1+w)=1/w+O(1)`, while the integrability of B,g gives `M_B(1-w)=b0+O(w)` and bounded `M_g(1-w)`. Consequently

```
M_h(1-w)=b0*w+O(w^2),
int h=0,               int h(x)*log x dx=-b0.
```

The derivative conclusion follows by the explicitly assumed absolute logarithmic domination, not by differentiating an unproved continued integral. Thus a nonzero integrable positive h is also excluded directly by its zero mass. Every admissible h has both signs. These are necessary moment constraints, not an existence theorem or a bound for h.

They have a concrete positive-primitive model: let k>=0 be smooth, supported in a compact subset of `(0,infinity)`, with `int k=1`, and take any b>1. Then

```
h_model(x) = b0/log(b) * (k(x)-k(x/b)/b)
```

has precisely these two moments, and its primitive is

```
H_model(x)=b0/log(b)*int_(x/b)^x k(u)du >=0.
```

However, matching moments is insufficient to identify the actual h. Even for an actual representation with H(x)=int_0^x h>=0, coefficient positivity yields only

```
int_0^x (B(u)-G(u))du = sum_n (mu*R^2)(n)/n * H(x/n) >=0,
```

provided the displayed interchange is justified. It does not give pointwise `B-G>=0`: differentiation of a nonnegative primitive has no such implication. The surviving hard obligation is the complete signed weighted sum, not its first two moments or integrated sign. All new physical comparison/moment statements here remain PAPER/Lean OPEN. No standalone receiver or generic primitive lemma was substituted for this obligation.

**Full divisor-power attempt.** Exact finite algebra gives

```
S_K = sum_(j=0..K) (-1)^j*choose(K+1,j+1)*zeta^j.
```

Applying this to g keeps every complete divisor channel. The fixed-degree principal part at Mellin s=1 has order K for K>=1; its highest coefficient has sign `(-1)^K`. For even K its inverse-Mellin leading term is positive `(int g)*log(x)^(K-1)/((K-1)!*x)`. This is a fixed-K observation only; it does not justify a growing-K asymptotic. C12.88 already proves a stronger shallow-depth diagnostic without a contour shift. Bounding channel errors separately introduces the binomial coefficient sum `2^(K+1)-1`, and no uniform signed bound on their full sum was established. The checked `CriticalPolynomialZetaSignRigidity` concerns a critical-line Cesaro sign condition and does not control this physical polynomial. The exact Neumann polynomial is different from the earlier factor-count interpolant, so its growth theorem was not transferred.

**Other source scope checks.** `HTGeometry/MonotoneMobiusPositivity` assumes an increasing nonnegative source and does not apply to the decaying barrier error. The initially attempted RHTower path was wrong and was corrected with file inventory before reading it. `DivisorCoreMellinBoundary` subtracts a finite-core pole but asserts no physical shift or distant-head mean; `Sieve/SelbergCoefficient.selbergTruncU_nonneg` is positivity of a different sieve mass. The generated proposal joining them does not prove signed cancellation. `MobiusCenteredSchurBoundary` gives Hardy limits on the line through zeta argument1, not the desired half-power line. `CCMPrimeDeficitCoprimeBalance` bounds energy plus signed cross work; its cross-work lower bound remains unproved. The primitive search's Abel definitions and complete-period covariance retain different cutoffs or unpaid actual source terms. None discharges the current bound.

**Next attack.** Retain the complete physical signed source and its arithmetic dependence when comparing scales. The positive T² representation and first-moment/primitive replacement have failed to supply a critical estimate; do not repeat them as positivity arguments. Seek a direct estimate of the actual centered remainder, including the coupled head and tail, or an independently proved arithmetic sign for that exact remainder. The full RH goal remains active and unmet.

**Execution audit.** Six owned searches across1005b–c reached terminal exit zero: polynomial, comparison, divisor, centered, mass, primitive. All partial. Polynomial/comparison/centered reported coverage pending (generations1191484/1191509/1215359); no fresh compiler counts were inferred. Divisor/mass/primitive snapshots reported64676/64999/65002 files, compiler-pending48748/49043/49046, compiled43 and stale2660 each, no method invalidation pending; later snapshots had older-generation/semantic-coverage warnings and background refresh. Candidate lemmas, source arguments, proof ideas and ingredient sets were inspected. A premature read of centered JSON while its live search handle66867 was running failed to parse an empty file; the same handle was polled to terminal success before the result was read, with no restart. All owned searches are terminal; exact temporary outputs are cleaned after recording. No Lean source edit/build, numerical mathematical computation, subagent, commit or umbrella build in1005b–c.

## C12.90 — complete Liouville binomial sign test (2026-10-03, 1005d)

**Active checkpoint.** Route MC; previous turn did not obtain a critical signed bound. Rechecked the actual low-breadth matching theorem and C12.10/C12.39/C12.64: target reuse does not prove fresh physical capacity or change residual sign imbalance. No capacity argument is claimed. Current source-specific conjecture tests `b_k=sum_(n>=1)lambda(n)/n^2*(1-1/n)^k<=0` for every k>=1. This is a conjecture, not a fact. For `y=x/(1+x)`, the exact geometric expansion would give `H_lambda(x)=(1-y)*sum_k b_k*y^k`; the zero harmonic Liouville sum controls the endpoint and must be justified before using the sign. Corpus search and analytic sign audit in progress. No computation or Lean/RH claim at this checkpoint.

**Outcome: no critical bound.** The all-k sign remains neither proved nor refuted. Two proposed sign-preserving inductions fail by exact positive summands, not by numerical experimentation. The identities and diagnostics below are PAPER/Lean OPEN; this is not a completed no-go or route retirement. No auxiliary receiver was formalized as a substitute for the missing estimate.

**Actual source and endpoint.** The corpus's Liouville Dirichlet identity gives the finite expansion

```
b_k = sum_(j=0..k) (-1)^j choose(k,j) zeta(2*j+4)/zeta(j+2).
B(y)=sum_(k>=0)b_k*y^k=(1+x)H_lambda(x), y=x/(1+x), 0<=y<1.
```

The geometric interchange inside the disc is absolute, bounded by `zeta(2)/(1-y)`. C12.79's zero harmonic Liouville sum gives `B(y)->0` as y increases to1; an absolute interchange at y=1 is not justified by the original double series. More explicitly, C12.85's fixed-order bound for the Liouville summatory function L, applied by Abel summation to `w_k(t)=t^-2*(1-1/t)^k`, gives

```
b_k=int_1^infty L(t)*t^-4*(1-1/t)^(k-1)*(2*t-k-2)dt,
b_k=O_A(1/(k*log(k)^A)).
```

For this estimate split t at sqrt(k). The lower part is exponentially small; on the upper part `log(t)>=log(k)/2`. Substitution u=1/t bounds the remaining absolute integral by `2/k+(k+2)/(k*(k+1))`. Thus the b-series is absolutely summable for A>1 and its sum is zero. This only gives fixed logarithmic savings. The factor `2*t-k-2` changes sign, so even an unproved one-sided sign for L could not be inserted without further work.

If the conjectured `b_k<=0` for k>=1 held, B would be decreasing and concave with B(0)=b0>0 and B(1)=0. Hence `B(y)>=b0*(1-y)` and `H_lambda(x)>=b0/(1+x)^2`. Neither that sign nor the resulting RH transfer is asserted here. A weaker sufficient target is the **upper** bound `b_k<=C_epsilon*k^(-3/2+epsilon)`, for every 0<epsilon<1/2. Indeed sum b=0 gives `B(y)=sum_(k>=1)b_k*(y^k-1)`; splitting at `k~1/(1-y)` then gives the required lower bound `H_lambda(x)>=-C'_epsilon*(1+x)^(-3/2+epsilon)`. This target remains open.

**Full triangular equation.** Transforming the actual square-forcing equation `A H_lambda=f`, with `A=sum_m D_m` and `D_m h(x)=m^-2*h(x/m)`, gives

```
c_k=sum_(r>=1) r^-4*(1-1/r^2)^k,
A_kj=choose(k,j)*sum_(m>=1)m^(-j-2)*(1-1/m)^(k-j),
c_k=sum_(j=0..k)A_kj*b_j,   A_kk=zeta(k+2).
```

All sums in each fixed row are absolute. Equivalently each m-term averages b over a binomial variable with k trials and success probability 1/m, with weight m^-2. Previous negative b_j give the wrong direction for a direct upper bound on b_k.

Taking the row difference `(k+1)c_k-k*c_(k-1)` does not fix that direction. Its off-diagonal coefficient is

```
D_kj=choose(k,j)*sum_(m>=1)m^(-j-2)*(1-1/m)^(k-j-1)
                                      *(j+1-(k+1)/m), j<k.
```

For every k>=3, `D_(k,k-2)>0`: the m=1 term vanishes, the m=2 bracket is `(k-3)/2>=0`, and every m>=3 term is positive. Thus the hoped-for nonpositive off-diagonal sign is false on an entire band. Passing to cumulative coefficients `P_k=sum_(j=0..k)b_j` also leaves a positive off-diagonal band, since

```
A_(k,k-2)-A_(k,k-1)
 = (k/2)*sum_(m>=1)m^(-k-2)*(m-1)*((k-1)*(m-1)-2)>0, k>=3.
```

These facts reject the two elementary maximum-principle arguments; they do not reject the actual b sign conjecture.

**Continuous averaging retained with its exact defect.** The continuous m-integral of each A row entry is `1/(k+1)` by u=1/m and the beta integral. Define the full signed sampling error

```
R_k=sum_(j=0..k)(A_kj-delta_kj-1/(k+1))*b_j.
c_k=b_k+P_k/(k+1)+R_k.
(k+2)*P_k=sum_(j=0..k)(j+1)*(c_j-R_j).
```

The last identity follows by telescoping, with P_(-1)=0. It retains the complete integer sampling error. A critical bound on R would propagate to b through this formula, but no such bound was proved. Replacing the integer rows by their continuous integrals silently discards this very term. Expanding the m-thinning expectation back through b returns the full divisor identity `lambda*1=squareIndicator`; smoothing alone does not eliminate the arithmetic source. The next attack must estimate the actual coupled R or b at all k, not derive another criterion or promote the continuous model to an estimate.

**Corpus and execution audit.** Five owned deep searches (pairing, breadth, binomial, recurrence, thinning) reached terminal exit zero; all partial. Pairing/binomial reported coverage pending at generations1215432/1215470. Breadth/recurrence/thinning snapshots reported65007/65011/65014 files, compiler-pending49048/49051/49052, compiled43 and stale2660 each, no method invalidation pending, older-generation and semantic-coverage warnings, background refresh. Candidate lemmas, source arguments, proof ideas and ingredient sets were inspected. Recurrence's generated chain mixes `TranscendentalRateObject.liouvilleRate_recurrence` (powers of Liouville's transcendental constant) with additive Liouville correlation and Gamma-Jacobi identities; source inspection excludes this chain. The actual `LiouvilleEvenIndexPositiveRecurrence` proves cofinal positivity of additive correlations, not these binomial coefficients. Thinning's proposed energy-to-continuation chain retains its unproved finite-energy hypothesis. The square-dilation unit theorem preserves the RH wall and supplies no cancellation. A guessed `LiouvilleBinaryEulerRecurrence.lean` path did not exist; file inventory corrected it before reading `LiouvilleEvenIndexPositiveRecurrence.lean`. No Lean edit/build, numerical mathematical computation, subagent, commit or umbrella build. Owned temporary search outputs are removed after recording. RH goal remains active and unmet.


## C12.91 — complete density and quadratic-source sign test (2026-10-03, 1005e)

**Active checkpoint.** Route MC. C12.90 supplied paper evidence against two inductions, but no critical estimate. Current attack retains its full sampling error and tests whether a positive quadratic expression or the actual Laplace density J(t)=sum lambda(n)*exp(-n*t)/n can control H_lambda. H_lambda(x)=integral_0^infty exp(-x*t)*J(t)dt for x>=0 by absolute interchange. No positivity of J, finite-prime closure, quadratic domination, or RH result is assumed. Corpus search and source audit in progress.

**Outcome.** No bound on the complete sampling error, no one-sided critical density bound, and no RH proof or falsification. The new diagnostics below are PAPER/Lean OPEN, not completed no-go cards or retired routes. They change which positivity arguments can be attempted; they do not supply the missing cancellation estimate.

**The exact sampling symbol retains the unknown source.** The continuous dilation operator is `C h(x)=int_1^infty m^-2*h(x/m)dm`. The generating function of C12.90's R is `(T-C)H_lambda/(1-y)`, with x=y/(1-y), where T excludes m=1. In the common absolute Mellin chamber its multiplier is

```
zeta(2-s)-1-1/(1-s).
```

`CriticalCenteredPrimeTailSamplingAnomalyWeld` identifies exactly this zeta sampling anomaly after u=2-s and bounds its norm by `norm(u)/Re(u)`. Its separate mass-pairing theorem uses the actual Xi outgoing derivative, not H_lambda. The anomaly's analyticity does not bound its product with the unknown Mellin source. `CCMPrimeEntryWorkSampling.ccmPrimeDeficitMidpointWork_lower` is a lower bound derived from nonnegative storage plus energy; the source explicitly leaves the needed upper work estimate open. Neither was transferred as an R bound.

**Tested positive quadratic representation, retaining every term.** Let a=1*squareIndicator, so a(r) is the number of square divisors of r. The corpus divisor identity and mu*1=delta give `lambda=mu*mu*a`. Consequently, for t>0,

```
J(t)=sum_(m,n>=1) mu(m)*mu(n)/(m*n) * K(t*m*n),
K(z)=sum_(r>=1) a(r)/r * exp(-r*z).
```

All regrouping is absolute: a(r)<=r and the divisor multiplicities have polynomial bounds, while exp(-r*m*n*t) decays exponentially. This is the complete kernel, not one selected r-channel. It does not define a positive quadratic form. The elementary tail estimate

```
0<=K(z)-exp(-z)<=exp(-2*z)/(1-exp(-z))
```

gives K(z)/exp(-z)->1. For distinct fixed positive integers u,v,

```
K(t*u^2)*K(t*v^2)/K(t*u*v)^2 -> 0  as t->infinity,
```

because its leading exponential is `exp(-t*(u-v)^2)`. The two-point Gram determinant is therefore negative eventually; the factors 1/(m*n) do not change its sign. This rejects arbitrary-vector PSD payment of this full kernel. It says nothing negative about the actual value J(t), whose mu vector is fixed. The corpus's Hilbert product-fibre identity has a different kernel and retains its own signed off-diagonal work. No inequality comparing the actual two quadratic forms was proved.

**Actual prime-density induction and its failure.** For a finite set P of primes define J_P using only P-smooth n with their literal lambda coefficients. For p outside P,

```
J_(P union {p})(t)=sum_(e>=0)(-1)^e*p^-e*J_P(p^e*t).
```

The natural conjectured induction was preservation of positivity and antitonicity. For one prime, both hold: J_p is an alternating sum of decreasing positive terms, and `-J_p'(t)=sum_e(-1)^e exp(-p^e*t)>0` by pairing successive terms. Thus J_{p,q}>0 for two distinct primes, since the q-insertion again alternates decreasing positive terms. This is the positive survivor of the elementary induction test; its Lean formalization remains open here.

However, antitonicity already fails for actual two-prime sources. Take distinct primes P<=p,q<=2P and t=P^(-3/2). Grouping the derivative source by total exponent gives

```
-J_{p,q}'(t)
 = exp(-t)-exp(-p*t)-exp(-q*t)
   + sum_(a+b>=2)(-1)^(a+b)*exp(-p^a*q^b*t)
 = -1+O(P^(-1/2))+O(exp(-sqrt(P))).
```

The absolute last tail is at most `sum_(d>=2)(d+1)*exp(-P^(d-3/2))`, bounded by a constant times exp(-sqrt(P)); no term is omitted. Hence J_{p,q}' is positive there for all sufficiently large P. The inspected `Sieve/PrimeCountingBigO.primeCounting_sub_logIntegral_isBigO` supplies two such primes for all sufficiently large P. This is an analytic family, not a numerical experiment. The complete J also cannot be antitone: its harmonic Abel limit is zero at t=0, while its n=1 term makes it positive for large t. These facts do not refute J>=0 or positivity of every finite J_P. They show why the positive decreasing cone cannot carry the induction through all primes.

The suggested `PositivePrimeDensityMobiusInversion` theorem assumes an increasing nonnegative input under a different logarithmic dilation transform. It does not apply to J_P or supply the lost monotonicity. The retrieved Bernstein theorems require complete monotonicity as input. The multiplicative/Euler-product search supplies the actual coefficient algebra and absolute-convergence products, not a physical sign law.

**Critical target retained instead of the stronger sign.** A direct lower estimate `J(t)>=-C_epsilon*t^(1/2-epsilon)` near zero would imply the desired H_lambda lower bound by its Laplace representation and the exponentially decaying large-t tail. No such estimate was obtained. The exact positive square forcing is still

```
sum_(m>=1) J(m*t)/m = sum_(r>=1) exp(-r^2*t)/r^2.
```

Its absolute interchange is valid for each t>0. Positivity of the right side does not control the inverse or J's negative part. The next signed-density attack must keep every dilation term rather than impose the failed antitone cone.

**Mollifier transfer audit.** Read the actual statements of `MoebiusMollifiedCriticalMoment` and `MoebiusMollifiedErrorThreeLines`. The critical fourth-moment bound contains the complete `X^2` mean-value term; its Cauchy--Schwarz consequence permits order X (up to logarithms and the height factors) for the mollified second moment. With a fixed Gaussian window, choose the height cutoff of order sqrt(log X) to pay the displayed Gaussian tail. The existing three-lines right budget is of order X^-2, so the resulting upper budget still grows like `X^(1-3*theta)` up to logarithms, with `theta=(sigma-1/2)/(5/2)<=1/5` for sigma<=1. It supplies no convergence at the needed line. A source-specific bound on the full cofinal moment, including the signed near-equal-product terms, is still required. No sharper right-edge constant, Gaussian truncation, or formal receiver was substituted for it. The generated search chain ending at the trivial `norm_edPoly_mobCoeff_le ... <= X` also does not produce this missing control.

**Execution audit.** Five searches (sampling, quadratic, density, multiplicative, mollifier) reached terminal exit zero. Sampling/quadratic reported partial coverage pending at generations1215601/1215614. Density and mollifier were partial snapshots with65017/65024 files, compiler-pending49054/49058, compiled43 and stale2660, no method invalidation pending, older-generation/semantic-coverage warnings. Multiplicative reported partial=false,65017 files, compiler-pending49054, compiled43/stale2660, current snapshot but semantic coverage unavailable. All reported background refresh. Candidate lemmas, source arguments, proof ideas and generated ingredient sets were inspected; premises and source mismatches were retained. No Lean edit/build, numerical mathematical computation, subagent, commit or umbrella build. Exact owned search outputs are removed after recording. Goal remains active and unmet.


## C12.92 — actual exponential weight and convolution-square test (2026-10-03, 1005f)

**Active checkpoint.** Route MC, same hard one-sided bound on the full Liouville density. C12.91 changed admissible positivity arguments but did not obtain a critical estimate. Testing whether w_t(n)=exp(-n*t)/n has a real absolutely summable Dirichlet-convolution square root for each t>0. Complete multiplicativity would then make J(t) a real square. This is a conjecture, not a result; a formal coefficient root or an unproved summability premise is insufficient. The corpus's binomial half of mu is a different arithmetic function and is not substituted for this moving weight.

**New paper candidate, formalization in progress:** `../3-formalized/mc-exponential-weight-phase-zero.md` retains the full proof under audit. Twist only the prime2 value from -1 to i, then vary phases in a moving interval [aN,bN]. The base smoothed series is o(1/logN); its cofactor response has nonconstant complex argument. The strict integral triangle gap yields a linear phase capacity larger than the actual center by delta/logN, while all terms containing two band primes form an exponentially small full tail. A simple zero inside the phase disc would prohibit an absolutely summable convolution square root of the actual exponential weight. This is a no-go candidate for the square-root conjecture, with a non-trivial positive simple-zero survivor; no no-go is closed or route retired. It does not settle the literal Liouville sign or critical negative-part estimate.

**Formal positive progress:** `LiouvilleTwistedDensityPhase.lean` proves the actual full fixed-twist density has strictly different phases at u and2u for every u>log16. It then proves the strict weighted integral triangle gap on [u,2u], including a premise-free existence theorem. The infinite tail is bounded rather than discarded; the strict integral proof derives its endpoint separation from the actual coefficients. Targeted leaf build, direct `lake --old env lean` audit, and a `/tmp` audit of all13 public theorems passed. Axioms are only `propext`, `Classical.choice`, `Quot.sound`. The leaf is wired into `RHTower.lean`. Global formal lint exited1 on13 other unreachable modules; no error for the new leaf. No umbrella build, heartbeat increase, numerical mathematical computation, subagent or commit.

**Hard gap and next exact obligation:** the full simple-zero survivor is not yet formalized. Its fixed-log center estimate follows on paper from the exact square and prime-two harmonic convolutions, with split-tail or logarithmic-moment domination proofs recorded in the dedicated card. Next formal work must discharge that actual center and the moving-prime weighted limit before applying the sphere-zero lemma. The unchanged RH-producing problem is still the one-sided half-power bound for the literal J_lambda; no critical estimate was proved in this cycle.

**Search audit:** seven searches reached terminal exit0: dilation, root, phase, prime-integral, Liouville rate, strict integral triangle, logarithmic convolution. Four were partial; root, Liouville rate and logarithmic convolution reported partial=false. Snapshots ranged65028–65041 inventoried files, compiler-pending49058–49065, compiled43/stale2660, with no method invalidation pending. All reported background refresh; all except root had older-generation warnings, and all except phase also reported semantic coverage unavailable. Candidate lemmas, source arguments, proof ideas and ingredient sets were inspected. Generated chains through zero transverse force, unrelated L-character zeros, fourth moments, or zero-configuration log moments retained their missing premises or source mismatch and were not used as theorems. Relevant actual source statements were read, and used analytic names/proofs were checked in `/tmp`. Owned search and Lean scratch files are removed after recording; no owned process remains.

### C12.92 continuation — actual twisted center and two-interval capacity plan (2026-10-04, 1005g)

**Verified advance:** `LiouvilleTwistedHarmonicDecay.lean` proves the complete harmonic square-dilation identity, the exact prime-two convolution, and the unconditional limits log(N+1)*H_lambda(N)->0 and log(N+1)*H_f(N)->0. `LiouvilleTwistedDensityCenter.lean` proves the exact full Abel identity and log(N+1)*F(1/(N+1)^2)->0 without any analytic or arithmetic premise. Summable logarithmic kernel moments carry the actual signed cancellation; the exponential proof retains both the entire short sum and entire tail. Thus the cofinal center obligation in the candidate simple-zero argument is now discharged. This is progress on the actual convolution-root obstruction, not the critical Liouville lower bound.

**New paper simplification:** two compact phase-separated intervals suffice. For ideal cofactor responses B_p=F(p/T)/p, the exact identity S^2-|Z|^2=sum_(p,q)(|B_p||B_q|-Re(conj(B_p)*B_q)) retains all terms. Uniform positive cross-interval phase defect, reciprocal prime mass >=c/logT in each interval, and S<=C/logT give S-|Z|>=c'/logT. The already inspected `HTGeometry.eventually_primeCount_window_ge` supplies the required prime-counting lower input; `pi_alt'` supplies the upper input. No weighted prime-integral limit is necessary. Total absolute cofactor error transfers this gap to the actual center. This capacity proof is still paper-only. The detailed card retains the exact errors and remaining full nonlinear/simple-zero obligations.

**Analytic simplification:** for each fixed t>0, take 1<R<exp(t). The elementary band-degree bound d(n)<=n gives geometric domination of the full series and derivative on |z|<=R, enough for holomorphy around the closed unit disc. Entire continuation and a logarithmic degree estimate need not precede the simple-zero proof. No nonlinear term is discarded.

**Validation and limits:** both targeted leaf builds and both direct `lake --old env lean` audits passed. All14 public theorems passed a combined `/tmp` axiom audit with only propext/Classical.choice/Quot.sound. Both leaves are wired into RHTower; no umbrella build. Global formal lint exits1 on14 other umbrella-reachability errors, with none for these leaves. Five searches completed, two partial=false and three partial,65045–65072 files, compiled43/stale2660/compiler-pending49066–49081, all with snapshot/semantic-coverage warnings and background refresh. Candidate/source/method/ingredient outputs were inspected and used statements checked directly. No added axiom, placeholder, heartbeat raise, numerical mathematical experiment, subagent or commit by this work. Owned temporary files are cleaned after recording. Next actual hard step is the two-interval prime-phase capacity plus exact full band decomposition; the simple-zero survivor, literal J_lambda half-power lower bound and RH remain unproved. Goal active/unmet.

### C12.92 continuation — actual prime capacity and complete band source (2026-10-04, 1005h)

**Verified advance:** four new audited leaves close the actual two-interval capacity and complete band-source obligations. `LiouvilleTwistedPrimeCapacity.lean` proves, without arithmetic or analytic premises, that two fixed intervals above1 have a positive actual-density angular defect and that log(T)*(sum|B_p|-|sum B_p|)>=kappa>0 eventually, where B_p=F(p/T)/p. The ordinary PNT and exact full finite pairwise deficit supply the proof; no moving weighted-integral assumption remains.

`LiouvillePrimeBandAlgebra.lean` gives the exact monomial character and degree decomposition, counting repeated primes. `LiouvillePrimeBandAnalysis.lean` bounds every excluded cofactor and the complete nonlinear source and derivative; the latter are both at most (T+1)*exp(-T). `LiouvillePrimeBandDecomposition.lean` reindexes every n=p*m and proves W(z)=C+z*sum_P beta_p*A_p+R(z), plus the actual baseline F=C-sum_P A_p+E. Thus the ideal response, exact cofactor response and actual source now have an audited connection; no prime square or unknown tail was omitted.

**Next exact target:** transfer the ideal gap by sum|A_p-B_p| and the already-proved cofinal center. Then align the actual A_p, use a moving circle centered at -C/S with radius g/(2*S), and apply the inspected sphere-domination theorem with |R|<g/6. The derivative bound excludes multiple zeros. The cofinal simple-zero theorem and absolutely summable convolution-square contradiction remain Lean OPEN. The original every-small-t version also requires a full center limit beyond the square sequence. C12.92 is not retired, and the literal Liouville half-power lower bound and RH remain unsolved.

**Validation:** four targeted leaf builds, four direct `lake --old env lean` checks and all34 public theorem axiom audits passed. Only propext/Classical.choice/Quot.sound; all four imports wired, no umbrella build. Global lint has15 unrelated reachability errors, none in these leaves. Three corpus searches completed with partial=false; snapshot, compiler freshness, source applicability and exact residual proof ledger are recorded in `../3-formalized/mc-exponential-weight-phase-zero.md`. No numerical mathematical computation, added axiom, placeholder, heartbeat raise, subagent or commit. Owned temporary files cleaned after recording. Goal active/unmet.

### C12.92 closure and next signed-density conjecture (2026-10-04, 1005i)

**Verified frontier advance:** the actual exponential weight has a simple bounded prime-phase zero at every sufficiently large real scale. The center theorem now holds for every real T: log(T)*F(1/T)->0. The final full-source proof transfers actual prime capacity through all cofactor and nonlinear errors and proves the zero is simple. Consequently some delta>0 excludes every absolutely summable complex Dirichlet-convolution square root of exp(-nt)/n for all0<t<delta. The universal scalar-root positivity construction is falsified; the strongest positive survivor is fully formalized. It does not falsify J_lambda>=0 or RH.

**Exact declarations:** `RHTower.LiouvilleTwistedDensity.tendsto_log_mul_exponentialDensity_reciprocal_zero`, `RHTower.LiouvillePrimeBand.exists_eventually_simple_prime_phase_zero`, `exists_small_no_summable_dirichlet_square_root`, and `not_all_weights_have_summable_square_roots`. Detailed proof and completed no-go audit: `../3-formalized/mc-exponential-weight-phase-zero.md`; retired proposal: `../5-failed/mc-exponential-weight-scalar-square-root.md`.

**Validation:** targeted builds of Center, SimpleZero and NoSquare passed. All three required final `lake --old env lean` checks passed with empty output. All eight public theorems passed /tmp axiom audits, only propext/Classical.choice/Quot.sound. New imports wired, no umbrella build. Global lint exits1 on thirteen unrelated unreachable modules; no error for these leaves. Seven searches this turn completed: five partial=false, two partial=true. Full coverage/freshness and rejected source mismatches recorded in the two dedicated cards. No added axiom, placeholder, heartbeat increase, numerical mathematical experiment, subagent or commit.

**Assessment and next hard problem:** this closes a real obstruction and its positive survivor, but does not improve the RH-critical lower estimate J_lambda(t)>=-C_epsilon*t^(1/2-epsilon). C12.93 now tests the actual finite-prime inequality K_P=J_P-t*J_P'>=0, which permits the increases that killed antitonicity. Its exact insertion and square-cofactor identities retain every prime power. A generic derivative hierarchy has not proved closure; the full arithmetic square-cofactor sign remains to be solved. Details in `mc-scaled-liouville-density-cone.md`. No additional conditional receiver or toy sign theorem was formalized instead. Goal active/unmet.

**1005i cleanup complete:** removed all25 exact owned /tmp search/proof/audit files after recording results. Every owned search, Lean and lint process reached a terminal exit; no owned live handle remains.

### C12.93 complete density / squarefree discrepancy continuation (2026-10-04, 1005j)

**Route MC; no critical estimate or new Lean theorem.** C12.92's previous audited simple-zero and no-square results remain valid, but this turn did not solve the complete K_P sign or the weaker RH-producing half-power bound. The dedicated card `mc-scaled-liouville-density-cone.md` records the full paper derivations and search audit.

The C12.79 positive-deletion coefficient mechanism also gives J_P=sum b_P(d)*J_lambda(dt)/d and the same identity for K=J-tJ', with all squarefree outside-prime cofactors retained. Consequently positivity of all finite-prime K_P is equivalent to full K positivity. The actual Dirichlet inverse lambda*mu^2=delta gives sum mu(n)^2*K(nt)/n=(1+t)*exp(-t); a retrieved pointwise-product theorem is not this identity.

Write A(x)=sum_(n<=x)mu(n)^2, rho=6/pi^2 and E=A-rho*x. Complete Abel summation, followed by the exact tail-primitive inverse, yields

    rho*K(t)=t*exp(-t)+t*C(t),
    C(t)=integral_1^infinity E(x)*K'(t*x)/x dx.

Every endpoint and full tail is retained. The positive continuum contribution is explicit, but the signed C term is still uncontrolled. C(t)>=-C_epsilon*t^(-1/2-epsilon) would give the needed K and J lower bounds. Absolute use of the square-root count error retains the unbounded near-zero derivative integral. Completing the integral below1 retains the boundary -rho*K(t)/t; it cannot erase the unknown source.

The real power-mode multiplier q(alpha)=alpha/rho*integral E(x)*x^(alpha-2) has exact positive deficit -alpha/[rho*(1-alpha)]*zeta(1-alpha)/zeta(2-2alpha) for0<alpha<1/2, tending to zero at the endpoint. This does not control complex modes: q(alpha)=1 precisely when zeta(1-alpha)=0 in that strip. Moreover E<0 on the symbolic interval(1/rho,2), so replacing E by |E| makes the comparison multiplier exceed1 near the critical exponent. These are paper diagnostics and an identified positive real-mode statement, Lean OPEN; no no-go or route is retired. An ordinary critical discrepancy moment was not assumed from its Abelian limit.

**Assessment:** exact arithmetic cancellation of C remains the hard problem. This turn changed the admissible comparison argument but did not move the critical bound. Do not repeat a positive-density replacement, a real-scalar-to-operator inference, or an absolute contraction near1/2. The next attack must preserve the actual signed E/K' dependence, rather than formalize another RH receiver.

**Audit:** nine searches terminal, partial=false with snapshot/compiler freshness and generated-chain mismatches recorded in the dedicated card. No Lean edit/build, axiom audit, numerical mathematical experiment, placeholder, heartbeat change, subagent, full/umbrella build or commit. Previous green Lean audits were not rerun on unchanged modules. Goal active/unmet; cleanup recorded in the working log.


### C12.93 exact-response closure and signed-record test (2026-10-04,1005k)

**Route MC; two new audited leaves, no critical cancellation estimate.**
`SquarefreeDiscrepancyMellin` identifies the literal squarefree counting discrepancy's
absolutely convergent Mellin moment on Re(s)>1/2, including the floor and lower endpoint.
Its complex response satisfies q(a)=1 iff zeta(1-a)=0 for0<Re(a)<1/2.
`SquarefreeDiscrepancyCriticalGap` proves q(a)<1 on the real subcritical axis, q(a)->1 at
one half, a uniform positive gap between the absolute and signed responses, and absolute
response>1 near the endpoint. The positive survivor and its complete paper proof are in
`../3-formalized/mc-squarefree-discrepancy-response.md`. Only the particular absolute
contraction is retired in `../5-failed/mc-squarefree-discrepancy-absolute-contraction.md`.
The actual K sign, signed correlation lower bound and RH remain OPEN.

Both targeted leaf builds and both required direct `lake --old env lean` audits passed.
All23 public theorem axiom checks in /tmp passed, only propext/Classical.choice/Quot.sound.
Both imports wired; indexes regenerated; no umbrella build. Global formal lint exits1 on13
unrelated unreachable modules, neither new leaf. An axiom audit accidentally overlapped the
second direct audit; its exact owned child/wrapper were stopped and verified gone, then it
was rerun successfully only after the direct audit exited. Detailed process audit is in the
survivor card. No numerical mathematical experiment, added axiom, placeholder, heartbeat
increase, subagent or commit.

**Assessment and next hard problem.** The previous paper obstruction is now fully formalized
with its strongest positive survivor; this changes available rigorous comparison tools but
does not improve J_lambda(t)>=-C_epsilon*t^(1/2-epsilon). Tested a new negative-record
subtraction: L_t(u)=K(u)-K(t)(u/t)^a>=0 at a negative record, yielding

    rho*(1-q(a))*K(t)=t*exp(-t)+t*integral E(x)*L_t'(tx)/x dx.

The retained signed work equals a compensated difference between continuous A(x)/x² work
and squarefree sampling; both parts can diverge separately. The positive real-mode deficit
is now explicit, but record nonnegativity gives no derivative or sampling sign. Direct
dyadic pairing retains the entire odd-cofactor remainder and supplies no lower bound.
No conditional receiver was added. The hard next step is joint arithmetic cancellation in
this complete signed work; neither real-mode positivity nor an absolute comparison pays it.
The exact paper derivation remains in `mc-scaled-liouville-density-cone.md`.


**1005k search completion:** four deep corpus searches reached terminal exit0, two partial=false
and two partial=true. Full metadata and source-applicability ledger retained in the survivor
card. The final rational-approximation/entire-orbit proposal is unrelated to arithmetic
Liouville and was rejected; actual prime-two/cofactor identities keep their whole remainder.


**1005k cleanup complete:** removed all15 exact owned /tmp search, proof, fragment, lint,
index-output and axiom-audit files; absence verified. All owned processes reached terminal
exit, including the explicitly terminated overlapping audit. No owned live handle remains.
Documentation/source diff check passed. Goal remains active and unmet.


### C12.93 retained logarithmic work and real-sign test (2026-10-04,1005l)

**Route MC; no new critical estimate or Lean theorem.** Previous turn's two audited response
leaves are a verified advance on the exact comparison obstruction, not on Liouville
half-power cancellation. Revalidated C12.36 and C12.77 before the new signed-record test.
The active card `mc-scaled-liouville-density-cone.md` retains the full paper derivations.

For the actual K, full coefficient convolution and a justified Frullani interchange give

    integral_0^infinity [exp(-v)K(t)-K(t+v)]/v dv+J(t)
      +sum_d Lambda(d)K(dt)/d = 2sum_m Lambda(m)K(m^2*t)/m^2.

Every term is absolutely convergent at fixed t>0. The even-power part was already controlled
in C12.36. Subtracting a growing negative-record power profile inside the full first-order
prime and continuous terms instead requires the finite compensation

    sum_(n<=R)Lambda(n)n^(a-1)-integral_1^R x^(a-1)dx
      =1+R^(a-1)(psi(R)-R)+(1-a)integral_1^R(psi(x)-x)x^(a-2)dx.

The inspected fixed-log Chebyshev-error bounds do not justify its ordinary limit for a>0.
This is an unproved extra convergence obligation, not a proof of divergence. Unlike the
squarefree discrepancy, separate prime errors do not admit the needed power comparison from
the available bound. Keep prime cutoffs and full source compensation inside(REC).

A real sum-of-squares proposal also retains the actual source sign. For any completely
multiplicative chi(p) in{1,-1}, chi=lambda*b_chi with b_chi(p^k)=2 for chi(p)=1 and zero
otherwise(k>=1). Full absolute rearrangement gives J_chi(t)=sum b_chi(d)J_lambda(dt)/d.
Universal real-sign positivity is therefore the same source-positivity obligation by the
existing positive-deletion mechanism. The generic heat-kernel argument fails even on the
four labels1,p,q,pq: the parity Fourier coefficient of the rate is(p-1)(q-1)/4>0, so its
damped coefficient has negative derivative from zero. This does not decide the actual
weighted/square-aggregated source; no candidate or route was retired and no receiver added.

**Next hard obligation:** bound complete signed record work using the joint arithmetic
coefficients, without replacing the finite prime compensation by an unproved boundary
value or assuming positivity for a generic kernel. Half-power J bound and RH remain open.

**Audit:** two deep searches terminal0/partial=false,65191/65193 files,43 compiled,2660 stale,
49159/49161 pending; snapshot/current1222708/1222709,1222735/1222735. Both semantic coverage
unavailable and background refresh, no pending method invalidation. Generated positive-
coefficient and absolute-convergence chains retain their unmet premises. No Lean edit/build,
axiom audit, numerical mathematical experiment, placeholder, heartbeat change, subagent,
umbrella build or commit. Goal active/unmet; exact cleanup recorded in the working log.


### C12.93 full inverse fibres and moving cutoff (2026-10-04,1005m)

**Route MC; no new critical estimate or Lean theorem.** Revalidated1005l's retained cutoff
and inspected actual corpus. The product-fibre law for mu(m)mu(n) has fixed sign, but the
lambda(n/d)mu(d)^2 inverse has exact complete cancellation lambda(n)sum_(d|n)mu(d)=delta(n).
This distinction does not remove the cutoff boundary. For R>=1,

    c_R(n)=sum_(d|n,d<=R)mu(d)^2*lambda(n/d),
    S_R(t)=sum_(d<=R)mu(d)^2*K(dt)/d
          =sum_n c_R(n)*(1/n+t)*exp(-nt).

For n<=R, c_R(n)=delta(n); forR<n<=2R, c_R(n)=-mu(n)^2. The first boundary band therefore
has a fixed negative sign in S_R, but every higher band remains. At t=c/R, its unsigned
mass tends to rho*integral_1^2(1/u+c)exp(-cu)du>0. It cannot be discarded via fixed-t
exponential decay.

The complete moving tail T_R(t)=sum_(d>R)mu(d)^2*K(dt)/d has paper asymptotic

    T_R(c/R)=rho*integral_c^infinity K(u)/u du+O_c(R^(-1/2)), c>0.

Full Abel summation retains the endpoint -E(R)K(c)/R and the integral involving K-uK'.
The surviving profile is positive for sufficiently large c by actual leading-term decay
at infinity, so the whole tail is not uniformly negligible on these cofinal paths. This
is not a bound on K near zero. Sending c to zero still needs its signed primitive defect
and stable recovery of K; negative-record values give the wrong direction through the
positive-weight head sum. No inverse-order claim, discarded band or critical estimate was
obtained. Complete paper derivations remain in `mc-scaled-liouville-density-cone.md`.

**Next hard target:** control the joint signed head and moving profile. Do not confuse
perfect cancellation on complete divisor fibres with a bound on their cutoff boundary,
or substitute a first-band sign or fixed-t tail estimate for this full source bound.

**Audit:** two deep searches terminal0/partial=false;65197/65198 files,43 compiled,2660 stale,
49164/49165 pending; snapshot/current1222847/1222849 and1222884/1222887. Both older-generation
and semantic-coverage warnings, background refresh, no method invalidation pending. All
candidate/source statements and proposed ingredient chains inspected. A harmonic-log limit
plus an explicit exponential-tail lemma does not imply critical decay of the source.
No Lean edits/builds/audits, numerical mathematical experiment, added axiom, placeholder,
heartbeat change, subagent, umbrella build, commit or no-go retirement. Goal active/unmet.

### C12.93 complete boundary profile and square-product endpoint (2026-10-04,1005n)

**Route MC; no critical estimate or new Lean theorem.** Previous moving-cutoff analysis
did not bound the source. This turn kept every product band. With h(u)=sum_(n<=u)lambda(n)/n,
L(u)=sum_(n<=u)lambda(n), P(u)=u*h(u)-L(u)=integral_1^u h(v)dv, the exact cutoff cumulative is

    sum_(n<=R*u)c_R(n)
      =1-rho*R*P(u)-sum_(m<=u)lambda(m)*(E(R*u/m)-E(R)).

Its normalized limit is -rho*P(u), with the complete signed harmonic prefix retained.
Full Abel summation recovers1005m's I(c)=integral_1^infinity h(u)*(1/u+c)*exp(-c*u)du.
Recovering K gives t^2*integral_1^infinity(t*u-1)*P(u)*exp(-t*u)du. The kernel changes
sign, so even an unproved P>=0 would not itself supply the needed K lower bound. The
known logarithmic harmonic decay yields no critical estimate here.

A second attack expanded the literal squarefree error before taking absolute values:

    t*C(t)=t^2*sum_(m,n>=1)mu(m)*lambda(n)*n*m^2
        *integral_(1/m^2)^infinity frac(y)*exp(-t*n*m^2*y)dy.

This full x>=1 expansion is absolute at each fixed t>0. At fixed product n*m^2, its
lower endpoint still depends on m. Completing all endpoints to zero would allow the
coefficient collapse to mu, but also adds the source term -rho*K(t), subject to the
proper K(0+) and integrability limits. Expanding the completed n-series absolutely
down to zero is invalid: its harmonic majorant diverges. This is the same lower-scale
charge from1005j, now exposed in the actual square-product grouping; no cancellation
estimate follows by removing it.

Full paper proofs and source metadata in `mc-scaled-liouville-density-cone.md`. Three
deep searches terminal0, partial=false/true/false, all candidate/source statements and
ingredient chains inspected. The proposed exp(-N^2) Liouville-rate positivity is a
different object; density positivity plus block-deletion energy has no source bridge.
No Lean changes/builds/audits, numerical experiment, axiom, placeholder, heartbeat raise,
subagent, full/umbrella build, commit or no-go retirement. Goal active/unmet.
Next estimate must retain the divisor-dependent boundary and its actual Liouville head;
another representation alone is not a frontier advance.

### C12.93 completed noncomparable sector and centered ceiling (2026-10-04,1005o)

**Route MC; new paper source-order law, no critical bound or Lean theorem.** A zero
harmonic-mass condition does not repair generic PSD of C12.91's kernel A(t*m*n): a
remote compensating coefficient enforces mass zero while preserving a negative finite
direction. This is not a counterexample for the actual Mobius vector or a retired route.
Actual finite-cutoff centering retains both harmonic cross and square boundary terms.

Kept the full square-divisor completion instead. Let a=one*squareIndicator. At each
product q define b from the orientation m|n, d from m=n, and c from neither m|n nor n|m,
with weights a(r)*mu(m)*mu(n) and r*m*n=q. Exact partition gives lambda=2b-d+c. The local
coefficient formulas are

    d(p^(2k))=d(p^(2k+1))=2k+1,
    b(p^(2k))=k+1, b(p^(2k+1))=k.

Writing D_i=2*floor(e_i/2)+1, s_i=(-1)^e_i, B_i=(D_i+s_i)/2, C_i=(D_i-s_i)/2 gives

    c(q)=2*sum_(S nonempty even subset of prime factors)
                  product_(i in S)C_i*product_(i notin S)B_i>=0.

The exact zero class is1, positive prime powers, and squarefree numbers with an odd
number of prime factors. This is positivity of complete a-convolved coefficients,
not of individual noncomparable pairs or an arbitrary coefficient quadratic form.
All physical fixed-t sums are absolute, giving J=2B-D+N with B,D,N nonnegative.

B(t) has the positive expansion over r^2*s^2*d^3 with d squarefree and B(0)<infinity.
For every0<alpha<1/2, 1-exp(-u)<=u^alpha yields B(0)-B(t)<=C_alpha*t^alpha using ordinary
convergent coefficient moments. D and N both diverge at zero and their difference tends
to2B(0); no critical rate follows. New exact conjecture: D(t)-N(t)<=2B(0). It would imply
the desired J lower bound through the proved-on-paper B allowance. It remains OPEN.
The coefficient2b-lambda is negative at squarefree products of two distinct primes, so
the positive-coefficient comparison does not prove this ceiling.

Complete paper proof and search ledger in `mc-scaled-liouville-density-cone.md`.
Four deep searches terminal0, partial=true/false/true/false. Candidate/source statements
and ingredient scopes inspected; generic positive-kernel hypotheses, energy receivers,
the additive anti-diagonal sign law and rectangle consumers do not supply the estimate.
No Lean source/build/audit, numerical experiment, axiom, placeholder, heartbeat raise,
subagent, full/umbrella build, commit or no-go retirement. New sector law is PAPER / Lean
OPEN. RH goal remains active and unmet. Continue the actual centered D/N comparison;
neither its limiting constant nor separate sector positivity settles it.

### C12.93 centered ceiling and lcm correction (2026-10-04,1005p)

**Route MC; no critical frontier movement or new Lean theorem.** Tested the actual
product quadratic against the corpus's positive lcm divisor square. With
f_t(u)=A(t*u)/u, the full lcm form collapses to sum_s exp(-t*s^2)/s^2. The correction
at squarefree lcm label k is exactly mu(k)*H_k(t), where H_k>0 has an explicit
nonnegative coefficient expansion from product_(p|k)(2*Id-T_p)-Id. A fixed prime's
negative correction has magnitude f_t(p)-f_t(p^2), which diverges as t decreases to0.
It cannot be paid individually by B(0)-B(t)->0. Complete parity cancellation remains
necessary; this does not refute the centered ceiling or retire its candidate.

The direct cumulative comparison is G(x)=sum_(n<=x)lambda(n)/n+2*sum_(n>x)b(n)/n.
Its exponentially weighted integral is exactly the centered gap. G>=0 would suffice,
but is unproved. The positive b-tail is supported on powerful integers and has all
subcritical half-power moments; estimating that tail does not estimate the Liouville
deficit. Finite-prime insertion of the centered gap has an explicit nonnegative
forcing with coefficients floor((e+1)/2)/p^e, alongside the still-signed alternating
dilation operator. No inequality controlling their complete combination was obtained.

Full paper proofs and scope checks are in `mc-scaled-liouville-density-cone.md`.
Five corpus searches terminal0, partial=false/true/false/false/false; no applicable
critical producer was established from the returned hits. No new Lean source, build,
axiom audit, numerical experiment, placeholder, heartbeat raise, subagent, full build,
commit or no-go retirement. RH remains unproved. Next work must bound G or the full
centered insertion sum; another lcm identity or individual-fibre estimate is insufficient.

### C12.93 coupled prefix and triangular-source test (2026-10-04,1005q)

**Route MC; no critical estimate or new Lean theorem.** An actual prime-interval
family rejects the stronger Euler-baseline comparison h_P>=ell_P-C*T_bP for any
fixed C. For P consisting of primes in(R,2R] and x=R^(3/2), the prefix is1-S,
S=sum1/p, while ell_P-(1-S)~S^2/2 and T_bP=O(sum1/p^2)=o(S^2). The centered G_P
still tends to1, so its required sign is not refuted. This paper test retains all
prime powers in the full Euler products; no numerical experiment or retirement.

The alternative full identity lambda*one=squareIndicator gives
K(t)=t*sum_s exp(-t*s^2)-t*integral_1^infinity frac(x)*K'(tx)/x dx. Nonnegative
frac does not sign its derivative pairing. At a negative power record, the remaining
defect is a compensated discrete sum minus an integral of nonnegative record excess;
neither piece can be discarded, and no needed comparison was proved.

Returned to the actual primitive P(x)=x*h(x)-sum_(n<=x)lambda(n). Although P>=0 would
not sign K, it would sign J directly through J(t)=t^2*integral P(x)*exp(-t*x)dx.
The weaker all-epsilon lower bound P>=-C_epsilon*x^(1/2+epsilon) also suffices for MC.
An exact short Mobius quadratic expression retains both hyperbola terms; its product
kernel is not generically PSD. The arithmetic lower bound on the complete expression
is still missing. This is the next hard source target, not a new conditional receiver.

Details in active C12.93 card. Four corpus searches terminal0, partial=false each;
source identities, logarithmic rates, unsigned sieve bounds and generated weight
positivity chains do not establish the sign. No Lean source/build/audit, numerical
mathematical experiment, axiom, placeholder, heartbeat raise, subagent, full build,
commit or no-go retirement. Goal active/unmet.

### C12.93 actual triangular short-head obstruction (2026-10-04,1005r)

**Route MC; one actual-source branch closed, no critical combined bound.** The
new unconditional Lean leaf `LiouvilleTriangularShortHead` proves
`A(U)-Z*U^2*H(U)=o(U*sqrt(U))` and `A(U)!=o(U*sqrt(U))`, where A is the literal
first short term at x=U^2 and H is the actual harmonic Mobius prefix. The square
kernel has a bounded lattice remainder; PNT controls its secondary term; inverse
Abel summation and the corpus Mertens square-root obstruction exclude the smaller
absolute size. This rules out separate absolute payment at every desired
half-plus-epsilon exponent. It does not establish signed excursions, refute a
one-sided A estimate, or bound the complete P=2A-B.

The exact positive survivor is formalized and audited before retiring the
separate-payment construction. See `../3-formalized/mc-triangular-short-head-scale-law.md`
and `../5-failed/mc-triangular-short-head-absolute-payment.md`. Targeted old-build,
required direct leaf audit and all four public axiom checks passed; only standard
axioms. Umbrella wired once, indexes regenerated. Global lint retains13 unrelated
reachability errors. Four corpus searches completed; detailed coverage in the
survivor card. No numerical experiment, heartbeat change, full/umbrella build,
subagent, commit or push. MC's hard joint lower bound and RH remain unproved.


## C12.99 — shifted triangular pole separation (2026-10-04,1005s)

Route MC still needs the complete one-sided half-power bound for P=2A-B. Joint positivity and rough-prime attempts left their signed remainder unbounded. New unconditional Lean progress: `LiouvilleTriangularPoleSeparation` supplies an actual shifted zeta zero w with Re(w)>=3/4 at which both competing denominators are nonzero, and proves that the full three-term pole model is analytic exactly when its short-head coefficient vanishes. Endless affine propagation of zeros would converge to the nonzero residue unit at1, so no numerical zero information or simplicity premise is needed.

The parent card `mc-triangular-quadratic-pole-cancellation.md` records a paper route to two-sided excursions of P+c*A for c!=0, hence of the actual B. The physical Mellin identity, bounded remainder's holomorphy and Landau transfer remain unformalized. No corresponding no-go is retired, no actual-source oscillation theorem is claimed from this leaf, and no RH-critical estimate improved. Audited component: `../3-formalized/mc-triangular-shifted-pole-separation.md`.

Targeted old-build, required direct leaf audit and two public standard-only axiom checks passed. Umbrella wired once; indexes regenerated and three API entries checked. Global lint has16 unrelated unreachable modules. Six corpus searches completed; detailed coverage and failed applicability checks are in the active density-cone card. Goal active/unmet; next complete the actual-source connection and return to the surviving joint lower bound.
