# TG: arithmetic covariance transfer to native zero exclusion

Status: IN PROGRESS. RH remains unproved. No unconditional native-source bound claimed.

## Target and verified starting point

The current Lean leaf `SoninPrimePolarResidueExclusion` converts bounded cofinal returns of the literal prime–polar cell source into RH. Its proof transports the native source through a Mellin primitive and a division-free differential identity, then contradicts the positive integer residue at a hypothetical strict-right zero. The quantitative producer remains missing.

Write `c_n = soninPrimePolarGridCoefficient n`, `A_n = sum_{j <= n} c_j`. The exact target is finite total energy

`sum_n A_n^2 / ((n+2)(n+3))`.

The unconditional cubic source budget is `sum_n Lambda(n)/(4 n log(n)^3) < 1`. It is not yet an upper bound for this native energy. Treating these two quantities as interchangeable would assume the hard step.

## Current attack: keep signed arithmetic covariance

For ground entries `B_n`, the physical covariance is `inner B_i B_j = 2a/(max(i,j)+2)`. The finite-source square is therefore

`2a [sum_n c_n^2/(n+2) + 2 sum_n c_n A_(n-1)/(n+2)]`,

where the sum is over the retained indices and `A_(-1)=0`. The prime diagonal is not summable; the signed prime–polar work must cancel it. Neither an estimate on individual prime weights nor a terminal discrepancy crossing pays for the accumulated positive energy.

Candidate mechanism: use the exact von Mangoldt divisor identity before estimating the covariance, retain the centered floor kernels and their nonperiodic boundary terms, and seek a signed comparison with the finite cubic budget. Complete-period averages alone are insufficient because the physical kernel is anchored at the actual origin.

Proof obligations, before any Lean implementation:

1. Exact source-preserving divisor expansion, including proper prime powers, polar continuum and endpoints.
2. Bound the full signed covariance; no termwise absolute-value replacement of mixed work.
3. Bound the boundary correction for the actual anchored source, rather than substituting an average over translations or a different Hilbert carrier.
4. Feed the resulting bound into the already verified native residue-exclusion theorem.

## Current-turn audit

- Previous turn: progress, because the native quantitative-to-residue conversion was checked in Lean. This turn has not yet closed another hard gap.
- Deep corpus query `prime polar source cumulative energy cubic budget signed coherence`: completed, `partial=false`; source inventory complete, compiler coverage mixed (many source-only/stale entries). The suggested ingredient set conflated unrelated energy theorems and is inapplicable. No usable producer was found.
- Checked exact native grid energy, chronological prime–polar work, regularized prime coefficient budgets, cubic safe-Euler clock, and Selberg symmetry formula in Lean source.
- Selberg symmetry's displayed `O(N)` remainder does not supply the critical square-integrable remainder needed here. No exponent improvement inferred from that identity.
- Discarded as proofs: prime-label orthogonality transferred to physical ground entries; ordinary harmonic-discrepancy convergence; endpoint crossings; complete-period sieve averaging without its anchored boundary correction; regularized higher-prime-power bounds substituted for the first-prime source.
- Investigating the floor-covariance arithmetic rather than adding another conditional receiver or index-identification leaf.

## Verification status

No Lean edits or new Lean result in this cycle yet. No numerical experiments. Existing conditional conversion is not an unconditional RH proof.

## Transfer test and remaining work

The second deep query, `Möbius signed floor covariance critical energy`, also completed with `partial=false`. It returned exact floor inversion and covariance identities, but no estimate of the retained signed arithmetic boundary work. The suggested generic symmetric-energy ingredients are inapplicable. The lexical query `Burnol ground normalized column bounded transfer` located the existing physical ground-transfer and arithmetic-selector interfaces; it did not provide the missing Burnol-to-native comparison.

The following bounded-transfer proposal was tested on its literal columns before attempting a proof: a single bounded linear map sends each primitive Burnol column at `(p,0)` to the native prime ground entry at `log p`. The column norms already obstruct this proposal. The Burnol column square is `1/(4 p log(p)^2)`; the native column square is `2a/p`. Such a map would require `8a log(p)^2 <= ||T||^2` for every prime. This does not reject TG or control the compensated prime–polar source. It rejects using a bounded columnwise transfer to import the cubic budget unchanged.

Normalizing each column separately does not automatically fix the mixed Gram. For log frequencies `u,v>0`, the normalized Burnol correlation is `(2 sqrt(u v)/(u+v))^3`, whereas the normalized native correlation is `exp(-|u-v|/2)`. Thus the former has quadratic small-separation loss and the latter linear loss. A complete formal proof of the corresponding normalized arithmetic-column obstruction has NOT been added; do not treat this calculation as a Lean theorem or a completed no-go closure.

Two attempted producer arguments failed their dependency audit:

1. A direct bounded transfer of the existing subunit cubic covariance fails the exact one-column norm test above. The unbounded inverse-clock factor cannot be silently absorbed in an operator constant.
2. Divisor/floor inversion preserves a signed anchored boundary covariance. The existing coprime balance bounds `criticalEnergy + crossWork`, not either term separately. The small-row bound excludes the endpoint row and the remaining large-index block. Discarding those pieces would erase the unproved cancellation.

No new hard gap closed this cycle. Keep the arithmetic producer active. The next proof attempt must control the retained signed prime–polar work on the actual source; a new receiver, a spectral index identity, or improved constants in the safe Euler budget would not resolve it.

## Continuation: complete jet fibres and coherent reconstruction

Previous goal turn classified as **no progress toward closing the proof gap**. Rechecked the current `SoninPrimePolarResidueExclusion` conclusion: the native energy premise is still present. Rechecked current `SoninPrimePolarJetLcmCovariance`: its full kernel transport explicitly retains high LCM labels, polar cross terms and the terminal square. No unconditional energy estimate was found.

Paper calculation for the exact incidence fibre: let `n` be squarefree with `n | k*m`. Partition its prime factors into `r` dividing only `k`, `s` dividing only `m`, and `t` dividing both. Its two-variable local product is

`(-x)^r (-y)^s (xy-x-y)^t`.

Each exclusive prime is forced into its corresponding divisor; each common prime has the three assignments left, right, or both. Differentiating once in each variable at `x=y=1` therefore gives

`jetLcmIncidence n k m = mu(n) * (r*s-t)`.

The pure diagonal has `r=s=0` and recovers the already formalized negative jet law. The mixed `r*s` term survives away from that diagonal. Summing all fibres at fixed `k,m` recovers the prime-power pair indicator, so this local calculation does **not** by itself estimate the native covariance. It is a finite algebraic reduction (`BRIDGE`), not an arithmetic producer. No novelty or Lean-formalization claim is made for it. Do not add an identity-only module merely to record it.

Checked another possible input: `ccmEulerRenewal_fullForce_critical_energy_le` gives a genuine modulus-uniform sixth-degree logarithmic bound, but on **coefficient** energy. `ccmEulerRenewal_prime_force_orthogonal` proves disjoint coefficient supports only. Different delay profiles still overlap in the physical norm. Importing this estimate into the native source without a coherent reconstruction estimate would be an unsupported step.

The bounded centered Möbius remainder does not remove this problem either. Its explicit work retains `exp(T)*sum(mu(n)/n)-sum(mu(n))` and the logarithmic Möbius primitive; it cannot be discarded or assigned a favorable sign. The exact `49/4` diagonal budget and bounded coprime balance leave these mixed terms intact.

Anti-theatre / anti-laziness audit: no new hard bound or novel theorem obtained in this continuation. Corpus reductions were checked, but further formalization of those reductions would not advance the missing producer. No numerical experiments, no Lean edits, no builds, no changes to the RH success criterion. The full signed arithmetic cancellation remains the active problem; no external input or permission is needed to continue attacking it.

## Continuation: closed-transfer and aperture-charge audit

This continuation is **no proof progress**, not a verified wait or an external blockage. The native arithmetic producer remains unproved. No Lean source was changed or compiled during this continuation.

Three documented deep searches were completed and their reported coverage checked:

- `actual zero prime source covariance bounded finite root`: partial results, older coverage generation, semantic coverage unavailable.
- `closed graph prime source Fredholm charge covariance transfer`: partial results, older coverage generation, semantic coverage unavailable.
- `off-line zero evaluation dilation leakage source budget`: `partial=false`, semantic coverage unavailable.

No applicable native-source upper bound was found in these results. An exhaustive source-text query for the existing native energy and bounded-return receivers still found the arithmetic premise on the relevant RH theorem. This is a statement about the checked results, not a claim that every possible corpus argument has been exhausted.

The proposed generic repair of the failed bounded transfer was to admit a closed, possibly unbounded, source-faithful map. The exact-norm first-trace version is already ruled out by `primeFirstTraceClock_topologicalNonlinearRiggingNoEscapeUniversality`: its graph-null sequence prevents a single-valued closed extension. The existing positive classification is explicit: the graph closure contains exactly pairs whose target coordinate at zero vanishes. Both statements are already formalized in that existing source. Verdict for this generic repair: **REDISCOVERED obstruction**, not a new result and not a retirement of TG. This theorem concerns its specified Hardy source topology; it must not be silently generalized to every Burnol/native realization or to the single actual compensated arithmetic trajectory.

The alternative of bounding a raw aperture defect and then reading off an integer also does not close the gap. `HedenmalmSoninWeylDefectQuantizationWall` already proves that every fixed positive packet charge can remain off the wall with raw defect arbitrarily close to one. Its singular logarithmic normalization recovers the charge, but no corresponding arithmetic bound for that singular normalization was obtained. The actual projected Burnol evaluation laws retain both aperture losses and the norm of the evaluation vector; they do not give a zero-specific upper bound by the cubic prime budget.

The lattice feature-budget search hit was checked at its exact hypotheses. `HedenmalmCriticalFeatureLatticePrimeGammaBudget` subtracts the critical-line feature trace and compares the corrected source excess with off-line feature energy. That correction still uses the Xi divisor, and the module explicitly leaves its arithmetic upper bound open. It cannot be substituted for a bound produced before selecting zeros.

Finite-cutoff zero displacement was also checked. It describes how approximating zeros approach an already chosen zero, with the center equal to that original zero. It does not move the center to the critical line or bound the native prime source. No zero exclusion follows from its small root displacement alone.

The active exact arithmetic target remains

`exists C, forall N, sum_{n <= N} A_n^2 / ((n+2)(n+3)) <= C`,

with the original `A_n = soninPrimePolarGridCumulative n`. This is the missing producer, not a newly established conjectural reduction. A proof must use the actual prime coefficients and unchanged polar masses. Any proposed factorization must reproduce the full finite covariance and account for its terminal square before applying an estimate. Do not introduce a new conditional receiver, an arbitrary-coefficient transfer, a divisor-dependent source budget, or an index identity as a substitute.

Audit: no new scientific knowledge or frontier advance in this cycle; several known obstructions were rechecked. Further generic transfer audits would repeat that failure. Continue with an arithmetic proof attempt on the complete signed covariance. No effort-based avoidance, numerical experiments, new axioms, or claims of unconditional RH. The goal stays active because the missing work is mathematical, not an external-state dependency.

## Active attempt: exact affine counterterm before signed inversion

The previous continuation was no proof progress. The next arithmetic attempt keeps the original deficit but changes its decomposition before estimating it. This is a supporting reduction, not a claimed new RH criterion or a completed hard bound.

Let `Z` be the exact finite logarithmic dilation sum, `M` its Möbius inverse, `D` the actual integrated Chebyshev deficit, and `h = Z D` the existing elementary source. Put

`b = log(2*pi)`, `c = EulerGamma + 1`, `a = c-b`,

`A(T) = a+b*T`, `s(T) = h(T)-Z A(T)`, `q = M s`.

Exact inversion gives `D(T)=A(T)+q(T)` for nonnegative time. Unlike the earlier subtraction of a continuous exponential and linear main term from `h`, the inverse of this counterterm is explicitly `A`; no unknown harmonic Möbius sum, Mertens sum, or logarithmic Möbius primitive is placed outside `q`.

Dependency-closed paper bound for `s`: write `x=exp(T)`, `N=floor(x)`, `L=sum_{n<=N}(T-log n)`, and `U=L-x+T/2+b/2`. Stirling gives

`U = N*(T-log N) - (x-N) + (T-log N)/2 - E_N`,

with `0<=E_N<=1/(12*N)`. Since `N>=1`, `0<=x-N<1`, and `0<=T-log N<=1/N`, one has `|U|<=2`. The existing bounded remainder `r=h-c*(x-1)+(b/2)*T` satisfies `|r|<=7/2`. Direct algebra then gives

`s = r-c+a*(x-N)+b^2/2-b*U`.

Therefore `|s|<=K`, where `K=7/2+|c|+|a|+b^2/2+2*|b|`. The exact coprime identity applies to `q` and yields

`exp(-T)*(q(T)^2+CoprimeCross(q,T)) = exp(-T)*M(s^2)(T)`,

whose right side has absolute value at most `K^2`. Consequently the full original deficit obeys

`exp(-T)*D(T)^2 + 2*exp(-T)*CoprimeCross(q,T)`

`<= 2*K^2 + 2*exp(-T)*A(T)^2`.

This is still a **signed** source bound. The actual hard conjecture is a uniform lower bound for the retained normalized cross term, with every coprime pair included:

`exists C >= 0, forall T >= 0, exp(-T)*CoprimeCross(q,T) >= -C`.

No such lower bound is being assumed or claimed. A generic nonnegative-matrix proof is already excluded by the corpus; the next sign analysis must use this exact arithmetic `q`.

Internal audit: the affine normalization is `BRIDGE`, not a novelty claim. Its purpose is to remove the unestimated explicit Möbius main channels from the subsequent arithmetic proof attempt. Formalization, if checked, must report the surviving signed term rather than presenting the bounded source as a bound on `D`.

The exact existing capstone was checked in `CCMRestrictedWeilPoleCompressionRHCriterion`: `riemannHypothesis_of_logChebyshevDeficitPrimitive_bound` consumes `|D(T)| <= B*exp(T/2)` with a constant `B`. A uniform lower bound on the cross term above would provide precisely that scale. Indeed `exp(-T)*A(T)^2 <= 2*a^2+4*b^2` follows from `exp(T)>=1` and `exp(T)>=T^2/2` for `T>=0`; the new signed inequality would then bound `exp(-T)*D(T)^2` by `2*K^2+2*C+4*a^2+8*b^2`. This paper implication is not the missing lower bound, and no additional conditional RH receiver is being added.

The original TG native-source residue conversion is unchanged. The affine normalization is an auxiliary arithmetic decomposition of the actual Chebyshev source, not a replacement success criterion or a claim that a bounded forcing has a bounded Möbius inverse.

### Checked affine-source support module

`formal/GaloisForLFunctions/RHTower/CCMPrimeDeficitAffineSource.lean` now formalizes the paper reduction above and is imported by `RHTower.lean`. The main checked statements are:

- `abs_ccmPrimeDeficitAffineSource_le`: uniform bound on the exact elementary source after subtracting the dilation of the affine profile.
- `ccmLogChebyshevDeficitPrimitive_eq_affine_reconstruction`: the original deficit is exactly the known affine profile plus the literal Möbius inverse of that source.
- `abs_ccmPrimeDeficitAffineSquareSource_le`: the normalized signed Möbius transform of the source square has a constant bound.
- `ccmPrimeDeficitAffine_coprime_balance`: exact reconstruction-square/coprime-cross balance, retaining every pair.
- `ccmPrimeDeficitCriticalEnergy_add_affine_cross_le`: unconditional bound on the original critical energy **plus** twice the normalized signed cross work.

Verification: the first direct Lean run found one ambiguous absolute-value rewrite; its argument was made explicit. The subsequent direct check passed. Targeted `lake build --old +GaloisForLFunctions.RHTower.CCMPrimeDeficitAffineSource` passed, reporting 13316 jobs. A scratch-only axiom audit of all five statements returned only `propext`, `Classical.choice`, and `Quot.sound`. Final `lake env lean GaloisForLFunctions/RHTower/CCMPrimeDeficitAffineSource.lean` passed without diagnostics. No heartbeat increases, placeholders, numerical experiments, or additional RH hypotheses were introduced.

`scripts/formal_tools.py lint` exited 1 with exactly two errors: missing umbrella reachability for `CHMDStage3TwistedArcGroundStateAndSechAnnihilation` and `EvenSectorPoleFreeNodeTests`. These are outside this edit's scope; neither was modified. The new affine-source module had no lint diagnostic. Whitespace checks were clean.

End-of-cycle audit: formal support progressed, but no new scientific knowledge beyond the corpus/literature is claimed and the hard arithmetic lower bound remains open. This is not an unconditional RH proof, an energy-only estimate, or a completed TG route. The original prime–polar native bound is also still unproved. Next work must attack the stated uniform lower bound on `exp(-T)*CoprimeCross(q,T)`; adding another receiver or dropping that term would not advance the goal.

## Continuation: source regularity and prime-factor sign attack

This continuation obtained **no new hard bound and no formal proof progress**. The exact target remains the uniform lower bound on the complete normalized coprime cross term for `q = M s`; neither the source nor the success criterion was replaced.

The documented deep query `Möbius inverse bounded source coprime cross lower bound` returned partial results. Its report recorded `coverage_snapshot_older_generation`, `semantic_coverage_unavailable`, and interrupted `source_retrieval`; candidate applicability was not certified. The returned source identities and the exact relevant Lean statements were inspected. They did not supply the required arithmetic lower bound. This is not an exhaustive absence claim about the corpus.

The residual-reflection theorem expresses the full reconstruction as a force/count convolution, with no sign hypothesis or lower bound on their product. The twisted Selberg factorization retains a signed finite Möbius factor. Its vanishing complete mass does not by itself bound a causally truncated convolution. The existing gcd-log diagonalization does give positive squares, but its kernel is `(gcd(a,b))*log(gcd(a,b))`; no equality or order comparison transferring that positivity to the complete actual coprime cross form was established.

Two proposed mechanisms were attacked on paper:

1. **Use the smooth settling of the elementary source to control its inverse.** This does not close the argument. With `x=exp(T)`, `N=floor(x)`, `d=log(x/N)`, and the Stirling remainder `E_N`, the exact auxiliary remainder is

   `U = N*d-(x-N)+d/2-E_N`.

   The elementary inequalities `z-z^2/2 <= log(1+z) <= z` for `z>=0`, together with `0<=x-N<1` and `0<=E_N<=1/(12*N)`, give `|U|<=7/(12*N)<=7/(6*x)`. Combining this paper estimate with the already checked exponential settling of the old remainder yields

   `s(T) = c0 + a*frac(exp(T)) + epsilon(T)`,

   `c0 = ccmPrimeDeficitDilationLimit-(EulerGamma+1)+b^2/2`,

   `|epsilon(T)| <= exp(-T)*((T+14)/4+7*|b|/6)`.

   This calculation is **paper-only**, not a new Lean result. It supplies no favorable sign. Indeed the exact finite divisor identity `sum_{n<=x} mu(n)*floor(x/n)=1` transforms the sawtooth term into `x*sum_{n<=x} mu(n)/n-1`. Splitting the source this way therefore exposes the Mertens and harmonic Möbius channels again. Moreover the decay estimate for `epsilon(T-log n)` does not make the terms with `n` near `x` small. Estimating those pieces separately does not prove the original cross bound. Do not mistake exponential settling of the forcing for stability of its inverse.

2. **Recover positivity by peeling one prime at a time.** For a causal profile `f`, extend it by zero to negative time and set `F_p(t)=sum_{k>=0} f(t-k*log(p))`; each relevant sum is finite. Let `C_p` be the coprime form restricted to indices not divisible by `p`, and let `S_p` shift the profile by `log(p)`. Splitting the two prime valuations gives the exact paper identity

   `C(f)(T) = C_p(F_p)(T)-C_p(S_p F_p)(T)`.

   It retains a signed difference, not a lower bound. The restricted coprime form is itself not supplied with a positive-semidefinite hypothesis. Iterating the finite prime splitting returns the existing complete identity `C(q)=M(s^2)`, including the same unbounded endpoint/cross cancellation. Verdict: **REDISCOVERED algebraic reduction**, not a new sign theorem. No new Lean module was created for it.

Anti-theatre audit: no zero exclusion, no uniform cross lower bound, no new scientific knowledge claimed. The strict-subunit cubic source budget is still on a different carrier from the actual native covariance; none of these calculations transports that budget to an integer zero multiplicity. The already checked affine module remains a supporting reduction only.

Anti-laziness audit: the complete source, both prime valuations, the causal boundary, and the signed term were retained; no numerical experiments, extra RH premises, or easier replacement target were introduced. These failed proof mechanisms do not retire TG and are not an external blockage. No Lean source changed or build ran in this continuation. Continue the arithmetic cancellation problem; do not repeat these source-regularity or factorization identities as frontier progress.

## Continuation: zero-specific transport attempt

Previous turn was no proof progress. This continuation also establishes no new source bound or zero exclusion. The proposed repair was to control the evaluator of an actual hypothetical zero, using its vanishing Mellin moment, without asserting a bounded transfer on every native vector. This is a search for the missing TG mechanism, not an additional RH premise.

Current Lean sources show why the simplest realization does not close:

- `BurnolFirstWallZeroDividedSource.xiDivisor_burnolZeroDividedSource_head` uses the actual Xi-zero equation to turn the full vanishing moment into a head/tail identity. The resulting head is `1/(1-rho)`, not zero. That nonzero head cannot be discarded when interpreting the divided source as an evaluator.
- `BurnolDividedShiftEvaluationSeparation.burnolMellinDividedShift_ne_evaluationVector_of_riemannZeta_eq_zero` rules out landing a nonzero closed co-Poisson source's Cauchy divided shift on the zero evaluator. The quantitative predecessor retains the strict-accretive source projection. This excludes that particular proposed realization; it does **not** prove that every possible zero-specific source functional is impossible.
- `BurnolSoninProjectedEvaluationTransport` retains both aperture losses and the norm of the evaluator in its exact bilateral law. Neither the zero equation nor the inspected divided-source identities supplied the missing upper bound by the cubic arithmetic budget.

The documented deep query `actual prime polar source nonlinear covariance finite energy` completed with partial results, older coverage generation, semantic coverage unavailable, and `semantic_retrieval` unfinished. The returned exact-source alternatives were checked at their actual statements. `RoutePNativeCovarianceSource.finite_native_covariance_comparison` compares its covariance with its own native energy; it does not bound that energy. Its undamped full native profile has a separately proved nonintegrability result in `RoutePNativeCriticalSquareEnergy`. That profile is different from the TG prime--polar cumulative energy, so its nonintegrability is not an obstruction to the TG target. The actual-head prime--polar--Gamma producer theorem states an equivalence with the reverse-prime bound and leaves nonnegativity to be proved. Four-prime father/detail positivity does not state domination of the TG covariance.

The complete finite Fourier-jet cubic was also checked before treating it as a global operator. `PrimeBurnolFourierJetCubicClosure.primeBurnolFourierJetCubicRelation_closure_balanced` describes the closure of the relation generated by all packet graphs at balancing parameters; it does not provide a single-valued closed operator compatible with all those packet actions. No arithmetic-to-zero projection map was obtained from it. Do not silently replace that relation by an operator or identify its finite cubic with the zero-counting projection displacement.

Audit: these are existing corpus results, not new scientific knowledge. No paper proof of the hard arithmetic statement was completed, so no Lean support module or additional conditional receiver was added. No numerical experiments or external novelty searches were performed. Both the original native-source admission problem and the exact affine coprime lower bound remain unproved. TG remains active; no route has been retired, and no external blocker has been identified. The next attempt must supply an actual inequality for the signed arithmetic source, rather than repeat these transport and index identifications.

## Continuation: arithmetic sign recovery from randomized energy

Previous turn was no proof progress. The new attempted mechanism kept the exact affine source and randomized only its prime signs. Write `s` for that source, `K` for its checked uniform bound, and put `f(t)=exp(-t/2)*s(t)` for nonnegative `t`, extended by zero to negative time. For a finite prime set `P`, use the literal causal product

`H_P(f) = product_{p in P} (I-p^(-1/2)*shift(log p)) f`.

When `P` contains every prime at most `exp(T)`, its value at every `0<=t<=T` is exactly `exp(-t/2)*q(t)`. No later-time or incomplete-Euler product is substituted for this causal equality.

The falsifiable arithmetic candidate was that the complete deterministic section has a uniformly bounded ratio to its independent-sign mean square (or a polynomial loss in `T` for the integrated version). This would control the actual source; it is **not proved or adopted as a premise**.

The finite Walsh calculation itself is elementary and already represented in the corpus. If independent signs are inserted at the primes, then for the complete finite prime set at time `t` the mean square is

`exp(-t)*sum_{n<=exp(t)} mu(n)^2*s(t-log n)^2 <= K^2`.

This is only the diagonal budget. The deterministic all-plus sign assignment in the product still gives the actual signed Möbius inverse. Conditioning on an increasing prefix of its actual signs replaces the diagonal by coherent cofactor squares; it restores, rather than estimates, the missing mixed terms. Almost-sure or average bounds therefore cannot be assigned to that particular completed sign sequence without an additional arithmetic proof.

The exact hypotheses of the relevant corpus results were checked. `MobiusDivisorRademacherSourceSection` gives the sign-section mean-square identity and explicitly does not bound the exceptional completed section. `RoutePFinitePrimeCovariance` and `RoutePFiniteBiasTransfer` retain the deterministic mean-head energy. Their uniformly summable bias cost only compares nearby gains, rather than replacing the actual gains by unbiased signs. Also, their displayed integral interfaces assume continuous causal input; the affine source has cutoff jumps, so those interfaces cannot be directly instantiated with this `f` without a separate integrability/density argument. Such an adaptation would not supply the missing arithmetic sign estimate.

A stronger one-prime sign proposal was considered: require nonnegative causal autocorrelation of each actual intermediate profile with its next prime shift. The exact energy step retains

`-2*p^(-1/2)*integral f_P(t)*f_P(t-log p)`.

No proof of that sign was obtained. It is not implied by positivity of the randomized square, the complete divisor identity, or a bound on the forcing. A full-ray estimate for a finite Euler product would also introduce values beyond the physical cutoff where the exact reconstruction identity is unavailable. Neither shortcut was used. This attempt does not establish a falsehood theorem for the source-specific candidate; its status remains **unproved**.

The documented random-covariance search returned `partial=false` with older coverage generation and unavailable semantic coverage. A second documented Cartier/Schatten/source-projection search returned `partial=false` with unavailable semantic coverage. Neither checked result supplied an upper bound for the actual zero-transfer projection displacement by the cubic arithmetic budget. An index identity or an isometry alone would not be that bound.

Audit: no new scientific knowledge, signed arithmetic inequality, or zero exclusion was proved. No Lean source changed, no build ran, and no new conditional receiver was added. No numerical experiments or added axioms. The useful constraint on the next attempt is precise: any randomization argument must estimate recovery of the actual prime signs, including the causal boundary and all cofactor correlations. Repeating the diagonal/mean-square identity is not progress. TG and the unconditional RH objective remain active; there is no external-state blocker.

## Continuation: prime jumps and one-sided index rigidity

Previous turn was no proof progress. This turn also did not prove the missing arithmetic bound.

The prime-jump attack retained the exact checked chronology:

`Storage(T) + integral_0^T CriticalEnergy = 2 + 2*Work(T) + JumpBudget(T)`.

`CCMPrimeDeficitChronologicalWork` proves nonnegative storage and a polynomial upper bound for the jump budget. These facts give a **lower** bound for signed work. They do not give the upper bound needed to control energy. The proposed use of the nonnegative prime-power jump weights did not establish a sign for the product with the actual state sampled before each jump. No signed-work estimate was derived, and no positivity premise was inserted.

A second attempted mechanism was to turn zero index into zero kernel using a genuinely one-sided scalar Hardy compression. This would require construction and verification for the same arithmetic operator, not just a general index theorem. The current source checks did not supply that construction:

- `RestrictedUnitaryCubicOperator.lean:21` defines `RestrictedUnitaryDatum` with unitarity, an orthogonal projection, and the Hilbert--Schmidt commutator as fields. It does not construct that datum for the actual zero-counting source.
- `RestrictedUnitaryCubicRelativeIndex.lean:1094` defines the algebra certificate as a conjunction of universal projection algebra and literal arithmetic source identities. The arbitrary projections in its first clause are not identified with an arithmetic zero projector in the other clauses. The strict-subunit certificate cannot be read as an upper bound for an unspecified projection displacement.
- `CCMArithmeticPrimeFredholmOrientation.lean:141` defines the signed Toeplitz index from an already supplied integer grade; the theorem at line 145 computes it as minus that grade. This is not an arithmetic construction of zero multiplicity or a bound on it.
- `ZetaChiHardyPhase` gives the actual critical-line Gamma phase identity. Merely passing to this scalar phase supplies no missing zero-specific source estimate. No scalarization of the TG compression with all required arithmetic and zero-incidence properties was proved.

The two documented deep searches completed with `partial=false`: the prime-jump search reported older coverage generation and unavailable semantic coverage; the scalar-Toeplitz search reported unavailable semantic coverage. Their inspected hits supplied the identities above, not the required signed upper estimate or arithmetic operator construction. These coverage statements do not assert that the entire corpus has been exhausted.

Anti-theatre audit: no new scientific knowledge or frontier movement. Existing source statements were checked again; no generic index lemma was formalized as a substitute. Anti-laziness audit: the actual signed work and the actual operator-construction obligation were tested, without effort-based scope reduction, numerical experiments, or new axioms. No paper proof of a new theorem was completed, so no Lean source changed or build ran. TG remains active and mathematically unresolved, with no external blocker. Future work must produce the missing arithmetic inequality or the actual source-to-zero operator bound, rather than repeat this distinction.

## Continuation: prime-power support, localization, and the literal cubic

No new arithmetic bound or zero exclusion was proved in this continuation.

The attempted producer was a causal inverse estimate using the actual deficit's prime-power derivative jumps. The unrestricted bounded-source inverse estimate is not available. A precise stronger candidate is the following: for a finite horizon `T`, allow profiles on `[0,T]` of the form

`q(t) = a*(exp(t)-1)+b+c*t - sum_{p<=exp(T)} w_p * sum_{k>=1, p^k<=exp(t)} (t-k*log(p))`,

where the outer sum is over primes, and put `S(t)=sum_{n<=exp(t)} q(t-log(n))`. Ask whether fixed constants `C,r>=0`, independent of the horizon and all coefficients, satisfy

`exp(-T/2)*|q(T)| <= C*(1+T)^r*sup_{0<=t<=T}|S(t)|`.

The actual affine reconstruction is a member of this class with `a=1`, `b=-ccmPrimeDeficitAffineIntercept`, `c=-ccmPrimeDeficitAffineSlope`, and `w_p=log(p)`. Thus this candidate addresses an arithmetic producer, rather than supplying another conditional zero-exclusion receiver. Its status is **UNPROVED**, including for the actual coefficients. The arbitrary-coefficient version is stronger than required and could fail; no support-only coercivity theorem is claimed. A polynomial loss would still give subcritical Laplace convergence for the actual deficit at every real part greater than one half, but that implication is not the estimate itself.

The attempted finite-dimensional argument did not close. Distinct-prime divisor incidences can simplify an LCM Gram, but the native chronological Gram is a reciprocal-maximum kernel. No valid domination between the needed forms was established. Averaging a finite prime truncation over later times would also use source values beyond its physical horizon, where it is no longer the original bounded source. Neither substitution is allowed.

The documented query `prime power supported source dilation coercivity spline energy` completed with `partial=false`, older coverage generation, and unavailable semantic coverage. Exact source inspection showed that `PhysicalPrimeEndpointMeshCoercivity` gives lower energy floors from jumps. `CCMCofinalPrimeLogCellCoercivity`, `CCMPrimeCliqueCoercivity`, and `CCMPrimeIslandCoercivity` establish positivity on selected support classes. None of those statements is the required upper bound on the actual reconstructed energy.

The proposed assembly of local estimates was then checked against the existing exact localization machinery. `CCMFiniteLocalizationCover.exists_ccmFiniteLocalization_positive_assembly` already decomposes every compact smooth source into positive local pieces, preserving mass, but retains both signed correction totals. More sharply, `CCMPrimeLocalizationStabilization.ccmLocalizationPrimeTotal_stabilized` says that once the piece diameter is below the first prime translation and the remainder vanishes, the prime correction equals **twice the original complete prime cross term**. Refining the cover does not remove that term. `CCMContinuousLocalizationInvariant` identifies the compensated local energy with the original continuous Gamma/pole quadratic. `CCMLocalizationPrimeBudget` bounds prime localization by a source-dependent absolute-correlation integral; it also proves that continuous compensation can be arbitrarily negative even for a positive actual Weil source. No transfer from that source-dependent integral to the strict-subunit cubic budget was obtained.

The second documented query, `arithmetic source localization signed prime correction global positivity`, completed with `partial=false` and unavailable semantic coverage. One retrieved result requires a useful correction to overly broad descriptions of the operator gap: **a literal arithmetic zero-counting cubic already exists in the corpus**. `CubicArithmeticRectangleSource.exists_faithful_arithmetic_rectangle_cubic` constructs genuine orthogonal projections, with nuclear source corrections, whose ordinary anchored cubic trace is the enclosed Xi multiplicity-copy count. Its source is literally `XiC` on a fixed smooth rectangle. The missing object is therefore not every possible arithmetic realization of zero count; it is a realization with the needed quantitative bound by the TG arithmetic budget.

The normalization in this construction was inspected. `CubicCirculantWindingIntegral.cyclicLoopPhase` is `f/|f|`; its exact logarithmic derivative is `f'/f - (log|f|)'`. The real logarithm integrates out of the winding, but that equality supplies no estimate for the remaining logarithmic current by an unnormalized source norm. Contour admissibility gives nonvanishing on the boundary, not a uniform quantitative reciprocal bound. No estimate for the normalized current or the actual zero-counting cubic was proved. This is not a claim that every possible source-specific transfer is impossible.

Anti-theatre audit: no new scientific knowledge or frontier advance; the localization identities and literal cubic are existing corpus results. Anti-laziness audit: prime-power consistency, the causal horizon, all signed localization corrections, and the actual phase normalization were retained. No numerical experiments, new RH premises, generic substitute index theorem, or Lean edits. No build ran because no dependency-closed new paper proof was obtained. TG remains active; no route is retired and no external blocker is identified. The exact original coprime lower bound and native source admission remain unproved.

## Continuation: moving Euler completion inside its cubic window

The prime-power spline coercivity candidate remains unproved, including for the actual coefficients. The next tested mechanism was narrower: use the exact absence of surviving-prime force before `(m+1)^3` to obtain a positive critical contraction for the moving modulus `m!`. The corpus proves that absence, but it retains the Euler action and deleted-prime force. Its deleted-force square-sum estimate is a coefficient estimate; the Mellin estimate explicitly retains a cost proportional to the carrier length. Neither is a bound on the complete coherent time energy.

**Paper result selected for formal verification:** positive critical renewal mass can be arbitrarily large *inside that same cubic window*, even with a moving factorial modulus. This rejects the proposed inference from the cubic causal cutoff alone to contraction. It does not reject signed cancellation for the actual deficit or retire TG.

Here is the dependency-closed paper proof. Let `C=(log(4)+4)+(8+Mertens.mertensTail)`, the exact constant in the existing prime Mertens estimate. Choose an integer `n>=2` with `log(n)>=4*C`, and set `m=n^2`, `U=n^3`, `N=n^6=U^2`. Subtract the prime Mertens estimates at `U` and `m`:

`sum_{m<p<=U} log(p)/p >= log(n)-2*C >= log(n)/2`.

Every prime in this interval is coprime to `m!`, hence has rough coefficient one. Also `n<=sqrt(p)` and `log(p)<=3*log(n)`, so

`n*log(p)/p <= 3*log(n)/sqrt(p)`.

Summing and cancelling the positive `log(n)` gives

`ccmEulerCriticalMass (m!) U >= n/6`.

The existing exact product-square inclusion therefore gives

`ccmEulerRenewalCriticalMass (m!) N >= n^2/36`.

But `N=m^3<(m+1)^3`, so the existing cubic causality theorem gives zero surviving-prime work at `T=log(N)`. Choosing `n` arbitrarily large makes the critical mass arbitrarily large while that work remains zero. No prime number theorem, numerical experiment, actual-deficit sign assumption, or RH premise enters this argument.

The positive survivor is the explicit moving-scale prime mass and its renewal-square lower bound, together with the exact causal separation. This is a boundary statement within TG, not the missing source-to-zero estimate and not a claim of external scientific novelty.

### Verified moving-cutoff boundary

`formal/GaloisForLFunctions/RHTower/CCMPrimeDeficitEulerMovingMass.lean` now proves the two quantitative lower bounds and the unconditional statement `exists_ccmEulerMoving_cubic_window_large_mass`: for every real bound there are positive `m,N` inside the cubic causal window with larger critical renewal mass and exactly zero surviving-prime work. The module is imported by `RHTower.lean`. The failed mechanism and positive survivor are recorded in `docs/drafts/pipeline/5-failed/tg-cubic-causality-positive-contraction-2026-10-15.md`; TG itself remains in progress.

Verification completed:

- Targeted `lake build --old +GaloisForLFunctions.RHTower.CCMPrimeDeficitEulerMovingMass` passed, reporting 13334 jobs.
- Scratch-only checks of the referenced mathlib names passed. All three theorem axiom audits returned only `propext`, `Classical.choice`, and `Quot.sound`.
- Final `lake env lean GaloisForLFunctions/RHTower/CCMPrimeDeficitEulerMovingMass.lean` passed without diagnostics.
- `scripts/formal_tools.py lint` passed; it reported existing large-file warnings. No heartbeat increases, additional axioms, placeholders, or numerical experiments were introduced.

The source search for causal prime-power coercivity completed with `partial=false` and unavailable semantic coverage. The moving-Euler search was partial with `semantic_retrieval` unfinished. A reciprocal-log Levy-clock search was also partial, with two queries and reranking unfinished. No zero-count-preserving reciprocal-clock transform was obtained; a finite-variance reinterpretation alone was not substituted for the deterministic zero-charge estimate. These searches do not establish exhaustive absence or external novelty.

Anti-theatre audit: the checked result strengthens the fixed-modulus obstruction by allowing factorial moduli to grow while retaining the exact cubic causal restriction. Its positive prime-window lower bound is explicit. It does not prove the actual deficit grows too fast, disprove signed cancellation, bound the zero-counting cubic, or advance the missing arithmetic upper estimate. No external scientific novelty is claimed.

Anti-laziness audit: the arithmetic coefficients, complete ordered prime-pair square, and deleted-force distinction were retained. The failed inference is closed with a positive theorem rather than a generic index lemma. The original arbitrary-coefficient spline proposal is still unproved, not refuted by this result. The main next obligation remains a signed bound for the actual source, such as the existing affine coprime lower-bound target; replacing it with a positive renewal contraction is now explicitly excluded by this causal argument alone. TG and unconditional RH remain active and unresolved.

## Continuation: actual neutral quadratic work and phase normalization

No new dependency-closed paper proof, Lean theorem, or arithmetic upper bound was obtained in this cycle. The moving-Euler lower bound above remains the last newly verified result. No Lean files were changed and no build or lint run is claimed for this documentation-only continuation.

The signed-action attempt used the actual coefficient vector from `CCMPrimeDeficitNeutralWork.lean`. At `N = floor(exp(T/2))`, it retains `mu(n)` for `n <= N`, has coefficient `-(n/N) * sum_{j<=N} mu(j)/j` for `N < n <= 2N`, and vanishes afterward. Its harmonic moment vanishes exactly. With `R` the complete divisor pole remainder, the unresolved full quadratic work is

```
Q(T) = sum_{m,n <= 2N} a_N(m) a_N(n) R(T - log(m) - log(n)).
```

Existing source theorems give `D(T) = L(T) - Q(T)`, a critical-scale polynomial bound on `L`, and a critical-scale polynomial bound on the entire absolute diagonal of `Q`. They do not give that bound on the unequal-label sum. `CCMPrimeDeficitCompletePole.ccmPrimeDeficitDivisorSource_harmonic_neutral_bound` retains the square of the coefficient l1 mass. Removing the exponential pole therefore does not itself supply the missing square-root-scale cancellation.

The attempted variational shortcut did not close this gap. `CCMPrimeDeficitCoefficientAction` and `LogarithmicReconstructionVariation` establish exact stationarity at the actual Möbius vector, but the Hessian is the signed complete doubled-source form. No minimizing or maximizing property was established for the actual vector. The two-point determinant in `CCMPrimeDeficitShortSourceMatrix` does not by itself decide the restriction to harmonic-neutral vectors; it was not used to claim such a no-go. Free coefficients beyond the half cutoff preserve the reconstruction action, but no extension with both controlled coefficient cost and controlled full quadratic work was constructed.

The direct zero-counting transfer was also checked again, without claiming novelty. `CubicArithmeticRectangleSource` already realizes actual enclosed Xi multiplicity as an ordinary anchored cubic trace. `CubicCirculantWindingIntegral` uses the actual phase `f/|f|` and proves

```
(phase(f))' / phase(f) = f'/f - (log |f|)'.
```

The exact derivative integrates away; the reciprocal factor in `f'/f` remains. No estimate for this normalized current or its cubic realization by the TG source budget was proved. The arbitrary completion-frame identities in `PrimeBurnolSourceFrameCubicHolonomy` do not identify that frame with the required arithmetic phase. `PrimeBurnolThetaCubicTraceCancellation` concerns its specified admitted traces and masks; its cancellation was not transferred to the actual zero-counting cubic. The inspected source-response determinant theorem in `CCMSourceResponseDeterminantDichotomy` requires a positive-semidefinite metric and boundary hypotheses, and does not discharge the actual signed arithmetic inequality. The critical-line feature projection equality in `HedenmalmWardGreenRemovableExtensionKernelProjection` is explicitly equivalent to RH, so it cannot be inserted as an unconditional producer.

Search accounting: `signed Euler action cancellation renewal critical source bound` ended partial with reranking unfinished; `harmonic neutral actual Mobius quadratic deficit Hessian lower bound` ended partial with semantic retrieval unfinished. Both reported older coverage-generation snapshots and unavailable semantic coverage. `orthogonal Riesz projection arithmetic trace defect zero exclusion` ended partial with two queries, the deadline, and filtering/judging unfinished. Exact relevant Lean statements were inspected. These searches prove neither exhaustive absence nor external novelty. No external literature search or numerical experiment was performed.

Anti-theatre audit: no new scientific knowledge or frontier movement this cycle. Several checks repeated existing corpus distinctions; another generic stationary-action, phase, or index receiver would repeat that work. The next cycle must attempt a proof of the actual unequal-label cancellation or an estimate on the same normalized arithmetic cubic that counts zeros. The route remains TG; this is not a reason to pivot or retire it.

Anti-laziness audit: the unresolved signed mixed term and reciprocal normalization were confronted directly. Neither was replaced with a diagonal, averaged-sign, or separately supplied index estimate. No effort-based scope reduction, extra RH premise, axiom, or substitute Lean module was introduced. The affine coprime lower-bound target and native source admission remain unproved. The unconditional RH goal remains active, with no external-state blocker.

## Continuation: cross-route one-sided tools recovered and applied

User correction: search other routes' and agents' Lean work for usable mechanisms, including previously proved two-sided-to-one-sided reductions. The temporary goal pause was followed by an explicit active status. The full objective remains unconditional Lean RH through TG.

This audit found a directly applicable theorem that the preceding cycles missed. `ChebyshevDeficitPrimitiveOneSidedRH.lean:580` already proves RH from either signed linear envelope of `exp(-T/2) D(T)`. Its public lower and upper versions are at lines 649 and 666:

```
forall T >= 0, -B (1+T) exp(T/2) <= D(T)  ==> RH
forall T >= 0,  D(T) <= B (1+T) exp(T/2)  ==> RH.
```

The proof uses a positive comparison measure and Landau's theorem. Its real-axis continuation is justified by nonvanishing of the pole-removed zeta function on the positive real axis; the resulting half-plane continuation excludes actual zeros. This is existing corpus mathematics, not a new result or an unconditional proof of the bound.

### Exact consequence for the current TG work

Let `W(T) = ccmPrimeDeficitShortQuadraticWork T`. The existing unconditional error estimate is `|D(T)-W(T)| <= 7 exp(T/2)`. Thus **either** of

```
W(T) <= B (1+T) exp(T/2),
-B (1+T) exp(T/2) <= W(T),
```

for every nonnegative `T`, suffices: transfer the selected side to `D` with constant `B+7` and apply the existing one-sided theorem. Both compositions were checked in `/tmp/tg_cross_route_one_sided_audit.lean` using `lake env lean`; the command exited 0. This is an applicability audit with explicit unproved arithmetic premises, not a new conditional leaf or a claimed solution.

For the exact neutral decomposition `D=L-Q`, the sufficient lower comparison is

```
Q(T) >= L(T) - B (1+T) exp(T/2).
```

That composition also passed the same Lean scratch audit. It retains the actual linear term and every mixed pair. No global sign of `Q`, no absolute bound on `Q`, and no positivity on all coefficient vectors is required by this target. The comparison itself remains the open arithmetic core. The existing polynomial bound on `L` is not silently replaced by a linear one. The alternative attempt to impose an eventual fixed sign was not selected; no new sign theorem or no-go is claimed.

### Other routes' reusable mechanisms

- `CCMUnitRieszSuzukiGreenPositiveInverse.lean:103,125,236` gives an exact inverse with positive coefficients: `g(t) + (3/2) integral(g) + (1/2) integral(integral(g))`. Its order preservation transfers a one-sided bound on the actual corrected Green source to the opposite signed Suzuki bound, retaining the boundary correction. This is a concrete positive inverse, unlike the signed Möbius inverse. It cannot be transferred between those operators without an identity.
- `MobiusDivisorOneSidedPowerGapBootstrap.lean:241,596,610,632` gives one-sided subpower control, sampling on arbitrary fixed positive integer powers, and adaptive power-window criteria for the actual Möbius-divisor Abel moment. Its proof combines endpoint monotonicity with a two-step contraction of the supremal zero displacement. A bounded upper sample is required in every sufficiently late window of width `n^(1-delta)`, for some `delta>0`; arbitrary cofinal returns do not meet that hypothesis.
- `MobiusDivisorLowerStripPowerGapBootstrap.lean:491,515,867,881,903` supplies the lower-bound mirror. Its source-level unconditional sample transport is `min(A(k)/k,0) - (n-k)/sqrt(n) <= A(n)/n` for `1<=k<=n`, giving a direct square-root-gap lower transport before the general power-gap bootstrap. These lower-mirror statements were inspected in source, not included in the scratch import audit.
- `GaussianPrimeBudgetOneSidedLaw.lean:695,947` needs only weighted integrability of the **positive excess** above a Gaussian prime-versus-continuum budget, for every positive Laplace weight. A pointwise bound or two-sided absolute norm is not needed. It supplies actual zero exclusion through the same positive/negative-part Landau mechanism. Transport of TG's source to this specific Gaussian excess is still required before use.
- `WeilParityPoleOneSidedRH.lean:118,125` shows either single literal parity test at every aperture already decides RH. Lines 206 and 358 give even-pole majorant and odd-pole nonnegative-minorant criteria with explicit arithmetic order hypotheses. They do not construct such a positive comparison system.
- `CCMPrimeDeficitBohrFlux.lean:378,412` had already applied the one-sided deficit theorem and proved cofinal two-sign oscillation of the actual incoming deficit. Reproving a generic one-sign obstruction would repeat existing work. `MertensSquareRootOmega.lean:706` and `WeilLagFunctionOneSided.lean:477` supply further one-sided endpoints, inspected in source.

Scratch validation: the actual deficit criterion, upper power-sampling criterion, and Gaussian excess equivalence imported successfully. Their axiom audits returned only `propext`, `Classical.choice`, and `Quot.sound`. Both signed short-work transfers and the neutral lower comparison elaborated successfully. No new Lean repository module, umbrella edit, arithmetic hypothesis discharge, numerical experiment, or full build was made.

Search accounting: the neutral-positivity deep query was partial with two subqueries and semantic retrieval unfinished; the sign-oscillation deep query completed with `partial=false`. The unrestricted cross-route deep query was partial at reranking and reported older coverage and unavailable semantic coverage. Rephrasing directly to lexical `oneSided riemannHypothesis` recovered the relevant criterion family, including the lower power-gap mirror. This is a warning against relying only on broad semantic rankings or restricting discovery to the current source-module prefix.

Anti-theatre: these are recovered existing tools, not new scientific knowledge. The mathematical frontier has not moved, but the next proof obligation has been corrected: one signed envelope on the actual short quadratic work is enough. Anti-laziness: exact carriers, signs, window quantifiers, and boundary corrections were checked; the direct TG compositions were run in Lean. The next research cycle must attack that one-sided arithmetic inequality and check cross-route mechanisms before inventing another receiver. TG remains active and the inequality remains unproved.
