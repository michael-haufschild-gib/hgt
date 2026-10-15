# HF: unrestricted prime-blind positivity

Status: IN PROGRESS, resumed by user. Original goal: unconditional Lean proof of the Riemann Hypothesis through route HF. No completion claim.

## Controlling user correction

User rejected the isolated-prime reflection branch below as busywork. Do not formalize it or continue sharpening obstructions. No new Lean code until a credible paper-proof strategy addresses HF's actual unrestricted positivity obstacle. On resumption, read broadly across the current Lean corpus, synthesize the big picture, and reason about a mechanism that could close the main gap. The side conjecture below is historical working reasoning, not an authorized next task. No research leaf was created. The owned scratch API check exited with errors before cancellation; its file was removed.

## Constraints

- Stay on HF; attack its missing positivity producer, including after failed conjectures.
- Mathematical evidence: current local Lean corpus and installed Lean dependencies. No web, external novelty audit, numerical experiments, or assumed RH.
- No added axioms, admissions, heartbeat increases, full builds, commits, or pushes.
- Final audit: foreground `lake env lean` on each changed leaf; wire new leaves into umbrella; lint; inspect axioms in `/tmp`.

## Plan and evidence

1. In progress: identify exact unrestricted HF obstruction from Lean definitions and proofs, using corpus search.
2. Form exact conjecture targeting that obstruction; attack and complete paper proof before formalization. Failures must retain their strongest positive survivor and drive next HF conjecture.
3. Formalize dependency-closed results and audit actual statements, imports, lint and axioms.
4. Continue toward actual `RiemannHypothesis`; intermediate bridges do not satisfy goal.

Available tool set has no `update_plan` or `multi_tool_use.parallel`; this card tracks plan, and independent tool reads use `Promise.allSettled`.

## Initial frontier verified in Lean

- `WeilConeUniquenessUnconditional.lean`: every full-positive weight is von Mangoldt on n ≥ 2, and full positivity is equivalent to RH plus that identification. This is uniqueness, not existence.
- `WeilMarkovOneBoundState.lean`: RH is absence of a negative-definite Markov two-plane. One negative Markov direction exists unconditionally.
- `PrimeBlindNonnegativeConeReduction.lean`: only nonnegative single tests reduce to the log 2 window. Does not establish unrestricted finite-mixture PBAP.
- Corpus query `route HF`: search finished, but coverage reports stale/pending compiler views and unmeasured semantic coverage. Candidate source must be checked, not treated as certified output.
- Corpus query `prime blind archimedean positivity`: finished; saved `/tmp/hf-pbap-search.json`.

## Current attack

Paper reasoning only. Broad source reading now covers the unrestricted HF cone, its actual null family, the Phi-Doob form, twisted-arc minimum principle, arithmetic Hodge constructions, and the Sonin/co-Poisson source spaces. The target remains unrestricted HF positivity. No main positivity theorem or credible complete proof has been obtained; no Lean work is queued.

The present attempt is to derive a positive arithmetic quotient energy whose boundary value is the **entire** archimedean-plus-pole form. The source-defined co-Poisson quotient is available in the corpus; the equality with the HF form still needs a proof. Merely declaring a positive norm, invoking GNS, or assuming a positive limiting trace does not supply that equality.

### Big picture from actual Lean source

- `WeilFullConeOneSidedCriterion.PrimeBlindPositive` quantifies over arbitrary finite nonnegative mixtures of complex compact C2 tests. The summed real autocorrelations vanish at every integer logarithm. The individual tests need not be nonnegative, disjoint, or separately blind.
- `WeilConeUniquenessUnconditional` and `TwistedArcMinimumPrincipleProof` already close the passage from an existing positive full cone to RH. The scalar twisted-arc minimum principle produces annihilating measures and Xi-divisible blind witnesses; its statement does not supply the missing quadratic positivity.
- `WeilPhiDoobArchimedeanJumpAndHalfLineFolding` already gives the complete identity M(Phi v) = E_arch(v) + sum E_prime(v) - integral Phi*cosh(x/2)*v^2. Both jump energies are positive. The required gap one on odd or primitive tests is still the full RH-strength assertion.
- `PrimeBlindPoleCuspIdentity` identifies the pole contribution with the cusp value of the cosine-dilation transform. A quadratic Green calculation must retain this term exactly.
- `DeningerArithmeticRealHodgeFactorization`, `DeningerClosedGeneratorHodgeWeilPurityUniversalityLaw`, and `RiemannGammaCoPoissonHodgeGreenDescentLaw` construct the relevant source structures but still leave the global positivity/compatibility/descent statement. They are possible tools, not an available positivity producer.
- `BurnolCoPoissonSourceSpace` defines an actual closed source and its orthogonal quotient; `BurnolCoPoissonQuotientDilationCollapse` removes the source projection after dilation on the next-aperture quotient. `BurnolCoPoissonDouglasFactorization` still assumes the required operator order. Do not substitute that assumption for a proof of HF.
- `ConnesTheorem5Positivity` assumes positive cutoff representations and their convergence. `ConnesTraceFormulaWeil` proves finite-chart asymptotics. The identity between those positive cutoffs and the full arithmetic limit must be established before these can close HF.

### Exact paper normalization for the current attempt

For a real log test h, put f(x) = x^(-1/2) h(log x), x>0, and let C be the unitary cosine transform C f(x)=2 integral_0^infinity cos(2*pi*x*y)f(y)dy. Write M for multiplication by log x. Mellin Plancherel gives the archimedean term as the quadratic form of H=M+C M C.

Indeed, with F(s)=integral f(x)x^(s-1)dx,

    Mellin(C f)(s) = chi(s) F(1-s),
    chi(s) = pi^(1/2-s) Gamma(s/2)/Gamma((1-s)/2).

Differentiation and chi(s)chi(1-s)=1 give

    Mellin((M+C M C)f)(s) = (chi'(s)/chi(s)) F(s).

At s=1/2+it this multiplier is exactly Re psi(1/4+it/2)-log pi. The pole term is 2 F(1)F(0). Normalized dilation D_n f(x)=sqrt(n)f(nx) has inner product equal to the log-test autocorrelation at log n. Thus the full mixture target is precisely the conductor quadratic plus the pole boundary pairing, subject to the summed integer-dilation orthogonality relations. This normalization is a working derivation of the existing datum, not a new positivity result.

Any proposed positive realization must annihilate the existing Xi-divisible null family, not merely dominate a smaller class of tests. A bare L2 norm or an uncorrected co-Poisson norm does not have that property. The next substantive step must produce and justify the actual quotient Green identity, including its cusp term and limiting domain, or find a different argument for the same unrestricted HF inequality. Do not formalize the normalization or create another conditional bridge while this step is missing.

### Reading and verification state

No web or novelty checks; no numerical mathematical experiments; no new Lean source or builds. Corpus search results were inspected alongside actual Lean statements. `/tmp/hf-dilation-energy-search.json` reports partial coverage and poor candidates, so it supplies no additional proof evidence. The source reads above do not replace a fresh compilation audit when an eventual main proof is ready.

## Cycle 1: reflected-prime positivity

Current source checks extend initial frontier: `WeilPhiDoobArchimedeanJumpAndHalfLineFolding` already proves the complete positive Dirichlet identity and its RH-equivalent gap-one inequality. `WeilPhiDoobReflectedKillingPotentialAndDisjointSupportDiagonal` already handles reflected archimedean killing; no need to rebuild those bridges.

Conjecture tested: the product-prime pairing of every real smooth half-line test is nonnegative, permitting its removal from the odd-sector comparison. Verdict: FALSE, by the exact isolated-atom construction below. This kills only that comparison, not HF.

### Dependency-closed paper proof and positive survivor

Let p ≥ 2 be an integer, and let f be real, continuous, compactly supported in [a,b], where log(p-1) < 2a and 2b < log(p+1). Its convolution square vanishes at every integer logarithm log n except log p (weights n=0,1 vanish separately). Indeed a nonzero product f(t)f(log n-t) requires 2a ≤ log n ≤ 2b, forcing p-1 < n < p+1 and therefore n=p.

Thus Π(f)=Λ(p)/sqrt(p) · ∫ f(t)f(log p-t) dt. Reflection Rf(t)=f(log p-t) preserves Lebesgue measure and is an involution. Set f+ = (f+Rf)/2, f- = (f-Rf)/2. Pointwise f·Rf = (f+)²-(f-)², and integration gives the exact spectral decomposition Π(f)=Λ(p)/sqrt(p)(||f+||²-||f-||²). The two sectors are orthogonal and their squared norms sum to ||f||². Consequently |Π(f)| ≤ Λ(p)/sqrt(p)||f||², with equality of either sign on its respective reflection sector.

For prime p, choose c=log p/2 and any sufficiently small r>0 with [c-r,c+r] contained in the isolating window and in (0,∞). An even smooth nonzero bump B supported in (-r,r) gives f+(x)=B(x-c) and f-(x)=(x-c)B(x-c). Their reflection signs are +1 and -1; their positive squared masses give strictly positive and strictly negative Π respectively. No numerical experiment, RH premise, or positivity premise is used.

Historical positive survivor: exact reflection-sector classification and sharp norm bound for the actual prime pairing, with both sectors realized by actual smooth compact half-line tests. NOT QUEUED FOR FORMALIZATION: user explicitly rejected this side branch. This is not an RH proof or a claim of literature novelty.

Superseded direction from that audit: global compensation in the combined half-line form. The controlling current task is the unrestricted positivity attack above, not further work on the isolated-atom statement.
