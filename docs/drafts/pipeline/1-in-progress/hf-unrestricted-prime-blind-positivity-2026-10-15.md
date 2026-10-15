# HF: unrestricted prime-blind positivity

Status: IN PROGRESS, resumed by user. Original goal: unconditional Lean proof of the Riemann Hypothesis through route HF. No completion claim.

## Controlling user correction

User rejected the isolated-prime reflection branch below as busywork. Do not formalize it or continue sharpening obstructions. Latest user instruction now permits Lean code for significant milestone discoveries. Formalize the complete quadratic prime-energy divisor decomposition, with convergence and all mixed terms, while keeping unrestricted HF positivity as the main objective. This does not authorize reviving the rejected isolated-prime branch. The owned scratch API check from that historical branch exited with errors before cancellation; its file was removed.

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

### Paper continuation: the full quadratic divisor lift

This is a calculation toward the main sign, not a proof of full Weil positivity. Following the latest user instruction, its full quadratic prime identity (Q1) has now been formalized. The linear divisor rearrangement already exists in `RiemannKernelTransformInjectivity.lean` (`cuspTerm_add_log`, `tsum_shift_cuspSeries_eq`). It must not be reported as a new advance.

Write

\[
 \psi(t)=(4\pi^2t^4-6\pi t^2)e^{-\pi t^2},\qquad
 \Phi(x)=e^{x/2}\sum_{m\ge1}\psi(me^x),\qquad
 G_r(t)=\psi(t)\psi(r/t).
\]

For a real compactly supported smooth `v`, put `a_t(m)=v(log(t/m))`. On the divisors of an integer `N`, define

\[
 D_N(a)=\sum_{m\mid k\mid N,\ m<k}\Lambda(k/m)(a(m)-a(k))^2.
\]

The complete prime Doob energy has the paper identity

\[
 E_{\rm prime}(v)=\sum_{N\ge2}\int_0^\infty G_N(t)D_N(a_t)\,\frac{dt}{t}.
\tag{Q1}
\]

Derivation: write each original jump with endpoints `x,x-log d`; use `Phi(x-log d)=Phi(log d-x)`; expand both full cusp series. Their half-density factors cancel the original `1/sqrt d`. Set `t=m exp x`, `k=md`, `N=mnd`. The two test values become `a_t(m),a_t(k)`, and the Gaussian factors become `psi(t),psi(N/t)`. This retains every prime power and every pair of theta indices. Absolute exchanges follow for compact `v`: one endpoint lies in its fixed compact support, while the other theta argument has Gaussian decay as `d` grows; near a zero shift, the squared difference is quadratic in the shift.

The graph in (Q1) is a weighted Cartesian product of complete graphs on prime exponents. Its vertex degree is exactly

\[
 \sum_{d\mid m}\Lambda(d)+\sum_{d\mid N/m}\Lambda(d)=\log N.
\]

If `p^e` is the exact power of `p` in `N`, its part of `D_N` is

\[
 (e+1)\log p\sum_{b\mid N/p^e}\sum_{j=0}^{e}
 \left(a(bp^j)-\frac1{e+1}\sum_{i=0}^{e}a(bp^i)\right)^2.
\tag{Q2}
\]

Thus the full prime graph has an exact conditional-variance decomposition, not an isolated-prime estimate. **This does not yet imply the desired sign:** `G_N` is signed outside its central region. The Gaussian weight and the archimedean contribution must be treated together.

The same change of variables carries the Gamma jump energy to a continuum of cofactor pairs `m,n` with `mn<r`. Its coefficient is

\[
 \sqrt d\,\omega(\log d)=\frac1{1-d^{-2}},\qquad d=\frac r{mn},
\]

where the actual source defines `omega(x)=exp(-x/2)/(1-exp(-2*x))`. The polar jump kernel `2 cosh(x/2)` has coefficient `d+1`. Indeed, using `integral Phi*cosh(x/2)=1/2`, its energy is `mu(v^2)-2(C(v)^2-S(v)^2)`, with `C(v)=integral Phi*v*cosh(x/2)` and `S(v)=integral Phi*v*sinh(x/2)`. Consequently the full Weil form at `Phi*v` becomes

\[
 \sum_{N\ge2}\int_0^\infty G_N(t)D_N(a_t)\frac{dt}{t}
 +\int_1^\infty\!\frac{dr}{r}\int_0^\infty\!G_r(t)
 \sum_{mn<r}\left(\frac1{(r/(mn))^2-1}-\frac r{mn}\right)
 \left(v(\log(t/m))-v(\log(tn/r))\right)^2\frac{dt}{t}.
\tag{Q3}
\]

Main proof obligation remains the sign of the **combined** expression (Q3), or the weaker existing odd-sector gap `E_arch+E_prime >= mu(v^2)`. The next paper step must use Poisson symmetry to combine the divisor variances with the continuous cofactor term and preserve the known Xi-divisible radical. Latest user instruction authorizes formalizing significant milestones; the complete quadratic prime decomposition is now verified. Q2's Cartesian-product variance formula and Q3's combined formula remain paper statements. No full Weil positivity theorem, RH proof, or novelty claim is made here.

Search/read state: `/tmp/hf-theta-divisor-search.json`, `/tmp/hf-rational-gram-energy-search.json`, and `/tmp/hf-theta-divisor-quadratic-search.json` finished; all report `partial=false`, but semantic coverage is unavailable and compiler metadata is mostly stale/pending. Actual sources additionally inspected: `WeilWorkPBAPGramPackets.lean` (arbitrary PSD null Gram matrices retain rational cross terms), `ThetaCuspPrimeArchSourceEquation.lean` (literal source equation), and `RiemannKernelTransformInjectivity.lean` (existing divisor rearrangement). No numerical mathematical computation.

Verified formalization: `formal/GaloisForLFunctions/RHTower/WeilPhiDoobDivisorEnergy.lean`. Q1 is expressed in logarithmic coordinates, with `fiber N u = cuspTerm R 1 u * cuspTerm R N (-u)` and test values `v(u-log m)`. The proof establishes the common integrable envelope

`|fiber N u| <= (4*pi^2+6*pi)^2 * N^4 * exp(-pi*N) * (2+exp(2*u)+exp(-2*u))*exp(-pi*cosh(2*u))`.

This proves absolute convergence for bounded continuous tests before any triple-series regrouping. The verified finite-fiber equivalence sends `(m,d,n)` to `N=m*d*n`, `(k,n)=(m*d,n)`, `(m,d)`, using two divisor antidiagonals. The theorem retains every theta-index pair and every prime power.

Public results in namespace `RHTower.PhiDivisorEnergy`:

- `summable_integral_norm_edge`: absolute convergence of all three indices before regrouping.
- `summable_integral_primeJump`: convergence of the original prime-jump integrals.
- `primeEnergy_divisor_hasSum`: the full divisor-integral series has the original prime energy as its sum.
- `primeEnergy_nat_eq_tsum_divisorEnergy_compact`: Q1 with exactly the natural-number prime sum used by the HF Dirichlet criterion, for every real continuous compactly supported test.
- `tsum_divisorEnergy_nonneg`: positivity of the complete signed divisor average, inherited from the actual prime energy. This does not supply the missing Gamma–prime–pole lower bound.

Validation completed: targeted `lake env lean -o .lake/build/lib/lean/GaloisForLFunctions/RHTower/WeilPhiDoobDivisorEnergy.olean GaloisForLFunctions/RHTower/WeilPhiDoobDivisorEnergy.lean` exits 0 without warnings. `/tmp/hf-divisor-energy-20261015-audit.lean` validated the core declarations and mathlib names; `/tmp/hf-divisor-energy-final-20261015-audit.lean` validated the final natural-index capstone. All audited statements depend only on `propext`, `Classical.choice`, and `Quot.sound`. The leaf is imported by `formal/GaloisForLFunctions/RHTower.lean`.

Repository-wide `scripts/formal_tools.py lint` exits 1, reporting unrelated modules unreachable from their umbrellas: `RHTower.CHMDStage17ComplexWavePacketFactorizationAndCoshSinhDecomposition`, `RHTower.DeningerMeyerCausalDivision`, and `HTGeometry.ParabolicCauchyAveraging`. No error for the new HF leaf was reported. Unrelated modules were not edited. No umbrella build, heartbeat increase, web search, numerical experiment, commit, or push was performed by this work.

Resume paper work on the combined Gamma–prime–pole sign. The isolated-prime sector branch remains excluded. The overarching RH goal remains active and incomplete.

## Cycle 1: reflected-prime positivity

Current source checks extend initial frontier: `WeilPhiDoobArchimedeanJumpAndHalfLineFolding` already proves the complete positive Dirichlet identity and its RH-equivalent gap-one inequality. `WeilPhiDoobReflectedKillingPotentialAndDisjointSupportDiagonal` already handles reflected archimedean killing; no need to rebuild those bridges.

Conjecture tested: the product-prime pairing of every real smooth half-line test is nonnegative, permitting its removal from the odd-sector comparison. Verdict: FALSE, by the exact isolated-atom construction below. This kills only that comparison, not HF.

### Dependency-closed paper proof and positive survivor

Let p ≥ 2 be an integer, and let f be real, continuous, compactly supported in [a,b], where log(p-1) < 2a and 2b < log(p+1). Its convolution square vanishes at every integer logarithm log n except log p (weights n=0,1 vanish separately). Indeed a nonzero product f(t)f(log n-t) requires 2a ≤ log n ≤ 2b, forcing p-1 < n < p+1 and therefore n=p.

Thus Π(f)=Λ(p)/sqrt(p) · ∫ f(t)f(log p-t) dt. Reflection Rf(t)=f(log p-t) preserves Lebesgue measure and is an involution. Set f+ = (f+Rf)/2, f- = (f-Rf)/2. Pointwise f·Rf = (f+)²-(f-)², and integration gives the exact spectral decomposition Π(f)=Λ(p)/sqrt(p)(||f+||²-||f-||²). The two sectors are orthogonal and their squared norms sum to ||f||². Consequently |Π(f)| ≤ Λ(p)/sqrt(p)||f||², with equality of either sign on its respective reflection sector.

For prime p, choose c=log p/2 and any sufficiently small r>0 with [c-r,c+r] contained in the isolating window and in (0,∞). An even smooth nonzero bump B supported in (-r,r) gives f+(x)=B(x-c) and f-(x)=(x-c)B(x-c). Their reflection signs are +1 and -1; their positive squared masses give strictly positive and strictly negative Π respectively. No numerical experiment, RH premise, or positivity premise is used.

Historical positive survivor: exact reflection-sector classification and sharp norm bound for the actual prime pairing, with both sectors realized by actual smooth compact half-line tests. NOT QUEUED FOR FORMALIZATION: user explicitly rejected this side branch. This is not an RH proof or a claim of literature novelty.

Superseded direction from that audit: global compensation in the combined half-line form. The controlling current task is the unrestricted positivity attack above, not further work on the isolated-atom statement.
