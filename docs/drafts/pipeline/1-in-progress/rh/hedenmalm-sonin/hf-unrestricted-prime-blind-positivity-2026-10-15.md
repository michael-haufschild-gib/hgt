# HF: unrestricted prime-blind positivity

Status: IN PROGRESS, resumed by user. Original goal: unconditional Lean proof of the Riemann Hypothesis through route HF. No completion claim.

## Controlling user correction

User rejected the isolated-prime reflection branch below as busywork. Do not formalize it or continue sharpening obstructions. Latest user instruction now permits Lean code for significant milestone discoveries. Formalize the complete quadratic prime-energy divisor decomposition, with convergence and all mixed terms, while keeping unrestricted HF positivity as the main objective. This does not authorize reviving the rejected isolated-prime branch. The owned scratch API check from that historical branch exited with errors before cancellation; its file was removed.

The active goal is the attachment `/Users/michael/.codex/attachments/4946f287-6508-4d1a-a888-72d3a3066aa6/pasted-text-1.txt`. It explicitly requires reading `docs/reports/rh-current-frontier-map.md` and `docs/reports/rh-killed-routes.md`, stating route and hard blockers in chat, and solving significant mathematical obstacles rather than adding criteria, estimates, or no-go results. HF is **Positive Hodge form on arithmetic cohomology**; unrestricted prime-blind positivity is the current realization. The HF section and relevant killed-route entries have been read. The subsequent user correction requires a continuing corpus-grounded conjecture/proof/revision loop. No web, novelty checks, or mathematical numerical experiments.

## Constraints

- Stay on HF; attack its missing positivity producer, including after failed conjectures.
- Mathematical evidence: current local Lean corpus and installed Lean dependencies. No web, external novelty audit, numerical experiments, or assumed RH.
- No added axioms, admissions, heartbeat increases, full builds, commits, or pushes.
- Current compile rule: foreground `lake --old env lean` from `formal/` on each changed leaf; write an olean/ilean only for a required import, never rebuild an existing dependency olean, and never compile an umbrella. Inspect axioms in `/tmp` when a significant milestone is ready.

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

The complete prime-energy divisor identity below is formalized; work on the main sign is on paper. Broad source reading covers the unrestricted HF cone, its actual null family, the Phi-Doob form, twisted-arc minimum principle, arithmetic Hodge constructions, and the Sonin/co-Poisson source spaces. The target remains unrestricted HF positivity. No main positivity theorem or complete proof has been obtained; no further Lean work is queued without a significant proved milestone.

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

## Continuation: full covariance and critical-line compensation

This continuation produced no new HF positivity theorem and no new Lean code. Keep the main goal active. The Gaussian Gram attempt did not produce a factorization of the full form. `WeilWorkSingularArithmeticGaussianPairing.lean` assumes `WeilPositiveFull`; its positive measure cannot be used to establish that premise.

The pole-to-zeta calculation attempted here is already formalized in `PrimeBlindPoleCriticalZetaDefect.lean`. For the symmetrized spectral measure `dν(t)=(1/(2π)) sum c_f |fhat(t)|² dt`, of mass `m`, integer blindness gives

    pole + Gamma = integral (2 + gammaBracket(t) - 2 Re zeta(1/2+it)) dν(t).

Do not re-formalize or call this a discovery. The source also proves the first-moment identity and a second-moment lower bound. `InvertedCosineDistanceGammaPhase.lean` gives a positive distance for *doubly* blind tests; ordinary integer blindness does not provide its extra cosine-dilation vanishing premise.

An exact auxiliary calculation for a finite prime set P retains all rational covariance terms. For σ>0 put

    Z_P,σ(t) = product_{p in P} (1-p^(-σ-it))^(-1),
    A_P,σ(t) = sum_{p in P,k>=1} log(p) p^(-k(σ+it)).

The finite Euler products have absolutely convergent expansions for every σ>0. Integer blindness therefore gives `integral Z dν=m` and `integral A dν=0`. Consequently

    V_P(σ) = integral |Z_P,σ-1|² dν
           = integral |Z_P,σ|² dν - m >= 0,
    V_P'(σ) = -2 Re integral (|Z_P,σ|²-1) A_P,σ dν.

Differentiation is justified locally in σ by the bounded finite Euler product and its uniformly convergent geometric derivatives. This is an auxiliary variance identity, not a significant milestone or a sign proof for the derivative. The factor `|Z|²-1` retains the mixed numerator/denominator correlations. Neither blindness nor positivity of `V_P` determines the sign needed in the derivative. No replacement of this covariance by a Haar average is allowed.

The unresolved constructive step is to identify a positive realization of the **combined** critical Gamma–prime–pole form, with the Euler covariance and pole residue both retained. An unrenormalized positive Euler norm does not yet give this realization. The full Phi-divisor formula (Q3) remains the concrete source expression to match; the known Xi-divisible radical must be preserved. Do not formalize the auxiliary variance calculation or another conditional positivity wrapper while this step is missing.

Additional actual Lean sources read: `WeilWorkPBAPGramPackets`, `WeilPaperPacketCoprimeFibre`, `WeilPaperPacketArchEnergy` (declaration inventory), `WeilPaperCovarianceDualAttainment`, `WeilWorkSingularArithmeticEulerPolydisk`, `WeilWorkSingularArithmeticHarmonicPositive`, `PrimeBlindLevelFloor`, `PrimeBlindPoleCurvatureFloor`, `WeilBlindPoleSignLaw`, and `ThetaRenewalExitDensity`. The renewal denominator is an auxiliary one-sided object; it does not supply full Weil positivity. `PrimeArchFiniteKMSLocalMomentClosure` and `PrimeArchConnesReflectionMain` retain their source-matching or saturation hypotheses.

Completed local searches: `/tmp/hf-combined-poisson-search-20261015.json`, `/tmp/hf-weil-poisson-search-20261015.json`, `/tmp/hf-gaussian-full-gram-search-20261015.json`, `/tmp/hf-integer-blind-zeta-mean-20261015.json`. Deep searches report `partial=false` but semantic coverage unmeasured and compiler freshness mostly pending/stale. Candidates were checked against source rather than treated as proof evidence. No web search, numerical mathematical experiment, build, or commit in this continuation.

## Continuation: theta cutoff and the two pole moments

Main sign remains unproved. No new Lean milestone, source edit, or build in this continuation. The following paper calculation records the boundary term needed by a Gaussian/co-Poisson factorization; it is not queued for standalone formalization.

Keep the physical normalization above and put

    b(x) = -2*pi*x^2*exp(-pi*x^2),
    q_N(x) = sum_{1 <= n <= N} psi(n*x),
    R = N + 1/2,
    qhat_N(x) = q_N(x) - R*b(R*x).

The primitive identity `psi(x) = d/dx (-2*pi*x^3*exp(-pi*x^2))` gives

    integral psi(x) dx = 0,       integral psi(x) dx/x = -1,
    integral b(x) dx = -1/2,     integral b(x) dx/x = -1.

Consequently every finite `q_N` has moments `0` and `-N`, whereas the completed theta source `q` has moments `1/2` and `1/2`. The corrected finite function `qhat_N` has **both moments exactly `1/2`**. For a correction of the form `-R*b(R*x)`, the first moment is `1/2` for every positive `R`; matching the second forces `R=N+1/2`. This explains why retaining only the leading escaping mass is insufficient for the quadratic pole pairing.

There is an exact midpoint-cell representation, not merely a formal asymptotic. On the cell `[k-1/2,k+1/2]` let

    K(t) = (1/2)*(1/2 - abs(t-k))^2.

Then `0 <= K <= 1/8`, and Taylor's formula integrated on each cell gives

    qhat_N(x) - q(x) = x^2 * integral_R^infinity K(t)*psi''(t*x) dt.

Indeed `qhat_N = sum_{n<=N} psi(n*x) + integral_R^infinity psi(t*x) dt`; the displayed remainder is the sum of integral-minus-midpoint-sample errors over the tail cells. Gaussian decay justifies their absolute sum. In particular its `dx` norm tends to zero, as does its `dx/x` norm, by the explicit majorants

    ||qhat_N-q||_{L1(dx)} <= (16*R^2)^(-1) * integral y^2*abs(psi''(y)) dy,
    ||qhat_N-q||_{L1(dx/x)} <= (8*R)^(-1) * integral y*abs(psi''(y)) dy.

The uncorrected escape can also be justified without exchanging a divergent theta integral: right-cell quadrature gives

    ||q_N-q-N*b(N*.)||_{L1(dx)} <= N^(-1)*integral y*abs(psi'(y)) dy.

Thus `q_N(x) dx` tends weakly, against bounded continuous functions on `[0,infinity)`, to `q(x) dx - (1/2)*delta_0`. The midpoint correction additionally fixes the second Mellin boundary moment exactly.

For a general suitable seed `f`, the same correction is the finite operator

    T_N f(x) = sum_{n<=N} f(n*x) - integral_0^(N+1/2) f(t*x) dt.

It specializes to `qhat_N` on `psi`. Its Mellin multiplier in `0 < Re(s) < 1` is

    sum_{n<=N} n^(-s) + (N+1/2)^(1-s)/(s-1).

This identifies the exact linear counterterm but does **not** give a positive quadratic realization. A scalar boundary mass or a nonnegative Peano kernel does not control the mixed Gamma-prime-pole terms. Those terms, including cross terms between different dilations of the boundary profile, remain in the main proof obligation. No inference from scalar positivity to a positive Gram matrix is justified here.

Next concrete main attempt: combine the divisor graph's conditional variances with the Gamma term into one positive variance identity. The full product fiber has signed tails; on `1 <= t <= N`, both Gaussian-polynomial factors in `G_N(t)` are nonnegative. A proposed identity must account exactly for the remaining tails and the pole boundary, retain arbitrary test values and all mixed terms, and annihilate the known Xi-divisible radical. No such identity or comparison has been proved. Do not substitute a per-prime estimate, an isolated graph spectral gap, or a new conditional wrapper for this task.

Focused corpus checks completed: `/tmp/hf-matrix-minimum-search-20261015.json`, `/tmp/hf-theta-boundary-pole-search-20261015.json`, `/tmp/hf-odd-ground-state-search-20261015.json`, and `/tmp/hf-actual-positivity-producer-20261015.json`. All searches terminated; none supplies a new unconditional producer. Coverage warnings remain, so this is not an exhaustive absence claim. `EulerMaclaurinCountertermQuadratureAndOneSidedPBAP` already has general unit-cell identities; `WeilPhiDoobArchimedeanJumpAndHalfLineFolding` already has the exact odd-sector gap criterion. Do not repackage either as a discovery. No numerical mathematical experiment or web search was used.

## Continuation: correlated Gamma prediction and the full quadratic remainder

No main HF positivity proof or new Lean code in this continuation. The constructive paper object below retains the complete arithmetic Gram matrix. Its identification with the full HF form is still unfinished; do not formalize it merely as another positive candidate.

For `alpha > 0`, the unit Gaussian scale vectors

    h_(alpha,x)(r) = sqrt(2/Gamma(alpha))*(2*pi)^(alpha/2)
                     *exp(alpha*x)*r^(alpha-1/2)*exp(-pi*exp(2*x)*r^2)

in `L2((0,infinity),dr)` have Gram kernel

    K_alpha(x,y) = cosh(x-y)^(-alpha).

This follows by the Gamma integral. Distinct scale vectors are linearly independent: remove their common power of `r`, and successively extract the slowest decaying Gaussian from a finite exponential sum. Thus every finite matrix on distinct nodes is positive definite.

Choose finite anchor nodes `A` and finite arithmetic nodes `S` (e.g. `log 2,...,log N`). Let `E_alpha` be the Schur complement of the `S` block of `K_alpha`; equivalently it is the Gram matrix of the anchor vectors after orthogonal projection off the span of the arithmetic vectors. For `beta > alpha > 0`, there is the **all-rank finite-increment inequality**

    E_beta >= E_alpha Hadamard K_(beta-alpha)|_(A x A).

Proof: `K_alpha - diag(E_alpha,0)` is positive semidefinite. Take its Schur product with the positive correlation matrix `K_(beta-alpha)`; use `K_beta = K_alpha Hadamard K_(beta-alpha)`. The resulting inequality for the full matrix descends to its Schur complement. This retains all off-diagonal arithmetic correlations. Increasing finite arithmetic sets gives the same finite-increment inequality for the closed-span projection, by convergence of orthogonal projections. No differentiability of that infinite limit has been established.

At finite arithmetic depth, differentiation is legitimate and gives the positive kernel

    L_alpha(x,y) = d/dalpha E_alpha(x,y) + log(cosh(x-y))*E_alpha(x,y).

The Gamma spectral probability density of `K_alpha` is

    p_alpha(t) = 2^(alpha-2)*abs(Gamma((alpha+i*t)/2))^2/(pi*Gamma(alpha)),
    d/dalpha log p_alpha(t)
      = log 2 - digamma(alpha) + Re digamma((alpha+i*t)/2).

The minimizer's coefficient derivatives drop out of the derivative of the residual Gram matrix by its orthogonality equations. Hence, at `alpha=1/2`, `E_alpha'` is the actual archimedean conductor pairing of the residual packets minus

    (digamma(1/2)-log(2*pi))*E_(1/2).

This is an exact Gamma-generator match. It is not yet the HF match: `L_alpha` also contains the anchor separation term, and neither the pole nor the prime contribution has been absorbed. In particular, normalized prediction monotonicity alone cannot be called full Weil positivity. Projection onto the dilates of one Gaussian is also not a representation theorem for every finite prime-blind mixture.

The finite boundary Gaussian from the preceding continuation makes the remaining terms explicit. Put `g(x)=exp(-pi*x^2)`, `b(x)=-2*pi*x^2*g(x)`, and, for any finitely supported real coefficients `a_n` on positive integers, put

    f(x) = sum a_n*b(n*x),       g_a(x) = sum a_n*g(n*x),
    A(s) = sum a_n*n^(-s),
    f_alpha(x) = -2*pi*sum a_n*(n*x)^(alpha-1/2)*g(n*x).

Then `f_(5/2)=f`. Gamma recurrence gives, with the physical normalization of this card,

    W_Lambda(f) = (d/dalpha ||f_alpha||_2^2)|_(alpha=5/2)
                 - ||g_a||_2^2 + A(0)*A(1)
                 - 2*sum_(d>=2) Lambda(d)*integral f(x)*f(d*x) dx.

Here `W_Lambda(f)` means the Weil form of the log test `u -> exp(u/2)*f(exp u)`. To check the identity: `Mellin b(s)=-s*Gamma_R(s)/2`, `Mellin g(s)=Gamma_R(s)/2`, and

    Re digamma(5/4+i*t/2) - Re digamma(1/4+i*t/2)
       = 1/(t^2+1/4).

Thus the Gamma recurrence subtracts exactly `||g_a||_2^2`. The two pole moments are `Mellin f(0)=-A(0)` and `Mellin f(1)=-A(1)/2`, giving exactly `A(0)*A(1)`. The displayed prime series converges absolutely: the dilation pairing is `O(d^(-3))` because `f(x)=O(x^2)` at zero and is a finite Gaussian-polynomial sum at infinity. Shape differentiation is justified in a neighborhood of `5/2` by the same Gaussian integrability. No sign has been established for the combined remainder.

Next main obligation is an exact coupling of this correlated Gamma-shape derivative with the entire prime operator, the Gaussian resolvent term, and both pole moments. It must cover arbitrary finite mixtures and preserve the Xi-divisible radical. A per-product-fiber spectral-gap estimate or a scalar conductor coordinate does not supply that coupling. Retain this as the concrete constructive attempt; no more standalone cutoff or covariance helper formalization.

Source checks: `GammaConductorSchurCapacity` concerns independent diagonal prime channels and has an unbounded scalar cost; `GammaConductorSchurResidual` and `GammaConductorSchurStrictDefiniteness` retain the actual correlated Gamma kernel. Their strict residual positivity is already in the corpus. `ThetaCuspGaussianScaleOperator` does not identify its first-pair scale operator with the full native source operator. `WeilPositivityFiniteLevelExistence` is a compactness reduction with finite-level existence still required. `RelaxedHerglotzProducerFloor` retains the producer premise at the critical boundary. None was used as an unconditional HF producer.

Finished searches: `/tmp/hf-divisor-gamma-variance-20261015.json`, `/tmp/hf-quadratic-green-producer-20261015.json`, `/tmp/hf-finite-weil-full-limit-20261015.json`, `/tmp/hf-gamma-prediction-monotonicity-20261015.json`. Search coverage warnings remain; actual source statements were checked. No owned live jobs, numerical mathematical experiment, web search, build, or commit.

## Resume audit and exact Gamma predictor remainder, 2026-10-24

Goal remains the unconditional HF proof of RH. The interrupted continuation made no new mathematical advance. This resumed batch revalidated the current sources and made the proposed Gamma transfer more explicit, but did not prove the main sign. No Lean source or build was added. The working card moved to its present `rh/hedenmalm-sonin` directory; use this path on resumption.

### Current source changes that matter

`CHMDPrimeChainSourceFactorization` now gives the complete crossing-prime factorization into nonnegative bipartite prime-chain variances, including absolute convergence, both theta indices, and every prime-power weight (`complete_chain_hasSum`, `complete_chain_norm_summable`). Its product fibers are restricted to the central interval where they are positive. This already accomplishes the positive crossing-sector rearrangement proposed in the earlier continuation; do not rederive or formalize it again. `QuotientSpectralGapAndOddChainCoercivity.riemannHypothesis_iff_odd_primeChain_poincare` still requires the complete archimedean + same-side prime + chain energy to dominate the cosh mass. Neither this criterion nor the quotient/radical reduction supplies that domination.

`CHMDOddProfileArchAbsorptionAndPrimeChainBridge` already absorbs the continuous reflected collar using the decreasing Gamma jump density. The reflected prime collar retains its exact mixed pairing. `OddSupersolutionCriterion` retains both the supersolution inequality and its admissibility data. `GlobalIncidenceAllocationCondition` retains the full allocation inequality. Do not treat those inputs as proved.

### What the positive Gamma remainder actually is

Fix finite distinct prediction nodes `S`, finite anchor nodes, and `alpha>0`. Write `K=K_alpha`, `psi(t)=log(cosh t)`, and let `c_x(s)` be the unique regression coefficients satisfying

    K(x,t) = sum_(s in S) c_x(s)*K(s,t),       t in S.

For the residual Gram `E_alpha` defined above, differentiation and these normal equations give the exact formula

    E_alpha'(x,y) + psi(x-y)*E_alpha(x,y)
      = sum_(s,t in S) c_x(s)*c_y(t)*K(s,t)
          *[psi(s-y)+psi(x-t)-psi(s-t)-psi(x-y)].

This is a genuine positive Gram form, with all mixed prediction coefficients retained. To see its structure, the positive kernels `exp(-delta*psi(x-y))`, `delta>0`, imply that

    B(x,y) = psi(x)+psi(y)-psi(x-y)

is positive semidefinite. Proof: append the base point `0`, give it the negative sum of the other coefficients, differentiate the resulting nonnegative quadratic form at `delta=0+`, and use that its value at zero is zero. Realize `B(x,y)=<b_x,b_y>`. The bracket in the displayed remainder is exactly `<b_x-b_s,b_y-b_t>`. Therefore the remainder is the Gram matrix of

    sum_(s in S) c_x(s)*h_(alpha,s) tensor (b_x-b_s).

The normal equations are essential. Replacing `c_x(s)` by Möbius coefficients does not preserve this formula or its sign. This clarifies the actual operator that would have to be matched to HF; it is not a proof that the full Weil form has this representation. The argument is a consequence of finite Schur-complement geometry, not a new main positivity theorem, and is not queued for standalone Lean work.

### Cutoff-coherent Möbius/Gamma connection and sign audit

For `alpha>0`, define on `x>0`

    k_alpha(x) = -2*pi*x^(alpha-1/2)*exp(-pi*x^2),
    R_(alpha,N)(x) = sum_(1<=n<=N) mu(n)*k_alpha(n*x),
    Pcut_(alpha,N)(x)
      = sum_(2<=d<=N) Lambda(d)*R_(alpha,floor(N/d))(d*x).

The exact finite identity is

    d/dalpha R_(alpha,N)(x) = log(x)*R_(alpha,N)(x) - Pcut_(alpha,N)(x).

It follows from `d_alpha k_alpha(nx)=log(nx)*k_alpha(nx)` and `mu*Lambda=-mu*log`; the product cutoff `dn<=N` is retained exactly. It is invalid to replace `floor(N/d)` by `N`. For the complete pointwise Gaussian series at fixed `x>0`, locally uniform Gaussian decay justifies the corresponding infinite identity. This pointwise fact does not establish convergence in the critical Hilbert/form topology or any limit of quadratic energies.

The underlying arithmetic connection is already formalized in `Deninger/DeningerMobiusConnection` and `HTGeometry/DirichletMaurerCartanMellinOrbitLaw`. Do not present it as a new discovery. At `alpha=5/2`, write `R_N=R_(5/2,N)`, `G_N(x)=sum_(n<=N)mu(n)*exp(-pi*n^2*x^2)`, `M_N=sum_(n<=N)mu(n)`, and `S_N=sum_(n<=N)mu(n)/n`. The earlier finite-Gaussian calculation gives exactly

    W_Lambda(R_N)
      = (d/dalpha ||R_(alpha,N)||_2^2)|_(alpha=5/2)
        - ||G_N||_2^2 + M_N*S_N
        - 2*sum_(d>=2)Lambda(d)*integral R_N(x)*R_N(d*x) dx.

Using the cutoff connection inside the shape derivative produces

    W_Lambda(R_N)
      = 2*integral log(x)*R_N(x)^2 dx
        - 2*integral R_N(x)*Pcut_(5/2,N)(x) dx
        - ||G_N||_2^2 + M_N*S_N
        - 2*sum_(d>=2)Lambda(d)*integral R_N(x)*R_N(d*x) dx.

Thus the correct one-sided prime sign does not by itself cancel the prime term of the full conductor form. All displayed integrals are finite for fixed `N`; the full prime pairing converges absolutely by the `x^2` zero of `R_N` at the origin. No positivity or uniform-in-`N` bound is asserted. In particular, do not use an infinite Möbius preimage as a Hilbert vector without proving its membership. This is an audit of a proposed HF coupling, not a switch to Möbius summatory estimates.

The outstanding constructive obligation is a source-compatible positive representation of the full form, including the cosine adjoint and the rank-two pole pairing. The positive Gamma predictor remainder above is an explicit candidate component; a match to the cutoff-coherent arithmetic operator must be proved, not assumed. The forward theta source, its exact boundary correction, and the complete positive prime-chain decomposition remain available. No new conditional Lean interface or auxiliary formalization is authorized by this batch's mathematical result.

All owned searches finished; no live build or search handle remains. Current output files: `/tmp/hf-gamma-full-compensation-20261024.json`, `/tmp/hf-primeblind-current-20261024.json`, `/tmp/hf-main-compensation-frontier-20261024.json`, `/tmp/hf-doob-resolvent-order-20261024.json`, `/tmp/hf-prime-chain-variance-20261024.json`, `/tmp/hf-gamma-arithmetic-closed-span-20261024.json`, `/tmp/hf-divisor-log-conjugation-20261024.json`, `/tmp/hf-shared-surplus-20261024.json`, `/tmp/hf-gaussian-dilation-density-20261024.json`, `/tmp/hf-mobius-gamma-shape-20261024.json`, and `/tmp/hf-mobius-shape-positive-20261024.json`. The resolvent-order, chain-variance, and closed-span searches returned partial results; use their actual hits, not an absence claim. No web, external novelty audit, numerical mathematical experiment, commit, or unrelated edit.

## Actual blind source spaces and their weighted duality, 2026-10-24

This continuation stays on the HF form. No main positivity theorem, new Lean source, or build. The new paper calculation below connects prediction to the actual unrestricted blindness constraints; it is not a claim that the Gamma predictor already proves HF. Do not formalize it as an isolated helper while the conductor/pole comparison remains unproved.

### Every finite complex mixture gives an actual wandering vector

Realify the physical transforms of the finite complex test mixture, including the square roots of its nonnegative coefficients, into one vector

    F in H = L2((0,infinity), R^k),    D_n F(x) = sqrt(n)*F(n*x).

The mixture's blindness is exactly `<F,D_n F> = 0` for every integer `n>=2`. No individual component is assumed blind. Put

    S_+(F) = closed span {D_n F : n>=2},
    S_-(F) = closed span {D_(1/n) F : n>=2}.

Then `R*F`, `S_+(F)`, and `S_-(F)` are pairwise orthogonal. Besides the defining blindness, the full forward/backward cross calculation is

    <D_m F,D_(1/n) F> = <F,D_(1/(mn)) F> = 0,    m,n>=2.

This retains the mixed rational correlations *inside* each source space: `<D_m F,D_n F>` need not vanish when neither integer divides the other. Those correlations cannot be replaced by independent prime coordinates. The span of the displayed three spaces is not assumed to exhaust `H`.

The componentwise unitary cosine transform satisfies

    C D_n = D_(1/n) C,    C S_+(F) = S_-(C F).

Consequently `C F` is also blind in the Hilbert sense. This does not assert that its Mellin pole moments lie in the original compact-test domain.

### Genuine regression residuals satisfy all integer blindness constraints

For finitely many Hilbert anchors `a_j`, define `V` as the closed span of all `D_n a_j`, `n>=1`, and `S` using `n>=2`. Both are invariant under integer dilation, and `D_d V` is contained in `S` for `d>=2`. Therefore

    e_j = (I-P_S)*a_j

satisfies `<e_j,D_d e_k>=0` for every pair of anchors and every integer `d>=2`. Proof: `e_k` lies in `V`, hence `D_d e_k` lies in `S`, while `e_j` is orthogonal to `S`.

The finite cutoff has an exact boundary term. If `S_N` is spanned by `D_m a_l`, `2<=m<=N`, and

    e_(N,k) = a_k - sum_(l,2<=m<=N) c_(k,l,m)*D_m a_l,

then for `2<=d<=N`,

    <e_(N,j),D_d e_(N,k)>
      = -sum_(l,N/d<m<=N) c_(k,l,m)*<e_(N,j),D_(dm) a_l>.

All other terms vanish by the finite normal equations. Increasing projections converge strongly, so each fixed-dilation pairing tends to zero without a coefficient estimate. This is only Hilbert convergence: it supplies neither convergence of the unbounded Gamma form nor the two Mellin pole moments. It also does not prove that Gaussian-anchor residuals approximate every native blind mixture.

### A positive capacity identity with all source correlations retained

Take a nonzero native realified blind vector `F`, write `m=||F||^2`, and let `S_+,N` and `S_-,N` use only `2<=n<=N`. Let `M` be multiplication by `log x`, and set

    E_+,N(s) = min_(u in S_+,N) ||exp(s*M)*(F+u)||^2,
    E_-,N(s) = min_(v in S_-,N) ||exp(s*M)*(F+v)||^2.

These are genuine finite-dimensional minima. Every native `F` and its finitely many dilates has support in a compact subinterval of `(0,infinity)`, so the weighted Gram matrices are smooth in `s` and remain positive on each actual source space.

Orthogonality gives `<F+u,F+v>=m` for every pair of source corrections. Weighted Cauchy--Schwarz therefore proves the exact finite-depth inequality

    E_+,N(s)*E_-,N(-s) >= m^2.

At `s=0`, both minima equal `m` and their corrections vanish. Differentiating the finite Schur complements gives

    E_+,N'(0) = E_-,N'(0) = 2*<F,M F>,
    E_+,N''(0) = 4*||M F||^2 - 8*||P_+,N M F||^2,
    E_-,N''(0) = 4*||M F||^2 - 8*||P_-,N M F||^2.

In particular,

    (log(E_+,N(s)*E_-,N(-s)))'' at s=0
      = (8/m)*||P_(R*F + S_+,N + S_-,N)^perp (M F)||^2 >= 0.

The factor 8 follows from differentiating the weight `exp(2*s*M)` and the inverse source Gram matrix. The sum of the three subspaces is orthogonal, which gives the final square. No diagonality inside either arithmetic source was used.

### The remaining HF comparison is explicit

The positive dual capacity uses `exp(-s*M)` on the backward source. The actual cosine capacity, transported back by `C`, uses `exp(s*C*M*C)` on that same source. Their first-order difference is the entire conductor `H_Gamma=M+C*M*C`, rather than the one-sided Möbius connection.

For the original native `F`, put `A=integral F(x) dx` and `B=integral F(x) dx/x`, componentwise. The required sign remains

    <F,H_Gamma F> + 2*<A,B> >= 0.

At finite depth the cosine capacity has derivative `2*<C F,M C F>` at zero. Thus the derivative at zero of

    log(E_+,N^F(s)*E_+,N^(C F)(s)/m^2) + 4*s*<A,B>/m

is exactly `(2/m)` times the required HF form. The positive forward/backward capacity inequality above does not compare these two different weights. Proving the conductor/pole comparison on the actual arithmetic sources is the next core obligation. Neither arbitrary Gamma regression coefficients nor ordinary Hilbert convergence discharge it. No new conditional Lean interface is queued.

Source inspection in this batch rechecked the literal co-Poisson source and bilateral quotient projection laws, the full theta arithmetic ground identity, and the covariance-dual attainment theorem. They retain their respective full-form comparison or positivity obligations. Additional corpus searches finished in `/tmp/hf-odd-positive-groundstate-20261024.json`, `/tmp/hf-source-positive-quotient-20261024.json`, `/tmp/hf-gamma-source-orthogonality-20261024.json`, `/tmp/hf-hedenmalm-main-source-20261024.json`, `/tmp/hf-integer-dilate-regression-20261024.json`, `/tmp/hf-moving-schur-generator-20261024.json`, `/tmp/hf-blind-bilateral-source-split-20261024.json`, and `/tmp/hf-blind-hardy-conductor-trace-20261024.json`. Search results are leads, not an exhaustiveness or novelty claim. No owned job remains live. No web, external novelty audit, mathematical numerical experiment, or unrelated edit.

## Closed-source first variation and the complete cosine product matrix, 2026-10-24

Previous goal turn: progress, by the proved bilateral source/capacity calculation. This continuation resolves its first-variation limit and identifies the pole coefficient in the actual deformed cosine pairing. The full HF sign is still unproved. No Lean source or build was added. User reiterated: no web searches and no novelty checks.

### First variation survives the closed arithmetic source

Let `F != 0`, `m=||F||^2`, and let `S` be any closed subspace orthogonal to `F`. Assume `x^s F` and `x^(-s) F` have finite squared norms for `s` in a neighborhood of zero. Define

    E_S(s) = inf { ||x^s*(F+u)||^2 : u in S, x^s*u in L2 }.

For every admissible `u`, the pairing of `x^s*(F+u)` with `x^(-s)*F` is exactly `m`. Cauchy--Schwarz and the competitor `u=0` give

    m^2 / ||x^(-s)*F||^2 <= E_S(s) <= ||x^s*F||^2.

If the weighted norms have two derivatives at zero, both bounds have first derivative `2*<F,M F>`. Consequently

    E_S(s) = m + 2*s*<F,M F> + O(s^2),

uniformly over all such source spaces `S`. This applies simultaneously to every finite arithmetic depth and to the closed span. It uses only the two scalar weighted norms of the original vector, not a derivative of an infinite Gram inverse.

There is also a vector statement. Let `T_s` be the closure of `{x^s*u : u in S, x^s*u in L2}`. The squared norm of the projection of `x^s F` onto `T_s` is

    ||x^s F||^2 - E_S(s) = O(s^2).

Thus that projected correction is `O(|s|)` in `L2`. A first-order pole term cannot be attributed to a loss of differentiability of these native-anchor capacities.

For every native compact C2 vector `F`, its cosine transform `G=C F` is bounded at zero and `O(x^(-2))` at infinity. Both vectors therefore satisfy the weighted-norm condition in a fixed neighborhood of zero. The full HF derivative identity at the end of the preceding section consequently holds for the two *closed* arithmetic source spaces as well as for their finite stages. This closes that limit issue without giving the missing sign.

### The pole is an exact logarithmic cosine boundary pairing

Write

    chi(z) = 2*(2*pi)^(-z)*Gamma(z)*cos(pi*z/2).

For native compact C2 `F`, Mellin cosine duality gives `Mellin(C F)(z)=chi(z)*Mellin F(1-z)` initially on `0<Re z<1` and then through `z=1`. The continuation and its derivative are justified by boundedness of `C F` at zero and its quadratic decay at infinity. Since `chi(1)=0` and `chi'(1)=-1/2`,

    G(0) = 2*A,      integral log(x)*G(x) dx = -B/2,
    A = integral F(x) dx,      B = integral F(x) dx/x.

All formulas are componentwise for the realification of a complex mixture. In particular the complete blind form is

    W(F) = integral log(x)*||F(x)||^2 dx
           + integral log(x)*(||G(x)||^2 - 2*<G(0),G(x)>) dx.

The second integrand is kept as a difference; separating it into a square and a constant would create divergent integrals at infinity. This is an exact boundary representation of the existing pole, not a positivity assertion.

### One family retains the cosine orientation, every integer product, and the pole

For real `s` sufficiently close to zero, set

    a_s(x) = x^s*F(x),       b_s = C(x^s*G),
    U_m(s)(x) = x^s*F(m*x),
    V_n(s) = C(x^s*G(n*x)),                 m,n>=1.

Their actual Hilbert pairing is a multiplicative Hankel matrix:

    K_s(m,n) = <U_m(s),V_n(s)>
      = (mn)^(-s-1) * integral x^s*<F(x),b_s(x/(mn))> dx.

The powers of `m,n` here follow from the normalized-dilation identity; the displayed source vectors themselves are unnormalized. At `s=0`,

    K_0(m,n) = integral <F(x),F(mn*x)> dx.

Hence actual mixture blindness gives exactly `K_0 = m*e_1*e_1^T`, with `m=||F||^2`. This uses products `mn`, not an assumption that the within-source Gram matrices are diagonal.

There is also a scalar operator identity for the continuous product variable. Put `A_F(r)=integral <F(x),F(r*x)> dx`, and let `X_s` multiply by `x^s`. Then

    K_s(r) = (C*X_s*C*X_s)(A_F)(r).

Indeed, taking Mellin transforms of the displayed pairing and substituting `u=x/r` gives

    Mellin K_s(z) = chi(z)*chi(1+s-z) *
      sum_j (Mellin F_j(z))*(Mellin F_j(1-z)).

The same formula is the Mellin transform of `C*X_s*C*X_s A_F`. For `s` near zero these identities hold on a common vertical strip containing the critical line, where the cosine transforms and the weighted integrals are defined. Mellin uniqueness identifies the continuous functions. Differentiation at zero gives the actual Gamma conductor, since `chi(z)*chi(1-z)=1` and `chi'/chi` is symmetric under `z -> 1-z`.

The boundary value is explicitly

    b_s(0) = 2*chi(1+s)*B_s,
    A_s = integral x^s*F(x) dx,
    B_s = integral x^(-s-1)*F(x) dx,
    c_s = 2*chi(1+s)*<A_s,B_s>.

Therefore the complete matrix has the exact decomposition

    K_s = c_s*v_s*v_s^T + R_s,       v_s(n)=n^(-s-1),
    R_s(m,n) = (mn)^(-s-1) *
      integral x^s*<F(x),b_s(x/(mn))-b_s(0)> dx.

The coefficient satisfies `c_0=0` and `c'_0=-<A,B>`. In particular the native pole pairing is exactly `-2*c'_0`.

The remainder has adequate regularity for the whole integer matrix, already for the native C2 class. If `supp F` lies in `[alpha,beta]`, with `alpha>0`, then for `0<=y<alpha`, Abel regularization of the cosine integral gives

    b_s(y) = chi(1+s) * integral F(t)*
      ((t-y)^(-1-s)+(t+y)^(-1-s)) dt.

To justify this, insert `exp(-epsilon*x)` in the defining cosine integral, use the product-to-sum formula, evaluate the elementary Gamma integral, and then let `epsilon` decrease to zero. On `|y|<=alpha/2` the two kernels and their `s` derivatives are uniformly smooth. The original integral also converges absolutely for `s` near zero, since `G(x)=O(x^(-2))`.

The two terms cancel the linear Taylor coefficient in `y`. Thus, uniformly on a sufficiently small closed `s` interval,

    |R_s(m,n)| <= C*(mn)^(-s-3),
    |d_s R_s(m,n)| <= C*(1+log(mn))*(mn)^(-s-3)

outside finitely many products. The finitely many remaining entries are continuously differentiable by dominated convergence. It follows that `R_s` is continuously differentiable in entrywise absolute-sum norm, hence in trace norm on coefficient `ell2`. Since `v_s` is continuously differentiable in `ell2` for `s>-1/2`, the same trace-norm conclusion holds for `K_s`.

At the anchor, differentiation of the actual Hilbert pairing gives

    K'_0(1,1) = <F,(M+C*M*C) F>.

For the whole matrix it gives

    K'_0(m,n) = (mn)^(-1/2)*<F,D_(1/(mn))*(M+C*M*C) F>.

The logarithms from differentiating the dilation factors cancel because `M+C*M*C` commutes with normalized dilation. Combining the anchor derivative and the exact tail coefficient gives the full native identity

    W(F) = K'_0(1,1) - 2*c'_0
         = R'_0(1,1) + <A,B>.

Equivalently, `lim_(n->infinity) n^2*K'_0(n,n) = c'_0`; the complete HF form is the anchor derivative minus twice that boundary coefficient.

This is now an actual cosine/source matrix with the full pole coefficient, rather than a Gamma-only positive candidate. The remaining task is to prove `R'_0(1,1)+<A,B> >= 0` from the native source construction and integer blindness. Entrywise decay and trace-class membership are not that sign proof. Nor may the coefficient `ell2` metric be substituted for the physical source Gram metric. The full within-source mixed Gram matrices must remain in any Schur or operator-order argument. No conditional positivity interface or auxiliary Lean formalization is queued.

Current source checks read `PrimeBlindPoleCuspIdentity` and `DilationAutocorrelationPeriodization` directly; their cusp and reciprocity identities remain the normalization references. All owned search commands finished, including the weighted-cosine, blind logarithmic uncertainty, Sonin generator, capacity derivative, cusp transfer, and fractional-cosine product-matrix searches. No web search, novelty check, numerical experiment, live owned job, build, or unrelated edit.

### Physical source completion of the full conductor pairing

**Conjecture tested:** the complete cosine-matrix derivative descends continuously to the actual closed arithmetic source spaces, without a lower bound on their coefficient Gram matrices. **Paper outcome: proved below.** This removes the coefficient/source-metric gap in the preceding construction; it does not prove the HF anchor sign. No Lean formalization is queued merely for another positivity receiver.

Let `Iu(x)=u(1/x)/x` be unitary inversion on `L2((0,infinity),R^d)`, and put `Fvee=IF`. The finite dimension `d` retains the realification of an arbitrary finite complex mixture. Assume only the native regularity: `F` is compact C2, supported in `[alpha,beta]`, `alpha>0`. Set

    V(F) = closure span { F(n*x) : n>=1 },
    V_N(F) = closure span { F(n*x) : n>=N }.

Define the pairing first on finite arithmetic sums:

    q(u,v) = <u,H_Gamma I v>,
    Q(u,v) = q(u,v) + 2*<integral u,integral v>,
    u in V(F), v in V(Fvee), H_Gamma=M+C*M*C.

Each finite sum belongs to the conductor domain: its cosine transform is bounded at zero and `O(x^(-2))` at infinity, so multiplication of that transform by `log x` is square integrable. Thus these displayed pairings are actual Hilbert pairings on the algebraic sources.

**Exact separated-source kernel.** Suppose `u` and `v` are supported in `(0,b]` and `(0,c]`, with `bc<1`. For the initial smooth compact sources,

    q(u,v) = - integral_0^b integral_0^c
                 <u(x),v(y)>/(1-x^2*y^2) dy dx.

Indeed `Iv` is supported above `1/c>b`, so the multiplication term `M Iv` vanishes on the support of `u`. Differentiating the previously established off-support cosine identity at zero gives

    (C*M*C)(Iv)(x) = - integral t*(Iv)(t)/(t^2-x^2) dt
                   = - integral_0^c v(y)/(1-x^2*y^2) dy,

where the last substitution is `t=1/y`. The factor is exactly one: `chi'(1)=-1/2` multiplies the sum of the two reciprocal kernels. No source Gram inverse enters.

The kernel expansion is an absolutely convergent nuclear expansion between the two physical L2 spaces:

    q(u,v) = - sum_(j>=0) <integral x^(2j)*u(x) dx,
                             integral y^(2j)*v(y) dy>.

For each scalar component the rank-one term has trace norm

    ||x^(2j)||_(L2(0,b))*||y^(2j)||_(L2(0,c))
      = (bc)^(2j+1/2)/(4j+1).

Their sum is finite because `bc<1`. This proves the identity and continuous trace-class extension for every L2 pair in the separated spaces, including limits of arithmetic sums. Compression to closed subspaces preserves the conclusion. In particular take

    b=beta/N, c=1/(alpha*N), N^2>beta/alpha.

Every vector in `V_N(F)` and `V_N(Fvee)` has the indicated support. The **entire infinite arithmetic tail**, measured in its physical source norm, is therefore already covered.

**Completion including the finite part.** Write `H_N(F)=span {F(n*x):1<=n<N}`. The sum

    V(F)=H_N(F)+V_N(F)

is closed: a closed subspace plus a finite-dimensional subspace is closed, and the sum contains every generating dilation. Its orthogonal complement to `V_N(F)` inside `V(F)` is finite dimensional. The corresponding statements hold for `Fvee`.

The mixed pairings with a fixed head vector are bounded in the physical L2 norm. For example

    q(h,v)=<I H_Gamma h,v>,
    q(u,k)=<u,H_Gamma I k>,

and both displayed representing vectors lie in L2. These formulas agree with the separated kernel whenever a head vector also lies in its tail space: such a vector has the tail support, and the off-support formula extends by L2 continuity in the other argument. Consequently the form is independent of the decomposition into head plus tail. Choose representatives for a basis of the finite-dimensional quotient; their linear lift is bounded. This gives a bounded extension of `q` to `V(F) x V(Fvee)`.

In the orthogonal head/tail decompositions its tail-to-tail block is trace class by the nuclear expansion above; every other block has finite-dimensional range or domain and is bounded, hence finite rank. Thus the **full physical-source pairing has a unique trace-class operator extension**. The polar pairing also extends: all left source vectors are supported in `(0,beta]`, all right source vectors in `(0,1/alpha]`, so their vector integrals are bounded L2 functionals. Its rank is at most `d`. Therefore the same conclusion holds for `Q`. This argument supplies actual continuity on the closed sources, rather than inferring it from trace-class coefficient matrices.

**Blind anchor, with its correct physical normalization.** If `m=||F||^2>0` and the mixture is blind at every integer `n>=2`, then for all closed-source vectors

    <u,Iv> = <u,F>*<Fvee,v>/m.

First check finite sums: their cross entries are `A_F(mn)`, zero except at `m=n=1`; their first coefficients are recovered by inner product with `F` and `Fvee`. Then pass to the closures. Thus the compressed inversion is a rank-one partial isometry, with unit singular value, not the coefficient-space scalar `m`. At its normalized anchor `e=F/sqrt(m)`, `eve=Fvee/sqrt(m)`,

    Q(e,eve) = W(F)/m.

**Exact signed tail in the even sector.** When `IF=F`, choose `N>beta`, so both tails are supported in `(0,b]`, `b<1`. On the same physical tail space,

    Q(u,u) = ||integral u||^2
             - sum_(j>=1) ||integral x^(2j)*u(x) dx||^2.

It is strictly negative for every nonzero vector with zero vector integral: if all even moments vanish, polynomials in `x^2` are dense in `L2(0,b)`, componentwise, forcing `u=0`. The pole term has been retained; for vector mixtures its finite-rank contribution has rank at most `d`, not necessarily one.

**What remains unpaid.** Neither this trace-class realization nor its signed tail proves `Q(e,eve)>=0`. The head-to-tail blocks remain present, and no positive order for their Schur complement has been established. The unrestricted source sign is still the main HF obstacle. The next conjecture must use the arithmetic/blind rank-one inversion relation together with this actual conductor operator to pay that coupling; another coefficient-norm estimate or an assumption of Schur positivity would not do so.

Relevant additional corpus source inspected: `BlindCoreWanderingNymanBeurling` gives actual Nyman–Beurling Mellin and wandering identities; `PrimeBlindPoleCriticalZetaDefect` already identifies the pole with the critical-line zeta first-moment defect; `SoninBurnolLogShellChannel` supplies a bounded shell approximation, not the full logarithmic source pairing above. None of those statements supplies the missing sign. The current batch contains paper work only, with no new Lean source, compilation, web search, or novelty audit.

## Cycle 1: reflected-prime positivity

Current source checks extend initial frontier: `WeilPhiDoobArchimedeanJumpAndHalfLineFolding` already proves the complete positive Dirichlet identity and its RH-equivalent gap-one inequality. `WeilPhiDoobReflectedKillingPotentialAndDisjointSupportDiagonal` already handles reflected archimedean killing; no need to rebuild those bridges.

Conjecture tested: the product-prime pairing of every real smooth half-line test is nonnegative, permitting its removal from the odd-sector comparison. Verdict: FALSE, by the exact isolated-atom construction below. This kills only that comparison, not HF.

### Dependency-closed paper proof and positive survivor

Let p ≥ 2 be an integer, and let f be real, continuous, compactly supported in [a,b], where log(p-1) < 2a and 2b < log(p+1). Its convolution square vanishes at every integer logarithm log n except log p (weights n=0,1 vanish separately). Indeed a nonzero product f(t)f(log n-t) requires 2a ≤ log n ≤ 2b, forcing p-1 < n < p+1 and therefore n=p.

Thus Π(f)=Λ(p)/sqrt(p) · ∫ f(t)f(log p-t) dt. Reflection Rf(t)=f(log p-t) preserves Lebesgue measure and is an involution. Set f+ = (f+Rf)/2, f- = (f-Rf)/2. Pointwise f·Rf = (f+)²-(f-)², and integration gives the exact spectral decomposition Π(f)=Λ(p)/sqrt(p)(||f+||²-||f-||²). The two sectors are orthogonal and their squared norms sum to ||f||². Consequently |Π(f)| ≤ Λ(p)/sqrt(p)||f||², with equality of either sign on its respective reflection sector.

For prime p, choose c=log p/2 and any sufficiently small r>0 with [c-r,c+r] contained in the isolating window and in (0,∞). An even smooth nonzero bump B supported in (-r,r) gives f+(x)=B(x-c) and f-(x)=(x-c)B(x-c). Their reflection signs are +1 and -1; their positive squared masses give strictly positive and strictly negative Π respectively. No numerical experiment, RH premise, or positivity premise is used.

Historical positive survivor: exact reflection-sector classification and sharp norm bound for the actual prime pairing, with both sectors realized by actual smooth compact half-line tests. NOT QUEUED FOR FORMALIZATION: user explicitly rejected this side branch. This is not an RH proof or a claim of literature novelty.

Superseded direction from that audit: global compensation in the combined half-line form. The controlling current task is the unrestricted positivity attack above, not further work on the isolated-atom statement.
