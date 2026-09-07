# CCM-FU actual divisor harmonic boundary and holomorphic source — 2026-09-07

Goal ACTIVE: unconditional Lean proof/falsification of RH via CCM-FU. RH, SD1, PE4 and assembled PE5 analytic no-go remain OPEN. Do not mark complete or blocked.

Full chain to state at new-turn opening: completed Guinand–Weil source → marked rectangular current → affine Suzuki checkpoints → signed curvature → coherent prime–polar–Gamma/unit-Riesz boundary → Xi-screw Green → RH.

## New verified leaves
1. formal/GaloisForLFunctions/RHTower/DivisorSourceHarmonicBoundary.lean (root namespace RHTower), 8 public theorems.
- divisorHarmonicWeight n = 1/(n(n+1)).
- divisorHarmonicBoundaryTerm n = D(n+1)*weight(n+1).
- divisorHarmonicBoundary = tsum term.
- summable_divisorHarmonicBoundaryTerm.
- divisorHarmonicBoundary_prefix_lower: every N>=1 finite weighted D prefix >=D(1)/3.
- divisorHarmonicBoundary_lower.
- one_thirtieth_le_divisorHarmonicBoundary, divisorHarmonicBoundary_pos.
- sum_primeFreeDivisorIncrement_div_eq: sum b(n)/n = sum D(n)weight(n)+D(N)/(N+1).
- tendsto_primeFreeDivisorDefect_div_succ.
- tendsto_sum_primeFreeDivisorIncrement_div: ordinary sum b/n tends to positive boundary.
Uses existing |D(N)|<=24 sqrt N and nonnegative ordinary prefixes of D, exact twice-Abel summation. Symbolic harmonic_mascheroni_half_bounds at4 and Real.log_two_lt_d9 give D(1)>=1/10. No experiment inputs.

2. formal/GaloisForLFunctions/RHTower/DivisorSourceDirichlet.lean (root RHTower), 12 public theorems.
- divisorSourceCoeff n = (b(n+1):Complex), actual existing b=primeFreeDivisorIncrement.
- divisorSourceDirichlet s = GaloisForLFunctions.RHTower.dirichletSum divisorSourceCoeff s.
- sum_divisorSourceCoeff: exact castD(N).
- norm_sum_divisorSourceCoeff_le: <=24*(N+1)^(1/2).
- divisorSourceDirichlet_converges: ordinary Dirichlet convergence for Re s>1/2.
- differentiableOn_divisorSourceDirichlet and analyticOnNhd_divisorSourceDirichlet: whole Re>1/2.
- divisorSourceDirichlet_partialSum_one, divisorSourceDirichlet_one.
- one_thirtieth_le_divisorSourceDirichlet_one_re, divisorSourceDirichlet_one_ne_zero.
- divisorSourceCoeff_absConv: shifted absolute convergence at real x>3/2.
- LSeriesSummable_primeFreeDivisorIncrement for Re s>3/2.
- divisorSourceDirichlet_eq_LSeries on same safe half-plane for exact b(n).

All20 public theorems axiom-audited ONCE: only propext, Classical.choice, Quot.sound. Scratch checks and both exact corresponding oleans passed. Both wired ONCE into formal/GaloisForLFunctions/RHTower.lean near DivisorUnsignedChannelPositivity. No umbrella, dependency, or lake build run. Do not reaudit/rebuild these completed results.
Global lint run once:18 errors, ALL concurrent unwired HTGeometry.PolynomialODEOddCompact* modules. No new CCM-FU errors. Foreign files untouched. Index refreshed (4changed0removed). git diff --check passed for scoped tracked files. New certificate and PE5 relative links checked.

## Docs
- New docs/drafts/pipeline/3-formalized/ccm-fu-divisor-source-harmonic-boundary.md exact proof and audit.
- Updated PE5 card docs/drafts/pipeline/1-in-progress/ccm-fu-bernoulli-prime-energy.md: nonvanishing divisor-source factor CLOSED, 3remaining steps.
- Frontier current-state paragraph updated, plus mobius-divisor-source-diagonal-dominance.md.
- Universal STATUS MUST-257: regularity does not imply vanishing; retain actual boundary, positive cumulative prefixes can force positive harmonic value. Self-contained exact example; no RH selection assertion.
- Existing finite Bernoulli certificate (previous turn) remains20 separately audited public theorems, untouched.

## PE5 remaining full analytic no-go
a(n)=mu(n)/2^omega(n), b actual source; g=a*b; H(M)=sum_{k<M}(sqrt(k+1)-sqrt k)sum_{d<=k}a(d)D(floor(k/d)).
Existing MobiusDivisorBernoulliPrimeEnergy provides exact finite H identity and H²<=E_half; MobiusDivisorAbelQuadraticDiagonal gives Q<=722M².
1. Construct exact a squared Euler factorization:
(1-X/2)^2=(1-X)*(1+X²/(4(1-X))).
L(a,s)^2=R(s)/zeta(s); correction R(s)=prod_p(1+p^(-2s)/(4(1-p^(-s)))) holomorphic near1/strictRe>.5, positive at1. No fractional Wiener-Ikehara needed.
2. For hypothetical H=O(M), piecewise W(x)=integral_1^x G0(floor u)/(2sqrt u)du has W=O(x). Extend finite landing to L(g,s)=2s(s+.5)integral_1^infinity W(x)x^(-s-1.5)dx holomorphic Re>.5.
3. Exact safe-half-plane product L(g)=L(a)*B (can use Re>2 and new LSeries identity on Re>1.5) implies near1 L(g)^2=B²R/zeta by identity continuation. B1>=1/30 and R1>0 give SIMPLE zero at1; holomorphic square cannot have simple zero. Conclude unconditional H not O(M), even after finite prefix; Jensen and Q<=722M² reject EVERY fixed half-average energy budget. Strong actual survivor needed before retiring PE5.
No need identify B=-zeta'-zeta²+2gamma*zeta in Lean or build Mellin holomorphy specifically for B: new exact ordinary Dirichlet continuation already supplies B. Product algebra can use its literal LSeries landing.
PE5 no-go doesn't refute adaptive PE4 or final SD1.

## APIs / pitfalls
Two namespaces: source root RHTower; Dirichlet APIs in GaloisForLFunctions.RHTower.
DirichletPolyBoundedAbel.tendsto_dirichlet_partialSum_of_poly_bounded C24 alpha.5 applies to sum of shifted b.
DirichletUniformAbel.differentiableOn_dirichletSum gives holomorphy strictly to right of any convergence point. Choose midpoint sigma. Must change set-membership hs to explicit real inequality before linarith.
DirichletWidthOne.absConvAt_of_convergesAt gives absolute convergence one unit right; choose midpoint between .5 and x-1.
DirichletAbsoluteAbscissa.norm_dirichletTerm_le and Summable.of_norm_bounded.
DirichletLSeriesBridge.term_succ_eq, summable_nat_add_iff1, hsum.sum_add_tsum_nat_add1 (zero LSeries term), tendsto uniqueness give exact LSeries equality.
All needed oleans already existed, no new dependencies built.
Complex casts around sums need inner explicit Real type ((sum ... : Real):Complex), otherwise Lean infers complex summands before cast. For composed cast limit, change hb to explicit Tendsto cast sum before simp_rw finite identity.
Top-level have := invalid: wrap example:True:=by. Polymorphic have:=@Name needs universe specialization; candidate scratch proofs verified APIs in context instead. Do not waste a recheck solely on that exploratory scratch failure.
Real.rpow_natCast/rpow_sub/sqrt_eq_rpow verified; avoid rewriting one_div inside fractional exponent. simp only[one_div] closes inverse vs division, rfl may not.
RegularizedDivisorHarmonicLimit and SummableDivisorHarmonicMean inspected: DIFFERENT generic divisor-transform regularizations, not existing proofs of this B boundary.
All new scratch, logs, API probe files scheduled for explicit deletion after memory. No active Lean work remains; only inspect/poll index if necessary before cleanup. Every Lean session completed. Preserve unrelated workers' processes/files.
