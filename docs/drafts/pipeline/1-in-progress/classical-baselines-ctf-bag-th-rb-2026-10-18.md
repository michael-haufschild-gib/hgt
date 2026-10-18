# Classical baseline theorems in CTF, BAG, TH, and RB

- **ID:** classical-baselines-ctf-bag-th-rb-2026-10-18
- **Stage:** 1-in-progress
- **Type:** CANDIDATE (formalization of classical theorems)
- **Source:** user attachment `94c10467-3b24-4880-934a-2f85291fdcbe/pasted-text-1.txt`, items 9–11.
- **Statement:** Unconditional classical approximation, recurrence, mean-square, Jensen–Hermite, and extremal divisor-sum theorems, with their exact RH gaps preserved.

## Scope and acceptance obligations

1. CTF: formalize Burnol's lower bound, raw Möbius nonconvergence in the actual Báez–Duarte carrier, and the supported Selberg row `μ(k) log(N/k)/log N`; connect the row to existing CTF/PM carriers.
2. Resolve the attachment's stronger raw-error `liminf ≥ Σρ 1/|ρ|² > 0` statement. Do not silently identify it with the optimized-distance logarithmic bound or with a positive limsup.
3. BAG: finite Dirichlet polynomial self-return with positive lower density; Carlson's L² mean-value theorem in the domain needed by Bagchi; state the exact tail conditioning still required.
4. TH: fixed degree, increasing shift Hermite asymptotics for the actual Xi Taylor coefficients, including all analytic coefficient estimates. A theorem with those estimates assumed is insufficient.
5. RB: define actual colossally abundant integers and prove the classical reduction, with quantifiers and any threshold made explicit.
6. Verify each delivered leaf with `lake --old env lean <module>`, audit axioms in `/tmp`, wire leaves into their area umbrellas, regenerate indexes and run `scripts/formal_tools.py lint`. No full/umbrella builds, numerical experiments, added axioms, proof holes, heartbeat increases, commits, or unrelated edits.

## Plan

- [x] Read task, project instructions, relevant route evidence and memories.
- [ ] Audit exact classical statements and current dependency coverage.
- [x] Complete CTF/PM statements and Selberg row (classical logarithmic normalization).
- [x] Complete BAG finite recurrence and actual-zeta mean-square baseline on the Bagchi strip.
- [ ] Complete TH Xi-specific Hermite asymptotics.
- [x] Complete RB eventual colossally abundant reduction.
- [ ] Kernel, axiom, wiring, lint, and cleanup audit against every obligation above.

## Evidence and statement audit

- Burnol, *A lower bound in an approximation problem involving the zeros of the Riemann zeta function*, Theorem 1.3, https://arxiv.org/pdf/math/0103058: `liminf D(λ) sqrt(log(1/λ)) ≥ sqrt(Σ mρ²/|ρ|²)`. The logarithmic factor and multiplicities cannot be discarded. This alone does not establish a constant raw-error liminf.
- Báez-Duarte, *Arithmetical Aspects of Beurling's Real Variable Reformulation*, Proposition 4.4, https://arxiv.org/pdf/math/0011254: natural raw sums do not converge in L². This does not by itself state the stronger raw liminf claimed in the attachment.
- Griffin–Ono–Rolen–Zagier, https://arxiv.org/pdf/1902.07321: actual Xi coefficient asymptotics and the general finite-difference Hermite limit must both be covered. Fixed degree and sufficiently large shift do not establish all-degree hyperbolicity at every shift.
- `RHTower/BaezDuarteBurnolMultiplicityAllZeros.lean`: multiplicity-weighted logarithmic lower bound over all critical zeros already present, using eventual lower bounds below an extended sum.
- `RHTower/BaezDuarteMobiusCriticalTailObstruction.lean`: raw full-error nonconvergence and a positive cofinal floor already present; a cofinal floor is not a liminf floor.
- `RHTower/Sieve/LinearMollifierGcdForms.lean`: exact unsupport-truncated coefficient formula, `S₀(N) log N → 1`, and `S₁(N) → 1` already present.
- `RHTower/SimultaneousPhaseRecurrence.lean`: arbitrarily late simultaneous returns; density is a separate obligation.
- `RHTower/RobinExtremalNumbers.lean` and `RobinCriterionRiemann.lean`: global penalized extremal comparison and eventual Robin criterion already present. Existing source does not use the name colossally abundant.

## Session state

Serena symbol lookup rejects the Lean tree as ignored; use exact source text and compiler checks for Lean operations. No callable `update_plan` tool is exposed; this card is the persistent plan. Independent reads use concurrent tool calls. Preserve existing unrelated dirty files, including frontier-map changes.

Research search `Jensen Hermite asymptotics fixed degree xi coefficients --mode deep --no-refresh --budget-seconds 40` completed (exit 0), partial after 40.03 seconds, coverage generation 1451831 pending. No directly applicable Xi/Hermite limit was returned; hits were source-only. Broad initial search completed without its output being retained after tool-output truncation; do not count it as coverage evidence.

## Verification

`RobinColossallyAbundantReduction.lean` compiled with `lake --old env lean -o .lake/build/lib/lean/GaloisForLFunctions/RHTower/RobinColossallyAbundantReduction.olean GaloisForLFunctions/RHTower/RobinColossallyAbundantReduction.lean`, exit 0, no warnings. It defines actual global penalized maximizers, proves `robinExtremalAt x` belongs to this class, and proves the unconditional eventual reduction and corresponding RH equivalence. It does not assert a checked numerical cutoff of 5040. Axiom/wiring/final audits remain.

`SelbergMobiusApproximation.lean` compiled: supported row, unit coefficient bound, first/last coefficients, fixed-index convergence, actual CTF/Nyman/Fermi errors and dyadic transfer. Final direct leaf and axiom audits remain.

User replied “do all. decide yourself”. Use the documented classical normalization. The stronger raw constant-liminf assertion is not supplied by either classical source and must not be reported as proved.

`BaezDuarteClassicalBaseline.lean` compiled, exit 0: strict positivity of the multiplicity-weighted critical mass using Hardy, the extended-real logarithmic liminf lower bound, and raw full-energy nonconvergence in one unconditional theorem. Wired into `RHTower.lean`.

`HTGeometry/AlmostPeriodicReturnDensity.lean` compiled, exit 0: every continuous Bohr almost-periodic function has return sets with positive lower Lebesgue density.

`FiniteDirichletPolynomialSelfReturn.lean` compiled, exit 0: positive lower density of uniform self-return on every compact set for any finite Dirichlet polynomial supported on positive integers. Wired into `RHTower.lean`. `BagchiConditionedTailGap.lean` compiled, exit 0: exact centered-tail identities and quantitative measure-loss transfer.

BAG tail audit: for `1/2 < Re(s) < 1`, the unsmoothed finite head need not approximate the fixed starting value. The required conditioned error is the centered tail increment `(ζ(s+iτ)-D_N(s+iτ))-(ζ(s)-D_N(s))`; unconditioned Carlson mean square alone does not supply this on finite-head return sets.

## Carlson proof work

Deep search `zeta mean square limit Dirichlet polynomial approximation sigma half` completed, partial after the 45-second budget, coverage generation 1452037 pending. No exact mean-square limit found. The returned AFE result bounds a shrinking displaced line and is not the required fixed-sigma limit. `CarlsonHalfPlaneProducerFloor.lean` proves a coefficient-growth consequence, not the mean-square equality.

Candidate dependency-closed proof: use arbitrary-order Euler–Maclaurin truncation at `N = floor(T^a)` on dyadic time windows, where `1 < a < 1/(2-2σ)` for `1/2 < σ < 1`. Choose even order `k` with `k-a(σ+k-1)<0`; all correction and remainder terms then have mean square `o(1)`. The weighted off-diagonal sum is `O(N^(2-2σ) log N)`, so the normalized polynomial mean tends to `Σ n^(-2σ)`. Finite-head subtraction gives the exact tail mean. Existing `DQPT/DqptDerivTower` Euler–Maclaurin is real-valued; complexify via real and imaginary parts, with no new axioms or assumed analytic estimates. This proof is a plan until its missing estimates are written and checked.

`ComplexEulerMaclaurin.lean` now compiled: arbitrary even-order complex formula, direct norm bounds on each cell and the summed remainder. `ZetaEulerMaclaurinArbitraryOrder.lean` now compiled: complex-power derivative tower, exact finite-tail decomposition, vanishing endpoint corrections, and the actual zeta remainder bound for every order. Both wired into `RHTower.lean`. Final direct leaf and axiom audits remain.

Found `Sieve.dirichlet_meanValue_sharp`, with error `104 Σ n |a_n|²`; no logarithmic loss is needed. `ZetaFiniteMeanSquare.lean` is implementing its sharp window transfer and actual zeta finite-head estimate. Use the ceiling cutoff `N = ceil(T^a)` for cleaner inequalities in the final asymptotic proof.

`ZetaFiniteMeanSquare.lean` and `ZetaSuperlinearTruncation.lean` compiled, exit 0: the sharp finite-head bound and the uniform actual zeta truncation estimate on dyadic windows. `ZetaSuperlinearCutoff.lean` compiled, exit 0: ceiling-cutoff bounds, convergence to infinity, weighted-power limits, and existence of a sufficient Euler–Maclaurin order for `a = σ + 1/2`. Both the uniform zeta error and `N^(2-2σ)/T` tend to zero for `1/2 < σ < 1`.

`IntervalMeanSquareTransfer.lean` and `ZetaDirichletBandMeanSquare.lean` are written, verification pending. They supply the uniform-error transfer, dyadic-to-prefix passage, and finite-head subtraction needed for the actual Carlson tail mean. TH actual Xi coefficient asymptotics remains outstanding; generic Jensen receivers do not discharge it.

`IntervalMeanSquareTransfer.lean`, `ZetaDirichletBandMeanSquare.lean`, and `CarlsonZetaMeanSquare.lean` compiled, exit 0. The latter proves the actual zeta tail mean on dyadic windows and on `[0,T]`, for every fixed finite head and `1/2 < σ < 1`, with limit `Σ_{n>M} n^(-2σ)`. Dominated convergence proves this coefficient tail tends to zero and gives the iterated unconditioned L² approximation theorem. All new Carlson dependency leaves are wired into `RHTower.lean`. Final direct leaf and axiom audits remain.

## TH concentration proof plan

Deep search `theta cusp moments large exponent concentration Gaussian Hermite asymptotics` returned partial coverage, generation 1452351 pending. No actual Jensen–Hermite limit was found. Source inspection found the exact leading-channel score and its all-degree Ward identity in `PrimeArchThetaGaussianApertureScoreConcentration.lean`.

Proposed alternative to an all-order saddle expansion (paper derivation below; not yet formalized):

- Let `w(x)=exp(9x/2-π exp(2x))`, `S(x)=π x exp(2x)-9x/4`, and choose `s_n>0` with `S(s_n)=n+1/2`. Existing source proves this saddle exists uniquely. Under density proportional to `x^(2n)w(x)`, set `Δ=x²-s_n²`.
- Polynomial Ward identity: `E[(S-r)P(x²)] = E[x² P'(x²)]`, `r=n+1/2`. It follows by linearity from the existing monomial score identity. For `P(y)=(y-s²)^(2p-1)`, the right side is `(2p-1)E[x²Δ^(2p-2)]`.
- For `s≥1`, elementary exponential inequalities give global coercivity `r Δ² ≤ 2s² Δ(S-r)`. On `|x-s|≤1`, `s≥2`, the stronger coefficient is `exp(-2)r/(3s)`. The global bound follows separately from `S(x)/x` increasing for `x≤s` and `S(x)/x²` increasing for `x≥s≥1`.
- Global coercivity and `|Δ|≤s²/2+Δ²/(2s²)` give, for fixed `p` and sufficiently large `r`, `E[Δ^(2p)] ≤ C_p s^(4p)/r^p`. Constants can be defined recursively.
- A cutoff-free local inequality adds `K Δ^(2p+2)/s²` to the Ward integrand, with `K=exp(-2)r/(3s)`. Outside the local window, `|Δ|≥s`; inside it, local coercivity applies. The global bounds then give `r^p E[Δ^(2p)]/s^(4p) ≤ C'_p/s + C''_p/(rs) + C_{p+1}s²/r → 0`. Saddle escape and `s²/r→0` follow directly from the explicit score.
- Existing pointwise comparison bounds the full positive theta source above and below by fixed multiples of `w`. Thus the same normalized centered-moment limits hold for the actual Xi moment density.
- Exact coefficient identity: `γ(n+j)/γ(n) = E[x^(2j)]/[4^j (n+1/2)_j]`. Use `r_n=n+1/2`, `A_n=s_n²/(4r_n)`, `δ_n=1/sqrt(r_n)`. This gives the probabilists' Hermite normalization. The deterministic factorial-ratio Jensen polynomial is a normalized Laguerre polynomial, with recurrence `(1+dδ²)Q_(d+1)=(X+2dδ)Q_d-dQ_(d-1)`. Its limit is `He_(d+1)=X He_d-d He_(d-1)`. Centered-moment limits make integration against `x²/s_n²` preserve this Hermite limit.

Every inequality, integral interchange, finite-degree recurrence, and actual-Xi coefficient identification above still needs its Lean proof. No claim of completed TH asymptotics is warranted yet.

TH progress: `ThetaJensenPolynomialWard.lean`, `ThetaJensenSaddleCoercivity.lean`, and `ThetaJensenCenteredMomentBounds.lean` compiled, exit 0. They establish the polynomial and centered Ward identities, saddle escape, `s_n²/r_n→0`, global and local score coercivity, and the all-order global centered-moment bound. `ThetaJensenCenteredMomentLimit.lean` has been written and is in its error-fix/verification cycle. `XiThetaPolynomialExpectation.lean` and `XiThetaConcentration.lean` are written but not yet verified. No TH modules are wired yet.

Deep search `Laguerre three term Hermite limit normalized rising factorial` completed, partial after 30 seconds, coverage generation 1452644 pending. It found the reusable `ScaledHypergeometric.rising` product and its recurrences, but no directly applicable Laguerre-to-Hermite theorem. Finite interpolation helpers in `HTGeometry/FinitePolynomialInterpolationLimits.lean` can convert bounded-degree pointwise convergence to coefficient convergence.

`ThetaJensenCenteredMomentLimit.lean` compiled, exit 0: every positive normalized even centered moment tends to zero. `XiThetaPolynomialExpectation.lean` is in verification; its first compile exposed two rewrite issues and a missing direct import, now corrected. `LaguerreJensenRecurrence.lean`, `LaguerreHermiteNormalization.lean`, `XiThetaHermiteMixedLimit.lean`, and `XiJensenHermiteIdentity.lean` are written but not yet verified. These encode the exact finite Laguerre recurrence, its regular Hermite normalization, the simultaneous mixed-moment induction, and the literal existing Xi Jensen polynomial identity. Coefficientwise convergence and the final audit remain.

`XiThetaPolynomialExpectation.lean` and `XiThetaConcentration.lean` now compiled, exit 0. Every fixed positive fluctuation moment of the actual Xi source tends to zero, with no assumed analytic estimates. `XiJensenHermiteLimit.lean` is written, including the coefficientwise limit via finite interpolation, but its algebraic dependencies are still being verified. The main three-term coefficient calculation in `LaguerreJensenRecurrence.lean` passed; base-polynomial simplifications are being corrected. No completed TH asymptotics claim yet.
