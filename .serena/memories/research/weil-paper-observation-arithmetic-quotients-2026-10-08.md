# Observation and arithmetic penalty quotients (2026-10-08)

Whole user goal ACTIVE, unbudgeted; priority docs/reports/weil-work. Previous and current goal turns PROGRESS. OpenAI/math results treated as proven. No subagents, commits/pushes, numerical experiments, new axioms, heartbeat increases, full builds or umbrella builds.

## 21 new public theorems, 2 leaves
`formal/GaloisForLFunctions/RHTower/WeilPaperObservedPenaltyQuotient.lean` (9 theorems, 2 definitions):
- `paperFiniteSpectralPenalty F s a` is real part of finite complex linear combination of bounded continuous observations. Reuses `Complex.reCLM.compLeftContinuousBounded`, no duplicate real-projection implementation.
- Exact expectation for any real probability law: Re(sum a_i * E F_i).
- `paperObservedPenaltyShift` is this known value at the supplied base native law.
- Throughout actual observed native completion every such penalty has exactly the base expectation; adding it shifts every objective and attained gamma value by the same scalar.
- All pairwise objective comparisons and all minimizers preserved. No claim that arbitrary Classical.choose selections coincide.
- Sharper bound: |V(G)-V(H)-shift(P)| <= ||G-H-P|| for every finite prescribed-observation penalty P.

`WeilPaperArithmeticPenaltyInvariance.lean` (12 theorems, 2 definitions):
- `paperOriginPhaseObservable` on existing `WeilOneSided.LogIndex = {n : Nat // 2 <= n}`. Actual compact torus arithmeticPhase pulled back via continuous primeSpectralPoint, with explicit exp(2*pi*I*xi*log n) formula.
- Integral_map proves exact equality of real spectral expectation and prime-torus moment for every probability law. Previous completed origin constraints then pay exact zero expectations.
- `paperArithmeticSpectralPenalty s a` is real part of arbitrary finite complex combination of these phases (real sine/cosine polynomial).
- Every such penalty has zero expectation on every completed observed family, without adding it to prescribed observations.
- Adding it leaves each objective, optimal value, all pairwise comparisons, and all minimizers exactly unchanged.
- Sharper value bound |V(G)-V(H)| <= ||G-H-P|| and optimizer-transfer gap 0 <= J_G(mu_H)-V(G) <= 2||G-H-P|| for every arithmetic penalty P.
These are compensated gamma-energy statements, not a minimum for full signed Weil energy. All constraints and integrability remain paid by existing completed-family construction.

## Validation
Both production finals PASS `lake --old env lean -o ... <module>`, EMPTY logs. Arithmetic draft passed first try. First draft needed only removal of already-closed-goal tactics and an explicitly typed Re-integral equality for rewrite transparency. Seven new Mathlib names verified in /tmp; CLM integral_comp_comm needed import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap in minimal probe. Correct current API integral_finsetSum; integral_finset_sum deprecated.
25 public declarations audited in /tmp/audit-weil-penalty-quotients.lean with exact set coverage against both source files: only propext, Classical.choice, Quot.sound. 84 owned modules exactly once in umbrellas, no umbrella builds. Owned cumulative661publictheorems/84modules; Weil586/71. Index53135PASS. Lint45280 has FIVE unrelated geometry unwired modules: ApertureConeCalculus, ApertureConeWinding, ApertureLogTranslation, ApertureOpenHistoryIdeal, BoundaryCoronaCStarAlgebra. Zero own errors. Scoped git diff/current two-leaf whitespace PASS. Searchback finds arithmetic value invariance line85, observation quotient bound line131; targeted exact search finds arithmetic transfer line134 (initial broad query lost it under per-module cap). Both drafts, two name probes, foundation/preparation/final runners cleaned; audit files/logs retained. All owned processes terminal.

## Source port
Bounded3leafbatch88121: QuadraticSieve.CoprimeBilinearBound, QuadraticSieve.IdealQuotients, CubicSieve.KernelEnergy PASS unchanged; fresh75 -> 78/2957. Source4declarationaudit13169 PASSstandard3: CanonicalQuadraticSieve.energy_bound, quotientMatrix_squared_norm_le; FirstPassCubeLabels.firstLogDensity_moment_integrable, actual_first_kernel_energy_envelope. All3compilerlogsempty. FinalreadonlyinventoryPASS78/2957. Canonical source untouched. Next Reciprocity.CubicJacobi, Reciprocity.RamifiedSymbol, Poisson.QuadraticProfiles, CubicSieve.FirstPassage, CubicSieve.RayCoefficients, QuadraticSieve.DivisorBlocks, CubicSieve.SecondPoisson, Eisenstein.Rows.

## Searches/next route
search-gamma-observation-quotient.json57619 and search-arithmetic-penalty-invariance.json15614 both partial, fullinventorypending0; all20candidate+20source statements each read. No duplicate application. Future search-closed-arithmetic-penalties.json53246 partial/fullinventorypending0, all20+20read; no closed arithmetic penalty quotient capstone found. NO future draft.
Next strong application: pass from finite arithmetic penalties to their closed REAL linear span in BCF(R,R), prove uniform-limit invisibility, and build actual normed quotient. Descend V to quotient as a 1-Lipschitz concave function. Possible sharp positive statement: constants have quotient norm |a|, using any supplied native complex-null probability as bounded separating expectation. Need search actual Mathlib quotient/CLM APIs and verify names; no pivot over missing infrastructure.
CRITICAL mathematical distinction: this is a real LINEAR subspace, NOT an algebra or ideal. Products of integer phases and their conjugates introduce rational-ratio phases or constants; do not assume multiplicative closure. Existing prime-torus injectivity uses rational phase moments, so invisible individual integer probes do not imply all mixed probes invisible.
Other caution: intersection of finite-constraint native closures need not equal closure of simultaneously constrained native family.

Live/tracking: tmp/hgt-openai-math/PROGRESS.md, own-files.txt. Preserve concurrent WeilWork* and geometry work. Only owned current new leaves and umbrella lines edited. No unfinished owned native draft.
