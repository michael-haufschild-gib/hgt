# EGC source-ray scale separation

- **ID:** EGC-RAY-20261018
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** Current frontier EGC; literal Lean source, no external novelty claims.
- **Goal:** Separate the actual Euler correction from the Gamma/pole baseline on the prescribed source ray, retaining every prime-power coefficient. Determine the exact decay obstruction before asking the ray to exclude off-line copies.

## Plan

1. Audit literal source and corpus asymptotic inputs. Completed.
2. Prove uniform logarithmic-grid tail bounds and the actual source decomposition on paper. Completed.
3. Formalize the arithmetic producer, coefficient recovery and full Gamma baseline. Completed.
4. Audit individual leaves, axioms, umbrella wiring and lint. Completed with the unrelated global lint limitation below. RH remains open.

## Corpus evidence

`PaperEGCSourceLanding` identifies the complete correction with the source-only centered trace difference. Existing convergence gives no rate. `PaperEGCEnclosedPoleCancellation` already closes the inner contour; repeating it cannot orient zeros. `XiShiftPrimeExposure.logDeriv_archFactor_closed` gives the literal pole/Gamma split. `GammaDigammaStirlingBound.norm_digammaStirlingDefect_le` gives the right-half-plane Stirling remainder. Mathlib `LSeries.tendsto_cpow_mul_atTop` recovers the first surviving coefficient of an absolutely convergent Dirichlet series.

Searches: `/tmp/hgt-egc-outer-search.json`, `/tmp/hgt-ewj-admission-search.json`, `/tmp/hgt-egc-ray-input-search.json`. Deep-search source inventory complete but compiler coverage mostly source-only; semantic coverage not measured and background refresh incomplete. Generated transfer proposals do not solve the target. Every used declaration will be checked in Lean.

## Paper theorem: arithmetic ray producer [PROVED HERE]

Write F(s)=Σ(n≥2) Λ(n)n^(−s), A(s)=(log archFactor)'(s), s=σ+ix and ε real. On σ>1 the exact source correction is

    Cε(σ,x) = iε/2 [A(s+iε)−A(s−iε)]
                − iε/2 [F(s+iε)−F(s−iε)].

Define the first bracket as Bε(σ,x). The difference R=C−B has the literal Dirichlet coefficient

    aε,x(n) = −iε/2 · Λ(n) · [n^(−i(x+ε))−n^(−i(x−ε))].

No Xi zero enters these definitions. The coefficient at n=0 is set to zero; n=1 vanishes because Λ(1)=0. Both phases have norm one for n≥1, hence |aε,x(n)|≤|ε|Λ(n). Consequently the series is absolutely convergent for σ>1 and agrees with the source by termwise subtraction, with all prime powers retained.

At any base σ₀>1 let M=Σ Λ(n)n^(−σ₀). For σ≥σ₀ and every real x,

    |R| ≤ |ε|·2^(σ₀−σ) M.

After deleting the literal n=2 coefficient, the same proof gives

    |R−aε,x(2)2^(−σ)| ≤ |ε|·3^(σ₀−σ) M.

Indeed for n≥b, n^(−σ)=n^(−σ₀)n^(−(σ−σ₀))≤n^(−σ₀)b^(−(σ−σ₀)); sum the nonnegative majorant. This is uniform in the complete frequency line x, not merely compact x. Multiplying the second estimate by 2^σ yields convergence to aε,x(2), because (2/3)^σ→0. More generally deletion of every coefficient below b gives exactly the same b-dependent bound. This is the framework contribution: a uniform tail theorem for families on the logarithmic integer grid, with the original signed coefficients preserved.

At x=0, aε,0(2)=−ε log(2) sin(ε log(2)); for 0<ε≤1 this is strictly negative. Thus the renormalized source has an eventual strict arithmetic sign and an exact nonzero leading prime coefficient. Absolute values occur only in the tail bound, not in the source definition.

## Gamma baseline paper proof [PROVED HERE; Lean verified]

Use the prescribed discrete ray σ=m+3/2 and write t=m+1. For any fixed complex a with Re a>0, z=t/2+a lies in the right half-plane and |z|≥t/2. At t≥4 the corpus Stirling bound gives |t(ψ(z)−log z+1/(2z))|≤24/t→0. Since t/2 is positive real,

    log(t/2+a)=log(t/2)+log(1+2a/t).

The branch identity is exact: the positive real factor has argument zero, and 1+2a/t has positive real part. Differentiability of log at 1 gives t log(1+2a/t)→2a. Also t/(2z)=1/(1+2a/t)→1. Subtracting the formulas for a and b cancels both the common logarithm and the reciprocal limit, proving

    t[ψ(t/2+a)−ψ(t/2+b)]→2(a−b).

For a=1/4+i(x+ε)/2 and b=1/4+i(x−ε)/2 the limit is 2iε. The Gamma logarithmic connection contributes half this, hence iε. Both rational pole differences vanish after multiplication by t: each individual t/(t+c) tends to 1, so the paired difference tends to zero. Multiplication by iε/2 gives the exact archimedean limit −ε²/2. The arithmetic bound with σ₀=2 makes tR→0, because a polynomial times 2^(−t) tends to zero. Therefore

    (m+1) Cε(m+3/2,x) → −ε²/2.

For ε≠0 this excludes o(1/(m+1)) decay of the unrenormalized correction. It supplies no zero-location sign: the baseline is source-independent Gamma geometry, while the remaining arithmetic term has the separate exact first-prime limit above.

## Boundary and no-go closure

Neither Euler-safe ray decay nor its eventual sign excludes off-line zeros. The verified full-source baseline rules out demanding o(1/σ) of the unrenormalized correction. The positive survivor is the coefficient-faithful, exponentially decaying arithmetic remainder with an explicit uniform tail budget. EGC remains live: expanding-real-coordinate outer covariance/sign is still unpaid. No route retirement or RH proof is claimed.

- **Exact obstruction:** `not_tendsto_paperEGCSourceExtractor_scaled_zero`; the scaled limit is −ε²/2, not zero, for every prescribed positive shift.
- **Strongest positive survivor:** exact archimedean subtraction, uniform base-2/base-3 budgets over the full frequency line, exact first-prime coefficient recovery, and eventual strict sign on the centered arithmetic ray.
- **New insight:** algebraic Gamma decay and exponential arithmetic decay are distinct source scales. A faster-decay premise on the full ray is false; replacing it with arithmetic renormalization preserves literal prime coefficients but still supplies no outer-contour orientation.
- **Status:** dependency-closed paper proof and all exact survivor statements verified in Lean. Fixed-shift results; no uniform shrinking-shift asymptotic is asserted.

## Verification

- `LogGridUniformDirichletTail.lean`: canonical leaf check passed, no warnings.
- `PaperEGCArithmeticRay.lean`: final canonical leaf check passed without warnings, including source split, uniform rates, exact first-prime coefficient and eventual sign.
- `HorizontalGammaDifference.lean`: canonical leaf check passed. Log contains a tactic suggestion, no errors or warnings.
- `PaperEGCSourceRayBaseline.lean`: final canonical leaf check passed without warnings.
- All 23 public theorem axiom reports passed with only `propext`, `Classical.choice`, `Quot.sound`; all 57 mathlib API probes passed in `/tmp/hgt-egc-ray-axioms.lean`.
- All four new leaves are imported by their theorem-area umbrellas. `git diff --check` passed; source hashes revalidated.
- `scripts/formal_tools.py lint` exited 1 on seven unrelated concurrent umbrella-coverage errors: BSU `OddPrimeSieveFamilies`, `SieveMomentFourier`, `SixthValuationPhaseRecovery`, `ValuationTripleResonance`; BVI `JordanUpperBoundAndGcdOrbitPrimitiveEnergy`, `PowerDampedRenormalizedDefectAndPronicCeiling`, `RenormalizedMobiusDefectAndFirstOctaveCancellation`. No new EGC leaf is flagged. Existing large-file warnings remain. Do not report a global lint pass.
- Audit evidence: `/tmp/hgt-egc-grid.log`, `/tmp/hgt-egc-gamma.log`, `/tmp/hgt-egc-arithmetic.log`, `/tmp/hgt-egc-baseline.log`, `/tmp/hgt-egc-ray-axioms.log`, `/tmp/hgt-egc-lint.log`, `/tmp/hgt-egc-ray-source-sha256.txt`, `/tmp/hgt-egc-ray-audit-manifest.json`.
- No full or umbrella build. Final checks use `lake --old env lean` for each leaf and `/tmp` axiom probes. Read-only frontier and framework READMEs remain untouched.

## Exact formal endpoints

- Framework: `lSeries_geometric_bound_of_support`, `lSeries_logGridTail_bound`, `tendsto_natScale_digamma_pair`.
- Arithmetic producer: `paperEGCCompleteCorrection_source_ray_split`, `norm_paperEGCRayArithmetic_sub_first_prime_le`, `tendsto_paperEGCRayArithmetic_first_prime`, `paperEGCRayCoeff_centered_two`, `eventually_paperEGCRayArithmetic_centered_re_neg`.
- Final source assembly: `tendsto_paperEGCSourceExtractor_scaled`, `not_tendsto_paperEGCSourceExtractor_scaled_zero`.

## Rotation checkpoint

Prior verified cycle RFHM; this cycle EGC, a different contour/source-asymptotic family. EWJ received reconnaissance only. After this bounded cycle, reassess the 27 live routes and 18 candidates; do not extend EGC by inertia. No conditional receiver or local sign is credited as an unconditional RH proof.
