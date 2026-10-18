# Explicit damping radius and finite-path perturbation

- **ID:** thim-explicit-damping-radius
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** For N≥2, 0≤ε≤1/(96N(N+1)log N), and M≥1 with R_N(M+1)<6(N+1), the damped prefix defect is at most −1/2, uniformly in endpoint height and power exponent.

## Goal

Make qualitative damping stability quantitative without evaluating examples or
assuming an unproved analytic estimate. Preserve the infinite radical-fiber
scope. The separate all-ε≥0 defect conjecture remains open.

## Gates

- [x] Corpus audit and current-source inspection.
- [x] Dependency-closed paper proof.
- [x] Scratch proof, actual-source Lean compile, all-declaration axiom audit.
- [x] Umbrella wiring, index/lint audit, ledger and memory, scratch cleanup.

## Paper proof [PROVED HERE]

Write c_ε(d)=μ(d)d^(−ε) and A=Σ_{1≤d≤N}|c_ε(d)−μ(d)|.
For d≥1 and ε≥0, 0≤1−d^(−ε)≤ε log d follows from exp x≥1+x.
Thus each coefficient difference is at most ε log N and A≤ε N log N.
The divisor-sum response difference is bounded by A at every argument.

For any two real paths f,g with |f|,|g|≤B and |f−g|≤A at both
ends of each edge, expand
f_j(f_{j+1}−f_j)−g_j(g_{j+1}−g_j)
=(f_j−g_j)(f_{j+1}−f_j)+g_j((f_{j+1}−g_{j+1})−(f_j−g_j)).
The absolute value is at most 4BA. Summing M edges gives 4MBA.
On 1≤j≤M+1<6(N+1), the established damped and undamped response
bounds give B=2 (the value at j=1 is one). Therefore
|D_ε(M)−D_0(M)|≤8MεNlog N≤48(N+1)εNlog N≤1/2
when ε≤δ_N=1/(96N(N+1)log N). Since D_0(M)≤−1, D_ε(M)≤−1/2.
The denominator is positive for N≥2.

For a large endpoint with radical at least two, compare its defect to the
finite radical representative. For radical one, compare to a Bertrand prime
N<p≤2N; equal response and increasing accumulated energy give the same upper
bound. Positive powers preserve the radical, so the radius is independent of
power exponent. N≤1 and empty prefixes have zero defect.

This improves the previous proposed 1/(48N²(N+1)log N) radius by N/2.
No optimality of 96 or of the asymptotic order is asserted.

## Quantitative obstruction survivor [PROVED HERE]

The same radius gives response error at most 1/(96(N+1)) at EVERY endpoint.
For prime p>5, N=6p−1 and k=30p, the undamped response is two. Therefore
all positive powers k^m retain response at least 3/2 and defect at most −1/2
throughout 0≤ε≤δ_N. Existing unit bounds before 5(N+1)=30p show that k
remains the first unit-envelope failure. The interval is positive and explicit;
it need not be uniform in p. This strengthens the failed-envelope route's
positive survivor rather than claiming a universal positive-damping obstruction
at one fixed exponent.

## Baseline and novelty audit

Known ingredients: exp tangent bound, finite ℓ¹ perturbation estimates and
product difference algebra. New formulation: explicit damping interval on
infinite radical fibers, using the strict integer-energy margin and finite-band
envelope. Observation baseline TH10 https://arxiv.org/abs/1009.5281;
shifted-correlation baseline CMS16 https://arxiv.org/abs/1612.03136.
Identical truncated divisor sum: Helfgott–Thompson Proposition3.2,
https://doi.org/10.1007/s40993-022-00408-8. No external priority claim.

Broad corpus query `coefficient perturbation finite sieve defect Lipschitz
quantitative damping radius`: partial=false,74132 inventoried files,pending0,
generation1454812; compiler coverage mixed. All 20 candidate lemmas and 20
source arguments inspected. Existing qualitative stability and radical
transport found; no explicit radius or matching finite defect perturbation
theorem in returned results. Prior narrower search was partial; this search
broadens coverage without claiming exhaustive literature absence.

Focused path query `bounded path correlation defect coefficient perturbation
Lipschitz`: partial=false,74136 files,pending0,generation1454866. All 20
candidates and 20 source arguments inspected. Existing short-window identities,
coefficient recovery, scaling, and equal-response monotonicity support the
proof; no matching finite-defect perturbation estimate in returned hits.

## Next conjecture, not yet formalized

Retain incidence frequencies instead of a uniform response error. Pointwise
edge expansion should give 6a(j)+2a(j+1), where a(j) bounds response error.
Summing divisor incidences yields an error bound
8ε Σ_{d≤N}log(d) floor((M+1)/d), hence at most
8ε(M+1)log N(1+log N). This suggests radius
1/(96(N+1)log N(1+log N)) on the same radical fibers.
The harmonic bound and all endpoint constants still require paper and Lean
audits; this is not a verified result or an optimality claim.

Preliminary field-filtered query `sum absolute response coefficient difference
divisor floor weighted perturbation`: partial=false,74136 files,pending0,
generation1454869. All 20 candidates and 20 source arguments inspected.
Useful hits include sum_Icc_sieveSeq_eq_drift_sub_sievedFractSum and coefficient
ℓ¹ bounds; no matching incidence-weighted defect bound in returned results.
Broaden the search before implementing this next conjecture.

## Verification

- Source: `formal/GaloisForLFunctions/TransHorizonIncidenceMechanics/QuantitativeDampingRadiusAndDefectPerturbation.lean` (288 lines).
- SHA256: `26f4f099e118a6e00df88f11dca456ba51ef49e780d092fe4d9949b45b2de6d5`.
- Full scratch and actual-source `lake --old env lean` exited 0 without warnings.
  All 16 theorems and one definition axiom-audited; no private generated helpers appeared.
  Every closure uses only standard Lean axioms.
- `logs/thim-quantitative-audit.json` checks all declarations/closures, 17 API entries
  and baseline docstrings, source/dependency hashes, fresh artifacts, unique
  umbrella import, MainTheorems reachability, whitespace and prohibited declarations.
- Evidence: `logs/thim-quantitative-{lean,axioms,index,lint}.txt`.
  Index exited 0. `lint --check-generated` exited 1 with 6 external findings,
  recorded exactly in audit JSON. No new-leaf or prohibited-declaration finding.
  Shared index freshness may change under concurrent edits; no clean global gate claimed.
- All owned jobs terminal; ten owned scratch files removed and verified absent.
  README unchanged. No full/umbrella build, numerical experiment, added axiom,
  heartbeat change, commit or push. Continuing research goal remains active.
