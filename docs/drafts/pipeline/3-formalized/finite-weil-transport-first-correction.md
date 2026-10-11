# First correction to canonical logarithmic transport

Status: formalized and natively audited.
Research sources: local Lean corpus only. No external novelty claim.

## Target

Put n=r+1, A=k+2, U=A+n. Let K be the canonical logarithmic
transport cost, m the canonical edge probability, and E=sum_i m_i i.
Define Q=(A/n)(1-AK). For every natural-valued offset t(r), prove
Q(r,2(r+1)^2+t(r)) tends to 1/2, without analytic hypotheses.

Extend to the entire probability fiber: for arbitrary sequences a(r),b(r)
in [0,1], let delta(r)=|a(r)-b(r)| and C be the exact optimal mixture
logarithmic cost. Prove (A/n)(delta-AC)-delta/2 tends to zero.
No convergence of a, b, or t is assumed.

## Dependency-closed paper argument

Existing logarithmic gap comparison gives, for adjacent gap g_i,
(A+i)g_i <= 1 <= (A+i+1)g_i, and Ag_i <= 1 <= Ug_i.
Hence i <= U(1-Ag_i) and A(1-Ag_i) <= i+1.
Average against m, using sum m=1: E <= U(1-AK),
A(1-AK) <= E+1. Since 0<=E<=r<n, normalization gives
Q-E/n <= 1/n and Q-E/n >= -E/U >= -n/U.
When n^2<=A, n/U<=1/n, so |Q-E/n|<=1/n.
At k=2n^2+t, the existing edge-mean bound is
|E/n-1/2|<=2 sqrt((n+1)/2)/n. Since sqrt((n+1)/2)>=1/2,
|Q-1/2|<=4 sqrt((n+1)/2)/n, which tends to zero by the
existing midpoint-binomial error limit.

The exact mixture-cost identity C=delta K gives mixture correction delta Q.
Since 0<=delta<=1, the same 4 sqrt((n+1)/2)/n error bound holds uniformly
over all mixtures, even when both endpoints vary arbitrarily with r.

## Corpus audit and work plan

- Existing exact K bounds and edge-mean limit inspected in Lean sources.
- Exhaustive K references contain no first-correction theorem.
- Formalize adjacent indexed gap bounds and weighted deficit sandwich.
- Formalize correction estimate and unconditional quadratic-start limit.
- Transfer the estimate to actual optimal mixture costs and prove uniform
  vanishing error for arbitrary endpoint sequences.
- Audit all new declarations natively, standard axioms, imports, freshness,
  globally unique names, local root search, and formal lint.

## Verification log

- Recovered prior API check; no owned live Lean process remains.
- Predecessor edge-midpoint verification metadata rechecked this continuation.
- Local lexical search for transport correction has no useful hit.
- Indexed gap bounds and weighted deficit sandwich passed native Lean
  without diagnostics.
- Correction-to-mean bound passed native Lean without diagnostics.
  A cancellation-lemma name mismatch was replaced by direct positivity.
- Simplified finite-width argument: E<=r implies AD<=n. With D>=0 and
  n^2<=A, obtain nD<=1; E<=(A+n)D then gives |AD-E|<=1 directly.
  Divide by n to get |Q-E/n|<=1/n.
- The quantitative endpoint bound and unconditional Q->1/2 root passed
  native Lean without diagnostics.
- Uniform mixture correction theorem passed native Lean without diagnostics.
- Final native scratch audit passed: all 14 public declarations depend only
  on propext, Classical.choice, and Quot.sound. Seven API references also
  type-checked. No owned Lean build remains live.
- Five leaves contain 14 public declarations (2 definitions, 12 theorems),
  all globally unique. Metadata audit found no stale own/direct artifacts,
  missing imports, nonempty native logs, or whitespace issues. All nine
  incoming imports inspected; each leaf wired once in the RHTower umbrella.
- Local root lookup finds exactly the two new limit theorems, with no markers.
- Scoped diff check passed. Repository lint has 367 size warnings and eight
  unrelated errors: missing umbrella imports for CCMParityTopLayerEvenFloor,
  CCMParityTopLayerOddTest, CCMParityTopLayerProjection,
  CCMParityTopLayerTransform, CCMPolarOddPrimeJumps, ZetaRigidOrdinateWindow,
  QKrawtchoukCompanionTriangular; sorry in CCMPolarOddPrimeJumps.lean:104.
  No lint issue belongs to this closure.

## Formal roots

- `WeilLogShiftTransportCorrectionLimit.lean:38`:
  `tendsto_finiteWeilCanonicalLogTransportCorrection_half`.
- `WeilLogShiftMixtureTransportCorrection.lean:49`:
  `tendsto_finiteWeilMixtureLogTransportCorrection_error_zero`.

Both roots quantify only structural natural-valued offsets and, for the
second, arbitrary endpoint sequences in the probability interval. Neither
assumes convergence, width bounds, analytic estimates, or unproved premises.

## Audit artifacts

- `/tmp/hgt-transport-correction-metadata.py`
- `/tmp/hgt-transport-correction-declarations.json`
- `/tmp/hgt-transport-correction-incoming-imports.txt`
- `/tmp/hgt-transport-correction-final-audit.lean` and `.log`
- `/tmp/hgt-transport-correction-root-search.json`
- `/tmp/hgt-transport-correction-lint.log`
- `/tmp/hgt-WeilLogShift*.log` (five named leaf logs)
