# Translated prefix observability and maximal zero runs

- **ID:** bvi-translated-prefix-observability
- **Stage:** 0-backlog
- **Type:** CONJECTURE
- **Source:** The exact initial-prefix kernel and determinant theorem, contribution 005;
  the integral-prefix lattice package, currently undergoing its final audit.
- **Statement:** Determine the sharp observation horizon uniformly over translations
  of a consecutive block of the actual prefix discrepancy.

## Goal

Initial observations from the arithmetic origin determine the nonconstant tail in
`N-1` samples. That proof uses the ordered triangular floor matrix at the origin.
It does not establish the same horizon for an arbitrary translated window. Resolve
this distinction before treating finite observability as a translation-invariant
property of the field.

## Candidate sharp classification

For `N=n+3`, `A:ℕ`, and arbitrary real weights `c`, investigate

`(∀ M∈[A,A+2*n+2], sievePrefixDiscrepancy N M c=0) ↔ sieveVariance N c=0`.

The proposed uniform horizon is `2*N-3` samples. The upper bound is unproved;
do not regard generic periodicity, a complete-period covariance identity, or the
origin-based result as a proof. Either prove the exact claim or find the structural
obstruction and replace it with a meaningful sharp statement.

## Candidate extremal family to audit

Let `a=n+2`, `N=a+2`, and choose the three supported raw weights

`c(a)=a`, `c(a+1)=-2*(a+1)`, `c(a+2)=a+2`.

All other weights are zero. Both the harmonic tail sum and the raw coefficient
sum vanish. The normalized coefficients are the second difference `(1,-2,1)`.
For an unconditional common-period anchor take `L=(k+1)*N!`.

The symbolic floor identities suggest the exact zero block

`L-a ≤ M ≤ L+a-1`,

of length `2*a=2*N-4`, with adjacent discrepancies `-a` at `L-a-1` and `a` at
`L+a`. For positive offsets smaller than `a`, all three floors remain constant.
For negative offsets, use
`floor((L-t)/d)=L/d-floor((t-1)/d)-1` for the three divisors of `L`.
The two vanishing sums cancel the constant terms. The nonzero terminal coefficient
would give strictly positive variance by contribution 005's exact variance kernel.

This is a paper mechanism awaiting a full boundary, dependency, and novelty audit.
No Lean has been written and no contribution credit is assigned. Do not count
the candidate lower bound and a later matching classification as separate work.

## Corpus evidence and next checks

- Deep query `translated prefix observation zero run divisor window`: all 20
  candidate statements and 20 source-argument statements inspected. Partial,
  generation 1449703 pending, semantic timeout, background refresh active.
  It recovered shifted truncated-divisor increment identities and full-period
  divisor-window discrepancy vanishing, but no exact competing classification.
- Field-filtered lexical query `periodic reflection translated window` returned
  26 declarations, mostly the existing Chinese Remainder successor-period module.
  All 26 entries were inspected across two pages. They do not classify the scalar
  discrepancy's translated zero windows.
- Deep query `sievedFractSum periodic translation reflection`: all 20 candidate
  statements and the single proposed ingredient set inspected; no source arguments.
  Partial, semantic timeout, older coverage generation 1449715 versus 1449717,
  compiler/source enrichment incomplete, background indexer active. Useful existing
  bridge: `sievedFractSum_eq_residueCombination` in contribution 004. The suggested
  elliptic-gamma/periodization ingredient set does not prove the required arithmetic
  reflection identity and must not be treated as an applicable proof.
- Next: verify the actual discrepancy's translation/reflection identities in source;
  audit every boundary of the proposed family;
  then attack the uniform upper bound. No numerical experiments.

## Gates

- [ ] 0 → 1: precise statement, completed corpus audit, chosen attack.
- [ ] 1 → 2: dependency-closed paper proof and novelty audit.
- [ ] 2 → 3: exact unconditional Lean theorems, named-source and axiom checks.
- [ ] 3 → 4: standalone exposition with verified scope and citations.

## No-go closure

If the uniform upper bound fails, record the exact obstruction and extract the
strongest positive survivor: a corrected sharp horizon, phase classification,
exact window kernel, or a nontrivial rigidity law. Formalize the dependency-closed
survivor before retiring the route.
