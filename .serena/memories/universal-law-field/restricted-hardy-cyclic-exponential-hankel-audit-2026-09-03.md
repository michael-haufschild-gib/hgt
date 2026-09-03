# Restricted-Hardy cyclic exponential-Hankel audit (2026-09-03)

## Outcome

Original Step 1–6 relative-projection route remains retired. A distinct positive exponential-Hankel surrogate has ample cubic numerical margin, but its direct bounded landing is also retired. Surviving open class is only a singular non-Hankel mapping-cone/determinant-line transgression formed before norms and before Xi specialization.

## Runpod

Replacement host was `root@213.173.111.70:31066`. All calculations ran foreground, one process. Uploaded scripts/results were removed after download and hash verification. Only host Jupyter service remained.

New script:
`scripts/numerics/restricted_hardy_cubic_exponential_hankel_audit.py`

Downloaded results:
`docs/drafts/pipeline/2-fully-proven/computations/predivisor-relative-operator-route-audit/restricted-hardy-cubic-exponential-hankel-results.json`
SHA-256: `2543cfa5e4bfcd1e1390130a4bf27cad5f5fb77f51a6eb5b8a916553009d1ff4`

Replacement-host reproducibility rerun:
`integral-nuclear-homotopy-defect-results.json`
SHA-256: `764b752bc2265127d0bff7ab09242456878b1d9ee40ebfddd81a9f9e57fd63a0`
This 5M/depth20 rerun is weaker than the existing 50M/depth30 sibling audit and changes no verdict.

## Candidate and exact finite identities

For `n=p^k`:
`a_(p,k)=k log p`,
`c_(p,k)=1/(2 p^k k^2 log p)`,
`H_X=sum c_i |e_{a_i}><e_{a_i}|`.

Finite feature Gram:
`G_ij=sqrt(c_i c_j)/(a_i+a_j)`.

Then:
`Tr H_X=sum 1/(4 p^k k^3 log(p)^2)`,
`Tr(H_X^3)=sum_ijk c_i c_j c_k/((a_i+a_j)(a_j+a_k)(a_k+a_i))`,
and positivity gives `Tr(H_X^3) <= (Tr H_X)^3`.

At `p^k<=10000` (1280 events):
- `Tr H_X=0.40215445468965655`
- `||H_X||=0.3855625981008574`
- `Tr(H_X^3)=0.057320757311682395`
- `2Tr(H_X^3)=0.11464151462336479`
- mixed cyclic share = `0.686809074484133`.

Thus diagonal-only mass misses 68.68% of cubic trace. Numerical size is not current obstruction.

## Exact locks

Corpus was checked first with `scripts/formal_tools.py research`.

1. `not_summable_norm_routeKPhysicalEndpointBoundaryRankOne`: literal ordinary-prime endpoint atoms are not absolutely nuclear.
2. `vonMangoldtAdditivePositiveLogJetGram_add_pointedBianchiBoundary_ne_momentHankel`: successor carrier plus actual additive pointed Bianchi boundary cannot be moment-Hankel because strict anti-Hankel curvature remains.
3. One-prime Connes–Consani source defect has no compactness/Schatten theorem in corpus.
4. Any bounded coefficientwise factorization giving `S_3` convergence from finite zero-winding stages gives `S_1` convergence of cubic defects; trace continuity preserves trace zero, so it cannot create completed trace one.

Therefore positive exponential Hankel is a budget surrogate, not producer.

## Surviving conjecture

`RPGT-C3`: literal Euler–Gamma–theta current must admit a degree-three mapping-cone or determinant-line transgression whose completed cubic trace is not the `S_1` limit of finite zero-index traces, while chiral moduli are controlled by full cyclic source kernel after a non-Hankel cross term is formed. Direct bounded one-particle landing, direct sum of positive legs, and post-completion zero Gram are closed.

Updated:
- active card `restricted-prime-gamma-toeplitz-polar-defect.md` §6.10
- computation `REPORT.md` §§6–7

No Lean module was created or changed; no Lean/build/axiom audit was needed.