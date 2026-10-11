# Finite Weil edge-to-midpoint probability bridge

Status: in progress. Sources restricted to the local Lean corpus and installed Lean dependencies.

## Target

For every canonical grid, prove that its midpoint probability profile is obtained by choosing an edge with probability equal to its canonical transport mass, then choosing either endpoint with probability one half. Extract exact moment identities and a stable comparison for test functions. Connect this bridge to the already formalized midpoint binomial law without inverting the averaging operator in l1.

## Local proof route

Add the existing canonical coupling's row and column marginal identities. Contract the resulting finite double sum onto oriented edges using the existing arbitrary-cost edge formula. The sum of a test function at source and target is independent of edge orientation. This gives the exact midpoint expectation as half the edge expectation of the two endpoint readings.

For the index reading, averaging the two endpoints adds one half. For a quadratic reading, averaging adds the corresponding centered square plus one quarter. For a general test, the difference from its left-endpoint edge reading is half the weighted adjacent increment; positivity and total edge mass one yield a stable bound.

Write n=r+1, e=sqrt((n+1)/2)/n, E=sum m_i i, and H=sum m_i(i-r/2)^2. The existing midpoint binomial l1 bound is 2e when k+2>=2n^2. Testing the centered linear function, bounded by n/2, gives |E-r/2|<=sqrt((n+1)/2). Testing its square, bounded by n^2/4, and using the exact binomial centered second moment n/4 gives H<=r/4+(n^2/2)e. Since n>=1 and sqrt((n+1)/2)>=1/2, H/n^2<=e. These bounds and the existing error limit give E/n->1/2 and H/n^2->0 along k=2n^2+t(r), for every nonnegative offset sequence t.

## Verification plan

Native leaf builds, actual-toolchain API probes, all-public-declaration axiom audit, own/direct dependency freshness, exhaustive incoming imports, local root lookup, and formal lint. No full umbrella build, numerical experiment, external paper, or web search.

## Progress

- Predecessor full-mixture transport modules revalidated: metadata reports no issues.
- Exact coupling and edge probability ingredients already exist in Lean.
- Exact midpoint bridge, moment and variance identities, stable test transfer, and normalized binomial moments compile with clean logs.
- Edge mean bounds compile; two redundant tactic warnings await cleanup.
- Edge concentration bound and both arbitrary-offset limit roots are undergoing native verification.
