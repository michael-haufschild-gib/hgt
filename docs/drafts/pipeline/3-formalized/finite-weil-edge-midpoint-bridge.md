# Finite Weil edge-to-midpoint probability bridge

Status: formalized in Lean 4. Sources restricted to the local Lean corpus and installed Lean dependencies.

## Target

For every canonical grid, prove that its midpoint probability profile is obtained by choosing an edge with probability equal to its canonical transport mass, then choosing either endpoint with probability one half. Extract exact moment identities and a stable comparison for test functions. Connect this bridge to the already formalized midpoint binomial law without inverting the averaging operator in l1.

## Local proof route

Add the existing canonical coupling's row and column marginal identities. Contract the resulting finite double sum onto oriented edges using the existing arbitrary-cost edge formula. The sum of a test function at source and target is independent of edge orientation. This gives the exact midpoint expectation as half the edge expectation of the two endpoint readings.

For the index reading, averaging the two endpoints adds one half. For a quadratic reading, averaging adds the corresponding centered square plus one quarter. For a general test, the difference from its left-endpoint edge reading is half the weighted adjacent increment; positivity and total edge mass one yield a stable bound.

Write n=r+1, e=sqrt((n+1)/2)/n, E=sum m_i i, and H=sum m_i(i-r/2)^2. The existing midpoint binomial l1 bound is 2e when k+2>=2n^2. Testing the centered linear function, bounded by n/2, gives |E-r/2|<=sqrt((n+1)/2). Testing its square, bounded by n^2/4, and using the exact binomial centered second moment n/4 gives H<=r/4+(n^2/2)e. Since n>=1 and sqrt((n+1)/2)>=1/2, H/n^2<=e. These bounds and the existing error limit give E/n->1/2 and H/n^2->0 along k=2n^2+t(r), for every nonnegative offset sequence t.

## Verification

Seven native leaf builds pass with empty logs. All 26 public declarations pass the axiom audit with only `propext`, `Classical.choice`, and `Quot.sound`. Eighteen actual-toolchain API probes pass. Own/direct dependency freshness, all 26 declaration names, all 14 incoming imports, and single umbrella imports pass the metadata audit. Both limit roots appear in the local index. No full umbrella build, numerical experiment, external paper, or web search was used.

Repository lint remains nonzero on foreign work: missing imports for `JointAncestryHalfPlaneExistence`, `ZetaOffLineMomentMontgomeryTaylor`, `ZetaOffLineMomentProportionTransfer`, and `QKrawtchoukCompanionTriangular`; a `sorry` in `ZetaOffLineMomentMontgomeryTaylor.lean:55` (`HD_one_ge`). None occurs in this dependency closure.

## Progress

- Predecessor full-mixture transport modules revalidated: metadata reports no issues.
- Exact coupling and edge probability ingredients already exist in Lean.
- `WeilLogShiftEdgeMidpoint`: exact endpoint pushforward and test pairing.
- `WeilLogShiftEdgeMoments`: exact mean shift and one-quarter variance increment.
- `WeilLogShiftEdgeTestTransfer`: stable adjacent-test and l1-test bounds.
- `WeilLogShiftBinomialProbabilityMoments`: exact binomial mass, mean and centered second moment.
- `WeilLogShiftEdgeMeanBinomialBound`: quantitative edge mean bounds.
- `WeilLogShiftEdgeConcentration`: quantitative normalized centered second-moment bound.
- `WeilLogShiftEdgeBinomialLimit`: `tendsto_finiteWeilCanonicalEdgeIndexMean_half` and `tendsto_finiteWeilCanonicalEdgeCenteredSecondMoment_zero`, for every offset sequence `t : ℕ → ℕ`.

All modules live under `formal/GaloisForLFunctions/RHTower/` and are wired into its umbrella. Audit artifacts are `/tmp/hgt-edge-midpoint-final-audit.lean`, `/tmp/hgt-edge-midpoint-final-audit.log`, and `/tmp/hgt-edge-midpoint-metadata.py`. This proves moment transfer and normalized concentration; it makes no claim of stable l1 inversion from midpoint to edge probabilities.
