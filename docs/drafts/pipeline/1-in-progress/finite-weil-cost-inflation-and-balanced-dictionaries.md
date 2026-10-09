# Cost inflation at fixed Gram form and balanced actual dictionaries

Status: DEPENDENCY-CLOSED PAPER CONSTRUCTION; Lean implementation in progress.
Reversal stability is closed. Broader search over all Weil modules found no
existing duplicate-node cost-inflation result; text search found no matching
construction. Broader lexical results concern other real/imaginary splittings.

## Implementation checkpoints

- [x] Paper construction and local novelty search.
- [x] Three leaves written: `WeilLogShiftGramCostInflation.lean`,
  `WeilLogShiftGramCoordinateReencoding.lean`, and
  `WeilLogShiftGramBalancedCostDictionary.lean`.
- [x] Twenty-one API terms verified, including explicit NNReal coercion helpers,
  `NNReal.mk`, and `Nat.cast_id` for support-cardinality transport.
- [x] Native cost-inflation leaf: exit 0, empty diagnostic log.
- [x] Native full-record reencoding leaf: exit 0, empty diagnostic log.
- [x] Native unconditional balanced-cost receiver: exit 0, empty diagnostic log.
- [ ] Complete ten-declaration public axiom audit, freshness, index, lint.

All three imports are wired. First inflation build passed form preservation
but failed on NNReal absolute-value/coercion normalization in the cost identity
and square-root parameter. Those expressions now use explicit NNReal helpers.
The second pass verified exact cost scaling; its remaining constructor mismatch
was diagnosed from the installed NNReal definition, whose documentation requires
`NNReal.mk` rather than an anonymous subtype constructor. That fix is in place.
Do not treat any pending build as passed. Logs:
`/tmp/hgt-weil-gram-cost-inflation-build.log`,
`/tmp/hgt-weil-gram-inflation-api.log`,
`/tmp/hgt-weil-gram-inflation-nnreal-api.log`.
Prepared final audit: `/tmp/hgt-weil-gram-inflation-final-audit.lean`.
All three native leaves completed successfully. Reencoding needed explicit beta
reduction before rewriting atom forms and `Nat.cast_id` after transporting support
counts. Final public axiom audit and index refresh are running; lint remains.

## Corpus evidence checked

- `WeilLogShiftFiniteGramCertificate.lean:130`: `FiniteWeilGramTest` is
  a sigma of arbitrary node and real amplitude arrays plus NNReal normalization.
  No distinct-node or amplitude-sign restriction occurs.
- `finiteWeilGramForm_apply` in the same file: the form is a signed quadratic
  sum in amplitudes, with kernel argument determined only by node differences.
- `WeilLogShiftFiniteTailCompensation.lean:168`: actual tail cost uses
  absolute amplitude products and the same node differences.
- `WeilLogShiftGramImage.lean:38`: `finiteWeilGramTestOfFinite` reindexes any
  finite node/amplitude type to an actual test. Its coefficient-vector theorem
  uses `Equiv.sum_comp` to preserve the double sum.
- Local lexical search and exhaustive text search over `WeilLogShiftGram*.lean`
  found no duplicate-node cost inflation theorem. Saved preliminary search:
  `/tmp/hgt-weil-gram-cost-inflation-frontier-search.json`. Search may need
  broadening to all Weil modules before implementation.

Only local Lean mathematical evidence; no web, papers, or numerics.

## Proposed exact construction

Given t>=1, replace each node i by two coincident copies, with amplitudes
((t+1)/2)*u_i and ((1-t)/2)*u_i; keep the outer NNReal normalization.
Their signed coefficients sum to 1. Their absolute coefficients sum to t.
Thus the Gram form should be unchanged for EVERY support and coefficient
vector, while `finiteWeilGramTailCost B` is multiplied by t^2 for EVERY B.
Use `Fin N × Fin 2` and `finiteWeilGramTestOfFinite` to obtain a native test.

Implementation parameterization: r:NNReal, with coefficients 1+r and -r.
This gives t=1+2r automatically and removes a separate scalar-range premise.
Use the equivalent finite index `Sum (Fin N) (Fin N)`; the corpus already
uses `Fintype.sum_sum_type` for the corresponding four quadratic blocks.

Consequently, for a test with positive unit tail cost k, any target C>=k
should be realized exactly without changing the form: choose
t=sqrt(C/k)>=1, so t^2*k=C. This is symbolic existence, not computation.

## Proposed balanced-dictionary discharge

Start with the existing unconditional D. Put a_w=D.balance w,
k_w=unit tail cost, p_w=a_w*k_w, and S=sum p_w. For each atom w,
choose target cost C_w=S/a_w. Positivity and the finite sum give C_w>=k_w.
Inflate each test to this exact cost while preserving its functional.
The resulting weights a_w*C_w all equal S.

The replacement map on tests is injective: equality of replaced tests
implies equality of their original forms. `D.weights_atom` distinguishes
distinct original forms, since their canonical weights are distinct unit
coordinates. Form preservation transfers the norm certificate and cardinality.
Transport balance, canonical coordinates, representation, and the feasible
ray along the induced equivalence of test subtypes, constructing a new
`FiniteWeilGramCoordinates s` directly.

For that transport, define new tests as the finite image of replacements.
The induced subtype map is bijective. Pull balance and each canonical weight
back by its inverse. `Equiv.sum_comp` transfers both representation and balance.
It also transfers the sums of nonzero-coordinate indicators, preserving the
support-cardinality bound. Pull any proposed new representation back along
the forward equivalence, apply the old feasible-ray iff, then push its pointwise
identity forward. These steps verify all fields of the coordinate record.
The empty dictionary is handled by the same finite-image construction.

The existing dimension-equality theorem should then give an actual dictionary
with optimal reversal factor exactly d for every nonempty support. Empty
support remains explicit/vacuous. This would discharge the previously open
balanced-actual-dictionary existence question, not merely assume balance.

## Required audits / limits

- Prove the double-sum signed and absolute identities on the actual objects.
- Verify all reindexing and square-root APIs against the installed toolchain.
- Check positive target costs and the atom-form injectivity argument.
- Construct all fields of the transported coordinate record; do not hide
  them behind a new model premise or an assumed balanced dictionary.
- Native leaves, complete public axiom audit, umbrella/freshness/index/lint.
- Cost inflation worsens absolute tail bounds while preserving functionals.
  It does not provide a small global cutoff-cost upper bound, nor prove
  exact single-test image surjectivity. Tail cost depends on representation,
  so attaining best reversal asymmetry is not the same as minimizing costs.
