# Quantitative excess mass forced by finite log-shift observations

- **ID:** weil-finite-block-excess-mass
- **Stage:** 3-formalized
- **Type:** QUANTITATIVE STRENGTHENING / finite observation stability
- **Write scope:** new `formal/GaloisForLFunctions/RHTower/WeilFiniteBlockExcessMass.lean`,
  its RHTower umbrella import, this card, generated index and session memory.
- **Source policy:** Lean corpus only. No external papers or numerical experiments.

## Exact targets

Let C=riemannAutocorr(0)>0, S_k=Icc(2,floor(exp(4k))), and P_k be the existing
finite complex log-shift probe panel. Reuse the corpus's normalized positive
part `WeilExcess.deviationExcess`. Define

`M_k(lam) = sum_{n in S_k} max((lam(n)-Lambda(n))/sqrt(n),0)`.

Prove the exact finite affine difference formula for P_k and the uniform bound

`norm(P_k(lam)(m)-P_k(mu)(m)) <= 4 C sum_{n in S_k}|(lam(n)-mu(n))/sqrt(n)|`.

Main target: for every q:N and t:R, there is a cutoff K independent of lam and
the panel lower-bound parameter eta:R. For every integer k>=K, the class of lam
with every finite probe real part >=-eta and
`exp(t)<=(Lambda(q+2)-lam(q+2))/sqrt(q+2)` lies in the class satisfying

`max(exp(t)/100 - eta/(4C),0) <= M_k(lam)`.

In particular, a nonnegative finite panel forces `exp(t)/100 <= M_k(lam)`.
There is no restriction on the tail and no summability, growth, full-cone
positivity or RH premise. Constants are sufficient bounds, not claimed sharp.

## Paper proof [CLOSED BY SOURCE AUDIT]

1. `WeilExcess.riemannAutocorr_le_zero`, together with
   `truncatedRiemannAutocorr_le_riemannAutocorr` and nonnegativity, gives
   `0<=K_L(y)<=C` for every real L,y.
2. The existing log-shift kernel formula and evenness show that its two signed
   samples have sum `4K_L(y)-2K_L(y+c)-2K_L(y-c)`, lying in [-4C,4C].
3. Replace both coefficient sequences by their finite-block completions using
   `weilLogShiftWindowPanel_completion`. In the difference of full functionals,
   the pole and archimedean terms cancel. Compact support gives summability of
   the coefficient series (`summable_primeAtoms`); their difference is supported
   on S_k because both completed tails equal Lambda. This yields the exact
   finite affine difference formula. The triangle inequality and step 2 give
   the uniform weighted l1 bound.
4. Cap lam pointwise at Lambda: b(n)=min(lam(n),Lambda(n)). This is a minorant and
   its prescribed deficit is at least the original deficit. The verified
   finite-block separator supplies one probe with real part <=-exp(t)C/25.
5. The weighted l1 difference between lam and b on S_k is exactly M_k(lam),
   by the definition of the normalized positive part. Therefore that probe's
   actual real part is at most `-exp(t)C/25 + 4 C M_k(lam)`.
6. Combine its observed lower bound -eta with this upper bound and divide by
   4C>0. Nonnegativity of M supplies the maximum with zero. Setting eta=0 gives
   the noiseless lower bound.

## Corpus audit

- Documented lexical search `"riemannAutocorr" "zero"` found the exact maximum
  theorem in `WeilDeviationTranslationBound.lean`; its proof was inspected.
- An exhaustive RHTower text search located 92 relevant autocorrelation-bound
  or functional-decomposition hits. Inspected the actual compact-support
  summability and `weilFullFunctional_eq_sub` source proofs.
- Documented lexical search `"excess" "deficit"` returned 23 declarations; both
  result pages were inspected. Candidate-lemma/source-argument sections were
  empty. These lexical searches provide no semantic-coverage certification.
- Nearest mean-balance and excess/deficit mean-comparison statements require
  full Weil positivity and Cauchy/translation bounds. The summable sign-part
  rigidity statements are global. They do not give this finite-panel estimate
  with a sequence-independent cutoff and an arbitrary observation lower bound.
- `WeilWorkDeficitRadicalBudget.lean` bounds short coherent-packet repair costs;
  its data and conclusions differ from this coefficient-excess lower bound.
- The predecessor `exists_uniform_finiteBlock_excess_of_deficit` gives an excess
  witness; this target bounds the amount of normalized excess, including an
  explicit correction for a lower bound -eta on the observed panel.
- No external novelty claim. Existing excess definitions and proved kernel
  bounds will be reused rather than duplicated.

## Work log

- [x] Re-read the active objective and revalidate the predecessor source.
- [x] Corpus search, nearest-result comparison and paper dependency audit.
- [x] Verify APIs in a /tmp toolchain probe.
- [x] Write finite affine differences, the uniform norm bound and both mass-bound proofs.
- [x] Direct leaf/axiom audits, umbrella import, index and authoritative lint.
- [x] All owned jobs terminal; removed all 15 owned scratch files and verified absence.

**[PAPER PROVED; LEAN VERIFIED]** The new source contains the excess-mass definition,
uniform paired-kernel bound, exact finite panel difference, weighted l1 bound,
arbitrary-lower-bound mass estimate and nonnegative-panel corollary. This
strengthens the predecessor's existence of an excess coefficient to a lower
bound on total normalized excess visible in the same finite coefficient block.

## Verification checkpoint

The API probe passed, including the imported autocorrelation maximum theorem's
standard axiom list. Initial leaf invocations stopped during import resolution,
before checking the new proofs: prerequisite objects were being rebuilt by
other sessions. Each missing object was matched to an existing compiler; no
duplicate build was launched. A source-import audit covers 4476 project imports
and checks all missing objects together before another leaf invocation. The
source has no heartbeat override. Owned scratch files use `/tmp/hgt-weil-mass*`.

## Final verification

- Direct final leaf command, run from `formal`, exited 0 with no diagnostics:
  `lake --old env lean -o .lake/build/lib/lean/GaloisForLFunctions/RHTower/WeilFiniteBlockExcessMass.olean GaloisForLFunctions/RHTower/WeilFiniteBlockExcessMass.lean`.
- A separate `/tmp` import/signature/axiom audit, run with `lake --old env lean`,
  exited 0. All six declarations have exactly
  `[propext, Classical.choice, Quot.sound]`:
  `weilFiniteBlockExcessMass`, `norm_logShiftRiemannPair_le`,
  `weilLogShiftWindowPanel_sub`, `weilLogShiftWindowPanel_lipschitz`,
  `exists_uniform_finiteBlock_excessMass_budget`, and
  `exists_uniform_finiteBlock_excessMass_of_deficit`.
- Inspected both exported mass-bound signatures: q,t are arbitrary; the cutoff
  precedes both the sequence and eta. Eta is any real number. No RH, full-cone
  positivity, growth or summability premise was introduced. The observations
  and deficit specify the source set of an unconditional set inclusion.
- `scripts/formal_tools.py index` exited 0; all six declarations have API rows.
- `RHTower.lean` imports the new module exactly once, immediately after
  `WeilFiniteBlockMinorantSeparation`. No umbrella or full build was run.
- Scoped `git diff --check` passed. No heartbeat setting was added.
- `scripts/formal_tools.py lint` exited 1. Its only errors were unrelated
  HTGeometry modules unreachable from their umbrella:
  `ApertureConeCalculus`, `ApertureConeWinding`, `ApertureLogTranslation`,
  `ApertureOpenHistoryIdeal`, `BoundaryCoronaCStarAlgebra`, and
  `CosineAlgebraicComponents`. These modules were not edited here. Repository
  lint is not claimed green.

## Research status

The quantitative survivor and its paper proof are formalized. Constants are
not claimed optimal. No external novelty claim or RH proof is asserted.
The broader corpus research goal remains active.
