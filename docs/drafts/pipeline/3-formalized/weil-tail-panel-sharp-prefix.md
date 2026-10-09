# Exact prefix capacity of simultaneous tail-panel completion

- **ID:** weil-tail-panel-sharp-prefix
- **Stage:** 3-formalized
- **Type:** SHARP CLASSIFICATION / positive completion and exact obstruction
- **Write scope:** `formal/GaloisForLFunctions/RHTower/WeilTailPanelSharpPrefix.lean`,
  its umbrella import, this card, generated index and memory. Previous verified sources unchanged.
- **Source policy:** Lean corpus only; no numerical experiments, external papers
  or heartbeat increases.

## Verified exact boundary

For base b and first window L=b+1, put

`N(b)=ceil(2 exp(2L))-1`.

Consider the property that every starting sequence lam and every height
function r(k) admit mu>=lam, with mu(n)=lam(n) for all n<=B, whose finite panels
are strictly above r(k) at every k>=L. This property holds exactly
when `B<N(b)`.

The positive survivor is a sharp capacity classification, including both
an explicit completion below the boundary and an exact invariant at the boundary.

## Proof obligations [CLOSED]

1. Prove N is the last integer strictly below 2exp(2L), lies strictly above
   exp(2L), and lies inside the coefficient block visible at the first window.
   Avoid assuming irrationality or transcendence of the exponential.
2. Extend the actual one-coordinate gain formula to any integer between
   exp(2L) and 2exp(2L); in particular use N.
3. Complete the first window with a positive spike at N. Then apply the existing
   simultaneous tail completion starting one window later. Its preserved block
   contains N, and outer monotonicity protects the first window's achieved bound.
4. Prove the m=2 probe is exactly invariant under all changes at indices >N:
   at those indices log(n)-log(2)>=2L, so all paired autocorrelation terms vanish.
5. If B>=N, freezing that prefix fixes the m=2 value; request a strict height
   equal to that original value to contradict universal completion.

## Work log

- [x] Read objective; classify previous turn as verified progress.
- [x] Revalidate predecessor declarations; run documented corpus search and
  focused exhaustive source search.
- [x] Audit nearest results and close paper proof.
- [x] Verify APIs, implement, run leaf/axiom audits, wire and index.
- [x] Authoritative lint and final status.
- [x] Memory updated; all owned jobs terminal; all 10 owned scratch files removed
  and absence verified.

**[PAPER PROVED; LEAN VERIFIED]** Five exported theorems and two definitions
passed the final leaf and axiom audits.

## Closed paper proof

Let E=exp(2L)>2 and C=ceil(2E). Since C>=1, N=C-1 satisfies C=N+1.
The ceiling laws give N<2E<=N+1, hence E<N<2E. For every natural n,
`N<n iff 2E<=n`. These statements require no arithmetic fact about exp(2L).

For any integer n with E<n<2E, every probe m has
`0<log(n)-log(m)<2L`, while its other two kernel arguments exceed 2L.
Exact strict support and the paired-kernel identity therefore give a positive
gain `2a*K_L(log(n)-log(m))/sqrt(n)` under a positive coefficient increase a at n.
The finite sum of positive parts of the required gain ratios supplies one
amplitude raising every first-window entry above its target.

If B<N, use n=N for that first completion v. Apply the already verified
tail-completion theorem to v with base b+1. The new preserved block reaches
exp(2(L+1))>2E>N, so the entire frozen prefix remains unchanged. Pointwise
dominance and outer monotonicity preserve the first-window lower bound; the
existing theorem supplies every later window's target.

For the converse, whenever n>N, the ceiling law gives n>=2E. At m=2,
`log(n)-log(2)>=2L`, and the central and positive-shift arguments also exceed
the support boundary. All three autocorrelations vanish, including at equality.
The finite affine difference formula proves exact complex invariance of this
probe when coefficients through N agree. If B>=N, any permissible completion
therefore leaves this probe unchanged. Choosing its strict target height equal
to the original value contradicts universal completion.

## Corpus comparison

The documented panel/completion query has 22 declarations in the predecessor
chain; both pages were inspected. The focused exhaustive text search found
no sharp log-shift prefix capacity statement. Existing finite-window and
simultaneous tail completions preserve a sufficient block; neither supplies the
last active integer nor the converse obstruction. Lexical search carries no
semantic coverage or external novelty claim.

## Implementation checkpoint

The API probe passed. The new source is
`formal/GaloisForLFunctions/RHTower/WeilTailPanelSharpPrefix.lean` and contains
the ceiling boundary, arbitrary common-coordinate gain and finite completion,
exact first-probe tail invariance, the universal completion predicate, and both
directions of its sharp classification. The first partial check found one
natural-to-real coercion mismatch in the ceiling lower bound; that was corrected.
The full leaf and axiom audits passed. No heartbeat setting was added. Owned
scratch files use `/tmp/hgt-weil-sharp*`.

## Positive survivor and exact obstruction

`weilTailPanelHeadCompletable_iff` proves the unconditional equivalence for every
natural base and prefix length. The left side quantifies over every starting
coefficient sequence and every real height function, and asks for one dominating
sequence meeting every later window's strict bound while preserving the prefix.
The right side is exactly `B < ceil(2exp(2(base+1)))-1`.

The positive construction and the negative obstruction are both formalized.
The obstruction is exact equality of the full complex m=2 functional under
arbitrary changes past the boundary. The survivor includes generic outer-spike
gain and completion at any integer in the common interval, not merely at one
chosen index. No endpoint irrationality premise was used.

## Final verification

- Final direct leaf command from `formal` exited 0 with no diagnostics:
  `lake --old env lean -o .lake/build/lib/lean/GaloisForLFunctions/RHTower/WeilTailPanelSharpPrefix.olean GaloisForLFunctions/RHTower/WeilTailPanelSharpPrefix.lean`.
- A separate `/tmp` import/signature/axiom audit with `lake --old env lean` exited 0.
  All seven exported declarations have exactly `[propext, Classical.choice, Quot.sound]`:
  `weilLogShiftSharpLiftIndex`, `weilLogShiftSharpLiftIndex_bounds`,
  `weilLogShiftWindowPanel_outerSpike`, `exists_weilLogShiftWindowPanel_outerSpike`,
  `weilLogShift_firstProbe_tail_invariant`, `WeilTailPanelHeadCompletable`, and
  `weilTailPanelHeadCompletable_iff`. This covers all private proof dependencies.
- Exported signatures and the universal completion predicate were inspected.
  The classification has no RH, full Weil positivity, growth, summability or
  arithmetic endpoint premise.
- `scripts/formal_tools.py index` exited 0; all seven API rows are present.
- The RHTower umbrella imports the leaf exactly once after
  `WeilTailPanelPositiveCompletion`. No full or umbrella build was run.
- Scoped umbrella `git diff --check` exited 0. New-file whitespace checking
  produced no diagnostics; its no-index exit 1 records the added-file difference.
- `scripts/formal_tools.py lint` exited 1 solely for seven unrelated unreachable
  modules: RHTower's `PaperCircleHeatInformation`, `PaperHeatSelectionInformation`;
  HTGeometry's `ApertureConeCalculus`, `ApertureConeWinding`,
  `ApertureLogTranslation`, `ApertureOpenHistoryIdeal`, and `BoundaryCoronaCStarAlgebra`.
  Those modules were not edited here. Repository lint is not claimed green.

## Research status and next question

This exact boundary is paper-proved and formalized. The broader corpus goal
remains active. The construction currently imposes no arithmetic support or
prime-power coherence restriction on coefficients. A substantive next question
is whether corresponding restricted profiles still admit positive completions.
Before forming an exact conjecture, search the corpus for actual profile
definitions and producers of admissible positive changes in the common interval.
The verified outer-monotonicity law permits additional nonnegative changes
beyond exp(2L), so a coherent positive change need not be a single spike.
No existence claim for such restricted completions is made here.
