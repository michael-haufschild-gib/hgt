# Simultaneous positive completion of all tail log-shift panels

- **ID:** weil-tail-panel-positive-completion
- **Stage:** 3-formalized
- **Type:** INFINITE COMPLETION / exact limitation of countable observations
- **Write scope:** `formal/GaloisForLFunctions/RHTower/WeilTailPanelPositiveCompletion.lean`,
  its umbrella import, this card, generated index and memory. Prior verified modules unchanged.
- **Source policy:** Lean corpus only. No numerical experiments or heartbeat increases.

## Exact theorem

For every natural base b, coefficient sequence lam and real height function r(k),
there exists a coefficient sequence mu such that:

1. mu(n)>=lam(n) at every coordinate;
2. mu(n)=lam(n) for every n<=exp(2(b+1));
3. every finite panel at every integer window k>=b+1 has all real entries >r(k).

Thus all sufficiently large panels, even simultaneously, leave an arbitrary
finite coefficient prefix unconstrained unless additional restrictions are paid.
This is not a claim about full Weil positivity or any coefficient growth bound.

## Proof structure [CLOSED]

- Increasing coefficients only beyond exp(2k) cannot lower any window-k probe:
  the paired kernel there is `-2K_k(y+c)-2K_k(y-c)<=0`.
- Recursively apply the verified one-coordinate positive completion at windows
  b+1,b+2,... . Every later spike lies outside the earlier window's index block,
  so it preserves earlier panel lower bounds.
- Show the spike at step i has index greater than i. Each fixed coefficient is
  therefore eventually constant; define mu(n) as its value at stage n.
- Prove mu dominates every finite stage and agrees with stage i+1 on the
  window-(b+i+1) index block. Apply the outer-coefficient monotonicity law to
  transfer that stage's strict panel lower bound to mu.
- This direct finite affine comparison avoids assuming summability of the
  infinitely many positive changes or taking an unjustified functional limit.

## Work log

- [x] Re-read objective; previous increment classified as verified progress.
- [x] Revalidate predecessor declarations and run documented corpus search.
- [x] Audit nearest monotonicity/recursive completion results and close paper proof.
- [x] Verify APIs and implement with default heartbeat limits.
- [x] Leaf and axiom audits, wiring, index and authoritative lint.
- [x] Memory updated; all owned jobs terminal; all 12 owned scratch files removed
  and absence verified.

**[PAPER PROVED; LEAN VERIFIED]** Four exported theorems and their private finite-stage
construction passed the final leaf and axiom audits.

## Closed paper proof

Write v_i for the coefficient sequence before completing window b+i+1. Apply
the verified single-window completion to obtain v_(i+1). It dominates v_i and
equals v_i on indices <=exp(2(b+i+1)). Every entry of its current panel strictly
exceeds r(b+i+1).

For i<=j, induction proves v_j(n)=v_i(n) whenever n<=exp(2(b+i+1)): the preserved
block grows with the step. Also every v_i is pointwise <=v_j. The elementary
exponential lower bound gives n<=exp(2(b+n+1)); hence coordinate n is unchanged
after stage n. Define mu(n)=v_n(n).

For any stage i and coordinate n, compare i with n. If i<=n, monotonicity gives
v_i(n)<=mu(n). If n<=i, coordinate stability gives equality. The same two cases
show mu(n)=v_i(n) on the stage-i preserved block. Therefore mu preserves the
initial block and dominates every finite stage.

For a fixed window k=b+i+1, mu and v_(i+1) agree at all indices <=exp(2k), and
mu dominates v_(i+1). The finite affine difference formula has nonnegative
coefficient differences. Each remaining paired kernel is nonpositive because
its central autocorrelation vanishes beyond exp(2k). Thus the actual panel of
mu is no lower than that of v_(i+1), proving its strict target bound. This uses
only finite sums; no infinite functional limit or summability premise occurs.

At b=0, the result additionally supplies positivity on the entire existing
countable family `WeilLogShiftTestsPositive`: every positive integer window is
covered, and window 0 has no integer probe index between 2 and exp(0)=1.
It preserves arbitrary input coefficients through exp(2).

## Corpus audit

Initial logShift/completion lexical query had no hits; the broadened panel query
returned 16 declarations, all inspected. Exhaustive references to both the
finite panel and `WeilLogShiftTestsPositive` occur only in the predecessor chain.
They include rigidity under a global minorant, finite visibility, affine
differences, excess budgets and single-window completion; none provides the
simultaneous tail completion. Lexical results carry no semantic coverage claim.
Mathlib's exact real-part finite-sum and natural-order induction APIs were read
for the proposed finite-stage proof. No external novelty claim is made.

## Positive survivor and receiver boundary

The proof produces one sequence for infinitely many windows, with an arbitrary
height function. The sequence dominates the input at every coordinate and
preserves the stated initial block exactly. Taking base=0 yields
`exists_weilLogShiftTestsPositive_prescribed_head`: the complete existing countable
test predicate admits completions of arbitrary coefficients through exp(2).
Thus this predicate by itself leaves those coefficients free. Global minorant
control in the earlier rigidity receiver supplies essential additional content.

The positive survivor consists of an exact paired-kernel identity, monotonicity
under arbitrary outer coefficient increases, eventual coordinate stability, and
simultaneous positive completion. No full Weil positivity, coefficient growth,
infinite series convergence or RH assertion is made.

## Final verification

- Final direct leaf command from `formal` exited 0 with no diagnostics:
  `lake --old env lean -o .lake/build/lib/lean/GaloisForLFunctions/RHTower/WeilTailPanelPositiveCompletion.olean GaloisForLFunctions/RHTower/WeilTailPanelPositiveCompletion.lean`.
- Separate `/tmp` import/signature/axiom audit with `lake --old env lean` exited 0.
  All four exported declarations have exactly `[propext, Classical.choice, Quot.sound]`:
  `logShiftRiemannPair_eq`, `weilLogShiftWindowPanel_outer_mono`,
  `exists_weilLogShiftTail_positive_completion`, and
  `exists_weilLogShiftTestsPositive_prescribed_head`. This transitively audits
  the private construction used by the two completion theorems.
- Exported signatures were inspected: base, lam and height are arbitrary;
  one existential mu meets every later window's strict height bound. The base-zero
  corollary uses the original `WeilLogShiftTestsPositive` definition.
- `scripts/formal_tools.py index` exited 0; all four public API rows are present.
- `RHTower.lean` imports the leaf exactly once after `WeilFinitePanelPositiveCompletion`.
  No full or umbrella build was run. No heartbeat setting was added.
- Scoped umbrella `git diff --check` exited 0. The new-file whitespace check
  produced no diagnostics (`git diff --no-index --check` reports the new-file
  difference with exit 1).
- `scripts/formal_tools.py lint` exited 1 solely for ten unrelated HTGeometry
  modules unreachable from their umbrella: `ApertureConeCalculus`,
  `ApertureConeWinding`, `ApertureLogTranslation`, `ApertureOpenHistoryIdeal`,
  `BoundaryCoronaCStarAlgebra`, `LegendreHalfCoordinates`,
  `PaperFourierLLogL.Compress.Fraction`, `PaperFourierLLogL.Compress.Low`,
  `PaperFourierLLogL.Compress.Phase`, and `PaperFourierLLogL.Compress.Thinning`.
  Those files were not edited here. Repository lint is not claimed green.

## Next conjecture [UNPROVED; CORPUS AUDIT REQUIRED]

The preserved-prefix threshold may have an exact sharp form. At the first
window L=base+1, let N=ceil(2exp(2L))-1, the last integer strictly below 2exp(2L).
Then exp(2L)<N<2exp(2L), suggesting that a spike at N permits arbitrary data at
all indices below N. Conversely the m=2 probe has zero paired kernel at every
integer above N, so freezing coefficients through N should prevent arbitrary
height targets. Proposed classification: universal tail-panel completion while
preserving indices <=B holds exactly when B<N.

Potential constructive shortcut: complete the first window at N, then apply
the current tail-completion theorem starting one window later. Its preserved
block contains N and the earlier block; outer monotonicity protects the first
window's achieved bound. This avoids rebuilding the infinite recursion.
The sharp integer boundary, generic-spike gain, first-probe invariance and both
directions of the classification remain to be searched, paper-audited and proved.
