# Summable-deficit rigidity cannot use only countable log-shift positivity

- **ID:** weil-logshift-summable-deficit-receiver-no-go
- **Stage:** 5-failed (premise reduction); positive survivor formalized
- **Type:** FAILED PREMISE REDUCTION / exact positive deficit realization
- **Write scope:** a new Lean leaf, its umbrella import, this card, generated
  index and memory. Existing verified sources remain unchanged.
- **Source policy:** Lean corpus only; no external papers, numerical experiments
  or heartbeat increases.

## Candidate premise reduction

Replace `WeilPositiveFull` by `WeilLogShiftTestsPositive` in the existing
summable-deficit/even-eventual-majorant rigidity theorem. The source proof uses
comb tests and then a full-cone summable-deviation theorem; it does not consume
only the countable log-shift family. The proposed replacement is false.

The separate summable-excess reduction is NOT falsified by this argument.
Its source uses modulated Fejer tests and a Fourier deviation-pairing theorem;
its status remains open in this investigation.

## Strongest positive survivor selected

Let N(base)=ceil(2exp(2(base+1)))-1 be the verified sharp first-probe boundary.
For every starting sequence and every real height function, construct one
dominating sequence mu with:

- every coefficient n<N(base) unchanged;
- mu(n)>=Lambda(n) for n>=N(base);
- normalized deficit exactly the input deficit for n<N(base), and exactly zero
  elsewhere, hence summable;
- all later finite panels strictly above their prescribed heights.

Specialize at base=0 to retain any positive normalized deficit exp(t) at n=2,
with zero deficit at every other coordinate, while satisfying the entire
original `WeilLogShiftTestsPositive` predicate. The resulting sequence is not
`WeilPositiveFull`, by the already verified full-cone summable-deficit rigidity.
This gives an exact counterfamily, not merely an abstract failed proof attempt.

## Survivor paper proof [CLOSED]

1. Before applying sharp completion, replace the input outside n<N by
   max(input(n),Lambda(n)). This only increases coefficients and removes all
   deficits in the replaceable tail.
2. Apply the sharp prefix completion theorem at B=N-1. The completed sequence
   preserves the entire earlier prefix and dominates the prepared tail.
3. The pointwise normalized deficit identity follows by the two index cases.
   Its support lies in Finset.range N, giving summability directly.
4. For the counterfamily use input Lambda(n) minus exp(t)*sqrt(2) only at n=2.
   Since 2<N(0), that coordinate remains fixed. Every other coordinate is at
   least Lambda. Its exact normalized deficit is the single atom exp(t) at 2.
5. Base=0 covers every positive integer window; window zero has no valid probe.
   Full positivity would force equality at 2 by summable-deficit rigidity,
   contradicting the strictly positive prescribed deficit.

## Work log

- [x] Read active objective; previous turn classified as verified progress.
- [x] Inspect actual full-cone summable-deficit and summable-excess proof uses.
- [x] Complete corpus/novelty and dependency audit; close survivor paper proof.
- [x] Formalize exact survivor and strict separation; run leaf/axiom audits.
- [x] Wire, index, authoritative lint and failed-card closure.
- [x] All owned jobs terminal; removed all 10 inventoried scratch files and
  verified absence. Recorded `research/weil-logshift-finite-deficit-separation-2026-10-09`.

**[PREMISE REDUCTION REFUTED; POSITIVE SURVIVOR PAPER PROVED; LEAN VERIFIED]**

## Exact survivor and verification

Source: `formal/GaloisForLFunctions/RHTower/WeilLogShiftFiniteDeficitSeparation.lean`.

- `RHTower.exists_weilLogShift_exact_deficit_prefix`: for arbitrary base, input
  coefficients and panel-height function, preserve every coefficient below the
  sharp boundary, remove every later deficit, realize the exact truncated
  normalized deficit profile, and exceed all later prescribed panel heights.
- `RHTower.exists_weilLogShift_single_deficit_separation`: for every real t,
  construct coefficients satisfying the original countable log-shift predicate,
  with normalized deficit exactly exp(t) at 2 and zero elsewhere, summable
  deficit, and failure of full Weil positivity. Every coefficient other than 2
  is at least von Mangoldt, so even an eventual-majorant premise cannot repair
  this replacement.

Both results have dependency-closed paper proofs above and kernel-checked Lean
proofs. Neither assumes full positivity, RH, numerical evidence or a new
analytic premise. The summable-excess question remains unresolved here.

Verification on 2026-10-09:

- Leaf check with `lake --old env lean -o ...` exited 0 without diagnostics;
  no heartbeat override, full build or umbrella build.
- Separate scratch import checked both public signatures and `#print axioms`:
  exactly `[propext, Classical.choice, Quot.sound]` for each.
- Exactly one theorem-area umbrella import; index command exited 0 and both
  public declarations appear in `formal/LEAN_API.md`.
- Scoped whitespace checks produced no diagnostics.
- Authoritative `scripts/formal_tools.py lint` exited 1 on 13 unrelated
  unreachable modules, with no error for this leaf. In `RHTower`:
  `CCMEvenFullGroundSecondMomentRH`, `CanonicalProductE1SecondDerivative`,
  `PaperCircleEnergyLocalization`, `StretchedBoseDefect`. In `HTGeometry`:
  `ApertureConeCalculus`, `ApertureConeWinding`, `ApertureLogTranslation`,
  `ApertureOpenHistoryIdeal`, `BoundaryCoronaCStarAlgebra`,
  `PaperFourierLLogL.Compress.Params`, `PaperFourierLLogL.Compress.Theorem`,
  `PaperFourierLLogL.Thermal.Piece`, `PaperFourierLawMeasure`.

## Corpus audit and scope of the failure

The documented summable/excess query returned 34 declarations; both pages were
inspected. Exhaustive references to `WeilLogShiftTestsPositive` contain only the
verified predecessor chain, with no finite-deficit counterfamily. The actual
summable-deficit proof calls full positivity on `combRiemannKernel L M` and later
uses full-cone summable-deviation rigidity. The summable-excess proof separately
uses modulated Fejer functions and vanishing Fourier deviation pairings.

The current counterexample refutes only the summable-deficit/eventual-majorant
replacement. It proves that some log-shift-positive systems with a single
nonzero deficit are outside the full Weil cone. It says nothing yet about
summability of their excess or weakening the summable-excess receiver.
Lexical search gives no semantic coverage certification or external novelty claim.
