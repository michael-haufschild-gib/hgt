# MC: structural obstruction removal

Status: IN PROGRESS. No contribution established yet.

## Objective

Find and prove one unconditional structural theorem that removes a hard obstacle
in the actual signed Möbius cancellation route. Improved bounds, RH equivalences,
conditional receivers, computational evidence, and generic rearrangements do not
meet the task. Use the Lean corpus as the research source; no web or external
novelty audit. Preserve unrelated existing edits.

## Plan

1. Recover the current frontier and obstruction from indexed Lean declarations
   and their full statements/proofs.
2. Iterate exact conjecture, attempted refutation, and learned replacement.
3. Complete a dependency-closed paper proof before formalization.
4. Formalize without unproved inputs; directly audit each new module using
   `lake --old env lean`, audit axioms, wire imports, run formal lint, clean scratch.

## Corpus findings

- `MobiusSquareResidueShortBilinear`: exact short reconstruction retains all
  product cutoffs; its kernel has a cubic positive diagonal and negative terminal
  principal minor. Sign-blind positivity is unavailable.
- Route MC's current entry identifies joint principal-counterterm/high-product
  cancellation as open. Small-modulus, low-product and terminal estimates do not
  control the whole source.
- Existing prime-insertion, physical-wavelet and growing-smoothing results must
  be inspected before proposing another local cancellation or smoothing scheme.

## Conjecture ledger

1. **Repair the square kernel using the source counterterms. Rejected: FALSE.**
   `MobiusSquareRenormalizedKernel.squareKernel_firstRowCorrection_minor_neg`
   leaves a negative principal minor at indices `2,N` for every `N >= 4`,
   for every correction supported in the first row or column. Its explicit
   negative direction and cubic positive diagonal exclude the proposed
   coefficient-independent sign mechanism. No new no-go is claimed.

2. **Obtain a positive source kernel by increasing prime-packet smoothing.
   Rejected in the fixed physical window.** The existing normalized packet
   escape theorem prevents a unit-mass pointwise limit in that window.
   Recentering would change the physical observation; it is not a proof of
   cancellation of the original source.

3. **Cancel opposite signs within complete product fibres. Rejected: FALSE.**
   `MobiusProductFibreVariation.pair_sign` proves
   `mu(m) mu(n) = lambda(m*n) mu(m)^2 mu(n)^2`.
   `abs_signedFibre_eq_unsigned` proves that product grouping loses no
   unsigned variation. Cancellation must cross products, even when factors
   share primes. `MobiusProductFibrePrimeBalance` already supplies the exact
   local two-placement law; its diagonal cancellation at prime three leaves
   child diagonals and other pair channels.

4. **Use complete LCM-fibre cancellation at the physical cutoff. Rejected:
   FALSE.** `EulerDeletionAllShiftLcmPolarity` already gives the full divisor
   incidence identity. `EulerDeletionCenteredLcmInitialCutoffSign` proves
   that the literal physical window `(t,H)=(0,15)` has complete-grade prefix
   through `10` equal to `-45/196`. Divisor-closed positive conservation
   therefore cannot be transferred to the physical initial segment.

5. **Upgrade finite-dimensional prime steering into exhaustive cancellation.
   Rejected as a completed argument: MISSING STEP.**
   `MobiusDivisorFiniteDepthPrimeCancellation` already produces an inward
   actual-prime collar for every nonzero coefficient vector in any fixed
   finite child field, uniformly on its coefficient sphere. A positive-span
   corollary would not advance this frontier. `MobiusDivisorUniformReserveHistory`
   controls sparse histories at all cutoffs, whereas
   `MobiusDivisorExhaustiveClockCheckpoints` exhausts primes only with budgets
   at moving checkpoints and short collars. Neither result pays the old
   cutoff after its remaining primes are processed. These different
   quantifiers cannot be interchanged.

## Current unresolved point

No unconditional construction has been found that retains the actual full
signed source and removes the changing-cutoff obstruction. For the square
bilinear formulation, principal counterterms and high-product remainder
remain jointly uncontrolled. A theorem merely restating their required
control, a finite-rank steering corollary, or another local cancellation
identity would not meet the requested contribution.

No route is newly retired. All negative results above were already proved
in the corpus. No new positive survivor or paper proof is claimed.

## Search and source audit

Used the documented `scripts/formal_tools.py research` command in lexical,
hybrid, and deep modes, including searches across all indexed Lean areas and
dependencies. Inspected candidate lemmas and source arguments, then read
relevant Lean statements/proofs. Search reported no unfinished stages in
the completed semantic requests, but warned of older coverage snapshots and
unmeasured semantic coverage; search results are leads, not a completeness
certificate. No web search, external novelty audit, or numerical experiment
was performed. Only the explicitly requested MC frontier entry and operational
instructions were read as repository Markdown; historical research cards
were not used.

## Self-audit

- No new mathematical knowledge established; requested frontier advance not achieved.
- Existing corpus results killed the proposed mechanisms before code was added.
- Formalizing their immediate consequences would be theorem packaging, not
  the requested structural breakthrough.
- Paper-proof and Lean phases remain uncompleted because no qualifying exact
  theorem has survived the mathematical audit.

## Verification

No Lean source changed, so no build or new axiom audit was run. Existing user
edits were preserved. This card records incomplete research, not completion.
