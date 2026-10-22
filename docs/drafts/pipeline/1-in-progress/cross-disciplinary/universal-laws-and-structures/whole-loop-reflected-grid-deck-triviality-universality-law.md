# Whole-loop reflected-grid deck-triviality universality law

## Status

`[LEAN PROVED — LITERATURE AUDITED] [CANDIDATE NEW SCIENTIFIC KNOWLEDGE]`

## Theorem-generated discovery

`incidence_wholeLoop_closure_of_closed` outputs a finite band-edge event family whose unit event
ledger is `LedgerFluxPaired`, together with the exact winding/enclosed-order parity. Independently,
`reflectedGridOffgridCharge_deckRed_two_eq_one_of_paired` consumes any `LedgerFluxPaired` list and
proves that adding it to the nontrivial completed reflected-grid carrier leaves level-two deck
charge trivial. The identical ledger type is the missing connector; no corpus theorem composes it.

## Universal law

For every closed, positive-modulus, strictly monotone incidence loop satisfying the whole-loop
factorization and winding-link hypotheses, and every nontrivial completed reflected grid:

1. band-edge events exist and form an even paired unit-flux ledger;
2. loop phase advance is an integral number of turns;
3. that winding integer has the parity of total enclosed analytic order;
4. completed reflected-grid charge plus the actual whole-loop event ledger has trivial level-two
   deck class.

Thus whole-loop off-grid events cannot alter the canonical reflected-grid parity class.

## Paper proof

Apply `incidence_wholeLoop_closure_of_closed` to obtain `n`, event locations, winding integer `k`,
the event equations, evenness, `LedgerFluxPaired (List.replicate n 1)`, and winding/order parity.
Apply `reflectedGridOffgridCharge_deckRed_two_eq_one_of_paired` to that exact ledger and the
nontrivial-grid hypothesis `1 ≤ N`. Package all conclusions under the same witnesses.

## Novelty protocol

No literature search was performed before the Lean theorem exact-checked.

Post-proof searches covered argument-principle root counts, winding parity, reflection-symmetric
zero configurations, paired crossing flux, and \(\mathbb Z/2\mathbb Z\) deck invariants.

Nearest sources:

- Li--Paulson, *Evaluating Winding Numbers and Counting Complex Roots through Cauchy Indices in
  Isabelle/HOL*, arXiv:1804.03922, formally links winding numbers to root counts by the argument
  principle:
  <https://arxiv.org/abs/1804.03922>
- Aguirre--Peral, *Splitting Obstructions and \(\mathbb Z_2\) Invariants in Time-Reversal Symmetric
  Topological Insulators*, studies reflection-symmetric winding and evenness of a winding number:
  <https://link.springer.com/article/10.1007/s11785-026-01963-z>
- Borcea--Brändén et al., *Polynomials with symmetric zeros*, arXiv:1904.01940, classifies standard
  reflection symmetries of polynomial zero sets but does not connect event ledgers to a completed
  reflected-grid deck charge:
  <https://arxiv.org/abs/1904.01940>

No source found the exact law: actual events forced by a closed analytic incidence loop form a
paired unit ledger, the same loop winding has enclosed-order parity, and adding that ledger to the
canonical completed reflected grid is provably invisible under the level-two deck reduction.
Novelty claim is restricted to this formal statement.

## Lean target

`formal/GaloisForLFunctions/RHTower/WholeLoopReflectedGridDeckTrivialityUniversalityLaw.lean`

## Verification

- exact and warning-free:
  `lake env lean GaloisForLFunctions/RHTower/WholeLoopReflectedGridDeckTrivialityUniversalityLaw.lean`
- wired into `formal/GaloisForLFunctions/RHTower.lean`
- final module, axiom, and lint audits deferred to terminal pass
