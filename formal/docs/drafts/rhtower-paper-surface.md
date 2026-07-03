# P2 — Publication surface: the RHTower formalization

**Status: surface document** (task #103). Register: LEDGER for the Lean claims (all
banked, axiom-clean `[propext, Classical.choice, Quot.sound]`, target
`GaloisForLFunctions.RHTower` green at 8576 jobs); SEARCH for framing decisions.

## Title candidates

1. *Zero counting without the argument principle: a machine-checked deck-class
   calculus and the multiplicity ladder for the Riemann Hypothesis*
2. *The RH_{2^k} ladder: a formalized monodromy reformulation of RH*
3. *A contour-free obstruction calculus for zeros of analytic functions, formalized*

Candidate 1 leads with the methodological contribution — recommended: the honest core
novelty is the METHOD (a complete zero-counting and deformation theory in Lean with no
argument principle, which mathlib lacks), certified by a nontrivial application (the
ladder equivalence against mathlib's `RiemannHypothesis`).

## The result surface (16 modules, dependency order)

**Arc A — the ladder (RiemannTower.lean + KummerObstruction/Peeling/RootExistence/
CoherentTower):**
- `rh_iff_forall_ladder` : RiemannHypothesis ↔ ∀ k, RHLadder k, where RHLadder k is
  the divisibility 2^k ∣ ord_ρ(ξ) at every zero right of the line. Also
  `rh_iff_tower` (ℤ₂-Kummer tower form) and `rhLadder_iff_root` (analytic 2^k-th root
  on the half-plane). Engine: root ⟺ order-divisibility on convex domains via
  exhaustion (`exists_root_iff_orders_dvd`), derivative-free root rigidity
  (`pow_root_unique`), global peeling.

**Arc B — the deck calculus (DeckCocycle/DeckMonomial/DeckAssembly/DeckMultiZero/
XiDeck):**
- `deckClass`: the μ_n-valued two-chart gluing invariant; choice- and basepoint-
  independent (`deckClass_root_indep`, `deckClass_basepoint_indep`), coherent in the
  dyadic tower (`deckClass_sq`), trivial iff roots glue
  (`deckClass_eq_one_iff_exists_root`).
- The counting dictionary with NO contour integral: `deckClass_single_zero`,
  `deckClass_multi_zero` (class = exp(2πi·Σm/n)), `xi_deckClass_eq_one_iff_ladder_dvd`
  — the ladder's clause IS deck-class triviality, end to end on the actual ξ.

**Arc C — the ledger (DeckHomotopy/LedgerJump/SeamCocycle/FarFieldAnchor/
ReflectionParity):**
- Conservation: `deckClass_deformation_invariant` (dominated perturbation cannot move
  the charge); jump: `deckClass_jump` (one crossing multiplies by exp(2πi·m/n)); seam:
  `seam_jump` (crossing an on-seam zero multiplies the bank-gluing constant by the
  same factor); anchor: `xi_deckClass_far_field`; parity at the fixed locus:
  `analyticOrderAt_even_of_reflection`, `xi_central_order_even`.

**Arc D — potential theory and counting (ModulusHolography/CountingSubstitute):**
- `deckClass_eq_exp_circleAverage_slope`: the class equals the exponential of the
  two-circle slope of the circle average of log‖f‖ — boundary modulus determines the
  charge (consumes mathlib's new Jensen formula).
- `enclosed_count_eq_of_close`: Hurwitz-type EXACT count stability under dominated
  perturbation (the large-n residue trick — no a priori bound); `pinned_zero_on_line`:
  the FE ∧ reality pinning lemma.

**Arc E — analytic continuation and families (UPlaneDescent/MirrorPencil +
Reflection/LogIndependence/PerturbationZero/DirichletRigidity):**
- `xiDescent` entire via a Painlevé/Morera reflection engine (cross-lane import),
  branch-free global descent identity `xi_eq_xiDescent`, and
  `rh_iff_xiDescent_ne_zero_slitPlane` (the Pólya–Jensen guise, machine-checked).
- `pencil_mirror` / `incidence` / `dirichletXi_one_sub` / `dirichlet_pencil_mirror`:
  FE-pair pencils, the incidence map, and the constant-root-number renormalization of
  mathlib's completed Dirichlet L.

## Novelty positioning (gate-checked)

- **Method (primary claim):** mathlib has no argument principle, no Rouché, no
  Hurwitz. This development delivers counting, deformation invariance, jump formulas,
  and local uniqueness WITHOUT them — monodromy constants + the large-n residue trick
  + (for the potential-theoretic face) Jensen. As far as we know this is the first
  complete contour-free zero-counting theory in a proof assistant. [Verify at
  submission: sweep Isabelle/Coq/mathlib4 for argument-principle formalizations —
  Isabelle HAS Rouché (Li–Paulson school); the claim must be scoped to "contour-free
  route" and to Lean/mathlib.]
- **Statement-level:** the multiplicity-grading RH_{2^k} of RH and its coarse-cocycle
  reading are literature-absent (delegated checks C2 — Bagchi's mechanism has no
  coarsening — and C0 #5 — nothing on off-line multiplicity; notes in the lane's
  checks/ directory; spot-check before submission).
- **Honesty clauses (must appear in the paper):** (a) RH ⟺ ∀k RH_{2^k} is classically
  trivial as a statement — the content is the obstruction language and the
  machine-checking; (b) xiDescent is the classical Ξ₁ (Pólya–Jensen) — the route
  (Painlevé, branch-free) and formalization are new, the statement is not; (c) the
  ladder adds no strength at any finite k unless a rung mechanism is found — the
  paper claims a LANGUAGE and a toolkit, not progress on RH itself.

## Venue and shape

Primary: ITP/CPP (formalization venue) — method-led, with the ladder as showcase.
Secondary surface: a short expository note on the ladder + deck cocycle for a general
audience (Experimental Mathematics / expository journal), citing the formalization.
The (RittΞ) material (doc 17) and pseudo-primeness free ground are a SEPARATE paper
candidate (classical function theory), pending C12.

## Pre-submission gate (blocking items)

1. Full-tree `formal_tools.py lint --check-generated --build` — currently blocked by
   the parallel q62 agent's in-flight Bottcher files; re-run when their session lands.
2. Spot-check the delegated notes consumed as novelty evidence (C2, C0, C11) against
   sources; the Isabelle/Rouché scoping check above.
3. Decide: single method paper vs method + companion note.
4. Blueprint/naming pass over the 16 modules (docstrings are publication-grade
   already; align terminology: "deck class" vs "coarse cocycle" — pick one).
5. The measured-campaign material (R-series) stays OUT of this paper (belongs to the
   lane's research narrative, not the formalization paper).
