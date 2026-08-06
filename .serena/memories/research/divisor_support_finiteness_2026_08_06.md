# Finiteness of divisorial support proved (2026-08-06)

Card: `docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/other/stable-coframe-log-calabi-yau-rigidity.md`
(still stage 2).

## New module

`GaloisForLFunctions/HTGeometry/DivisorSupportFinite.lean`

| statement | declaration |
|---|---|
| a height-one prime containing `a` is minimal over `(a)` | `mem_minimalPrimes_span_of_height_eq_one` |
| **nonzero element vanishes along finitely many prime divisors** | `finite_heightOneSupport` |
| **divisorial support of a rational form `a/b` is finite** | `finite_heightOneSupport_frac` |
| complement of the support | `notMem_of_notMem_heightOneSupport` |

All axiom-clean.  `lake build GaloisForLFunctions.HTGeometry` green (14913 jobs).

This is exactly the `hfin` hypothesis of `EigenvolumeRamificationSystem.lean`.  Recall
`exists_infiniteSupport_order_ne_neg_one` (same lineage) shows finiteness **cannot** be dropped,
so this was a load-bearing assumption and is now a theorem in the Noetherian model.

## mathlib pieces that made it short

- `Ideal.mem_minimalPrimes_of_height_eq (e : I ≤ J) [J.IsPrime] [J.FiniteHeight]
  (e' : J.height ≤ I.height) : J ∈ I.minimalPrimes` — the exact shape needed;
- `Ideal.one_le_height_span_singleton_of_mem_nonZeroDivisors` — Krull's height theorem side;
- `Ideal.finite_minimalPrimes_of_isNoetherianRing` — **note `R` is an explicit argument**
  (`... R (Ideal.span {a})`), which is easy to get wrong and produces a confusing
  `CommSemiring ↥(Ideal.span {a})` instance error.
- `FiniteHeight` is a one-field structure: `⟨Or.inr (by rw [hp]; exact ENat.one_ne_top)⟩`.

## Card status: every abstract hypothesis but one is now discharged

`EigenvolumeRamificationSystem` needs `hlaw`, `hone`, `hfin`, `hF` (surjective), and ramification
on cycles.  Now theorems in the local/Noetherian model:
- `hlaw` — `ramificationShiftLaw_frac` (`LocalRamificationOrderLaw.lean`), for forms with poles;
- `hone` — `one_le_ord_map_uniformizer` (`RingOrdRamification.lean`), needs **locality**, not
  injectivity;
- `hfin` — this module.
Still an assumption: `hF`, surjectivity of the divisor map (geometrically: every prime divisor
downstairs is dominated — lying-over/going-down for a finite surjective map).

Remaining beyond that: the scheme-level transport (`AlgebraicGeometry.ord` pullback law, divisor
as a cycle), and identifying a rational top form with a coframe top wedge.  See
`research/ring_ord_ramification_bridge_2026_08_06` for the interface.

## Repo hazard

Lint gate currently reports **proof debt (a `sorry`)** in another agent's untracked
`RHTower/MobiusCriticalTransportAssembly.lean:203`.  Not mine; my modules are all axiom-clean.
