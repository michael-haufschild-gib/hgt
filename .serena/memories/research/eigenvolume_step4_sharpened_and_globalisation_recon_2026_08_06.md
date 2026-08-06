# Step 4 sharpened + globalisation reconnaissance (2026-08-06)

Card: `docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/other/stable-coframe-log-calabi-yau-rigidity.md`
(still stage 2).

## Sharpened Step 4

Added to `GaloisForLFunctions/HTGeometry/EigenvolumeRamificationSystem.lean`:

- `one_lt_prod_iterate_of_exists_ramified` — one index above one on the cycle makes the product
  exceed one (all indices `≥ 1`);
- **`eigenvolumeOrder_eq_neg_one_of_ramifiedCycle`** — a periodic prime whose cycle carries
  ramification at even *one* place has order exactly `-1`.  **No** expansion at every component,
  **no** finiteness of the support, **no** surjectivity;
- `eigenvolumeOrder_eq_neg_one_of_someRamified` — the horizon theorem under that weakened
  hypothesis.

Why it is sharper than the card: only the *product* of the indices along the cycle enters the
fixed-point equation `c + 1 = (∏ e)(c + 1)`, so the card's appeal to int-amplification for
`e_E > 1` at *every* component is much more than is needed.  Axiom-clean.

## Globalisation reconnaissance — the important finding

mathlib **already has** the order of a rational function along a codimension-one point of a
scheme:

- `AlgebraicGeometry.ord (f : X.functionField) (z : X) : ℤ`, with `ordHom`,
  `ord_eq_ordHom_of_coheight_eq_one`, `ord_eq_zero_of_coheight_neq_one`, `ord_mul`, `ord_add`,
  `ord_of_isUnit`, `ord_eq_iff`, `ord_le_ord_iff`
  (`Mathlib/AlgebraicGeometry/OrderOfVanishing.lean`);
- `Ring.ord`, `Ring.ordFrac`, `ord_mul`, `ord_pow`, `ord_of_isUnit`, and crucially
  **`ord_eq_addVal : Ring.ord R x = IsDiscreteValuationRing.addVal R x`**
  (`Mathlib/RingTheory/OrderOfVanishing/{Basic,Noetherian}.lean`) — this is the bridge from my
  DVR-level results to the scheme-level `ord`.

mathlib **does not** have:
1. the divisor of a rational function as a cycle with **finite support**
   (`Mathlib/AlgebraicGeometry/AlgebraicCycle/Basic.lean` is a stub: only `mapCoeff`, `map`,
   `map_id`);
2. any **pullback law** for `ord` along a morphism of schemes — i.e. no ramification index at a
   scheme point and no `ord (φ^* g) z = e · ord g (φ z)`.

Those two are the concrete next targets.  (2) is the scheme-level form of
`addVal_map_eq_mul_ramification` (already proved for DVRs in `LocalRamificationOrderLaw.lean`),
and `ord_eq_addVal` is the intended glue.  (1) supplies the `hfin` hypothesis of
`EigenvolumeRamificationSystem`.

Still out of reach after those: `N^1(X)`, ampleness, int-amplified endomorphisms (needed only for
the *unsharpened* Step 4, which the new `..._of_ramifiedCycle` largely bypasses), and Corollary B
(MMP).

## Repo hazard (recurring, worse today)

The `HTGeometry` umbrella build currently **fails**, on two *other* agents' untracked modules that
they wired in while still broken: `SquarefreeClockLaw.lean` (cast mismatch `↑0 ^ (-σ)` at
lines 209-211) and `SubsystemComponentDecomposition.lean` (`rewrite` motive not type correct at
line 199).  All five modules of this card's lineage build green on their own
(`lake build` of them: 3034 jobs, success) and the lint gate is clean.  Check `git status` before
attributing an umbrella failure.
