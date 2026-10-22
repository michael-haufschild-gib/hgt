# Theta product-fibre cofinal drop repair

- **ID:** CLG-TTF-COFINAL-DROP-REPAIR
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `rh-current-frontier-map.md` routes CLG/TTF; frontier map remains read-only
- **Statement:** At a separation where first completed product fibre rises away from modular seam, cofinal higher product fibres have a strictly positive drop which exceeds first-fibre rise. Same repair persists for positive-center germ.

## Goal

Extract strongest positive survivor from first-fibre odd-Ptolemy no-go. Replace vague need for cancellation by exact infinite-shell repair inequality. This is prerequisite for any aggregate proof of global `C₅`: completed source must first restore monotone drop destroyed by first fibre.

## Gates

- [x] 0 → 1 in-progress: source-pure statement, corpus dependencies and proof architecture located
- [x] 1 → 2 fully-proven: dependency-closed paper proof, `[PROVED HERE]`
- [x] 2 → 3 formalized: Lean theorem family below; targeted build and axiom audit pass
- [ ] 3 → 4 publication-ready

## Paper proof

**C1.** Define higher cofinal tail by summing completed product fibres `k + 2`. Absolute summability and product-fibre collapse give exact decomposition

`full reflected product = first fibre + higher tail`,

because fibre zero is empty.

**C2.** First theta atom has positive seam derivative, hence first product fibre rises at some `t>0`. Full completed reflected source is strictly decreasing at every positive displacement. Subtracting two exact decompositions forces

`first-fibre rise < higher-tail drop`.

**C3.** Continuity in center preserves strict first-fibre rise on right germ. Pointwise strict decrease of completed source then gives same cofinal repair inequality throughout germ.

**[PROVED HERE]** Let `a_k(u,t)` denote completed product-fibre amplitude and put
`H(u,t) = sum_{j>=0} a_{j+2}(u,t)`. Absolute summability and cofinal product-fibre collapse give

`a_1(u,t) + H(u,t) = P(u,t)`,

where `P(u,t)` is completed reflected-source product; fibre zero is empty. Exact positive seam derivative of first theta atom supplies `t>0` with `a_1(0,t)>a_1(0,0)`. Strict decrease of completed reflected source gives `P(0,0)>P(0,t)`. Subtracting two decomposition identities yields

`a_1(0,t)-a_1(0,0) < H(0,0)-H(0,t)`.

First-fibre amplitude is continuous in center, so strict rise persists in a neighborhood of zero. Restriction to right neighborhood gives positive centers. At each such center, same strict completed-source decrease and exact decomposition give identical repair inequality.

## Lean certificate

- Module: `GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspCompletedProductFiberCofinalDropRepair`
- Exact decomposition: `thetaCuspCompletedProductFiberAmplitude_one_add_higherTail`
- Seam repair: `exists_thetaCuspCompletedProductFiberHigherTail_drop_repairs_first_rise`
- Positive-center germ: `exists_thetaCuspCompletedProductFiberHigherTail_drop_repairs_first_rise_germ`
- Positive witness: `exists_pos_thetaCuspCompletedProductFiberHigherTail_drop_repairs_first_rise`
- Audit: targeted module build PASS; axioms only `propext`, `Classical.choice`, `Quot.sound`; no project axiom or hypothesis.

## No-go survivor

- **New invariant:** cofinal higher-fibre repair margin = higher-tail drop minus first-fibre rise.
- **Expected sign:** strictly positive at one seam witness and positive-center germ.
- **RH relevance:** atomwise or fibrewise `C₅` positivity is impossible starting architecture; aggregate tail must repair monotonicity before curvature/projective antitonicity can be attacked.

## Log

- 2026-08-28 — created after formal first-fibre odd-wall no-go exposed exact seam-rise mechanism.
- 2026-08-28 — `[PROVED HERE]`; formal cofinal decomposition, seam repair, and positive-center germ built and audited.
