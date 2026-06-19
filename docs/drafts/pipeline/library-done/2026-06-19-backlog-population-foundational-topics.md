# Ledger update request — backlog populated with every foundational research topic (22 new cards)

**From:** orientation/backlog pass
**Date:** 2026-06-19
**Targets:** `docs/drafts/door/00-index.md` (gatekeeper + cross-cutting **Work package** columns),
`docs/drafts/door/00-status.md` (§B "Pick something to prove" links; §C per-row "now carded" annotations)

## What changed
Every foundational research topic across `00-index.md`, `00-status.md`, and the `door/` buckets that did
**not** already have a pipeline card now has one in `0-backlog` (22 new cards). **No new §C statements**
were introduced — each card tickets an **existing** §C row (or a bucket open-core/work-package). So the
ledger work is **annotation + work-package links**, not new rows. No scorecard change (C5 still the gap).

Already-carded topics were not duplicated (G1/G3 fully-proven; C5★ carriers, erosion, Ш, holonomicity in
1-in-progress; baker-for-stieltjes, carrier-herglotz-rh, c7-autonomy, cross-prime-curvature,
function-field-native-reproof, lee-yang in 0-backlog). EMBASSY/framing items (time bucket #61–67,
#94–96), IMPORTs, and FALSIFIED rows were intentionally **not** carded.

## The 22 new cards → §C row(s) / bucket

**Gatekeeper cores**
- `g2-dss-lower-bound.md` — G2 open core: lower bound = obstruction **C** (#15) + DSS-cross (#18) → rows #7/#15/#18 | [[G2-multi-q-siegel-shidlovsky]]
- `dss-reduction-formalize.md` — DSS reduction + conditional Nesterenko→DSS as Lean Props → rows #10/#11 | [[G2-multi-q-siegel-shidlovsky]]
- `compute-omega-h2-gl.md` — compute `ω ∈ H²(G_L)` (G4 open core; folds #28 Langlands identity) → rows #27/#28/#71 | [[G4-multi-q-picard-vessiot-and-langlands-group]]
- `weil-positivity-operator.md` — G5: `RH ⟺ H_W = −Δ_prime + V_arch ≥ 0` (#38) + HP `[D,P]=0` (#39) → rows #38/#39 | [[G5-unitarity-gatekeeper]]
- `zero-estimate-uniformity.md` — obstruction B uniformity-in-S (Conj 5′) → rows #13/#14 | [[G2-multi-q-siegel-shidlovsky]]

**A1/A2 unification**
- `a1-a2-unification-brick.md` — one object, two readings + the single rigidity → rows #51/#52/#53/#55/#56/#57 | [[bucket-A1-A2-unification-the-carrier]]
- `faces-orthogonality.md` — Face A ⊥ Face B (G14) → row #54 | [[bucket-A1-A2-unification-the-carrier]]

**Realization & no-margin**
- `realization-problem.md` — Euler ⟺ two-faces IFF (#86) + G17 overdetermination (#84) → rows #84/#86 | [[bucket-realization-and-fake-family]]
- `no-margin-uniform-bound.md` — the one missing uniform bound (#89) → rows #89/#90 | [[bucket-the-no-margin]]
- `is-lambda-a-period.md` — is `Λ` a period (#95) → row #95 | [[bucket-the-no-margin]]

**Sibling conjectures**
- `family-dss-gsh.md` — family-DSS = GSH (G13) → row #100 | [[bucket-new-sibling-conjectures]]
- `koszul-acyclicity.md` — Koszul-acyclicity (G15) → row #99 | [[bucket-new-sibling-conjectures]] / [[G4-multi-q-picard-vessiot-and-langlands-group]]
- `seam-firewall.md` — finite-place ⊥ archimedean (G6) → row #106 | [[bucket-new-sibling-conjectures]] / [[bucket-the-seam-archimedean-obstruction]]
- `fe-fourier-quasicrystal.md` — FE = Fourier quasicrystal (G8) → row #97 | [[bucket-new-sibling-conjectures]]
- `intrinsic-rh-locus-pure-polarized.md` — RH locus = pure+polarized (G9) → row #98 | [[bucket-new-sibling-conjectures]]
- `tate-prime-rigidity.md` — secular weld motivic⊕non-period (G12) → row #101 | [[bucket-new-sibling-conjectures]] / [[bucket-the-seam-archimedean-obstruction]]
- `regularization-freshness.md` — regularization creates transcendence (G16) → row #75 | [[bucket-the-seam-archimedean-obstruction]] / [[bucket-new-sibling-conjectures]]
- `motivic-period-tower.md` — two non-interacting Galois towers (SEED-U) → row #102 | [[bucket-new-sibling-conjectures]] / [[bucket-the-seam-archimedean-obstruction]]
- `friable-dirichlet-auxiliary.md` — native auxiliary space (N5) → row #103 | [[bucket-new-sibling-conjectures]] / [[G2-multi-q-siegel-shidlovsky]]
- `tamagawa-strength-one.md` — positive-direction strength = 1 (SEED-B) → row #105 | [[bucket-new-sibling-conjectures]] / [[bucket-the-no-margin]]
- `transcendence-implies-gue.md` — transcendence ⟹ GUE (B11) → row #107 | [[bucket-new-sibling-conjectures]]
- `hp-not-too-algebraic.md` — HP can't be too algebraic (B18) → row #108 | [[bucket-new-sibling-conjectures]] / [[G5-unitarity-gatekeeper]]

## Suggested §C annotations (append "— carded: `<file>`" to each row's cell; no row count change)
#7/#15/#18 → g2-dss-lower-bound · #10/#11 → dss-reduction-formalize · #13/#14 → zero-estimate-uniformity ·
#27/#28/#71 → compute-omega-h2-gl · #38/#39 → weil-positivity-operator · #51–#53/#55–#57 →
a1-a2-unification-brick · #54 → faces-orthogonality · #75 → regularization-freshness · #84/#86 →
realization-problem · #89/#90 → no-margin-uniform-bound · #95 → is-lambda-a-period · #97 →
fe-fourier-quasicrystal · #98 → intrinsic-rh-locus-pure-polarized · #99 → koszul-acyclicity · #100 →
family-dss-gsh · #101 → tate-prime-rigidity · #102 → motivic-period-tower · #103 →
friable-dirichlet-auxiliary · #105 → tamagawa-strength-one · #106 → seam-firewall · #107 →
transcendence-implies-gue · #108 → hp-not-too-algebraic.

## Suggested 00-index.md "Work package" column updates
- **G2 row:** → `g2-dss-lower-bound` (+ `zero-estimate-uniformity`, `dss-reduction-formalize`, `friable-dirichlet-auxiliary`)
- **G4 row:** → `compute-omega-h2-gl` (+ `koszul-acyclicity`)
- **G5 row:** → `weil-positivity-operator` (+ existing `carrier-herglotz-rh`)
- **bucket-A1-A2:** → `a1-a2-unification-brick` (+ `faces-orthogonality`)
- **bucket-seam:** → `compute-omega-h2-gl`, `seam-firewall`, `regularization-freshness`, `tate-prime-rigidity`
- **bucket-realization:** → `realization-problem`
- **bucket-no-margin:** → `no-margin-uniform-bound` (+ `is-lambda-a-period`, `tamagawa-strength-one`)
- **bucket-new-sibling:** → the 12 sibling cards above (shortlist remainder `family-dss-gsh`, `koszul-acyclicity` now carded)

## Not final
All 22 are `0-backlog` (gate 0→1 mostly unchecked) — tickets, not results. No conjecture upgraded; the
two-channel rule holds. C5 remains the gap; scorecard unchanged.
