# Route unification: which frontier-map routes are one route in different languages

- **ID:** `route-unification-dictionaries-2026-10-21`
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean) programme + report
- **Source:** `docs/reports/review-2110/walls-ledger.md` (the walls dictionary, Wall 1 = five faces of
  one number) extended from obstacles to routes of `docs/reports/rh-current-frontier-map.md`
- **Statement:** the live routes and candidates of the frontier map fall into a small number of
  clusters, each cluster being one receiver read in several languages; every identification is an
  unconditional Lean dictionary theorem (no premises, no axioms, no computation), and the report
  `docs/reports/review-2110/route-unification-ledger.md` records the clusters, the dictionaries,
  the exact differences that survive, and the open arrows.

## Goal
Stop duplicated effort: every certificate pushed on one face of a cluster is a certificate on every
other face, and counts once (the walls ledger's rule, applied to routes). Three graded units carry
the clusters: the zero width (prime side and zero side), the aperture (positivity side) and the
per-zero orientation (zero-indexed candidates). The dictionaries make the merges theorems.

## Gates
- [x] 0 → 1  in-progress: corpus survey done with the search tool (`research`) and `rg`;
  37 width-graded receivers (`xiZeroHalfPlaneBound_iff_*`), 135 per-zero indicators
  (`*_iff_re_eq_half`), the aperture ingredients (Rayleigh GLB, smoothing limit, parity split,
  odd capacity, Doob factorization, dominance chain, Rayleigh bridge) located.
- [ ] 1 → 2  fully-proven: every arrow a composition of corpus theorems plus the new aperture
  arguments (mollification into the strict interior; left-continuity of `μ`).
- [ ] 2 → 3  formalized: the three dictionary modules compiled with `lake env lean`, axioms
  standard, wired into the `SquareRootThreshold` umbrella.
- [ ] 3 → 4  not applicable (no stage 4 for non-RH items).

## Deliverables
1. `SquareRootThreshold/TheRoutesMeasureOneAperture.lean` — positivity cluster (RW, ACT, OWU,
   EWU, AIP/APT windows, SRT window and lag): at every aperture `A`, `μ(A) ≥ 0` ⟺ window
   positivity on every smaller aperture ⟺ even ∧ odd window positivity; odd window ⟺ OWU capacity
   inequality; odd window ⟹ ACT pole-free single-shift inequality; `μ(A) ≥ 0` ⟹ EWU blind minimum
   `≥ 0`, ⟹ SRT lag functional `≥ 0` at lag `2(A − w)`; endpoint RH.
2. `SquareRootThreshold/TheRoutesMeasureOneZeroWidth.lean` — width cluster beyond the walls
   dictionary: PBM regularized abscissa, TT Wold energy and directed covariance, HCF Gaussian
   Hankel tail cone, SZ shifted zero-free region, TH thermal projective moments, CCM source
   tomography (RW/HF), cosine shifts of `Ξ` in the Laguerre–Pólya class once the shift passes
   the width (LA/TT/SZ/HCF), packets and splines (WL).
3. `SquareRootThreshold/TheZeroIndexedRoutesMeasureOneSide.lean` — per-zero dictionary for the
   zero-indexed candidates (HJ residual, SEC jet boundedness, CDC confluence, …): all vanish at a
   zero iff it is on the line, and the global forms are RH.
4. `docs/reports/review-2110/route-unification-ledger.md` — the clusters, merges and open arrows.

## Approach
Glue through the corpus's three zero-set languages (`zetaZeroWidth`, `XiZeroHalfPlaneBound`,
`XiDivisorSupport`) and through the full zero form `Ẑ` on real `C²_c` tests. New mathematics in
the aperture module: window positivity at aperture `A` is the restricted Weil ground energy
`μ(A) ≥ 0` up to the closed/open-aperture distinction (mollification of a `C²` window test into the
strict interior, continuity of the complete Weil energy under mollification, Suzuki's continuity
of `μ`), and the parity split of `Ẑ` turns the all-profile window into the even and odd windows.

## Log
- 2026-10-21 — card created; survey complete; module 1 in progress.
