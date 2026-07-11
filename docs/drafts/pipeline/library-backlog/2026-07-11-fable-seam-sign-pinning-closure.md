# Ticket: door index — seam-sign pinning closed (obstruction map complete)

Requested updates to `docs/drafts/door/00-index.md` / `00-status.md` (apply-agent to place):

1. **Card closed:** `seam-sign-pinning` moved `1-in-progress` →
   `3-formalized/not_new_scientific_knowledge/`. All claims [PROVED HERE, Lean, axiom-clean].
   Headline: complete obstruction map of the Real (σ-equivariant) root tower — off-line regions
   free (mirror gluing), symmetric regions = plain ladder + unconditional line ledger, symmetric
   boundaries = one sign bit = crease-ledger parity, pro-level off-line = RH verbatim
   (`rh_iff_xi_equivariant_coherentTower_offline`). Verdict: machine-checked no-go — regionally
   the equivariant theory adds nothing; "RH ⟺ Real tower extends across the strip" retired in
   region form.

2. **New Lean module:** `formal/GaloisForLFunctions/RHTower/EquivariantOfflineRegion.lean` —
   the region-level echo: `offline_symm_left_eq_mirror_image` (symmetric off-line region = mirror
   pair), `exists_equivariant_root_iff_offline`, `equivariant_coherentTower_offline_iff`,
   `xi_equivariant_root_iff_offline` (generic carrier; any `n`; no sign/parity clause). Wired
   into the `RHTower` umbrella. Axiom-clean.

3. **New backlog card:** `pipeline/0-backlog/chowla-anchor-dirichlet-real-tower.md` — the
   dissolution machinery pointed at Λ(s,χ), real primitive χ: the anchor bit = sign L(½,χ) =
   Siegel parity in (½,1); dissolution law = central nonnegativity. The seam-sign theory's first
   carrier where the bit is an open arithmetic quantity.

Note for the formal maintainer: `GaloisForLFunctions.RHTower` umbrella currently fails to build
on the pre-existing committed module `SummableEulerCalkinInjectivity.lean` (rewrite failure at
line 106, unrelated to this work; `EquivariantOfflineRegion` builds green and lint passes).
