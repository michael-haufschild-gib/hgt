# Library ticket — tate-prime-rigidity moved to 3-formalized (2026-07-16, Fable)

Informal ticket for the door-index agent; do not apply to door files from this session.

## 00-status updates requested
- Row **#101** (tate-prime-rigidity, "the secular weld is the non-split K-extension"): stage is now
  **3-formalized**. Type repaired to THEOREM-only per the Leaner return (apex delegated to
  `bigraded-corank-dss-cross` / `baker-for-stieltjes`, no conjecture co-claimed in the ticket).
- Lean surface (all unconditional, baseline axioms, lint clean):
  - `formal/GaloisForLFunctions/HTGeometry/SecularWeldRigidity.lean`:
    `equivariant_linear_kills_scaled`, `SecularWeld.dilation`,
    `SecularWeld.no_equivariant_dilation_retraction`, `SecularWeld.secularWeld_nonSplit`,
    `FormalWeightRing.equivariant_functional_kills_positive_weight`,
    `FormalWeightRing.equivariant_functional_eq_constant_coeff`.
  - `formal/GaloisForLFunctions/RHTower/StieltjesLogWeldTierOne.lean`:
    `logPrime_int_affine_relation_eq_zero`, `logPrime_rat_affine_relation_eq_zero`,
    `friableC1`, `friableBeta`, `friableC1_eq_sum_beta_log`, `friableC1_rat_iff_zero`,
    `friableC1_eq_zero_iff`, `friableC1_irrational_of_ne_zero`, `tier1_no_isolation`.
- Rows **#117** (multi-q-shafarevich-gluing-group) and **#124** (stieltjes-log-weld): their cards
  received Lean-anchor updates — #117's no-equivariant-retraction is now formalized at full ring
  strength; #124's Tier-1 (c₁ log-span, rationality dichotomy, no-isolation for `[H]_N`) is now
  formalized; both instances factor through the one shared lemma (the D2 unification in Lean).

## 00-index updates requested
- Under the seam/DSS-cross cluster, note: "rigid weld = non-split K-extension" now has an
  unconditional Lean backbone; the Tier-1 weld sits at the **Hermite floor** (in-tree
  `exp_int_irrational`), strictly below Baker — no Baker input is consumed by the banked tier.

## Addendum (same day, second pass) — third instance formalized
- New module `formal/GaloisForLFunctions/HTGeometry/DiagonalModeDivision.lean` (unconditional,
  baseline axioms): `modeFrequency_eq_zero_iff`, `modeFrequency_ne_zero`,
  `log_diagonalWeightReal`, `diagonalWeight_eq_one_iff`, `diagonal_mode_division`,
  `diagonal_equivariant_kills_mode`, `no_diagonal_equivariant_retraction`.
- 00-status: rows for #117 (arithmetic residue: qualitative floor formalized) and the Lemma-R
  bridge card (`combination-mode-reducibility-baker-bridge`: R(i) + division formalized; R(ii)
  Baker stays paper-tier). The weld now has three Lean instances of one mechanism
  (per-prime, weight-one Taylor, combination-mode).
- Housekeeping note for the maintainers: `formal_tools.py lint` currently reports several hundred
  "owned module unreachable from umbrella" errors caused by OTHER sessions' freshly created leaf
  files not yet registered in the area umbrellas (e.g. RHTower/AtomicBernsteinPacketRpowGrowth,
  created 11:51 today). The three modules of this ticket ARE registered and clean.
