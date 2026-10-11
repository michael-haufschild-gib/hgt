# Critical-density law for lossless ports of Ξ

- **ID:** PTR-CRIT-DENS
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Source:** ptr-goal-loop-2026-10-09.md row 68; 3-formalized/ptr-critical-scale-anti-crystal.md
- **Statement:**
  - (i) Assume RH. For large T, the heights t ∈ [3T^{1/2} + ½, T − ½] at which the ordered ordinates are
    (C/log T)-rigid on |γ_k − t| ≤ 8τ₂ form a set whose complement in that interval has measure > 10⁻¹⁷ T.
  - (ii) Every strict lower-Pólya E with Re E = Ξ, E ≠ 0 on ℝ, has for large T at least c·T log T zeros z with
    Im z ≥ −C'/log T and Re z ∈ [3T^{1/2}, T].
    A positive proportion of its resonances are critical.

## Gates
- [x] 0 → 1  in-progress
- [x] 1 → 2  fully-proven
- [x] 2 → 3  formalized:
  - (i) `eventually_volume_nonRigidHeights_gt` (ZetaCriticalNonRigidDensity);
  - (ii) `eventually_card_critical_resonances_ge` (XiCriticalityResonanceDensity): c = 10⁻⁷⁹, C' = 2·10⁶⁰,
    log T ≥ 10⁶¹;
  - core lemma `rigidAt_of_local_resonance_free` (XiCriticalityLocalRigidity);
  - refactors: `phaseSpeed_window_margin`, `sum_norm_critRow_interior_le_of_rigidOff`,
    `false_of_critical_bounds`.

  Standard axioms; all wired.

## Phase 4
BRIDGE. The non-rigidity half restates gap-distribution facts in rigidity language. The port half (ii) is a new
statement. Under RH the canonical port Ξ + icΞ' has a resonance in every gap, at depth ≍ 1/(cL²). So positive
proportion is the right order; "almost all" is out of reach of the Fejér-row method.

## Paper proof
- (i) Rerun cycle 67 with the rigidity hypothesis only on a set G of heights. Put the complement N = [A,B] \ G
  into the bad set of the box partition. The extra cost is 96·10²⁶·|N| in the bad integral, i.e.
  4.8·10¹⁴|N|·L after division by 2τ₁. The contradiction survives if |N| ≤ 10⁻²⁰T.
- (ii) Use a margin-m version of `phaseSpeed_window`. A box [t − m − 1, t + m + 1] × [−h, 0] free of zeros makes
  the phase speed log-Lipschitz with constant 2/min(h, m) on [t − 1, t + 1]. That gives (min(h, m)/2)-rigidity
  for indices with γ_k, γ_{k+2} ∈ [t − 1, t + 1]. The phase speed is positive there because the window holds a
  zero of Ξ.
  - Non-rigid heights lie within m + 1 of a critical resonance.
  - Hence |N| ≤ #critical resonances · (2m + 2), which gives a lower bound on the count.
  - Take m, h ≍ C/L. The window [t − 1, t + 1] is then too long; use [t − 9τ₂, t + 9τ₂], margin m = 8τ₂.

## Log
- 2026-10-11 — created (cycle 68).
- 2026-10-11 — formalized (cycle 68).
  - Density constant 10⁻¹⁷, because the extended-grid bad set is ~1.5·10⁻¹⁹T and must fit under it.
  - The count statement is "every finite set containing the critical resonances has ≥ T log T/10⁷⁹ elements",
    which avoids proving that the zero set is finite.
