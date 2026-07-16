# Lee–Yang marginal forcing structure — threshold trichotomy, marginal degeneracy, carrier marginality

- **ID:** lee-yang-marginal-forcing-structure
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean 4, unconditional) — the fully proven structural half of
  `lee-yang-localization` (G7), split out per the Lean formalizer's return note on the parent.
- **Grade:** BRIDGE (substrate) — inherited from the parent; elementary parts individually
  [SEARCH]-grade, the value is the formal skeleton that pins G7's §1–§4 and its ζ-side anchor.
- **Source:** split from `../../0-backlog/lee-yang-localization.md` (G7, SEED-E §81–82/§81.3).
  Reuses in-tree anchors `CarrierHerglotz` / `carrierHerglotz_iff_onLine`
  (`RHTower/FieldConjectures.lean`), `xi` / `rightHalf` / `rh_iff_xi_ne_zero_right`
  (`RHTower/RiemannTower.lean`); companion to `finite-congruence-pencil-factorization.md`
  (`HTGeometry/CongruencePencil.lean`).

## Statement (four Lean modules, all unconditional)

**(1) Threshold trichotomy and marginal degeneracy** — `formal/GaloisForLFunctions/HTGeometry/LeeYangForcingThreshold.lean`
A forcing family is an up-set `L ⊆ ℝ` (localization persists under stronger interaction;
`IsForcingFamily`). Then:
- forced stratum: `sInf L < t → t ∈ L` (`IsForcingFamily.mem_of_threshold_lt`);
- rejected stratum: `t < sInf L → t ∉ L` (`notMem_of_lt_threshold`) — the wrong-sign rejection;
- off the margin the mechanism decides: `t ≠ sInf L → (t ∈ L ↔ sInf L < t)`
  (`IsForcingFamily.mem_iff_threshold_lt`);
- closed loci attain the threshold (`csInf_mem_of_isClosed`) — **the boundary bit is free**;
- **no-margin equivalence**: closed `L`, free half `t₀ ≤ sInf L` ⟹ `t₀ ∈ L ↔ t₀ = sInf L`
  (`mem_iff_eq_csInf_of_le`) — localization at the physical point IS the threshold-pinning equality;
- **degeneracy at the margin**: same-threshold families disagreeing at it
  (`threshold_membership_undetermined`); no rule reading the threshold decides the marginal bit
  (`no_threshold_decision_rule`); the full closed+free-half data-type still does not decide the
  physical point (`closed_forcing_data_not_decide_marginal`);
- affine transport of family/threshold/marginality (`isForcingFamily_image_affine`,
  `csInf_image_affine`, `marginal_transport`) — presentation-independence of the axis
  (dBN time ↔ pencil weight).

**(2) The two-spin Lee–Yang trichotomy** — `formal/GaloisForLFunctions/HTGeometry/LeeYangTwoSpinCircle.lean`
For `leeYangTwoSpin b z w = 1 + bz + bw + zw`, driven by the contraction identity
`‖1+bz‖² − ‖b+z‖² = (1−b²)(1−‖z‖²)` (`normSq_contraction`):
- forced: `|b| ≤ 1` ⟹ no zero with both fugacities in the open unit disc
  (`leeYang_confinement`, strict for `|b| < 1`); diagonal circle law `‖z‖ = 1`
  (`diagonal_zeros_on_circle`);
- **marginal**: `b = ±1` ⟹ factorization `(1±z)(1±w)` — the interaction decouples, zeros pin at
  `∓1` (`leeYangTwoSpin_marginal_pos/_neg`, `leeYangTwoSpin_marginal_zero_iff`), diagonal double
  root = zero collision (`leeYangTwoSpin_marginal_diagonal_sq`);
- anti-forced: `|b| > 1` ⟹ zeros strictly inside the polydisc (`exists_zero_in_polydisk`,
  `exists_zero_in_polydisk_of_lt_neg`) — the fake region, rejected by the sign of `1 − b²`;
- packaged: `TwoSpinConfined b ↔ |b| ≤ 1` (`twoSpinConfined_iff_abs_le_one`), locus
  `= Icc (−1) 1` (`twoSpinConfined_eq_Icc`).

**(3) The positivity pencil is a closed forcing ray** — `formal/GaloisForLFunctions/HTGeometry/PencilPositivityRay.lean`
`pencilPositivityLocus A P = {t | (t•A − P).PosSemidef}` for real matrices, PSD `A`:
- up-set (`isForcingFamily_pencilPositivityLocus`), closed (`isClosed_pencilPositivityLocus` —
  intersection of closed half-lines, one per test vector);
- no-margin corollary: free half `1 ≤ sInf` ⟹ `(A − P).PosSemidef ↔ sInf = 1`
  (`pencil_posSemidef_iff_csInf_eq_one`) — Weil-type positivity at the physical weight is exactly
  the pinning `λ_c = 1`. Extends `CongruencePencil` toward the DeWitt card's flagged 2→3 targets
  (cone/threshold structure formalized; the operator-norm identification of `λ_c` remains open).

**(4) The carrier interaction locus is purely marginal; RH as marginality** —
`formal/GaloisForLFunctions/RHTower/LeeYangMarginalCarrier.lean`
`carrierInteractionLocus x = {y | CarrierHerglotz (x + y·i)}`:
- `= {0}` (`carrierInteractionLocus_eq_singleton`): localization holds exactly at the marginal
  coupling — the locus is the singleton of its own threshold
  (`carrierInteractionLocus_eq_threshold`), has empty interior
  (`interior_carrierInteractionLocus`), and is not a forcing family
  (`not_isForcingFamily_carrierInteractionLocus`) — **the monotone forcing mechanism fails at the
  arithmetic carrier**; localization there is never forced-with-margin;
- `RiemannHypothesis ↔` every hypothetical right-half `ξ`-zero coupling `½ − Re ρ` lies in the
  marginal locus (`riemannHypothesis_iff_zero_coupling_marginal`), equivalently the carrier is
  Herglotz at every seam coordinate `(ρ−½)(−i)` (`riemannHypothesis_iff_carrierHerglotz_at_zeros`).
  Both equivalences are unconditional; **neither asserts RH**.

## What is NOT proven here (quarantine)
The apex of the parent card — real-rootedness achieved at the marginal point, i.e. RH — is not
proven, not assumed, and appears only inside unasserted `↔` statements. `[OPEN CORE]` stays with
the parent.

## Verification (ledger)
- Each of the four modules: `lake build +<module>` green, **zero warnings**
  (deprecations `left_mem_Ici`→`self_mem_Ici`, `push_neg`, unused simp args, unused section
  variables all cleaned).
- `#print axioms` on all 25 public theorems (scratch file, 2026-07-16):
  every one depends on `[propext, Classical.choice, Quot.sound]` only — no `sorryAx`, no custom
  axioms, unconditional.
- Umbrella wiring: imports appended to `GaloisForLFunctions/HTGeometry.lean` (3 modules) and
  `GaloisForLFunctions/RHTower.lean` (1 module), verified present by inspection.
- **Deferred (user directive 2026-07-16: no further builds this session):** umbrella-target
  builds, `formal_tools.py lint --check-generated`, index regeneration
  (`formal_tools.py index`). Queued in
  `../../library-backlog/2026-07-16-fable-lee-yang-marginal-forcing-structure.md`.

## Gates
- [x] 0 → 1 / 1 → 2: inherited from parent (§1–§4 paper-proven there).
- [x] 2 → 3: the four modules above, unconditional, standard axioms only.
- [ ] 3 → 4: with the parent — "RH is the marginal stratum where crystalline forcing degenerates."

## Log
- 2026-07-16 (Fable) — created as the formal split of `lee-yang-localization` per Leaner's
  return note; four modules written, built module-by-module (single low-priority process each,
  shared-laptop discipline), axioms checked. Session seed 317826398794344498; rng move
  `invariant`, collision domains `auction-theory`, `renormalization`.
