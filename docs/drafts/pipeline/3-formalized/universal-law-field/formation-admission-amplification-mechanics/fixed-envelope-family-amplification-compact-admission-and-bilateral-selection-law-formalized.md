# Fixed-envelope family amplification and bilateral selection — Lean certification

- **ID:** ULF-FAAM-1
- **Lean module:** `GaloisForLFunctions.HTGeometry.FixedEnvelopeFormationAmplification`
- **Status:** `[LEAN-CERTIFIED] [UMBRELLA-WIRED] [NO SORRY] [NO AXIOMS] [TARGETED BUILD]`

| Card result | Lean |
|---|---|
| Theorem 3.1 — packet fusion | `normalizedFormationPacket_add`, `fixedDecayAmplifiedDefect_factorization` |
| Theorem 3.2 — joint reconstruction and information-neutral reflection | `normalizedFormationPacket_reflection`, `normalizedFormationPacket_reconstructs_exponent` |
| Theorem 4.1 — one-degree compact-admission classification | `degreeCompactAdmission_iff` |
| Theorem 5.1 — finite detecting degree | `fixedDecayAmplifiedDefect_tendsto_one_of_eq`, `fixedDecayAmplifiedDefect_tendsto_atTop_of_gt`, `exists_detecting_degree_of_pos` |
| Theorem 5.2 — one-sided all-degree selection | `allDegreeCompactAdmission_iff_nonpos` |
| Theorem 5.3 — bilateral global selection | `bilateralAllDegreeCompactAdmission_iff_zero` |
| §8 — adaptive-decay countermodel | `adaptiveDecayPositiveDriftCountermodel_closed` |
| capstone | `fixedDecayBilateralSelection_closed` |

Sections 6, 7 and 9 are organ fusion, fourth-organ predictions and a relation to the frontier;
none asserts a theorem beyond the above, and no RH statement is claimed.

## Verification (2026-08-20)

The module elaborates from the tree with 0 errors; every public `theorem`/`lemma` in it reports
only `propext`, `Classical.choice`, `Quot.sound`.  It is imported by
`GaloisForLFunctions.HTGeometry.UniversalLawField`.
