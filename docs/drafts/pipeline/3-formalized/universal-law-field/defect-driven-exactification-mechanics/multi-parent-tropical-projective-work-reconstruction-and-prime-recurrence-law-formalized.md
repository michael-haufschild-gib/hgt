# Multi-parent tropical-projective work and prime recurrence — Lean certification

- **ID:** ULF-DDEM-TPW-1
- **Stage:** 3 — formalized in Lean 4
- **Paper card:**
  `docs/drafts/pipeline/2-fully-proven/universal-law-field/defect-driven-exactification-mechanics/multi-parent-tropical-projective-work-reconstruction-and-prime-recurrence-law.md`
- **Lean module:**
  `GaloisForLFunctions.HTGeometry.ConstitutiveTropicalProjectiveWork`
- **Umbrella:** `GaloisForLFunctions.HTGeometry.UniversalLawField`

## Certified mechanism

For every nonempty finite family of exact parent actions, Lean certifies:

- mandatory maximum work and reversible tropical-projective width;
- width nonnegativity and exact zero classification;
- invariance under a common potential;
- reference-parent work conservation along arbitrary finite histories;
- nonnegative work on closed histories;
- exact observer-memory reconstruction through kernel pairs;
- positive invisible-width witness when reconstruction fails;
- affine clock width as absolute elapsed time times clock span;
- centered-width zero iff centered parameter zero;
- arbitrarily late finite-prime phase returns carrying a linear tropical-work lower bound.

## Main declarations

| Clause | Lean declaration |
|---|---|
| parent increment bounded by mandatory work | `constitutiveExactWork_le_familyWork` |
| projective zero law | `constitutiveFamilyWidth_eq_zero_iff` |
| common-gauge work law | `constitutiveFamilyWork_add_common_potential` |
| common-gauge width invariance | `constitutiveFamilyWidth_add_common_potential` |
| local conservation | `constitutiveFamilyWork_conservation` |
| finite-history conservation | `constitutiveFamilyPathWork_conservation` |
| closed-history nonnegativity | `constitutiveFamilyPathWork_nonneg_of_closed` |
| observer reconstruction | `relativeProfile_factorsThroughRange_iff_collapsedWidth_zero` |
| invisible-width witness | `exists_collapsed_positive_familyWidth_of_not_factorsThroughRange` |
| affine absolute-width law | `affineClock_familyWidth_eq_abs_mul_span` |
| centered selector reduction | `affineClock_centeredWidth_eq_zero_iff` |
| recurrence/open-work prediction | `PrimeTropical.exists_large_return_with_tropical_width` |

## Verification

```text
lake env lean GaloisForLFunctions/HTGeometry/ConstitutiveTropicalProjectiveWork.lean
lake build GaloisForLFunctions.HTGeometry.UniversalLawField
python3 scripts/formal_tools.py lint
```

Direct foreground elaboration passes.  Dedicated foreground umbrella build completes 11,799 jobs.
Formal lint passes.  `#print axioms` on five capstones reports only:

```text
propext
Classical.choice
Quot.sound
```

No computation certificate, `sorry`, `admit`, project axiom, `opaque`, `unsafe`, Xi specialization,
or RH premise enters the proof.

## Certified boundary

`affineClock_centeredWidth_eq_zero_iff` is a selection reduction, not RH.  It proves that once a
nonzero prime clock span is present, projective width vanishes exactly at the centered parameter.
The missing arithmetic theorem is independent source-normal descent of the complete projective
profile at every Xi zero.

