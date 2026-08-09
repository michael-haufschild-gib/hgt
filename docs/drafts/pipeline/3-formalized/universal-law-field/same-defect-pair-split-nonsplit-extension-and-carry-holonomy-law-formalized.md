# Same-defect split/nonsplit extension and carry holonomy — Lean certification

- **ID:** ULF-DEFECT-2
- **Paper card:**
  `same-defect-pair-split-nonsplit-extension-and-carry-holonomy-law.md`
- **Lean module:**
  `GaloisForLFunctions.HTGeometry.ConstitutiveExtensionCarry`
- **Universal-law umbrella:**
  `GaloisForLFunctions.HTGeometry.UniversalLawField`

## Certified declarations

### Exact split event

`constitutiveSplitInclusion_injective`, `constitutiveSplitQuotient_surjective`, and
`constitutiveSplitQuotient_eq_zero_iff` certify the sequence with middle object `(ZMod 2)²`.
`constitutiveSplit_has_additiveSection` proves splitting; `constitutiveSplitCarry_eq_zero` proves
the canonical carry vanishes.

### Exact nonsplit event

`constitutiveCarryInclusion_injective`, `constitutiveCarryQuotient_surjective`, and
`constitutiveCarryQuotient_eq_zero_iff` certify the sequence with middle object `ZMod 4`.
`constitutiveCarry_no_additiveSection` proves no additive right section exists, while
`constitutiveCarry_one_one` proves the canonical carry on `(1,1)` is the nonzero kernel generator.

### Identical size, different memory

`constitutiveSplitMiddle_card` and `constitutiveCarryMiddle_card` prove both middle objects have
cardinality four. `constitutiveBaseHistory_period_two` and `constitutiveSplitHistory_period_two`
prove observation and split lift close after one base period. The nonsplit lift instead satisfies
`constitutiveCarryHistory_period_increment`, its increment is nonzero by
`constitutiveCarryHistory_increment_ne_zero`, and it closes only after the second base period by
`constitutiveCarryHistory_period_four`.

### Bundled field theorem

`constitutiveSameDefect_split_nonsplit_carry_holonomy` combines split versus nonsplit, zero versus
nonzero carry, closed observation versus open lifted history, and eventual lift closure in one
unconditional theorem.

## Verification

```text
lake env lean GaloisForLFunctions/HTGeometry/ConstitutiveExtensionCarry.lean
lake build GaloisForLFunctions.HTGeometry.ConstitutiveExtensionCarry
lake build GaloisForLFunctions.HTGeometry.UniversalLawField
```

All checks passed. `#print axioms` on pointwise exactness, nonsplitting, and bundled capstone reports
only `propext`, `Classical.choice`, and `Quot.sound`. No project axiom, placeholder, or unresolved
theorem premise is used.

## Exact field consequence

An ordered kernel--cokernel pair and positive size are not a complete constitutive invariant.
Extension class, equivalently carry up to coboundary, is independent memory; lifted recurrence
holonomy reads it even when endpoint observation and cardinality agree exactly.
