# Theta-source global conservative current sewing law

- **ID:** `ULF-ODTM-6`
- **Stage:** 3 — formalized in Lean 4
- **Scientific status:** `[PROVED HERE] [DEPENDENCY-CLOSED] [LEAN-FORMALIZED] [NOT RH]`
- **Paper proof:**
  `docs/drafts/pipeline/3-formalized/universal-law-field/on-shell-defect-transmutation-mechanics/theta-source-global-conservative-current-sewing-law-paper.md`
- **Lean modules:**
  `HTGeometry.ConstitutiveDependentLpGaugeTransport`;
  `RHTower.HedenmalmThetaSourceGlobalConormalCurrentSewing`

## Formalized capstones

Lean constructs the canonical contraction
`D_mu=(1+||C_mu||)^(-1) C_mu`, proves it is nonzero with range exactly the source eigenline, and
places each reflected pair in the oriented Hilbert double `G_mu ⊕₂ G_(-mu)`.  These doubles sew
into one dependent `ell²` formation space.  Its global reflection is isometric and involutive; its
global diagonal current is bounded; and the exact identity

```text
R D R = Chi D
```

holds, where `Chi_mu=(-1)^(dim G_mu-1)`.  A single injected packet recovers the original
unnormalized current exactly after multiplication by its known denominator, so global boundedness
does not erase local Jordan history.

## Verification

Scratch and project-path elaboration pass.  Targeted named leaf build passes
(`10978/10978`); umbrellas are wired but were not built.  Eight audited capstones depend only on
`propext`, `Classical.choice`, and `Quot.sound`.  Scoped forbidden-declaration scan and
formal lint and `git diff --check` pass.

## Remaining gate

Global formation and functional-equation conservation now exist unconditionally.  The identity
sharpens the missing selection law: any RH-bearing mechanism must constrain source-fibre
occurrence or an equivalent arithmetic formation budget.  Generic reflection, bounded sewing,
and positivity cannot do this alone.
