# Verified-height amplification from an equivariant collar

- **ID:** verified-height-equivariant-collar
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) / counting interface / `[BRIDGE]`
- **Source:** `VerifiedHeightAmplification.lean`; `WindowLadder.lean`
- **Statement:** RH verified through `H` extends through `U` if the new
  positive-ordinate strip zeros in `(H,U]` contain at most one point in a
  central collar and no point in the right outer wing.

## Goal

Isolate the exact equivariant integer input needed to extend a verified RH
height without demanding nonvanishing along the entire top boundary.  The
interface remains valid when the old endpoint is itself a simple critical-line
zero.

## Theorem

For real `a,H,U`, let

```text
C(a;H,U) = {rho : xi(rho)=0, H<Im rho<=U,
            0<Re rho<1, 0<Im rho, |Re rho-1/2|<a},
W+(a;H,U) = {rho : xi(rho)=0, H<Im rho<=U,
             0<Re rho<1, 0<Im rho, 1/2+a<=Re rho}.
```

If every positive-ordinate strip zero through `H` lies on the critical line,
`#C(a;H,U)<=1`, and `W+(a;H,U)` is empty, then every positive-ordinate strip
zero through `U` lies on the critical line.

Indeed, a right-half-plane zero either lies in `W+`, which is excluded, or in
`C`.  In the latter case its critical-line reflection is a distinct second
member of `C`, contradicting `#C<=1`.  A left-half-plane zero reflects to the
excluded right half-plane.

The stronger whole-strip interface is also formalized: if the full increment
contains at most one distinct zero, RH extends through `U`.

## Lean certificate

- File:
  `formal/GaloisForLFunctions/RHTower/VerifiedHeightAmplification.lean`
- Theorems:
  `RHTower.rhVerifiedThrough_amplify_of_equivariant_collar` and
  `RHTower.rhVerifiedThrough_amplify_of_increment_ncard_le_one`
- Supporting declarations: `RHVerifiedThrough`, `stripZeroIncrement`,
  `centralStripZeroIncrement`, `rightWingZeroIncrement`.
- Axioms: only Mathlib foundations `propext`, `Classical.choice`, and
  `Quot.sound`; no analytic placeholder.

## Research consequence

`[BRIDGE]` This is an elementary symmetry-and-counting theorem, not new
literature knowledge and not a strict numerical improvement of the verified
height.  It corrects the analytic target.  A full top-edge minimum modulus can
vanish when the endpoint is a verified simple line zero.  The sufficient
source inputs are instead:

1. a central one-zero census in the collar; and
2. a zero-free certificate in only one outer wing.

The unresolved significant step is to derive both inputs, with explicit
`U>3,000,175,332,800`, from the infinite Euler/archimedean constraint rather
than by enumerating more zeros.

## Gates

- [x] 0 -> 1 in-progress: exact equivariant interface and proof stated.
- [x] 1 -> 2 fully-proven: finite-set/reflection proof complete.
- [x] 2 -> 3 formalized: both Lean theorems build and are axiom-checked.
- [ ] 3 -> 4 publication-ready: deliberately not promoted; this is a bridge,
  not a novel standalone theorem.

## Log

- 2026-07-10 -- formalized during the third verified-height attack.
