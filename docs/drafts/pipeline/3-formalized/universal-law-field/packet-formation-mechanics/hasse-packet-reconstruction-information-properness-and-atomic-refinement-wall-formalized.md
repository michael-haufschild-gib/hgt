# Hasse packet formation, reconstruction, information properness, and atomic wall — Lean certification

- **ID:** ULF-PFM-1-CERT
- **Paper card:**
  `packet-formation-mechanics/hasse-packet-reconstruction-information-properness-and-atomic-refinement-wall.md`
- **Lean module:**
  `GaloisForLFunctions.HTGeometry.ConstitutiveHassePacketFormation`
- **Universal-law umbrella:**
  `GaloisForLFunctions.HTGeometry.UniversalLawField`

## Certified mechanism

This module certifies one formation mechanism, not another route receiver.

1. `hasseFiniteDifference_packet` proves that each finite alternating Hasse row forms the single
   cancellation packet `(1-q)^n` before any infinite refinement.
2. `hasSum_hassePacketRecovery`, `hassePacketJointAtom_factor`, and
   `hasSum_hassePacketJointAtom` prove a parameter-independent geometric recovery kernel and the
   exact factorization
   `joint packet atom = Fermi scale × recovered packet depth`.
3. `coe_hassePacketScale_eq_salemFermiKernel` identifies the scale marginal with the already
   certified Salem Fermi kernel.
4. `hasSum_hasseAtomicMass_fixedColumn` and `summable_hasseAtomicMass_iff` classify the unsigned
   atomic refinement exactly: it is summable iff `1 < sigma`.
5. `packet_formation_atomic_refinement_wall` proves the critical-strip separation: every formed
   depth kernel is summable while the coefficientwise atomic refinement is not.
6. `finite_fermiFormationMeasure` proves positive Fermi formation is a finite measure for every
   positive exponent and normalizer.
7. `fermiFormationMeasure_eq_imp_parameter_eq` proves global parameter recovery from formation
   measure equality.
8. `reflected_fermiFormationJeffreys_eq_zero_iff_center` proves the exact reflected-information
   selector: for `0 < sigma < 1`, symmetric KL work vanishes iff `sigma = 1/2`.

Together these declarations certify the paper's load-bearing law:

> formation can remain admitted after every coefficientwise refinement has ceased to exist, while
> one common recovery kernel preserves enough positive information to identify reflection center.

## Verification

```text
lake env lean GaloisForLFunctions/HTGeometry/ConstitutiveHassePacketFormation.lean
lake build GaloisForLFunctions.HTGeometry.UniversalLawField
scripts/formal_tools.py lint
```

All checks passed.  A separate `#print axioms` audit of reconstruction, atomic-wall, measure,
parameter-recovery, and reflected-Jeffreys declarations reports only `propext`,
`Classical.choice`, and `Quot.sound`.  There is no project axiom, `sorry`, `admit`, `opaque`, or
`unsafe` declaration.

## Exact scope

Certified declarations cover formation, reconstruction, admission wall, finite positive measures,
identifiability, and reflected-information selection.  The complex Hasse row integral, its full
eta-series identity, the zero-phase orthogonality, and the QFI lower bound remain paper-level in the
source card.  They are not claimed as Lean theorems here.

Consequently this certificate does **not** prove RH.  The successor paper theorem now proves that
functional reflection does lift information-neutrally through every common packet-recovery kernel,
but also proves that this is an isometry and therefore preserves, rather than kills, reflected
Jeffreys work.  The remaining selector conditional is strictly stronger: a pre-zero source relation
must force that conserved symmetric work to vanish.
