# Conservative carrier genesis and bipolar repair -- Lean certification

- **ID:** ULF-ERM-1
- **Stage:** 3-formalized
- **Paper source:** `docs/drafts/pipeline/2-fully-proven/universal-law-field/endogenous-representability-mechanics/conservative-carrier-genesis-bipolar-repair-base-change-and-fresh-return-defect-law.md`
- **Lean module:** `GaloisForLFunctions.HTGeometry.ConstitutiveCarrierGenesisRepair`
- **Status:** [LEAN-CERTIFIED] [UNCONDITIONAL] [ROUTE-INDEPENDENT] [NOT RH]

## Certified content

The module defines two-sided conservative unary-law extension and compatible semantic retraction,
then proves:

1. every admitted enlarged finite word restricts to an admitted old word;
2. every admitted old finite word lifts to an admitted enlarged word;
3. future-retaining repair pulls back exactly;
4. future-forgetting repair has the canonical old-to-new lax comparison;
5. a compatible semantic retraction supplies the reverse comparison and hence exact pullback;
6. the three-state carrier-genesis cell is conservative on old execution, has exact fine pullback,
   has a strict fresh-return defect for coarse repair, and admits no compatible retraction;
7. `carrierGenesisRepairMechanism_unconditional` bundles the mechanism without premises at theorem
   declaration level.

Principal declarations:

- `ConservativeUnaryLawExtension`
- `CompatibleUnaryLawRetraction`
- `conservativeUnaryLawExtension_restrict_word`
- `conservativeUnaryLawExtension_lift_word`
- `unaryLawInterior_pullback_conservative`
- `unaryLawClosure_pullback_lax`
- `unaryLawClosure_pullback_of_compatibleRetraction`
- `unaryLawClosure_pullback_conservative_iff`
- `carrierGenesisCell_freshReturn_strict`
- `carrierGenesisCell_noCompatibleRetraction`
- `carrierGenesisRepairMechanism_unconditional`

## Verification

- `lake env lean GaloisForLFunctions/HTGeometry/ConstitutiveCarrierGenesisRepair.lean`: pass.
- `lake build GaloisForLFunctions.HTGeometry.ConstitutiveCarrierGenesisRepair`: pass, 3,000 jobs.
- `lake build GaloisForLFunctions.HTGeometry.UniversalLawField`: pass, 11,580 jobs.
- `scripts/formal_tools.py lint`: pass.
- Scratch-file `#print axioms` audit: only `propext` and `Quot.sound` on audited declarations.
- Module wired into `HTGeometry.UniversalLawField`.

No `sorry`, `admit`, `axiom`, `opaque`, `unsafe`, computation, route-specific premise, analytic
hypothesis, or RH statement is used.

## Exact boundary

Certification proves repair behavior assuming a conservative carrier extension. It does not prove
that every exposed challenge canonically generates such an extension, nor that revision recursively
terminates or escapes. Those remain ERM-A, not certified consequences.
