# Finitary formation, joint saturation, and cofinal-law birth — Lean certificate

- **ID:** ULF-GTM-2
- **Stage:** 3-formalized
- **Paper theorem:**
  `docs/drafts/pipeline/2-fully-proven/universal-law-field/genesis-termination-mechanics/finitary-formation-joint-saturation-and-cofinal-law-birth-barrier.md`
- **Lean module:**
  `GaloisForLFunctions.HTGeometry.ConstitutiveFinitaryFormation`
- **Umbrella:** `GaloisForLFunctions.HTGeometry.UniversalLawField`

## Certified content

Lean proves, for an arbitrary index type and arbitrary set of laws:

1. composite monotone finitary formations are finitary;
2. every finite formation history has finite ancestry;
3. the union over all finite histories is finitary;
4. extensive finitary formations make this saturation an idempotent closure operator;
5. this operator is the least closure containing every generating formation;
6. the closure adjoining `0` exactly to infinite subsets of `ℕ` is nonfinitary;
7. no finite-history joint saturation of monotone extensive finitary formations equals that
   cofinal-birth closure.

## Significant declarations

```lean
finitaryFormation_comp
runFormations_finitary
wordSaturationClosure_finitary
wordSaturationClosure_least
cofinalBirth_not_finitary
cofinalBirth_ne_wordSaturationClosure
```

## Verification

- direct foreground elaboration:
  `lake env lean GaloisForLFunctions/HTGeometry/ConstitutiveFinitaryFormation.lean`;
- forbidden-token lint: `scripts/formal_tools.py lint`;
- axiom audit: only project-permitted foundations reported;
- final umbrella audit:
  `lake build GaloisForLFunctions.HTGeometry.UniversalLawField`.

No `sorry`, `admit`, new `axiom`, `opaque`, `unsafe`, or computational certificate is used.
