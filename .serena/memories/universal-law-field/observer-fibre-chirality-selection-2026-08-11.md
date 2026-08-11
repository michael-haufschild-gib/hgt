# Observer-fibre chirality selection mechanics (2026-08-11)

Paper card: `docs/drafts/pipeline/2-fully-proven/universal-law-field/formation-chirality-reversal-mechanics/observer-fibre-chirality-conservation-and-sufficient-reversal-selection-law.md`.
Lean: `formal/GaloisForLFunctions/HTGeometry/ConstitutiveObserverFibreChirality.lean`, wired into `HTGeometry.UniversalLawField`.
Stage3: `docs/drafts/pipeline/3-formalized/universal-law-field/formation-chirality-reversal-mechanics/observer-fibre-chirality-conservation-and-sufficient-reversal-selection-law-formalized.md`.

Exact laws: `klChirality = KL(P||R)-KL(R||P)`; observer current is source minus visible chirality; source = visible + fibre; currents compose additively through observer chains; conditional-disintegration theorem identifies current with forward conditional KL minus reverse conditional KL; involutive endpoint exchange kills visible chirality; preserving both directed KL costs makes fibre current zero; a structure-encoded strict chronology plus sufficient reversal comparison forces equal parameters.

Fourth-organ prediction: any observer tower ending in exact reversal must store all positive source chirality in signed fibre currents; some stage is positive, quantitatively at least average. This is signed counterpart of nonnegative total-variation overlap loss and competitive path-history variation, not a scalar identification.

Global grammar updated: chronology -> observer conservation -> serial locality -> reversal -> sufficiency -> selection, with independent scale-properness selector. Remaining RH landing: construct either a physical uniform full-formation-work bound, or a pre-zero scalar sufficient statistic comparison whose centered endpoint laws are exchanged by reflection. No RH claim.

Verification: direct Lean passed; final `lake build GaloisForLFunctions.HTGeometry.UniversalLawField` passed 11,826 jobs; `scripts/formal_tools.py lint --check-generated` passed; axiom audit only propext/Classical.choice/Quot.sound; no stale Lean/Lake processes.