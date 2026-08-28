# SC rigged-Krein all-prime phase object — 2026-08-28

Formalized a new structural SC theorem in `formal/GaloisForLFunctions/RHTower/SourceHorizontalRiggedKreinPhaseObject.lean`; card at `docs/drafts/pipeline/3-formalized/sc-rigged-krein-all-prime-phase-object.md`.

## Result

For open-strip `s`, define prime weight `w_s(p)=|preDivisorPrimeCarrier s p|`, reservoir functional
`L_s(a)=Σ_p sqrt(w_s(p)) Re(a_{A(p)})`, and symmetric form
`B_s(a,b)=preDivisorOrientation s * (Σ_p w_s(p) Re(a_{A(p)})Re(b_{A(p)}) - L_s(a)L_s(b))`
on `DeningerHeightKothe`.

Lean proves:
- all series summable;
- `|B_s(a,b)| ≤ 2 p₀(a)p₀(b)`;
- reflection oddness `B_(1-conj s)=-B_s` and wall vanishing;
- every injective finite prime-axis Gram restriction equals the existing `preDivisorSharedReservoirMatrix` exactly;
- exact finite inertia transfers;
- unbounded negative index on right and unbounded positive index on left using canonical prime enumeration;
- combined capstone `preDivisorRiggedPrimeWittPhaseObject_capstone`.

Principal declarations:
`abs_preDivisorRiggedPrimeWittPairing_le`,
`preDivisorRiggedPrimeWittPairing_lineConj`,
`preDivisorRiggedPrimeWittGram_eq_sharedReservoirMatrix`,
`preDivisorRiggedPrimeWittPairing_unboundedNegativeIndex_right`,
`preDivisorRiggedPrimeWittPairing_unboundedPositiveIndex_left`,
`preDivisorRiggedPrimeWittPhaseObject_capstone`.

## Conjecture loop

C1 abstract bilateral Krein carrier: REDISCOVERED in corpus.
C2 analytic scalar orientation: FALSIFIED by corpus quantized jump/polar cancellation.
C3 rigged source form: PAPER-PROVED and LEAN-PROVED.

## Verification

Passed:
- `lake env lean GaloisForLFunctions/RHTower/SourceHorizontalRiggedKreinPhaseObject.lean`
- `lake build GaloisForLFunctions.RHTower.SourceHorizontalRiggedKreinPhaseObject`
- targeted `#print axioms` for five main theorems; only `propext`, `Classical.choice`, `Quot.sound`
- no forbidden `sorry/admit/axiom/opaque/unsafe`
- indexed by `scripts/formal_tools.py research`
- wired into `formal/GaloisForLFunctions/RHTower.lean` and `scripts/check_axioms.sh`.

Global lint still fails only on unrelated pre-existing unwired modules; this module is reachable and raises no lint error. Do not kill other agents' active Lean processes.

## Honest RH status

Closes SC infinite carrier/finite-packet compatibility (COMP) burden. It is not RH. It deliberately has infinite reflected negative index. Remaining exact SC core: construct coefficient-faithful meromorphic Xi determinant/landing from this rigged form and prove a source-derived positive polarization. Novelty label remains `[NOVELTY UNVERIFIED]`: exact application absent from checked corpus/literature, but no publication-level priority claim.
