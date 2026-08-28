# HC50: HB source FE cocycle versus fixed Peierls rigidity (2026-08-28)

Formal module:
- `GaloisForLFunctions.RHTower.ThetaCuspHawkingBMSourceFECocycleFixedPairingRigidity`
- File: `formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMSourceFECocycleFixedPairingRigidity.lean`
- Card: `docs/drafts/pipeline/3-formalized/hb-source-fe-cocycle-fixed-pairing-rigidity.md`

Corpus-derived insight:
- Direct opposite-channel ratio `conj(a(Rq))/conj(a(q))` does not telescope as an anti-linear reflection cocycle.
- Correct FE-within-channel ratio is `κ(q)=1` at unit-source extinction, otherwise `a(Rq)/conj(a(q))`.
- It transports literal unit source exactly, is unique off wall, and obeys `κ(Rq) * conj(κ(q)) = 1` unconditionally.
- On a reflected Finsupp basis, fixed complex-bilinear Peierls pairing preservation is `κ(q)^2=1`.
- Lean proves `κ(q)^2=1 ↔ re(q.1)=1/2`; the two sign branches reduce to conjugate cubic carrier identities. One factors through centered real coordinate; the other contradicts nonzero Xi height via real/imaginary equations.
- Universal fixed-basis-pairing compatibility is equivalent to RH.

Proof-burden consequence:
- Source-faithful FE transport and transported-form compatibility are automatic.
- Missing HB producer must identify transported Peierls form with fixed physical Peierls form; that condition is already an exact RH receiver.

Audit:
- direct Lean passed
- target build passed 11918/11918
- public axioms only `propext`, `Classical.choice`, `Quot.sound`
- umbrella wired
- global lint has only unrelated pre-existing unreachable-module errors