# Dense arithmetic Lorentz-lattice rigidity law — Lean certificate

- **ID:** ULF-DALR-01
- **Stage:** 3-formalized
- **Paper proof:** `../../2-fully-proven/universal-law-field/dense-arithmetic-lorentz-lattice-rigidity-law.md`
- **Module:** `GaloisForLFunctions.RHTower.DenseArithmeticLorentzLatticeRigidity`

Certified declarations:

- `RHTower.trace_lorentzBoost`
- `RHTower.PrimeWeldIntegralLorentzLatticeFrame.traceDescent`
- `RHTower.eq_zero_of_primeWeldLorentzIntegralTraceDescent`
- `RHTower.primeWeldLorentzIntegralTraceDescent_iff`
- `RHTower.eq_zero_of_primeWeldIntegralLorentzLatticeFrame`
- `RHTower.primeWeldIntegralLorentzLatticeFrame_nonempty_iff`

The last theorem is the closed classification: one common invertible rank-two frame in which every
prime-log-weld Lorentz boost has integer coordinates exists exactly at horizontal grade zero.

Verification on 2026-09-02:

- `lake env lean GaloisForLFunctions/RHTower/DenseArithmeticLorentzLatticeRigidity.lean` — PASS
- `lake build GaloisForLFunctions.RHTower.DenseArithmeticLorentzLatticeRigidity` — PASS
- `/tmp` `#print axioms` audit — only `propext`, `Classical.choice`, `Quot.sound`
- wired into `GaloisForLFunctions.RHTower` and `HTGeometry.UniversalLawField`
- no umbrella build run
