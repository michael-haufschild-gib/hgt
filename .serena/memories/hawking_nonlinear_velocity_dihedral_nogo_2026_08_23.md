# Nonlinear Hawking velocity dihedral no-go (2026-08-23)

Created `formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingNonlinearVelocityDihedralNoGo.lean`, imported by `RHTower.lean`, documented in `docs/reports/endpoints.md`.

Exact results for `V(a,w)=i M₂(a,w)/XiC'(w+ia)`:
- `M₂(-a,-w)=M₂(a,w)` for complex w.
- For real w, `M₂(a,-w)=conj M₂(a,w)` and `M₂(-a,w)=conj M₂(a,w)`.
- `V(-a,-w)=-V(a,w)`; for real w, `V(-a,w)=-conj V(a,w)` and `V(a,-w)=conj V(a,w)`.
- Closed no-go: an inversion-complete pair has both vertical velocities nonpositive iff both vanish. Otherwise one partner has strictly positive vertical velocity.

Research significance: unweighted one-sided/passive damping across the full Xi inversion divisor cannot orient all nonlinear Hawking resonances. Surviving RH producer must be chiral/tilt-weighted (break inversion pairing), force zero vertical velocity/real-sheet retention, or use a multiplicity-complete divisor-centroid law. General local centroid velocity via argument principle is classical; novelty lies, if anywhere, in a theta-backreaction-selected weighted sign law.

Verification: target Lean compiled; module olean built only for import; #print axioms run only on 12 new theorems plus new velocity definition, all depending only on `[propext, Classical.choice, Quot.sound]`; scratch files deleted; no umbrella build or git.