# HC92 horizon/boundary relative source-FE cocycle rigidity

Formalized 2026-08-28 in `GaloisForLFunctions.RHTower.ThetaCuspHawkingBMRadiativeSourceFEHorizonBoundaryRelativeCocycleRigidity`.

Main closed theorem: `hbXiPhaseSensitiveUnitRadiativeSourceFEHorizonBoundaryRelativeCocycleRigidity`.

New result:
- Exact BM second-harmonic boundary transfer satisfies Schwarz conjugation and is nonzero on every Xi copy.
- Boundary response `P_B(q)=T(q)P_H(q)` is transported by `kappa_B(q)=T(Rq)kappa_H(q)/conj(T(q))`; boundary cocycle is nonzero and involutive.
- For every common nowhere-zero diagonal gauge b, `kappa_B^b/kappa_H^b = T(Rq)/conj(T(q))`; relative cocycle is gauge invariant.
- `kappa_B^b(q)=kappa_H^b(q) iff Re(q)=1/2` for every such b.
- Existence of one global common-gain gauge is equivalent to `RiemannHypothesis`.

Interpretation: HC91 kills single-channel reflection-reality by source-following phase gauge. HC92 proves a common gauge cannot erase horizon/boundary relative holonomy. Remaining HB proof burden is a physical derivation of universal horizon/boundary gain matching, not phase convention.

Audit: direct `lake env lean` passed; targeted `lake build` passed 13097/13097; axioms only propext/Classical.choice/Quot.sound; formal lint has no HC92 finding (only unrelated pre-existing unreachable modules). Card promoted to `docs/drafts/pipeline/3-formalized/hb-horizon-boundary-relative-cocycle-common-gauge-rigidity.md`.