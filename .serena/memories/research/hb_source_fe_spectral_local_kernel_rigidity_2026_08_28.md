# HC55 — HB source-FE spectral-local kernel rigidity (2026-08-28)

Formal module: `GaloisForLFunctions.RHTower.ThetaCuspHawkingBMSourceFESpectralLocalKernelRigidity`

Card: `docs/drafts/pipeline/3-formalized/hb-source-fe-spectral-local-kernel-rigidity.md`

Corpus-led result:
- Literal BM unit source and normalized source-FE cocycle are constant across `XiZeroCopy` multiplicity labels with equal support.
- Define spectral-fibre locality by `K q r ≠ 0 → q.1 = r.1`; this permits arbitrary mixing of multiplicity copies over one zero.
- For any reflection-real Ward kernel, a nonzero spectrally local coefficient forces `Re(q)=1/2`.
- Thus every tilted row is identically zero and its basis packet lies in the left radical.
- Trivial left radical gives a nonzero coefficient in every row.
- Therefore reflection reality + spectral locality + trivial left radical make full finite-packet source-FE covariance equivalent to RH.
- HC54's canonical line-conjugate permutation kernel is spectrally local iff RH, proving its unconditional off-wall nondegeneracy is genuinely cross-spectral.

Interpretive boundary:
HC52 diagonal and HC53 within-FE-orbit restrictions are subsumed at the support-fibre level. HC54 showed arbitrary algebraic nondegeneracy is insufficient. HC55 isolates exact remaining hard producer: derive spectral locality of the fixed physical augmented Einstein/Teukolsky Peierls current from source dynamics before divisor selection.

Audit:
- direct `lake env lean`: pass
- target-only `lake build GaloisForLFunctions.RHTower.ThetaCuspHawkingBMSourceFESpectralLocalKernelRigidity`: 11923/11923 pass
- 10 public theorem `#print axioms` checks: only `propext`, `Classical.choice`, `Quot.sound`
- umbrella import wired
- formal lint has no HC55 error; global failures are unrelated pre-existing umbrella reachability gaps
- bounded primary-literature audit found Kerr QNM different-frequency orthogonality from conserved local currents (arXiv:2210.15935) but no Xi source-FE kernel classification.