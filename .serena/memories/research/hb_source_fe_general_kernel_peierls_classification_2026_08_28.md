# HC52 — HB source-FE arbitrary-kernel Peierls classification (2026-08-28)

Formal module: `formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMSourceFEKernelPeierlsClassification.lean`
Formalized card: `docs/drafts/pipeline/3-formalized/hb-source-fe-general-kernel-peierls-classification.md`
Umbrella: imported by `formal/GaloisForLFunctions/RHTower.lean` after HC51.

New results:
- `hbXiPeierlsKernelForm K x y` allows an arbitrary ordered bivariate kernel on finite Xi packets.
- `forall_hbXiPeierlsKernelForm_packetTransport_iff_kernelWard`: full packet covariance iff `K(Rq,Rr) κ(q) κ(r)=conj(K(q,r))` for every ordered pair.
- `hbXiPeierlsUnitSourceFEKernelConjugation` is the source-cocycle anti-linear kernel involution; it squares to identity.
- `kernelWard_iff_kernelConjugation_eq`: Ward kernels are exactly its fixed points.
- `kernelWard_iff_exists_kernelSymmetrization`: every Ward kernel, and only one, is in the image of `A ↦ A + C(A)`; fixed kernel preimage is `K/2`.
- `kernel_diagonal_eq_zero_of_kernelWard_of_reflectionReal_of_tilt`: any reflection-real Ward kernel has zero diagonal at every tilted Xi copy, regardless of off-diagonal couplings.
- `forall_hbXiPeierlsKernelForm_packetTransport_iff_rh_of_reflectionReal`: for any reflection-real kernel nonzero on every diagonal, full packet covariance iff RH.

Interpretation: arbitrary mixed-copy/cross-fibre terms cannot hide fixed physical diagonal defect. Transported mixed-copy forms exist unconditionally, but identifying a reflection-real nondegenerate physical form with one remains RH-strength. This closes algebraic kernel loophole beyond HC51 diagonal classification. Remaining hard producer is literal augmented Einstein–Teukolsky/Peierls dynamics forcing fixed-form Ward covariance or phase-sensitive source cancellation.

Verification:
- direct `lake env lean` passed;
- target-only `lake build GaloisForLFunctions.RHTower.ThetaCuspHawkingBMSourceFEKernelPeierlsClassification` passed, 11920/11920;
- all 15 public theorem axiom audits: only `propext`, `Classical.choice`, `Quot.sound`;
- no forbidden declarations; `git diff --check` passed;
- formal lint has no HC52 issue; global failure only unrelated unreachable modules;
- scratch and Lean processes cleaned.

Bounded novelty audit: corpus search found HC51 diagonal theorem but no arbitrary kernel fixed-point classification. Primary literature search found Green–Hollands–Sberna–Toomani–Zimmerman arXiv:2210.15935 conserved Teukolsky bilinear form, but no Xi-source cocycle packet-kernel/RH rigidity theorem. Generic involution linear algebra is classical; novel content is literal BM/Xi specialization and arbitrary-kernel obstruction.