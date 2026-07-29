# Purity-boundary TOE and colour-cancellation selection (2026-07-29)

## Frozen conjecture

New Stage-1 card: `docs/drafts/pipeline/1-in-progress/purity-boundary-theory-of-everything.md`.

Public law: **“The universe is the edge of quantum possibility. Matter moves along the edge. Spacetime points away from it. All four forces are how the same edge bends.”**

Methodology is strict: this is an informed truth-hunch frozen before proof route; provability begins afterward. Do not reshape it to fit Gauss–Codazzi, projector calculus, exceptional geometry, Lean, or an action.

Frozen physical content: pure possibility is tangential; colour-preserving actuality is transverse; transverse event composition generates spacetime/time; one purity-boundary comparison curvature has gravity plus exact-global-form SM internal responses; mixed response is Higgs/soldering; long-wavelength limit is Einstein–Dirac–Yang–Mills–Higgs; complete actualization history is HGT to finite DA observers.

## Hostile novelty verdict

Broad ingredients are prior: quantum geometric metric/Berry curvature, projector and N-bein Cartan geometry, Gauss–Codazzi–Ricci, embedding/brane/Kaluza–Klein gauge-gravity, pure-spinor second fundamental forms, graviweak/spectral/exceptional programmes. Direct collisions include Akama–Hattori hep-th/0008133, Wang arXiv:0805.4479, Romero–Velasquez–Vergara arXiv:2406.19468, Låvenberg Zenodo 10.5281/zenodo.16993473, and 2026 Pati–Salam/DeWitt metric work. Exact actuality-normal conjunction remains priority-open, not proved. Current Nature verdict: DO NOT WRITE MANUSCRIPT.

Central hostile gaps: base-space construction, observer-independent actualization, operational Lorentz signature, universal-connection no-selection, kinematics≠dynamics, weak/Lorentz lock, topology debt, exceptional composition, matter/generations, finite prediction.

## Exact post-freeze survivor

Paper card: `docs/drafts/pipeline/2-fully-proven/not_new_scientific_knowledge/pure-spinor-color-cancellation-normal-selection.md`.
Formal certificate: `docs/drafts/pipeline/3-formalized/not_new_scientific_knowledge/pure-spinor-color-cancellation-normal-selection.md`.
Lean: `formal/GaloisForLFunctions/HTGeometry/PureSpinorColorNormalSelection.lean`, imported by `formal/GaloisForLFunctions/HTGeometry.lean`.

At standard pure spinor with W=A⊕B, dim_C A=3, dim_C B=2:
T = Λ²A* ⊕ (A*⊗B*) ⊕ Λ²B*.
Projection of Cartan second fundamental form to colourless normal B has only one nonzero sector:
Λ²A* × (A*⊗B*) → B (and reverse).
It vanishes on colour×colour, mixed×mixed, and any weak-scalar pair. For every nonzero colour bivector c, pairing(c,-) is surjective onto full B doublet.
Coordinate law:
β_4=-c12 m35+c13 m25-c23 m15,
β_5= c12 m34-c13 m24+c23 m14.

Lean declarations:
- `pureSpinorColorlessNormal_color_mixed_eq`
- `pureSpinorColorlessNormal_mixed_color_eq`
- `pureSpinorColorlessNormal_color_color_eq_zero`
- `pureSpinorColorlessNormal_mixed_mixed_eq_zero`
- `pureSpinorColorlessNormal_weakScalar_left_eq_zero`
- `pureSpinorColorlessNormal_weakScalar_right_eq_zero`
- `pureSpinorColorMixedNormalPairing_surjective`

Verification passed:
- direct `lake env lean GaloisForLFunctions/HTGeometry/PureSpinorColorNormalSelection.lean`, no warnings;
- final `lake build GaloisForLFunctions.HTGeometry.PureSpinorColorNormalSelection`, 8476/8476;
- `scripts/formal_tools.py lint`, passed (only pre-existing large-file warnings);
- `#print axioms`: only `propext`, `Classical.choice`, `Quot.sound`.
No stale Lean/Lake process remained.

Novelty classification: standard pure-spinor/representation mathematics, exact sector selection extracted here; not new physics. Physical reading (“actuality is forced colour cancellation creating spacetime”) remains conjectural.

## Next open core

Do not duplicate Gauss–Codazzi or projector curvature math. Solve `OPERATIONAL PURITY CROSSING`: base-free, gauge-independent event object; intrinsic colour-preserving normal selection and composition; incidence/topology/differentiability/soldering without prior spacetime; relative index paying weak/spacetime topology debt; exact Lorentz + S(U2×U3) selection; quantum-consistent unique IR action; finite parameter-reducing prediction.

The sharper exact question exposed by the survivor: why should physical actualization be the forced Cartan cross-contraction between colour-bivector and mixed colour–weak tangent sectors?