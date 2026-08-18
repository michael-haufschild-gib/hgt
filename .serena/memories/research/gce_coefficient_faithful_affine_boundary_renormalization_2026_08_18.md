# G-CE coefficient-faithful affine boundary renormalization

Formal module: `formal/GaloisForLFunctions/RHTower/MobiusGammaXiPreScalarAffineBoundaryRenormalization.lean`.
Card: `docs/drafts/pipeline/3-formalized/new_scientific_knowledge/ccm/g-ce-coefficient-faithful-affine-boundary-renormalization.md`.

Exact new bridge:
- actual moving zero-clock affine packet retains nonzero charge and zero marked odd jet;
- normalized zero-mode readout equals full completed Euler–Gamma/Xi source trace;
- forced correction is (-2i\,\logDeriv(xiNonrightCanonicalProduct)(iw)+boundarySelfSymbol);
- renormalized readout equals continued anti-causal Ward response;
- for every finite head/depth it equals `mobiusGammaXiCoupledErrorSourceResponse j N baseIndex` exactly, before limits;
- correction equals sourceResponse minus (-2i) times normalized affine readout, proving divisor complement is forced;
- along existing source-native strictly cofinal finite self-adjoint schedule it converges to (d=continuedXiAntiCausalWardResponse(1/2));
- zero-limit iff RH;
- all actual finite G-CE walls are PSD at fixed budget 4 iff RH;
- actual positive schedule budgets converge to (4+|d|^2).

Scientific verdict: requested boundary comparison is solved exactly and source provenance is retained, but it does not prove RH. It exposes the sharp obstruction: coefficient-faithful renormalization reconstructs radial Hardy debt (|d|^2); four-unit positivity remains equivalent to RH. Pure commutator, plain normalization, and universal (-I) cancellation are falsified.

Verification:
- direct `lake env lean` passed;
- targeted module build passed;
- axiom audit only `propext`, `Classical.choice`, `Quot.sound`;
- forbidden-token scan clean.
Global lint was blocked only by unrelated concurrent HTGeometry modules missing umbrella imports.