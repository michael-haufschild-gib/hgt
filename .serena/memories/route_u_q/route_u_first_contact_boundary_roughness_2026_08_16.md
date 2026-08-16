# Route U: first-contact boundary roughness (2026-08-16)

Formalized in `formal/GaloisForLFunctions/RHTower/SuzukiFirstContactBoundaryRoughness.lean`; dedicated card `docs/drafts/pipeline/3-formalized/route-u-first-contact-boundary-roughness.md`.

Closed capstone:
`riemannHypothesis_or_ccmFirstContactBoundaryRoughness :
  RiemannHypothesis ∨ CCMFirstContactBoundaryRoughness`.

If RH is false, there is a least positive aperture with zero restricted Weil/Friedrichs ground energy; every strictly smaller positive aperture has positive ground energy; the zero ground state is attained and physically nonzero; no strict smooth-interior source represents it.

Mechanism: false RH -> negative compact smooth screw-energy witness via exact Suzuki criterion; realize it in a larger aperture; combine small-aperture positivity, antitonicity, continuity, sInf/IVT to select first contact; ground-state attainment; smaller-aperture positivity excludes all strict smooth-interior representatives.

Novelty audit: Suzuki 2026 already gives qualitative existence of some degenerate aperture. No exact collision found for least-contact selection plus smooth-interior exclusion. No priority claim without independent review.

Verification:
- direct `lake env lean`: pass
- exact leaf `lake build GaloisForLFunctions.RHTower.SuzukiFirstContactBoundaryRoughness`: pass (10492/10492; missing oleans rebuilt)
- public theorem axioms exactly `propext`, `Classical.choice`, `Quot.sound`
- forbidden declaration scan clean
- wired in `formal/GaloisForLFunctions/RHTower.lean`; umbrella deliberately not built
- route map kept read-only

Next hard core: extract an actual boundary defect/trace invariant for first-contact ground state, or pivot to Route Q source-native cofinal incidence if corpus has no boundary compactness/trace theorem.