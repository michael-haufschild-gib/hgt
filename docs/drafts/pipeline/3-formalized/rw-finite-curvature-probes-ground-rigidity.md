# Finite literal prime-curvature probes preserve the full ground floor

- **ID:** RW-FINITE-CURVATURE-PROBES
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean); bounded novelty audit, universal absence unverified
- **Source:** RW; exact two-jump expansion and constrained physical-sample fibre density.
- **Statement:** For every aperture and every finite set of physical probe points, the compact smooth exact-pole sources whose normalized real observables have simultaneously zero prime generator, jump energy and Gamma-two at all probes are dense in the completed constrained form domain. Their actual Rayleigh infimum equals the original constrained ground energy.

## Dependency-closed paper proof

Fix the actual finite signed prime index set `J_a`. For each probe `x`, collect `x`, every first shift `shift(i,x)`, and every ordered second shift `shift(i,shift(j,x))`, with `i,j∈J_a`. The union over finitely many probes is a finite footprint `F`. No assumption that the shifts commute is needed.

Split the footprint into `F_in={y∈F:|y|<a}` and its complement. Prescribing zero complex source values on `F_in` leaves a form-norm dense smooth exact-pole fibre by the established finite-sampling theorem. Every compact interior source already vanishes at the other footprint points: its topological support lies inside `(-a,a)`, so both endpoints and exterior points are forced zero.

The real normalized observable `f(y)=Re(g(y))/(e^{y/2}+e^{-y/2})` therefore vanishes on the entire footprint. Every first difference at a probe is zero; every first difference at a first-shift point is zero. The literal generator and jump energy vanish. Every summand in the unconditional ordered two-jump formula for Gamma-two also vanishes, including every rate-variation term. Thus all chosen readers are exactly zero simultaneously, with the original rates and cutoffs retained.

Density in the constrained form norm implies continuity of the complete Weil quadratic and physical mass along approximants. Approximate a nonzero constrained near-ground vector inside this zero-footprint fibre; physical mass stays nonzero and its Rayleigh value approaches the same value. The upper bound for the repaired Rayleigh infimum follows for every positive tolerance; its lower bound is the original constrained ground-energy lower bound. Hence the two infima agree exactly.

## Strong positive survivor

All finite local prime generator/energy/curvature repairs remain compatible with every completed near-ground state, at every aperture, even when the finite footprints contain closed endpoints or exterior points. This identifies the exact receiver after arbitrary finite probe repairs. It does not address a continuum of probes, integrated inequalities, Fourier constraints or stronger norms.

## Audit

- Corpus search before new code: `prime jump curvature finite evaluation ground infimum`; deep retrieval is supplemented by exhaustive literal `gammaTwo` source search because semantic coverage is not certified.
- All ordered two-step footprint points must be accounted for; no sampling of probe points or indices.
- Named old-mode leaf build and final `lake env lean GaloisForLFunctions/RHTower/CCM/CCMFiniteCurvatureProbeGroundRigidity.lean` passed, exit 0, no warnings; umbrella wired. Four public declarations are `silent_of_interior_samples_zero`, `exists_silent_source_close`, `exists_silent_source_rayleigh_lt`, and `silentRayleigh_inf_eq`, in namespace `RHTower.FinitePrimeCurvatureProbes`.
- All four `#print axioms` checks report only `propext`, `Classical.choice`, `Quot.sound`. No numerical experiments, heartbeat changes or full builds.
- Bounded public searches for Weil finite-point generator/curvature repairs found no matching theorem. Inspected [Connes–Consani Appendix C](https://alainconnes.org/wp-content/uploads/Selecta.pdf) concerns finite Mellin vanishings and the all-aperture criterion; [Zhu's compact-window paper](https://arxiv.org/html/2608.24827v2) concerns Fourier envelopes and finite matrices. Neither inspected argument identifies this fixed-aperture physical two-jump fibre and its exact infimum. Universal public-literature or training-data absence is unverified.
