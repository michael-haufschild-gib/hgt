Follow-up to `mem:research/hawking_topological_darboux_starobinsky_spectral_flow_2026_08_25`.

Added two unconditional theorems to formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingTopologicalDarbouxStarobinskySpectralFlow.lean:
- d4BMXiThetaMirrorAIMEOrientedFlow_eq:
  delta * DeltaK_AIME = 24 delta^2 / D(q).
- d4BMXiThetaMirrorAIMEOrientedFlow_pos_iff:
  0 < delta * DeltaK_AIME iff Re(rho) != 1/2.
Here D(q)=a(1-a)(2-a)(3-a)(a+1)(a+2)>0 and delta=a-1/2.

Interpretation: exact AIME component has theta-oriented transfer strictly aligned with tilt. Any full second-order remainder capable of cancellation must contribute an oppositely oriented term of at least the exact magnitude 24 delta^2/D at tuned mass M_*(q). This is component-level source-specific sign, not a proof of full nonlinear passivity.

Target Lean passed; both new theorems have only propext, Classical.choice, Quot.sound. Lint has only unrelated existing umbrella-reachability errors. Scratch and generated oleans trashed.