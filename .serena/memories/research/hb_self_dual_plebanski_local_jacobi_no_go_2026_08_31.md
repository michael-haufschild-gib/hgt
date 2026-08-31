# HB self-dual Plebanski local-Jacobi no-go (2026-08-31)

Qualifying route kill on HB surviving radiative ++ causal-cut branch.

Internal corpus basis: exact self-dual AdS4 vertex `ads4SelfDualPlaneWaveVertex`; same-charge identity `V(p,q;h)=h^2(p-q)^2/2`; total third-order causal-cut reduction; Peierls stationary-channel elimination. External primary audit: flat self-dual gravity higher tree amplitudes vanish; AdS4 literature establishes deformed kinematic algebra/cubic vertex but no theta-cusp same-charge cyclic zero-set theorem.

New exact invariant: three local same-charge channels satisfy
`V(p,q;h)+V(q,r;h)+V(r,p;h)=h^2((p-q)^2+(q-r)^2+(r-p)^2)/2`, independent of AdS curvature. For real physical momenta and nonzero h, zero iff p=q=r. Double-copy squaring converts alternating kinematic Jacobi into positive graph-Laplacian rigidity.

Lean module: `formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingHBSelfDualPlebanskiLocalJacobiNoGo.lean`. Capstone: `d4HBSelfDualSameChargeLocalJacobiCancellationRouteKilled`. Wired into `formal/GaloisForLFunctions/RHTower.lean`. Direct `lake env lean` PASS. Targeted build PASS 11214/11214. Axioms only propext, Classical.choice, Quot.sound. Global lint only unrelated concurrently unwired modules.

Docs: `docs/drafts/pipeline/3-formalized/hb-self-dual-plebanski-local-jacobi-no-go.md`; failed card `docs/drafts/pipeline/5-failed/hb-self-dual-plebanski-local-jacobi-cancellation.md`.

Consequence: local self-dual integrability cannot extinguish HB radiative ++ source. Survivor must be a genuinely nonlocal causal Green/resolvent phase/orientation identity including completed continuum and zero-frequency/threshold sectors before left projection. This does not kill the full HB route.

Related prior memory: `mem:research/hb_finite_local_angular_threshold_no_go_2026_08_31`.