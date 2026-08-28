# HB canonical left-response Ward (HC21)

Formalized 2026-08-28 in `formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMCanonicalLeftResponseWard.lean`, wired into `formal/GaloisForLFunctions/RHTower.lean`.

Evaluate canonical regular/complementary BM left connection covector on its own exact horizon-to-AdS connection column scaled by global `c`. Despite fibre-dependent covectors and connection coefficients, each evaluation equals exactly `c` for every Xi copy. Both response functions are extensionally HC20 constant correction, and both corrected currents equal HC20 source-independent current pointwise. Local zero locus is `c=0 ∨ Re(q)=1/2`; global law is `c=0 ∨ RH`. Unit Ward for either branch is exactly canonical Peierls–Darboux optical darkness.

This closes radial left-QNM normalization, source-independence, branch choice, and noncollapse as separate burdens. HC22 later corrected the remaining-gap diagnosis: `ThetaCuspHawkingBMGlobalLeftCoordinatePeierlsIncidence` already gives exact canonical left-source incidence for one target-independent global Peierls propagator. Remaining two-branch gap is FE–Schwarz covariance of literal canonical left sources; HC22 proves that covariance is exactly equivalent to RH and fails at every tilted fibre.

Audit: direct Lean passed; target build passed (11915 jobs); ten endpoints use only `[propext, Classical.choice, Quot.sound]`; forbidden/diff clean; global lint only unrelated reachability failures. Card: `docs/drafts/pipeline/3-formalized/hb-canonical-left-response-ward.md`.
