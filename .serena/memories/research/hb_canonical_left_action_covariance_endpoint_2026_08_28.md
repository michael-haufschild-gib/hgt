# HB canonical left-action covariance endpoint (HC22)

Formalized 2026-08-28 in `formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMCanonicalLeftActionCovarianceEndpoint.lean`, wired into `formal/GaloisForLFunctions/RHTower.lean`.

Corpus synthesis corrected HC21's remaining-gap diagnosis. `ThetaCuspHawkingBMGlobalLeftCoordinatePeierlsIncidence` already constructs one target-independent global Peierls propagator with exact canonical left-source BM incidence on every Xi fibre. HC22 separates this unconditional incidence from two-branch FE–Schwarz covariance.

For nonzero amplitude, reflected canonical regular left source equals canonical complementary left source iff `Re(q)=1/2`. Universal unit left-source covariance iff RH. Define `HBXiPeierlsCanonicalLeftActionCovariance n` as actual global incidence plus universal covariance; Lean proves this package iff RH, iff unit canonical regular-left response Ward, and iff canonical FE–Schwarz orbit optical darkness. On every tilted fibre, incidence remains exact, covariance fails, and canonical orbit optical power is strictly positive.

Novel survivor: incidence failure is not the obstruction. Any off-wall continuation must abandon individual two-branch covariance in favor of the four-sector FE–Schwarz orbit landing, or supply an independent law already strong enough to imply RH.

Audit: scratch/direct Lean passed; target build passed (11916 jobs); nine endpoints use only `[propext, Classical.choice, Quot.sound]`; forbidden scan clean; global lint only unrelated reachability failures. Formalized card: `docs/drafts/pipeline/3-formalized/hb-canonical-left-action-covariance-endpoint.md`. Failed-route card: `docs/drafts/pipeline/5-failed/hb-canonical-two-branch-left-action-covariance-no-go.md`.
