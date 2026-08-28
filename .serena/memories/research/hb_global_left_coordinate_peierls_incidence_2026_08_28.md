HC14 closed the HB augmented source-incidence burden in Lean.

Module: formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMGlobalLeftCoordinatePeierlsIncidence.lean
Umbrella: formal/GaloisForLFunctions/RHTower.lean

Construction:
- HBXiPeierlsPacket := XiZeroCopy →₀ ℂ; carrier is pair of packets.
- Fixed coordinate pairing is finite-support dot sum.
- hbXiPeierlsRadialWeight n q is negative BM complementary Frobenius exponent.
- hbXiPeierlsPropagator n is one target-independent Xi-diagonal symplectic rotation, fixed across all q and independent of amplitude/target.
- Canonical left connection covectors send literal source-scaled regular outer coefficients to (a,0) and conjugated Schwarz-complementary coefficients to (0,conj a).
- Global source pairing is skew and equals exact d4BMXiSecondHarmonicSourceScaledBoundaryConcomitant on every fibre.
- Pointwise Finsupp multiplication supplies symmetric/cyclic quadratic residual; algebraic square-root branch lifts give exact quadratic sources.
- Full phase-normalized Peierls cubic cut equals exact BM candidate unconditionally.

Main theorems:
hbXiPeierlsSourcePairing_skew
hbXiPeierls_BM_leftSource_incidence
hbXiPeierls_BM_quadraticSource_incidence
hbXiPeierls_phaseNormalizedCubicCut_eq_BM_candidate
hbXiPeierlsBranchSchwarzCovariant_iff
forall_hbXiPeierlsBranchSchwarzCovariant_iff_rh

New conclusion: literal radial source incidence/Peierls algebra is no longer the HB open core. Remaining source-fixed branch Schwarz covariance holds pointwise iff Re(q)=1/2 and globally iff RH. Abstract carrier enlargement, radial normalization, and target fitting cannot close that remaining step.

Verification:
- direct lake env lean passed cleanly
- target lake build passed (11885 jobs after shared dependency replay)
- #print axioms on five endpoints: [propext, Classical.choice, Quot.sound] only
- global lint has unrelated pre-existing unreachable-module errors; none for HC14
- frontier map was read-only and untouched by this work

Cards:
docs/drafts/pipeline/3-formalized/hb-global-left-coordinate-peierls-incidence.md
docs/drafts/pipeline/5-failed/hb-global-peierls-incidence-alone-no-go.md

Literature audit through 2026-08-28 checked arXiv 2305.19332, 2210.15935, 2112.11168, 0708.0450, 2509.03598; no external exact Xi-indexed construction/classification found.