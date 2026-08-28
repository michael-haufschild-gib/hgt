# HC16: FE–Schwarz orbit Peierls trace (2026-08-28)

Module: `formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMFESchwarzOrbitPeierlsTrace.lean`
Formalized card: `docs/drafts/pipeline/3-formalized/hb-fe-schwarz-orbit-peierls-trace.md`
Failed-route card: `docs/drafts/pipeline/5-failed/hb-positive-fe-schwarz-orbit-symmetrization-cancellation-no-go.md`

HC15 forced off-wall source-faithful continuation into at least four FE–Schwarz sectors. HC16 constructs the minimal orbit landing using the single HC14 target-independent Peierls propagator and sectorwise unit-carrier amplitudes.

Exact result:
`hbXiPeierlsFESchwarzOrbitCubicTrace n q = -4 * normSq(mixing(q)) * (8n+5)`.
It is invariant under both `xiZeroCopyReflectEquiv` and `xiZeroCopyConjEquiv`, strictly negative in real part off wall, zero iff `Re(q)=1/2`, and universally zero iff RH.

Stronger classification: reflection-invariant real pair weights `a,b` give
`weightedTrace = -2*(a+b)*normSq(mixing(q))*(8n+5)`, hence
`weightedTrace=0 ↔ a+b=0 ∨ Re(q)=1/2`.
Positive-total-weight averaging retains the RH detector. Opposite pair weights cancel unconditionally and are RH-blind.

Novelty audit through 2026-08-28 found only component antecedents (Khavkine Peierls/covariant phase space; Green et al. Kerr reflection currents; Spiers–Pound–Moxon nonlinear Teukolsky sources; Ripley et al. second-order Kerr numerics), not the Xi quartet trace or weight classification.

Verification: direct Lean passed; target-only build passed (11895 jobs after shared replay); six endpoint axiom prints only `[propext, Classical.choice, Quot.sound]`; forbidden scan clean; umbrella wired. Global lint failures were unrelated umbrella reachability errors.

Next burden: derive positive/nonzero-total-weight orbit-trace stationarity from a literal gauge-fixed Einstein–Teukolsky action or boundary Ward identity. Positive symmetrization itself is a proven no-go.