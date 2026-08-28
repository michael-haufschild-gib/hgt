# HB source-independent response dichotomy (HC20)

Formalized 2026-08-28 in `formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMSourceIndependentResponseDichotomy.lean`, wired into `formal/GaloisForLFunctions/RHTower.lean`.

For constant divisor-independent response `c`, corrected BM current factors exactly as `c * unsquaredSourceCurrent`. Exact local classification: current zero iff `c=0 ∨ Re(q)=1/2`. Exact global classification: universal current zero iff `c=0 ∨ RiemannHypothesis`. Hence zero response is the unique blind fixed scalar branch; every nonzero fixed scalar response retains RH force. Unit fixed-response Ward is premise-free equivalent to RH and to HC18 canonical Peierls–Darboux optical darkness. Any nonzero fixed response is nonzero at every tilted Xi copy.

Combined with HC19, this gives sharp boundary: source-matched reflected response can fake stationarity, but nonzero fixed scalar response cannot. Remaining HB burden: derive a fixed source-independent scalar from literal action/Green/QNM physics and prove noncollapse.

Audit: direct Lean passed; target build passed (11914 jobs); seven endpoints use only `[propext, Classical.choice, Quot.sound]`; forbidden/diff clean; global lint only unrelated reachability failures. Literature audit found classical source-independent QNM excitation factors and Kerr conserved currents but no Xi/RH dichotomy. Cards: `docs/drafts/pipeline/3-formalized/hb-source-independent-response-dichotomy.md`, `docs/drafts/pipeline/5-failed/hb-source-independence-without-noncollapse-no-go.md`.