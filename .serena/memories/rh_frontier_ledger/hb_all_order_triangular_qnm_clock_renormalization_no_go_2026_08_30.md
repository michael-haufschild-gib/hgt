# HB all-order triangular QNM clock-renormalization no-go (2026-08-30)

Formalized a class-level kill of all finite-order and formal all-order history-local QNM-solvability producers.

Artifacts:
- Module: `formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMAllOrderTriangularQNMClockRenormalizationNoGo.lean`
- Capstone: `RHTower.d4BMMixedCasimirAllOrderTriangularQNMClockRenormalization_noGo`
- Card: `docs/drafts/pipeline/3-formalized/hb-all-order-triangular-qnm-renormalization-no-go.md`
- Umbrella: `formal/GaloisForLFunctions/RHTower.lean`

Mathematics:
- For arbitrary nonlinear remainder hierarchy whose order-k term depends only on lower corrections, nonzero simple BM Jost derivative gives a unique infinite correction tower by strong recursion.
- Zeroth correction equals the exact physical mixed-Casimir BM counterterm.
- Every tilted Xi fibre has all hierarchy equations solved while the leading correction is nonzero.
- Under source-reduced darkness preservation, full tower vanishes iff Re(q)=1/2; globally full zero tower iff RH.
- The leading all-order correction extinguishes the exact returned Evans determinant on every Xi fibre.
- This kills perturbative solvability at every finite/formal order as an HB selector. Survivor: independently derive global no-renormalization/standard-clock law, or leave simple-pole/history-local class through genuine non-triangular resonance collision.

Audit:
- Direct `lake env lean`: pass.
- Targeted module build: pass.
- Axioms: only propext, Classical.choice, Quot.sound.
- Corpus research sees module/capstone and umbrella import is wired.
- Repo lint red only on unrelated pre-existing reachability debt; new module is reachable.
- Current literature audit: arXiv:2607.19492 supplies all-order QNM frequency shifts but no Xi/RH nonselection classification.
- No own Lean process left running; other concurrent agents had their own Lean processes and were not touched.

Related prior result: `mem:rh_frontier_ledger/hb_modewise_qnm_clock_renormalization_no_go_2026_08_30`.