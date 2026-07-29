Active Stage-1 card: docs/drafts/pipeline/1-in-progress/actuality-conservation-boundary-colligation-law.md.

Core physical target: actuality conservation. A source-complete objective event changes a coherent distinction into its complementary causal boundary rather than deleting it. Retained curvature is Standard Model gauge; target/frame curvature is gravity; mixed transfer is Higgs/soldering. Hypertranscendence is conjectured global nonclosure of accumulated event history, not yet a physical theorem.

Prior exact bridges:
1. SymmetryFractureDefectConservation.lean: for self-adjoint involution A, projections P,Q, and unitary U, T=UQ and S=UP are orthogonal partial isometries; S canonically realizes ker(T)≃coker(T). Existing exceptional model gives 4/6/4. Standard defect algebra.
2. QuaternionicActualityGraphLock.lean: for unit u,v,q under Spin(4) pair action (u,v)·x=u x v*, fixing q iff v=q* u q. The graph partner is unit; graph fixes Rq and preserves q⊥=(Im H)q. Standard custodial/observer-field bridge.

New exact no-go and classification (2026-07-29):
- Paper: docs/drafts/pipeline/3-formalized/not_new_scientific_knowledge/quaternionic-graph-endpoint-flatness.md
- Lean: formal/GaloisForLFunctions/HTGeometry/QuaternionicGraphEndpointFlatness.lean
Define endpoint right transport tau(q,r)=r* q. Lean proves unit/action, tau(q,q)=1, reverse=star, strict cocycle tau(r,s)tau(q,r)=tau(q,s), and triangle holonomy=1. Every unit pair transporter mapping q to r satisfies v=r* u q and factors exactly
  (u,r* u q)=(1,r* q)(u,q* u q).
Flat endpoint transport conjugates graph stabilizer Delta_q to Delta_r.

Killed subclaim: event-selected directions/stabilizers alone generate gravity. Endpoint directions admit canonical pure-gauge transport, so clock-direction disagreement is frame kinematics, not curvature. This is ordinary homogeneous-space/Cartan/Higgs mathematics, not new science. Extra path/history/connection data are necessary.

Strongest positive survivor: every transporter is uniquely flat endpoint transmutation times a source-stabilizer history residue. This identifies the first possible carrier of nonzero holonomy.

Frozen replacement conjecture: ACTUALITY MEMORY CURVATURE LAW—every objective event contains irreducible comparison history beyond its endpoint facts; the non-endpoint-compressible residue is not an added field but the missing part of the same actuality colligation. Its retained curvature gives SU3×SU2×U1, its created Lorentz-frame curvature gives gravity, and its mixed component gives Higgs/soldering, with no fifth sector. Public: “Gravity is reality remembering how quantum possibility became fact.” Sharper: “Facts do not curve the universe by themselves. The universe curves because it remembers how they became facts.”

New exact open core: SOURCE-COMPLETE HISTORY-RESIDUE UNIQUENESS. Derive objective colligation, q/r endpoints, presentation-invariant C_e=tau(q,r)M_e factorization, M_e from colligation rather than supplied, nonabelian composition/curvature, exact exceptional force decomposition, Lorentzian soldering/Einstein dynamics, and finite prediction.

Hostile blockers: residue arbitrary appended connection; presentation dependence; ordinary Berry/process-memory/Cartan rediscovery; compact SO3 cannot yield boosts/tetrad/free fall; flat lab false positives; peer exceptional residues/fifth forces; no unique E-D-YM-H action; HT no physical functor; no finite prediction.

Verification for QuaternionicGraphEndpointFlatness: direct `lake env lean GaloisForLFunctions/HTGeometry/QuaternionicGraphEndpointFlatness.lean` passed; final `lake build GaloisForLFunctions.HTGeometry.QuaternionicGraphEndpointFlatness` passed 3015/3015; #print axioms only propext/Classical.choice/Quot.sound; proof-debt scan clean; base formal lint passed; git diff --check passed; no stale Lean/lake process. Generated indexes were refreshed multiple times, but `lint --check-generated` could not stabilize because concurrent unrelated work created/edited ParametricSpectralBranch and then an unimported SpectralClusterTransfer during the checks. Do not attribute that failure to this module.

Shared worktree: HEAD was 42ee3160 at start; do not commit. Preserve concurrent dirty files.

Endogenous-possibility jump (later 2026-07-29): repeated GNS/history/process/Jordan audits suggest physics commonly fixes not only spacetime but also possibility carrier, intervention alphabet, and duality before events. Frozen sharper form of EVENT--SPACETIME RECIPROCITY: every objective event changes the type of what can happen next and creates the complementary comparison relating the new future to removed distinctions. Time is the non-finitely-compressible order of these changes; interaction is reciprocal comparison. Public: “The future does not exist until events create it. Gravity is how their futures disagree.” This is a hunch, not physics proved.

Exact new bridge: formal/GaloisForLFunctions/HTGeometry/EventRangeRecordCompletion.lean and docs/drafts/pipeline/3-formalized/not_new_scientific_knowledge/event-range-record-completion.md. For equal finite dimensions, faithful R:V→coker(T) makes V≃range(T)×coker(T); rank-six ten-to-ten gives exact 10≃6+4. Standard linear algebra, no novelty.

Integration with prior involution machinery: EventInvolutionComplement.lean now defines involutionCokernelRecord, proves involutionContinuation_prod_cokernelRecord_injective, and defines involutionRangeRecordCompletionEquiv. Thus A²=1 canonically selects the cokernel record and closes finite algebraic source-to-range+record completion; open physics is why objective source selects A, why its complement is causal rather than internal, and why composition yields Lorentz+GSM+Higgs and HT.

New mathematical target: source-generated fibred reciprocal process with event-created possibility fibres, positive source-derived partial dagger, and no finite source-preserving horizontalization. Hostile alternatives: fixed-carrier totalization, ordinary non-Markovianity, Stinespring dilation, infinite Cauchy data, supplied duality, arbitrary exceptional decoration. New open core in active card: EXCEPTIONAL ENDOGENOUS-POSSIBILITY RECONSTRUCTION, nine items ending in a finite gravity–gauge/clock–charge prediction. Nature verdict remains DO NOT WRITE MANUSCRIPT.

Verification: direct Lean for EventRangeRecordCompletion and EventInvolutionComplement passed; final `lake build GaloisForLFunctions.HTGeometry.EventInvolutionComplement` passed 2948/2948; capstone axiom audit only propext/Classical.choice/Quot.sound; formal lint passed; indexes regenerated; git diff check clean; no stale Lean/lake process.

Local-response no-go (later 2026-07-29): docs/drafts/pipeline/3-formalized/not_new_scientific_knowledge/color-event-local-response-independence.md and formal/GaloisForLFunctions/HTGeometry/ColorEventLocalResponseIndependence.lean. For any isometric X with XᴴX=I and arbitrary Hermitian H plus skew-Hermitian K, Y=X(H+K) has herm(XᴴY)=H and skew(XᴴY)=K. Hermitian/skew responses reconstruct the full comparison and equality of both is equivalent to equality of comparisons. Thus at every regular timelike 3×2 event, causal and internal response are independently prescribable. A common M3,2(C) carrier cannot derive a gravity–gauge relation, relative coupling, dynamics, or prediction. Exact positive survivor: local response space is the product Herm_n(C)×SkewHerm_n(C); any real force unification must restrict admissible successors or complete histories. Public discriminator: “The laws of nature live between events, not inside them.”

Priority boundary strengthened: causal-set sequential growth already makes spacetime grow event by event (Rideout–Sorkin), and Hermitian Jordan systems were proposed for Standard Model plus MacDowell–Mansouri gravity in hep-th/9302030. Nature novelty requires a source-selected succession law that correlates locally independent responses, uniquely derives 3+1 Lorentz plus U1/SU2/SU3 and E-D-YM-H dynamics, and yields a non-adjustable gravity–gauge or clock–charge prediction.

Verification: direct Lean passed; final `lake build GaloisForLFunctions.HTGeometry.ColorEventLocalResponseIndependence` passed 2956/2956; axiom audit only propext/Classical.choice/Quot.sound; formal lint passed; indexes regenerated; git diff check clean. Preserve shared dirty worktree; do not commit.