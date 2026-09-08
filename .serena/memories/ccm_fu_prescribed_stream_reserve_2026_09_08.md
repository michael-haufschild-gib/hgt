# CCM-FU prescribed stream reserve — checked progress

Active goal remains unconditional RH proof/falsification via CCM-FU. RH NOT solved; keep goal ACTIVE. Frontier map READ ONLY (latest user override). No commits/pushes. No subagents. No experiments this turn. All six owned /tmp files removed and every owned Lean process terminal.

## Significant positive result
Closed frozen fixed-fraction prescribed-stream target:
actual bounded-quotient distinct target list t can be processed preserving relative order with exactly K helpers per target and ONE ceil(A sqrt M) final reserve batch. Every prefix physical signed two-coordinate displacement ≤ H sqrt M; every complete successor envelope ≤ C' M²; endpoint envelope decreases by M. Freshness accounting includes all prescribed primes in the source windows and all used helpers. Fixed b,K,H independent of initial budget C, cutoff and target. A,C' depend on C.

Actual hypothesis: initial P contains coupledTwoCore (all primes below15 except2), excludes2, source pool initially fresh, Psi(M,P)≤C M². Every target p prime, p<M, p∉P, 15≤p, M/p≤14. M=14(b+1)N. Exact capacity (K+1)|t|+ceil(A sqrt M)≤capacity−1. Eventually simpler 2(K+1)|t|≤capacity−1 suffices by PNT-derived square-root capacity. Initial P budget is explicit; this is NOT RH or exhaustive prime processing.

## Files and public surface
New generic leaves, global namespace HTGeometry (NOT GaloisForLFunctions.HTGeometry):
formal/GaloisForLFunctions/HTGeometry/InwardPlaneDisplacementReturn.lean:
- def planeDisplacementRadius z=sqrt(z1²+z2²)
- planeDisplacementRadius_add_le
- planeDisplacementRadius_inward_step
- exists_planeDisplacement_return_batch
- exists_planeDisplacement_restoring_batch

formal/GaloisForLFunctions/HTGeometry/InwardPlanePrescribedStream.lean:
- exists_planeDisplacement_prescribed_stream

Modified formal/GaloisForLFunctions/RHTower/MobiusDivisorPrescribedWindowRepair.lean:
exposed former private interfaces without changing proofs or original published theorem statements:
- def mobiusDivisorTwoPlanePacket (was packet)
- norm_mobiusDivisorTwoPlanePacket_le_nine (was packet_bound)
- mobiusDivisorCoupledTwoPool_data (was pool_data)
- exists_mobiusDivisorTwoPlaneWindowGeometry (was source_window_geometry)
- mobiusDivisor_two_plane_repair_error_budget (was repair_error_budget)
Private interfaces' internal references all updated.

New formal/GaloisForLFunctions/RHTower/MobiusDivisorPrescribedStreamRepair.lean:
- exists_mobiusDivisor_prescribed_stream_repair
- eventually_mobiusDivisor_prescribed_stream_repair
Imports generic stream and source window repair. Main theorem maxHeartbeats800000 locally. Full statement exports all-prefix physical displacement AND envelope bounds. Private physical_displacement_bound converts normalized sum to physical L1 bound.

All 3 new leaves wired into correct HTGeometry/RHTower umbrellas without building umbrellas.

Paper proof/frozen target/full scope:
docs/drafts/pipeline/3-formalized/ccm-fu-prescribed-stream-reserve.md
Moved from 1-in-progress after proof completed. Full rigorous proof/constants in card.
No new universal-law-field STATUS entry: result route-specific, no distinct route-independent RH law. Frontier map untouched.

## Mechanism
B=9, source inward margin c>0, reserve per helper ≥dM in BOTH square reserves. Euclidean radius r≤2 product norm. Inward step has Δr²≤−c r+2B². Set R=4B²/c+2B+c. Bound r(z+v)≤max(R,r(z)−c/4). Choose K with Kc/4≥2B. Prescribed packet raises radius≤2B; K helpers restore toR. Generic list induction excludes target list plus all already-used helpers, retains every prefix≤R+2B. Final n helper padding stays inR. Physical H=2(R+2B). Exact batch source identity:
Psi(P∪L)+min(reserve0,reserve2)≤E+2sqrt(E)D+D².
C'=C+2sqrtC H+H². A=(2sqrtC H+H²+1)/d. n helpers pay error+M. Fixed fraction follows (2A+2)sqrtM≤capacity−1 eventually, ceil(a)<a+1, sqrtM≥1, hence2n≤capacity−1.

## Validation — do NOT repeat
Scratch checks and exact foreground lake env lean emissions PASS for all 3 new leaves and modified source leaf. Final actual emission session21693 exit0. Audit session31740 exit0.
Audited exactly11 new/newly public theorems ONCE via /tmp:
generic4+stream1+sourceexports4+actual2.
All only propext,Classical.choice,Quot.sound. No new axiom, sorry, native_decide/computed certificate.
Index regenerated. Single lint --check-generated FAILED only3 unrelated concurrent missing umbrella imports:
RHTower.FokasLenellsCauchyResolvent,
HTGeometry.FokasLenellsJumpGeometry,
HTGeometry.FokasLenellsSingularPhase.
Large-file warnings preexisting. No owned proofleaf/debt errors. Scoped whitespacePASS.
Scoped Lake package audit remains pending because prior package planning attempted broad dependencies; do NOT retry broad planning/full builds. No lake build performed this turn.
No mathematical computation/RunPod processes, results or uploads. Do not rerun prior finiteweight screen.

Owned scratch files removed: /tmp/ccm_plane_return.lean, ccm_plane_stream.lean, ccm_window_geometry.lean, ccm_actual_stream.lean, ccm_fraction_append.txt, ccm_stream_axioms.lean. No owned Lean process live.

## Remaining hard problem and next turn
Full chain actual divisor source→renewable signed reserve→exhaustive selection→uniform O(M) signed Abel bound→RH.
This closes LINEAR RESOURCE COST for any bounded-quotient target stream under fixed fraction capacity. It does not renew supply across all quotient ranges, process multiple unbounded quotients, or land complete endpoint. Full path from empty with one uniform quadratic ceiling remains open. Prior fixed-weight terminal-head barrier does not rule out mainfixedpositiveweight completepath; do not overstate frontier's broader wording.

Potential source-local next direction, only investigated (NO theorem yet): initial fixed child core may have unconditional quadratic envelope by finite-label merger factor2 per prime, starting from existing mobiusDivisorSelectionEnergy_empty_le_nine_twentyFifths_sq. This would instantiate stream result nonvacuously, but is secondary to hard global renewal. Do not mistake it for missing global bound. Current successor envelope is max current energy and every immediate successor; read MobiusDivisorSuccessorAverageObstruction.lean at315. Existing exact initial bound in MobiusDivisorUniformSuccessorTransport.lean at245. Core definition in MobiusDivisorCoupledTwoSourceCone.lean at19. No generic factor2 bound located yet (quick research returned none; not proof of absence).

## Tool/check discipline
Use /Users/michael/Documents/code/hgt/formal workdir for Lean. One owned process; wait for terminal exit before next. Always lake env lean scratch then exact leaf olean onlyneeded. No umbrella builds. Axioms onlynewonce.
Lean lets in goals: dsimp only before intro to avoid introducing let-bound M as P.
Use spaces near comparisons to avoid '<m'/'≤m' Matroid notation.
List.sum_toFinset f hnd translates finset sum to mappedlist sum; take.Nodup from hnd.take without k arg.
Nat.ceil_lt_add_one (0≤a) verified.
Source theorem main already checked mathlib names through scratch; no need repeated #checks.
Serena manual read this turn; Lean semantic symbol support unavailable from previous evidence. update_plan not callable.
Prior relevant memory ccm_fu_weighted_terminal_head_barrier_2026_09_08. Prior21 theorems audited; don't recheck.
