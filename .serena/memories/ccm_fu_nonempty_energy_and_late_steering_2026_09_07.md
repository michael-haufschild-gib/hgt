# CCM-FU nonempty-energy obstruction and exact late-prime steering

Goal remains ACTIVE: RH, SD1, PE4, PE4G and PE4C are OPEN. This turn is PROGRESS: closed an actual nonempty-energy counterexample plus all-cutoff source steering laws. Full proof chain: completed Guinand–Weil source → marked rectangular current → affine Suzuki checkpoints → signed curvature → coherent prime–polar–Gamma/unit-Riesz boundary → Xi-screw Green → RH.

## New Lean leaves, verified and wired
1. `formal/GaloisForLFunctions/RHTower/MobiusDivisorNonemptyEnergy.lean` (140 lines). One definition and nine public theorems.
   - `mobiusDivisorNonemptyEnergy M P := E_M(P)-F_M(P,empty)^2`.
   - `mobiusDivisorNonemptyEnergy_eq_sum` identifies it with all nonempty label squares; `_nonneg` unconditional.
   - `mobiusDivisorSelectionEnergy_insert_cross` is deltaE=2 sum p-free F(R)F(p+R).
   - `mobiusDivisorNonemptyEnergy_insert_cross` is deltaV=2 sum nonempty p-free F(R)F(p+R)-F({p})². Exact head cancels; no sign claim for mixed term.
   - `mobiusDivisorNonemptyEnergy_union_late_primes`: V(P∪L)=V(P)-sum_L C_p² for disjoint unprocessed late-prime block (pprime,p<M,M≤2p). `_le` follows for arbitrary head sign.
   - `mobiusDivisorSelectionEnergy_late_block_steering`: for q∉L, delta_q E(P∪L)=delta_q E(P)-2 t_L F(P,{q}), with t_L=sum_L K_p≥0. q need not be prime in this identity; ordinary unprocessed prime application is included. `_le` for Fq≥0 and `_ge` for Fq≤0. Late consumption can help or harm depending on retained singleton sign. This is not a producer of the missing signed budget.
2. `formal/GaloisForLFunctions/RHTower/MobiusDivisorNonemptyEnergyObstruction.lean` (283lines). Five public theorems.
   - `mobiusDivisorDilationChannel_twentyOne_tail_box`: -0.08<C5(21)+C10(21)<-0.06; C15(21)>0.1.
   - `mobiusDivisorSelectionFibre_twentyOne_three_gt`: F21({2},{3})>0.04, using exact all-cutoff reflected interpolation to F7({2},empty)=C1(7)+C2(7), where existing boxes give C1≤.115, -C2≥.139. sqrt3>1.7 gives >.0408.
   - `mobiusDivisorNonemptyEnergy_twentyOne_step`: V21(insert5{2})-V21({2})=2 F21({2},{3}) C15(21)-(C5(21)+C10(21))². Only one nonempty p-free overlap survives. The p5 partner support is R empty or {3}, established by restricting to multiples5 and reindexing to d≤4.
   - `_twentyOne_strict_growth`: increase>1/1000.
   - `not_forall_mobiusDivisorNonemptyEnergy_insert_le`: universal all-state, all-prime V-contraction is false. This says nothing about existence of a good V-path.

## Analytic proof inputs
No numerical experiment is used. Gamma box .5768≤gamma≤.57722 comes from harmonic half-error and existing analytic bound. Defects D1 in[.1536,.1545], D2[.0003,.0021], D3[.2525,.2551], D4[-.2076,-.2041], from analytic log2/log3 bounds. Rational root sandwiches for5,10,15,20,21 are squared and checked algebraically. Exact quotient-block identities bound C5+C10 andC15. C20=0 via mu4=0 and coprime multiplicativity. All supporting helpers are private and covered through new public-declaration dependency audits.

## Diagnostic, guidance only
Frozen question: every prime step contracts V=E-H²? Separate full-path existence question. `nonempty_reanalysis.py` in docs/drafts/pipeline/2-fully-proven/computations/ccm-fu-adaptive-prime-energy-2026-09-06/ reads ALL stored subset states through32. Heads reconstructed from isolated late-prime energy differences, using known analytic coefficient Cp=-(sqrtM-sqrtp)(2gamma-1), no channel table or greedy regeneration. All late anchors cross-checked. 41409 edges, 2472 V-growing edges; firstM21 P{2} q5. V=.0896410812874598→.09741929690042564, head .07026250973107048→-.0019584110320793316, initialE=.5305858519824452. Every cutoff through32 has some V-nonincreasing complete path, only numerical. Max head disagreement across anchors4.196643033083092e-14; min reconstructedV -1.9817480989559044e-14 at zero endpoint. Original tolerance1e-12max(1,E0). Output `nonempty-reanalysis.json` records inputSHA, allcutoff path witnesses and diagnostics. Nothing imported intoLean.

## Documentation
Promoted temporary in-progress nonempty card to `docs/drafts/pipeline/5-failed/ccm-fu-nonempty-energy-contraction.md`, with paper proof, positive survivor, exact statuses and audit. Updated PE4 card, SD1 card, computation README, current frontier row/detail/no-go table. Universal STATUS entry `MUST-NONEMPTY-ENERGY-COUPLING` states generic component-energy/sign distinctions understandable without route research. No RH completion claim.

## Verification: do NOT repeat
Both leaves passed scratch and exact foreground `lake env lean <leaf> -o <exact olean>`, no warnings on final versions. All15 NEW public declarations axiom-audited ONCE: only propext/Classical.choice/Quot.sound. Both wired once after LatePrimeInterleavingCapacity. No old-declaration audit, umbrella/full/dependency build. Single global lint found ONLY five unrelated concurrent missing umbrella imports: ThetaCuspDeepTailCalibration, ThetaCuspDeepTailCooling, ThetaCuspTwoAtomReflectedApproximation, ThetaCuspTwoAtomReflectedBounds, ThetaCuspTwoAtomSourceApproximation. Neithernewleaf flagged; no proofdebt error. `formal_tools.py index` regenerated3reports and refreshed6changed0removed insearchindex. OwnedLean handles allcompleted; nine owned/tmp scratch/audit/lint files removed at end.

## What remains
A growing interleaving is necessary (previous capacity theorem), but head-only balancing cannot assume V monotonically contracts at every smaller-prime step. Need compatible control of nonempty mixed products AND the signed singleton that determines late steering. Late-block identity implies its insertion cannot change the V-gain of a fixed other prime: subtract identical removed-square terms before/after. That corollary is immediate from the stronger exact block identity; no separately named theorem was added. Finite existence of V-nonincreasing paths does NOT bound complete E or the final head. Do not replace the actual goal by another receiver or finite pass.

## Lean notes
For nonempty sum identity, `change` E to sum of F²; unfolding only E without F leaves syntactically distinct sums that linarith treats independently. For root normalization at21, norm_num splits some roots: rewrite sqrt10=sqrt5*sqrt2, sqrt15=sqrt5*sqrt3, sqrt20=2sqrt5; ring_nf; norm_num[Real.sq_sqrt]; ring. For finite set erasure with numeral inequalities, norm_num[Finset.erase_insert,hpR] at congrArg-erase equality succeeds where simp alone leaves {3,5}.erase5. Verify mathlib names in scratch, oneforegroundLeanprocess, emitonlyneededoleans, auditonlynewdeclarationsonce.