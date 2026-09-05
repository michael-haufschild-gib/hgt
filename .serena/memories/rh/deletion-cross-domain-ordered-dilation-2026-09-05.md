# Euler deletion: zero-independent cross domain and complete finite dilation

Goal remains ACTIVE, not complete or blocked. No RH proof, no verified novel architecture. User excludes all classic/spectral/Gamma/theta/Mobius mechanisms; use corpus research tool AND rg. No proactive subagents. Workspace has concurrent edits: preserve main card current candidate (cylinder-signature refinement), do not restore older C6 holonomy.

## Finished new leaves
1. formal/GaloisForLFunctions/RHTower/EulerDeletionQuasiShuffleCrossDomain.lean (189 lines). Namespace RHTower.DeletionChronologicalLimit contains generic Abel finite-variation theorem and proof of crossPrefix_converges. Public RHTower.tendsto_chronologicalCrossPrefix_eulerDeletion_domain (line172): for all p,q:N and s,t:C with positive real parts and sum >1, chronological cross prefix of eulerDeletionWeightedJump p s and q t converges; NO ZERO ASSUMPTION. Formal p denotes actual modulus p+1. RHTower.tendsto_chronologicalSecondPrefix_eulerDeletion_domain line180 gives self limit for every Re(s)>1/2. Ordered convergence only; no arbitrary rearrangement or absolute summability away from zero asserted.
2. formal/GaloisForLFunctions/RHTower/EulerDeletionQuasiShuffleOrderedDilation.lean (~162 lines). Namespace RHTower.DeletionOrderedDilation. Define Wpq^N(x,y)=sum n<=N/q sum m<=(qn-1)/p x_m*y_n. ordered_deletion_eq_wedges line35 proves arbitrary-sequence exact four-term law H(a_p x,a_q y)=W11(x,y)-p Wp1(x o p,y)-q W1q(x,y o q)+pq Wpq(x o p,y o q). le_strict_floor_iff line29 verifies pm<qn (diagonal excluded). Dirichlet specialization line84, Hermitian specialization line105. Actual source bridge ordered_hermitian_eq_chronologicalCrossPrefix line124. hermitianDilationCombination_eq_crossPrefix line144 equates grouped four-term expression with source at every cutoff; hermitianDilationCombination_converges line154 gives zero-independent domain limit. No separate wedge limits assumed.
Both wired immediately after EulerDeletionQuasiShuffleSecondConvergence in RHTower.lean, CrossDomain before OrderedDilation. Do not full-build umbrella.

## Proof idea
Inner weighted deletion prefixes converge by existing bounded-prefix Abel theorem. They are bounded. Multiply inner prefix by outer conjugated kernel. Product tends to zero and has summable increments: jump*kernel is O(n^-(Re(s)+Re(t))); bounded prefix*kernel increment absolutely summable for Re(t)>0. Apply generic Abel with bounded outer periodic coefficient prefix. Exact finite dilation is two applications of existing eulerDeletion_weighted_Icc_eq_dilation, retaining all strict floor cutoffs. Thus convergence and finite identity themselves are not zero-location producers.

## Docs and literature
Complete paper proof / exact scope / validation: docs/drafts/pipeline/3-formalized/euler-deletion-cross-domain-and-ordered-dilation.md. Main audit card QSR2.5 and source-convergence paragraph updated; new leaves audit added. STATUS entries EDQS-DOMAIN-001 and EDQS-ORDER-001 explain route-independent limits of existence and reindexing. Main novelty gate corrected: literal ordered periodic double series is published object, exact fit to Kelliher–Masri, Analytic continuation of multiple Dirichlet series of Euler–Zagier type, equation1.4 and section9.2, https://math.ucr.edu/~kelliher/papers/LFunctionsFull.pdf (primary opened, 2004 manuscript). Not novel object. Further source refinement law is still missing; only that could support qualifying architecture. Komori–Matsumoto–Tsumura IJNT11.pdf also inspected as nearby ancestry, different coefficient indexing; excluded functional equations NOT used.
Analytic continuation holonomy is already rejected by concurrent main card: identical functions agreeing on common open region agree throughout connected continuation domain for all exponents, not only zeros. Current cylinder-signature pivot asks finite-degree closure and nontrivial signature refinement BEFORE continuation. Degree2 source closure is concurrent existing module EulerDeletionQuasiShuffleCylinderClosure. No new coherence theorem produced here.

## Exact validation and processes
Scratch dir /tmp/hgt-deletion-cross-limit-VJDXsM: CrossLimit.lean, OrderedDilation.lean, FinalAudit.lean. All own Lean sessions TERMINATED after output; no known live own process.
- Final CrossLimit scratch session76218 exit0, standard axioms.
- CrossDomain targeted lake build session91386 exit0, one leaf built35s; replayed existing PolydiscWeierstrass warning only. 8792 jobs count is cached dependency graph, not full build.
- Final OrderedDilation scratch77352 exit0, standard axioms.
- OrderedDilation targeted build53504 exit0, leaf30s.
- Imported FinalAudit48130 exit0. Seven capstones report ONLY propext, Classical.choice, Quot.sound.
- formal_tools.py lint94706 exit0, existing large-file warnings only. Earlier main-card transient unrelated Brizard unreachability is not current blocker; did not edit Brizard.
- git diff --check scoped files exit0.
- research exact hermitianDilationCombination_converges refreshed index and retrieves leaf154.
- ps process inventory denied by sandbox; all individually tracked owned commands had terminal exit results. No need escalation or killing other work.
- No full build, no Runpod computations, no commit/push. Preserve unrelated concurrent changes.

## Next work
Do not repeat finished validation or claim QSR2.5 still lacks finite ordered dilation. Decisive source-derived replication/dilation coherence remains unproved. The literal analytic object and ordinary double-shuffle are published; architecture novelty remains unestablished. Reopen corpus-first independent mechanism search or test current finite cylinder-signature pivot's actual non-tautological source law. Do not count additional scalar closure identities as RH progress without testing what they add.