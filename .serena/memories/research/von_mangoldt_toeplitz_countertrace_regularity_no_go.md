# Von Mangoldt Toeplitz countertrace regularity no-go (2026-08-08)

Formalized unconditionally.

Modules:
- GaloisForLFunctions.HTGeometry.PowerMomentRatioEscape
- GaloisForLFunctions.HTGeometry.MomentToeplitzRegularityNoGo
- GaloisForLFunctions.RHTower.VonMangoldtToeplitzCountertraceRegularityNoGo

Capstone:
- RHTower.vonMangoldtToeplitzCountertraceRegularityNoGo

Proof route:
1. Define positive log-segment measure sum over n>=2 of finiteVonMangoldtRealWeight n times volume restricted to (log n, log(n+1)].
2. Exact identity: integral x^q dnu = vonMangoldtSuccessorRelativeMoment(q+1)/(q+1).
3. Infinitely many primes give positive measure above every threshold.
4. Generic finite-measure theorem proves adjacent power-moment ratio tends to infinity using 2R/3R split.
5. Hence source reverse adjacent ratios tend to zero.
6. Exact opening cancellation plus bounded counterweights yields geometric-tail contradiction.
7. Unbounded entries exclude both bounded l2 Toeplitz realization and any l2-valued linear realization from c00.
8. Capstone retains exact opening cancellation and constant finite countertrace law.

Audit:
- direct lake env lean checks pass
- targeted lake build GaloisForLFunctions.RHTower.VonMangoldtToeplitzCountertraceRegularityNoGo passes
- #print axioms: only propext, Classical.choice, Quot.sound
- formal_tools lint reports unrelated pre-existing umbrella reachability failures; none names these three modules
- card moved to docs/drafts/pipeline/3-formalized/new_scientific_knowledge/other/von-mangoldt-toeplitz-countertrace-regularity-no-go.md

No RH, PNT asymptotic, numerical computation, sorry/admit/axiom/opaque/unsafe.