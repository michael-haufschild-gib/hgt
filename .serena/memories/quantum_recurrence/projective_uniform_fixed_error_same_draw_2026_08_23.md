Frontier advance (2026-08-23): proved global-phase-robust, system-size-independent continuous-circuit hardness for maximally projective static Hamiltonians, and instantiated it for one ordinary nearest-neighbour Gaussian draw with laboratory growth and permanent Haar separation.

Files:
- formal/GaloisForLFunctions/HTGeometry/UniformFixedErrorSpectralTorusCircuitHardnessLaw.lean: added eventually_atMostQuarterCircuitEntropyBound_lt_projectiveBooleanCarrier. Strengthens circuit net entropy from <2^D to <2^(D-1), preserving capacity after fixing one global sign.
- formal/GaloisForLFunctions/HTGeometry/UniformProjectiveFixedErrorCircuitHardIntervalLaw.lean: new. Anchored Boolean spectral reflections form 2^(D-1) projective code, pairwise operator distance >=1 under every global phase. Quarter-net pigeonhole gives hard seed separation >3/20; maximal projective density and uniform continuity give syndetic intervals at physical operator error 1/10; physical Schrödinger bridge included.
- formal/GaloisForLFunctions/RHTower/NearestNeighborUniformFixedErrorContinuousCircuitSameDrawLaw.lean: new closed eventual existence theorem. For every polynomial exponent q and all sufficiently large L, one ordinary static nearest-neighbour two-local Gaussian draw has robust lab-time linear lower bound, syndetic positive-width intervals excluding every continuous SU(4) circuit of gate count <=(2L)^q at error 1/10, and permanent two-query Haar separation.
- Wired HTGeometry.lean and RHTower.lean.

Verification:
- lake env lean on all changed/new source files passed.
- targeted lake builds for both new modules passed.
- #print axioms on entropy, packing, physical interval, same-draw capstone: only propext, Classical.choice, Quot.sound.
- formal lint found no forbidden declarations in new work but global lint exits nonzero due unrelated pre-existing/uncommitted unreachable RHTower modules: CompletedSourceInfiniteJetClassification, FiniteResidueModeOperatorRank, FourierL2SobolevDomain, L2WeakDerivativeUniqueness, WeightOneCliffordLogClosure, WeightOneCliffordPositiveClosure, WeightOneCliffordSpectralClosure.
- no stale lean/lake process.

Scientific status: closes prior size-dependent-error weakness for polynomial continuous circuits and closes hidden global-phase flaw in naive Boolean packing. Does NOT yet prove Brown initial post-ramp plateau/first return, and late gate budget is polynomial. Next target: extend atMostQuarterCircuitEntropyBound comparison to s(n) ~ 2^n/[1024(n+1)] (near Hilbert dimension), then attack return-excised initial interval. Useful estimates: for R<=s<=2^n, n^2<=2^(2n), 1+16R<=2^(n+5), so term <=2^((34n+160)R+1); choose s=2^n/(1024(n+1)) to keep total entropy exponent below 2^n-1.