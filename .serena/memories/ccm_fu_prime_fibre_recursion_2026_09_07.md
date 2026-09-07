# CCM-FU exact two-cutoff fibre recursion and orientation reversal

## Goal/status
RH goal ACTIVE, not solved. Full chain: completed Guinand–Weil source → marked rectangular current → affine Suzuki checkpoints → signed curvature → coherent prime–polar–Gamma/unit-Riesz boundary → Xi-screw Green → RH.
Current turn made verified progress: exact actual-source recursion and complete mixed energy update at integer prime-dilation anchors; cofinally positive isolated retained prime fibres after processing smaller primes. PE4/PE4G, SD1 and RH remain OPEN. Frozen factor-one targets unchanged. PE5 independent averaging remains fully refuted (earlier memory), and earlier late-prime block endpoint control remains closed.

## New source law (root namespace RHTower)
Let F(M,P,R)=mobiusDivisorSelectionFibre M P R and Q(M,P)=mobiusDivisorSelectionEnergy M P. For p prime, N<p, p∉P, p∉R:
F(p*N,P,insert p R) = -sqrt(p)*F(N,P,R).
F(p*N,insert p P,R) = F(p*N,P,R)-sqrt(p)*F(N,P,R).
This is exact integer homothety including the finite source labels, Möbius signs, terminal zeros, and arbitrary prior processed P. No asymptotic or changed coefficient system.
For N≥2 the exact energy law is
Q(p*N,insert p P)-Q(p*N,P) = -2sqrt(p)*Σ_(R⊆Pi(p*N)\{p}) F(p*N,P,R)*F(N,P,R).
The copied square cancels the removed p-containing energy, leaving the COMPLETE mixed inner product. No sign of that mixed term is proved. The law is at exact pN anchors; general nonintegral quotients need the clipped terminal block retained.
When Pi(N)⊆P, smaller source concentrates at ∅ and F(pN,P,{p})=-sqrt(p)*S(N), S(N)=Σn∈Icc1N C_n(N).

## New leaves already verified
`MobiusDivisorPrimeFibreHomothety.lean` (215 lines,8 public theorems):
1 mobiusDivisorSelectionFibre_eq_sum_Icc: extend the squarefree active support to Icc1M using nonsquarefree and terminal zero coefficients.
2 mobiusDivisorSelectionFibre_mul_prime hp hNp P R hpP hpR: full reflected copy.
3 mobiusDivisorSelectionFibre_mul_prime_singleton: singleton is reflected smaller head.
4 mobiusDivisorSelectionFibre_of_all_source_primes_processed N P R hP: all source mass at ∅ if Pi(N)⊆P.
5 mobiusDivisorSelectionFibre_mul_prime_of_all_small_primes_processed: scalar -sqrt(p)*S(N) landing.
6 mobiusDivisorSelectionFibre_insert_mul_prime: every p-free fibre update.
7 mobiusDivisorSelectionHead_insert_mul_prime: head update.
8 mobiusDivisorSelectionEnergy_insert_mul_prime hp hNp hN P hpP: exact two-source energy change.
Imports LatePrimeFibres, EulerDeletionQuasiShuffleConvergence and Mathlib.Algebra.BigOperators.Group.Finset.Powerset.

`MobiusDivisorRetainedPrimeOrientation.lean` (86 lines,6 public theorems):
1 sum_mobiusDivisorDilationChannel_seven_neg: S(7)<0 from PREVIOUSLY analytic both-negative last-prime groups at7 and exact sum preservation.
2 mobiusDivisorSelectionFibre_seven_mul_prime hp h7p: at P=mobiusDivisorSelectionPrimes7 (primes2,3,5), singleton in cutoff p*7 equals -sqrt(p)*S(7).
3 mobiusDivisorSelectionFibre_seven_mul_prime_pos: positive for every prime p>7.
4 exists_mobiusDivisorSelectionFibre_positive_gt B M₀: some prime p>7 with M₀≤7p and B<F(p*7,Pi7,{p}). Thus cofinally unbounded positive retained fibres.
5 not_forall_mobiusDivisorSelectionPrimeFibre_nonpos: no blanket sign law for all retained prime singletons after arbitrary P, even with prime p<M unprocessed.
6 mobiusDivisorSelectionHead_insert_seven_mul_prime_gt: processing p in that actual state strictly increases the head.
Original prime coefficients C_p(M)≤0 from earlier unsigned positivity. Merging smaller source labels can reverse their orientation. No new experimental evaluation was performed or used.

## Verification DONE; do NOT repeat
Both scratch files passed; exact leaf checks `lake env lean <leaf> -o <exact olean>` passed with no errors/warnings. Both needed oleans exist; both imports wired ONCE directly after MobiusDivisorLatePrimeBlocks in RHTower.lean. No lake build, umbrella, full, or dependency build.
All14 NEW public theorems axiom-audited ONCE: only propext, Classical.choice, Quot.sound. Do not re-audit these or earlier12 block/25 PE5 growth/26 Euler-pole results.
Global formal lint ran once.10 unrelated concurrent modules missing umbrella imports: RHTower.ThetaCuspEffectiveCompensationSource, EffectiveFirstAtomJets, EffectiveFirstAtomProfiles, EffectiveLikelihoodCooling, EffectiveOddDeterminant, EffectiveReflectionApproximation, EffectiveSourceApproximation, EffectiveTailScale (full names all start ThetaCusp); HTGeometry.FirstAtomOddTailAlgebra and HankelThreePerturbation. Neither new CCM-FU leaf flagged. Preserve other work.
Index ran once (7changed0removed including concurrent work), git diff --check passed, new certificate links and one-per-leaf wiring checked. All10 owned scratch/log files removed; no owned Lean process remains.

## Documentation
New certificate: docs/drafts/pipeline/3-formalized/ccm-fu-prime-fibre-recursion.md.
PE4 card appended exact retained recursion, complete mixed energy law, positive singleton counterfamily, proof statuses. Updated frontier CCM-FU row/paragraph and SD1 card. Added compact route-independent `MUST-RETAINED-SOURCE-ORIENTATION` after MUST-217, instead of further lengthening that already large entry.
No route retirement: PE4 is not refuted by positive retained fibres. The failed blanket sign extension is subordinate; strongest positive survivor is the full retained-field recursion and energy identity, both formal.

## Next actual obligation
Control the signed mixed inner product or a compensating original-budget invariant during smaller-prime interleaving, including final S(M)^2≤Q(M). Do not treat the recursion alone, another equivalent receiver, or additional local sign counterexamples as the missing bound. General pN quotient anchors may need real clipped-block transport for scheduling at every fixed cutoff. Do not drop terminal blocks.
Existing late-band result p≥M/2 is still a common-sign isolated scalar block; every subset energy≤max endpoints. This cannot be extended wholesale after smaller-prime processing because exact reflected copies inherit S(N)'s signs. Both positive and negative retained contributions must be handled by the source controller.

## Lean proof patterns verified
- For full fibre sum, unfold selectionIndices, sum_filter; nonsquarefree C vanishes. Extend Icc1(M−1) to Icc1M via terminal C(M,M)=0.
- Restrict p-containing target label to p|n, then `sum_Icc_filter_dvd_reindex p (p*N) hp.pos`, `Nat.mul_div_cancel_left N hp.pos`.
- For n≤N<p, hp.coprime_iff_not_dvd plus Nat.le_of_dvd gives coprime. Apply mobiusDivisorDilationChannel_mul_coprime and ArithmeticFunction.moebius_apply_prime.
- Label identity `(p*n).primeFactors\P=insert p(n.primeFactors\P)` from Nat.primeFactors_mul and hp.primeFactors. Cancel inserted p via ext and p absent on each side.
- `Finset.sum_powerset_insert (notMem_erase p U) f` splits U.powerset using `conv_lhs => rw [← insert_erase hpU]`. This gives exact energy decomposition without enumerating the cube.
- For `(if ∅=∅ then ... else ...)`, use `if_pos rfl` or simp; bare rw[if_true] does not match the unevaluated equality.
- Square-root divergence: `(Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop).const_mul_atTop hpos`; get eventual threshold from tendsto_atTop then eventually_atTop. Select an actual prime beyond max8(max N M₀) via Nat.exists_infinite_primes. No prime numerical certificate required.
