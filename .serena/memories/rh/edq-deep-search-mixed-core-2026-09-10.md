# EDQ mixed-core deep search, 2026-09-10

Goal remains active and unachieved; no new source bound/RH proof. User forbids editing rh-current-frontier-map.md. No new Lean modules or mathematical computations this turn.

Appended section `Deep search: mixed prime correlation and the full-tail estimate` to docs/drafts/pipeline/1-in-progress/edq-full-covariance-core-attack.md (after line 1265).

Three further searches, all --any --mode deep --budget-seconds 120 --no-refresh --per-module 1:
- coprime Mobius dilation energy mixed correlation: 12 candidate_lemmas + 12 source_arguments, 120.006s.
- Mobius Gram Bessel dilation cutoff correlation: 16+16, 120.013s.
- signed bilinear cancellation Hilbert Cotlar: 12+12, 120.035s.
All partial, deadline/filter_and_judge unfinished, no proof_ideas or ingredient_sets, pending/incomplete coverage. All 80 declaration occurrences matched current source-block hashes; all source_only/unchecked. Statements reviewed; selected relevant bodies read. Do not treat retrieval as exhaustive or kernel validation.

Relevant exact source boundaries:
- MobiusDivisorLocalizedInteractions mixed selection difference bound retains 4^(|P|-1)*M*(floor((M-1)/(pq))+floor((M-1)/max p q)). Different family from raw prime-free Gram pairing; no growing-core bound.
- MobiusDivisorPrimeCorrelationPhysical release = 2*density(P+p)*p^(-3/2)*D_P(p). UniformRenewal gives fixed-P uniform-Y bound with explicit core residue + L1 Mellin boundary constant, and D_(P+p)(Y)<=-c_P sqrt p on Y in [p,(1+eta_P)p] for sufficiently large p. Keep release prefactor. Cannot replace changing-core estimates by fixed-core ones.
- MobiusAdditiveDilationDiagonalization has Parseval but requires remaining signed incidence point-evaluation bound.
- Sieve.HilbertBilinear has a harmonic Fourier multiplier; HTGeometry MontgomeryVaughanDampedMeanSquare retains spacing costs. Neither identifies actual EDQ symmetric kernel or closes signed remainder.

Actual prime split from prior turn still needs lower bound 2<A_N,Z> >= ||A_N||²+||Z||²-q||F_floor(N/p)||²-C N^eps. None of inspected candidates provides it.

Tried selecting small harmonic counterterm. Lexical deningerHarmonicPartial search + source followups did not provide suitable cofinal selection. Even granting H_N=0, full quotient-depth certificate >=2 N L eta_N²+N/L>=2N eta_N for all L>0. Available positive B gives eta_N=B exp(-(log N)^(1/3)/108), so this certificate grows faster than N^eps for eps<1. This is NOT a lower bound for actual energy, only a failure of that upper estimate, even with perfect scalar cancellation. Need stronger signed quotient-increment control.

Scratch checks of fixed-core candidates failed at missing transitive XiCTaylorThetaTailPrimitiveRayInteriorSquare.olean before examples checked; no dependency rebuild. Separate elementary certificate inequality checked via lake env lean /tmp/edq-tail-certificate-root-20260910.lean with narrow mathlib imports, exit0. Initial broad Mathlib run stopped exact owned child PID72743 at ~100s elapsed/11sCPU; parent closed exit143 before next run. Narrow imports fixed efficiency. No newtree => no axiom audit, lint or leaf/umbrella build.

All owned search/Lean sessions completed. Temporary JSONs and scratches cleaned in final cleanup. Preserve concurrent foreign changes to umbrellas, HTGeometry, HB docs and search scripts. No STATUS/frontier edits justified by this failed bound attempt.