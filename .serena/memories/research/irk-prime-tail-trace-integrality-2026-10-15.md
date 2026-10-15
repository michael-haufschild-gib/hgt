# IRK trace integrality checkpoint (2026-10-15)

User insists on IRK and specifically: irrational canonical trace integrality must kill off-line multiplicity through noncommutative topology, not conventional spectral counting. Apply hgtl7, corpus-only research, no numerical experiments; active RH goal is NOT complete.

New verified leaf: formal/GaloisForLFunctions/RHTower/PrimeRotationTraceTailIntegrality.lean (225 lines; 8 public theorems + 1 definition). Umbrella import once at RHTower.lean:8579 at checkpoint. Actual-path `lake --old env lean` passed warning-free, olean/ilean fresh. All 9 public declarations audited using /tmp/irk-trace-tail-axioms.lean: only propext, Classical.choice, Quot.sound. API index refreshed. Global lint exit1: unrelated concurrent SoninPrimePolarHeadMellin and SoninPrimePolarResidueExclusion unreachable; preserve concurrent files.

Exact results:
- primeLogFrequency m = 2*pi*k iff m=0 and k=0 (finite integral prime coefficients). Proof: exp left algebraic; exp(2*pi*k) transcendental for k!=0 by Gelfond-Schneider base -1 exponent -2*k*I. Then existing prime log independence.
- primeRotationTraceCoordinate q rank m = rank + primeLogFrequency m/(2*pi*q) has unique rank and coefficient vector for q!=0.
- Trace admitting such coordinates avoiding every finite prime set iff integer (primeRotationTrace_tail_iff_integer, line130).
- Two distinct prime trace-coordinate lattices intersect exactly in Z, even with different nonzero natural clocks (primeRotationTrace_two_prime_ranges_iff_integer, line210). Equal traces force both Chern coordinates zero and ranks equal.

These are arithmetic coordinate-lattice results. They DO NOT construct actual Xi projective modules, canonical traces, Chern pairings, or an all-prime K0 trace range. No RH theorem or beyond-literature novelty claim.

Hard source target: construct one Xi relative-index class descending to two distinct prime rotation algebras with trace-preserving common ambient identification; stronger target is descent to every finite-prime tail. Finite Euler deletion preserves Xi divisor in Re(s)>0, but holomorphic unit equivalence does NOT yet imply bounded projective-class descent. Need actual map from relative analytic divisor complex to finite projectives retaining off-line Chern charge. Next cycle must work on this map, not further arithmetic receiver lemmas or estimates.

Corpus: FiniteGaugeTailCharge.lean fully read; finite unimodular Euler gauges holomorphic nonzero on positive half-plane, finite-modification divisor invariants have dense fibers; continuous separated invariant readout collapses. This warns against silently promoting tail divisor invariance to a continuous K0 class. Finite Euler deletion alone is insufficient.

Auxiliary paper-only audit (NOT formalized after user focus): native rotation algebra has no generalized modulation eigenvectors in projective modules. Distinct phase diagonal => (V-lambda)a=0 has rank<=1, hence compact, hence a=0 by Calkin faithfulness. Projectives embed in free modules. Natural l2(Z) representation has e0 eigenvector, so representation is not projective. Keep subordinate, do not continue conventional spectral counting.

Own working log: docs/drafts/pipeline/1-in-progress/irk-rh-source-loop-2026-10-15.md. Old markdown research prohibited by user; own log allowed. All owned current draft/API/search scratch removed; axiom scripts and /tmp/irk-trace-tail-lint.log retained. No live owned jobs at checkpoint. No subagents.
