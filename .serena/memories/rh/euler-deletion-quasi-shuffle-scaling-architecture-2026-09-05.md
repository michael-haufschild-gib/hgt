# Euler-deletion quasi-shuffle scaling architecture (2026-09-05)

Current provisionally admitted architecture: chronological deletion-signature refinement tower.

- For modulus P=q+1, canonical deletion jump word is (1,…,1,−q), equal to the literal coefficient `a_P(n)=1-P[P|n]` on one full block.
- Finite exact core: level-one sum is 0; diagonal quasi-shuffle bracket (sum of squared jumps) is q(q+1)=P(P−1).
- For a finite complex word, `H₂=Σ_{i<j}x_i conjugate(x_j)` satisfies `|Σx|²=Q+2 Re H₂`. Closed-source chronological P-fold replication scales `H₂` by P; Euler amplitude P^(1−s) scales it by P^(2−2σ). A closed word with Q≠0 has H₂≠0, so coherence of actual chronological second levels forces σ=1/2.
- Lean: `RHTower/EulerDeletionQuasiShuffleScaling.lean` proves block/coefficient identification, actual chronological deletion word, level-one and bracket formulas, Hermitian quasi-shuffle identity, concatenation cross term, closed-source replication, amplitude scaling, unique half exponent, specialized deletion-word coherence implication, and premise-free capstone `eulerDeletionSignatureScaling_closed`. Imported by `RHTower.lean`; direct check, targeted build, and axiom audit pass. Current global lint is blocked by an unrelated concurrently added unreachable Brizard module.
- Open producer QSR: simultaneous level-one closure of all Euler-deletion paths at a zeta zero must force chronological replication–Euler-dilation coherence for at least one nonzero bracket. This is not proved.
- Kill gates:
  - closed endpoint alone never implies higher-signature coherence;
  - QSR cannot assume equality of P and P^(2−2σ);
  - infinite iterated sums need cutoff-independent cofinal renormalization fixed before the zero;
  - square summability for σ>1/2 is domain information, not contradiction;
  - no FE/1−s, Gamma, theta, spectral, Möbius, Weil positivity.
- Literature/corpus: iterated-sums/quasi-shuffle signatures and tree-like signature theory are known; bounded searches found no exact Euler-deletion × chronological replication × Euler-amplitude refinement synthesis. Nearby `EulerSquarefreeWickQuadraticCommonRefinementDescent` inserts half-density/reflection and is RH-equivalent; nearby `CycleDeletionShiftedHankelRankOneUniversalityLaw` is banned shifted-Hankel shape blindness. Neither is usable or the same mechanism. This is not a novelty certificate.
- Prior multiplication-fibre route retired: `mem:rh/coprime-deletion-multiplication-fibre-architecture-2026-09-05`.
- Main card: `docs/drafts/pipeline/1-in-progress/rh-corpus-architecture-audit-2026-09-05.md`.
- STATUS facts: F680, CANNOT-306, MUST-215.

Next: QSR-2. Define weighted finite deletion prefixes and prove the exact Euler dilation/interleaving identity, then prove cutoff convergence on Re(s)>1/2 using bounded periodic partial sums. Generic finite chronological algebra is complete. Do not touch zeta-zero coherence until the weighted finite dilation identity is source-complete.
