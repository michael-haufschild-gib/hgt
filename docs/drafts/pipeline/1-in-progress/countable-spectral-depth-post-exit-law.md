# Countable spectral-depth post-exit law

- **Status:** in progress
- **Target module:** `GaloisForLFunctions.RHTower.CountableSpectralDepthPostExitLaw`
- **Scientific role:** close post-exit recurrence gap in infinite pure-point spectral-depth law

## Conjecture

For every normalized nonnegative summable countable pure-point spectral
packet, every feasible finite-head water profile, and every finite integer
checkpoint \(E\), there is a strictly later survival return. If \(T\) is the
spectral-depth deadline for one sampled orbit, the later return occurs at
some
\[
  E<N\le (E+1)T,
\]
with the same full-packet survival defect and the same entropy bound on
\(\log T\).

Equivalently, the optimized spectral-depth theorem controls genuine
post-exit recurrence rather than merely a positive time that might precede
the first exit.

## Proof route

Apply the existing countable spectral-depth deadline to the phase packet
\((E+1)x\). A return after \(m>0\) steps for this rescaled packet is a return
after \(N=m(E+1)>E\) steps for the original packet. Transfer the torus
coherence predicate through associativity of the integer action, then use
the exact Hamiltonian/coherence equivalence.

## Acceptance

- direct foreground `lake env lean <file>` passes;
- axiom audit reports only `propext`, `Classical.choice`, `Quot.sound`;
- theorem includes strict post-checkpoint inequality, physical survival
  predicate, original defect, and original spectral-depth entropy bound;
- no numerical computation or finite-dimensional ambient assumption.
