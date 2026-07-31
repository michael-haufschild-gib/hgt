# Countable spectral-depth post-exit law

- **Status:** formalized
- **Lean module:** `GaloisForLFunctions.RHTower.CountableSpectralDepthPostExitLaw`
- **Scientific role:** close post-exit recurrence gap in infinite pure-point spectral-depth law

## Result

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

The theorem is stronger than a post-exit implication: every finite
checkpoint is followed by a return. Its exit specialization preserves the
exit certificate and produces a strictly later return.

## Proof

Apply the existing countable spectral-depth deadline to the phase packet
\((E+1)x\). A return after \(m>0\) steps for this rescaled packet is a return
after \(N=m(E+1)>E\) steps for the original packet. Transfer the torus
coherence predicate through associativity of the integer action, then use
the exact Hamiltonian/coherence equivalence.

## Formal declarations

- `exists_countableSpectralDepth_postCheckpointReturn`
- `exists_countableSpectralDepth_postExitReturn`

## Verification

Direct foreground `lake env lean` compilation passed. Axiom audit reports
only `propext`, `Classical.choice`, and `Quot.sound`.

The theorem includes the strict post-checkpoint inequality, physical
survival predicate, original full-packet defect, and original
spectral-depth entropy bound. It makes no finite-dimensional ambient
assumption and uses no numerical computation.
