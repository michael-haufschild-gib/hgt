# Route P — labelled Gamma-valuation primitive profile: facts

- **LEAN FACT.** `GammaValuationSchurLabelledProfile.lean` constructs the literal ordered
  profile
  ```text
  (depth e, prime index n) |-> (n + 1) (a(e,n) - a(e,n+1)).
  ```
  It is globally summable for every height-Köthe source vector.  The proof spends only the first
  Deninger height seminorm and pays both endpoints of each adjacent difference.

- **LEAN FACT.** This profile vanishes iff every literal prime-power coordinate of the source
  vanishes.  The substantive step is that a zero difference profile would make each prime-index
  slice constant, while source summability forces that constant to be zero.

- **LEAN FACT.** The pre-existing weak Gamma-valuation Schur kernel factors through the new
  profile only after summing its prime-index component at each fixed depth.  Thus its scalar
  per-depth aggregate, not the cumulative adjacent primitive itself, is the exact locus of prime
  label loss.

- **WHOLE-ROUTE CONSEQUENCE.** Route P now has an explicit source-native, infinite,
  label-preserving object before scalarization.  Any successful source-to-Hellinger/Calderón
  boundary map must act on this profile (or retain strictly more data) before per-depth
  aggregation.  A scalar weak-kernel landing cannot satisfy the labelled mixed-term gate.

- **OPEN HARD GATE.** Construct and prove graph-closed a coefficient-faithful transport of this
  profile into the actual Gamma/co-Poisson Hodge defect domain, with finite tail energy before
  scalar orientation.  No such source-to-domain transport, and no RH proof, has been obtained.
