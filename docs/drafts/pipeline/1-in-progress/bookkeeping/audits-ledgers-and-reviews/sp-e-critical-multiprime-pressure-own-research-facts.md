# SP-E critical multi-prime transport pressure: own research facts

- Every finite critical forward block has the exact decomposition
  ```text
  core(p - 2 + L) - core(p - 3)
    = Σ_{p ≤ k ≤ p + L} Λ(k)/k - (log(p + L) - log(p - 1)).
  ```
  Consequently, if that block is nonpositive, its full literal prime-power mass is at most its
  polar logarithmic drift.  This closed theorem is
  `suzukiCheckpointCriticalMertensDeviationCore_nonpos_forwardBlock_vonMangoldt_budget`.

- A nonpositive forward block of the literal critical Mertens--polar source cannot spend only
  the first prime atom.  If distinct primes `p < q ≤ p + L` occur in the block, with `p ≥ 27`, then
  ```text
  log p / (2p) + log q / (2q) ≤ log (p + L) - log p,
  ```
  and therefore
  ```text
  log p / 2 + p log q / (2q) ≤ L.
  ```
  Both inequalities are unconditional finite source laws in
  `CCMFUSuzukiCriticalMultiPrimeTransportPressure.lean`.

- Whole-route consequence: growing memory is not itself a viable SP-E/CCM-FU invariant.  Its
  cancellation budget must track the *actual prime history* inside each source window.  This is
  stronger than the prior one-prime `log p / 2` lower bound and exposes the missing invariant as
  a source-executed, prime-weighted memory law.

- Limitation: no local prime-density or prime-gap hypothesis is used.  Thus this two-prime law
  does not by itself force a second prime inside every logarithmic window and does not establish
  the uniform signed lag bound.  It is a positive survivor from the locality obstruction, not an
  RH proof.
