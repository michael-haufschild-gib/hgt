# SP-E critical variation source: own research facts

- The RH-equivalent critical variation action has the exact source representation
  ```text
  action(H) = M(0) W_H(0)
    + Σ_{j < eventIndex(H)-2}
        (Λ(j+3)/(j+3) - (log(j+3)-log(j+2))) W_H(j).
  ```
  Here `M` is the literal critical Mertens--polar remainder and `W_H` is its literal triangular
  multiplier.  This is closed as
  `suzukiCheckpointCriticalMertensDeviationVariationAction_eq_weightedPrimePolar` in
  `CCMFUSuzukiCriticalRemainderVariation.lean`.

- Whole-route consequence: SP-E's unresolved gate is neither an endpoint estimate nor an
  unsigned variation estimate.  It is uniform control of this signed, source-executed,
  multiplier-weighted prime--polar history.  Replacing it by an absolute-value bound destroys
  the cancellation that the action encodes.

- The bridge and a scratch reproduction were checked with `lake env lean`.  Its axiom audit
  reports only `propext`, `Classical.choice`, and `Quot.sound`.

- Limitation: the identity identifies the hard global invariant; it does not prove its uniform
  bound and therefore does not close the RH equivalence.
