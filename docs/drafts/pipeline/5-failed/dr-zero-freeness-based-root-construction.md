# DR — Zero-freeness-based root construction

- **Stage:** 5-failed; retired proof mechanism, not a refuted root criterion.
- **Failure:** Construct roots from RH/zero-freeness, then use root existence to prove RH. `xiDiscKummerRoot_of_riemannHypothesis` explicitly consumes RH; cusp roots use independently known classical zero-freeness only on that cusp.
- **Positive survivor:** Analytic 2^k-th root on the right half-plane iff every zero order is divisible by 2^k. One sufficiently high finite degree on each cofinal regional disc suffices for RH, using the unconditional O(r log r) order bound; no compatible infinite tower required.
- **Boundary:** A fixed-degree root can have zeros of divisible multiplicity. The equivalence is valid; no impossibility of an independent root construction is asserted.
- **Open replacement:** Independent arithmetic construction or divisibility law beyond the known zero-free region.
- **Proof status:** Survivor formalized in Lean; source-reviewed [L].
- **Lean:** `RHTower/RiemannTower.lean::rhLadder_iff_root`; `RHTower/XiHeightAdaptiveFiniteLadder.lean::riemannHypothesis_of_xiHeightAdaptiveDiscKummerRoots`; `RHTower/XiHeightAdaptiveFiniteLadderClosure.lean::xiHeightAdaptiveDiscKummerRoots_iff_riemannHypothesis`.
- **Constructor evidence:** `RHTower/XiHeightAdaptiveFiniteLadderClosure.lean::xiDiscKummerRoot_of_riemannHypothesis`; `RHTower/XiSymmetricZeroFreeCuspDyadicRoots.lean::exists_xi_firstTraceZeroFreeCusp_extension_of_farHalf_root`.
