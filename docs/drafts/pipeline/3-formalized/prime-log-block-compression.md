# Complete prime-block Euler comparison

Source: [`PrimeLogBlockCompression.lean`](../../../../formal/GaloisForLFunctions/RHTower/PrimeLogBlockCompression.lean).

The literal primes in `[k^4,(k+1)^4)`, `k>=2`, have count `m_k` and logarithmic mean `c_k`. Replacing the block by `m_k` copies of `exp(c_k)` preserves its zeroth and first logarithmic moments. Lean proves the full prime-power Euler-log error obeys

`|A_k(s)| <= (240 |s|² exp(2|s|)+30) k^(1-4 Re(s))`.

The complete error sum is holomorphic on `Re(s)>1/2`. Actual finite Euler quotients converge to its negative exponential, a holomorphic nonzero function. All fifteen public theorems are unconditional apart from displayed numerical domain restrictions; no RH or source-cancellation premise, added axiom, or computational certificate is used.

This is a `[BRIDGE]`: an all-scale comparison estimate. It does not exclude zeros. The [research card](../1-in-progress/prime-log-block-compression.md) supplies the paper continuation argument, novelty limits, and remaining source problem. The separate infinite compressed Euler product and its zero-preservation identification are not claimed as Lean theorems.

Validation: scratch and source `lake env lean` checks pass; named `lake build GaloisForLFunctions.RHTower.PrimeLogBlockCompression` passes (6.6 seconds); module is wired into `RHTower.lean`. All fifteen public theorems were checked by `#print axioms` in `/tmp/rh_prime_block_axioms.lean`; each depends only on `propext`, `Classical.choice`, and `Quot.sound`. Refreshed formal index and `scripts/formal_tools.py lint` pass. No full or umbrella build was run. No owned Lean process remains.
