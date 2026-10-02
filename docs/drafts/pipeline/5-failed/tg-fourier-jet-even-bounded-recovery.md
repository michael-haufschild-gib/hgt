# TG-C9.5: bounded recovery fails on the literal even prime core

- **ID:** TG-C9.5-20261002-01a0
- **Stage:** 5-failed
- **Retired candidate:** bounded ambient recovery of the first input from the two physical outputs.
- **Lean:** `PrimeBurnolFourierJetClosure`, `PrimeBurnolFourierJetPrimeCore`.

## Exact obstruction

For every prime p there is no continuous linear map R from physical L2×L2 to physical L2
such that `R(output)=firstInput` on the actual finite prime-depth Fourier–jet graph.
The Euler amplitudes and the original even source columns are retained. This is stronger
than the earlier full-carrier obstruction: it applies to the literal arithmetic core.

The separate even-source proof uses the actual parity theorem
`h_n(-x)=(-1)^n h_n(x)`. Let P be the physical even projection and suppose R recovers
the first coordinate on even maximal-domain source pairs. Define
`T=F^(-1) R (0,-(8π²)^(-1) F P·)`.
Even Hermite tests admit the exact cancelling pair `(Fφ,-φ)`; odd Hermite-tail outputs
are killed by P. Therefore `T* h_0` annihilates every weak Hermite-tail test. The audited
tail theorem forces it to vanish. Recovery on the even Gaussian contradicts its nonzero
norm. No odd source vector is inserted into the even carrier.

A recovery identity on the finite core is closed because R is continuous. C9.4's exact
graph-core equality therefore extends it to the even maximal-domain source, giving the
contradiction above. Ordinary L2 density is not used as a substitute for graph density.

## Positive survivor and status

The actual closed Fourier–jet graph still has injective input and output projections.
Every single prime's literal multiplication graph core completes to the entire even
maximal graph, and its Fourier–jet source completes to the even maximal source graph.
These are exact uniqueness and arithmetic-domain results. The survivor has a complete
paper proof and audited Lean formalization in
`../3-formalized/tg-fourier-jet-closed-graph.md` and
`../3-formalized/tg-fourier-jet-prime-graph-core.md`.

Both modified production leaves pass `lake --old env lean` with matching oleans.
All ten public theorems across both leaves pass a separate axiom audit, using only
`propext`, `Classical.choice`, `Quot.sound`. Umbrella wired; no full build.
Final lint reports twelve unrelated unwired leaves, recorded in the working log.

## Surviving hard question

This theorem uses only the physical output norm. It does not prove that the original
neutral projection is unbounded for the stronger norm retaining both input and output.
That distinct source-projection question is C9.6. Gamma–Xi identification, Hardy-index
transfer, and the sub-unit producer remain open. No RH conclusion follows.
