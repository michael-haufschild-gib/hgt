# Simplicity of the confined Weil spectrum

- **Stage:** 3-formalized
- **Source:** [QIC](../../../reports/rh-current-frontier-map.md#qic)

At any positive ratio and any real eigenvalue, every nonzero confined eigenfunction has nonvanishing Laplace transform on the entire imaginary axis. At a putative boundary zero, the undamped resolvent is an admissible test. Its ordinary inner product and bare Weil pairing with the state vanish, so the eigenvalue equation forces its weighted square norm to vanish. Fourier inversion then kills the state. At frequency zero the integral is therefore injective on each real eigenspace. Orthogonal rungs have strictly increasing critical ratios. [Boundary theorem](../../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/Index/EveryConfinedEigenspaceIsSimple.lean#L28) · [Simplicity](../../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/Index/EveryConfinedEigenspaceIsSimple.lean#L102)

For every r > 0 and integer k ≥ 1, window tests realize at least k negative directions exactly when k distinct critical ratios lie strictly below r. Their null states are orthogonal in the confinement weight and span a strictly negative space at r. Window approximation preserves that space. Conversely, a window with k negative directions forces a ladder whose kth rung already lies below r. Every positive index reached or exceeded is the exact maximum on an interval of positive length. In particular, failure of RH forces such an interval of index two, even for infinitely many off-line zeros. [Exact count](../../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/Index/TheConfinedIndexCountsDistinctCriticalRatios.lean#L140) · [Index-two interval](../../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/Index/TheConfinedIndexCountsDistinctCriticalRatios.lean#L207)

The eight audited declarations use only `propext`, `Classical.choice`, and `Quot.sound`.
