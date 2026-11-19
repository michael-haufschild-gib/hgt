# Every confined state has an absolute zero-mode expansion

- **Stage:** 3-formalized
- **Source:** [QIC](../../../reports/rh-current-frontier-map.md#qic)

Let $F$ be a confined null state at a positive ratio $R$. For each centered zeta zero $z$, counted with multiplicity, put $c_z=-a(R)^{-1}LF(z)A(z-8)$, where $A(w)=((w+9)(w+10)(w+11)(w+12))^{-1}$. Then
$$
\sum_z |c_z|\,|z|^2<\infty,\qquad
F_{\rm avg}(t)=\sum_{\Re z>0}c_z e^{(z-8)t}+O(e^{-8t})\quad(t>0).
$$
The exact sum over all zeros equals the averaged state minus its four explicit exponential terms. These statements include infinite off-line divisors. [Absolute coefficients](../../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/Modes/EveryConfinedStateHasAnAbsoluteZeroModeExpansion.lean#L52) · [Exact expansion](../../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/Modes/EveryConfinedStateHasAnAbsoluteZeroModeExpansion.lean#L332) · [Right-zero sum](../../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/Modes/EveryConfinedStateHasAnAbsoluteZeroModeExpansion.lean#L346)

Since $\Re z>-1/2$, each $|z+j|$ for $1\leq j\leq4$ dominates $|z|$. The Laplace transform is bounded on the zero strip and $\sum_z |z|^{-2}<\infty$. For the transform identity, take the subtracted Cauchy formula at $w,-9,-10,-11,-12$. The partial-fraction weights of $A$ cancel the common subtraction before summation. Laplace inversion gives the pointwise expansion. The left and on-line terms satisfy the stated remainder bound by absolute convergence. [Cancellation of the subtraction](../../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/Modes/EveryConfinedStateHasAnAbsoluteZeroModeExpansion.lean#L95)

The five audited declarations use only `propext`, `Classical.choice`, and `Quot.sound`.
