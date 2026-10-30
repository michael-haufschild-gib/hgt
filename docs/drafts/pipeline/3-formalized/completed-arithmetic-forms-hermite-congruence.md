# Exact Hermite congruence for complete moment sources

**ID:** completed-arithmetic-forms-hermite-congruence  
**Stage:** Formalized  
**Type:** Complete-form source bridge

For $g(z)=e^{-4z^2}$, define
$$T_{nk}=\binom nk g^{(n-k)}(0).$$
These coefficients are real. Each finite matrix $T_N$ is lower triangular with
diagonal one and determinant one. Its transpose action is bijective.

For every entire function $F$,
$$\partial_z^i\partial_w^j\bigl(g(z)g(w)F(z+w)\bigr)_{(0,0)}
=\sum_{a\le i}\sum_{b\le j}T_{ia}T_{jb}F^{(a+b)}(0).$$
Consequently the complete real mixed head equals
$$H_{\rm Hermite}=T_N[\Re F^{(i+j)}(0)]T_N^{\mathsf T}.$$
For $F=e^{4z^2}$ this is exactly $\operatorname{diag}(8^ii!)$.
For the literal normalized first theta atom it is exactly the physical kernel
$e^{-4z^2-4w^2}F_q(z+w)$.

The unit-circle Cauchy estimate gives $|g^{(m)}(0)|\le m!e^4$.
Since $\binom nk(n-k)!\le n!$, every coefficient satisfies $|T_{nk}|\le n!e^4$.
This bound retains all lower coefficients when transporting an exponentially small source tail.

Lean: `CompletedArithmeticForms/HermiteJetCongruence.lean`.
Capstones: `mixedKernelJet_wickSourceKernel`, `realWickJetMatrix_eq_congruence`,
`realWickJetMatrix_gaussian`, `hermiteJetMatrix_det`,
`hermiteJetMatrix_transpose_injective`, `hermiteJetMatrix_transpose_surjective`,
and `hermiteJetCoefficient_abs_le`.
Each audited theorem depends only on `propext`, `Classical.choice`, and `Quot.sound`.

For $q\ge4(N+2)^2$, put $C_N=50e^{3}\exp(2e)(N+1)(N+2)^2$.
The literal first-atom Hermite head satisfies
$$|v^{\mathsf T}(H^{(1)}_{\rm Hermite}-\operatorname{diag}(8^ii!))v|
\le \frac{NC_N}{q}\sum_{i<N}8^ii!v_i^2.$$
The entry bound is $C_N\sqrt{8^ii!8^jj!}/q$ through degrees $i,j\le N$.
Lean: `CompletedArithmeticForms/HermiteSourceBound.lean`,
`firstAtomWickError_normalized_jet_le`, `firstAtomHermiteError_eq`, and
`firstAtomHermiteHead_relative_error_le`; all three axiom sets are standard.
