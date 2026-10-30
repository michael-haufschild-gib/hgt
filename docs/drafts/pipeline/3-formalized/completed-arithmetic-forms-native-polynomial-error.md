# Polynomial relative error of the complete native source

**ID:** completed-arithmetic-forms-native-polynomial-error  
**Stage:** Formalized  
**Type:** Complete theta source estimate

Let $q=\pi e^{2x}$, $\gamma_k=16^k(1/2)_k$, and
$A=27e^{3\pi}/399$. The literal infinite-source estimate is
$$|\sigma_k-\sigma_k^{(1)}|\le A\,24^{2k}q^ke^{-3q},
\qquad q\ge2k+6.$$
Lean: `RHTower.abs_thetaCuspNativeScaledEvenJet_sub_first_le_effective` and
`RHTower.regimeOneLikelihoodScale_eq`.

The physical first atom obeys
$$|\sigma_k^{(1)}-\gamma_k|\le 3k^2\gamma_k/q,
\qquad q\ge\max(3,k^2).$$
Lean: `CompletedArithmeticForms.firstAtomScaledEvenJet_quadratic_error_le`.

The complete-source estimate is
$$|\sigma_k-\gamma_k|\le(3k^2+A)\gamma_k/q,
\qquad q\ge\max(k^2,8k,2k+6).$$
Lean: `nativeScaledEvenJet_quadratic_relative_error_le` and
`nativeScaledEvenJet_quadratic_relative_error_le_through` in
`CompletedArithmeticForms/NativePolynomialHorizon.lean`.
The exact payment uses
$q^ke^{-q}\le k!$, $8^kk!\le\gamma_k$, and $72^k\le e^{8k}$.
The two remaining exponential factors pay the order exponential and one factor of $q$.
Every atom of the source remains present.

For a positive comparison matrix $G$, the natural mixed-form cost is
$N\sum_iG_{ii}(G^{-1})_{ii}$ times the relative entry error.
This weights each inverse-coordinate cost by its own Gaussian variance.
Lean: `CompletedArithmeticForms/WeightedInverseStability.lean`,
`relative_entry_error_le_varianceInverseCost`.
The exact weighted cost is the variance-weighted cofactor sum divided by the
complete determinant and is at least the matrix dimension.
For $G_{N,s}=[\gamma_{i+j+s}]$, $V_{N,s}=\sum_iG_{ii}(G^{-1})_{ii}$,
$L=s+2N$, and $B_{N,s}=NV_{N,s}(3L^2+A)$, the actual complete native form has
relative error at most $B_{N,s}/q$ on $q\ge\max(L^2,8L,2L+6)$.
If $q>2B_{N,s}$, the strict half-Gamma form remains.
Its exact Schur successor has relative error at most $B_{N+1,s}/q$.
The scale $\max(L'^2,8L',2L'+6)+2B_{N+1,s}$, $L'=s+2(N+1)$,
places the successor strictly between one half and three halves of its Gamma reserve.

Lean: `CompletedArithmeticForms/NativeVarianceHorizon.lean`,
`nativeBalancedHead_polynomial_relative_error_le`,
`nativeBalancedHead_half_posDef_of_polynomial_scale`, and
`nativeBalancedSuccessor_half_bounds_of_polynomial_horizon`.
All audited capstones depend transitively only on `propext`, `Classical.choice`, and `Quot.sound`.
The variance cost remains rank dependent; a polynomial mixed-rank horizon is a separate estimate.
