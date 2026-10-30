# Polynomial rank payment for the complete native form

**ID:** completed-arithmetic-forms-native-hermite-rank  
**Stage:** Formalized  
**Type:** Complete-source coercivity estimate

For $q=\pi e^{2x}$, put
$$D=50e\exp(2e),\qquad A=27e^{3\pi}/399,\qquad
P_N=N\bigl(De^2(N+1)(N+2)^2+Ae^8\bigr).$$
Let $m_{2k}=\sigma_k^{\rm native}(x)$ and $m_{2k+1}=0$, with the exact
first-atom mass and Gaussian length normalization. Let $\mathcal G_N$ be the
full signed Gaussian moment head. On $q\ge16(N+2)^2$,
$$|v^{\mathsf T}([m_{i+j}]_{i,j<N}-\mathcal G_N)v|
\le\frac{P_N}{q}v^{\mathsf T}\mathcal G_Nv.$$
If also $q>2P_N$, then $[m_{i+j}]-\mathcal G_N/2$ is positive definite.

The first-atom Hermite entries have error
$De^2(N+1)(N+2)^2\sqrt{8^ii!8^jj!}/q$.
The complete native remainder has absolute entry error $Ae^8/q$ in the same
coordinates. Each Gaussian norm $8^ii!$ is at least one. The weighted-entry
bound pays the full form with one dimension factor. The exact monic Hermite
congruence has bijective transpose action, preserving the relative cost when
returning to the original complete source coordinates.

Lean: `CompletedArithmeticForms/NativeHermiteHorizon.lean`.
Capstones: `gaussianFullHead_posDef`, `nativeHermiteHead_relative_error_le`,
`nativeBalancedFullHead_polynomial_rank_error_le`, and
`nativeBalancedFullHead_half_posDef_of_polynomial_rank_scale`.
Each audited axiom set contains only `propext`, `Classical.choice`, and `Quot.sound`.

The exact principal embedding $i\mapsto2i+s$ transfers this bound to every shifted
rank-$n$ head at dimension $M=2n+s$. The exact successor at rank $n$ uses
$M=2(n+1)+s$ and satisfies
$$|S_n^{\rm native}-C_{n,s}|\le(P_M/q)C_{n,s},
\qquad q\ge16(M+2)^2,\quad q>P_M.$$
For $S_M=16(M+2)^2+2P_M$ and $x\ge\max(0,\tfrac12\log(S_M/\pi))$,
$$C_{n,s}/2<S_n^{\rm native}<3C_{n,s}/2.$$
Lean: `CompletedArithmeticForms/PolynomialRankHorizon.lean`,
`nativeBalancedHead_polynomial_rank_error_le`,
`nativeBalancedSuccessor_polynomial_rank_error_le`, and
`nativeBalancedSuccessor_half_bounds_of_polynomial_rank_horizon`.
Every audited axiom set is standard.

The literal physical shifted head is $q^sD H_n(\sigma_s)D$ with
$D_{ii}=\theta_1(x)q^i$. Both parity blocks of full signed rank $N$ fit in
dimension $N+1$. Consequently $q\ge S_{N+1}$ makes the full physical head strict.
For $C=16+2De^2+2Ae^8$, the polynomial scale satisfies $S_M\le C(M+2)^4$.
The resulting source-center bound is
$$x\ge\max(0,\tfrac12\log(C/\pi)+2\log(N+3)).$$
For the exact shifted successor, replace $N+1$ by $2(n+1)+s$ in this envelope.
Lean: `CompletedArithmeticForms/NativePhysicalRankHorizon.lean`,
`nativePolynomialRankScale_le_quartic`,
`nativeSignedHead_posDef_of_logarithmic_rank_horizon`, and
`nativeBalancedSuccessor_half_bounds_of_logarithmic_rank_horizon`.
All five audited capstones have only the three standard axioms.
