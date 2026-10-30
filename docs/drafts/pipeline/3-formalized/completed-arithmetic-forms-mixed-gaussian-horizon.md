# A quantitative mixed Gaussian horizon

**ID:** completed-arithmetic-forms-mixed-gaussian-horizon  
**Stage:** Formalized in Lean 4  
**Type:** Relative form estimate and simultaneous rank exhaustion

For a real positive definite $N\times N$ matrix $G$, set $T=\operatorname{tr}(G^{-1})$.
The positive-form Cauchy–Schwarz inequality at $G^{-1}e_i$ gives
$$v_i^2\le (G^{-1})_{ii}\,v^TGv,\qquad \|v\|_2^2\le T\,v^TGv.$$
Indeed $G(G^{-1}e_i)=e_i$, so the mixed pairing is $v_i$ and the first diagonal
pairing is $(G^{-1})_{ii}$. Summing the coordinate inequalities proves the trace bound.
If every entry of a symmetric perturbation $A-G$ has absolute value at most $\epsilon$,
$$|v^T(A-G)v|\le N\epsilon\|v\|_2^2\le N\epsilon T\,v^TGv.$$
Thus $N\epsilon T<1/2$ makes $A-G/2$ positive definite, with all mixed entries retained.
The same conclusions include the empty matrix.

For the Gaussian moments $\gamma_j=16^j(1/2)_j$, let
$$G_{N,s}=[\gamma_{i+j+s}]_{i,j<N},\qquad T_{N,s}=\operatorname{tr}(G_{N,s}^{-1}).$$
The inverse is an explicit finite matrix; its determinant is the positive product
$$\det G_{N,s}=\prod_{j<N}16^{s+2j}(1/2)_s j!(s+1/2)_j.$$
Consequently its trace can also be written as the sum of diagonal cofactors divided
by this product. No source-dependent minimum or unspecified convergence radius enters $T_{N,s}$.

At $q=\pi e^{2x}\ge3$, put
$$A_{N,s}(x)=\left[\frac{(-1)^{i+j+s}f_{1,x}^{(2(i+j+s))}(0)}
 {f_1(x)^2q^{i+j+s}}\right]_{i,j<N}.$$
The all-order Gaussian bound gives the simultaneous relative estimate
$$
|v^T(A_{N,s}(x)-G_{N,s})v|
\le\frac{N T_{N,s}(2(s+2N))!D}{q}\,v^TG_{N,s}v,
\qquad D=e^{4+2e^2}(24+10e^2).
$$
The factorial is a uniform bound for every required entry order. Hence
$$q>2N T_{N,s}(2(s+2N))!D\quad\Longrightarrow\quad A_{N,s}(x)-G_{N,s}/2>0.$$

For a full signed head of dimension $R$, set $E=\lceil R/2\rceil$, $O=\lfloor R/2\rfloor$.
The parity identity gives the two blocks $(E,0)$ and $(O,1)$. Positive mass and scale
congruences preserve strictness. In particular the explicit scale
$$
Q_R=3+2D\big[E T_{E,0}(4E)!+O T_{O,1}(2+4O)!\big]
$$
satisfies
$$q(x)\ge Q_R\Longrightarrow H_R(s_x^{(1)})>0\Longrightarrow R<\kappa(x).$$
Every smaller head is a principal restriction of this positive head. An explicit center is
$\max(0,\frac12\log(Q_R/\pi))$. This is a quantitative lower boundary for the complete
mixed first-atom form. It uses the inverse of the entire Gaussian head rather than only its
diagonal. The infinite theta remainder and the integrated signed hierarchy remain distinct
source estimates.

Lean: `CompletedArithmeticForms/InverseTraceStability.lean` and
`CompletedArithmeticForms/FirstAtomMixedHorizon.lean`.
The principal declarations are `squareMass_le_inverseTrace_energy`,
`relative_error_le_inverseTrace`, `half_relative_posDef_of_inverseTrace`,
`gaussianInverseTrace_eq_cofactor_div`, `firstAtomBalancedHead_relative_error_le`,
`firstAtomBalancedHead_half_posDef_of_scale`, `firstAtomSignedHead_posDef_of_scale`,
`firstAtomFailureRank_gt_of_scale`, and `firstAtomFailureRank_gt_of_horizon`.
Their transitive axiom dependencies are exactly `propext`, `Classical.choice`, and `Quot.sound`.
