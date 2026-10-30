# Uniform mixed-entry payment after a complete Weil prefix

**ID:** completed-arithmetic-forms-weil-prefix-payment  
**Stage:** In progress  
**Type:** Quantitative actual-source Schur transfer

Let $A,B,D$ be the prefix, mixed, and tail blocks of the literal complete
Weil matrix for the explicit trans-Metzler plateau, at horizon $N$ and overlap $c$.
The exact prefix identity replaces overlap by $cM/N$ without changing atom width.
The corpus endpoint energy exceeds $1/20$, and uniform spectral control through
touching therefore gives one horizon beyond which
$$A\succeq\frac1{20}I\qquad(0<c,\ M\le N,\ cM\le N).$$
Its inverse consequently obeys
$$0\le b^{\mathsf T}A^{-1}b\le20\|b\|^2.$$
For the actual mixed block, the proposed quantitative completion is
$$0\le y^{\mathsf T}B^{\mathsf T}A^{-1}By\le20\|By\|^2,
\qquad D-20B^{\mathsf T}B\preceq D-B^{\mathsf T}A^{-1}B\preceq D.$$
This retains all signed prime, Gamma, and polar mixed entries. At overlap $3/2$
and horizon $3K$, the prefix has size $2K$ and the residual has size $K$.
The constant is independent of both sizes. Positivity still requires an
actual lower bound for the remaining tail relative to this coupling cost.
The displayed source payment requires Lean formalization.
