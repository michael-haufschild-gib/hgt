# Dimension-independent finite contraction payment

**ID:** completed-arithmetic-forms-geometric-contraction  
**Stage:** Formalized  
**Type:** Complete-form comparison tool

For $0\le\rho<1$, define finite matrices
$$L_{ij}=\mathbf1_{j\le i}\rho^{i-j},\qquad C=LL^{\mathsf T}.$$
Their exact masses and contraction entries are
$$\sum_jL_{ij}=\sum_{j=0}^i\rho^j,\qquad
\sum_iL_{ij}=\sum_{k=0}^{N-j-1}\rho^k,\qquad
C_{ij}=\sum_{r\le\min(i,j)}\rho^{i+j-2r}.$$
The matrix $C$ is symmetric and nonnegative entrywise. Every row sum is at most
$(1-\rho)^{-2}$, independently of dimension.

For any real source matrix $E$ with
$|E_{ij}|\le BC_{ij}w_iw_j$, $B\ge0$, and $w_i\ge0$,
$$|v^{\mathsf T}Ev|\le B(1-\rho)^{-2}\sum_iw_i^2v_i^2.$$
The proof retains both finite boundaries and uses the symmetric weighted row bound.
At $\rho=1/2$ the complete-form payment is exactly $4B$.

Lean: `CompletedArithmeticForms/GeometricContraction.lean`.
Capstones: `geometricContraction_eq_sum`, `geometricContraction_row_le`, and
`geometricContraction_form_bound`.
All three audited axiom sets contain only `propext`, `Classical.choice`, and `Quot.sound`.
