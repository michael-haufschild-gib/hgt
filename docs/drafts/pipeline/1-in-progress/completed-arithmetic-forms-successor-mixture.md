# Exact successor reserve under source addition

**ID:** completed-arithmetic-forms-successor-mixture  
**Stage:** In progress  
**Type:** Exact completion and native tail application

For a moment source $m$, let $A_m=H_N(m)$, $b_m=(m_{i+N})_{i<N}$,
$u_m=A_m^{-1}b_m$, and $S_m=m_{2N}-u_m^{\mathsf T}b_m$.
When $A_m,A_n\succ0$, put $w=u_{m+n}$. Completing both squares gives
$$S_{m+n}=S_m+S_n+
(w-u_m)^{\mathsf T}A_m(w-u_m)+
(w-u_n)^{\mathsf T}A_n(w-u_n).$$
The additional reserve is nonnegative and vanishes exactly when $u_m=u_n$.
No sign condition on either successor scalar is needed.

The single-head completion identity is formalized as
`RHTower.schurMovingMinimizer_inverse` in
`RHTower/ThetaCusp/ThetaCuspSchurMovingMinimizerVariance.lean`.
The scalar finite-mixture identity is formalized as
`HTGeometry.schurComplement_sum_eq` in `HTGeometry/QuotientFusionProjectionGenesis.lean`.
The arbitrary-rank Hankel mixture identity and actual native application are targets here.

For $2X_{N+2}\le r<t$, let $m_k=T_k(r)-T_k(t)$ and $n_k=T_k(t)$
be the complete native band and tail moment sequences. The proposed logarithmic
tail theorem makes both full rank-$(N+1)$ matrices strict. The mixture identity
would give an exact decomposition of $S_N(T(r))$ into band reserve, later-tail
reserve, and a nonnegative mismatch of their inverse-head minimizers.
In particular the integrated successor would decrease strictly with its endpoint.
