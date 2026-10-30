# Exact successor reserve under source addition

**ID:** completed-arithmetic-forms-successor-mixture  
**Stage:** Formalized in Lean 4  
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
The arbitrary-rank Hankel mixture identity is `successorSchur_add_eq` in
`CompletedArithmeticForms/SuccessorMixture.lean`.

For $2X_{N+2}\le r<t$, let $m_k=T_k(r)-T_k(t)$ and $n_k=T_k(t)$
be the complete native band and tail moment sequences. The logarithmic
tail theorem makes both full rank-$(N+1)$ matrices strict. The mixture identity
gives an exact decomposition of $S_N(T(r))$ into band reserve, later-tail
reserve, and a nonnegative mismatch of their inverse-head minimizers.
The integrated successor decreases strictly with its endpoint.

For every $w$, the complete monic test $v=(-w,1)$ satisfies
$$v^{\mathsf T}H_{N+1}(m)v
=S_m+(w-u_m)^{\mathsf T}A_m(w-u_m).$$
Thus $(-u_m,1)$ attains the exact successor and every other monic direction
pays its discrepancy in the original head norm. Lean:
`successor_monic_energy_eq`, `successorTestVector_energy_eq`,
`successorMixtureVariance_eq_zero_iff`,
`nativeTailSuccessor_band_decomposition`, and
`nativeTailSuccessor_strictAnti_of_quadratic_rank_horizon`.
All six audited capstones have only `propext`, `Classical.choice`, and `Quot.sound`.
