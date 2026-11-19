# Separate conductor energies on arbitrary interleavings

For actual signed conductor multiplicities $u_i,v_i$ through $N$, let $U^2=\sum_i r_i^2u_i^2$, $V^2=\sum_i r_i^2v_i^2$ with $r_i>0$ nondecreasing. For each nonnegative quotient price $w$, put $A_N^2=\sum_{k=1}^N1/r_k^2$ and $B_N^2=\sum_{k=1}^N(w_k/r_k)^2$. The combined positive quotient variation and half the integrated absolute jet satisfy
$$
\sum_{k=1}^N w_k|C_k|+\frac12\int_0^1|J(x)|\,dx
\le (4A_NB_N+A_N^2)UV.
$$
When both scalar square sums converge, one constant works at all cutoffs. The two supports may overlap anywhere and the coefficients may have either sign.

Indeed, $C_k=T_k-T_{k+1}$, where $T_k=\sum_i(u_iv_{ki}+v_i u_{ki})$. For $i\ge1$ and $s=0,1$, the map $k\mapsto(k+s)i$ is injective, and its conductor weight is at least $r_k$. Cauchy–Schwarz bounds $\sum_k w_k|v_{(k+s)i}|$ by $B_NV$. A second Cauchy–Schwarz bounds $\sum_i|u_i|$ by $A_NU$. Summing both orientations at both shifts gives $4A_NB_NUV$. Each of the two real jet monomials is at most one on $[0,1]$, giving the remaining $A_N^2UV$.

Lean declarations include `directedMultipleVariation_le`, `twoSided_variation_separate`, `mixedJetSection_le_total_variations`, `interleaved_joint_separate` and `interleaved_joint_uniform`. [Formal proof](../../../../formal/GaloisForLFunctions/SignedArithmeticCorrespondences/SeparateConductorEnergiesOnInterleavingSupports.lean)


For $1/r\in\ell^2$, the converse holds. Against $u=\delta_1$, the cells are $2v_1-v_2,v_2-v_3,\ldots,v_N$, with $v_{N+1}=0$ in the first entry when $N=1$. For $v_k=(-1)^km_k$, every $|C_k|\ge m_k$. Test nonnegative integers $m_k=\lfloor M w_k/r_k^2\rfloor$. Writing $T=\sum_{k=1}^N(w_k/r_k)^2$, the energy bound implies $MT\le Cr_1M\sqrt T+\sum_{k=1}^Nw_k$. Taking $M$ arbitrarily large at fixed $N$ gives $T\le C^2r_1^2$. Lean proves the integral tests and the equivalence in `anchored_price_test` and `interleaved_weight_test_iff`. [Converse proof](../../../../formal/GaloisForLFunctions/SignedArithmeticCorrespondences/TheSharpWeightTestOnOneConductor.lean)
