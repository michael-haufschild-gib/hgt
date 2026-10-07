# Uniform double-exponential source truncation

Status: dependency-closed paper proof of the uniform source estimate; complete scratch and final installed Lean leaf audits passed without warnings. All four public capstones use only propext, Classical.choice, and Quot.sound. This is a quantitative bridge, not a positivity producer.

Write Phi=riemannKernelReal, U_L=Phi*bulkCutoff L, K=Phi autocorrelation, K_L=U_L autocorrelation, and P_c h(y)=h(y)-p_c h(y-c)-p_c h(y+c), p_c=1/(2 cosh(c/2)). Let q(L)=exp(-exp(2(L-1))). All constants below are fixed real constants independent of L, y, and c in [0,1].

## Exact statements

There is B>0 such that Phi(x)<=B exp(-exp(2|x|)) exp(-2|x|). Consequently there is C>0 with

|K_L(y)-K(y)| <= C q(L) exp(-2|y|),

|P_c^2 K_L(y)-P_c^2 K(y)| <= C q(L) exp(-2|y|) for all L,y and 0<=c<=1.

There are C>0,L0 such that for all L>=L0 and 0<=c<=1,

|archEnergy(P_c U_L)/(2*pi)-atomPairing(Lambda,P_c^2 K)| <= C q(L).

## Proof

1. The existing whole-line theta sandwich gives Phi(x)<= (101/100)*4*pi^2*exp(9u/2)*exp(-pi X), u=|x|, X=exp(2u). Put d=pi-1>0. Since exp(9u/2)<=X^4 exp(-2u), and (d X)^4/24<=exp(d X), obtain the first estimate with B=(101/100)*4*pi^2*24/d^4. Every comparison holds for all real x.

2. The bulk cutoff lies in [0,1] and equals one when |x|<=L-1. Thus D_L=U_L-Phi satisfies |D_L(x)|<=B q(L) exp(-2|x|): inside that interval it is zero; outside it is bounded by Phi(x), and exp(2|x|)>=exp(2(L-1)). This also holds for negative L.

3. Independently, existing source decay gives |Phi(x)|,|U_L(x)|<=C4 exp(-4|x|). Expand K_L-K=D_L star U_L + Phi star D_L. The existing correlation estimate for envelopes A exp(-2|x|), B exp(-4|x|) bounds each term by A B J exp(-2|y|), J=integral exp(-2|v|). The second term is the same estimate at -y after translation. All integrals are integrable by existing compact-source and envelope lemmas. Hence C=2 B C4 J suffices (enlarge by one for strict positivity).

4. The existing polar-shift estimate multiplies the envelope constant by (1+2 p_c exp(2c))^2. On [0,1], 0<p_c<=1/2 and this multiplier is <=(1+exp 2)^2. Linearity identifies the difference of polar autocorrelations with P_c^2(K_L-K). This proves uniformity without taking a limit in c or interchanging an unproved infinite sum.

5. The existing atomPairing bound sends any envelope H exp(-2|y|) to a bound 2 H sum_n |w(n)|/n^2, provided that sum converges. For w=Lambda this summability is already proved. Apply the bound to the difference; summability of each separate term follows from its envelope. The uniform polar pairing error is therefore <=C_atom q(L).

6. The proof of existing nearRadicalEnergy_le_ratio and nearRadical_ratio_le gives, for Y=exp(2(L-1))>=max(100,log(720*nearRadicalConst(S,Lambda_d)+1)), nearRadicalEnergy(L)<=exp(-Y)*integral |U_L|^2. Here S=zetaInvSqSum>=0, Lambda_d is a fixed bound on the smooth transition derivative, and the integral is uniformly bounded by existing exists_integral_norm_sq_truncatedRiemannKernel_le. Choose L0 large enough for that displayed Y threshold. The actual zero-side estimate is |W(P_c U_L,P_c U_L)|<=9 nearRadicalEnergy(L) for every c>=0. It is therefore uniform on [0,1] and <=C_zero q(L).

7. The existing exact archimedean energy split gives E(P_c U_L)/(2*pi)=Re W(P_c U_L,P_c U_L)+atomPairing(Lambda,P_c^2 K_L). Subtract the limiting pairing and use the triangle inequality and steps 5-6. This proves the final claim without RH, a zero-side sign, or a premise about other test functions.

## Attack, significance, and next obligation

Verdict BRIDGE: sharper literal-source uniformity is useful for finite exact realization. It does not constrain energies of arbitrary matched families. The natural-aperture realization requires a finite shift cutoff, exact residual repairs at every supported integer, and full normalization accounting; none is silently supplied by this theorem.

Parent audit (2026-10-07): corpus deep searches returned existing fixed-shift convergence and exponential autocorrelation bounds. Current primary abstracts inspected: Connes-Consani arXiv:2006.13771 (archimedean trace positivity); Zhu arXiv:2608.24827v2 (certified compact windows, conditional upper asymptotics and limitations); Freedman arXiv:2606.29555 (finite-core Weyl reduction, with remaining lifts explicitly open). These do not supply the literal uniform theorem or universal WP02 inequality. This limited audit does not establish literature novelty. No computation used.
