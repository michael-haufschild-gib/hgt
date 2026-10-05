# BAG growing joint unlabelled cofactor source

Let L=log N, P_N=primes<=N, and fix arbitrary complex lambda,mu. Put
s=1+lambda/L, t=1+mu/L. The complete unlabelled local product

H_N=product_(p<=N) (1-p^(-s))*(1-p^(-t))*E_0(1/p,p^(-s),p^(-t))

converges to exp(J), where
J=P(lambda)+P(mu)-P(lambda-mu)-P(mu-lambda),
P(u)=integral_0^1 (exp(u*x)-1)/x dx, extended with value u at zero.
This is pointwise in the fixed complex displacement pair; compact-uniform
parameter convergence is a separate strengthening.

The corpus exact regular-factor identity gives, once both drifts have
small real part,

H_N=(product_(p<=N) cubicPrimeFactor(p,1,lambda/L,mu/L)) *
  R_N(lambda-mu)*R_N(mu-lambda)/(R_N(lambda)*R_N(mu)),

where R_N(u)=product_(p<=N)(1-p^(-1+u/L))/(1-1/p). The finite prime
cutoffs are cofinal in the finite-subset filter. Therefore the corpus
locally uniform convergence of the regular cubic product applies along
the moving parameters (1,lambda/L,mu/L)->(1,0,0). Its limiting correction
is exactly1, by the zero-coordinate identity and continuity. The four
Euler ratios converge by ChiRamanujanMovingCofactorLimit. Their limits
are nonzero complex exponentials, so division is legitimate. Combining
the four exponents proves the stated J, with both frequency differences.

For nonzero lambda and mu, the actual weighted valuation trace with both
original growing coprime principal-character cofactors satisfies

(lambda/L)*(mu/L)*C_N(s)*C_N(t)*weightedTrace(1,lambda/L,mu/L,P_N)
  -> exp(J).

Indeed eventual positivity of Re(s),Re(t) justifies the exact weightedTrace
sum/product formula. Each cofactor is its original finite Euler product
times zeta. Their Euler factors reconstruct H_N exactly. Both punctured
zeta residues tend to1. The final statement has no extra premise; its
nonzero displacement domain is represented by Complex units.

This covers the entire unlabelled valuation cone and original cofactors.
It does not yet prove the distinguished three-label source limit, its
collision correction, compact-uniform parameter convergence, or physical
axes saving. The exact masked response assembly and compact-continuity
row argument are recorded in P1 bag-growing-near-pole-source.
