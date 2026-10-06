# BAG signed full-plane transfer of the complete growing source

01ax. Paper proof and production Lean audit complete. Scratch30915 and
production50199 PASS; final axiom85157 standard3 only. Index8884 PASS.
Lint39568 terminal1: three unrelated HTGeometry unreachable modules;
no owned error. See P3 bag-signed-source-sector-transfer.

For every fixed rho1,rho2>0 and every FIXED Schwartz Phi on R²,

  (1/logN)*integral_R² Z_N(t1,t2)*Phi(t1,t2) -> 0,

where Z_N is the actual criticalCompletedConeEuler at primes<=N and lines
1+rho_i/logN+i*t_i. Both original growing coprime cofactors, both label
exclusions, the allowed first/second collision and all signed valuation
sectors are retained. No uniformity, nonvanishing or cancellation premise.

Write L=logN. Partition the plane into |t1|<=|t2| and |t2|<|t1|. In the
first sector substitute t1=x/L,t2=y. The normalized integrand becomes

  1_[|x/L|<=|y|]*Z_N(x/L,y)*Phi(x/L,y)/L².

The U3 axes envelope bounds it by C*T^54*|Phi(x/L,y)| times two scaled
inverse-square profiles. On this sector the second is bounded by the
first, namely (1+|x|)^-2. Schwartz decay cancels T^54 and leaves the
N-independent integrable majorant K*(1+|x|)^-2*(1+|y|)^-2. The formal proof
uses order58 and simultaneously obtains full unscaled integrability.

For y!=0 the indicator eventually equals1. The actual M1 source theorem
gives the limit exp(-2gamma)*G(rho1+i*x)*Phi(0,y). The line y=0 is null.
Dominated convergence therefore gives the integral of this separated
limit. M2 proves integrability and ZERO signed vertical integral of G,
so the sector limit vanishes. Exact scalar substitution/Fubini supplies
the original normalized sector integral.

Every local weighted Euler expression is symmetric in its two nomes.
Exchanging the first two labels preserves both masks and the allowed
collision; both cofactor factors commute. Thus the original complete
source is exactly symmetric under simultaneous exchange of the two lines.
Apply the same proof to the STRICT second sector with exchanged rho_i and
the swapped Schwartz test. The sectors partition the entire plane exactly;
their integrals add, proving the full result. No separate joint-box estimate
or compact-uniform source remainder is required for fixed tests.

Remaining hard gap: the actual normalized physical profile is N-dependent.
It cannot be substituted into this fixed-test theorem. Its selected cutoff
derivative budgets, height-averaged fractional regularity and line tails
remain under investigation (P1 bag-physical-height-averaging-transfer).
No physical o(N/log²N) saving or RH conclusion has been proved here.
