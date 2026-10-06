# BAG uniform curved-frequency strip energy

01ax. Paper and Lean proof complete. Source:
`ChiCubicCurvedFrequencyEnergy.lean`, public
`RHTower.BAGTrace.bagCubicCurvedFrequency_uniform_strip_energy`.
For each 0<=s<3/2, one positive constant bounds the integral over the ENTIRE
strip |lambda*a|<=1/4 of
 (1+|a|+|b|)^(2s)/[(1+|a|)^2*(1+|b|)^2*(1+|a*v+b*u+lambda*a*b|)^2],
uniformly for every real lambda and u,v in[1,2]. Integrability is included.
Zero curvature gives the full stationary plane. Original lambda=1/N low
rectangle is contained. Only structural domain parameters; no analytic
bound, uniformity, cancellation or RH assumption.

Put A=1+|a|, B=1+|b|, C=1+|D|. The strip gives U=u+lambda*a in[3/4,9/4].
Triangle inequalities give A<=3(B+C), B<=3(A+C). Partition by the smallest
size. Each case is bounded by a constant times one of A^-2 B^(2s-4),
A^(2s-4) B^-2, or A^(2s-4) C^-2. The first two integrate as products.
For the third, affine substitution b->a*v+U*b has Jacobian<=4/3.
The formal full-plane majorant clamps U below by3/4; it agrees on the
strip. Fubini and product integrability finish the bound because 2s-4<-1.
The proof uses no numerical computation.

This controls the moving curved concentration set at Sobolev orders
strictly ABOVE ONE, the central low-frequency ingredient for the actual
physical profile. It is not the physical regularity theorem: exact
multiplier transfer, selected cutoff derivative budgets, high frequencies,
Minkowski/Plancherel and positive-log-map tails remain open.

Audits: scratch47746 PASS; production4476 emptyPASS using
`lake --old env lean GaloisForLFunctions/RHTower/ChiCubicCurvedFrequencyEnergy.lean -o .lake/build/lib/lean/GaloisForLFunctions/RHTower/ChiCubicCurvedFrequencyEnergy.olean`.
Final axiom91780 PASS, standard3 only. Index18632 PASS; umbrellaonce.
Lint1720 terminal1: six unrelated unreachable modules,174warnings;
no owned error. No full build, resource-limit override or new axiom.
Prior corpus search86162: nonpartial66007files,generation1248594/current1248595,
noerrors,refreshincomplete; all20candidate+20source statements inspected.
