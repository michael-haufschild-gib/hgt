# Frozen D4: identify the cause of continuation stalls

Question: are the two D3 stalls near kappa=.35 folds of the interaction coordinate, triple spectral zeros, or numerical failures without a nearby degeneracy? Compare a conductor-5 collision and the two successfully continued theta directions. This changes whether an apparent interaction-induced branch loss is interpreted as new zero-pair behavior or a coordinate failure.

For F=X+lambda*D+kappa*lambda^2*W, solve the two collision equations linearly in (lambda,kappa*lambda^2). Set A=X*W'-X'*W, B=D*W'-D'*W, C=X*D'-X'*D. Where A,B are nonzero, lambda(t)=-A/B and kappa(t)=B*C/A^2. Derivatives use analytic X,D,W jets. This algebraic parametrization is derivable and is not a discovery claim. It removes the failing choice of kappa as continuation coordinate.

Five intervention/control cells: theta direction (+,-), t in [31.5,33.5] and [39.5,42]; theta directions (+,+),(-,+), t in [87.6,88.6]; primitive conductor-5 direction (-,+), t in [16,18]. Use 65-point sign scans of kappa'(t), bracketed refinement, original-equation checks and explicit pole/denominator failures. Admit candidates only when 0<kappa<1, lambda>0 and sufficient positive-multiplier bound<1. No scan-completeness claim.

Discriminating measurements: F_lambda, F_tt, kappa'', lambda'(t), and their scaled residuals. F_lambda=0 with nonzero F_tt identifies a parameter degeneracy at an ordinary double zero; F_tt=0 with nonzero F_lambda instead signals a candidate triple spectral zero. Either requires higher-precision and independent-source validation. Failure to find a root does not settle the cause of a D3 stall.

Recompute moment coefficients at 70/120/180 digits, locate/refine at 50/100/160 digits. Independently integrate F,F_t,F_tt,F_lambda at each admitted candidate and at t+1/8, using the actual theta kernel or the separately verified character-theta kernel, 190 digits, cutoff 4 (16 terms for theta, 40 for conductor 5). No positivity of a Dirichlet kernel, rigorous interval remainder or formalized new theorem is claimed.

Prediction attempt: implicit-function geometry predicts which factors can make kappa a bad coordinate, but does not identify which factor fails, whether a regular fold is present in these intervals, its parameters, or whether the same behavior occurs in the arithmetic control. The generic alternatives and matrix identities serve only as inexpensive controls. A successful numerical classification is local; it establishes neither full zero ancestry nor global first collision.

Current deep/method search and earlier moment-instability results audited; no applicable theorem settles these explicit parameters. Cached coverage remains pending. Previous broad caustics/discriminant papers motivate branch geometry, not imported theorems. Full HB causal action remains unassembled; these are source-deformation and arithmetic experiments, not physical extinction.

One pod, <=14 workers, numerical library threads 1, shared 585-second cap including preparation and validation plus <=10 cleanup. First two low-height cells form the pilot; reject remaining cells if projected cost exceeds available budget. Preserve partial results. No continuation of a timed-out scan.
