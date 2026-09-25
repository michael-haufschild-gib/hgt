# Frozen family D2: discriminate interaction from root-solver bias

Question: does D1's apparent gap change survive a one-dimensional discriminant method, or was it caused by the two-variable solver's unequal failures? Restrict to seed gaps 4,7,24 and diagonal directions (+,+),(+,-),(-,+), additive and product models. Do not complete or extend D1's abandoned scan.

Use the exact same theta-source deformation definitions. Let X=Xi(t), D=a*H1(t)+b*H2(t), W=interaction*a*b*H12(t). Derive A=X W'-X'W, B=D W'-D'W, C=X D'-X'D. For interaction present, scan R=A^2-B*C; recover lambda=-A/B and check F=F_t=0. For interaction absent, scan C and recover lambda=-X/D. This avoids a two-variable Newton guess. Degenerate denominators and residual failures stay explicit. A finite sign scan can miss even-order discriminant roots; it is not a proof of completeness.

Multiple experiments: 18 model/direction/gap cells; 33 equally spaced points per gap followed by bracketed root refinement; all admissible discovered roots at 50 digits; fresh moment coefficient solves and refinement at 100/160 digits; direct theta-kernel Fourier and derivative integration for selected lowest-threshold candidates. Compare solver methods, source interaction switch, direction and gap. Direct source integral uses the corpus kernel, not a sum of shifted zeta functions.

Falsifier for the apparent-pair-change interpretation: the alternative method recovers missing low-threshold roots in both models with the same responsible gap. An interaction effect remains a candidate only if stable after refinement and source-integral validation. No claim about the true first collision outside these three basins.

Prediction attempt: generic positive-kernel/moment insufficiency is known and excluded as discovery. D1's solver failures prevent predicting whether the apparent gap change is physical in this surrogate family. The elimination identity itself is a derived bridge/implementation check, not the discovery target.

Frozen validation targets: compare all original collision equations scaled by exp(-pi*t/4)*(1+t^2)^(7/8). Increasing precision must stabilize lambda and t. Direct source quadrature uses [0,3], 16 theta summands, 190 digits, subdivided integration; increasing summands/cutoff is an error check where needed. No rigorous interval remainder claim. Missing HB corrections and boundaries remain unknown.

Admission: D1 report and current deep/method search audited; use the same source provenance. Discriminant viewpoint motivated by arXiv:2605.27342v1; mathematical elimination derived here. User increased the cap before execution: entire family including preparation, scans and validation <=585 seconds plus <=10 cleanup, 14 workers. Preserve partial results; no one-hour continuation by sharding.
