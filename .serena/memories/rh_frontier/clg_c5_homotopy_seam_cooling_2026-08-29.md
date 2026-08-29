# CLG C5 homotopy seam cooling (2026-08-29)

Exact seam algebra for the affine likelihood homotopy found the first nonzero M''' coefficient at order t^7:
(8 F2^3/3) [9(2xy-z) + 2(x+r)(y-s)^2/(-a2)],
x=-F3/F2, y=F4/F2, z=-F5/F2.
Thus the new source gate is F2*F5 - 2*F3*F4 > 0, equivalently (F4/F2^2)' > 0.

Sufficient split:
1. 3*A*F2 < -F3.
2. -F5 < 6*A*F4, equivalently (exp(3A)*F4)' > 0.

(1) is now a closed Lean theorem in ThetaCuspFixedActionC5LikelihoodLiftReduction.lean:
three_mul_scale_mul_thetaCuspLikelihoodSourceLogPartitionJetTwo_lt_neg_jetThree.
Targeted source check/build pass. #print axioms: propext, Classical.choice, Quot.sound.

Computation report:
docs/drafts/pipeline/2-fully-proven/computations/2026-08-29-c5-homotopy-seam-cooling/REPORT.md

Key exact computation:
- Pointwise p4*p6-p5^2 is negative in the physical tail; generic Cauchy proof killed.
- Pointwise p5<=3A p4 fails away from minimal edge.
- Complete n=2 atom-plus-ray ordinary reserve for F5+6AF4 is exp(-3A)*12A*P9(A)/(2A-3)^6 before common positive factors.
- P9(A) expanded in y=A-6 has all positive integer coefficients, so dominant reserve is exactly positive for A>=6.
- 4096-point 80-digit scan A in [6,1000], verified at 120 digits/n<=20, found no violation. At A=6, n>=3 ordinary opposition / n2 reserve = 2.0075e-10.
- Exact dominant asymptotics: R2=6-4/A+19/(12A^2)+..., R4=6-8/A-7/(4A^2)+..., 2R2-R4=6+59/(12A^2)+....

Open core: prove -F5<6AF4 by (i) higher-atom tail absorption using gap 8-3=5 and (ii) Bell correction absorption. Numeric results cannot be Lean premises. Frontier map and Stage1 card theta-c5-likelihood-homotopy-curvature.md updated.
