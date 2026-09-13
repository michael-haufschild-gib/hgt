# Interaction continuation of constrained-theta collisions

**Outcome:** four gap-24 tracks reach the opposite interaction endpoint and pass four return checks. The two (+,-) tracks stop at the minimum allowed continuation step. All outputs were downloaded and checksum-verified. Whole-family runtime 233.53 seconds.

For gap-24 direction (+,+), lambda moves from .00589249371103 to .00597673903943 as kappa goes from 0 to 1. Direction (-,+) moves from .0109767490713 to .0101478418484. These are continued local collision branches, not minima selected independently from successful scans. Fresh 100/160-digit endpoint refinement recovers the original candidates. Maximum return error in t is 3.56e-36; independent theta-source normalization anchors at t+1/8 agree within 3.01e-170 in the fixed envelope units.

| Unfinished (+,-) track | Last kappa | Last t | Last lambda | Positive-multiplier bound |
|---|---:|---:|---:|---:|
| From additive gap-4 candidate | .3546875 | 32.5145821286 | .0770590738104 | .109745 |
| From product gap-7 candidate | .3484375 | 40.7244552412 | .0615015980906 | .0874563 |

Both stalls occur well inside the sufficient positive-multiplier region. A failed corrector does not establish a branch endpoint, singularity, disappearance of zeros, or disconnection of the two candidates. Their last accepted Jacobian determinants are nonzero; only the next proposed parameter steps failed. The unresolved issue is whether kappa is a bad coordinate along these branches.

**Positive salvage and next discriminant:** because F=X+lambda*D+kappa*lambda^2*W, the two collision equations are linear in lambda and kappa*lambda^2. With A=X*W'-X'*W, B=D*W'-D'*W, C=X*D'-X'*D, the regular locus has lambda(t)=-A/B and kappa(t)=B*C/A^2. This derived algebraic parametrization can test folds of kappa(t) without continuation in kappa. It is an implementation bridge, not a newly formalized theorem. Distinguish F_lambda=0 from F_tt=0 before interpreting a fold as a triple zero.

**Consequence for HB/RH:** direction-dependent interaction sensitivity survives branch matching in the two control directions. The apparent (+,-) switch remains unresolved. No global first collision, zero ancestry at lambda=0, physical extinction or source-selection theorem has been established.
