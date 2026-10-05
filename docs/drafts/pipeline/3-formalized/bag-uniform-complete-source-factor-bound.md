# BAG uniform factor bound for the complete original source

01au. Fixed positive real rho1,rho2; alpha=rho1/logN+i*t1,
beta=rho2/logN+i*t2. Uniformly for EVERY real frequency pair, eventually
at the ORIGINAL prime cutoff,

 |criticalCompletedConeEuler P_N (1+alpha) (1+beta)|
  <= C*|zeta(1+alpha)|*|zeta(1+beta)|*
       |Q_N(beta-alpha)*Q_N(alpha-beta)/(Q_N(-alpha)*Q_N(-beta))|.

Both original coprime cofactors, both exclusions, the allowed first/second
collision and every signed sector are retained. Marked factors are bounded
using their explicit cofactor-completed numerators on compact annuli.
No local unlabelled factor is inverted. Thus its zeros cause no gap.
Three exact label indicators and Mertens normalization control the full sum.
No local nonvanishing, source estimate, uniformity or RH premise is assumed.

Leaf ChiRamanujanUniformLabelSource590lines/API1;
criticalCompletedConeEuler_uniform_factor_bound.
Scratch63282 emptyPASS. Unused private helpers/imports removed. Final
foreground production58554 emptyPASS via lake --old env lean <leaf> -o <olean>.
Combined /tmp ingredient/axiom audit57460 PASS: main theorem standard3 only;
one unused private scratch binder warning, corrected before next audit.
Index10670 PASS/API entry; umbrella import once. Lint99416 terminal1:
7 unrelated unreachable modules plus unrelated active proof debt
HTGeometry/HankelSingularHeight.lean:75 (lastWeightZero_comp_originParam),
174warnings. No owned leaf issue. Global lint gate does NOT pass.
No full/umbrella build, added axiom, placeholder, heartbeat change, numerical
experiment, commit or push. A broad final simplification hit default
heartbeats; an explicit factor identity replaced it without raising limits.

P2 bag-uniform-complete-source-envelope gives the complete paper mechanism.
The factor bound is now Lean proved. The integrable axes envelope is being
assembled from this result and audited U2/global moving-residue bounds.
Fixed-test signed cancellation, actual moving physical profiles/tails,
physical norm saving, growing moments/cofactors and common-height return
remain open. RH goal ACTIVE.
