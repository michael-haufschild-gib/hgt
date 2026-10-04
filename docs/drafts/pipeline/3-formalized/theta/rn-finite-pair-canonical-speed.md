# RN: increasing finite-pair canonical speed

2026-10-04. Formalized in ThetaFinitePairCanonicalSpeed; 10 public theorems.
Target: one missing coefficient sign in the full finite-pair Schur current.
Parent: ../../1-in-progress/rn-finite-pair-positive-transport-primitive.md.

For the literal source let p=-(log k)', c=p', v=c'. For x>0,y>=x,t>=0 set
  lambda=(p(t+y)-p(y))/(p(t+x)+p(t+y)).
Claim: partial_t lambda>0 throughout this entire chamber.

The corpus already proves c>0, p(0)=0, p strictly increases, and v/c strictly
increases on the nonnegative ray because c*c''-v²>0
(ThetaCurvature.logEnergy_pos). Retain that curvature variation exactly.

For a fixed d>0 define
  Q_d(u)=[c(u)*p(u+d)-c(u+d)*p(u)]/[c(u)+c(u+d)].
Direct differentiation gives
  Q_d'(u)=[p(u)+p(u+d)]*[v(u)*c(u+d)-c(u)*v(u+d)]
              /[c(u)+c(u+d)]² <0 for u>=0.
Thus
  Q_d(u)<=Q_d(0)=c(0)*p(d)/(c(0)+c(d))<p(d).
For d=0 the same quotient is identically zero.

Put u=t+x,d=y-x. For d>0, Q_d(u)<p(d)<=p(y); for d=0,
Q_0(u)=0<p(y). Writing C=c(t+x), D=c(t+y), P=p(t+x), R=p(t+y),
the exact speed derivative is
  lambda_t=[D*(P+p(y))-C*(R-p(y))]/(P+R)²
           =(C+D)*(p(y)-Q_d(u))/(P+R)²>0.
No tail approximation, numeric bound, source truncation or RH premise is used.

Consequently the coefficient
  A=-lambda*x*s_x-2*t*lambda*s_y-lambda_t
in the full current A*N+(D_current-A*s_x)*B+lambda*(s_x-s_y)
is strictly negative: lambda>=0, s_x,s_y>0 and lambda_t>0.
Matched-packet positivity N>0 therefore contributes a strictly negative term.
The remaining coefficient multiplying B can be positive; its compensation
is still open. Do not discard it or claim full coordinate-current positivity.

Novelty audit: deep corpus query for canonical speed/curvature cross derivative
returned non-partial inventory65123, predominantly source-only metadata.
It recovered the confluent speed_left_deriv formula and actual transport ODE,
but no finite-pair speed sign. Their source bodies were read. The suggested
ingredient set merely computes derivatives and does not prove this sign.
Validation completed 2026-10-04:
- Leaf export with `lake --old env lean -o ...` passed with empty diagnostics.
- Required direct audit `lake env lean GaloisForLFunctions/RHTower/ThetaFinitePairCanonicalSpeed.lean`
  passed with empty diagnostics.
- All10 public theorem axiom queries passed in /tmp: exactly propext,
  Classical.choice, Quot.sound.
- Wired into GaloisForLFunctions/RHTower.lean; no umbrella build.
- Formal lint reports14 unrelated unreachable modules; no own-leaf error or
  forbidden proof declaration.

The actual speed derivative and complete term A*N<0 are formally proved.
Full signed compensation, general anchors, arbitrary rank and arithmetic RH
transfer remain open.
