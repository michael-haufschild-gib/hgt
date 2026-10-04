# RN: exact finite-pair signed Sturm crossing

2026-10-04. Formalized in ThetaFinitePairSturmCrossing.lean,22 public theorems.

For every actual finite pair (0,x), x>0, the signed scalar source-energy
density ThetaSturm.density(0,x,t) has exactly one positive zero. It is negative
before that zero, including t=0, and strictly positive afterward.

Let s=(p(t+x)-p(t))/x, d=s', j=ts-p(t). The proof establishes strict increase
of j*s/d on the nonnegative ray. It starts at0 and exceeds1/2 at a finite
source-defined point. The forcing d-2js therefore crosses once from positive
to negative, and equals -s² times the literal signed density.

New finite source comparisons retain curvature variation:
  p(t)*s''<c(t)*s', v(t)*s<=c(t)*s',
  c(t)*(t*c(t)-p(t))<t*p(t)*v(t).
They follow from actual logarithmic curvature convexity, projective slope
descent and source derivative comparisons. No numerical bound optimization,
source truncation, RH hypothesis, added axiom or heartbeat increase is used.
Complete paper proof: ../../1-in-progress/rn-finite-pair-sturm-crossing.md.

Validation:
- `lake --old env lean -o .lake/build/lib/lean/GaloisForLFunctions/RHTower/ThetaFinitePairSturmCrossing.olean GaloisForLFunctions/RHTower/ThetaFinitePairSturmCrossing.lean`: exit0, empty diagnostics.
- Required `lake env lean GaloisForLFunctions/RHTower/ThetaFinitePairSturmCrossing.lean`: exit0, empty diagnostics.
- All22 public theorem axiom queries in /tmp: exactly propext, Classical.choice, Quot.sound.
- Wired into GaloisForLFunctions/RHTower.lean; no umbrella build.
- Fresh formal lint: exit1,14 unrelated unreachable modules; no error for this leaf or forbidden proof declaration. The two additional errors since the correction-current lint are RoutePFinitePrimeCovariance and RoutePPrimeCovarianceBudget.

The nonlocal consequence N=a+sB>0 is now formalized, including its actual
source-tail endpoint; see rn-finite-pair-packet-positivity.md. All11 public
theorems in its two leaves passed direct source and standard-axiom audits. Full Schur coordinate compensation,
general anchors, arbitrary rank and arithmetic RH transfer remain open.
