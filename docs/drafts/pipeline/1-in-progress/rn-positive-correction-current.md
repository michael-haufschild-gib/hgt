# RN-P-7y: global positive-correction current

Route RN. Status: dependency-closed paper proof, Lean pending, 2026-10-04.
Parent: rn-finite-pair-positive-transport-primitive.md.

Target for the exact positive correction D=B-t:
Q(t,y)=(p(t+y)-p(t))*(1/y+1/(2t))+1/(2t²), t,y>0.
Prove Q_y-(p(t+y)-p(y))*Q<0 on the entire positive quadrant.
No claim that this alone pays the signed companion C0.

Set z=t+y, C=c(z), V=c'(z), A=p(z)-p(y), B=p(z)-p(t), L=2t+y.
The positive cleared margin is
  F=t*y*L*A*B-2*t²*(y*C-B)-y²*(t*C-A).
It equals -2*t²*y² times the desired negative current.

Actual source inputs, all already in the corpus:
- c>18 on nonnegative ray: ThetaCuspDefect.sourceCurvature_gt_eighteen.
- 0<V<2C: ThetaCurvature.velocityGap_pos and C5GlobalCurvatureSigns.
- c''<9c: ThetaCuspDefect.source_projective_upper (C5ClockSourceOrientation).
- c' strictly increases; p'=c, c'=V, p(0)=V(0)=0.

Integrating 9c-c''>0 gives V<9p(z)<=9zC. This is a proof ingredient,
not a numerical-bound optimization target.
Curvature monotonicity gives A,B>0. Two exact chord comparisons:
  t*C-A <= V*t²/2,  y*C-B <= V*y²/2,
  t*C <= (1+2t)*A,  y*C <= (1+2y)*B.
The first follows by two derivative comparisons from increasing c'; the
second from increase of 2p-c and the lower tangent bounds A>=t*c(y),
B>=y*c(t).

For z<=1/2, V<2C gives
  A>t*C*(1-t), B>y*C*(1-y),
  A*B>t*y*C²*(1-z).
The first chord comparison gives
  F >= t*y*(L*A*B-(3/2)*t*y*V).
If z<=1/4, C*(1-z)>27/2 and V<9zC show
  (3/2)*V<C²*z*(1-z)<=C²*L*(1-z).
If 1/4<=z<=1/2, z*(1-z)>=3/16, C>18 and V<2C give the
same strict comparison. Hence F>0 throughout z<=1/2.

For z>=1/2 put U=(1+2t)*A-t*C>=0 and W=(1+2y)*B-y*C>=0.
Exact positive decomposition:
  C*F = t*y*((C*L-6-4*L)*A*B+4*U*B+2*W*A)
          +C*(2*t²*W+y²*U).
Since C>18 and L>=z>=1/2, C*L-6-4*L>0. Thus F>0 here too.
All regions are covered. No finite computation, numerical approximation,
source truncation, or new premise is used.

Remaining hard problem: transport the negative Q current through the exact
D=B-t correction and show that it pays the signed C0=t*s_y-Sigma_x/2
contribution. The second improper identity is still paper-only. General
anchors, arbitrary-rank positivity and arithmetic RH transfer remain open.
