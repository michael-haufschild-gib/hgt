# RN-P-7y: global positive-correction current

Route RN. Status: global correction-current sign formalized and directly audited, 2026-10-04.
Certificate: ../../../3-formalized/theta/rn-positive-correction-current.md.
Full signed compensation and the second improper identity remain open.
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

## Nonlocal compensation successor

The Q-current sign retains D's sign but does not retain enough of its size.
For the corrected density ratio r2_x, let F0(t)=integral_0^t 2s*k(s)^2 ds
and Htt=J-F0(t). The exact paper Green candidate is
  O2_x(t)=integral G(t,s)*(-r2_x'(s)) ds,
  G(t,s)=F0(min(t,s))*(J-F0(max(t,s))).
The factor -r2_x'(s)=finiteSecantEnergy(x,s)*k(x+s)/(2*k(s)) is positive.
The normalization is exact: O2'=J*w*(r2-mean(r2)), total w mass=J.
This is not yet a formalized integral identity; integrability and endpoint
terms must be proved. It is the next source-dependent representation to use
when paying C0's derivative, not permission to discard C0 or replace D by a
free positive variable. The target remains the full signed current.

## Renormalized positive-mass identity

A further exact paper simplification eliminates C0 without estimating it.
With w=k(t+x)k(t+y)/(k(x)k(y)), the previously formalized density satisfies
  w*(a+s_y B) = (w*B/(2t))' + w*(Q*B-1/(2t)).
The new mass density is strictly positive because B>t and
Q*t-1/(2t)=(p(t+y)-p(t))*(t/y+1/2)>0. The boundary flux tends to1/2 at zero
(B/t->1, w->1) and to0 at infinity. Thus a primitive of the new positive
mass has finite limit E(x,y)+1/2. The same nonnegative-derivative improper
integral theorem can prove its integrability without separately estimating
C0 or p(t)*k(t+x). This complete analytic transfer is still Lean pending.

The formal derivative target for the whole row then becomes
  E_y = integral w*(correctionCurrent(t,y)*B_x(t)
                     +(p(t+y)-p(y))/(2t)) dt.
Differentiation/integrability of this formula remain obligations. Its exact
compensation question is a positive cost paid by a positive kernel:
  integral w*correctionMargin(t,y)*B_x(t)/(2*t²*y²)
    > integral w*(p(t+y)-p(y))/(2t).
The left kernel's sign is the new theorem being audited. B>t alone does not
pay the cost pointwise near zero. Use the actual Green representation of B
or B-t; never replace it by an arbitrary positive function. This is the
next nonlocal mathematical problem, not a completed global Schur sign.

Lean capstone also targets strict decrease of the literal positive kernel
  weightedCorrection(t,y)=k(t+y)/k(y)*Q(t,y)
for every fixed t>0 on y>0. Its derivative is exactly k(t+y)/k(y) times
the correction current. Multiplication by the fixed positive x-factor and
D_x(t) then preserves the strict node comparison; whole-row compensation
still needs the retained positive cost.

## Gaussian calibration of the missing compensation

Exact paper diagnostic (corpus search inspected; no ready calibration found): for k(t)=exp(-c*t²/2),
c>0, integration of the product derivative gives H(x,y)=k(x)k(y)/c. Hence
E(x,y)=0. The actual finite-pair variables in this model are
  B_x(t)=(exp(c*x*t)-1)/(c*x), a_x(t)=-c*B_x(t).
Thus B>t and the correction current is strictly negative, while the whole
row derivative is zero. The cost is exactly paid, not strictly exceeded.
This rejects any sufficiency shortcut using only those two strict signs.
The positive survivor is the exact saturation calibration: strict full-row
compensation must use the actual curvature variation or an equivalent
Gaussian-cancelling source invariant. For this model N=a+s_x B=0 exactly.
No statement about a counterexample for the literal theta source is made.
