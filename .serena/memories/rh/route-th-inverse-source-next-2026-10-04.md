# Route TH inverse-source frontier — 2026-10-04
Active unlimited goal: unconditional Lean RH proof/falsification. NOT achieved; no external blocker. No subagents, commits, numerical experiments, full/umbrella builds. 29 owned saved leaves now audited/wired. No live owned build/search jobs at this checkpoint. Previous goal turn is PROGRESS: N17/N18 saved actual proofs.

## Rules and location
cwd /Users/michael/Documents/code/hgt. Final audits from formal:
lake --old env lean -o .lake/build/lib/lean/GaloisForLFunctions/RHTower/<Leaf>.olean GaloisForLFunctions/RHTower/<Leaf>.lean
One owned foreground Lean at a time, poll exact handle until terminal. #print axioms in /tmp only, standard3=[propext,Classical.choice,Quot.sound]. No sorry/axiom/native_decide/heartbeat overrides. Wire exact imports once; never build umbrella. Preserve shared edits. Serena symbol lookup rejects new Lean paths as ignored, so exact text fallback was used for visibility-only edits.
Card: docs/drafts/pipeline/1-in-progress/theta-c5-nonlocal-defect-transport.md
Log: docs/drafts/pipeline/1-in-progress/route-th-source-sign-working-log.md
TH map: docs/reports/rh-current-frontier-map.md. RN heading remains intact.
Earlier N9-N15 details: mem:rh/route-th-nonlocal-c5-next-2026-10-02.

## Notation and established route
RHTower.ThetaCuspDefect namespace. c=thetaCuspLogCurvature, B=c'', H=sourceDefectJet=4c'-c''', b=B-4c>0, b'=-H.
Fix0<t<=u. e(s)=(c(u+s)+c(u-s))/2, E'=e, E(0)=0; Q'=2E,Q0=0.
p=e',r=e'',w=e'''; D1=tE,y=E+te,d=2e+tp,d'=3p+tr.
Actual source: c>18,c'>=0,c'<2c,4c<c''<9c onx>=0. c''/c strictly decreases. N10 H<(4+12/q)b and H'>fH with f<0, -f*(4+12/q)<162.
N9 J3''-(d'/d)J3'<18eJ3. N12 psi=sinh(ky), k²=9/(2c(u)), J3/psi strictly decreases. Positive Green transfer F'F0<FF0', F=-actualcenterNumerator>0,F0>0; full compensation F*modelComp<actualComp*F0. N13 modelComp=(W-5)F0-5tF0'>=0 still open; even full C5 would not prove all-degree/RH.
N14 ThetaCuspC5ClockSourceOrientation: actual P=1311c4-1017c²B-122cC+176B²>0. Candidate local coefficient P/(315c²)>0, but analytic germ identification unproved. Public source_projective_upper B<9c. source_fourth_curvature_upper C<846c newly made public; latest final39294 exit0 empty log.
N15 ThetaCuspC5IntrinsicActionProfile: F*=t^(9/5)Q^(8/5)exp(6Q/5), h=F*'/F*=9/(5t)+12E/5+16E/(5Q). Explicit h' audited.
R=actionProfileInverseReserve=dD1(h²+h')-(d'D1+dy)h+d²>0 on0<t<=u.
J*=intrinsicActionInverseSource=F*R/(4D1²)>0. Literal inverse-Green operator and derivatives audited. Full Bose budget (W-5)F*-5tF*'>=0 audited. Need J*/psi increasing AND zero-endpoint Green recovery before inferring N13.
N16 target psi R'+[(h-2y/D1)psi-psi']R>0. No proof yet.

## N17 CERTIFIED
Leaf ThetaCuspC5LinearClockEnvelope. Scratch45006 exit0, standard3 on three endpoints. Final26866 exit0 empty log; initial wrong-cwd final attempt exited1 missingrelativefile, corrected audit is authoritative. Exact umbrella import once.
linearClockEnvelope(z)=(15+3z+6z²+z³)/(15+3z+z²).
clock_coth_lt_linearEnvelope line85 proves z cosh(z)/sinh(z)<envelope forz>0.
Proof: cleared error after2exp(z) is exp(2z)(3z²-12z+15)-(2z³+9z²+18z+15). First3 derivatives vanish0, fourth=48z²exp2z>0; four positive derivative steps.
constantInverseClockGrowth=1+2z²/15+(z²/5+4z4/675)/(1+z²/10+z4/675).
linearEnvelope_lt_constantInverseClockGrowth line115 proves strict comparison. Cleared polynomial:
11/90-19z/450+2z²/135-z³/1125+2z4/10125
=(z-19/10)²/90+739/9000+z²[2(z-9/4)²/10125+73/27000]>0.
This is ONLY the constant-curvature diagnostic, not actual varying source order.
Old bound (105+45z²+z4)/(105+10z²) has quadratic growth; possible global weakness identified, no actual-source counterexample asserted. Linear envelope replaces it in the next sufficient target.

## N18 CERTIFIED — actual finite coupled shape cancellation
Leaf ThetaCuspC5CoupledShapeQuadrature. Scratch88089 exit1 normalization/division errors; corrected58774 exit0, standard3 on all3 audited endpoints. Final92615 exit0 EMPTY LOG. Wired once.
Private qp=p,qr=r,qfour=e''''; public quadratureCurvatureThird=w.
quadratureCurvatureThird_lt_primitive proves w(s)<846E(s) for0<s<=u by integrating actual fourth-curvature bound. Private E_chord gives E(s)<=sE(t)/t on[0,t].
gamma=tE/Q,alpha=te/E,beta=t²p/E,delta=t³r/E.
coupledShapeBlock S=64(gamma-1)-22(alpha-1)+57beta-55delta.
coupledShapeKernel K(t,s)=(170/3)t²s-7s³+16s4/(3t)
=s[54t²+s²+8/(3t)*(t+2s)*(t-s)²]>0 forpositive s,t.
coupledShapeBlock_variance_identity line142:
E*S+integral_0^t K*w =64(tE-Q)²/(tQ).
Primitive K*r-K_s*p+K_ss*e-K_sss*E+(64/t)Q differentiates exactly toK*w; endpoint yields55t³r-57t²p+22te-86E+64Q/t.
coupledShapeBlock_lower_reserve line181:
0<S+(827*846/45)t4.
Uses w<846E, E chord, positiveK, exact integral K*(s/t)=(827/45)t4. This controls one adverse block, NOT all N16 mixed terms.
No computations/added axioms/heartbeat overrides. Temporary N17/N18 Lean files removed after final0.

## Next hard target / N19 PAPER mechanisms
Still attack full actual N16 finite sign, not optimize constants. Set Z=tE,D=2alpha+beta,L=3beta+delta,A=9+12Z+16gamma,
P=144Z²+384Zgamma+96gamma²+156Z+208gamma-9+5alpha+25beta.
Rbar=R*t²/E²=D*P/25-L*A/5; J*=F*Rbar/(4t4).
dot=t d/dt:
dotZ=Z(1+alpha), dotgamma=gamma(1+alpha-2gamma),
dotalpha=alpha+beta-alpha²,
dotbeta=(2-alpha)beta+delta,
dotdelta=(3-alpha)delta+epsilon, epsilon=t4*w/E.
With z=ky, the sufficient ACTUAL remaining algebraic target is
(15+3z+z²)[(A/5-4)Rbar+dotRbar]
 -D/(1+alpha)*(15+3z+6z²+z³)Rbar>=0.
N18 controls its coupled linear shape block; higher mixed terms and clock geometry remain.

Dependency-closed PAPER geometry to formalize as needed:
1. r>4e,0<=p<2e imply r e-p²>0, so p/e increases.
Freeze t: F(s)=(e(t)+t p(t))E(s)-e(t)s e(s), F'=t p(t)e(s)-s e(t)p(s)>0 on0<s<t. Gives dotalpha>0.
2. Freeze t: G(s)=(E(t)+t e(t))Q(s)-2E(t)sE(s), G'=2[t e(t)E(s)-sE(t)e(s)]>0 by alpha order. Gives dotgamma>0.
3. Integrate p<2e and E>=c(u)t to get alpha<1+2t. r>2p givesdelta>2t beta, hence dotbeta>beta>0.
4. Preserve the affine defect relation from N14's proof, not just846c: C<4B+162(B-4c)=166B-648c. Thus w<166p-648E, epsilon<166t²beta-648t4. NOT yet a public Lean theorem. Source_fourth_curvature_upper proof has the exact ingredients before it applies B<9c.
Subsidiary conjecture Rbar'>0 remains open. Crude independent epsilon<=846t4 loses useful coupling; retain beta/defect relationship. Do not claim any N19 sign without full proof.

## Validation/search state
Final lint67896 exit1,13 unrelated unreachable modules, none ours. Log /tmp/th-c5-coupled-shape-quadrature-lint.log; ThetaTailFinitePairTransport replaced earlier ThetaTailTransportPrimitiveFloor in error set. RN heading preserved. Map/card/log updated.
Search29253 terminal0 partial1215957 inverse-source hits; search60699 terminal0 partial=false1216118 (source/method candidates unverified), no quadrature closure; search42698 terminal0 partial1216220, action/elasticity identities only, no checked monotonicity. No live owned jobs.
