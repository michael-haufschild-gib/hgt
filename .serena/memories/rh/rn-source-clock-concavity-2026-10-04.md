# RN-P-7ah: source concavity in two clocks

Route RN goal ACTIVE; RH not proved/falsified. No subagents, computations/experiments, additional axioms, unproved source premises, heartbeat increases or full/umbrella builds.

New leaf formal/GaloisForLFunctions/RHTower/ThetaDiagonalClockGeometry.lean, namespace RHTower.ThetaDiagonalClock, 20 public theorems. Imports ThetaCoordinateCanonicalGlobal and ThetaFinitePairSturmCrossing. Let actual p=thetaCuspLogDecaySlope, c=p', v=c', a=c'', U=ThetaCoordinate.sourcePotential. Define A=x*c-p, M=ThetaCoordinate.potentialConvexityMargin=3*x*c²-3*p*c-x*p*v, R=c*v-p*a. Existing actual source A,M,R>0. New reserves:
B=potentialReserve=x*M-2*A²; B'=M+x²*R>0;
C=curvatureReserve=x*M-A²; C'=M+x²*R+2*x*v*A>0.
Both vanish at0 and are strictly positive on x>0.
B=x²c²+xpc-2p²-x²pv; C=2x²c²-xpc-p²-x²pv.

slopeRatio=p/x, clock=x*p-1, clockRate Q=p+x*c>0. potentialSlope=A/(x²p)>0 has derivative -B/(x³p²)<0. clockSlope=A/(x²Q)>0 has derivative -2C/(x³Q²)<0. Both strictAntiOn positive ray. Public slopeRatio_potential_chord and slopeRatio_clock_chord give strict lower/upper endpoint tangent comparisons for every0<x<y. This is actual source p/x concavity in U and z, NOT complete Ward-forcing concavity. Private generic chord lemma removes duplicated argument; all public sign laws have only domain constraints, no source hypotheses.

Validation: API1601 passed. Checks92376/47756 failed elaboration/extra tactics only; repaired. Final actual-source check/export3895 via lake --old env lean GaloisForLFunctions/RHTower/ThetaDiagonalClockGeometry.lean -o correspondingolean exited0, no diagnostics; no source edits afterward. All20 public #print axioms queries26415 via /tmp passed, each exactly [propext, Classical.choice, Quot.sound]. Full manifest checked20 expected/20 actual, none missing/extra/nonstandard. Import wired RHTower.lean. Lint36597 exit1 with18 unrelated unreachable modules, no own-leaf/forbidden error; exact names saved in working log. Targeted whitespace check passed. All owned processes terminal; all11 temporary files removed and absence verified.

P3 docs/drafts/pipeline/3-formalized/theta/rn-source-clock-concavity.md; frontier updated. Main ongoing card docs/drafts/pipeline/1-in-progress/rn-finite-current-integrated-compensation.md; working log rn-singular-weight-conjecture-loop-2026-10-01.md.

Hard target preserved: previous mem:rh/rn-diagonal-ward-single-crossing-2026-10-04 has F=1-g*(1+n)/Z and E. Need F-z*D/x²>0, D=E/k². Proposed complete forcing concavity equivalent Q*(g*j)''-Q'*(g*j)'>0 with j=1+n, retains favorable 2Q*g'*j'. Still unproved. Source p/x concavity is a new global ingredient, not completion.

Concrete positive-coarea-mass extension: for u>0, alpha=shift(0,x,u), beta=x+alpha, ell=alpha+beta, S=p(alpha)+p(beta), N=ell*(beta*c(beta)-alpha*c(alpha))-x*S, T=alpha*c(alpha)+beta*c(beta)+alpha²*v(alpha)+beta²*v(beta). Actual rate m=S/ell satisfies m_x=N/ell³, m_xx=(T-S)/ell³-3xN/ell⁵. Potential-concavity target (3xp+ell²c)*N-p*ell²*(T-S)>0. At u=0 equals x²*B>0 (closed). Positive-u sign unproved. Exact N=ell*(A(beta)-A(alpha))+2u*(p(beta)/beta-p(alpha)/alpha) shows how new potential chords enter while retaining variable weights. Ward-clock version replaces p,c withQ,Q'. Even proving full-mass rate concavity only addresses g; full mixed-row feedback must be paid. Do not silently replace goal with boundary or component sign.

Mixed-row second jet already available: Mrow=ThetaJoint.firstLeft 0 x; Mrow'=mixed 0 x; Mrow''=mixedRight 0 x. For d=x*k0*kx,L=1/x-p, j''=[Mrow''-2L*Mrow'+(L²+1/x²+c)*Mrow]/d. Actual signed comparison, not smoothness, remains hard.

Search83823 partial=false inventory65309;11212 false65311;83853 false65311;62410 false65315. Semantic coverage unmeasured/source-only metadata dominant. All20 candidates+20 source statements+proposed ingredients inspected each. Last search indexed our unverified leaf, not used as independent evidence. Existing potential-margin, projective-reserve and source derivatives apply; unrelated clock hits don't. No absence inferred from search.

Repair lessons: simp id_eq and Pi.mul_apply/Pi.pow_apply before field_simp; explicit nonzero Q after unfolding; typed HasDerivAt lambdas plus convert! avoid subtraction-function instance mismatch in derivative rewrite. Remove ring after field_simp if it already closes goal; no linter suppression.