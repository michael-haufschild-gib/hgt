# Reflected cosine product repair: completed candidate audit
Date 2026-10-07. Active RH goal unchanged/incomplete. User says ignore repeated arxiv2610.05474 prompt: already read earlier. hgtl7 applied; anti-theatre and anti-laziness answers posted. Significant novelty beyond literature NOT established.

## Verified artifacts
Card docs/drafts/pipeline/1-in-progress/cosine-product-basepoint-repair.md.
Three new leaves under formal/GaloisForLFunctions/HTGeometry:
- CosineProductRepair.lean: entire N,D, both reflections, W0=1 analytic, W'0=-i*T'0 nonzero; Nw=Dw implies w∈3ℤ including common zeros; off-real N≠D. product_repair_certificate line140.
- CosineProductAperiodic.lean: exact return jets including double returns/common basepoints; projective_period_eq_zero line181; reflected_lattice_aperiodic_certificate line201.
- CosineProductInfiniteFiber.lean: point(n)=fiberPoint1(7n+1), n:ℤ injective; T(point)=T0, T(-point)≠T0 via mod7; genuine analytic 1-points with nonzero denominator; infinite_regular_one_fiber line88; no_polynomial_coordinates line95.
All wired once HTGeometry, latest lines16789–16791 (concurrent unrelated edits may shift). Frontier infrastructure entry precise, no C2-P/novelty claim.

## Construction
T=LabeledCosineDescent.source, a=T0, b=CosineBasepointRepair.divided=dslope T0.
H=T(w)-T(-w), K=(T(w)-a)(T(-w)-a).
Cancel w from (H+iK)/(H-iK):
N=b(w)+b(-w)-i*w*b(w)*b(-w)
D=b(w)+b(-w)+i*w*b(w)*b(-w).
Generic diagonal value -1; origin diagonal basepoint before cancellation, so old regular-positive-diagonal no-go does not apply. Off-real N=D impossible; filling cannot create off-real1-point.

## Exact aperiodicity proof
C=T'0≠0. Return T(x)=a gives x=((18n+1)^2-1)/12 and T'(x)*(18n+1)=C.
Projective period τ: ∀w,N(w+τ)D(w)=N(w)D(w+τ).
Scaled coordinates yield:
H(w+τ)*w*b(w)*b(-w)+K(w+τ)*(b(w)+b(-w))=0.
At0 Kτ=0. First derivative yields
C*(Tτ-T(-τ))+2*(s*(T(-τ)-a)-t*(Tτ-a))=0, s=T'τ,t=T'(-τ).
Exactly one return factor0 forces2s=C (or2t=C); source jet gives18n=1 impossible.
Double return: u(w)=dslope T τ(w+τ), v(w)=dslope T(-τ)(-(w+τ)); shifted differences w*u,-w*v. Cancel w² away from0, continuous fill yields C(s+t)=2st. Source jets sA=C,tB=C implyA+B=2, n+m=0. Locations τ=q(n),-τ=q(m) give54n²=0, henceτ0.
No global basepoint classification, positivity, integer-size or growth estimate.

## Infinite fiber/nonrationality
Labels7n+1. Reflected return labelm would give
(18m+1)^2+(18(7n+1)+1)^2=2.
Modulo7 square=5 contradicts Fermat x^7=x,5^3=6,5≠0. Exact algebra, no numerical experiment.
At these points b=0,b(-w)≠0 ⇒N=D≠0.
For polynomialsP,Q,Q≠0 with NQ=DP everywhere, infinite regular1-fiber forcesP=Q by Polynomial.eq_of_infinite_eval_eq. Off-real N≠D then Qevalw0; existing CosineInfiniteDiagonal infinite nonreal family forcesQ0. Exact projective nonrationality, retaining basepoints.

## Audit limits
General one-fiber+bothreflections nonperiodicity is classical: rational Cayley(w) for finite fiber; odd entire sin(πw/3)/(w²-9), filled±3, supplies infinite simple lattice fiber and nonperiodicity after Cayley. Do NOT advertise this general boundary as new.
Contribution: exact rational reflected-cosine repair escapes previous positive-diagonal obstruction and passes local tests. Significant scientific novelty unestablished. No RH premise discharged.
Full C2-P still requires BOTH other cube-root fibers supported in prescribed residue classes and ALL marked local degrees simple. Not proved/disproved. Formal simple origin only; infinite regular1-points means denominator nonzero, NOT formal all-simple theorem.
Canonical secant repair ConjectureE still open after sum no-escape theorem; see mem:rh/cosine_sum_no_escape_formal_2026_10_07. Product does not settleE.

## Next consequential target
For λ³=1,λ≠1 classify (1-λ)H+i(1+λ)K=0 retaining cancellations. Need exact prescribed labels/localdegrees, not more one-fiber polishing.

Possible geometry OPEN CORE in card, unproved:
Proper cosine-pair curve (T(w),T(-w)) in P1×P1. At(∞,∞), W=-1. For limitingλ≠-1 boundary fiber has two points each with one finiteT coordinate. Connected cluster set fixes one point; scalar descended cosine has no finite asymptotic path, contradiction.
Missing dependency-closed scalar no-asymptotic proof, pair properness, projective boundary identities. Existing ConicInteriorLimit.conic_interior_limits/mixed_product_limits may establish properness without bounds. Scalar proof likely exp quadratic roots + finite connected cluster + exp-sheet stabilization, square-lift as earlier.
This would control asymptotic ends for all3marked targets; it does NOT locate fibers or settleC2-P. Avoid indefinite classical Iversen infrastructure without three-fiber insight.

## Search/source audit
Lexical cosine/basepoint: secantrepair only. Period/derivative/basepoint OR:20ranked+5exploration inspected; relevant source_period_eq_zero and LabeledCosineMobius.projective_period_eq_zero audited. Infinite/fiber/rational query found old RationalCosineDiagonalRepair.infinite_off_real_one_fiber. Polynomialidentity found in mathlib and scratchverified.
Primary Bergweiler–Eremenko real.pdf Thm1 no help: W already maps real line to circle via conjugate reciprocity, and proof uses excluded characteristic estimates. radial_mero_revision2.pdf concerns3distinctrays, not3labels on same line. bergwei.pdf primary classicalcos√z examples read intro; exact novelty not established. No stale arxiv reread.
Paper-card anti-theatre corrects overbroad novelty claim explicitly.

## Validation/cleanup
Target build --old +GaloisForLFunctions.HTGeometry.CosineProductInfiniteFiber passes3405jobs.
Final direct lake env lean EACH of3leaves passes exit0 with no warnings/output.
Five axiom checks only propext,Classical.choice,Quot.sound.
Scoped diff whitespace clean; no-index untracked emptyexit1 means newfilediff, no whitespace error.
Global lint exit1,12unrelated unreachable:
RHTower.WeilConeVonMangoldtZetaPencil,XiTiltRayGrowth;
HTGeometry.ApertureConeCalculus,ApertureConeWinding,ApertureLogTranslation,ApertureOpenHistoryIdeal,BoundaryCoronaCStarAlgebra,ModularHeightBounds,ModularLambdaGrowth,ModularThetaNormBounds,SchottkyDiskGrowth,SchottkyHalfPlaneGrowth.
No productleaf flagged. Do not report globalpass.
Index exit0 regeneratedAPI/GAPS/OVERVIEW,5changed0removed.
All owned processes exited. Seven scratchfiles removed via apply_patch Delete File. No commit/push/fullbuild/umbrella/heartbeatincrease.

## Lean lessons
convert! for function-instance alignment. Shifted-source HasDerivAt comp needs simp[Function.comp_def] to clearid/Pi-neg. ContinuousAt.comp explicit f:=funw:ℂ=>w+τ (or-(w+τ)) avoids badzero-unification.
continuousAt_dslope_same.mpr differentiability suffices for double-returnjet; no2ndderivatives.
Tendsto.congr' eventuallyequal source→target; F=ᶠ0 requires he.symm fromconstantlimit.
ZMod norm_num did not reduce numerals: use ZMod.natCast_eq_zero_iff7 7; square5 proof after casts uses linear_combination hh-52*h7.
Base finalderivative ring emitted harmless suggestion despiteexit0; ring_nf finalclean.
Nonexistent names corrected: HasDerivAt.congr,pow_eq_zero,Filter.EventuallyEq.tendsto_iff. Verified alternatives sq_eq_zero_iff,Tendsto.congr',Polynomial.eq_of_infinite_eval_eq,mul_left/right_cancel₀,ZMod.pow_card.
