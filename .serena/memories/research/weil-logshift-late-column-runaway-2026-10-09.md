# Every sufficiently late fixed inverse column runs away
Verified 2026-10-09. ONLY local Lean corpus and installed local Lean/mathlib APIs. NO WEB, PAPERS OR NUMERICAL EXPERIMENTS. Indefinite corpus goal remains active; no subagents. All owned jobs terminal and scratch cleaned.

## Exact new theorem
exists_weilLogShiftRecoveryMomentResponse_fixed_column_runaway:
  exists K:Nat, forall k>=K, forall y:Real,
    Tendsto (fun n => |weilLogShiftRecoveryMomentResponse y n k|) atTop atTop.
Thus EACH sufficiently late FIXED impulse column, at EVERY real shift, has absolute terms tending to infinity. This is stronger than moving-diagonal growth and was proved independently via the full triangular recurrence.
exists_weilLogShiftRecoveryMomentResponse_fixed_column_not_summable gives nowhere signed nonsummability for each such column.
The original coordinate-zero conjecture remains OPEN. Do not infer anything about every early column or claim K=625.

Stronger coefficient theorem:
exists K>=625, forall k>=K, forall n>=k+2, forall j with k+2<=j<=n,
 exp((j+1)*(n-j))*|Column(k,j)| <= |Column(k,n)|.
Here all arithmetic in exponents is REAL after casting; avoid natural subtraction there.
Column(k,n)=Inverse(UnitHistory k)(n)-Inverse(0)(n).
Seed Column(k,k+2)=1/W(k+2,k+2)>0; coefficients vanish below seed. Therefore exists c>0, forall n>=k+2, c*exp((k+3)*n)<=|Column(k,n)|.

## Five new leaves, all final sources compiled/exported cleanly
formal/GaloisForLFunctions/RHTower/WeilLogShiftTwoEdgeLower.lean
formal/GaloisForLFunctions/RHTower/WeilLogShiftRecoveryRowBounds.lean
formal/GaloisForLFunctions/RHTower/WeilLogShiftSubdiagonalAmplification.lean
formal/GaloisForLFunctions/RHTower/WeilLogShiftRecoveryColumns.lean
formal/GaloisForLFunctions/RHTower/WeilLogShiftLateColumnRunaway.lean
All five uniquely wired immediately after WeilLogShiftExponentialPrecisionGenericity in RHTower.lean. No old public APIs changed. Generated LEAN_API/GAPS/OVERVIEW refreshed by index.

## Exact new APIs and analytic mechanism
TwoEdgeLower (3 theorems):
smoothTransition_ge_exp_edge {x} (0<x): exp(-1/x)/2<=S(x).
truncatedRiemannAutocorr_central_lower_two_edges {L z d a}
 (0<d)(0<=z)(z/2+d+a<=L)(1<=L+z/2-d):
 (2*d*((2*pi^2)*S(a))^2)*exp(-(2*pi*exp(z+2*d)))<=KL_L(z).
truncatedRiemannAutocorr_central_lower_exp_two_edges adds0<a and gives
 (d*(2*pi^2)^2/2)*exp(-2/a-2*pi*exp(z+2*d))<=KL_L(z).
Opposite cutoff factors equal1; only two facing factors are small. Old symmetric margin bound wasted four.

RecoveryRowBounds (5 theorems):
truncatedRiemannAutocorr_le_exp_edge_relaxed L y r hmargin:
 KL_L(y)<=exp(8-4r)*K(y), with hmargin:2L-y<=1/r. No sign premise on r needed; r<2 uses full-kernel bound and exp factor>=1.
weilLogShiftRecoveryCutoff_column_margin_le n j hj2:
 2Cutoff(n)-(logj-log2)<=(n+1-j)/j.
weilLogShiftRecoveryWeight_row_edge_bound n j hj2 hjn:
 |W(n,j)|<=2exp(8-4j/(n+1-j))*(P_log2(j)+P_0(j)).
exists_weilLogShiftRecoveryWeight_row_exponential_bound {a}(0<a)(a<pi):
 exists C>0, forall2<=j<=n, |W(n,j)|<=Cexp(-a*j-4j/(n+1-j)).
weilLogShiftRecovery_tail_exponent_gap {n j:Real}(j+2<=n)(625<=j):
 (pi+9/4)*n-(99*pi/100)*j-4j/(n+1-j)-(j+1)*(n-j-1)<=-n/100.
Proof sets m=n-j-1>=1, uses m+4/(m+2)-2=m^2/(m+2)>=m/3, pi<4 and j>=625. Entirely symbolic.

SubdiagonalAmplification (5 theorems):
weilLogShiftRecoveryWeight_subdiagonal n hn2:
 W(n+1,n)=2KL_Cutoff(n+1)(logn-log2)/sqrt(n).
exists_weilLogShiftRecoveryWeight_subdiagonal_polynomial_lower:
 exists A>0, eventually A/(n+1)^2*exp(-(pi+20/9)*(n+1))<=W(n+1,n).
Set N=n+1, d=1/(20N), facing margin a=9/(10N). Half overlap>=1/(n+2)>=19/(20N) for n>=18. Cutoff>=2 eventually guarantees opposite plateaux. Convex exponential chord absorbs kernel widening in constant pi*(exp2-1)/20. sqrt(n)<=N gives quadratic prefactor.
exists_weilLogShiftRecoveryWeight_subdiagonal_exponential_lower {b}(pi+20/9<b):
 exists D>0, eventually Dexp(-b*(n+1))<=W(n+1,n).
eventually_weilLogShiftRecoveryWeight_subdiagonal_amplifies:
 eventually 2exp(n+1)*W(n+1,n+1)<=W(n+1,n).
exists_weilLogShiftRecoveryWeight_tail_dominance_threshold:
 exists J>=625, forall n j, J<=n -> J<=j -> j+1<=n ->
 (n+1)*|W(n+1,j)|*exp(-(j+1)*(n-j))<=W(n+1,n)/2.
Uses a=99pi/100, b=pi+9/4, the exponent gap and (n+1)*C*exp(-(n+1)/100)->0. These are fully unconditional native weight conclusions.

RecoveryColumns (1 def,6 theorems):
weilLogShiftRecoveryCoefficientColumn k n := Inv(Unit k)n-Inv(0)n.
_eq_zero k n (n<k+2).
_row k n (2<=n): sum j in Icc2n Column(k,j)*W(n,j)=if n=k+2 then1else0.
_seed k =1/Wseed; _seed_pos k.
_row_zero k n (k+2<n): same sum=0.
weilLogShiftRecoveryMomentResponse_eq_coefficientColumn y k n hn2:
 Response(y,n,k)=(Column(k,n)/sqrt n)*P_y(n).

LateColumnRunaway (4 public theorems,1 private tail helper):
exists_weilLogShiftRecoveryCoefficientColumn_growth
exists_weilLogShiftRecoveryCoefficientColumn_exponential_lower
exists_weilLogShiftRecoveryMomentResponse_fixed_column_runaway
exists_weilLogShiftRecoveryMomentResponse_fixed_column_not_summable
Inductive older tail is bounded by W(n+1,n)*|Column(k,n)|/2. Zero prefix handles early j; remaining entries use dominance threshold and previous growth. Cardinality(Icc2(n-1))<=n+1 sums the bound. Two exact sum_Icc_succ_top splits expose adjacent and diagonal terms. Reverse triangle and amplification force one-step gain exp(n+1). Induction yields two-index comparison. Kernel critical rate at every y is below2pi+1, so coefficient growth beats all shifts. A positive exponential-over-(n+1) lower envelope gives absolute response tending to infinity. Summability would force absolute terms to0.

## Verification
All five FINAL leaves compile/export with lake --old env lean <leaf> -o <object>, exit0, no diagnostics. Main growth/runaway/nonsummability all passed FIRST compilation; later cleanup removed an unused helper argument and redundant tactics. Other failures were API/normalization/positivity facts, no paper argument change.
Exhaustive /tmp #print axioms for all23 PUBLIC THEOREMS: every set exactly [propext, Classical.choice, Quot.sound], all names covered once, exit0 and no diagnostics. Private tail helper transitively covered. Axiom scratch also verified norm-decay API used by nonsummability.
Index exit0:5 changed,0 removed. ALL24 public API rows checked for kind,module,path,line and duplicates. Five unique imports checked. Source hashes unchanged after final compiles and audits; objects newer than sources. Scoped gap/raised-limit/whitespace checks passed.
Latest global lint exits1 ONLY for6 unrelated unreachable modules:
RHTower.HorizontalIsolationCrossPairDecay
HTGeometry.PaperFrameDualNumberBoundary
HTGeometry.PaperOriginalDiscreteValuation
HTGeometry.PaperOriginalValuation
HTGeometry.PaperSL2PolynomialLift
HTGeometry.QKrawtchoukCompanionWeakLimit
No affected-file diagnostic. Do not fix unrelated modules; earlier14-error list is historical.
All owned jobs terminal. Ten explicit /tmp/hgt-weil-column-* scratch/log/manifest files removed, including prior search.json; absence verified. No commits, full/umbrella builds, computations, web, papers or subagents.

## Cards and exact next task
Formalised: docs/drafts/pipeline/3-formalized/weil-logshift-late-column-runaway.md
Original working/open-coordinate-zero card: docs/drafts/pipeline/1-in-progress/weil-logshift-fixed-column-obstruction.md
NEXT WORKING CARD: docs/drafts/pipeline/1-in-progress/weil-logshift-arbitrary-precision-impulse.md
Dependency-closed PAPER proof recorded, NO Lean yet for next payoff. Re-search local corpus before new Lean.
Target: for arbitrary bounded center, any strictly positive coordinatewise envelope epsilon, and any finite prefix M, find a bounded history differing at EXACTLY ONE coordinate k>=M, obeying all envelope constraints, with nowhere tail-unbounded moments. This removes the earlier sigma<4-pi restriction for EXISTENCE and retains exact prefix.
Stronger: for every sufficiently late fixed k, at most one real amplitude t on line center+t*Unit(k) can fail WeilLogShiftUniformNowhereBounded. If two distinct amplitudes fail, contraposition of origin-to-all-shifts gives eventual origin bounds for both. Their difference equals (t-u)*Response0 column; its norm tends infinity, contradiction. Pick two distinct NONZERO amplitudes epsilon(k), epsilon(k)/2: at least one good. Both satisfy the envelope, all other coordinates agree exactly. At-most-one exception may depend on center,k; do NOT assert every nonzero perturbation of arbitrary center diverges.
Existing APIs freshly inspected: weilLogShiftRecoveryMoment_sub_eq y n h g = MomentCLM y n(h-g); weilLogShiftUniformNowhereBounded_of_origin h (forall B N exists n>=N, B<norm Moment0 h n); weilLogShiftUniform_nowhere_summable_of_nowhere_bounded.
Further exposed conjectures (paper/novelty audit needed): strict alternating signs in each late impulse column; quadratic-exponent lower coefficient bound from exp(n+1) step gain; generic/measure consequences in arbitrary envelope spaces. None formalised yet.

## Lean lessons
Root convexOn_exp, NOT Real.convexOn_exp. abs_sub_le takes3 arguments; use A,0,B for |A-B| bound. mul_le_mul_iff_left₀ cancels a POSITIVE RIGHT factor; right₀ cancels left factor. Finset.sum_Icc_succ_top is generated by to_additive, so lexical source search only sees prod_Icc_succ_top; verified in scratch. Its arguments hab:a<=b+1 and f, conclusion sumIcc a(b+1)=sumIccab+f(b+1).
For logarithm width, normalize n+1+1 to n+2 and ring_nf at h and goal before linarith to align 1/den and -2/den.
In convert of Tendsto proofs, remaining goal is equality of neighborhood filters at0 and c*0: use simp only[mul_zero,add_zero], not ring. ring emitted informational failed-to-close suggestions despite compile success; JSON Lean diagnostics located them, now all final leaves clean.
Avoid field_simp followed by ring if field_simp already closes. For exponential(-G) versus exp(-(j+1)*(n-j)), simpa only[G,neg_mul].
Serena symbol ops unavailable for ignored formal files; established apply_patch fallback. update_plan unavailable; cards are authoritative task tracking.
