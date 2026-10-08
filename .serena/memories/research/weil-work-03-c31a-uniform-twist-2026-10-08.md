WP03 goal ACTIVE/unbudgeted. Main receiver is still uniform quotient boundedness from arbitrary WeilPositiveFull lam; NOT solved. Newest complete cycle C31a. Use hgtl7 every turn. No agents authorized, no commits/push, no computations, no full/umbrella builds, no heartbeat hacks. Owned Lean prefix WeilWorkSingularArithmetic*, owned card/results, umbrella imports. Foreground one Lean process at a time, targeted lake build --old +Leaf, final lake env lean sourcepath; axiom audits /tmp only.

CRITICAL correction to mem:research/weil-work-03-c30d-harmonic-sign-2026-10-07: tentative C31 phase-free three-dilate profile is FALSE AS STATED. Gaussian J_T(y) near-term is 2 W_T(y)cos(2*pi*y); integer y=n makes cos1 but y=n/2 gives(-1)^n. The proposed scalar Mellin multiplier -1/8 cannot force harmonic equality. C30d harmonic sign L=ReP(1)<=0 remains fully verified.

C31a COMPLETE: two new leaves, 9 public theorems, both targeted --old builds and both final direct source checks pass without warnings. All9 #print axioms lists only propext/Classical.choice/Quot.sound. Imports added immediately after HarmonicSign around RHTower.lean7066. Formal lint exit1 only9 unrelated unreachable modules: RHTower.WeilWorkHigherDenominatorBesselBoundary/FourierBoundary/WeakTrace, WeilWorkQuantizationPairing; HTGeometry.ApertureConeCalculus, ApertureConeWinding, ApertureLogTranslation, ApertureOpenHistoryIdeal, BoundaryCoronaCStarAlgebra. No owned/prohibited declaration issue. Index exits0; generated catalog files no Git diff. All18 owned /tmp scratch/log/research files removed after job exits. No active owned process/unverified source.

New interfaces namespace RHTower.WeilSingularArithmetic, open GaussZeroSum:
TwistedGaussianError imports GaussianError.
1 exists_weighted_twisted_gaussian_kernel_error_le:
 exists C>=0 forall T>=1 y>0, y^(9/8)*abs(J_T(y)-2W_T(y)cos(2*pi*y))<=C*T^(5/6).
Proof split Y=T^(4/3), near kernel bound A(y/T²+1/T), far (B+2)T²/y².
2 exists_norm_source_twisted_gaussian_error_le hW:
 exists C>=0 forall r>0 T>=1, Summable(actual a_n*(J_T(nr)-2W_T(nr)cos(2*pi*nr))) AND norm(tsum)<=C/r^(9/8)*T^(5/6).
QUANTIFIER ORDER uniform C independent of r. a=sourceSquareCoeff lam=((lam0-Lambda)*1)*1. Uses absolute LSeries convergence at9/8 from hW only.

TwistedExtraction imports TwistedGaussianError.
3 exists_norm_source_twisted_gaussW_le hW hr: exists C>=0 forall T>0, actual a_n W_T(nr)cos(2*pi*nr) summable and normsum<=C*T².
4 summable_source_scaled_leftKernel hW hT hr.
5 source_twisted_gaussian_error_eq hW hT hr: sumerrors=sumJ-2sumWcos, both series separately summable.
6 integrable_sourceZetaPairing_scaled_gaussian hW hT hr:
 actual right-contour F(3/2+it)*[r^(1-(3/2+it))*g_T(3/2+it)] integrable.
Uses original rightsource integrability and constant norm r^(-1/2) of power.
7 integral_sourceZetaPairing_scaled_eq_kernelSum hW hT hr:
 integral actual scaled contour=2*pi*r*sum a_n J_T(nr).
8 exists_norm_source_scaled_contour_sub_gaussian_le hW:
 exists C>=0 forall r>0 T>=1 norm(integral actual scaled contour -4*pi*r*sum a_n W_T(nr)cos(2*pi*nr)) <= C*r^(-1/8)*T^(5/6).
This is uniform scale error, cost(k/m)^(1/8) for r=m/k.
9 source_twisted_gaussW_half_eq lam T: halfscale sum equals sum a_n W_T(n/2)*(-1)^n exactly.

C31a verdict PROGRESS/BRIDGE, not literature-novel or WP03 closure. Failed C31 profile retained clearly marked FALSE in PROOF; RESULT/EVIDENCE/card and frontier WP03 row corrected and updated. Paper proof of stronger uniform quantifiers recorded before Lean. Anti-theatre and anti-laziness posted in chat: no literature-novel result claimed; classical representation rediscovered; exact source theorem moves formal frontier only; no effort-based deferral.

NEXT C31b has DEPENDENCY-CLOSED PAPER PROOF in docs/reports/weil-work/results/03-singular-arithmetic/PROOF.md final section. No Lean code for it yet. Exact target from hW alone, for each real c: exists C>=0 forall0<t<=1,
 Re[(1+c²/2)H(t) -(c/2)H_alt(t/4) -c H(4t)] <= C*t^(-5/12).
H=sum a_n exp(-pi n²t), H_alt=sum a_n(-1)^n exp(-pi n²t).
Q(s)=1-c*2^-s, q=Q(s)Q(1-s), entire/bounded on strips, conjugate and1-s symmetric, criticalvalue|Q|².
Multiply canonicalJ Gaussian by q: quarterstrip decay and realcritical0 yield real contour0.
Multiply zetaGaussianPairingTest by q and use generic HerglotzPairing.re_integral_weilContinuation_mul_test_eq for nonnegative spectral integral.
Thus actual source F weighted by q has nonpositive Re integral on.75.
Preserve exact residue shift to1.5: right <=-pi*ReP1*q1*exp(1/(4T²)), uniformly bounded (q1 not presumed positive).
Expansion q(s)=1+c²/2 -(c/2)*2^(1-s) -c*(1/2)^(1-s).
C31a extraction gives weighted Gaussian (1+c²/2)S1-c S2-(c/2)Shalf and normerror O_c(T5/6). S1=H(t), S2=H(4t),Shalf=H_alt(t/4),t=4pi/T².
Do NOT infer weighted bound from scalar C30 bounds (negative coefficients).
Do NOT factor weighted Mellin as Gamma_R V q. It contains separate V_alt.
C31b formalization is next concrete task.

Broader C32 competing conjectures: full positivity alone gives all ordinary gcd-weighted harmonic limits plus finite twist nonpositive quadratic law; competing possibility only regularized/subsequential limits. OPEN CORE: arithmetic limit existence, not assumed. No ordinary harmonic convergence->subseries convergence inference. Full form and even all fixed probes still do not supply uniform denominator tightness / absolute tails needed for WP03.

Corpus audit: C31a/b searches complete no partial, latest68559files generation1281694; all20candidate+20source statements read, proposed generic ingredients inapplicable. C32 deep query positive quadratic gcd matrix Dirichlet coefficients zero first coefficient rigidity was partial at semantic deadline,68565files generation1283089; all20+20 inspected. Follow-up lexical/rg found exact relevant preexisting:
- WeilZetaSquareDilationRigidity: full-positive Lambda*a+mu*f+v impliesa=delta under absolute boundary decay and regular v; not applicable arbitrarysource.
- WeilFibreBochnerLaw.twistFibreSum_nonpos_of_weilPositiveFull retains NotchSmall.
- WeilConeNotchBochnerLaw.notchBochner_le retains NotchSmall AND all gcdHarmonicSum limits.
- HTGeometry/GcdWeightedSeriesInversion.eq_zero_of_tsum_gcd_mul_div_eq_zero retains sum|b|/sqrt(n)<infty; final sieve pays absolute harmonic tails. Cannot assume here.
Existing gcd/fibre algebra REDISCOVERED, not new science.

External primary sources read this turn:
Booker arxiv1308.3067 PDF Definition1.3: discrete strip-supported m, finitely many noninteger multiplicities, coefficient axioms. ArbitraryhW lacks these; no classification shortcut. Oliver1601.05009 sameframework abstract.
Fazzari2306.15553 classical additive-twist Estermann/Voronoi setting.
Guillot-Wu1901.01947 HTML intro gives GCD=totient divisor Gram factorization, cites Smith/Beslin-Ligh; classical, not novelhere.
Hong0808.3550 multiplicative Smithmatrix positivity additional assumptions not ours.
No external theorem supplies arithmetic limit/tail closure.

Lean lessons this cycle:
near kernel bound writes2*cos*exp but our target2*gaussW*cos; use simpa only[gaussW,mul_assoc,mul_left_comm,mul_comm], not change.
Scale product regroup use simpa AC not convert...ring on proposition.
rw[mul_pow]; field_simp closes denominator equality; do not append ring (no goals).
Do not rw[mul_assoc] prematurely in normfactor bound; explicit calc weighted inequality thenring.
Minimal /tmp API probes verified Real.abs_cos_le_one, Real.mul_rpow, rpow_pos_of_pos, div_le_div_iff, summable_norm_iff; Complex.norm_cpow_eq_rpow_re_of_pos, Continuous.const_cpow, Integrable.mul_bdd, Real.cos_nat_mul_pi.
No further audits of untouched C30 modules needed.
