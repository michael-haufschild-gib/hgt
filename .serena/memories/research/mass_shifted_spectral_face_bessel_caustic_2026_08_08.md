# Mass-shifted spectral-face: sharp Bessel caustic (2026-08-08)

Paper-only research; no Lean edits/builds.

Primary card:
- docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/mass-xi-finite-true-prime-cone.md

Report:
- docs/reports/mass-shifted-spectral-trace-route.md §9.3 (ignored by git via docs/reports/)

New paper-proved results:
1. Exact Bessel exterior geometry for F_u(h): for h >= kappa u, kappa>1,
   |F_u(h)| <= C u^(-1/2) exp(-a sqrt(h^2-u^2)) for u>=1.
2. Sharp raw-source slope kappa_B = a/sqrt(a^2-1/4).
   For kappa>=kappa_B, complete exterior true-prime tail is C0; at endpoint O(u^-1/2).
   Hence RH iff finite true-prime prefix through exp(kappa u) is uniformly bounded.
3. Sharpness: for 1<kappa<kappa_B, any annulus from exp(kappa u) to exp(lambda u), lambda>kappa,
   has modulus >= c u^(-1/2) exp((kappa/2-a sqrt(kappa^2-1))u).
4. PNTPlus MediumPNT yields theta(e^h)-e^h = O(e^h exp(-c h^(1/10))).
   Stieltjes IBP plus differentiated Bessel envelope removes a discrepancy layer
   H_*(u)=kappa_B u-Lu^(1/10). For fixed admissible c, exact method wall is
   L_c=c kappa_B^(1/10)/(2a^2-1/2); every 0<L<=L_c gives a C0 exterior discrepancy tail.
   New exact RH criterion is prefix discrepancy through W_*(u)=log(floor(exp(H_*))+1).
5. Graded type/cone duality: for 0<=lambda<=1/2,
   kappa_(a,lambda)=[a sqrt(4a^2+4lambda^2-1)-lambda]/[2(a^2-1/4)],
   solving kappa/2-a sqrt(kappa^2-1)=lambda.
   For lambda<1/2 and kappa>=kappa_(a,lambda), finite prime cone has type lambda iff corpus
   transverse mass displacements are <=lambda. Subthreshold annuli are not type lambda.

Higher principle:
- g_u(h)=h/2-a sqrt(h^2-u^2) is prime entropy minus Bessel action.
- Raw-source caustic g=0 is kappa_B.
- PNT remainder e^{-c h^alpha} penetrates a simple caustic by O(u^alpha).
- Allowed vertical type and minimal spatial aperture are dual coordinates.

Remaining exact core:
- Prove uniform bound for prime discrepancy on [0,W_*(u)); equivalent to RH.
- Further progress must retain phase. Raw-source, modulus PNT, generic mean-square, full KG energy,
  adjacent-prime phase, Hilbert/QEC frames, and W1/W2 clock transport have explicit failure laws.

Formalization later (after refactor):
- Existing usable corpus: XiMassCriticalOutgoingOpenCore, discrete remainder/centered atom/integer face,
  prime-square boundary residue, higher valuation ideal, XiMassStripFourierLipschitz,
  PNTPlus.MediumPNT/chebyshev_asymptotic, graded mass source/type equivalence.
- Missing analytic layer: complex modified-K1 Fourier identity, integral/derivative envelopes,
  sectorial asymptotic, logarithmic prime block bounds, Stieltjes tail IBP.

## Type-zero hostile audit extension

Further paper-only results, still no Lean writes/builds:
- RH is equivalent to type-zero growth of any finite true-prime prefix whose boundary H(u) satisfies H(u)/u -> kappa_B; aggressive retreat kappa_B u-u/log(u+e) is allowed.
- Actual integral Lipschitz theorem controls balanced adjacent-prime coboundaries but leaves scalar Chebyshev-error class. PNTPlus absolute bounds retain type 1/2.
- Selberg floor transform hierarchy has Mellin symbols (-1)^k zeta^(k); k=0 square-root endpoint kills zero modes, log lifts detect multiplicity but have only order-X source bounds.
- Weighted floor family Q_theta=T_(n^-theta)R has exact inverse T_(mu n^-theta). Sharp type-zero invertibility threshold is theta=1/2. For theta>=1/2, Q_theta and R have equivalent critical type-zero bounds; for theta<1/2 model f(N)=sqrt N loses type 1/2-theta. Thus harmonic Q_1 is stable preconditioning, not proof-burden reduction.
- For A_N(D)=sum_(d<=D)R(floor(N/d)), B_N(D)=A_N(D)+2 gamma D, harmonic Q_1 is exact Abel average of B_N(D); endpoint |B_N(N)|<=24 sqrt N is already Lean-proved.
- Exact floor-fibre identity with M=floor(N/(D+1)), alpha_m={N/m}, eta=D-floor(N/(M+1)) isolates reciprocal sawtooth sum sum_(m<=M)(Lambda(m)-1){N/m}; discrete Abel lowers fake O(M^2) floor loss to O(M).
- Endpoint anchoring simplifies it further:
  sum_(d>D) R(floor(N/d)) = sum_(m<=M)(Lambda(m)-1)(floor(N/m)-D),
  B_N(D)=B_N(N)-that-2 gamma(N-D).
  Sawtooth is a coordinate for centered signed triangular hyperbola transport, not independent cancellation.
- Existing bounded-displacement/Wasserstein transport results take norms and lose the Lambda-1 signs; displacement reaches N-D and absolute cost is O(N log M). Exact surviving source gate is type-zero control of harmonic D-average of this centered triangular transport before absolute values.
- Generalized Dirichlet mean square needs exponential prime-log aperture at caustic scale and is not a type-zero-stable sampling inverse.

Files updated:
- docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/mass-xi-finite-true-prime-cone.md, §24/C43-D.
- docs/reports/mass-shifted-spectral-trace-route.md, §9.3 equations 9.3.42--9.3.50.

## Critical floor Wiener closure

- For arithmetic `a`, define `||a||_(1/2;N)=sum_(d<=N)|a(d)|/sqrt(d)`.
- If `a*b=delta_1` and both critical truncation norms are `N^o(1)`, exact floor associativity plus the weighted triangle inequality proves
  `N^(-1/2) T_a f` has type zero iff `N^(-1/2) f` has type zero.
- This strictly generalizes the power-weight threshold. Every scalar floor filter with subpower absolute conditioning in both directions preserves the RH obstruction; smoothing that genuinely reduces known bounds must pay positive critical type unless new signed arithmetic cancellation controls the inverse.
- Qualification is essential: finite Dirichlet support alone does not imply a critically subpower inverse.
- Ordinary `a=1` lies outside the class (`||a||~sqrt N`); replacing absolute inverse conditioning by `sum_(d<=N)mu(d)/sqrt(d)=N^o(1)` is itself RH-strength.
- Remaining mechanisms: signed centered triangular transport, scale-sensitive timelike Bessel prime correlation, or genuinely nonlinear/prime-adaptive synthesis.

Files extended:
- paper card §C43-E, equations 24.34--24.36.
- report §9.3, equations 9.3.51--9.3.53.

## Harmonic projection and causal-Hardy closure

- Exact harmonic projection of centered triangular path is
  sum_(D<N)(1/D-1/(D+1)) C_N(D)=B_N(N)-Q(N)-2 gamma H_N.
  Hence its critical type zero is equivalent to Q, then R, then RH.
- Exact path Gram kernel is K(q,r)=ell*v+2ell-(ell+v+1)H_ell. Fixed low-index diagonal is O(N^2);
  D=1 already contains R(N), so an N^(1+o(1)) positive-energy bound is RH-quality.
- For gauged massive half-wave U_u and physical projection P_H,
  H>u>=0 implies ||P_H U_u P_H||=exp(lambda u). Proof uses a negative-frequency modulation packet
  supported in (u,H), whose outgoing translation remains inside causal interval.
- With actual damping S_(sigma,u)=F^-1 exp(-(sigma+iu)omega) F and any kappa>1,
  lim_(u->infinity) u^-1 log ||P_(kappa u) S_(sigma,u) P_(kappa u)||=lambda.
  Uniform square-root expansion and packets at r=u^q, 1/2<q<1, prove lower bound; outgoing
  factor 1/2-partial_h changes only o(u) logarithm.
- Both exact outgoing cone and sharp Bessel caustic have slope >1, so causal/Hardy compression
  cannot remove critical type. Spatial causality is not corona polarization.
- New causal theta reader has Lean-proved zero direct reflected action and no Lambda-1 coupling;
  true Xi Wiener-Hopf complement is zero-divisor-defined and old quotient analyticity is RH-equivalent.
  Neither reduces source proof burden.

Files extended:
- paper card §C43-F--G, equations 24.37--24.52.
- report §9.3, equations 9.3.54--9.3.64.

## Fixed causal filter rigidity

- For every nonzero bounded Hardy boundary multiplier B and every kappa>1, the damped gauged
  Wiener-Hopf family compressed to (0,kappa*u) has exact exponential type lambda.
- Proof: Hardy uniqueness forces nonzero boundary Lebesgue points arbitrarily far in negative
  corona; sqrt(u)-width semiclassical packets centered at c*u stay inside superluminal cone and
  grow at rate Im omega(xi_R), then xi_R -> -infinity gives lambda.
- Any moving filter lowering type by delta must have depth exp(-delta*u+o(u)) on every surviving
  negative-corona packet. Stable inversion pays reciprocal type. This is microlocal twin of
  critical floor Wiener lemma.
- Fixed causal readers, Blaschke products, rational resolvents, finite jets, and analytic smoothers
  are therefore closed as norm-based routes.

Files extended:
- paper card §C43-H, equations 24.53--24.56.
- report §9.3, equations 9.3.65--9.3.67.

## Selberg anchor/mass horizon mismatch

- Corpus small-value theorem requires log(z/y)>40/delta+2 to find |R(m)|<=delta*m+log z+1.
- Critical target delta=X^(-1/2+epsilon) at X=exp(h) therefore needs log-window width
  >40 exp((1/2-epsilon)h)+2, exponential in log-time.
- Every mass/outgoing/Bessel cone has only O(h) log horizon. In such a window theorem can force
  only delta=Omega(1/h), leaving normalized error exp(h/2)/h and type 1/2.
- Pointwise gain-window and slow variation cannot repair this exponential horizon deficit.
  New signed cancellation must change reciprocal 1/delta resolution law.

Files extended:
- paper card §C43-I, equations 24.57--24.60.
- report §9.3, equations 9.3.68--9.3.70.

## Harmonic resolvent, mass horizon, and parabolic heat closure

Paper-only; no Lean writes/builds.

- C43-J--M: harmonic primitive/adjoint conserves critical exponent at every finite depth; exact critical Mellin resolvent is `-(1/2-i xi)^(-1)`, inverse of outgoing mass symbol. Smooth Bessel phase gauges are local Mellin twists and type-rigid.
- C43-N--O: moving critical mass diagonal is type zero but quotient-null. Smooth arithmetic connections are type-rigid; exact node connections are rank-one/local; approximate many-prime connections require RH-strength estimates.
- C43-P--Q: exact square-root mass information horizon. `a^2/u->infinity` erases each off-line orbit; `a^2/u->0` preserves it. Finite conjugation-stable packets separate by Cesaro chirp mean square for `a=u^theta`, `1/3<theta<1/2`; full-tail bridge remained.
- C43-R--S: parabolic blow-up of massive half-wave is Gaussian heat on `w=alpha^2`; exact positive subordination kernel
  `K_(a,t)(s)=at/sqrt(pi) s^(-3/2) exp(-a^2(s-t)^2/s)`.
  Mass jet `L_a=partial_tau^2-a^2` recovers polynomial-square heat filters exactly. Integral Lipschitz theorem reduces to integer polynomials and rational positive times.
- C43-T--V: literal Euler-line parabolic source, Hermitian/orientation split, and exact budget
  `D_P=G_P-Re H_P=2 sum exp(-tA)[Im(P(w)e^(-itB/2))]^2`.
  For `P=1`, `D_1=sum exp(-tA)(1-cos(tB))`; vanishing all times iff RH.
- C43-W: hostile audit repaired completed arch source to
  `1/s+1/(s-1)+Gamma_R'/Gamma_R`. Critical contour shift produces positive polar residue and exact split
  `Re H_P=2e^(t/4)P(-1/4)^2+(1/pi)int F gammaHardyPhaseRate-(1/pi)sum Lambda(n)/sqrt(n) Fhat(log n)`.
- C43-X: fixed-degree prime jet is superexponentially invisible as `t->0`; heat-Hankel moments converge after anisotropic scaling to strictly positive Gaussian moment matrix. Every fixed degree has unconditional small-time positivity.

## Oscillator wedge and filtered-Turan route

- C43-Y: Mehler diagonal bound plus Gaussian imaginary translation proves universal parabolic wedge:
  `exists eta>0, t(d+1)<=eta => Re H_P(t)>0` for every nonzero `deg P<=d`.
  Core estimates:
  central Gamma-negative mass fraction `O(sqrt(t(d+1)))`;
  `|Fhat(xi)|/int F <= exp(-xi^2/(4t)+2sqrt(d)|xi|/sqrt(t))`.
- C43-Z: RH is equivalent to every polynomial-filtered adjacent Turan curvature
  `Delta_Q=H_(Q,0)H_(Q,2)-H_(Q,1)^2=H_Q H_Q''-(H_Q')^2 >=0`.
  Converse: kill lower real shells by real finite interpolation; bottom nonreal shell has negative recurrent normalized determinant; shell gap kills tail.
  Each `H_(Q,k)` has exact repaired prime--Gamma formula with test `x^(2k)Q(x^2)^2e^(-tx^2)`.
- C43-AA: coefficient-uniform prime information cone. For `N=2degQ+k`,
  `|Fhat_(Q,k)(xi)| <= M exp(-xi^2/(4t)+sqrt(2N)|xi|/sqrt(t))`.
  Beyond `log n >= log2+16sqrt((d+k+1)t)+32t`, complete prime tail is
  `O(M exp(-L^2/(16t)))`. Probe sees only `n<=exp(O(t+sqrt(dt)))` up to certified tail.
- C43-AB: independent-prime covariance route fails exactly. For `Q=1`, one-frequency curvature is
  `pi(t-xi^2)/(2t^4) exp(-xi^2/(2t))`, negative for `xi^2>t`.
  `GammaConductorSchurCapacity` additionally gives nonsummable independent-prime scalar conductor cost. Survivor is coherent double-prime kernel plus mixed polar--Gamma covariance.
- C43-AC: RH iff every real polynomial-filtered heat trace is eventually log-convex. Bottom-shell Cesaro law:
  `lim_T T^(-1) int_1^T e^(2At) Delta_Q(t) dt
    = -(1/2) sum_(B_j+B_k=0)(B_j-B_k)^2 <0`
  under first off-line filtered shell.
- C43-AD: shell-adaptive real filters can be rationalized with error `e^(-ct)`; clearing denominators gives fixed-degree integer filters of height `e^(O(t))`. Countable RH criterion: for every fixed degree and coefficient exponent, eventual Turan positivity uniformly inside integer height cone `ht(Q)<=e^(Ct)`.
- C43-AE: finite-degree shell ladder. If first `d+2` distinct squared shells are critical then every nonzero degree-`d` filtered curvature is eventually strictly positive; conversely that eventual property forces first `d+1` shells critical. One-shell gap is exact interpolation budget, especially for mixed on/off-line shell.

Current exact source target:
- Prove coherent completed curvature
  `(A0-P0)(A2-P2)-(A1-P1)^2>=0`
  eventually and uniformly on every fixed-degree exponential-height integer cone.
- Prime information radius and coefficient-conditioning radius are both `exp(O(t))`.
- Diagonal KMS/passive, independent-prime Schur, termwise prime sign, norm-first, scalar transport, finite primitive, and fixed causal routes are closed.
- Newest relevant corpus: `XiGaussianHeatHankelLadder`, `XiHeatTuranBottomDetection`, `XiPrimeGammaContourTuranBottomShellUniversalityLaw`, `FiniteHermiteCRT`, phase recurrence, `GammaConductorSchurStrictDefiniteness`, `GammaConductorSchurCapacity`, `PrimeLogKMSHermitianCompletion`.
- C43-AF: large-time source superresolution wall. Prime saddle is at `log n=t` because
  `L/2-L^2/(4t)=t/4-(L-t)^2/(4t)`; continuous main is `2pi e^(t/4)`, canceling polar residue.
  Surviving shell signal is `e^(-At)`, but PNTPlus leaves `e^(t/4-c t^(1/10)) poly(t)`.
  Eventual curvature cannot follow from modulus PNT or finite saddle expansion; exact coherent
  prime--polar--Gamma cancellation before norms is mandatory.
- Closest literature found: arXiv:1904.12438 (de Bruijn--Newman heat flow), arXiv:1910.01227
  (Jensen polynomials), arXiv:2607.16795 (coefficient-side Toeplitz wedge); no matching
  divisor-heat filtered-Turan/prime-information-cone statement located.
- C43-AG: for every moving polynomial heat jet, `U=2log|P(z^2)|-t Re(z^2)` is subharmonic on `|Im z|<1/2`; half-density contour shift makes prime source its boundary envelope. Absolute polynomial-jet/PNT routes are closed; only signed boundary cancellation survives.
- C43-AH: any absolutely convergent positive conic sum in `R^3` compresses exactly to at most three original rays. Therefore complete prime moment packet `(P0,P1,P2)` equals at most three actual prime-power feature vectors with positive aggregate weights before Lorentz determinant. Infinite per-prime Schur conductor divergence is not intrinsic.
- C43-AI: for `Q=1`, coherent prime curvature is `M_t^2/(16t^4) * (Var_mu((log n)^2)+8t^2-8t E_mu((log n)^2))`. Continuous saddle `log n ~ N(t,2t)` makes bracket exactly zero. New target is completed prime--Gamma Gaussian Stein identity; PNT modulus still exponentially underresolved.
- C43-AJ: reflected Meyer countertransport `G_c` with capacity <=2 Gaussian-averages exactly to parabolic heat source. Heat jets have integral capacity bound `sum |q_k| C_k tau^(-k)` proved by differentiated Gaussian kernels before any evaluation continuity. Turan is 2x2 reflection Gram on this cyclic source cone; generic evaluation continuity remains RH-equivalent.
- C43-AK: new corpus Gaussian line Wronskian equals horizontal displacement times positive Gaussian density and is in divisor `ell^2`. Its norm is `pi^-2 sum delta_q^2 exp(-Re(w_q)/pi)`. For isolated line-conjugate pair at `T=1/(2pi)`, filtered Turan defect equals `-8pi^2 gamma^2 |Q(w)|^4` times pair Wronskian energy. Global cross-shell terms block direct norm identity; surviving avenue is line-reflection-invariant arithmetic factorization of moment/zero-jet exterior determinant.
- Files extended through card equations (24.163)--(24.179) and report (9.3.146)--(9.3.155). No Lean writes/builds/computations.


