# Hyperbolic multiplier lifting: facts and boundaries

Research scope: independent BiScale Uncertainty. Original target remains transfer to
the odd secant/plastic functional and the supplied 100-contribution research program.
Supporting lemmas, documentation repairs, and classical inequalities are not separate
contributions. Four substantive results are Lean verified: compensated multiplier Gram
transfer (13 public theorems), uncompensated squared-jump transfer into global secant
energy (19), the actual signed plastic crossover receiver (18), and the exact smooth odd
fixed-energy leakage family (12). Supporting theorem
counts are not contribution counts. No literature-priority claim.

## Exact laws

- Write C=C_(1/2)f and S=S_(1/2)f. Then h_f(x) sech(x/2)
  =(h_C(x)-h_S(x)) sech(x/2)^2. The scale is 1/2, not 1/4.
- R_C=R+R_S. At source zeros, h_C=h_S. Equality does not establish that
  either multiplier correlation is zero.
- For arbitrary nodes and real weights v,
  G_C(v,t)-G_S(v,t)=sum_(i,j) v_i v_j cosh((t_j-t_i)/2) h_f(t_j-t_i).
  On a source clique this difference is R sum_i v_i^2, while G_S remains a full Gram form.
- With x_i=t_i-y and v_i=b_i sech(x_i/2)^2, the compensated collar is
  L=sum_i [b_i h_f(x_i) sech(x_i/2)+v_i Delta_C(x_i)]. Exactly
  L=R_C sum_i v_i-sum_i v_i h_S(x_i), hence
  L >= R_C sum_i v_i-sqrt(R_S G_S(v,t)).
- The actual clique defect is D=G_S-R_S sum_i v_i^2; it need not be positive.
  When D=0, the lower bound is R sum_i v_i+
  R_S(sum_i v_i-sqrt(sum_i v_i^2)). Continuous collar weights allow integration
  over compact intervals. No zero-grid assumption is needed for the defect-aware theorem.
- Explicit robust clique transfer: L >= R W+R_S(W-sqrt(sum_i v_i^2))
  -sqrt(R_S max(D,0)). This displays the clique coefficient and the entire
  defect penalty separately. It requires no assumption on the sign or size of D.
- Arbitrary signed kernel samples k_i are admitted by taking b_i=k_i cosh(x_i/2).
  The companion then has weight k_i/cosh(x_i/2). This is a finite-collar receiver
  for the actual plastic kernel. The third bridge below now gives a global bound through
  the exact positive-remainder decomposition, with the signed moment retained.

## Failed inferences and survivors

- **Inherited clique zeros:** Pillar VI supplies equality of multiplier correlations,
  not multiplier blindness. The smooth odd family below now proves failure at the actual
  lag log(2), with fixed original energy and unbounded multiplier leakage. Survivor:
  its exact hyperbolic growth law and positive weighted packet invariant; retain G_S
  and its defect or additional position/moment data. Full infinite-grid blindness
  remains outside this counterexample's scope.
- **Lower increment bound has the wrong sign:**
  Delta_f sech=R(sech-sech^2)+(Delta_C-Delta_S)sech^2.
  A lower bound on Delta_S alone therefore cannot be substituted as a lower bound
  for Delta_f. Survivor: compensated secant correlation transfer with the cosine
  increment retained. The squared-jump identity below supplies independent support-based
  control and removes that companion in a bound for the actual secant increment.
- **Secant is not plastic:** the actual plastic kernel is piecewise
  `levyCoshKernel`, with a signed pairing involving `2 cosh - levyCoshKernel`.
  Kernel resemblance does not identify the two functionals.
- **Contribution counting:** four field-specific results, not one contribution per
  declaration. Cauchy–Schwarz and ground-state representation are classical mechanisms.
  External novelty is unestablished; exact-phrase search was inconclusive.

## Uncompensated transfer: exact facts

- For every real compact continuous f and every real alpha,x, writing g(u)=sinh(alpha u)f(u),
  integral sinh(alpha u)sinh(alpha(u+x))[f(u)-f(u+x)]^2 du
  =2[cosh(alpha x)h_g(0)-h_g(x)]. The multiplier product may be negative pointwise.
- Choose B>0 from the actual compact source support. With S=S_(1/2)f and
  K_B(x)=sinh(B/2)sinh((B+|x|)/2)>0,
  cosh(x/2)R_S-h_S(x) <= K_B(x)[R-h_f(x)]. There is no cosine companion
  or additive commutator error; the support factor remains.
- For x_i=t_i-y, arbitrary real b_i, v_i=b_i^2 sech(x_i/2)/K_B(x_i),
  and G_S(v,t)=sum_(i,j) v_i v_j h_S(t_j-t_i),
  sum_i b_i^2[R-h_f(x_i)]sech(x_i/2)
  >= R_S sum_i v_i cosh(x_i/2)-sqrt(R_S G_S(v,t)).
  With A=sum_i v_i^2 and D=G_S-R_S A, a further explicit lower bound is
  R_S[sum_i v_i cosh(x_i/2)-sqrt(A)]-sqrt(R_S max(D,0)).
  No zero-grid or parity premise is imposed. Actual multiplier cliques have D=0.
- The source secant integrand satisfies 0<=F(x)<=4R exp(-x/2), so it is integrable
  on (0,infinity) for C_c sources without differentiability. For d=|delta|,
  t_k=kd, k<n, b_k=1, the integral from 0 to d of the full-Gram bound at offset
  -y is at most J_sech(f). Proof uses exact tiling into [0,nd] and nonnegativity.
  This is the full original secant energy. The third bridge below transfers it into the
  distinct plastic functional without identifying their kernels.
- The new support factor does not control multiplier blindness or eliminate the measured
  Gram defect. An odd source makes S even; it does not add a zero-grid conclusion.

## Verification and next mathematical question

Paper proof and scope: `docs/drafts/pipeline/1-in-progress/hyperbolic-multiplier-lifting-2026-10-17.md`.
Implementation: `formal/GaloisForLFunctions/BiScaleUncertainty/HyperbolicMultiplierGramTransfer.lean`.
Final direct-source compilation passed without warnings. All 13 theorem axiom audits
returned only `propext`, `Classical.choice`, `Quot.sound`. Source SHA256:
`12ec9a1f19c416d8d0601c1c1e133880318a69cb43d84e3a133034fd8b387444`.
The module is imported by the BiScale umbrella and indexed. Global lint failed on
unreachable concurrent modules `AsymptoticTailCoercivityAndNyquistTrap5Closure`,
`MultiCosetGramPackingAndNyquistDensity`, `ProducerConsumerDualityAndNymanBeurlingBridge`,
plus concurrent `LEAN_API.md`/`LEAN_OVERVIEW.md` drift. Do not alter others' unfinished
modules to conceal that status. Exact commands and audit scope are on the paper card.

Second implementation: `formal/GaloisForLFunctions/BiScaleUncertainty/HyperbolicJumpEnergyTransfer.lean`.
Direct actual-source compilation passed without warnings. All 19 public theorem axiom
audits returned only `propext`, `Classical.choice`, `Quot.sound`. Source SHA256:
`56fb077bbe28fbae0d143d8a62f68db8bbcc87c5c3c941c2e0b43feea856e2b4`.
Module imported by the BiScale umbrella; index refresh passed. Current global lint
outcome is recorded on the master card.

Third implementation: `formal/GaloisForLFunctions/BiScaleUncertainty/PlasticCrossoverGramReceiver.lean`.
Actual-source compilation passed without warnings. All 18 public theorem axiom audits
returned only `propext`, `Classical.choice`, `Quot.sound`. Source SHA256:
`c34e886a83d099242571f9bdcb2b4e49fd3841608fad2448b9615e2ee49cd923`.
Umbrella import and index refresh completed; current global lint status is on the master card.

Remaining questions: control actual sine Gram leakage under logarithmic source zeros,
quantify or remove support dependence, and compare the negative odd sine moment with
the now-separated positive secant and plastic remainder energies. The cosine companion
is removed, and the actual signed plastic receiver is established with that moment retained.
The fourth result excludes source-energy-only leakage estimates from odd parity and a
single logarithmic zero. Test source-centered weighted identities or stronger zero-grid
constraints before seeking a uniform replacement for actual Gram data.

## Actual plastic crossover: exact facts

- At c*=screwSignThreshold>0, k(x)=levyCoshKernel c* x and V=levyCoshPotential c*.
  For E=integral f cosh(u/2), O=integral f sinh(u/2),
  P(f)=V R+integral_(u,v) f(u)f(v)[2cosh((u-v)/2)-k(|u-v|)]
  =2 integral_(x>0) k(x)[R-h_f(x)]dx+2(E^2-O^2).
  Actual compact continuity discharges every pair/jump integrability obligation.
- The exact excess weight 2k(x)-sech(x/2) is 4cosh(x/2)-sech(x/2) for x<=c*
  and archDualLevySinhWeight x for x>c*. Both are positive. Thus
  P=J_sech+R_plastic+2(E^2-O^2), R_plastic>=0, with R_plastic the source increment
  integrated against that excess. The general jump and moment identities were already
  corpus results; this assembly is the bridge, not a new claim for those ingredients.
- Every verified disjoint-collar sine Gram lower bound L<=J_sech gives
  L+R_plastic+2(E^2-O^2)<=P, hence L+2(E^2-O^2)<=P.
  For any origin coefficient a, aR+L+2(E^2-O^2) is a lower bound on the full
  original expression (a+V)integral f^2 plus the signed residual pair integral.
- F(u)=[f(u)-f(-u)]/2 constructs a compact odd source from arbitrary compact data.
  Its cosine moment is zero, S_(1/2)F is even, and the receiver becomes
  L(F)-2[integral F sinh(u/2)]^2<=P(F), including the analogous origin-coefficient form.
  This neither assumes multiplier clique zeros nor erases the odd sine moment.
- Odd parity cancels E; the current proof does not establish nonnegativity of the signed
  pairing. The theorem retains the negative moment; positivity or a
  uniform all-grid domination of that moment is not established here.

## Exact smooth odd leakage family

- Reuse the existing even smooth packet phi from
  `formal/GaloisForLFunctions/RHTower/EvenSectorSmoothBlindInterpolationObstruction.lean`.
  Its mass m=h_phi(0)>0 and support diameter is below d/10, d=log(2)>0.
  All new source code is in BiScaleUncertainty; the packet module is unchanged.
- For t=|T|, take coefficients (-1,1,1) at (t+d,t+2d,t+3d) and opposite coefficients
  at their negatives. This constructs an actual compact smooth odd source f_T.
  Six supports are disjoint; exactly four signed overlaps survive at lag d.
- For every real T, h_fT(0)=6m and h_fT(d)=0. Define the fixed positive invariant
  M=integral cosh(u)phi(u)^2 du>=m>0. The exact multiplier law is
  h_(S_(1/2)fT)(d)=2 sinh(|T|+2d)sinh(d/2)M>0.
- For every real A, a constructed member satisfies
  h_(S_(1/2)fT)(log 2)>A h_fT(0), while its energy remains 6m and its source
  correlation at log(2) remains zero. The proof uses sinh(x)>=x for x>=0;
  no numerical computation or asymptotic premise is used.
- This invalidates inherited multiplier zeros and any uniform source-energy-only
  leakage bound on this source class. The positive survivor is the exact growth law
  and weighted mass M. Only one logarithmic source zero is imposed; no conclusion
  about the full infinite prime grid or source moment cancellation is asserted.
- Classical packet separation and hyperbolic addition are reused mechanisms.
  The contribution is this actual odd logarithmic-zero family with its fixed source
  energy and exact unbounded multiplier leakage, counted once. External priority is
  unestablished.

Fourth implementation: `formal/GaloisForLFunctions/BiScaleUncertainty/OddMultiplierLeakageFamily.lean`.
Final direct actual-source compilation exited 0 without warnings. Source SHA256:
`fd8f41743e0b8a24bb2a4ebd43594b172a93ffef3c3066c9a631afedaa500ef0`.
Theorems `source_sinh_autocorr_lag` and `exists_odd_logZero_large_sinhCorrelation`
state the exact law and unconditional unboundedness. Audit results are on the master card.

Serena ignores Lean paths in this project; direct symbol lookup returned that error.
Use inspected source plus apply_patch. Keep one owned foreground Lean process at a time.
