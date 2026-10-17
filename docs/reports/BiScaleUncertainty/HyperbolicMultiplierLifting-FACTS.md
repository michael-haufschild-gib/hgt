# Hyperbolic multiplier lifting: facts and boundaries

Research scope: independent BiScale Uncertainty. Original target remains transfer to
the odd secant/plastic functional and the supplied 100-contribution research program.
Supporting lemmas, documentation repairs, and classical inequalities are not separate
contributions. Eight substantive results are Lean verified: compensated multiplier Gram
transfer (13 public theorems), uncompensated squared-jump transfer into global secant
energy (19), the actual signed plastic crossover receiver (18), the exact smooth odd
fixed-energy leakage family (12), the centered source-Gram replacement with its
full secant/plastic receiver (15), the source Schur envelope with its all-center
comparison, exact clique boundary and full receiver (16), arithmetic collision
control with its doubled-zero/dyadic specialization and full receiver (24), and the
uniform dyadic multiplier frame with explicit source errors and full receiver (19). Supporting theorem
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
- **Contribution counting:** eight field-specific results, not one contribution per
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
The module is imported by the BiScale umbrella and indexed. Global lint depends on
concurrent work; the latest snapshot, exact commands and audit scope are on the paper
card. Do not alter others' unfinished modules to conceal that status.

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

Remaining questions: quantitatively dominate source-variance and collar-support costs
by the positive secant and plastic remainder energies. The coherent-packet estimate
below replaces the independent negative odd moment by actual source data, with a
support-radius-free moment penalty on the full logarithmic source grid. This does
not prove positivity of the complete functional or remove the collar support factor.
The cosine companion is removed and the actual signed plastic receiver is established.
The fourth result excludes source-energy-only leakage estimates from odd parity and a
single logarithmic zero. The fifth supplies exact centered weighted control of the
multiplier defect; the sixth removes source-parallel packet cost and proves that mean
centering already minimizes the entire envelope on source cliques. Uniform coercivity
still requires stronger information about source variance. The seventh result now
reduces the arithmetic difference-node Gram exactly to weighted collision energy
under a doubled source-zero range, supplied by full logarithmic blindness on dyadic chains.

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
state the exact law and unconditional unboundedness. All 12 public theorem axiom audits
returned only `propext`, `Classical.choice`, `Quot.sound`. Umbrella wiring and index refresh
passed. Latest global lint status is on the master card.

## Centered source-Gram control and actual receiver

- For F=oddCompactSource f, arbitrary real alpha,c, and q_c(u)=(cosh(2alpha u)-c)F(u),
  the exact odd-reflection identity is
  integral q_c(u)F(u+x)du=2cosh(alpha x)h_(S_alpha F)(x)
    +[cosh(alpha x)^2-c]h_F(x).
  All sources are constructed from actual compact continuous data.
- For ordered off-diagonal node pairs P, d_ij=t_j-t_i and
  a_ij=v_i v_j/[2cosh(alpha d_ij)], write
  E_c=sum_P a_ij[c-cosh(alpha d_ij)^2]h_F(d_ij),
  Q_c=h_(q_c)(0), and G=translationGramEnergy F P a d. Then
  D=E_c+integral q_c(u)[sum_P a_ij F(u+d_ij)]du and
  |D-E_c|<=sqrt(Q_c G). Hence D<=U_c=E_c+sqrt(Q_c G).
  This controls every multiplier off-diagonal contribution using original source
  correlations and one actual weighted source energy. No support radius enters this
  defect bound. On a source clique E_c=0; the pair-difference Gram remains full.
- With R=h_F(0), M=integral cosh(2alpha u)F(u)^2 du and
  W=integral cosh(2alpha u)^2 F(u)^2 du,
  Q_c=W-2cM+c^2 R and R Q_c=(Rc-M)^2+V, V=RW-M^2>=0.
  The exact minimizer identity is Q_(M/R)+R(c-M/R)^2=Q_c, including R=0.
  Minimizing Q_c alone need not minimize U_c when E_c depends on c.
- At alpha=1/2 and the existing source-derived transfer weights v_i, replace D by
  U_c in the uncompensated penalty:
  B_c=R_S[sum_i v_i cosh((t_i-y)/2)-sqrt(sum_i v_i^2)]
      -sqrt(R_S max(U_c,0)). This is below the existing full-Gram bound and original
  secant jump collar. Continuity permits integration over the disjoint arithmetic
  collars, yielding integral B_c<=J_sech(F) and
  integral B_c+R_plastic(F)-2[integral F(u)sinh(u/2)du]^2<=P(F).
  Actual multiplier origin energy remains; every off-diagonal multiplier sample has
  been replaced by explicit source data. The jump envelope still uses source support.
- General difference-Gram geometry and weighted variance growth still require control
  beyond the arithmetic/dyadic specializations below. Repeated nodes, signed weights,
  zero source energy and zero-length collars require no added hypotheses.
- The corpus's integral Cauchy--Schwarz and packet Gram identities are reused.
  The fifth contribution is their exact parity-dependent source representation and
  transfer into the actual receiver, counted once. No literature-priority claim.
- Concurrent `HyperbolicMultiplierIncrementAndOddSignCoercivity.lean` gives joint
  increment and signed-collar estimates retaining multiplier samples; its actual
  statements do not supply this centered source replacement or establish full odd
  positivity. It is not counted among this work's contributions.

Fifth implementation: `formal/GaloisForLFunctions/BiScaleUncertainty/CenteredHyperbolicGramControl.lean`.
Actual-source compilation exited 0 without warnings. All 15 public theorem axiom audits
returned only `propext`, `Classical.choice`, `Quot.sound`. Source SHA256:
`943a494e19a78335bbc2bb288adf016474e44c5ea747a3937528aa39a529f85e`.
Main results are `CenteredHyperbolicGram.odd_defect_abs_sub_correction_le`,
`centered_energy_minimizer`, `odd_secantEnergy_ge_centered`, and
`odd_plasticCrossover_ge_centered`. Current global lint status is on the master card.

Serena ignores Lean paths in this project; direct symbol lookup returned that error.
Use inspected source plus apply_patch. Keep one owned foreground Lean process at a time.

## Source Schur envelope and exact clique-centering boundary

- With the same difference packet P=sum a_p F(.+d_p), put R=h_F(0),
  K=<F,P>=sum a_p h_F(d_p), G=||P||^2, mu=M/R, and Q=||q_mu||^2.
  The actual centered source is orthogonal to F. If R=0, the existing variance
  and packet Cauchy--Schwarz inequalities force M=K=0, so every formula below
  remains valid with ordinary real division and no nonzero-energy premise.
- The actual compact packet P_perp=P-(K/R)F has energy H=G-K^2/R>=0.
  Its pairing with q_mu equals that of P. Therefore
  |D-E_mu|<=sqrt(Q H), and D<=U_perp=E_mu+sqrt(Q H).
  This uses actual source correlations and weighted source energy; every repeated
  difference and cross correlation remains in G.
- For every real center c, E_c=E_mu+(c-mu)K and Q_c=Q+R(c-mu)^2.
  The scalar square identity (a^2+x^2)(b^2+k^2)-(ab-xk)^2=(ak+xb)^2 proves
  U_perp<=E_c+sqrt(Q_c G). Thus the new envelope is at least as strong as
  every earlier scalar-centered envelope, including signed correlations.
  This is a comparison theorem, not a claim that its infimum is always attained.
- At alpha=1/2, using U_perp in the uncompensated penalty gives a continuous
  lower bound dominating every centeredJumpBound. Integrating the existing
  disjoint arithmetic collars gives a bound for J_sech and for
  P(F), retaining R_plastic(F)-2O(F)^2 and the source-support jump factor.
- **Exact boundary:** source clique zeros force K=E_c=0 for every c.
  Hence U_perp=U_mu, and U_mu<=U_c for every c: scalar mean centering already
  minimizes the whole envelope on a clique. Projection onto F cannot improve it
  further. Do not infer that the remaining difference-node Gram is diagonal.
  Failed extra-clique-gain inference and positive survivor are closed in
  `docs/drafts/pipeline/5-failed/source-line-projection-extra-clique-gain-2026-10-17.md`.
- The residual weighted variance, support factor and negative odd moment remain.
  The arithmetic difference-node Gram is now controlled by the seventh result
  below; arbitrary node geometry remains outside that doubled-range specialization.
- Classical projection and Cauchy--Schwarz are supporting mechanisms. The exact
  multiplier-envelope comparison, clique boundary and actual functional receiver
  form one contribution. No literature-priority claim.

Sixth implementation: `formal/GaloisForLFunctions/BiScaleUncertainty/ProjectedHyperbolicGramControl.lean`.
Actual-source compilation exited 0 without warnings. All 16 public theorem axiom
audits returned only `propext`, `Classical.choice`, `Quot.sound`. Source SHA256:
`27a0251e688b257952cca194ea612814c5c73f5b9e1e3a01349932f9411b0384`.
Main namespace `ProjectedHyperbolicGram`; capstones `projectedDefectUpper_le_every_center`,
`sourceClique_centering_boundary`, `odd_secantEnergy_ge_projected`, and
`odd_plasticCrossover_ge_projected`. Six contributions, 93 public supporting theorem
audits in total. Latest global lint status is recorded on the master card.

## Arithmetic collision law and doubled source-zero range

- For N+1 nodes t_i=i delta, real weights v_i, and slots r=0,...,2N, set
  d_r=(r-N)delta and
  b_r=sum_(i!=j, N+j-i=r) v_i v_j/[2cosh(alpha d_r)]. The actual source
  difference packet equals sum_r b_r F(.+d_r). Its central amplitude b_N=0.
  Equal integer differences are combined before squaring, for signed weights too.
- For 1<=k<=N,
  b_(N+k)=[sum_(i=0)^(N-k) v_i v_(i+k)]/[2cosh(alpha k delta)].
  Uniform v_i=1 gives (N+1-k)/[2cosh(alpha k delta)]. Thus multiplicity is
  coherent; the collision cost is not the sum of individual pair squares.
- Define A=sum_r b_r^2 and
  Z=sum_(r!=s) b_r b_s h_F((s-r)delta). Exactly G=R A+Z. The source
  covariance and correction also coalesce into K=sum b_r h_F(d_r) and
  E_c=sum b_r[c-cosh(alpha d_r)^2]h_F(d_r). No zero is assumed.
  R A+Z-K^2/R is nonnegative, being the actual source Schur energy.
- If the original source has h_F(m delta)=0 for 1<=m<=2N, the existing
  arithmetic-clique theorem proves Z=0; the same source zeros give K=E_c=0.
  The exact identity Q_mu R=V, V=RW-M^2, then gives |D|<=sqrt(V A).
  This discharges the difference-Gram orthogonality from explicit source zeros;
  it never assumes inherited multiplier zeros. The theorem proves sufficiency
  of this doubled range, not that it is minimal under every weight pattern.
- For the canonical odd source F, h_F(log n)=0 for all n>=2 supplies the
  required dyadic zeros by n=2^m. This is a local source-grid specialization;
  no implication from arbitrary input data to source blindness is asserted.
- The unconditional collision envelope is
  E_mu+sqrt(Q_mu[R A+Z-K^2/R]). It equals the established projected envelope.
  At alpha=1/2 it transfers into the full original secant/plastic receiver for
  actual compact sources, with all cross-lag errors, positive plastic remainder,
  support factor and negative odd moment retained. Under doubled zeros the
  collar leakage penalty is exactly sqrt(R_S sqrt(V A)).
- All unconditional identities include delta=0, N=0 and R=0. When delta=0,
  different integer slots may represent the same real displacement; Z retains
  those additional correlations. The doubled-zero specialization at delta=0
  forces zero source energy whenever its range is nonempty.
- The uniform dyadic collision problem is resolved below: A<=2(sum v_i^2)^2
  yields a multiplier frame radius from actual source variance. The coherent-packet
  theorem then replaces the separate odd moment by a source-data budget. Quantitative
  domination of variance and collar-support costs remains open.
- Existing finite-train lag grouping, arithmetic clique orthogonality and
  Cauchy--Schwarz are reused. Exact multiplier collision control and the actual
  receiver count as one contribution. No literature-priority claim.

Seventh implementation: `formal/GaloisForLFunctions/BiScaleUncertainty/ArithmeticMultiplierCollisionControl.lean`.
Actual-source compilation exited 0 without warnings. All 24 public theorem axiom
audits returned only `propext`, `Classical.choice`, `Quot.sound`. Source SHA256:
`ea5f7325683aa67f27d59ecaf8319b851f675324abc2a95cab2c3c87f46abaf8`.
Main namespace `ArithmeticMultiplierCollisions`; results
`differenceGram_eq_collision_add_error`, `odd_defect_abs_le_variance_collision`,
`odd_logGrid_defect_abs_le_variance_collision`, `odd_plasticCrossover_ge_collision`.
Seven contributions, 117 public supporting theorem audits in total. Latest global
lint status is on the master card.

## Uniform dyadic multiplier frame and actual receiver

- At alpha=1/2 and d=log2, W2=sum_(i=0)^N v_i^2, the arithmetic lag amplitudes
  obey b_(2N-r)=b_r, b_N=0 and
  A=2 sum_(k=1)^N b_(N+k)^2. Aperiodic Cauchy--Schwarz and
  [2cosh(kd/2)]^2>=2^k give A<=2 W2^2 for arbitrary signed v and every N.
- For actual odd F, R=hF0, M=int cosh(u)F^2, W=int cosh(u)^2 F^2 and
  V=RW-M^2>=0, the doubled source-zero range hF(md)=0, 1<=m<=2N gives
  |G_S(v)-R_S W2|<=sqrt(2V) W2. Consequently
  G_S(v)<=(R_S+sqrt(2V))W2, with frame constant independent of chain length.
  Full logarithmic blindness supplies the zero range. Multiplier zeros are not used.
- For every actual compact odd source, retain Q=||q_mu||^2, E_mu and Z from
  the arithmetic collision law. Since QR=V,
  Q(RA+Z)<=2V W2^2+Q max(Z,0). Thus the unconditional frame upper bound is
  G_S(v)<=U=(R_S+sqrt(2V))W2+E_mu+sqrt(Q max(Z,0)).
- With v_i(y)=sinhJumpTransferWeights F b (i*d) y i, define
  L(y)=R_S sum_i v_i(y)cosh((i*d-y)/2)-sqrt(R_S max(U(v(y)),0)).
  Then L(y)<=secantJumpCollar F (range(N+1)) b (i*d) y. All coefficients
  are continuous; for b=1, integral_(0..d) L(-y)dy<=J_sech(F), and
  integral_(0..d) L(-y)dy+R_plastic(F)-2(int F(u)sinh(u/2)du)^2<=P(F).
  These full receivers are unconditional on actual compact input and N.
- Doubled source zeros cancel E_mu and Z exactly, reducing the collar penalty to
  sqrt(R_S (R_S+sqrt(2V))W2). N=0, signed weights and zero-energy sources are covered.
- This replaces measured collision structure by a uniform radius. It may be
  weaker than exact collision/Schur control. The radius depends on source position
  through V; no removal of source support, negative-moment control, universal
  positivity, or optimal numerical constant is proved.
- Corpus audit: 460 declarations in 71 modules, hybrid partial67.40s; text/source
  retrieval unfinished and semantic coverage unmeasured. Existing profile-stable
  dyadic frames retain actual operator error; this result supplies a source-variance
  radius and full original-functional transfer. Finite Cauchy--Schwarz, reflection
  and geometric summation are supporting mechanisms, not separate contributions.

Implementation: `formal/GaloisForLFunctions/BiScaleUncertainty/DyadicMultiplierFrameBound.lean`.
Actual-source compilation passed without warnings; source SHA256
`f40cd139089ff168e6522ece36565284fe7e62530df457e3b58256d0d9c5adec`.
Main namespace `DyadicMultiplierFrame`; capstones `dyadic_collisionEnergy_le`,
`odd_sinhGram_le_frame_of_double_zeros`, `odd_sinhGram_le_frameGramUpper`,
`frameJumpBound_of_double_zeros`, and `odd_plasticCrossover_ge_frame`.
All 19 public theorem axiom audits passed with only `propext`, `Classical.choice`,
`Quot.sound`. Eight contributions, 136 public supporting theorem audits in total.
The full 100-contribution goal remains active; latest global lint status is on the master card.

## Coherent packet mass controls the negative odd moment

- For every actual compact g, put d=log2, B=multiplierSourceRadius(g)+1 and
  P_N(u)=sum_(i=0)^N g(u+id). Its support lies in (-B-Nd,B], its integral is
  (N+1)int g, and its square integral is the actual uniform-weight Gram G_g(1).
  Hence (N+1)^2 (int g)^2<=(2B+Nd)G_g(1).
- For S=sinh(u/2)F and canonical odd F, O=int S is the exact negative-moment
  component in P(F)=J_sech+R_plastic-2O^2. Set U_N=frameGramUpper(F,N,1)
  and B=multiplierSourceRadius(S)+1. Then
  O^2<=M_N=(2B+Nd)max(U_N,0)/(N+1)^2, without source-zero assumptions.
  The full original functional satisfies I_K+R_plastic-2M_N<=P(F), where
  I_K=integral_(0..d) frameJumpBound(F,K,1,-y)dy. N and K are independent.
- Under full logarithmic source blindness, G_S(1)<=C(N+1) for every N,
  C=R_S+sqrt(2V). Thus (N+1)O^2<=(2B+Nd)C. An Archimedean integer-growth
  contradiction gives O^2<=dC, with no support-radius factor in this moment bound.
  Consequently I_K+R_plastic-2dC<=P(F) on the full logarithmic source grid.
- This eliminates the separate linear hyperbolic moment as an unbounded input
  to the receiver. Its replacement still costs source energy and weighted variance;
  the collar still uses source support. No universal positivity or optimality is claimed.
- Existing interval Cauchy--Schwarz, support/integral translation laws and the
  actual packet Gram identity are reused. The contribution is their source-variance
  odd-moment bound and actual plastic receiver, counted once. Corpus searches were
  partial57.36s (393 declarations/38 modules) and partial58.06s (442/84), with
  text/source retrieval unfinished and semantic coverage unmeasured.

Implementation: `formal/GaloisForLFunctions/BiScaleUncertainty/DyadicHyperbolicMomentControl.lean`.
Actual-source compilation passed without warnings; source SHA256
`a963bbb08e6d77c842f11009fef217ca83f783faf79a5f911bc1128f8dc8eef5`.
Main namespace `DyadicHyperbolicMoment`; capstones `odd_moment_sq_le_budget`,
`odd_plasticCrossover_ge_momentBudget`, `odd_logGrid_moment_sq_le_frame`, and
`odd_logGrid_plasticCrossover_ge_frame`.
