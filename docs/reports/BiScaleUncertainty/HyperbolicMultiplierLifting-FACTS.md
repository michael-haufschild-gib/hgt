# Hyperbolic multiplier lifting: facts and boundaries

Research scope: independent BiScale Uncertainty. Original target remains transfer to
the odd secant/plastic functional and the supplied 100-contribution research program.
Supporting lemmas, documentation repairs, and classical inequalities are not separate
contributions. Twenty-four substantive results are Lean verified: compensated multiplier Gram
transfer (13 public theorems), uncompensated squared-jump transfer into global secant
energy (19), the actual signed plastic crossover receiver (18), the exact smooth odd
fixed-energy leakage family (12), the centered source-Gram replacement with its
full secant/plastic receiver (15), the source Schur envelope with its all-center
comparison, exact clique boundary and full receiver (16), arithmetic collision
control with its doubled-zero/dyadic specialization and full receiver (24), and the
uniform dyadic multiplier frame with explicit source errors and full receiver (19), and
coherent-packet odd-moment control with its unconditional plastic receiver and logarithmic-grid
specialization (12), and the fourth-moment variational jump receiver with its exact
variance identity and full secant/plastic transfers (18), and the attained hyperbolic-ray
certificate with signed activation criterion and full receivers (16), and the unconditional
source-lattice multiplier frame, odd-moment penalty and full plastic receiver (16), and signed
coherent cancellation with its exact boundary law and sharper full plastic receiver (13), and
unbounded realized cancellation at fixed source energy with its full plastic transfer (13), and
the explicit coherent source-cancelling producer with its unconditional energy error and
sharper odd moment/plastic bound (10), and the exact finite coherent filter with
its signed Gram formula and unconditional moment/plastic transfer (14), and the quantitative
finite-filter lattice comparison with explicit unconditional plastic gain (11), and hyperbolic
variance rigidity with the exact strict-gain domain and full plastic certificate (13), and finite-filter
support escape with a strictly positive Schur residual and exact plastic correction (13), and the actual
folded-source variance with its exact coherent equality domain and full plastic correction (9), and
actual nonzero-mean coherent attainment with the optimal universal coefficient and full plastic transfer (12), and
the canonical fixed-annulus retraction preserving full odd coherent data and pricing the original plastic functional (14), and
the actual coherent kernel splitting, nonzero zero-fold family and unconditional plastic nonnegativity (25), and
exact source-realized plastic line minimization with coherent-data preservation and full gain transfer (21). Supporting theorem
counts are not contribution counts. No literature-priority claim.

Canonical overview: `formal/GaloisForLFunctions/BiScaleUncertainty/README.md`, read-only
by user instruction. Main results retain signed source correlations; source-grid zeros
appear only in secondary specializations. Research scope remains multiplier lifting.
Trap10 applies here through explicit compact-source producers and proved quantitative
energy errors before functional transfers. It does not redirect this topic to RH or
Chebyshev bounds. No independent analytic estimate may be left as a capstone premise.

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
- **Contribution counting:** fourteen field-specific results, not one contribution per
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

Remaining questions: optimize over all signed control vectors and quantitatively dominate
the source-variance/quadratic moment costs by positive original energies. The canonical
hyperbolic ray now has an explicit attained optimum and signed activation criterion.
The coherent-packet
estimate replaces the independent negative odd moment; the fourth-moment variational
receiver below removes the collar support-radius factor. On the full logarithmic
source grid neither penalty needs an explicit support radius. The source-lattice budgets
below now remove that grid hypothesis from the radius-free moment penalty as well.
This does not establish
positivity of the complete functional or extend the compact-source domain.
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
  domination of variance and the replacement quadratic control cost remains open.
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
All 12 public theorem axiom audits passed with only `propext`, `Classical.choice`,
`Quot.sound`. Nine contributions, 148 public supporting theorem audits in total.
The full 100-contribution goal remains active; latest global lint status is on the master card.

## Fourth-moment variational receiver replaces the collar support radius

- For every actual compact f and real alpha, let m(u)=sinh(alpha u), S=mf,
  R=||f||^2, R_S=||mf||^2 and T=||m^2 f||^2. The earlier source moments obey
  M=R+2R_S, W=R+4R_S+4T, hence the exact identity 4RT=V+4R_S^2.
  This identity includes zero-energy sources; no division by R is used.
- Put H(x)=T cosh(alpha x)^2+(T+R_S)sinh(alpha x)^2. For h=f-f(.+x)
  and w(u)=m(u)m(u+x), translation invariance and the symmetric endpoint identity
  give int w^2 h^2<=4H. Integrating (h-a*w*h)^2>=0 and using the exact weighted
  jump law gives Delta_f(x)>=2a[cosh(alpha x)R_S-hS(x)]-2a^2H(x), every real a.
  Compactness supplies integrability; no numerical support radius occurs.
- At alpha=1/2, nodes t_i, real b_i, signed controls a_i and x_i=t_i-y, set
  v_i=2b_i^2 sech(x_i/2)a_i and Q=sum_i 2b_i^2 sech(x_i/2)H(x_i)a_i^2.
  The actual collar is at least R_S sum_i v_i cosh(x_i/2)-sqrt(R_S G_S(v))-Q.
  The full actual Gram is retained; no sign condition on controls is needed.
- For canonical odd F on dyadic chains, replacing G_S by frameGramUpper(F,N,v)
  produces fourthFrameBound. Its continuous coefficients integrate to
  I4_N(a)<=J_sech(F), where I4_N(a)=integral_(0..log2) fourthFrameBound(F,N,a,-y)dy.
  Therefore I4_N(a)+R_plastic-2O^2<=P(F), unconditionally. The ninth finite
  moment budget gives I4_N(a)+R_plastic-2M_M<=P(F), again unconditionally.
- Full logarithmic source blindness gives the further actual receiver
  I4_N(a)+R_plastic-2log2(R_S+sqrt(2V))<=P(F). Neither the collar nor this moment
  penalty contains a support radius. The domain remains actual compact sources;
  source weighted variance and the quadratic control cost remain explicit.
- This trades a support envelope for measured quadratic energies. It need not
  dominate every earlier bound, and no universal positivity, optimal control or
  external-priority claim is made. Cauchy--Schwarz, completed squares and elementary
  hyperbolic identities are supporting mechanisms, not separate contributions.
- Corpus audit: 449 declarations/75 modules, hybrid partial47.97s; text/source
  unfinished, semantic coverage unmeasured, compiler freshness partial. Existing
  jump and Gram laws were read and reused; no corresponding fourth-moment
  variational receiver appeared in the returned candidates.

Implementation: `formal/GaloisForLFunctions/BiScaleUncertainty/FourthMomentJumpReceiver.lean`.
Actual-source compilation passed without warnings; source SHA256
`8d9747052621b15517162d5e00e039c667a1fb0de1c5af6c6495e54d5d159e24`.
Main namespace `FourthMomentJump`; capstones `fourthEnergy_variance_identity`,
`source_increment_ge_variational`, `odd_secantEnergy_ge_fourthFrame`,
`odd_plasticCrossover_ge_fourthFrame_momentBudget`, and
`odd_logGrid_plasticCrossover_ge_fourthFrame`.
All 18 public theorem axiom audits passed with only `propext`, `Classical.choice`,
`Quot.sound`. Ten contributions, 166 public supporting theorem audits in total.
The full 100-contribution goal remains active; latest global lint status is on the master card.

## Attained hyperbolic-ray certificate and signed activation

- For d=log2, x_i=id-y, c_i=cosh(x_i/2), define B=sum_(i=0)^N c_i^2,
  D=(1/2)sum_i H(x_i)c_i^3, U=frameGramUpper(f,N,c), and
  A=R_S B-sqrt(R_S max(U,0)). All signed source-frame errors remain in U.
- For canonical odd F, controls a_i=lambda*c_i^2/2 give weights v_i=lambda*c_i.
  Exact Gram scaling and the fourth-moment transfer imply
  lambda*A-lambda^2*D <= secantJumpCollar for every lambda>=0.
- The scale lambda*=max(A,0)/(2D) attains C=max(A,0)^2/(4D), and every
  nonnegative scale on this ray gives a bound <=C. This is a ray optimum;
  no claim of optimality over all control vectors.
- Degenerate sources need no assumption: T=0 forces R_S=0 by
  4RT=V+4R_S^2 and V>=0, so H=D=A=C=lambda*=0. If T>0, H>0 and the
  nonempty chain gives D>0. Consequently C is nonnegative and continuous in y
  for every fixed actual compact source, including T=0.
- Exact signed-source activation: C>0 iff A>0 iff
  R_S max(U,0)<(R_S B)^2. On a doubled source-zero chain, U=(R_S+sqrt(2V))B;
  if R_S>0 this becomes sqrt(2V)<R_S(B-1). Main receiver does not assume zeros.
- I_C=integral_(0..d) C(F,N,-y)dy <= J_sech(F), hence
  I_C+R_plastic-2O^2<=P(F), and I_C+R_plastic-2momentBudget(F,M)<=P(F),
  every independent N,M. Full logarithmic source blindness additionally permits
  the moment cost 2d(R_S+sqrt(2V)). Collar certificate has no support radius
  or free controls. The complete plastic functional need not be positive.
- The contribution discharges the free scale along a canonical geometric profile,
  supplies its exact activation boundary, and connects the explicit bound to the
  full original functional. Classical scalar quadratic optimization is supporting
  machinery, not another contribution. No external-priority claim.
- Corpus audit: 1037 declarations/83 modules, hybrid partial59.05s;
  text/source retrieval unfinished, semantic coverage unmeasured and compiler
  freshness partial. Existing fourth-moment, frame and allocation results reused.

Implementation: `formal/GaloisForLFunctions/BiScaleUncertainty/OptimizedHyperbolicRayReceiver.lean`.
Final actual-source compile passed without warnings; 324 lines, source SHA256
`862c9717d24a6f8a0f1efb03367e34432176d26340faf9656bc38be36167602c`.
Namespace `HyperbolicRay`; capstones `optimalScale_attains`, `odd_collar_ge_optimized`,
`optimizedCollar_pos_iff`, `odd_secantEnergy_ge_optimized`, and
`odd_plasticCrossover_ge_optimized_momentBudget`.
All 16 public theorem axiom audits passed with only `propext`, `Classical.choice`,
`Quot.sound`. Eleven contributions, 182 public supporting theorem audits in total.
Umbrella and index updated; canonical README unchanged. Full goal remains active;
latest global lint status is on the master card.

## Original-source lattice costs replace the moment blindness hypothesis

- For every actual compact f, the integer sequence h_k=h_f(k log2) has finite
  support. Its intrinsic mass Gamma=sum_(k in Z)|h_k| is therefore a finite
  real sum. No summability or chosen support-radius premise is supplied.
- With mu=sourceMean(f,1/2), Q=||q_mu||^2, define e_0=0 and
  e_k=(mu-cosh(k log2/2)^2)h_k/(2cosh(k log2/2)) for k!=0.
  Its intrinsic mass E=sum_Z|e_k| is finite too. Both sequences are even.
  Signed correlations are admitted explicitly; these costs use absolute values
  and can overpay cancellation.
- Finite lattice rows inject into Z. The symmetric Schur estimate yields
  sum_(i,j) w_i w_j k(j-i) <= (sum_Z|k|)sum_i w_i^2 for every even finite-support
  kernel k. Thus the exact sourceCorrection is <=E*W2, and the coalesced
  source difference Gram is <=Gamma*A_collision<=2Gamma*W2^2.
- Consequently canonical odd F satisfies G_S(w)<=C(F)*W2 for all chain lengths
  and arbitrary signed coefficients, where C=R_S+E+sqrt(2Q Gamma)>=0.
  This replaces source-grid blindness with quantified original-source data.
  No multiplier correlations or assumed frame bound enter the constant.
- Coherent packets obey (N+1)^2 O^2 <= (2B+N log2)C(N+1). Integer growth
  eliminates B and N, proving O^2<=log2*C(F) unconditionally. The optimized
  collar I_opt from the preceding result therefore gives
  I_opt+R_plastic-2log2*C(F)<=P(F), every actual canonical odd source.
  Neither the collar nor this moment penalty has an explicit support-radius factor.
- If all positive dyadic source samples vanish, Gamma=R and E=0. The exact
  identity Q*R=V recovers C=R_S+sqrt(2V), including zero-energy inputs.
  The earlier grid-bound constant is recovered exactly, not with a larger baseline.
- This is one contribution: a uniform multiplier frame and full moment/plastic
  receiver replacing the blindness hypothesis by finite intrinsic lattice costs.
  Classical Schur bounds and the packet limit argument are supporting machinery.
  Finite moment budgets can still be sharper; no universal plastic positivity,
  all-control optimum, noncompact extension or external-priority claim.
- Corpus searches: 835 declarations/85 modules, partial57.83s, and 599/93,
  partial78.38s. Text/source retrieval unfinished, semantic coverage unmeasured,
  compiler freshness partial. Actual centered/collision/frame, packet and Schur
  proofs were inspected and reused.

Implementation: `formal/GaloisForLFunctions/BiScaleUncertainty/SourceLatticeMultiplierFrame.lean`.
Final actual-source compile passed without warnings; 318 lines, source SHA256
`68a380d612b38045195d2f1aa62428ffeb050afe993bc7e72da5f203559a3302`.
Namespace `SourceLattice`; capstones `odd_sinhGram_le_latticeFrame`,
`odd_moment_sq_le_latticeFrame`, `odd_plasticCrossover_ge_latticeFrame`, and
`latticeFrame_of_source_zeros`. All 16 public theorem axiom audits passed with only
`propext`, `Classical.choice`, `Quot.sound`. Twelve contributions, 198 public
supporting theorem audits. Umbrella and index updated; canonical README unchanged.
The next result preserves cancellation in the coherent correction. Quantitative
domination of moment/variance costs by positive original energies remains open.

## Signed coherent correction survives the moment limit

- For the preceding actual correction samples, define sigma=sum_Z e_k,
  tau=2sum_(m>=0)(m+1)e_(m+1), and
  C_signed=R_S+sigma+sqrt(2Q Gamma). Compactness makes both sums finite.
  These quantities admit every signed source correlation.
- Exact pair counting gives E_N(1)=2sum_(m<N)(N-m)e_(m+1). Once N covers
  the finite support, E_N(1)=(N+1)sigma-tau exactly. Boundary effects have a
  fixed intercept; the extensive coefficient keeps its sign.
- For canonical odd F, actual coherent multiplier packets satisfy
  G_S(1)<=C_signed(N+1)-tau eventually. The packet support inequality and
  integer growth remove the fixed intercept, without any sign premise on tau:
  O^2<=log2*C_signed(F). Consequently C_signed(F)>=0; no max is inserted.
  This is a coherent-direction bound, not an arbitrary-weight frame estimate.
- N_minus=sum_Z max(-e_k,0)>=0 measures the exact improvement:
  C_abs-C_signed=2N_minus. Thus C_signed<=C_abs for every compact source,
  strictly whenever any correction sample is negative. Actual-source realization
  is proved in the next result.
- The full unconditional receiver is
  I_opt+R_plastic-2log2*C_signed<=P, equivalently
  I_opt+R_plastic-2log2*C_abs+4log2*N_minus<=P.
  The collar is unchanged, and the exact gain is visible in source data.
- Positive dyadic source zeros recover C_signed=R_S+sqrt(2V) exactly.
  This is secondary; the main moment and plastic receivers assume only actual
  compact input. No universal plastic positivity or all-vector optimum is claimed.
- This is one contribution sharpening the odd moment penalty by signed source
  cancellation. Triangular counting and the affine limit lemma are supporting
  machinery. No external novelty claim.

Implementation: `formal/GaloisForLFunctions/BiScaleUncertainty/SignedCoherentMomentReceiver.lean`.
Final actual-source compile passed without warnings; 317 lines, source SHA256
`73bee1950bc1b31f37fc71bc01781b0ccf59377d14df72022b048571d929cc64`.
Namespace `SignedCoherentMoment`; capstones `sourceCorrection_one_eventually_affine`,
`odd_moment_sq_le_coherentBudget`, `latticeFrame_sub_coherentBudget`, and
`odd_plasticCrossover_ge_cancellation_gain`. All 13 public theorem axiom audits
passed with only `propext`, `Classical.choice`, `Quot.sound`. Thirteen contributions,
211 public supporting theorem audits. Umbrella wired; index/lint evidence is on the
master card. Canonical README remains read-only and unchanged.
The next result discharges actual-source realization of strict gains. The other
frontiers remain open.

## Unbounded cancellation realized at fixed original energy

- Reuse the smooth odd six-packet family, with d=log2, packet mass m>0 and
  weighted packet mass H>0. Set F_T=source(|T|+d). For every real T,
  h_F(0)=6m, h_F(d)=0 and h_F(2d)=-2m. Exactly two within-half pairs survive
  at the second lag; all reflection-crossing pairs are separated from it.
- Write c=2sinh(d/2)H>0. The existing exact multiplier law gives
  h_S(d)=c*sinh(|T|+3d). Since h_S(d)<=R_S and M=R+2R_S,
  2c|T|<=6m*mu(F_T). This derives mean growth from the actual source family.
- The correction at integer lag2 obeys the exact balance
  cosh(d)e_2=m(cosh(d)^2-mu(F_T)). Together with
  C_abs-C_signed=2sum max(-e,0)>=-2e_2, it yields
  C_abs(F_T)-C_signed(F_T)>=b|T|-2m*cosh(d),
  b=2c/(3cosh(d))>0. This explicit bound uses only one correction sample.
- Consequently, every real A admits an actual smooth odd source with the same
  positive original energy6m and first-lag zero, whose signed-budget gain exceeds A.
  For that same source, every N satisfies
  I_opt(F,N)+R_plastic(F)-2d*C_abs(F)+2d*A<P(F).
  Thus the conditional gain from the previous result is realized and unbounded
  at fixed original energy; absolute correction mass can overprice coherent packets
  arbitrarily under these constraints.
- This is a budget-separation theorem. No moment-bound attainment, full-grid
  blindness, universal plastic positivity or optimality over all controls is asserted.
  One contribution; packet enumeration and scalar growth arguments are supporting
  machinery. No new bump family or external novelty claim.

Implementation: `formal/GaloisForLFunctions/BiScaleUncertainty/RealizedCoherentCancellation.lean`.
Final actual-source audit passed without warnings; 235 lines, source SHA256
`23f205f2ec505806a23334d70a7e65c4945580c8b57f6e88d9d35d03b6a09d86`.
Namespace `RealizedCoherentCancellation`; capstones `outwardSource_second_correlation`,
`outwardSource_correction_balance`, `outwardSource_gap_lower`, and
`exists_smooth_odd_fixedEnergy_plastic_gain`. All 13 public theorem axiom audits
passed with only `propext`, `Classical.choice`, `Quot.sound`. Fourteen contributions,
224 public supporting theorem audits. Umbrella wired; all16 public declarations
indexed. Canonical README unchanged; global lint snapshot is on the master card.
Remaining frontier: cancellation in the coherent difference-Gram price, all-control
optimization, and comparison of moment/variance costs with positive original energies.
Full goal remains active.

## Explicit coherent producer and recovered source energy

- Put d=log2, R=h_f(0), v_k=h_f(kd)/cosh(kd/2) for k>=1,
  kappa=sum v_k and eta=sum k*v_k. Compact source correlations make both sums
  finite. For the actual uniform difference packet P_N, with m=N+1, its source
  covariance is exactly m*kappa-eta after the finite source support is included.
- The concrete compact producer r_N=P_N/m-(kappa/R)f satisfies
  ||r_N||²=||P_N||²/m²-2(kappa/R)<f,P_N>/m+kappa²/R.
  Consequently, eventually
  ||r_N||²<=D+B/m, D=2Gamma-kappa²/R, B=2kappa*eta/R.
  This retains the sign of the explicit inverse-length boundary term. All real
  divisions are totalized; the theorem includes R=0. Nonnegative producer
  energies force D>=0, so this is not an assumed Schur or analytic bound.
- Since q=(cosh(u)-mu)f is orthogonal to f, source cancellation changes no pairing
  with q. With Q=||q||² and the previous signed correction sigma, the actual odd
  source F=oddCompactSource f obeys
  O(F)²<=d*C_proj(F), C_proj=R_S+sigma+sqrt(Q*D)>=0.
  The finite boundary terms vanish in the compact chain-packet integral limit.
  Thus I_opt(F,N)+R_plastic(F)-2d*C_proj(F)<=P(F) for every collar cutoff N.
- C_proj<=C_signed. The exact gain law is
  (C_signed-C_proj)*(sqrt(2QGamma)+sqrt(QD))=Q*kappa²/R.
  The same full plastic certificate therefore improves by exactly
  2d*(C_signed-C_proj). No source-zero or sign hypothesis is needed.
- The producer cancels the limiting source component; it is not claimed exactly
  orthogonal to f at every finite N. D is a proved asymptotic upper price, not a
  claim that the producer energy attains D. The moment coefficient controls the
  coherent direction, not all signed packet weights. No universal plastic
  positivity or literature-priority claim.

Implementation: `formal/GaloisForLFunctions/BiScaleUncertainty/CoherentSourceProjection.lean`.
Final actual-source audit passed without warnings; 433 lines, seven public
definitions and ten public theorems. SHA256
`77cc97109b5001a42f7cf41d50d5a1649a2c3bf9a08c37addfc85c1b5124bd06`.
All ten public axiom audits use only `propext`, `Classical.choice`, `Quot.sound`.
Fifteen contributions, 234 public supporting theorem audits. Umbrella wired;
all17 public declarations indexed. Canonical README fully read at260lines,
hash `dda7a67adbca527a21596c6fb672c28afb5feda594fe3b552a781325df7c3933`,
unchanged by this work. Latest global lint snapshot is recorded on the master card.
Remaining frontier: replace absolute correlation mass in the coherent difference
cost by the actual signed filter energy; realize and classify projection gains;
optimize all signed controls and compare moment costs with positive original energies.
Full goal remains ACTIVE at15/100.

## Exact finite coherent filter and signed Gram energy

- Choose the intrinsic integer L=sourceCutoff(f) with L*d>2*multiplierSourceRadius(f),
  d=log2. At the omitted positive lags, the two source factors cannot both be
  nonzero. Original, sine-multiplied and centered cross-correlations therefore
  vanish there. This uses support separation, not an inference from a cancelled
  original-source correlation to a multiplier zero.
- The concrete compact filter is
  A_L(u)=sum_(k=1)^L [f(u+kd)+f(u-kd)]/(2cosh(kd/2)).
  Its exact original-source energy is
  G_L=sum_(k,l=1)^L [h_f((l-k)d)+h_f((l+k)d)]/[2cosh(kd/2)cosh(ld/2)].
  Both signed difference and reflected-sum correlations survive; no absolute
  correlation mass appears in this finite energy.
- K=<f,A_L> equals the previous covarianceMass kappa exactly. The actual compact
  r=A_L-(K/R)f has energy H=G_L-kappa²/R>=0 and is orthogonal to f, including
  R=0. In that case integral Cauchy--Schwarz forces K=0. With Q=||q||² and
  q=(cosh(u)-mu)f, <q,A_L>=<q,r><=sqrt(QH).
- For canonical odd F, the filter reproduces the complete coherent slope:
  sigma+<q,A_L>=2sum_(k=1)^L h_S(kd). For every K>=0, at N=L+K,
  G_S(N)=(N+1)[R_S+sigma+<q,A_L>]-B,
  B=2sum_(k=1)^L k*h_S(kd). This is exact; the omitted centered pairing is zero.
- Consequently O²<=d[R_S+sigma+<q,A_L>] before applying any norm bound.
  The finite Schur price C_local=R_S+sigma+sqrt(QH) is nonnegative on canonical
  odd sources and gives O²<=d*C_local. The full functional obeys
  I_opt(F,N)+R_plastic(F)-2d*C_local(F)<=P(F), for every collar cutoff N.
- Main capstones construct their source cutoff and producer. No unknown
  analytic bound, source-zero condition or nonzero-energy premise remains.
  The exact signed energy retains the finite support window; its uniform lattice
  comparison is established below. No norm-price attainment or universal
  plastic positivity is asserted. One contribution; generic finite counting and
  affine-limit arguments are supporting machinery, not new contribution counts.

Implementation: `formal/GaloisForLFunctions/BiScaleUncertainty/LocalCoherentFilter.lean`.
Final actual-source audit passed without warnings; 463 lines, seven public
definitions and fourteen public theorems. SHA256
`1e71a25424aebd61b98307a70d8ba62c28b2e085c7b51e3d360fd4ce2946988c`.
All fourteen public axiom audits use only `propext`, `Classical.choice`, `Quot.sound`.
Umbrella wired; all21 public declarations indexed. Canonical README and previous
source15 unchanged. The next result supplies the missing comparison with the
earlier projected lattice budget.

## Quantitative dominance of the finite filter

- For the actual finite filter A_L and Gamma=sum_Z|h_f(kd)|, d=log2,
  ||A_L||²<=Gamma*rho_L, where rho_L=2sum_{k=1}^L[2cosh(kd/2)]^{-2}.
  Distinct positive/negative lattice positions give an absolute row bound by
  Gamma while preserving the actual signed Gram energy on the left.
- The exact first coefficient square is 2/9. Bounding subsequent squares by
  2^{-k} gives rho_L<=13/9, uniformly in L, including L=0. This constant is
  sufficient for the comparison; no optimality is asserted.
- Let H=||A_L||²-kappa²/R and D=2Gamma-kappa²/R. Then
  D-H>=5Gamma/9>=0. The same exact source projection cancels from the gap;
  the new improvement comes from the finite producer's coefficient energy.
  This remains valid at R=0 with totalized division.
- Consequently C_local<=C_proj. With Q=||q||², the exact identity
  (C_proj-C_local)(sqrt(QD)+sqrt(QH))=Q(D-H)
  gives the explicit nonnegative gain
  g=(5QGamma/9)/(sqrt(QD)+sqrt(QH))<=C_proj-C_local. If the denominator
  vanishes, g=0 and the comparison still holds.
- For every canonical odd F and every collar cutoff N,
  I_opt(F,N)+R_plastic(F)-2d*C_proj(F)+2d*g(F)<=P(F).
  The producer, its coefficient bound, and the zero-energy branch are all
  discharged. Signed source data remain unrestricted. The exact strictness
  domain is classified below; no optimal coefficient, budget attainment or
  plastic positivity is asserted.
  This does not contradict the no-extra-projection-gain law on exact cliques.

Implementation: `formal/GaloisForLFunctions/BiScaleUncertainty/LocalFilterLatticeGain.lean`.
Final actual-source compile and all11 public theorem axiom audits passed without
warnings. Axioms: only `propext`, `Classical.choice`, `Quot.sound`. Source has260
lines, three public definitions and eleven public theorems; SHA256
`da97d0679dfcd8f390e0279cc0ae1704e9ac94045e700123ce277c123ab05a57`.
Umbrella wired, all14 public declarations indexed. README and source16 unchanged.
The following rigidity result resolves the strictness domain left open by the
quantitative comparison. Schur slack and producer optimization remain distinct questions.

## Hyperbolic variance rigidity and exact strictness domain

- For actual compact continuous f, autocorr(f,0)=0 iff f=0. Continuity
  upgrades almost-everywhere zero energy to pointwise zero source.
- For every real scale alpha and scalar center c,
  centeredSource(f,alpha,c)=0 iff f=0 or (alpha=0 and c=1).
  The same classification holds for its origin energy. At nonzero scale,
  a hyperbolic level set consists of at most two points. A continuous source
  supported there is zero, so no nonzero source is a multiplier eigenvector.
- V(f,alpha)=0 iff f=0 or alpha=0, and V>0 iff both f and alpha are nonzero.
  This discharges strict positivity at scale1/2 from actual source data.
- Gamma>=R. For nonzero f, Q>0, Gamma>0 and D>=H+5Gamma/9>0.
  Therefore the constructed finite-filter gain g is positive iff f!=0 and
  zero iff f=0. Likewise C_local<C_proj iff f!=0. These are exact
  degeneracy classifications, not uniform positive lower gaps.
- F=oddCompactSource f is zero iff f is even. Hence g(F)>0 exactly when
  f is not even. For every f,N, the explicit improved lower bound
  B+2(log2)g(F)<=P(F) is strictly larger than B iff f is not even.
  The full plastic certificate requires no positivity or source-zero premise.
  No universal plastic positivity or norm-price attainment follows.

Implementation: `formal/GaloisForLFunctions/BiScaleUncertainty/HyperbolicVarianceRigidity.lean`.
Final actual-source compile and all13 public theorem axiom audits passed without
warnings. Only `propext`, `Classical.choice`, `Quot.sound`. Source has232 lines,
13 public theorems, no public definitions; SHA256
`2d3baccc6ece6eefd2e74eea3fca2862453c0a4b119eab0e5ddf5483cff44b9c`.
Umbrella wired; all13 public declarations indexed. README and source17 unchanged.
Generic zero-integral facts support this single rigidity/strict-gain contribution.
The following result settles finite-filter norm-price attainment and identifies
its exact Schur slack. Other producer optimizations remain distinct questions.

## Finite-filter escape and unavoidable Schur slack

- The actual finite hyperbolic filter A_f is nonzero somewhere outside
  support(f) iff f!=0. If M=sup support(f), choose u in support(f) with
  M-log2<u and set v=u+L log2. Only the outermost translate survives at v;
  A_f(v)=f(u)/(2cosh(L log2/2))!=0 while f(v)=0. Arbitrary signs and
  disconnected support are allowed.
- With q=(cosh(u)-mu)f, Q=||q||², beta=<q,A_f>, and
  r=A_f-(kappa/R)f, the actual compact residual e=r-(beta/Q)q is orthogonal
  to both f and q. Its measured energy satisfies
  E=||e||²=H-beta²/Q and Q E=QH-beta², including zero energy.
- The escaping value survives both projections: e(v)=A_f(v). Thus E=0
  iff f=0, and E>0 iff f!=0. Consequently beta²<QH iff f!=0.
  Nonzero compact sources cannot saturate this finite-filter Cauchy--Schwarz price.
- For nonzero f, |beta|<sqrt(QH); the rationalized denominator is strictly
  positive. The totalized correction
  g_res=Q E/(sqrt(QH)+beta)=sqrt(QH)-beta
  is nonnegative, positive iff f!=0, and gives
  C_local-g_res=R_S+sigma+beta. The original signed pairing is retained.
- The existing exact coherent pairing endpoint therefore yields
  I_opt+R_plastic-2(log2)C_local+2(log2)g_res<=P(F), for every canonical
  odd F and collar cutoff. The recovered increment is strict iff the original
  input is not even. This identifies the norm slack through an actual positive
  residual; it does not claim a new endpoint beyond the established pairing
  receiver, global optimality, a uniform positive gap, or plastic positivity.

Implementation: `formal/GaloisForLFunctions/BiScaleUncertainty/FiniteFilterSchurResidual.lean`.
Final actual-source compilation and all13 public theorem axiom audits passed
without warnings; only `propext`, `Classical.choice`, `Quot.sound`. Source has345
lines, four public definitions and thirteen public theorems; SHA256
`6f119308bd255012affd90d0eeaac906b40a35147aec5298f5cc23a7cac90119`.
Umbrella wired; all17 public declarations indexed. README and source18 unchanged.
Nineteen contributions, 285 supporting public theorem audits; full goal ACTIVE.
The nonattainment route and its fully formalized positive survivor are recorded in
`docs/drafts/pipeline/5-failed/finite-filter-schur-saturation-2026-10-17.md`.
Final global lint after one bounded refresh reports eight unrelated unreachable
modules and concurrent drift in LEAN_API/LEAN_OVERVIEW; no owned lifting module
flagged. Exact snapshot on master card. No global clean gate claimed.
Remaining frontier: optimize actual source-supported producers, quantify useful
residual lower bounds, and compare exact signed moment prices with positive source energies.

## Folded sinh source and the remaining coherent defect

Lean-verified result in
`formal/GaloisForLFunctions/BiScaleUncertainty/FoldedHyperbolicCellDefect.lean`.

- Put d=log2, F=oddCompactSource f, S=sinhCompact(1/2)F, and
  P(x)=sum_(k in Z) S(d(x+k)). Actual compact support makes this sum
  locally finite. It is a continuous 1-periodic source, with
  integral_0^1 P=O/d and integral_0^1 P²=C/d, where
  O=integral F(u)sinh(u/2) and C=R_S+sigma+beta=C_local-g_res.
- The explicit cell residual e=P-O/d has nonnegative energy
  E_cell=integral_0^1 e². Its exact identity is
  d² E_cell=d*C-O². This is the remaining coherent moment slack,
  distinct from the strictly positive finite-filter Schur residual.
- E_cell=0 iff P(x)=O/d throughout [0,1]. Hence the exact coherent
  moment endpoint is an equality precisely for constant folded sources.
  This does not assert that every nonzero source has positive cell slack.
  The following attainment result constructs nonzero constant-fold sources.
- For every f and every collar cutoff N, the full functional satisfies
  I_opt+R_plastic-2d*C_local+2d*g_res+2d²E_cell<=P_plastic(F).
  Both corrections are actual source energies, with all summability and
  support requirements discharged. This recovers the original exact moment
  penalty geometrically; it does not claim a stronger endpoint than that
  penalty or universal plastic positivity. Signed source data remain unrestricted.

This is one contribution: identification of the full coherent defect with an
actual folded-source energy, its equality domain, and its plastic transfer.
Generic periodization identities are supporting tools only. No external
novelty claim. Nonzero-mean attainment is settled below. Nonzero zero-fold
sources and the full kernel of the fold map remain separate questions.

Final actual-source compilation and all nine public theorem axiom audits passed
without warnings; only `propext`, `Classical.choice`, `Quot.sound`. Source has302
lines, three public definitions and nine public theorems; SHA256
`9ca67e26ad5db447e31ae6da2e5b78831c3a55eb5a1134f6e752d6ba77af3df6`.
Umbrella wired; all12 public declarations indexed. README and source19 unchanged.
Twenty contributions, 294 supporting public theorem audits; full goal ACTIVE.
Final global lint after one bounded refresh reports eight unrelated unreachable
modules and concurrent drift in LEAN_API/LEAN_OVERVIEW; no owned lifting module
flagged. Exact snapshot on master card. No global clean gate claimed.

## Actual coherent attainment and the sharp universal coefficient

Lean-verified result in
`formal/GaloisForLFunctions/BiScaleUncertainty/CoherentMomentAttainment.lean`.

- With d=log2 and t(x)=max(0,1-|x|), set
  p(u)=(t(u/d-2)+t(u/d+2))/2 and F_a(u)=a*p(u)/sinh(u/2).
  The profile is even, supported in [-3d,3d], and identically zero on
  [-d,d]. Division therefore defines an actual compact continuous odd
  source, including at0; no missing regularity or inversion premise remains.
- The sinh multiplier is exactly a*p. On x in [0,1], only lattice
  indices -3,-2,1,2 contribute. Their profile values are respectively
  x/2,(1-x)/2,x/2,(1-x)/2. Thus the actual fold equals a on the closed
  cell. The canonical odd-source map fixes F_a.
- Exact values: cellMean(F_a)=a, O(F_a)=d*a, E_cell(F_a)=0,
  C_exact(F_a)=d*a². Also F_a=0 iff a=0. In particular F_1 is a
  nonzero-mean equality case of the exact coherent moment bound, while
  retaining strictly positive local Schur slack by contribution19.
- For every real c, the universal inequality O(odd f)²<=c*C_exact(odd f)
  for all actual compact continuous f holds iff log2<=c. The source F_1
  proves necessity; the existing coherent bound and C_exact>=0 prove
  sufficiency. This establishes the best coefficient within the actual
  odd hyperbolic source class, not only for arbitrary periodic functions.
- For every signed a and collar cutoff N,
  I_opt(F_a,N)+R_plastic(F_a)-2(log2)²a²<=P_plastic(F_a).
  No source-grid blindness, smoothness beyond continuity, or universal
  plastic positivity is claimed. Generic tent identities and scalar
  homogeneity support this one attainment/sharpness contribution.

Final actual-source compilation and all12 public theorem axiom audits passed
without warnings; only `propext`, `Classical.choice`, `Quot.sound`. Source has249
lines, two public definitions and twelve public theorems; SHA256
`f97dc36c6f8330117cdf3ebc823250ff6dd79573fe9f4d6f06123684beb3b161`.
Umbrella wired; all14 public declarations indexed. README and source20 unchanged.
Twenty-one contributions, 306 supporting public theorem audits; full goal ACTIVE.
The sub-log2 universal-coefficient route is closed with this positive survivor in
`docs/drafts/pipeline/5-failed/sublog-coherent-moment-coefficient-2026-10-17.md`.
Final global lint after one bounded refresh reports16 unrelated unreachable
modules and concurrent drift in LEAN_API/LEAN_OVERVIEW; no owned lifting module
flagged. Exact snapshot on master card. No global clean-gate claim.

## Canonical fixed-annulus representatives of odd coherent classes

Lean-verified result in
`formal/GaloisForLFunctions/BiScaleUncertainty/AnnularCoherentRetraction.lean`.

- For arbitrary actual f, let F=oddCompactSource f, d=log2 and
  P_f=cellFold F. The fold is continuous, 1-periodic and even.
  With A=attainingSource(1), the explicit representative
  R_f(u)=A(u)*P_f(u/d) is an actual compact continuous odd source.
  Its support is contained in d<|u|<3d, independently of the input radius.
- The entire fold is preserved: cellFold(R_f)=P_f on all real arguments.
  The periodic factor is constant along each summation lattice, while
  cellFold(A)=1. This gives exact zero reconstruction error without a tail
  hypothesis or a source-zero assumption.
- The constructor is idempotent, R_(R_f)=R_f, and R_f=R_g iff P_f=P_g.
  Representatives therefore distinguish exactly the full folded coherent
  classes. No linearity or source-norm optimization is asserted here.
- Mean, signed odd moment, exact signed coherent price and cell defect are
  preserved: cellMean(R_f)=cellMean(F), O(R_f)=O(F),
  C_exact(R_f)=C_exact(F), E_cell(R_f)=E_cell(F).
- The original full functional consequently obeys
  I_opt(F,N)+R_plastic(F)-2d*C_exact(R_f)+2d²E_cell(R_f)<=P_plastic(F).
  The original collar and remainder stay attached to F. Original source
  energy, individual lattice correlations and full plastic value are not
  asserted to be preserved. No universal plastic positivity follows.

One contribution: exact canonical reduction of full odd coherent classes to
a fixed annulus, with preservation laws and transfer to the original functional.
Periodic identities and tent support facts are supporting tools only.

Final actual-source compilation and all14 public theorem axiom audits passed
without warnings; only `propext`, `Classical.choice`, `Quot.sound`. Source has167
lines, one public definition and fourteen public theorems; SHA256
`376b1420b5b868bb8f5cfd99683fbb28d7229d70f733375eb69d3f7c45fd3a9b`.
Umbrella wired; all15 public declarations indexed, with an exact name-list match.
README and source21 unchanged. Twenty-two contributions,320 supporting public
theorem audits; full goal ACTIVE. Final global lint after one bounded refresh
reports21 unrelated unreachable modules and concurrent LEAN_API/LEAN_OVERVIEW
drift; no owned lifting module flagged. Exact snapshot on master card.
No repository-wide clean-gate claim.

## Actual coherent kernel and a plastic-nonnegative source splitting

Module `formal/GaloisForLFunctions/BiScaleUncertainty/CoherentKernelSplitting.lean`.
Let O(f)=oddCompactSource f and R(f) be the annular representative.

- K(f)=O(f)-R(f) is an actual compact continuous odd source with zero fold.
  It is an idempotent projection; R(K(f))=0 and K(R(f))=0. Moreover
  K(f)=O(f) iff cellFold(O(f))=0, so it reaches the entire odd zero-fold domain.
- O(f)=R(f)+K(f). Exact coordinate uniqueness is
  O(f)=R(g)+K(h) iff R(f)=R(g) and K(f)=K(h).
  Pointwise finite lattice support proves the fold linearity used here;
  no infinite-sum convergence premise is imposed.
- The signed hyperbolic moment, exact coherent price and cell defect of K(f)
  all vanish. Its full plastic value is exactly
  P_plastic(K(f))=J_secant(K(f))+R_plastic(K(f)).
  At every cutoff N,
  I_opt(K(f),N)+R_plastic(K(f))<=P_plastic(K(f)), hence P_plastic(K(f))>=0.
  This is an unconditional conclusion for an explicitly produced source.
- The kernel contains a concrete nonzero family. With d=log2,
  A=attainingSource(1), B(u)=A(u/2), define W_a=K(a*B)=a*K(B).
  At u=4d, K(B)(4d)=1/(2*sinh d) is nonzero because R(B)(4d)=0.
  Thus W_a=0 iff a=0, and h_(W_a)(0)=a²h_(W_1)(0), with positive energy
  exactly for a!=0. Every W_a has zero fold and coherent price and retains
  the full zero-penalty plastic bound.
- No real scalar c bounds original energy by c*C_exact on all actual odd
  sources. W_1 alone refutes every c. The positive survivor is the exact
  decomposition and the constructed plastic-nonnegative kernel above.
  Energy control for R(f), or after adding a kernel cost, remains open.

No original-energy orthogonality, plastic additivity between the coordinates,
prime-grid blindness or extra source smoothness is asserted. Strictness on
nonzero kernel sources is established below. This is one substantive kernel/decomposition contribution;
supporting linearity and quadratic scaling are not separate contributions.

Direct source compilation and all25 public theorem axiom audits passed without
warnings, using only `propext`, `Classical.choice`, `Quot.sound`. Source has337 lines,
two public definitions and25 public theorems; SHA256
`a66ab901bde6e45677acc2e0e8ab35f1a4e4402fca415863936d64a08c7e0dcf`.
Umbrella wired; all27 public declarations indexed with an exact name-list match.
Source and audit theorem-name lists also match exactly. Twenty-three contributions,
345 supporting public theorem audits; full goal ACTIVE. The energy-control no-go
is closed with this formally verified positive survivor in
`docs/drafts/pipeline/5-failed/coherent-price-controls-source-energy-2026-10-17.md`.
Final global lint after one bounded refresh reports10 unrelated unreachable
modules, with no generated-file drift and no owned lifting module flagged.
Exact snapshot on master card; no repository-wide clean-gate claim.

## Exact plastic minimization within a coherent class

Lean-verified module
`formal/GaloisForLFunctions/BiScaleUncertainty/PlasticCoherentLineMinimizer.lean`.
For arbitrary actual inputs f,g, set F=oddCompactSource(f), H=kernelPart(g),
Q=plasticCrossover, q=Q(H), and b=(Q(F+H)-Q(F)-Q(H))/2.

- q=0 iff H=0, and q>0 iff H!=0. The positive jump integral vanishes only
  for the zero compact source: zero integral forces its continuous correlation
  difference to vanish on x>0, including a lag beyond its support diameter.
  Thus nonzero coherent-kernel directions have strictly positive plastic curvature.
- The actual compact odd source F_t=F+t*H satisfies
  Q(F_t)=Q(F)+2tb+t²q for every real t. Original signed pair integrals are
  admitted through the existing unconditional integrability theorems.
- The full fold is preserved for every t, hence so are the signed hyperbolic
  moment and exact coherent price. Finite lattice support discharges the
  summability needed for the public fold add/scalar identity.
- Define t_*=-b/q, F_*=F_(t_*), and G=b²/q, including total division at q=0.
  When q=0, H=0 and b=0, so F_*=F and G=0. Universally,
  Q(F_*)=Q(F)-G and Q(F_t)=Q(F_*)+q(t-t_*)².
  The source F_* therefore attains the minimum on the entire prescribed line.
  Equality holds iff H=0 or t=t_*; improvement is strict iff b!=0.
- For every cutoff N, the original full functional receives the bound
  I_opt(F_*,N)+R_plastic(F_*)-2*O_moment(F)²+G<=Q(F).
  Collar and remainder belong to the actual corrected source; the signed
  moment belongs to its preserved coherent class. No free analytic, curvature,
  integrability or step-selection premise remains.

This is one actual-source minimization and gain-transfer contribution.
Generic quadratic algebra and completion of the square are supporting tools.
No minimizer over the whole coherent fiber, convergence of repeated corrections,
source-energy orthogonality, preservation of source-grid zeros, or universal
plastic positivity is claimed. The theorem minimizes the original plastic
functional along the chosen line, not only a surrogate lower bound.

Direct source compilation and all21 public theorem axiom audits passed without
warnings; only `propext`, `Classical.choice`, `Quot.sound`. Source has354 lines,
five public definitions and21 public theorems; SHA256
`23c31eead3da768eea9f6ee378b02c857bff49e44bea5fe9f6c740ad263a6023`.
Umbrella wired; all26 public declarations indexed with exact source/API and
source/audit name-list matches. Twenty-four contributions,366 supporting public
theorem audits; full goal ACTIVE. Final global lint after one bounded refresh
reports22 unrelated unreachable modules and concurrent LEAN_API drift; no owned
lifting module flagged. Exact snapshot on master card; no global clean-gate claim.
