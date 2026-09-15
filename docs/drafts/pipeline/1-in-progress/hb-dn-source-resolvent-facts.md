# HB DN: own source-resolvent facts

- **DN1 — Lean verified.** For the actual continued radial response at fixed
  source frequency `w` and actual normalizable reader at independent `v`,
  `(v^2-w^2)*int rho*y_w*n_v = 2*[W]+int n_v*S_w` on every
  `0<e<=b<1`. Both integrals are separately admitted. Its diagonal limit is
  `2*w*int rho*y_w*n_w = 2*[partial_v W]+partial_v int n_v*S_w`.
  Angular data and source frequency stay fixed in that derivative.
  `OriginalSourceResolvent`: scratch passed; isolated exact module build
  passed; umbrella import added; formal lint passed. **Whole-route effect:**
  an actual source identity replaces differentiation of the evolved response;
  compact endpoints alone do not establish full matching.

- **DN2 — Green reduction Lean verified; full forcing/QNM formula analytical.** Removing the
  explicit opposite-mode singularity from the two-frequency pairing gives
  `(v^2-w^2)*Ireg(v)=J(w,v)+(v+w)*E(w)*beta(v)` in the right chamber.
  Its diagonal is `2*w*GreenFP=J_v+E*(beta+2*w*beta')`.
  Since `cE=-J(w,w)`, adding the actual Green temporal corner cancels the
  reader derivative, leaving `-mu*(mu-2)*C*J_source`. Full forcing contributes
  `-mu*w*C*FP int n_w*S_w/z`; its temporal corner remains until QNM evaluation.
  Exact estimates, counterterms and continuation argument:
  [source reduction](hb-dn-source-moment-reduction.md).
  **Whole-route effect:** the remaining QNM value has a concrete three-source-
  period expression to formalize and compare with the physical receiver;
  no receiver equality, impossibility theorem or RH conclusion is proved.

- **DN3 — Fixed normalization constraint from the explicit source.** The
  source-frequency derivative holds `chi` and `K` fixed. Differentiating
  `fundamentalSourceMoment(w,s,amp)` along the fundamental curve also changes
  its substituted `K` and is a different derivative. The tortoise-weighted
  moment requires the original `-log(2)` endpoint constant. Neither change
  is allowed when identifying the complete original action.

- **DN4 — Scope correction from inspected corpus.** Synchronized complete
  static matching and canonical QNM continuation already occur in
  `OriginalStaticCanonicalAction`. The six independent-cutoff drafts are
  deferred; strengthening them does not evaluate `canonicalQNMValue` or
  couple it to the extinction receiver. No further cutoff strengthening is
  part of this source-reduction attack.

- **DN5 — Lean verified.** The actual two-frequency forced-response bracket
  tends to zero at the horizon when `Re(w+v)>0` and `Re(w-v)>0`, with source
  frequency in its original nonreal convergence chamber. Its outer limit is
  also zero for independent source and reader chamber frequencies.
  `OriginalSourceResolventEndpoints.mixedBracket_horizon_limit` uses the
  actual incoming quotient and its source-transport derivative;
  `mixedBracket_outer_limit` uses both admitted original Green moments and
  weighted mode-derivative limits. Scratch and isolated exact module audit
  passed; module wired. **Whole-route effect:** both endpoint terms in the
  global two-frequency source identity are derived. DN6 supplies whole-domain
  integral admission; the full subtracted diagonal identity remains separate.

- **DN6 — Lean verified.** `OriginalWholeSourceResolvent.whole_source_resolvent`
  proves `(v^2-w^2)*int_0^1 rho*y_w*n_v=int_0^1 n_v*S_w` for the actual
  response and independent reader in the mixed convergence wedge. Both
  whole-domain absolute integral admissions and both vanishing endpoint
  terms are derived. Scratch and isolated exact module audit passed;
  module wired. **Whole-route effect:** the full-exterior identity needed
  for the source-only metric-action reduction is available. DN10 supplies
  the pole subtraction; DN11 supplies the original metric/temporal diagonal.
  This is not a receiver-matching result.

- **DN7 — Lean verified.** `OriginalReaderRegularization` derives the actual
  fixed-source/independent-reader core, a uniform linear endpoint remainder,
  and its subtracted Mellin holomorphy for `Re(a)>-2`, including `a=-1`.
  `readerHorizonRegularPart_continuousAt_below` gives continuity across `v=w`.
  `readerOppositeRegularPart_original_below` identifies its weighted opposite
  branch with the original `oppositePairingFinitePart`, preserving the exact
  logarithmic counterterm and constant. A single source-derived interval
  supports all sufficiently small cutoffs and independent nonreal readers.
  Scratch and isolated exact module audit passed; module wired.
  **Whole-route effect:** the divergent reader diagonal is now controlled,
  and its logarithmic branch has the original physical normalization.
  DN8 supplies complete horizon identification; the whole-domain diagonal
  source identity remains separate.

- **DN8 — Lean verified.** `OriginalReaderDiagonalMatch` identifies the incoming
  diagonal with `incomingPairingFinitePart`, then proves on one common family
  of small cutoffs that the continuous `readerHorizonRegularPart` equals the
  complete original `normalizableHorizonPairingFinitePart`. Conditions are
  `Re(w)>0`, `Im(w)!=0`, `c(w)!=0`, and `w-2*s!=0`; no matching or endpoint-limit premise is added. Both power
  counterterms and the logarithmic constant are retained. Scratch and isolated
  exact module audit passed; module wired. **Whole-route effect:** the horizon
  normalization needed for the source-action reduction is identified, rather
  than assigned. The outer integral, full source-difference limit, QNM
  continuation/evaluation and receiver equality are not closed by this result.

- **DN9 — Analytical source-derivative limit; off-diagonal formula verified in DN10.** Subtract
  `J(v,v)=-c(v)*E(v)` before taking the regularized reader diagonal:
  `(v+w)*Ireg(w,v)+c(v)*(E(v)-(v+w)*E(w)/(2*v))/(v-w)` equals
  `-int n_v*(S_v-S_w)/(v-w)`. Its limit is
  `2*w*GreenFP+c*(E'+E/(2*w))=-int n_w*partial_w S_w`.
  The added term is exactly the prescribed Green temporal corner.
  **Whole-route effect:** proving separate reader derivatives of `J` and `c`
  is unnecessary. DN10–DN11 supply regularized-pairing continuity, the literal
  diagonal source identity and the actual derivative of `E`. DN12–DN13 supply the source domination, derivative admission, and chamber identity.
  Fixed `chi,K,s,amp` and the original finite constants remain essential.

- **DN10 — Lean verified.** `OriginalRegularizedSourceResolvent` proves the
  full exterior pole subtraction, identifies every sufficiently small endpoint
  coefficient with the actual `greenHorizonAmplitude`, and derives the literal
  diagonal source admission and identity `J(v,v)=-c(v)*E(v)`. Its
  `readerFullRegularPart_source_difference_below` proves DN9's complete
  off-diagonal source-difference identity in the genuine mixed convergence
  wedge, with all original source data fixed. Scratch and isolated exact
  module audit passed; module wired. **Whole-route effect:** combining the
  metric pairing and temporal-corner quotient before the diagonal limit is
  now a full-domain theorem. DN11 supplies the combined metric/temporal
  diagonal; the source derivative integral, QNM evaluation and
  extinction-receiver comparison remain separate.

- **DN11 — Lean verified.** `OriginalMetricTemporalDiagonal` proves reader
  continuity of the actual outer integral through its physical endpoint,
  analyticity of the actual `greenHorizonAmplitude` away from the original
  source/connection denominators, and the complete temporal quotient limit
  `c(w)*(E'(w)+E(w)/(2*w))`. Its
  `fullMetricTemporal_diagonal_limit_below` identifies the full left side of
  DN10 with `2*w*GreenFP+c*(E'+E/(2*w))`, where `GreenFP` contains the
  original horizon finite part and actual outer integral. Scratch and isolated
  exact module audit passed; module wired. **Whole-route effect:** only the
  literal source divided-difference interchange remains to formalize in the
  convergence-chamber Green-action reduction. QNM continuation/evaluation
  and receiver equality remain open.

- **DN12 — Lean verified.**
  For fixed original source data, nonreal `w`, `Re(w)>0`, and `w-2*s!=0`,
  local uniform Gauss/coefficient/source bounds give
  `|n_v*S_u|<=C*z^(-1/2)` on a source/reader ball and `0<z<1`.
  Applying the corpus's `Bottcher.norm_sub_le_of_bounded_on_ball` in the
  source variable gives `|n_v*(S_v-S_w)/(v-w)|<=(2*C/R)*z^(-1/2)` on
  the half ball. Dominated convergence yields DN9's source derivative
  integral, with its absolute admission. `OriginalSourceActionReduction`
  passes scratch and isolated exact module audit; module wired.
  **Whole-route effect:** the source-derived Cauchy bound closes
  the chamber interchange without separate logarithmic estimates;
  the physical QNM still needs its original incoming subtraction and fixed
  tortoise constant. Proof: the source-reduction paper's Cauchy subsection.

- **DN13 — Lean verified.** `OriginalSourceActionReduction` proves, on one
  source-derived family of small interfaces in the genuine chamber,
  `2*w*GreenFP+c*(E'+E/(2*w))=-int_0^1 n_w*partial_source S_w`.
  `GreenFP` is the original horizon finite part plus the actual outer integral;
  no bound, matching, or limit premise is supplied. The same module proves
  `S_w=exp(w*tortoiseOf(z))*A(z)*T(w)` and
  `partial_source S_w=sourceProfile(T=1)*(tortoiseOf(z)*T+T')`, with all
  angular data fixed. Scratch and isolated exact audit passed; module wired.
  **Whole-route effect:** the unknown evolved-response derivative is eliminated
  from the Green metric/corner action. Native forcing, continuation with the
  original subtractions, and the finite QNM extinction law remain necessary.

- **DN14 — Analytical identity; Lean pending.** For the actual fundamental
  source core `F`, integration by parts with its original counterterms gives
  `w*Z0=-D`, where `D=FP int_0^1 z^w*F'` subtracts only `F'(0)`.
  The exact cutoff error is `-e^w*(F(e)-F(0)-F'(0)*e)`, which vanishes
  for `Re(w)>-2`; the outer boundary is zero because `F(1)=0`.
  **Whole-route effect:** the proposed complete QNM value becomes
  `mu*C*(T*D-(mu-2)*(T'*M+T*X))`. All periods share one Mellin exponent
  and first subtraction. No finite constant or angular normalization changes;
  canonical source continuation and extinction remain open.

- **DN15 — Lean verified.** `OriginalPhysicalSourceAction` proves the actual
  physical Green metric term plus the complete prescribed temporal corner
  equals `-mu*(mu-2)*C*int n_w*partial_source S_w+mu*c*C*Fforcing'/2`
  in the genuine chamber. It also proves the exact native forcing pullback
  `T*pullback=-n_w*S_w/z`, and at either physical QNM identifies the combined
  source-action density with
  `z^w*F*((mu-2)*(tortoiseOf(z)*T+T')+w*T/z)`. All angular data stay fixed.
  Scratch and isolated exact module audit passed; module wired.
  **Whole-route effect:** physical coefficients, forcing sign/Jacobian and
  the elementary QNM source core are identified. The remaining equality is
  continuation of this source formula with the original finite counterterms;
  the full finite QNM value and extinction comparison are not proved.

- **DN16 — Lean verified.** `OriginalSourceIncomingSubtraction` derives the
  exact independent-frequency incoming subtraction and bounds its remainder
  by `C*(z^(beta+1)+z^(-1/2))`, `beta>-2`, locally at every nonreal
  `Re(w)>-2` away from the literal source pole. The Cauchy derivative estimate
  preserves this integrable bound for the actual source derivative. Its
  diagonal remainder is analytic in frequency, and its explicit incoming
  derivative contains exactly `log(z)/2-log(2)`. All estimates come from
  the actual source and Gauss series. Scratch and isolated exact audit passed;
  module wired. **Whole-route effect:** source-derivative domination now reaches
  the physical QNM strip with the original finite constant. Integrating this
  remainder, restoring its primitive, and matching the canonical action are
  the remaining source-continuation steps.

- **DN17 — Lean verified.** `OriginalSourceHorizonFinitePart` integrates the
  actual differentiated-source remainder and proves holomorphy for nonreal
  `Re(w)>-2` away from `w=2*s`. The explicit restored primitive includes
  `log(z)/2-log(2)` and its derivative is the literal leading incoming density.
  The original horizon source cutoff converges to this value with no supplied
  admission or limit premise. Scratch and isolated exact module audit passed;
  module wired. **Whole-route effect:** the source derivative now has a
  normalized holomorphic horizon continuation through the physical QNM strip.
  The full exterior continuation and its canonical metric/corner equality
  remain to close; this is not yet the full QNM value.

- **DN18 — Lean verified.** `OriginalSourceFinitePart` extends DN17 over the
  full exterior. The actual outer source-derivative integral is analytic away
  from the source pole, without a real-part restriction; the full finite part
  is analytic for nonreal `Re(w)>-2`. It is the limit of `int_e^1 n_w*d_source S_w`
  plus the original incoming primitive, and equals the admitted ordinary
  integral when `Re(w)>0`. Scratch and isolated exact audit passed; module
  wired. **Whole-route effect:** the differentiated-source side now has its
  unique source-normalized continuation through either physical QNM. The
  remaining comparison must retain the native forcing's canonical power/log
  terms and prove equality with the full canonical metric/temporal action.

- **DN19 — Lean verified.** `OriginalNativeSourceFinitePart` identifies the
  native forcing pullback with the bare fixed source overlap, admits its
  actual outer integral at every positive interface, and proves that integral
  entire. The original canonical two-branch horizon restoration then glues
  to a single full-cutoff limit, analytic for nonreal `Re(w)>-2`. The canonical
  incoming value, incoming slope and opposite logarithmic value all remain.
  Scratch and isolated exact audit passed; module wired. **Whole-route
  effect:** both source finite parts in the proposed complete QNM action are
  now analytic and source-normalized. The full canonical action/source
  identity is the next unproved equality, not an assumed matching premise.

- **DN20 — Lean verified.** `OriginalCanonicalSourceAction` proves equality
  of the complete canonical metric/temporal action with the two actual
  source finite parts and retained forcing temporal corner in the genuine
  chamber. Meromorphic uniqueness extends the identity to both physical
  QNMs. Their canonical value is exactly
  `-mu*(mu-2)*C*Dsource + mu*w*C*T*Nnative`; the forcing corner vanishes by
  the actual connection zero. No matching, admission or limit premise is
  supplied. Scratch and isolated exact module audit passed; module wired.
  **Whole-route effect:** the evolved response and temporal/metric
  reconstruction are eliminated from the remaining value problem. The
  decisive burden is now extinction/nonextinction of this combined source
  value relative to the unit left-source clock, including the original
  angular coefficient. No receiver equality or impossibility is proved.

- **DN21 — Existing corpus statements inspected; application unproved.**
  `ExponentialTypeZeroDensity.exponentialType_zeroCount_linear` supplies an
  `O(T)` zero bound for a nonzero entire function with a global finite
  exponential-type bound. `Zeta23SimpleCriticalDensity` supplies the closed
  `T*log(T)/(72*pi)` simple-critical census. The uniform Ingham detector
  density bound has exponent `(16/5)*(1-sigma)`, hence `4/5` at `sigma=3/4`,
  with fixed polylogarithmic loss. The angular four-Lambda formula's inspected
  strict-right restriction enters through `nativeRamanujanChamber`, whose
  divisor shifts are packaged with strictly negative real parts; the preceding
  actual Bessel/Fourier and three-moment modular identities permit all Xi
  copies. **Whole-route effect:** a possible full-action impossibility test has
  specific growth, angular-boundary and counting obligations. The exact
  contour numerator and those remaining obligations are stated in the own
  source-reduction paper. Those census statements alone do not supply the
  canonical-cutoff attachment or matching impossibility.

- **DN22 — Lean verified.** `OriginalElementaryQNMAction` evaluates the
  canonical incoming forcing coefficients at either actual QNM as `F0=F(0)`
  and `F1=-2^(2*s-w)*amp^2*((2*s-w+2)*(A+B)/4+B)`, with opposite logarithmic
  coefficient zero. It proves the complete canonical value is the limit of
  one elementary source integral plus these forcing counterterms and the
  original differentiated-source primitive, including `-log(2)`. No response,
  transfer coefficient, limit or matching premise remains in that cutoff.
  Scratch and isolated exact module audit passed; module wired. **Whole-route
  effect:** the full value problem is now expressed in the elementary
  Mellin/logarithmic periods needed for the compact-contour test. Its
  nonvanishing and the resulting matching obstruction remain unproved.

- **DN23 — Lean verified.** `PhysicalAngularClosedHalfPlane` extends the actual
  divisor-product four-zeta identity to shifts with nonpositive real parts by
  dominated convergence, using the existing divisor-square majorant. The
  original Bessel/Fourier, modular three-moment, and testing-parameter
  continuation then give `physicalSelfSourceCoefficient_fourLambda_closedHalfPlane`
  for every actual copy with `Re(rho)>=1/2`. Its zero condition is exactly
  `xi(5*rho/2-1)=0 or xi(rho/2)=0 or xi(3*rho/2)=0`, including critical
  copies. Scratch and isolated exact module audit passed; module wired.
  **Whole-route effect:** critical angular exceptions in the full-action
  counting test are now identified with actual affine Xi collisions. The
  complete canonical-cutoff attachment and the counting injection remain open
  in Lean; no matching impossibility is claimed.

- **DN24 — Lean verified.** `FundamentalJacobiMonodromy` proves that the
  actual first-subtracted source moment times `exp(2*pi*i*w)-1` equals its
  compact logarithmic-cover contour for `Re(w)>-2`, `w+1!=0`. The small-circle
  remainder bound follows from the source's derivative on the unit disk.
  On every affine parameter curve the contour is entire and has a global
  finite exponential-type bound. Scratch and isolated exact module audit
  passed; module wired. **Whole-route effect:** the scalar Jacobi moments
  now have the required contour representation without a continuation or
  growth premise. Its attachment to the original complete action and the
  angular/radial counting comparison remain open; matching impossibility
  is not yet proved.

- **DN25 — Lean verified.** `FundamentalCanonicalContour` proves the
  fixed-source Jacobi derivative's exact monodromy correction and the full
  candidate numerator's entirety, finite exponential type, and linear zero
  count. Its direct nonzero anchor is at `w=-1`, `s=-2`:
  `H_n(-1,s)=2*pi*i*2^(2*s)`, `A=-3/2`, `B=0`, `H_M=-3*pi*i/8`, hence
  `G(-1)=27*pi^2*T(-2,-1)/4>0`. Positivity uses the original smooth onset
  against `exp(-3*u)`, with its positive plateau. Every other summand of
  this same numerator contains the zero monodromy factor at the anchor.
  The fixed-source onset derivative is cleared before substituting its
  physical affine gap. Scratch and isolated exact module audit passed;
  module wired. Default heartbeat limits are unchanged.
  **Whole-route effect:** nontriviality needs no second-order expansion at
  `w=0`. The numerator's identity with the actual canonical cutoff and the
  angular/radial counting comparison are still required. The forcing
  attachment must use the two-subtraction finite part or its first-moment
  integration-by-parts combination; the first-subtraction definition cannot
  be applied directly to exponent `w-1` in the physical strip.

- **DN26 — Lean verified.** `FundamentalJacobiLogIntegral` identifies the
  fixed-source Jacobi derivative with the admitted first-subtracted
  logarithmic integral and its exact constant
  `-g0*(log(2)/(2*(w+1))+1/(2*(w+1)^2))`. Its restored positive-cutoff
  integral converges to that same derivative for `Re(w)>-2`, `w+1!=0`.
  Uniform source derivative bounds and Cauchy domination derive admission;
  no integral, differentiation or limit premise is supplied. Scratch and
  isolated exact module audit passed; module wired. **Whole-route effect:**
  the logarithmic period is now attached to its own original cutoff. The
  nonlinear radius transport and twice-subtracted forcing attachment still
  precede the canonical-action equality and counting obstruction.

- **DN27 — Lean verified.** `FundamentalCountertermTransport` proves
  `tortoise(x*(2-x))=(log(x)-log(2-x))/2` and transports the original
  logarithmic counterterm with zero finite discrepancy for `Re(w)>-2`.
  It also transports both forcing counterterms, retaining the slope
  `g1=-(w+1)*2^w*F0/2+2^(w+1)*F1`, away from `w=-1`.
  Analytic divided slopes derive the vanishing quadratic remainder;
  positive complex powers absorb its logarithmic counterpart. Scratch and
  isolated exact module audit passed; module wired. **Whole-route effect:**
  neither counterterm introduces an adjustable finite constant under the
  original radius substitution. The actual forcing integral and complete
  canonical-action assembly remain to be attached.

- **DN28 — Lean verified.** `FundamentalForcingMoment` identifies the
  actual twice-subtracted Jacobi forcing with
  `Y_n=n*J_(n-1)(w,s-1/2)+(2*s-1)*J_n(w,s-1)` for `n>0`,
  `Re(w)>-2`, `w+1!=0`. The upper boundary vanishes and the lower
  quadratic remainder tends to zero by the analytic divided-slope lemma.
  Both forcing coefficients are retained; no shifted first-subtraction
  integral is asserted to converge. Scratch and isolated exact module
  audit passed; module wired. **Whole-route effect:** the forcing period
  used in the complete contour numerator has its original finite-part
  normalization. The source coefficient transport and canonical assembly
  remain to be completed in Lean.

- **DN29 — Lean verified.** `FundamentalSourceLogTransport` attaches the
  actual degree-four source's tortoise-weighted integral in the original
  radius to `2*a^2*(A*X_2+B*X_4)`. Its positive-cutoff pullback is exact,
  and its restored limit retains the original `log(z)/2-log(2)` constant.
  Scratch and isolated exact module audit passed; module wired.
  **Whole-route effect:** the full logarithmic source contribution is
  attached. The original forcing coefficient transport and complete
  canonical-action assembly remain open in Lean.

- **DN30 — Lean verified.** `FundamentalSourceForcingTransport` attaches
  the original physical-radius forcing to `2*a^2*(A*Y_2+B*Y_4)`.
  The original source core and slope give exactly the transported value
  `2^w*F0` and slope `-(w+1)*2^w*F0/2+2^(w+1)*F1`.
  The full restored forcing limit follows with both counterterms retained.
  Scratch and isolated exact module audit passed; module wired.
  **Whole-route effect:** all three source periods now have their original
  normalization. Assembling them into the canonical value and applying
  the radial/angular counting obstruction remain open in Lean.

- **DN31 — Lean verified.** `CanonicalSourcePeriodAttachment` identifies
  the full original canonical QNM value with
  `-mu*C*((mu-2)*(Td*M+T*X)+T*Y)` at every physical copy, branch,
  side and source amplitude. `Td` differentiates frequency with the source
  rate fixed; all three periods retain their original finite-part constants.
  Scratch and isolated exact module audit passed; module wired.
  **Whole-route effect:** the complete temporal, metric and forcing action
  is now evaluated in source periods. Attaching its entire numerator and
  proving the critical-copy counting obstruction remain open in Lean.

- **DN32 — Lean verified.** `CanonicalContourAttachment` proves, on the
  actual true/true unit-source curve,
  `E(w)^2*(5*w+8)^2*canonicalQNMValue=-mu*C*G(w)`.
  The entire numerator from DN25 is thus attached to the complete original
  temporal/metric/QNM value. Its logarithmic monodromy correction and
  twice-subtracted forcing survive unchanged. Scratch and isolated exact
  module audit passed; module wired. **Whole-route effect:** the proposed
  counting obstruction now concerns the actual full action. The remaining
  obligation is to compare its radial/angular exceptional sets with the
  actual simple critical Xi census.

- **DN33 — Lean verified.** `FullCanonicalMatchingNoGo` injects the three
  actual critical-copy angular collision sets into the residue-unit zero
  count on `Re=3/4`. For the simple-critical census up to height `N/3`,
  each image lies within ordinate `N-2` when `N>=12`. The corpus density
  bound makes each exceptional count at most `N` eventually. Multiplicities
  are retained; every injected zero has positive analytic order.
  Scratch and isolated exact module audit passed; module wired.
  **Whole-route effect:** angular cancellation cannot absorb the
  superlinear simple-critical census.

- **DN34 — Lean verified.** `FullCanonicalMatchingNoGo` proves the actual
  complete canonical action has zero value at only `O(N)` simple critical
  Xi zeros up to height `N/3`. For every `eps>0`, their number is eventually
  at most `eps` times the actual simple-critical count. The argument uses
  DN32's complete-action factorization, DN25's nonzero entire numerator,
  DN33's angular injections and the corpus's `Omega(N*log(N))` lower bound.
  Scratch and isolated exact module audit passed; module wired.
  **Whole-route effect:** full-action nonvanishing has relative density one
  on this critical census, including all possible cancellation between the
  temporal, metric and forcing contributions.

- **DN35 — Lean verified; matching no-go closed with positive survivor.**
  `exists_critical_canonicalQNMValue_ne_zero` produces an actual critical Xi
  copy with nonzero complete true/true unit-amplitude QNM action.
  `not_exists_hbXiPeierls_fullCanonicalQNM_matching` excludes matching it
  through the literal complementary unit-source probe for every possible
  copy-dependent returned vector. The stronger
  `not_exists_hbXiPeierls_fullCanonicalExtinction_matching` excludes even
  equality of their zero loci; arbitrary nonlinear carrier responses are
  included. DN34 is the quantitative positive survivor. Scratch and
  isolated exact module audit passed (98 seconds, two jobs); module wired.
  **Whole-route effect:** this literal unit-source matching option is
  impossible. Different source-retaining receivers are not excluded;
  RH is neither proved nor falsified. Exact scope and proof:
  [closed matching option](../5-failed/hb-full-canonical-unit-source-matching.md).

- **DN36 — Lean verified.** At every actual Xi copy and all four source-branch /
  fundamental-QNM combinations, `Re(2*s)<Re(w)`. The continued onset and its
  fixed-source frequency derivative are therefore the ordinary convergent
  integrals of `chi(u)*exp((2*s-w)*u)` and minus `u` times that density.
  `OriginalCausalSourceMatching` proves derivative admission by the local
  majorant `u*exp(-d*u)`, `d=(Re(w)-Re(2*s))/2>0`.
  **Whole-route effect:** fundamental-QNM time moments need no regularization;
  the source's spatial finite parts remain essential. No statement about
  arbitrary overtones is included.

- **DN37 — Lean verified.** The original spatial cutoff with factor
  `(mu-2)*(tortoise(z)-u)+w/z` and all original counterterms converges to
  `K(u)=-mu*C*chi(u)*exp(2*s*u)*((mu-2)*(X-u*M)+Y)`.
  Its absolutely convergent Laplace integral at the actual fundamental QNM
  equals `canonicalQNMValue`, for every Xi copy, source branch, QNM side and
  amplitude. `canonicalCausalSourceCutoff_tendsto` and
  `canonicalCausalSourceProfile_laplace` prove this without a matching premise.
  **Whole-route effect:** a concrete causal receiver retaining all three
  original source periods now matches the complete canonical action. This
  receiver is not identified with the retarded field or Hawking-clock
  extinction observable; DN35's unit-source obstruction remains.
  [Exact bridge](hb-eg-original-causal-source-matching.md). Scratch and isolated
  exact-module audit passed (128 seconds, two jobs); umbrella wired; formal
  lint passed. No heartbeat/transparency override or axiom audit was added.
