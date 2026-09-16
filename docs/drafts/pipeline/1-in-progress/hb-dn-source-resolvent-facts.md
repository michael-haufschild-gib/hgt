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

- **DN38 — Lean verified.** The complete action satisfies
  `A_q(a)=a^2*A_q(1)` for every original Xi copy and all four fundamental
  branch combinations. Its exact amplitude fibres are
  `A_q(a)=A_q(b) iff A_q(1)=0 or a^2=b^2`.
  **Whole-route effect:** source-amplitude information survives the complete
  temporal/metric/forcing assembly; it is not removed by QNM continuation.

- **DN39 — Lean verified.** At each fixed copy and branch combination, an
  arbitrary decoder of `hbXiPeierlsPlusSource a q` recovers the complete
  action for all amplitudes iff critical-line placement implies `A_q(1)=0`.
  Away from the critical line, evaluation of the carrier's original
  coordinate followed by division by its nonzero unit coefficient supplies
  the converse. This classifies existence, not physical production of that
  decoder. **Whole-route effect:** no regularity or Peierls-pairing restriction
  is responsible for the source-encoding obstruction.

- **DN40 — Lean verified; stronger matching no-go closed.** No arbitrary
  copy-dependent decoder of the literal source carrier matches the complete
  true/true action across nonzero amplitudes. DN35 supplies an actual
  critical copy; amplitudes one and two have identical zero carriers but
  distinct actions `A_q(1)` and `4*A_q(1)`. No vacuum assumption is used.
  Positive survivor: at an actual erased critical fibre, the full physical
  action distinguishes exactly the squared amplitudes. **Whole-route effect:**
  replacing only the returned vector or output reader cannot repair the
  original encoding; additional original source data must be retained.
  Fixed-amplitude fitting and encodings supplied with additional data are
  outside this obstruction. [Exact scope and classification](../5-failed/hb-full-canonical-source-encoding.md).
  `FullCanonicalSourceEncodingNoGo`: scratch and exact audit passed (102
  seconds, two jobs); umbrella wired; formal lint passed. RH remains open.

- **DN41 — Lean verified.** The original full Eisenstein scalar
  `scalar(center q)` is nonzero somewhere for every actual Xi copy. Its
  horizontal mean and first height derivative would force both original
  Weyl coefficients to vanish if the scalar vanished identically; reflection
  and the closed right-half-plane zero-free theorem exclude this. The
  unchanged time-domain source is consequently nonzero at some physical
  interior point on each branch, using its AdS-leading radial coefficient.
  **Whole-route effect:** no Xi copy is a vacuum source merely because a
  selected angular or QNM period cancels.

- **DN42 — Lean verified.** Equality of complete original causal
  potentials on the open physical wedge is equivalent to equality of
  squared amplitudes, for every Xi copy and both branches. An original
  local wave-operator observation, with point and nonzero normalization
  independent of amplitude, recovers exactly `a^2`.
  **Whole-route effect:** this gives a concrete physical observation of the
  information erased by the literal carrier, before QNM continuation.

- **DN43 — Lean verified.** No arbitrary copy-dependent decoder of
  the unchanged Peierls source carrier can reconstruct the original causal
  potential across nonzero amplitudes. An actual critical copy erases both
  amplitudes one and two; DN42 distinguishes their physical fields. The
  matched object is the original potential on `0<p<r`, not a classification
  modulo arbitrary metric gauge equivalences. Fixed-amplitude fitting and
  encodings retaining additional original data remain outside the no-go.
  **Whole-route effect:** temporal matching through this carrier already
  fails before taking a QNM readout. RH remains open.

  [Exact scope and positive recovery](../5-failed/hb-native-retarded-source-encoding.md).
  `NativeFieldMatchingNoGo`: scratch and exact audit passed (91 seconds, two
  jobs); umbrella wired without an umbrella build; formal lint passed.

- **DN44 — Lean verified.** At every actual Xi copy, the literal source
  contact `((7λ−2)Q−2ΔQ)/8` is nonzero somewhere. Identical vanishing would
  annihilate its entire two-jet; the established differential identity
  would then annihilate the original scalar, contradicting DN41.
  **Whole-route effect:** this coefficient cannot be treated as an absent
  term when deriving a pointwise transpose of the full original source.

- **DN45 — Lean verified; exact positive classification.** Every
  differentiable radial multiplier preserving the original opposite-branch
  source-transpose identity, with all amplitudes and onset times retained,
  is exactly `c(1+u)^5/u^4` on `x<0`, `u=−tanh(x)`. Conversely every such
  multiplier preserves that identity. The actual nonzero contact forces
  the weight equation; no freely chosen angular test is substituted.
  Its exact fourth-order boundary coefficient is
  `c a² timeOnset(2t,v) Q(z)`, with the original opposite rate `t`.
  **Whole-route effect:** the boundary charge is forced by source
  reciprocity throughout this class, rather than an arbitrary normalization.

- **DN46 — Lean verified; local matching option closed.** No nonzero
  differentiable radial multiplier preserving that full source identity
  gives finite AdS limits at every angular point. Consequently it cannot
  produce any physical fundamental QNM radial profile, even with an
  independent target Xi copy, either QNM branch or radial normalization,
  and arbitrary angular coefficient. This is a pointwise full-source
  result; projected actions, integral transforms, angular operators,
  changed clocks and extra boundary contributions are outside its scope.
  **Whole-route effect:** radial multiplication cannot repair this source
  transpose into an admitted QNM. General physical matching and RH remain
  open. [Proof and positive boundary-charge classification](../5-failed/hb-local-source-transpose-matching.md).
  Exact `LocalSourceTransposeRigidity` audit passed (53.67 seconds, two jobs);
  umbrella wired without an umbrella build.

- **DN47 — Lean verified.** The original compact onset pulse transform
  satisfies `P(0)=1` and `|P(z)|≤2 exp(2|z|)`. Its true/true QNM argument
  is exactly `5ρ/2−3`. Hence only `O(T)` actual simple critical Xi sources
  up to height `T` have a zero onset factor, with the original duration
  unchanged. **Whole-route effect:** a fixed onset cannot erase a positive
  fraction of the simple critical source census through this factor.

- **DN48 — Lean verified; positive pole-survival theorem.** Only `O(T)`
  actual simple critical Xi sources have zero original true/true physical
  fundamental residue. The census is `Ω(T log T)`, so surviving sources
  have relative density one. Their original continued Green response has
  no finite limit at the fundamental QNM, for every interior detector and
  every nonzero original amplitude. An actual surviving critical source
  simultaneously has an analytic full canonical action at that QNM.
  **Whole-route effect:** action regularity and response-pole disappearance
  are distinct; changing observables does not inherit a vanishing law.

- **DN49 — Lean verified; original pole matching option closed.** No
  arbitrary returned Peierls carrier matches the genuine unit-source
  fundamental residue at all Xi copies, even only in their zero loci.
  Every critical unit probe vanishes, while DN48 supplies actual critical
  sources with surviving poles. **Whole-route effect:** replacing the
  regular canonical value by the original Green residue does not repair
  the unchanged complementary unit-source clock. Other metric or nonlocal
  receivers, full temporal matching, fixed-time extinction and RH remain
  outside this theorem.
  [Exact scope and positive survivor](../5-failed/hb-original-green-pole-matching.md).
  `OriginalGreenPoleMatchingNoGo`: scratch passed (10.21 seconds); exact
  module audit passed (9.12 seconds, two jobs); umbrella wired without a build.
  Global lint reports the separate unwired `OnsetTransgressionHorizon` module.

- **DN50 — Lean verified; exact temporal classification.** The original
  canonical source profile is `K(u)=chi(u)*exp(2su)*(A+uB)`, with
  `A=−mu*C*((mu−2)*X+Y)` and `B=mu*C*(mu−2)*M`. For `u≥1`, its pair
  `(K(u),exp(2su)*B)` translates by `exp(2sT)*(k+T*b,b)`.
  Two late samples recover the second coordinate exactly. A scalar clock
  represents every late step iff `B=0`; eventual zero is equivalent to
  `A=B=0`, hence to an identically zero profile.
  **Whole-route effect:** the first source-time moment is retained data,
  not a scalar normalization or an arithmetic multiplicity claim.

- **DN51 — Lean verified; arbitrary finite-packet linear matching closed.**
  A finite exponential mixture with arbitrary, possibly repeated complex
  frequencies represents the late original profile only if `B=0`.
  Every surviving DN48 pole forces `B≠0` for all nonzero original
  amplitudes. Thus an actual critical Xi source excludes every finite
  packet encoding and every time-independent complex-linear readout of
  the original centered physical clock, for every overtone index.
  **Whole-route effect:** increasing packet size or retaining amplitude
  data does not repair this temporal matching. Infinite expansions,
  time-dependent readers and nonlinear observations are outside this no-go.

- **DN52 — Lean verified; positive matching formula.** At the original
  source-time coordinate, both source branches obey
  `K(u)=chi(u)*exp(−3u)*h(u)^4*(A+uB)`, where `h(u)` is the original
  centered-clock coordinate of the reflected unit copy for the true
  branch and the original unit copy for the false branch. The complete
  canonical temporal/metric/QNM action equals its convergent Laplace
  integral, with both original moment coordinates retained. No clock-time
  rescaling or fitted frequency is used.
  **Whole-route effect:** the source supplies an explicit quartic,
  time-dependent clock observation. This is not a conjugacy of the full
  PDE flow with the packet clock, a physical Peierls pairing, or RH.
  [Proof, obstruction and positive survivor](../5-failed/hb-original-source-clock-rigidity.md).
  `OriginalSourceClockRigidity`: scratch passed (82.10 seconds); exact
  module audit passed (93.83 seconds, two jobs); umbrella wired without a build.
  Global lint still reports the separate unwired `OnsetTransgressionHorizon` module.

- **DN53 — Lean verified; original time/radial reciprocity.** For the full
  theta-square Dirichlet kernel and two original reduced source branches,
  `f_b(t,x)*K(s-t,x,y)*f_c(s,y)` is absolutely integrable over both original
  positive time axes and both negative radial rays. Its majorant separates
  as `exp(-(alpha+g)t)*exp((g-alpha)s)*exp((2-alpha)(x+y))`, with
  `1<=g<alpha<2`. The established future response equals its source-event
  integral. Kernel radial symmetry and admitted Fubini give
  `integral f_b*A_c = integral R_b*f_c`, retaining both causal supports,
  the image term and fixed onset. **Whole-route effect:** reciprocity of
  this actual reduced-source bulk is constructed without an abstract
  reciprocity premise.

- **DN54 — Lean verified; actual antisymmetric source bulk and reflection.**
  The causal integral `integral f_b*(R_c-A_c)` equals the full kernel
  applied to `f_c(t,x)*f_b(s,y)-f_b(t,x)*f_c(s,y)`. Restoring the full
  angular testing square preserves absolute admission and skewness.
  Literal source reflection gives
  `P(reflect(q),true,false,a,d)=-P(q,true,false,d,a)` with independent
  amplitudes retained. **Whole-route effect:** the candidate now has an
  admitted source-integral bulk with proved skewness and branch exchange.
  The retarded null-field identification, advanced wave equation, lift/cap
  contributions and complete metric/QNM attachment remain unproved;
  this is not the completed physical Peierls matching or RH.
  [Proof and scope](hb-en-original-source-reciprocity.md).
  `FullSourceRadialReciprocity`: scratch 9.34 seconds; exact module audit
  11.95 seconds, two jobs; umbrella wired without a build.

- **DN55 — Lean verified; original kernel source vertex.** For the literal
  full-theta Riemann kernel in source-based null distances, compact
  separated-test transposition gives `integral H*phi'*psi' =
  Q*phi(0)*psi(0)+integral angularAction*phi*psi/(4*cosh(x)^2)`.
  **Whole-route effect:** the weak kernel equation retains the exact
  full-square source vertex and characteristic coefficient. General
  temporal tests and source-coordinate transport remain to be proved.

- **DN56 — Lean verified; strict growth after angular testing.** In the
  original log-height chart, set `T(psi)=DX²(exp(k)*psi)+
  Dk²(exp(-k)*psi)+Dk(exp(-k)*psi)`. For every smooth compact test,
  `integral exp(-k)*psi*angularAction = integral T(psi)*angularKernel`.
  The pairing is bounded by `C(q,psi)*exp(g*arcosh(t))`, with the original
  `g=1+2*abs(Re(center(q)))<2`. **Whole-route effect:** weak angular
  transposition supplies the strict growth margin needed for the future
  source without a pointwise angular-jet growth premise.

- **DN57 — Lean verified; full original future-source angular action.**
  The product of `T(psi)` with the original future density is jointly
  absolutely integrable in angular position, positive delay and the full
  negative radial ray. Its majorant separates as
  `exp(-alpha*tau)*exp((g-alpha)*h)*exp((2-alpha)*y)*
  norm(T(psi)(z))*exp(g*abs(im(z)))`, with `g<alpha<2`.
  Admitted Fubini identifies `integral T(psi)*originalFutureResponse` with
  the original reduced source integrated against the angular-tested
  direct-minus-image kernel, retaining both causal indicators and fixed
  onset. **Whole-route effect:** the actual future field now has this
  constructed weak angular action. The complete temporal wave equation,
  lift/cap equations and full metric/QNM attachment remain open.
  [Proof and exact remaining obligations](hb-eo-advanced-wave-transposition.md).
  `AdvancedKernelTransposition`: scratch passed; isolated exact module
  audit 119.64 seconds, two jobs; umbrella wired without a build.

- **DN58 — Lean verified; general temporal tests of the original kernel.**
  The native closed-cone Goursat kernel satisfies
  `integral H*eta_uv=Q*eta(0,0)+integral J*eta` for joint null tests.
  Smooth compact physical time/radius tests supply the far-edge conditions
  through compact support of their actual derivatives. The identity extends
  to the entire causal cone. **Whole-route effect:** temporal testing no
  longer requires separated time/radius tests or a density assumption.

- **DN59 — Lean verified; physical source normalization.** The actual
  advanced chart is `tau=s-(u+v)/2`, `x=y+(u-v)/2`. Its measure pushforward
  is `2*volume`, and its mixed derivative of a smooth physical test is
  `(partial_tau^2-partial_x^2)/4`. The area factor `1/2` and the original
  kernel half-factor give source coefficient one. **Whole-route effect:**
  the temporal operator and source vertex now share the actual coordinates
  and normalization, without a spectral or clock substitution.

- **DN60 — Lean verified; original Dirichlet temporal weak equation.**
  For every smooth compact joint time/radius test, the full native kernel
  obeys `integral [K_D*wave(phi)-A_D*phi/cosh(x)^2] =
  Q*(phi(s,y)-phi(s,-y))`, where `A_D` retains both causal angular actions
  and their half-factor. Both cone residuals are absolutely integrable.
  For `y<0` and tests supported in `x<0`, the result is exactly `Q*phi(s,y)`.
  **Whole-route effect:** general temporal source/image matching is closed
  at kernel level. The original infinite-response weak equation, lift/cap
  equations and complete metric/QNM matching remain open.
  [Proof and remaining source-level identity](hb-ep-general-temporal-transposition.md).
  `GeneralTemporalTransposition`: scratch passed; exact leaf audit
  40.29 seconds, two jobs; umbrella wired without a build.

- **DN61 — Lean verified; original source/target absolute admission.**
  The original source-event density times any continuous compact joint
  target test is absolutely integrable. A product majorant is
  `C*exp((g-alpha)*s)*exp((2-alpha)*y)*
  norm(phi(tau,x,z))*exp(-g*tau+g*abs(im(z)))`, with `g<alpha<2`.
  Admitted Fubini identifies this integral with the actual infinite future
  response tested in all four target variables. **Whole-route effect:**
  full source transposition is available without a pointwise angular-jet
  growth assumption, while retaining the fixed onset and entire radial ray.

- **DN62 — Lean verified; actual future response's full reduced weak wave.**
  For every joint smooth compact test `Phi` supported in `x<0`, the actual
  infinite future response `A` obeys
  `integral A*(exp(-k)*wave(Phi)-T(Phi)/cosh(x)^2)
  = integral exp(-k)*Q*S*Phi`. Both sides are absolutely admitted. Kernel
  temporal and angular transposition retain the source normalization and
  Dirichlet image; joint compact support removes the image vertex.
  **Whole-route effect:** the original response's reduced temporal/angular
  equation is closed. Original lift/cap equations, boundary identification
  and the full physical metric/left-QNM action remain open.
  [Exact proof and remaining matching obligations](hb-eq-full-source-weak-wave.md).
  `FullSourceWeakWave`: scratch passed; exact leaf audit 31.02 seconds,
  two jobs; umbrella wired without a build.

- **DN63 — Lean verified; source-horizon escape preserves weak action.**
  With original source time `s=v-y`, the invariant depends on the escaping
  source radius through `radialUnit(y) in [0,1]` for `y<0`. This compact
  parameter gives a uniform bound on each compact joint target test.
  Dominated convergence commutes the actual source-horizon kernel limit
  with that pairing. The source vertex leaves the test support, so the
  original direct-minus-image horizon kernel has zero bulk weak wave
  action. **Whole-route effect:** source-horizon passage retains the wave
  equation without pointwise angular-jet bounds or a postulated cap PDE.

- **DN64 — Lean verified; original cap preserves the reduced bulk source.**
  The actual cap equals `-2*liftTraceCoefficient*integral_(v>0) b(v)*H_v`,
  with original onset derivative `b`, both characteristic arms and original
  horizon kernel half-factor. A product majorant with `g<alpha<2` admits
  source-time/target Fubini. The cap is a homogeneous weak solution for
  every joint smooth compact physical test; its pairing is absolutely
  convergent. Subtracting it from the actual infinite future response
  preserves the complete original reduced source. **Whole-route effect:**
  cap bulk matching is closed. Assemble the existing pointwise source-lift
  equation with this response/cap identity, then identify the complete
  physical metric/current/left-QNM action and boundary data.
  [Proof and exact remaining obligations](hb-er-original-cap-wave.md).
  `OriginalCapWeakWave`: scratch passed; exact leaf audit 11.59 seconds,
  two jobs; umbrella wired without a build. No full matching or RH claim.

- **DN65 — Lean verified; complete original bulk source of the corrected future field.**
  For every joint smooth compact test supported in `x<0`,
  `U = timeLiftField + originalFutureResponse - capBoundaryField` satisfies
  `integral U*weakWaveTest(Phi) = integral exp(-k)*timeOriginalForcing*Phi`.
  Every field/source pairing is absolutely admitted. Temporal integration
  by parts and zero-radius angular transposition identify the original
  lift's actual wave. Original onset plus physical test support convert the
  reduced source-event integral to the full target integral; the existing
  gradient-absorption identity then restores the complete original forcing.
  **Whole-route effect:** original bulk source identification is closed for
  this corrected future field. Full metric/current reconstruction and the
  noncompact left-QNM/boundary action are not established by a compact-test
  weak equation. Matching and RH remain open.
  [Exact proof and scope](hb-es-complete-original-weak-source.md).
  `CompleteOriginalWeakSource`: scratch passed without errors or warnings;
  exact leaf audit 16.93 seconds, two jobs; umbrella wired without a build.

- **DN66 — Lean verified; admitted retarded inverse is the actual original field.**
  `retardedResponse((p+r)/2,(p-r)/2) = fullNullResponse(p,r)` for all real
  null coordinates, with the same original source, theta square and image.
  Odd reflection folds the whole-line source to the negative radial ray.
  Onset and causal support restrict the exact null transport to a compact
  source rectangle; its Jacobian preserves the original factor `1/4`.
  **Whole-route effect:** the admitted source reciprocity now uses the same
  retarded field as the existing actual metric/current construction.

- **DN67 — Lean verified; corrected future comparison retains an explicit cap.**
  With `U` the original lift plus actual future response minus original cap,
  `originalPotential-U = retardedResponse-response+cap` pointwise.
  Consequently the admitted source pairing is exactly
  `integral S_b*(originalPotential_c-U_c-cap_c)` on the complete original
  source-event domain. Its absolute integrability is proved separately.
  **Whole-route effect:** replacing the reduced future field by `U` must
  retain this cap contribution in the metric/current comparison; no cap
  current vanishing, full QNM matching or RH conclusion follows here.

- **DN68 — Lean verified; retarded event inverse has the original pulse reconstruction.**
  The admitted retarded response equals `-timeAngularSeedField/kappa +
  retardedNullAction(fullSourceOnsetPulse)/kappa`. The pulse and angular
  seed are the independently constructed original fields; the existing
  pulse support theorem confines ingoing time to `[0,1]`.
  **Whole-route effect:** the corresponding future reconstruction can be
  attacked through this specified pulse and the seed's horizon cap. That
  future identity is unproved; pulse support does not erase radial infinity
  or a boundary current.
  [Exact identities and remaining matching obligations](hb-et-original-retarded-causal-difference.md).
  `OriginalCausalDifference`: scratch passed without errors or warnings;
  exact leaf audit 104.81 seconds, two jobs; umbrella wired without a build.

- **DN69 — Lean verified; future seed Green identity retains one null face.**
  In source null coordinates `v=t_source+y,w=t_source-y`, cut at `w=L`.
  For `b(v,w)=sourceSeedField((v-w)/2)*timeOnset(v)`, use
  `K*b_vw-b*K_vw=partial_w(K*b_v)-partial_v(b*K_w)`.
  The actual direct and image diagonals cancel, leaving
  `A_waveSeed^L=Seed+integral_(p..L) K_D(v,L)*b_v(v,L)
  -integral_(r..L) K_I(v,L)*b_v(v,L)`.
  **Whole-route effect:** the required cap comes from a specified physical
  terminal face; this orientation needs no angular-kernel derivative limit.
  `FutureSeedFiniteGreen.finite_future_seed_wave`: the original fields,
  derivatives and characteristic values discharge all analytic premises.
  Scratch and exact leaf audit passed without warnings; audit 36.61 seconds,
  two jobs. Umbrella wired without a build.

- **DN70 — Lean verified; source growth controls the actual seed angular mean.**
  The inspected forced mean equation has limiting roots `2*s+1,-2*s-2`.
  Their real parts are bounded above by the existing
  `g=1+2*|Re(q)-1/2|<2`; for the positive root this follows separately
  on both physical branches. The two-mode squared energy absorbs
  `coth(d)-1<1/d` in the positive gap `gamma-g`, yielding
  `|M(d)|+|M'(d)|<=C exp(((g+2)/2)*d)` at each angular base point.
  The original clock exponent satisfies `2*Re(s)+gamma<0`, giving an
  integrable clock-weighted majorant for the mean and radial derivative.
  **Whole-route effect:** a strict decay margin for the independently
  specified seed cap is available without RH or a spectral projection.
  `FullAngularMeanGrowth.angularMean_growth` and
  `angularMean_terminal_majorant`: scratch and exact leaf audit passed
  without warnings; audit 19.25 seconds, two jobs. Constants may depend
  on the fixed angular base point; no global angular uniformity is claimed.

- **DN71 — Lean verified; specified future seed/pulse bridge.**
  The actual seed and lift first derivatives are `O(exp(2*y))` for
  `y<0`; pulse support in `v in [0,1]` confines causal circle radii to
  a compact interval. This admits the independently defined future
  pulse integral. DN69's terminal integrand has the integrable bound
  `C exp((2*Re(s)+(g+2)/2)*v)` and converges to the independently
  defined `-CSeed`. Combining with the already admitted original future
  response gives `kappa*A_Q+Seed=A_P+CSeed`, now verified in DN77.
  **Whole-route effect:** the future and retarded reconstructions use the
  same original seed/pulse and an explicit surviving cap. Differentiated
  metric/current admission and noncompact left-QNM matching remain open.
  [Derivation, factors, boundary terms and precise scope](hb-eu-future-onset-pulse-reconstruction.md).
  Its finite identity is verified in DN69 and DN72; the terminal cap and
  null-exhaustion limit in DN74; original-coordinate admission/exhaustion
  in DN75–DN76; exact coordinate identification and limit assembly in DN77.

- **DN72 — Lean verified; finite future reconstruction uses the original source balance.**
  `finite_future_source_balance` integrates the actual
  `fullSourceOnsetPulse-kappa*timeReducedCoefficient*fullSquarePotential`
  on the direct/image finite future null regions and obtains exactly
  `timeAngularSeedField+seedTerminal`. The original amplitude, clock,
  theta square, circle averaging and factor `1/4` remain present.
  **Whole-route effect:** the finite part of DN71's infinite bridge is now
  closed without a response or matching premise. DN75–DN77 identify its
  infinite limit with the original future integrals; full
  temporal/metric/QNM matching remains open.
  [Verified finite identity and remaining infinite bridge](hb-eu-future-onset-pulse-reconstruction.md).

- **DN73 — Lean verified; terminal angular control is uniform in both radial variables.**
  For `v>=0,y<=0` and every real target radius `x`,
  `arcosh(max(1,I(v-y-tau,x,y)))<=v+|tau|+log(4)`.
  The exact invariant is affine in `u=radialUnit(y) in [0,1]`;
  its numerator and `cosh(x)>=1` give `I<=2*exp(v+|tau|)`.
  Combining with DN70 yields one integrable physical-clock majorant for
  the actual full angular mean and radial derivative, independent of
  both `x` and `y`. This includes the direct and reflected target radii.
  **Whole-route effect:** the angular part of the moving terminal-face
  domination is closed; DN74 also supplies the actual seed factors and
  terminal limit; DN75–DN77 complete pulse admission and coordinate identification.
  differentiated metric/current and noncompact left-QNM matching remain open.
  `FullAngularMeanGrowth.source_horizon_radius_bound` and
  `angularMean_source_horizon_majorant`, audited with DN70.

- **DN74 — Lean verified; actual future seed boundary converges to its independent cap.**
  `seedTraceCoefficient=-kappa*power(2*s,2)*amp^2` is the actual seed limit;
  its radial derivative tends to zero. `seedCapField=-2*cSeed*integral_(v>0)
  timeOnsetFirst(v)*H_B(v)` retains the full angular mean, original
  direct/image characteristics and half factor. Its integrand is absolutely
  admitted, and the existing `seedTerminal` tends to `-seedCapField` for
  every real pair of null target coordinates. Consequently the original
  finite pulse-minus-source actions tend to `Seed-CSeed`.
  **Whole-route effect:** the terminal face in the frozen future bridge is
  closed without a matching/decay premise or a cap defined by discrepancy.
  DN75–DN77 identify that null exhaustion with `A_P-kappa*A_Q`.
  Metric/current and noncompact left-QNM matching remain open.
  `FutureSeedHorizonCap.seedTerminal_horizon_limit`, `seedCap_integrable`,
  `finite_source_balance_limit`: scratch and exact leaf audit passed without
  warnings; audit 28.91 seconds, two jobs. Umbrella wired without a build.

- **DN75 — Lean verified; pulse admission has a product majorant in original coordinates.**
  Choose `gamma=decayExponent(q)<alpha=(gamma+2)/2<2`.
  The actual seed derivative factors as `exp(2*y)` times a profile continuous
  on `u=radialUnit(y) in [0,1]`; the existing `radialLiftFirst_horizon` gives
  the same factor for twice the lift derivative. The fixed transition factor
  is bounded by `C exp(-alpha*v)` via the actual onset and its derivative.
  On either causal cone, circle radius is at most elapsed time `h`, so DN70
  and the existing native source bound give the pulse-kernel majorant
  `C exp(-alpha*tau) exp((gamma-alpha)*h) exp((2-alpha)*y)`.
  Both factors are integrable on `h>0,y<0`.
  **Whole-route effect:** absolute admission is proved directly in the
  original future coordinates; DN77 identifies it with DN74's null exhaustion.
  `FuturePulseAdmission.seedFirst_horizon`, `density_bound`,
  `density_integrable`, `response_fubini`: scratch check passed;
  exact leaf audit passed in 65.20 seconds, two jobs, with an informational
  `ring_nf` suggestion and no errors or warnings. Umbrella wired without a build.

- **DN76 — Lean verified; original outgoing cuts exhaust the admitted source balance.**
  `futureRegion(tau,L)={h>0,y<0,tau+h-y<=L}` increases to the entire
  original future source region. `truncatedResponse_limit` gives its
  pulse integral limit `A_P`; `sourceBalance_limit` gives the actual
  pulse-minus-source integral limit `A_P-kappa*A_Q` without a matching
  premise. This uses DN75 and the existing absolute admission of `A_Q`.
  **Whole-route effect:** the original-coordinate side of the scalar
  matching limit is closed. DN77 identifies this cut integral with the
  finite null Green action, including Jacobian, causal supports, image
  sign, and circle factor. Metric/current and
  noncompact left-QNM matching remain open. Audited in the same leaf as DN75.

- **DN77 — Lean verified; the original future scalar bridge is closed.**
  `FutureSourceBridge.finite_source_balance_coordinates` identifies the
  original outgoing cut of `P-kappa*S*Q` with the finite null Green action.
  Open/closed boundary sets agree almost everywhere. Under
  `v=tau+h+y,w=tau+h-y`, the direct cone is
  `p<=v,r<=w,v<=w,w<=L`; the image is `r<=v<=w<=L`.
  Both cone integrals are admitted separately. The exact area factor
  and unchanged half-kernel give the original factor `1/4`.
  Uniqueness of DN74 and DN76's limits proves `future_source_balance`:
  `kappa*A_Q+Seed=A_P+CSeed`, for every time, nonnegative radial depth,
  physical branch, source amplitude and angular base point. No matching,
  decay or response premise is added; the cap is independently defined.
  **Whole-route effect:** future scalar reconstruction uses the same
  original seed/pulse as the retarded inverse, with the surviving cap
  retained. Required metric/current regularity and noncompact left-QNM
  admission/identification remain open; RH is not proved.
  Scratch check passed in 74.69 seconds; exact leaf audit in 25.57 seconds,
  two jobs, no warnings. Umbrella wired without a build.

- **DN78 — Lean verified; the full future upper direct pulse is smooth through its corner.**
  For `a=v-r`, `b=1-exp(2*y)`, its actual invariant has
  `I-1=2*(1-exp(-w-a))*(exp(a)-1+b)/((1+exp(-w))*(2-b))`.
  Resolving `(a/T,b)` into `(t,t*u)` and `(t*u,t)` gives `I-1=2*t*H`
  with H strictly positive on both closed squares for `w,T>0`.
  Signed `arsinh` radii are smooth and equal the original radii at the
  compact parameters. The exact triangle Jacobian is `T*t`.
  Both full angular fields and the original transition derivative are retained.
  `cornerAction_eq_upperDirectAction` proves exact integral equality;
  `upperDirectAction_smooth` proves every target/cutoff derivative exists.
  `upperSample_original` identifies each sample with the original future pulse
  divided by `4*exp(2*y)`, and `future_invariant_compact` verifies time reversal.
  **Whole-route effect:** this characteristic corner is no longer an obstruction
  to differentiating the actual pulse. Lower direct/image assembly, equality
  with the admitted source-event response, cap regularity, and noncompact
  left-QNM matching remain open. RH is not proved.
  Leaf `ThetaCuspHawkingBMFuturePulseCorner`: scratch 42.12 seconds; exact audit
  85.13 seconds, two jobs, no warnings. Source/olean verified; umbrella wired.
  Repository lint still flags the pre-existing unwired OnsetTransgressionHorizon.

- **DN79 — Lean verified; one smooth cutoff covers the full pulse at every target time.**
  `T(r)=1+exp(-r)>0` obeys `r+T(r)>=2`, directly from the inspected
  `Real.add_one_le_exp (-r)`. Since the actual pulse vanishes for source
  ingoing time `v>1`, both upper future regions may be truncated at this
  smooth cutoff without losing any source. The lower direct region remains
  `p<=v<=r`. **Whole-route effect:** global assembly of DN78 with the two
  remaining characteristic charts needs no target-dependent cutoff patches.
  The exact compact-to-source-event integral identification is still required;
  `FuturePulseAssembly.pulseSpan_covers` formalises the cutoff; DN80–DN81
  formalise the compact assembly and its cutoff tail.

- **DN80 — Lean verified; all three compact future pulse regions form one smooth action.**
  Lower direct uses `v=r-w+w*a,z=exp(-w*(1-a))*b`, Jacobian
  `w*exp(-w*(1-a))`; upper image uses `v=r+T*a,z=b`, Jacobian T.
  Their exact invariants factor into `2*a*(1-b)*Hlower` and `2*a*Himage`,
  with both H strictly positive on the closed source square for w,T>0.
  Smooth signed radii agree with the original radii there.
  `edgeAction_eq_integral` and `upperDirectAction_eq_integral` preserve
  every source coordinate factor. `compactFutureAction_eq_charts` assembles
  lower direct + upper direct - image using DN79's smooth span;
  `compactFutureAction_smooth` proves joint smoothness in r, log(w), X, k.
  `compactSample_original` identifies both kernels with the original pulse
  divided by `4*exp(2*y)`. No angular channel or original clock is replaced.
  **Whole-route effect:** compact regularity of the entire pulse formula is
  closed; exact identification with admitted source-event A_P remains open.
  Horizon-cap regularity and noncompact left-QNM matching still remain.
  Leaf FuturePulseAssembly: scratch 32.21 seconds; exact audit 101.52 seconds,
  two jobs, no warnings. Source/olean verified and umbrella wired.

- **DN81 — Lean verified; the actual compact mean loses no outgoing-cut strip.**
  For either image choice and every finite v interval `[a,b]`,
  `integral_(a..b) integral_(0..exp(v-L)) compactMean(v,z)` tends to zero.
  The mean extended by `z -> max(0,z)` is continuous in `(v,z)` and equals
  the original mean on this strip. Writing `epsilon=exp(-L)` reduces its
  limit to continuity of a finite parameter-dependent primitive at epsilon=0.
  **Whole-route effect:** the needed source-horizon cutoff removal is closed
  without a new growth/decay premise. The finite-cut equality with the original
  gated source-event integral remains necessary before invoking uniqueness
  with the already admitted A_P limit. `compactMean_cut_tail`, audited in DN80.

- **DN82 — Lean verified; the admitted original future pulse is jointly smooth.**
  The original gated source-event cut equals direct compact cut minus image
  compact cut, with exact null and exponential Jacobians. After the single
  support cutoff, it equals the full compact action minus two direct strips
  plus one image strip. DN81 removes all three strips; uniqueness with the
  original `truncatedResponse_limit` proves `response_eq_compactFutureAction`.
  `original_response_smooth` proves joint smoothness in r,W,X,k for
  `tau=r-exp(W)/2,x=-exp(W)/2`, covering the physical radial interior.
  Both original angular fields, both causal indicators and the fixed pulse
  are retained. **Whole-route effect:** original future-pulse regularity is
  closed; horizon-cap regularity, differentiated metric/current identification
  and noncompact left-QNM admission remain. Full matching and RH are not proved.
  Leaf FuturePulseIdentity: scratch 41.29 seconds; exact audit 104.41 seconds,
  two jobs, no warnings, default heartbeats. Source/olean verified; umbrella wired.
  Lint has only the pre-existing unreachable OnsetTransgressionHorizon error;
  no new-leaf error. Owned check/audit processes exited and scratch was removed.

- **DN83 — Lean verified; both original horizon caps share one fixed source radius.**
  `V_x(h)=tau+log(cosh(x)*exp(h)+sinh(x))` maps `h>0` bijectively to
  `v>tau+x`; its Jacobian is `cosh(x)*exp(h)/(cosh(x)*exp(h)+sinh(x))`.
  The actual horizon argument is exactly exp(h). `sourceArm_eq_fixedArm`
  retains the original positive-time domain and characteristic gate;
  `liftCap_eq_fixed` and `seedCap_eq_fixed` attach both admitted original caps.
  `combinedCap_eq_fixed` identifies `CSeed-kappa*CLift` with kappa times
  the original squared-amplitude factor and the fixed-arm difference for
  `B-s*(s-1)*Q/4`. Both characteristic arms remain.
  **Whole-route effect:** differentiation can target explicit scalar weights
  without moving the angular sampling radius. It does not identify the full
  physical Peierls/QNM observable with the canonical source-profile receiver.
  Leaf FixedSourceHorizon: scratch 12.41 seconds; exact audit 16.05 seconds,
  two jobs, no warnings, default heartbeats. Source/olean verified; umbrella wired.
  Existing seed-cap arm theorem made public with unchanged proof; exact
  dependency audit 58.73 seconds, two jobs, no warnings.

- **DN84 — Lean verified kernel; analytical temporal/radial cap regularity.**
  Beyond the unchanged onset interval the weight is `exp(2*s*h)*W(tau,x,exp(-h))`.
  Its denominator `cosh(x)+z*sinh(x)=(1-z)*cosh(x)+z*exp(x)` is strictly
  positive for `0<=z<=1`. `tailWeight_smooth` proves W smooth through z=0;
  `late_weight_factorization` proves exact equality with the original weight.
  On a compact tau/x neighborhood all its target derivatives are bounded
  uniformly in z. The already proved mean growth gamma<2 and `Re(2*s)<-2`
  give the same integrable tail exponent at every temporal/radial order.
  Finite-prefix integration plus dominated differentiation proves joint
  temporal/radial C-infinity regularity of both caps on paper, at fixed X,k;
  that integral-regularity theorem is not yet formalised. **Whole-route effect:**
  angular differentiation remains a distinct obligation. Norm-of-mean growth
  alone does not justify the proposed absolute fixed-plane source integral.
  Full temporal/metric/QNM matching and RH remain open.

- **DN85 — Lean verified; quantitative global mean-square bound for the actual response.**
  A modular cell meeting the radius-R hyperbolic ball, R>=0, has representative
  entries bounded by `2 exp(R)`: bottom-row square norm <=`2 exp(R)`, top-row
  square norm <=`2 exp(2R)`. Integer-box counting gives at most `(7 exp(R))^4`
  projective cell pullbacks. The original scalar lift satisfies
  `integral_ball |lift(u)|^2 <= (7 exp(R))^4 integral |cellExtension(u)|^2`.
  `globalResponse_ball_square_bound` attaches this bound to the actual smooth
  full-forcing response with `u=embedding(weakResponse(q,branch))`; its native
  zero-extension integral is finite by the established L2 membership.
  **Whole-route effect:** supplies quantitative absolute source control that
  cannot be inferred from norm-of-spherical-mean growth. No angular-jet growth
  premise is added. Leaf ModularBallGrowth: scratch 43.48 seconds; exact audit
  8.59 seconds, two jobs, no warnings, default heartbeats; umbrella wired.

- **DN86 — Analytical proof; absolute angular admission closes the cap regularity argument on paper.**
  Hyperbolic ball area <=`2*pi*exp(R)` and DN85 give L1 ball growth
  `C exp(5R/2)` for the actual L2 remainder. The explicit three cusp powers
  and existing `fullSquarePotential_global_growth` have pointwise ball growth
  exponents below 2, hence L1 exponents below 3. Therefore the complete
  `F=B-s(s-1)Q/4` admits every radial weight `exp(-p*d)`, p>3, by geometric
  shell summation. The original fixed-plane kernel has exactly
  `p=1-2 Re(s)>3`. Every target derivative preserves this exponent because
  `D=cosh(x)*cosh(d)+sinh(x)` stays positive and every target derivative of
  `cosh(d)=((X-a)^2+Y^2+y^2)/(2Yy)` is bounded by a compact-target constant
  times cosh(d). Substituting `h=log(cosh(d))` in DN83 gives the exact polar
  measure and original kernel. Absolute Fubini and dominated differentiation
  prove joint C-infinity regularity of both original caps on paper, without
  bounds on differentiated sources. DN88–DN89 formalise weighted absolute
  admission. The parameter theorem and original-cap attachment remain
  unformalised; DN85 alone is not that theorem. **Whole-route effect:** removes the analytical angular regularity
  obstruction to differentiating the full corrected field; noncompact physical
  left-QNM admission and field/action identification remain open. Full proof:
  `hb-fe-absolute-angular-admission.md`. Full matching and RH are not proved.

- **DN87 — Lean verified; weighted absolute admission of the actual response.**
  In the original hyperbolic volume, radius-R ball area is at most `8 exp(R)`.
  Combining this with DN85 via `|f| <= (|f|^2/t+t)/2`, `t=exp(3R/2)`,
  proves `integral_ball |globalResponse(q,branch)| <= C exp(5R/2)`.
  Geometric shell summation proves integrability of
  `exp(-p*dist(z,i))*|globalResponse(q,branch,z)|` for every `p>5/2`.
  The response theorem has no additional growth or integrability premise.
  **Whole-route effect:** supplies absolute admission of the actual L2 remainder
  needed for the fixed-plane cap representation. DN88–DN89 attach the cutoff,
  full square and kernel; cap differentiation and physical left-QNM field/action
  identification remain distinct formal obligations. Full matching remains open.
  Leaf `ThetaCuspHawkingBMWeightedResponseAdmission`: scratch 5.69 seconds;
  exact audit 7.26 seconds, two jobs, no warnings; umbrella import wired.

- **DN88 — Lean verified; full-source admission at the unchanged physical exponent.**
  All three principal cusp powers have real exponent at most two; the actual
  cutoff vanishes below height two. Modular invariance and orbit-height control
  give `|globalCuspCutoff|<=C max(1,y,1/y)^2`. The proved full-square bound
  gives the same ceiling. Ball area then yields absolute mass `O(exp(3R))`;
  geometric shells admit every weight with exponent p>3. Combining DN87 proves
  weighted absolute admission of `B-aQ` for every complex a and every radial
  center. The original fundamental rate satisfies `-2<Re(s)<-1`, so the actual
  `F=B-s(s-1)Q/4` is admitted at `p=1-2 Re(s)>3`, with no new growth premise.
  **Whole-route effect:** closes the complete source estimate needed for
  fixed-plane cap admission; no angular remainder or mixed cusp term is dropped.
  Leaf `CompleteSourceAdmission`: scratch 87.91 seconds; exact audit 42.58
  seconds, two jobs, no warnings; default heartbeats; umbrella wired.

- **DN89 — Lean verified; original two-arm plane-kernel admission and exact density.**
  For `D=cosh(x)cosh(d)+sinh(x)` and
  `c_x=min(cosh(x),exp(x))/2>0`, `D>=c_x exp(d)`. The original onset bound
  yields `|cosh(x) onsetFirst(v,tau+log(D))/D|<=C exp(-(1-Re(v))d)` for
  `Re(v)<=1`, with C independent of source and target points. At v=2s, DN88
  proves absolute admission of both arms of the complete F, including original
  factor `parameter(q,branch)*power(2s,2)*amp^2/(2*pi)`.
  `planeKernel_radial_density` proves the exact pointwise equality between
  `sourceJac*onsetFirst*sinh(d)/cosh(d)` and `planeKernel*sinh(d)` under
  `h=log(cosh(d))`. **Whole-route effect:** absolute source admission and the
  radial density are proved. The global hyperbolic polar integration identity,
  equality with the original cap, parameter differentiation, and physical
  left-QNM pairing remain open; full matching and RH are not proved.
  Leaf `PlaneKernelAdmission`: scratch 9.54 seconds; exact audit 10.03 seconds,
  two jobs, no warnings; default heartbeats; umbrella wired.
