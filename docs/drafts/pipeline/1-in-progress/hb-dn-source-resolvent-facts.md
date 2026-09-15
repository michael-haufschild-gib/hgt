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
