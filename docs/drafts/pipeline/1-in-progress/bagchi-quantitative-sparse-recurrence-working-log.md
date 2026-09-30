# Bagchi sparse recurrence — working log

Updated: 2026-09-12. Scope: facts and no-gos established during this research thread. No proposals.

## Facts

- **F01 — Receiver only.** `RecurrenceZeroDensity.lean` proves abstract zero transfer/counting
  contradiction from supplied recurrence and zero-count inequalities; it does not produce zeta
  recurrence.
- **F02 — Finite torus cost.** Finite prime-phase return volume is of order `epsilon^d`; available
  deterministic delay is `(Q+1)^d` at error `2*pi/(Q+1)`.
- **F03 — Current zero-density range.** Actual Lean strict-right zeta zero count begins at
  `sigma=7/10`, with exponent at most `(16/5)(1-sigma)`. No corpus theorem wires Huxley large values
  to a zeta zero count for every `sigma>1/2`.
- **F04 — Uniform winding gap.** One actual Xi circle around a critical-line zero has nonzero
  winding and a fixed positive sup-distance from every continuous periodic zero-winding loop.
  Evidence: `exists_xiBoundaryLoop_zeroWinding_uniformGap`.
- **F05 — Fixed-scale AFE bounds.** Available displaced Gaussian-AFE estimates give deep reflected
  tail `C*L^(-1)+D*(1+|tau|)^4*L^(-7/2)` and classical-head replacement error
  `E*|tau|^(-eta)*(1+L^(1/2+eta))`, `0<eta<=1/4`.
- **F06 — Phase-cell resonances survive.** Conditioned Bohr mean of every integer frequency
  supported on conditioned primes equals its positive Fejer multiplier
  `product_p(1-v_p(n)/(N_p+1))`, bounded below by `product_p(N_p+1)^(-1)`.
- **F07 — Exact dual target.** At fixed `x>0`, with direct edge `D`, dual edge `M`, pole residue `R`,
  `M(t)-(M(s)+R(s))=(D(t)-D(s))-(zeta(t)-zeta(s))-R(t)`. Direct recurrence plus `R(t)->0`
  makes zeta recurrence equivalent to synthesis of target `M(s)+R(s)`. Evidence:
  `RHTower.SmoothAFEZetaGeneralSelfRecurrenceDualNecessity`.
- **F08 — Terminal scale.** At `Re(s)=1/2+d`, fixed-`x` dual length is comparable to `T/x`;
  chi size `T^(-d)` times coefficient square mass `N^(2d)` gives order-one full-block variance.
  Any head `N=T^alpha`, `alpha<1`, has normalized variance `T^(-2d(1-alpha))`.
- **F09 — Prime-only shell.** Primes in `(N/2,N]` have total radius of square-root order divided by
  `log T`, but variance of order `1/log T`.
- **F10 — Exact largest-prime carrier decomposition.** For arbitrary complex `a` and `X<Y^2`,
  `sum_{n<=X} a_n X_n = B_Y + sum_{Y<p<=X} X_p C_p`, with
  `C_p=sum_{m<=X/p}a_(pm)X_m`. Every cofactor satisfies `m<Y`; `B_Y` and `C_p` read only phases at
  primes `<=Y`; channel prime `p` is outside that set. Evidence:
  `RHTower.SteinhausLargestPrimeDecomposition`.
- **F11 — Complex Steinhaus Parseval.** For finite nonzero support and arbitrary complex
  coefficients, `E|sum a_n X_n|^2=sum|a_n|^2`. Evidence:
  `RHTower.SteinhausComplexSecondMoment`.
- **F12 — Exact channel-energy partition.** Expected squared energies of all largest-prime channels
  equal coefficient square mass of the non-`Y`-smooth sector. Evidence:
  `steinhausCoefficientMass_eq_smooth_add_largePrimeChannelEnergy`.
- **F13 — Axiom audit.** F07, F10, F11, F12, F15--F20 depend only on `propext`,
  `Classical.choice`, and `Quot.sound`; targeted builds pass.
- **F14 — Dense-support Gaussian warning.** arXiv:2605.21737 proves, in its random multiplicative
  setting, that its standard complex-Gaussian CLT forces sparse support; it does not exclude a
  Gaussian mixture or direct full-support law.
- **F15 — Variable-cofactor channel floor.** For `0<d<1/2`, prime `p` with `2p<=N`, and normalized
  model weight `N^(-2d)n^(-(1-2d))`, the dyadic cofactor block `N/(2p)<m<=N/p` contributes at least
  `((1/2)/2^(2d))/p`. Evidence: `normalized_power_channel_lower_recip`.
- **F16 — Positive ideal terminal mass.** Summing F15 over primes between the half- and
  two-thirds-power cuts gives an eventual positive normalized lower bound. Their reciprocal mass
  tends to `-log(1/2)+log(2/3)=log(4/3)>0`. Evidence:
  `eventually_normalized_power_terminal_channels_lower`.
- **F17 — Direct right-line conductor localization.** If `0<d`, `d+eta<1/2`, and `Y>0`, the
  actual right-line dual weight satisfies
  `|W_R(d,tau,Y)-1| <= C*Y^eta/(max 1 |tau|)^eta`. The proof shifts the Gaussian contour from
  `Re w=1` to `Re w=-eta`; the analytic domain is `Re w>d-1/2`, and the chi-ratio contributes
  exactly the net power `|tau|^(-eta)`. Evidence:
  `exists_norm_smoothAFEZetaRightDualWeight_sub_one_le_conductor`.
- **F18 — Actual right-line AFE connection.** The general AFE coefficient at
  `s=1/2+d+i*tau` is exactly `-(chi(s)n^(s-1)W_R)`, and its error from the classical main term is
  bounded by the main-term norm times `C*((n*x)/(max 1 |tau|))^eta`. The corresponding exact
  two-series AFE and a separately reflected AFE with an ordinary primal cutoff are Lean-proved.
  Evidence: `exists_norm_smoothAFEZetaDualCoefficientGeneral_right_add_main_le`,
  `riemannZeta_rightDisplaced_eq_two_tsum_smoothAFE_dualWeight`, and
  `riemannZeta_rightDisplaced_eq_reflectedPrimal_add_complement`.
- **F19 — Literal reflected-AFE terminal mass.** On `tau in [N,2N]`, reflection of the left-line
  chi upper bound gives `|chi(1/2+d+i*tau)| >= c*N^(-d)`. The ordinary cutoff has norm at least
  `1/2` on one fixed inner interval. Consequently the half-to-two-thirds prime-power channels of
  the literal reflected-primal AFE coefficients have an eventual uniform positive aggregate
  square-mass floor. Evidence: `exists_norm_zetaChi_rightDisplaced_ge_nat_window`,
  `norm_sq_smoothAFEZetaRightReflectedPrimalCoefficient_eq_actual`, and
  `exists_eventually_reflected_actual_terminal_channels_lower`.
- **F20 — Literal conditional-energy event.** Squaring any complex Steinhaus carrier gives its
  finite Dirichlet convolution; complex Parseval plus the divisor-fibre bound gives fourth moment
  at most `C_epsilon*(M^2)^epsilon*variance^2`. Weighted Cauchy aggregates channels without their
  cardinality, zero-variance channels vanish exactly, and Paley--Zygmund gives probability at least
  `1/(4*C_epsilon*(N^2)^epsilon)` that literal reflected-primal terminal channel energy exceeds
  half a fixed positive mass. Evidence: `exists_integral_norm_four_steinhausFinCarrier_le_rpow`,
  `exists_measure_steinhausFinEnergy_gt_half_ge_rpow_of_totalVariance_pos`, and
  `exists_eventually_measure_reflectedPrimalChannelEnergy_gt_ge_rpow`.
- **F21 — Joint covariance is an explicit arithmetic Gram form.** For any finite node family and
  complex direction `u`, a linear combination of largest-prime channels equals the channel of the
  combined coefficients. Frozen-channel Parseval identifies its conditional large-prime covariance
  with the sum of squared channel combinations; averaging the small phases identifies that sum with
  the explicit prime--cofactor coefficient Gram energy. Complex Cauchy--Binet expresses the Gram
  determinant as the sum of squared maximal coefficient minors, so any one selected terminal minor
  gives a quantitative determinant floor. Evidence: `integral_normSq_steinhausFiniteNodeLargePrimePacket`,
  `sum_integral_normSq_reflectedPrimalFiniteNodeChannelCombination`, and
  `norm_sq_steinhausFiniteNodeFeatureMinor_le_gram_det_re`.
- **F22 — Stable real-terminal power minor.** For distinct node exponents, the normalized terminal
  rows `z ↦ exp(β_j z)` remain linearly independent after restriction to every nonempty real
  interval embedded in `ℂ`. Hence every such interval contains pairwise distinct real log-samples
  with a nonzero square evaluation determinant. Continuity upgrades that determinant to a fixed
  positive norm floor whenever each sample stays in one sufficiently small neighborhood. Evidence:
  `exists_realComplexInterval_powerEvaluation_det_isUnit` and
  `exists_powerEvaluation_det_norm_lower_neighborhood`.
- **F23 — Linear sample supply in every fixed normalized interval.** For `0 ≤ a < b`, each terminal
  prime channel contains at least `(b-a)N/p - 1` cofactors with `pm/N ∈ (a,b]`. Summation gives the
  reciprocal-prime main term; the accumulated floor loss is `#terminalPrimePowerWindow N = o(N)`.
  Hence some `c>0` gives at least `cN` terminal prime--cofactor samples eventually. Evidence:
  `terminalPrimePowerWindow_normalizedProductCofactorBlock_card_lower` and
  `exists_eventually_terminalPrimePowerWindow_normalizedProductCofactorBlock_card_linear`.
- **F24 — Colored many-minor compensation.** Strictly ordered finite color blocks inject their
  transversals into distinct canonical Pluecker coordinates, so a common minor norm floor `c`
  contributes `product(card S_j)*c^2` to the Gram determinant. Product-first ordering of terminal
  prime--cofactor features makes nonoverlapping normalized intervals strictly separated. Each fixed
  interval has `Ω(N)` actual features; finitely many intervals therefore supply `Ω(N^J)` distinct
  minors. Evidence: `prod_card_mul_sq_le_hermPluckerNormSq_of_coloredChoices`,
  `exists_eventually_prod_terminal_normalizedProductFeatureBlock_card_ge_pow`, and
  `prod_normalizedProductBlock_card_mul_sq_le_arithmeticGram_det_re`.

## No-gos

- **N01 — Zero-free finite Euler carrier plus uniformly vanishing tail.** Impossible on a decisive
  zero-enclosing boundary by F04.
- **N02 — Ordinary universality with shrinking slit, current input.** Missing-arc winding control
  requires an exterior zero-free buffer; no uniform shrinking-compact density estimate is present.
- **N03 — Fixed-scale AFE power truncation.** `L=T^a` requires simultaneously `a>8/7` from deep tail
  and `a<eta/(1/2+eta)<=1/3` from conductor localization.
- **N04 — Fixed-`d` generalized recurrence then `d->0`, current input.** No uniform onset/count on
  intervals of length `O(1/|d|)`; fixed-parameter density does not supply required near-identity
  shift.
- **N05 — Whole-interval tail-good set plus phase-return set.** Separate positive-measure statements
  do not force intersection; any conclusion reducing to N01 is impossible.
- **N06 — Recent shrinking-target transfers inspected.** IID Haar thinning and mixing-map
  metastability do not apply to deterministic irrational prime flow or couple to zeta tails.
- **N07 — Vitali from available moments on phase cells.** Cell mass decays exponentially in prime
  dimension while right-half-plane truncation improves only polynomially; second/fourth moments do
  not yield local boundedness on selected cells.
- **N08 — Naive conditioned diagonal mean square.** False by F06: all smooth-ratio cross terms retain
  positive multipliers.
- **N09 — Coordinatewise terminal targeting at same height.** Polynomially many terminal phases
  give superpolynomial return delay; logarithmically many phases give vanishing total amplitude.
- **N10 — Prime-only terminal synthesis as order-one variance source.** False by F09; it is a
  moderate-deviation problem.
- **N11 — Standard dense-support complex-Gaussian CLT as default target.** Unsupported and contrary
  to F14 in the paper's setting; no general impossibility beyond that setting is claimed.
- **N12 — Fixed-cofactor subterminal channel.** At `Re(s)=1/2+d`, `d>0`, a channel with fixed
  cofactor and primes `p<=T^theta`, `theta<1`, has normalized square mass at most logarithmic factors
  times `T^(-2*d*(1-theta))`; it vanishes. Constant reciprocal-prime mass at `d=0` does not solve
  recurrence on a compact containing a zero with fixed positive displacement.
- **N13 — Marginal small-ball bounds as simultaneous boundary control.** False as a general
  principle: arXiv:2609.11795 constructs fixed-direction small-ball lower bounds with catastrophic
  failure after searching over a low-Gaussian-width family. C15 needs a joint finite-node law or a
  proved complexity/occupancy bound, not nodewise estimates alone.
- **N14 — Shifted anticoncentration as target recurrence.** arXiv:2609.06526 gives uniform *upper*
  small-interval bounds for a conditional Gaussian scale mixture by controlling inverse conditional
  variance. C15 needs a *lower* probability near its prescribed planar target; the theorem's model
  and inequality direction do not supply it.
- **N15 — Sub-conductor localization alone does not control the terminal edge.** F17 tends to zero
  when `Y/|tau| -> 0`, but at the terminal scale `Y` proportional to `|tau|` its upper bound is only
  `O(1)` and gives no lower bound for `|W_R|`. Positive survivor: F18's reflected AFE moves the
  terminal carrier to the ordinary primal cutoff, where a fixed inner fraction can be treated by
  the independent cutoff estimate. F19 completes that surviving transfer.

## 2026-09-30 independent producer continuation

- **F25 — Uniform literal finite-node mean Gram floor.** For fixed distinct nodes
  `1/2+d_j+i*b_j`, `0<d_j<1/2`, there exist `r,c>0` such that eventually for all
  `tau in [5N/4,7N/4]` the actual reflected-primal arithmetic Gram determinant over
  `terminalPrimePowerWindow N` is at least `c`. Exact common-height phases drop out of minor
  norms; positive cutoff and chi envelopes give `N^(-J/2)`, while colored multiplicity gives
  `N^J` squared minors. Evidence:
  `RHTower.exists_eventually_reflectedPrimalFiniteNode_gram_det_lower_height_window`,
  `SmoothAFEZetaReflectedFiniteNodeGram.lean`. Leaf audit and six axiom audits pass with standard
  axioms only. Umbrella wired; index refreshed. Global lint still reports unrelated unreachable
  modules. No recurrence or RH claim; conditional covariance/target law/orbit transfer remain.
- **F26 — Next exact quantity.** Joint synthesis requires the conditional matrix, not its mean.
  Product-frequency collisions in a determinant expansion must be combined before Parseval.
  C16/C16a in the main card record the live producer attack; no substitute receiver was added.
- **F27 — Exact conditional determinant fibres and common-height removal.**
  `SmoothAFEZetaConditionalGramFibres.lean` proves the literal determinant carrier identity,
  collision-faithful Parseval, the full Gram energy identity, its exact expectation, and subpower
  fourth moments. `SmoothAFEZetaConditionalGramShape.lean` proves that each complete signed fibre
  has one common height phase; its norm loses that phase exactly. Main identity:
  `integral_reflectedPrimalConditionalGram_det_eq_shape`. The conditional mean determinant is
  the chi/conductor row scale squared times an explicit height-independent shape mass. Both leaf
  compilations passed without warnings. The lower shape-mass estimate remains open.
- **F28 — Probabilistic scale and alternate source construction.** C16b now asks for a same-event
  inverse-covariance target cost `o(log N)`, allowing a slowly shrinking covariance floor. Hardy's
  scalar critical-chaos result is evidence for that scale, not a weighted matrix/orbit theorem.
  C17 records a slow-cofactor, multi-mode phase construction as an unproved paper candidate.
  Corpus Selberg--Delange assembly still takes the fractional Kato asymptotic as a premise and
  cannot supply this construction. No new receiver, RH premise, or numerical experiment added.
- **F27 validation checkpoint.** Final leaf audits used `lake --old env lean -o ...`; all eight
  exported theorem axiom audits passed in `/tmp/BagConditionalFibresAudit.lean`, with only
  `propext`, `Classical.choice`, `Quot.sound`. Both new modules are wired into `RHTower.lean`.
  Global formal lint exited 1: unrelated unreachable modules and a concurrent `sorry` in
  `XiSliceLogLogOrderDensity.lean:403`. It reported no issue in these BAG modules. The formal
  index is refreshed after integration. Independent recurrence and RH remain unproved; goal active.
- **F29 — Unconditional finite-prefix means.** `SteinhausFinitePrimeCofactorMean.lean` evaluates
  the nonzero mean of every finite prime-phase defect by a finite Euler product and proves an
  exact coherent twist extension preserving the prescribed prefix. Final leaf compilation passed.
- **F30 — Weighted coherent cofactor modes.** `SteinhausFinitePrimeWeightedCofactor.lean` proves
  the normalized weighted limit `A_S(t)/(s_j+i*t)` directly by divisor convolution and dominated
  Tannery. Final leaf compilation passed without warnings. All eleven exported results across F29
  and F30 passed axiom audit in `/tmp/BagFinitePrefixAudit.lean`, with standard axioms only.
  Both modules are wired into the umbrella. Next: assemble one full-rank cofactor packet while
  preserving earlier finite prefixes. Quantitative covariance, same-event background/target cost,
  uniform moving-height control, and orbit transfer remain open.

- **F31 — Compatible full-rank cofactor packet.** `SteinhausFinitePrimeCofactorRank.lean`
  constructs one phase extending any finite prescription and a nonzero node determinant with
  all cutoffs above any prescribed bound. Cauchy modes escape every proper subspace; freezing
  earlier prefixes keeps earlier rows fixed. Final leaf and all four exported axiom audits pass
  with standard axioms only. Umbrella wired and index refreshed. Global lint reports ten
  unrelated unreachable modules, no issue in these BAG leaves. C17.4 strengthens isolated
  cutoffs to whole coherent blocks before attempting literal covariance growth.

- **F32 — Prescribed separated cofactor blocks with arbitrary energy budget.**
  `SteinhausFinitePrimeCofactorModes.lean` constructs one phase preserving any finite prescription
  and approximating prescribed Cauchy modes on whole blocks `[M_i,2*M_i]`. Blocks are separated,
  every prefix mean `A_i` is nonzero, and `M_i*|A_i|^2` exceeds any prescribed budget. Final leaf
  and both exported axiom audits pass with standard axioms only. This retains the intended energy
  gain when passing to reciprocal prime intervals. Smooth cutoff and literal channel transfer
  remain; no conditional centre bound or recurrence claim is made.

- **F33 — Gaussian cutoff transfer on every constructed block.**
  `SmoothAFEFinitePrimeCofactorModes.lean` proves convergence of each literal finite Gaussian
  cofactor vector to its hard-cutoff vector and preserves every prescribed mode uniformly for
  all `0<r<=r0`, with one common threshold across the separated blocks. Final leaf and both
  exported theorem axiom audits pass with standard axioms only. The complete F29–F33 chain has
  five warning-free leaf compilations and nineteen exported theorem axiom audits, all standard.
  All five modules are wired into `RHTower.lean`; index refreshed. Latest global lint exits 1
  on eleven unrelated unreachable modules, with no issue in these BAG leaves. Targeted
  whitespace checks pass. No full/umbrella build or numerical experiment was run.
- **Producer checkpoint after F33.** Next exact obligation: remove common height and factor
  literal largest-prime channels through F33's cofactor vectors; control the floor-normalization
  node factor; count primes in the new proportional intervals; prove the resulting conditional
  Gram lower bound. The old half-to-two-thirds-power terminal window does not contain these
  primes. Same-event centre/target control, uniform prefix/cell constants, and deterministic
  orbit transfer remain open. Independent recurrence and RH remain unproved; goal active.

- **F34 — Exact literal reflected-primal cofactor transfer.**
  `SmoothAFEReflectedCofactorTransfer.lean` absorbs common height by an exact logarithmic phase
  shift, factors the actual largest-prime channel through F33's Gaussian cofactor vector, and
  separates conductor scale, common row phase, cofactor length, and the fixed-node floor factor.
  It proves the floor ratio is in `(L/(L+1),1]` and its fixed complex powers approach one uniformly
  as `L` grows. The complete final leaf compilation passes without warnings; all six exported
  theorem axiom audits pass with standard axioms only. An earlier scratch assembly omission was
  caught and fixed before this complete audit; only the basic identity had been checked then.
- **F35 — Actual reciprocal prime counts and common conditioning seam.**
  `SteinhausCofactorPrimeBlocks.lean` proves exact cofactor membership `[M,2M)`, disjointness for
  separated blocks, and eventual cardinality at least `N/(4*M*log N)`. Blocks with `M<=K` lie
  above the common threshold `N/(2K)`, which eventually contains all constructed cofactors and
  satisfies `N<(N/(2K))^2`. Final leaf and all five exported axiom audits pass with standard
  axioms only. Combined audit: `/tmp/BagLiteralPrimeBlockAudit.lean`. Both modules are wired
  into the umbrella. Next: robust Cauchy direction and literal conditional Gram coercivity;
  same-event centre/target control and orbit transfer remain open.
- **F36 — Robust Cauchy-row coercivity.** `SteinhausCofactorModeCoercivity.lean` proves fixed
  positive constants `epsilon,c` such that every node coefficient vector has one prescribed
  Cauchy mode whose entire `epsilon` row-neighborhood pairs with it by at least `c*norm(u)`.
  Final leaf compilation and exported theorem axiom audit pass without warnings or nonstandard axioms.
  This is the direction estimate used for a whole reciprocal prime block, not an averaged Gram
  substitute. C17.9 now assembles F33 with F34's exact floor correction before applying it.

- **F37 — Uniform literal floor-corrected mode blocks.**
  `SmoothAFECorrectedCofactorModes.lean` controls F34's exact corrected rows for every actual
  channel with cofactor cutoff in a selected block, uniformly over all sufficiently small
  positive common smoothing scales. It retains any finite prescribed phase prefix, separated
  positive cutoffs, nonzero means, and arbitrary `M_i*norm(A_i)^2` budgets. Final leaf compilation
  passes without warnings; F36 and F37's exported theorem axiom audits pass with standard axioms
  only in `/tmp/BagCorrectedCofactorAudit.lean`.
- **F34–F37 final checks.** Four leaf compilations and thirteen exported theorem axiom audits
  pass. Umbrella wiring and index refresh complete; targeted whitespace check passes. Global
  lint exits 1 on fourteen unrelated unreachable modules, with no issue in these BAG leaves.
  Superseded owned scratch fragments and failed name probes were moved into a separate temporary
  archive; passing proof sources and final audit files remain available. No Lean process remains
  running after the completed audits. Independent recurrence and RH remain unproved; goal active.
- **Next exact step.** Apply F36 at half its row tolerance, obtain F37's corrected blocks with a
  sufficiently large budget, and use F35 to count every prime in the block selected for each node
  coefficient vector. F34 then transfers this energy to actual channels; the proved chi envelope
  supplies the conductor factor. Aim for an arbitrarily large constant over `log N` in the actual
  pointwise conditional Gram bound, uniformly over the prescribed common-height window, before
  constructing phase cells or attempting same-event centre/target and orbit estimates.

- **F38 — Pointwise normalized conditional energy.**
  `SmoothAFENormalizedChannelEnergy.lean` proves that, for any requested real constant `H`, one
  phase extending an arbitrary finite prescription and one conditioning threshold `N/(2K)`
  give normalized channel energy at least `H*N/log N * norm(u)^2` in every coefficient direction,
  eventually in `N` and uniformly for all sufficiently small positive smoothing scales. The
  proof uses F36's selected direction, F37's exact corrected rows, and F35's actual prime count.
  Final leaf compilation passes without warnings. A redundant positivity premise on `H` was
  removed because the proof establishes the statement for every real `H`. All three exported
  axiom audits pass with standard axioms only.

- **F39 — Actual reflected conditional energy.**
  `SmoothAFEReflectedConditionalEnergy.lean` proves a common conductor lower envelope, the exact
  norm transfer, and the actual reflected-primal conditional energy lower bound `H/log N` in
  every direction. One fixed prefix, inverse-rotated by common height, works throughout
  `[5*N/4,7*N/4]`, eventually in `N`, for every sufficiently small positive smoothing scale.
  Final leaf compilation is warning-free; all three exported theorem axiom audits report only
  standard axioms. Both new leaves are wired. `/tmp/BagPointwiseCovarianceAudit.lean` checks all
  six F38–F39 exports. This closes C18 at phase points; independent recurrence remains open.
- **Next C19.** Prove positive measure of fixed finite-character cells, then uniform stability
  of corrected rows on one such cell. The working card records the dependency-closed paper
  mechanism and keeps the separate height-rotation and centre/target obligations explicit.

- **F38–F39 integration checks.** Index refresh completed. Global formal lint reports eleven
  unrelated unreachable modules and no BAG issue; targeted whitespace check passed.
- **F40 — Positive finite-character cells.** `SteinhausFiniteCharacterCells.lean` proves
  character continuity, exact integer-period invariance, fractional-part reduction, positive
  measure of unit-cube open neighborhoods, and positive measure of every positive-radius finite
  character cell around an arbitrary real phase prescription. Final leaf compiles without
  warnings and is wired. Axiom audit is prepared; uniform corrected-row perturbation is the
  active mathematical assembly.

- **F41 — Uniform corrected-row cell stability.** `SmoothAFECofactorCellStability.lean`
  proves finite-character perturbation control and a prescribed block construction valid
  throughout one fixed cell. Final leaf passes without warnings and is wired. Normalized and
  actual energy theorems are now being strengthened to retain that cell, with their original
  pointwise statements preserved as corollaries. Coordinatewise measure transport is the next
  C19 assembly; its paper argument is recorded on the main card.

- **C19 energy strengthening.** The normalized and reflected-primal covariance proofs now
  quantify over every phase in one fixed finite-character cell. Their original pointwise
  statements are short corollaries, avoiding duplicate prime-count and conductor proofs.
  Both scratch checks pass; normalized final leaf passed without warnings, reflected final
  leaf is running. The exact phase-translation measure proof also passes its scratch check.
- **Centre-cost audit.** Recorded the circularity in dividing an unconditional background
  moment by a covariance-cell mass that itself depends on the desired covariance constant.
  No centre or local-target conclusion is being inferred from the covariance event.

- **F42 — Height-uniform phase-cell mass.** `SteinhausFiniteCharacterCellRotation.lean`
  proves a measure-preserving representative for every coordinatewise real phase translation,
  exact character transport, and equal cell mass at every translated centre. Final leaf passes
  without warnings and is wired. Both strengthened energy leaves also pass final compilation.
- **F43 — Actual positive covariance event.** Scratch assembly passes. The final leaf
  `SmoothAFEReflectedCovarianceEvent.lean` is wired and compiling; it includes measurability,
  a fixed strictly positive event mass independent of height, eventual placement of the entire
  cell prefix below the conditioning threshold, and the actual channel lower bound in every
  direction. Combined twenty-theorem axiom audit prepared at
  `/tmp/BagPhaseCellProducerAudit.lean`.
- **C20 frontier preparation.** Corpus search `/tmp/bag-prefix-centre-search.json` finds exact
  largest-prime decomposition, unconditional Parseval and frozen channel covariance, but no
  finite-prefix conditional background bound. Source inspection confirms that ordinary Parseval
  diagonalises all primes, whereas freezing a prefix retains off-diagonal pairs agreeing outside
  it. The next paper obligation is the exact grouped second-moment source formula, then an audit
  of its budget dependence; no background bound or recurrence claim has been assumed.

- **F38–F43 FINAL.** Six final leaf compilations pass without warnings. Initial C18 six-export
  audit and final C19 twenty-export audit use only `propext`, `Classical.choice`, `Quot.sound`.
  `/tmp/bag-fixed-covariance-cell-axioms.log` records the final audit and exact main statement.
  All leaves are wired, index refreshed, targeted whitespace check passed. Formal lint reports
  fourteen unrelated unreachable modules and no BAG issue. Current owned Lean jobs are complete.
  Superseded scratch proof/name-probe files were archived; passing current proof and audit files
  remain available. C18–C19 are closed. Independent recurrence and RH remain open; goal active.
  Next: C20 finite-prefix conditional background source formula and same-event target-cost audit.
