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
- **C20.1 active formalization.** `/tmp/BagFrozenPrefixKernel.lean` contains the explicit
  finite-prefix overwrite, continuous/integrable character kernel, exact product integral,
  exterior-factorisation equality criterion, retained-pair quadratic identity and positive
  grouped second-moment formula. The first kernel and quadratic identities pass; the current
  check fixes only finite-sum grouping elaboration and one redundant tactic. No repository leaf
  has been created for this step yet. This exact formula is not a background bound.

- **F44 FINAL — Frozen-prefix second moment.** New leaf
  `SteinhausFrozenPrefixSecondMoment.lean` compiles without warnings, wired and indexed. Seven
  public theorem axiom audits pass with standard axioms only, recorded in
  `/tmp/bag-frozen-prefix-second-moment-axioms.log`. Exact norm-squared moment is a sum of squares
  grouped by exterior factorisation. Formal lint currently has seventeen unrelated unreachable
  modules and no BAG issue. No owned Lean/search process remains active after these checks.
- **C20.2 next analytic target.** Deep search completed (`partial=false`, full inventory,
  compiler coverage mostly pending/stale; semantic coverage unmeasured) without an applicable
  completely multiplicative low-moment theorem. Primary paper arXiv:1703.06654, Theorem 1 and
  Corollary 1, confirms the unweighted square-root-normalized first-mean/probability decay.
  `SecondMoment.lean` mentions that result only in motivation. Weighted Abel transfer and
  fixed-cofactor large-prime L2 decay would turn that decay into bounded background on each
  fixed C19 event with mass at least half its mass, avoiding the budget/mass circularity.
  These are open proof obligations; no external analytic premise was added. Only independent
  recurrence producer remains in scope. RH goal active.

- **C20.3 / F45 scratch complete.** Coefficients in every fixed cofactor range have a
  square-root-conductor envelope. Individual channels and every finite-node direction inherit
  it uniformly over phases and all positive smoothing scales. PNT gives a uniform `C/log N`
  conditional energy ceiling. The actual full carrier minus its smooth background has an exact
  coefficient-mass second moment and the same ceiling. Eight scratch exports pass without
  warnings in `/tmp/BagChannelUpper.lean`; final leaf integration is next. This is an unconditional
  small-channel/remainder estimate, not the missing low-moment estimate for the full carrier.
- **F45 FINAL.** New `SmoothAFEReflectedChannelUpper.lean` and shared cutoff-bound export
  compile warning-free with `lake --old env lean`. All nine axiom checks use only standard
  axioms (`/tmp/bag-channel-upper-axioms.log`). New leaf wired; whitespace clean. Global lint
  reports 21 unrelated unreachable modules, no BAG issue. Superseded owned name probes and
  proof fragments archived; passing scratch and final audit retained. The only remaining
  owned process is the managed deep search for critical Euler-product/barrier source material.
  C20.3 closes the actual remainder L2 estimate and finite-node maximal-channel/energy upper
  bounds. C20.2 full-carrier low-moment decay, same-event local target law, and deterministic
  orbit transfer remain open. No added premise, numerical computation, full build, commit, or push.
- **C20.2 source audit complete.** Deep search completed without execution errors, full inventory,
  but mostly pending/stale compiler metadata and unmeasured semantic coverage. No applicable
  critical Euler-product barrier theorem among candidates/source arguments. Rejected generated
  ingredient set: a scalar half-Lipschitz sign fact plus circle log-convexity does not prove
  random-walk survival. Targeted lexical and exhaustive phrase searches also yield no applicable
  source. No owned Lean or search process remains active. F45 final index visibility checked next.
- **F45 index verified.** Exact-name lexical search returns the new actual remainder theorem
  at its final leaf, line 274. Final checks complete; memory updated with source-search outcome
  and next genuine analytic dependency. Goal remains active and exclusively BAG producer.

- **C20.4 / F46 scratch verified.** `SteinhausEulerQuadraticApprox.lean` proves the actual
  finite Euler product equals its logarithmic exponential, and a cutoff/phase/height-uniform
  cubic remainder bounds its quadratic logarithmic approximation on `Re(s)>=1/2`. Real log
  and two-sided squared-norm comparisons follow. Final leaf compilation running; no decay
  or recurrence conclusion claimed.
- **C20.5 new qualitative attack.** Current papers inspected: Gorodetsky–Wong arXiv2405.19151
  (Gaussian-chaos coupling) and Hamdan arXiv2604.05563 section2 (level sets, Gaussian local
  comparison, barriers). New proposed route avoids sharp-rate inputs: consistent Poisson-kernel
  tilts, growing centered variance plus fourth moments and zero-one give qualitative tilted
  barrier death; a planar mean-value bound plus uniform Euler second moments controls global
  barrier failure. Combining these should give normalized critical mass vanishing in probability.
  This is OPEN, recorded in full on the card. `PoissonKernelBound.circleAverage_poissonKernel_log_norm`
  is a directly relevant existing source for the exact tilted logarithmic mean. Existing
  `HolomorphicBallMeanSq.normSq_value_mul_area_le_integral_ball` assumes an entire function,
  so applying it directly to the meromorphic finite Euler product is invalid; derive a local
  analytic-disc version or use an entire approximation with audited strip control.
- **F46 FINAL.** Six public theorem axiom audits pass with standard axioms only, logged in
  `/tmp/bag-quadratic-euler-axioms.log`. Final leaf warning-free, wired and indexed at final
  theorem line152; whitespace clean. Global lint has15 unrelated unreachable modules and no
  BAG issue. No owned Lean/search process remains. C20.4 exact source comparison closed;
  C20.5 qualitative Poisson-tilted barrier argument remains OPEN, not an assumed input.
- **C20.5a exact tilt, paper proof and formal target.** On the unit circle, the normalized
  squared Euler factor `(1-r^2)/|1-r*z|^2` equals `poissonKernel 0 r z`: both denominators
  have square `1+r^2-2*r*Re(z)`. For `0<=r<1`, the denominator never vanishes and the
  weight is positive. Poisson's formula for the constant function gives mass one. Applied
  to the zero-free analytic function `z -> 1-r*z`, it gives weighted log mean
  `log(1-r^2)`. Changing angle `theta=2*pi*x` transfers both identities to the actual
  coordinate interval `[0,1]`; a `withDensity` measure therefore realizes the tilt as a
  probability law, with centered log increment `-log|1-r*e(x)|+log(1-r^2)`. These are
  dependency-closed paper identities. Formalization starts in `/tmp/BagPoissonTilt.lean`;
  no barrier, moment-decay, or recurrence conclusion is assumed.
- **C20.5a / F47 FINAL.** `SteinhausEulerPoissonTilt.lean` constructs the concrete interval
  density and tilted measure, proves strict positivity and continuity, unit total mass,
  arbitrary-observable change of measure, the exact negative-log mean, and zero centered
  mean. Nine public theorem axiom audits use only `propext`, `Classical.choice`, `Quot.sound`
  (`/tmp/bag-poisson-tilt-axioms.log`). Final leaf passes warning-free and is wired. Global
  lint reports nineteen unrelated unreachable modules, no BAG error. The next moment leaf
  proves a direct far-arc lower bound and pointwise `6r` upper bound; scratch verification
  is in progress. The independent recurrence producer remains open.
- **C20.5a / F48 FINAL.** `SteinhausEulerPoissonTiltMoments.lean` proves five exports:
  tilt density `>=1/7`, centered log modulus `<=6r` in absolute value, signed far-arc
  bound `<=-r/4`, actual tilted second moment `>=r^2/336`, and all absolute moment
  ceilings `(6r)^k`, for `0<=r<=3/4`. Final leaf passes warning-free; five axiom audits
  use standard axioms only (`/tmp/bag-poisson-tilt-moments-axioms.log`). Wired, whitespace
  clean, final lint nineteen unrelated unreachable modules and no BAG error. F47/F48 exact
  index visibility checked. No owned build/search process remains active.
- **C20.5b next-source audit.** Deep search `/tmp/bag-one-sided-fourth-moment-source.json`
  has full 63,350-file inventory but `partial=true`: the filter/judge returned incomplete or
  malformed JSON. Its twenty candidates and twenty source arguments were inspected; none
  supplies the needed signed positive-tail law. Compiler metadata mostly pending/stale,
  semantic coverage unmeasured, refresh deferred to background indexer. Direct corpus
  search found `FourthMomentEscape.measure_sq_gt_half_ge` and `PaleyZygmund.paley_zygmund`
  (two-sided or nonnegative statements), plus `IntegralCauchySchwarz.sq_integral_mul_le`.
  The card now gives an elementary signed-tail derivation without symmetry: truncation
  yields a positive first-moment floor, mean zero halves the absolute mean, and tail
  Cauchy–Schwarz yields probability `>=1/(128*C)` at a fixed multiple of `sqrt(V)`.
  Actual product-law prime-sum moments must be proved before this is used; no receiver
  assuming the missing decay is being substituted. The independent recurrence goal stays open.
- **C20.5c product-sum source, paper proof before implementation.** Use radius
  `randomEulerRadius (1/2) n`, zero for nonprimes, and the now-proved coordinate tilt at
  that radius. Their countable product is a probability measure; its centered log terms
  are independent and bounded by `6r_n`. For every finite set `P`, the actual sum has mean
  zero and second moment `sum_P E Z_n^2`, between `(sum_P r_n^2)/336` and
  `36 sum_P r_n^2`. For `n` outside `P`, independence and centering give the exact
  fourth recurrence `E(S+Z_n)^4=ES^4+6 ES^2 EZ_n^2+EZ_n^4`. The proved coordinate
  bounds inductively imply `ES^4<=3*(36 sum_P r_n^2)^2=3888*(sum_P r_n^2)^2`.
  Since `r_n^2=1/n` at primes and zero otherwise, these are literal arithmetic moments.
  Implementation starts in `/tmp/BagTiltPrimeSum.lean`; no growth or decay estimate is
  assumed. Existing independent-coordinate second moments and mathlib finite-sum
  independence match the product-law setting; uniform Steinhaus fourth-moment formulas
  do not directly apply to this asymmetric tilt.
- **C20.5c source search complete.** `/tmp/bag-independent-fourth-source.json` has
  `partial=false`, no execution errors, complete inventory, mostly pending/stale compiler
  evidence, and unmeasured semantic coverage. All twenty candidates and twenty source
  arguments inspected. Its proposed pairing of a finite sum of integer fourth powers
  with a Gaussian saddle moment is inapplicable to the actual independent tilted sum.
  Mathlib's `iIndepFun.indepFun_finsetSum_of_notMem` and independent-product integral
  formula give the needed exact recurrence directly. Existing prime reciprocal
  nonsummability supplies variance divergence. The new source leaf is in final checking;
  `/tmp/BagTiltPositiveTail.lean` then instantiates the signed-tail argument on these
  actual prime sums, with no missing recurrence or decay premise.
- **C20.5c / F49 FINAL.** `SteinhausEulerTiltPrimeSum.lean` (331 lines) constructs the
  actual countable product law and centered prime variables, proves measurability,
  integrability of all finite powers, independence, exact centering and variance additivity,
  explicit two-sided variance bounds, fourth moment `<=3888*(sum r_n^2)^2`, fourth-to-variance
  ratio `<=3888*336^2`, and variance divergence. Eighteen public theorem axiom checks
  use standard axioms only (`/tmp/bag-tilt-prime-sum-axioms.log`). Final leaf warning-free,
  wired; lint fifteen unrelated reachability errors, no BAG error. Signed positive-tail
  proof remains in scratch; barrier event and recurrence are not claimed.
- **C20.5b / F50 scratch passed.** `/tmp/BagTiltPositiveTail.lean` proves positive
  variance for `N>=3`, an explicit one-sided probability lower bound, and constants
  `c,delta>0` such that the actual centered sum exceeds `c*sqrt(V_N)` with probability
  at least `delta`, uniformly in `N>=3`. The proof derives a positive first-moment
  floor by truncation and uses the existing Paley–Zygmund theorem on `max(S_N,0)`.
  No symmetry is assumed. Final `SteinhausEulerTiltPositiveTail.lean` build running.
- **F50 FINAL and next barrier target.** Final leaf passes warning-free; all three public
  axiom audits use only `propext`, `Classical.choice`, `Quot.sound`
  (`/tmp/bag-tilt-positive-tail-axioms.log`). Wired and indexed at line145; F49 variance
  divergence indexed at line313. Whitespace clean; final lint fifteen unrelated unreachable
  modules and no BAG error. No owned Lean/search process remains active. Superseded name
  probe and growth fragment archived under
  `/var/folders/h4/zrd73pg91clb__kg1kzrlcph0000gn/T/bag-superseded-c20-tilted-sums-c_s2j7k_`.
  Passing scratch and audit files retained. Card C20.5d records the next literal event:
  for cofinal cutoffs `u_j`, `S_(u_j)<=A+2 log(1+V_(u_j))` at all scales. Finite phase
  changes shift every sum by at most `9*card(changed coordinates)`. The positive-tail
  theorem, variance divergence, and `log=o(sqrt)` bound every fixed-A event below mass1;
  continuity from below and product zero-one should make their union null. Formalize that
  statement and finite-horizon survival decay next, retaining selected cutoffs. Do not
  replace it with mere unboundedness of all integer-cutoff sums.
- **C20.5d implementation start.** Revalidated F49/F50 source and the exact product
  zero-one signature. Formal target: the literal logarithmic-variance barrier along every
  cofinal cutoff sequence has zero probability, and each fixed real-A finite-horizon
  survival probability tends to zero. The only cutoff hypothesis is cofinality; all
  distributional facts come from the proved actual tilted product model. Work starts in
  `/tmp/BagTiltBarrier.lean`; include measurability, finite-coordinate invariance, logarithm
  versus square-root growth, and continuity of probability, not an assumed barrier receiver.

- C20.5d / F51 FINAL: `/tmp/BagTiltBarrier.lean` passed, then final 234-line
  `SteinhausEulerTiltBarrier.lean` passed `lake --old env lean` warning-free. Nine
  axiom audits standard-only. Wired; exact-name index total 1, survival at line 214.
  Lint exit 1: 17 unrelated unreachable modules, no BAG error. Logs:
  `/tmp/bag-tilt-barrier-{final,axioms,lint}.log`, index JSON alongside.
- Both deep corpus searches finished non-partial; inspected all 20 candidates and
  20 source arguments each, plus ingredient sets. Snapshot compiler metadata is
  mostly pending/stale, refresh incomplete because background indexer running;
  semantic coverage unmeasured. Applicable statements verified from source/Lean,
  not inferred from retrieval scores. Barrier search found no stronger replacement;
  density search found generic finite `pi_withDensity` in `GaussianShiftInformation`.
- C20.5e next: paper proof above is dependency-closed. Formalize actual finite density,
  head change of measure, literal finite-barrier specialization, and its vanishing
  weighted mass. Spatial maximum, critical-mass, arithmetic low moments, same-event
  centre/local-target control, and deterministic recurrence remain open.

- C20.5e / F52 FINAL: 171-line `SteinhausEulerTiltFiniteDensity.lean` passes final
  `lake --old env lean` warning-free. All six axiom audits standard-only. Wired;
  exact-name index total 1, main limit line 157. Lint exit 1: 20 unrelated unreachable
  modules, no BAG error. Logs `/tmp/bag-tilt-finite-density-{final,axioms,lint}.log`.
- F52 elaboration: explicit `n`, dependent type `E`, base measures, and coordinate
  density arguments avoid a `pi_withDensity` elaboration heartbeat timeout. No
  heartbeat override. For `lintegral_map (hd.mul hf)`, normalize `Pi.mul_apply` and
  unfold the concrete/local densities before comparing to an explicit product lambda.
- C20.5f paper improvement: choose cutoffs `u_j>=j+3`, `V_(u_j)>=j` using divergence.
  Spatial target only needs `E sup |F_N|^2<=C*log(N)*M_N`, while `M_N>=log(N)` is
  elementary. This avoids quantitative Mertens clock synchronization. F52 permits
  every final cutoff beyond the tested head, so full-cutoff mass decay needs no
  separate martingale interpolation. All spatial steps remain explicitly open.
- Next work: literal finite Euler product second moment / density and centered-log
  identifications; uniform ratio under real-part shifts `O(1/log N)`; local planar
  submean; global good barrier, phase rotations/Fubini, critical-mass decay. Then
  arithmetic first-mean, weighted/frozen-prefix same-event centre, local-target mass,
  and deterministic recurrence transfer. Do not mark the producer closed.

- C20.5f source audit passed: `mertensFirst_upper`, `harmonic_le_prod_primesBelow`,
  and `log_add_one_le_harmonic` verified in `/tmp/BagEulerSpatialSourceAudit.lean`;
  all three have only standard axioms. Log `/tmp/bag-euler-spatial-source-axioms.log`.
  Superseded name probes archived at `/var/folders/h4/zrd73pg91clb__kg1kzrlcph0000gn/T/bag-superseded-c20-barrier-probes-x8nllx_8`. No owned Lean/search
  process remains live; passing scratch proofs and final audit logs retained.

- New goal turn: prior turn classified VERIFIED PROGRESS. Re-read goal attachment,
  listed/read current BAG memory, checked architecture/testing docs (absent),
  revalidated frontier/STATUS and actual F52 source. Only BAG work continues.
- C20.6 paper proof above: complex Poisson normalization avoids a separate rotation
  proof for exact second moments. Formalize literal F46 product, not a surrogate
  polynomial or a new assumed moment bound. Scratch `/tmp/BagEulerSecondMoment.lean`.

- C20.6 / F53: scratch all six public theorems passed. Final 160-line
  `SteinhausEulerSecondMoment.lean` compiles warning-free and is wired. Axiom audit
  running in `/tmp/BagEulerSecondMomentAudit.lean`, log
  `/tmp/bag-euler-second-moment-axioms.log`; no full/umbrella build.
- C20.7 paper proof entered: r_N=1/(16*(1+logN)), exact finite partition ratio
  bounded uniformly for sigma>=1/2-r_N. Use exp(t)-1<=t*exp(t), denominator>=1/4,
  and existing prime-log upper bound. Deep ratio search found no applicable
  ready-made replacement; all20 candidates+20 source arguments and ingredient set
  inspected. Local-planar deep search partial at text retrieval; lexical follow-up
  recovers only the known entire-function mean-square leaves. Keep local extension
  obligation explicit; do not misuse the entire-function theorem.

- F53 complete audit: all six public theorem axioms standard-only, exact-name index
  total 1 at line 121. Global lint exit 1: 13 unrelated unreachable modules, no BAG error.
  C20.7 scratch first pass had only one redundant `rfl` after a closing rewrite;
  removed it and exported the radius upper bound required by disc geometry.

- C20.7 / F54 FINAL: `SteinhausEulerSpatialPartition.lean` 206 lines, final warning-free,
  eight public theorem axiom audits standard-only. Wired, exact-name index visible.
  Logs `/tmp/bag-euler-spatial-partition-{final,axioms,lint}.log` (lint running at
  this entry). Passing scratch `/tmp/BagEulerSpatialPartition.lean` retained.
- C20.8 scratch `/tmp/BagEulerLocalMeanSq.lean`: local Gutzmer + Tietze extension +
  polar mean square; proves actual finite Euler products holomorphic on Re>0 and
  specializes the local disc inequality to F54's radius. Single owned Lean compile
  running, session 49293. Name probes all passed in F54 audit file; no new axioms or
  heartbeat overrides.

- F54 lint finished exit 1: 14 unrelated unreachable modules, no BAG error.
- F55 initial scratch compile had two elaboration errors: missing `id_eq` in the
  translated ball map and explicit constant arguments for `differentiableAt_const`.
  Both corrected; replacement compile is session 89145. No duplicate Lean job.
- C20.9 paper proof recorded: explicit rectangle envelope avoids any supremum
  measurability assumption and yields expectation at most `(128*C/pi)*M_N^2`.
  Existing rectangle/Tonelli research results already inspected; actual API probes
  will run after F55 terminates.

- C20.8 / F55 FINAL: 224-line `SteinhausEulerLocalMeanSq.lean`, warning-free final
  leaf, all four axioms standard-only, wired, exact-name index total 1 at line 212.
  Logs `/tmp/bag-euler-local-mean-sq-{final,axioms,lint}.log`; lint exit 1 has 18
  unrelated unreachable modules. First no-refresh index lookup was stale; normal
  documented search sees the new theorem. Auxiliary generic API probes need explicit
  universe-zero parameters in `have := @...`; corrected audit is exit 0.
- C20.9 / F56 scratch `/tmp/BagEulerSpatialEnvelope.lean`: eight public theorems,
  actual jointly measurable Euler product, rectangle geometry/area, exact nonnegative
  second moment, explicit envelope and domination, Tonelli expectation bound.
  Single owned Lean process session 48508. No hypotheses replaced by assumed
  analytic estimates. Still no independent recurrence producer.

- C20.10 paper improvement recorded: select `V_(u_j)>=2^j` and use the single
  geometric aggregate `sum_j 2^(-j-1) Z_(u_j)/M_(u_j)^2`. Its expectation is bounded
  by the same spatial constant; Markov gives a simultaneous barrier at every scale
  and spatial point. This removes p-series and countable-union bookkeeping without
  changing F51/F52 hypotheses or adding a quantitative clock assumption.
- Deep spatial-barrier search nonpartial: all20 candidates, all20 source arguments,
  and proposed ingredient set inspected; none supplies the required literal result.
  Snapshot-generation warning, semantic coverage unmeasured, refresh incomplete
  because background indexer runs. Lexical field-identity query returns129 hits,
  first20 inspected; existing log-product identity is a relevant source, while exact
  density and centered-sum identifications remain next obligations.

- C20.9 / F56 FINAL: 204-line `SteinhausEulerSpatialEnvelope.lean`, warning-free
  final leaf, all eight public axioms standard-only, wired and index-visible.
  Logs `/tmp/bag-euler-spatial-envelope-{final,axioms,lint}.log`; lint exit 1 lists
  16 unrelated unreachable modules. Key Lean detail: give explicit `p := ...` to
  `ENNReal.ofReal_mul` when both sides contain several products; finish associations
  with `simp only [mul_assoc]`. `mul_le_mul_left'` is deprecated; current equivalent
  is `mul_le_mul_right`. Avoid unconstrained `gcongr` across restricted integrals.
- C20.10 / F57 scratch `/tmp/BagEulerGlobalEnvelope.lean`: geometric aggregate,
  measurability, finite expectation, simultaneous selected-cutoff/spatial domination,
  and uniform Markov exceptional-event bound. Current single Lean job session10165.
  Variance-selected cutoffs and literal centered-log/phase identities still follow.

- C20.10 / F57 FINAL: 134-line `SteinhausEulerGlobalEnvelope.lean`, warning-free
  final leaf, all five public axioms standard-only, wired, exact-name index total1
  at Markov theorem line122. Logs `/tmp/bag-euler-global-envelope-{final,axioms,lint}.log`;
  latest lint exit1:16 unrelated unreachable modules, no BAG error. One initial
  geometric-sum reciprocal cancellation required explicit `ENNReal.inv_mul_cancel`.
- C20.11 paper proof recorded. Reuse actual F46 log-product/exponential identities
  and F53 prime-character identity for exact `D_N=|F_N(.5)|²/M_N` and
  `S_N=log|F_N(.5)|-logM_N`; nonprime coordinates contribute weight1/log0.
  Use existing measure-preserving coordinate rotation with shifts
  `-t*log(p)/(2*pi)`. Transport the whole finite-barrier event at each fixedt.
  Define the spatial barrier directly using the jointly measurable F56 field;
  this avoids an unnecessary joint rotation-map measurability theorem.
- Turn checkpoint: F53–F57 all final, 31 public axiom audits standard-only. All
  owned Lean and research commands exited; passing scratch files/audit logs retained.
  No independent recurrence or RH claim. Next work is C20.11 exact identities and
  phase covariance, actual exponential-variance cutoff selection, spatial restricted
  mass/F52 assembly, and full-cutoff convergence in probability. Later arithmetic
  first-mean, weighted/frozen-prefix same-event centre, local-target mass and
  deterministic vertical recurrence remain explicit.

- New goal turn: previous classified VERIFIED PROGRESS. Re-read goal attachment;
  listed/read latest BAG memory, architecture/testing docs absent; revalidated
  frontier/STATUS, F52 density, F53 partition and C20.11 paper proof from current
  source. Sole scope remains independent recurrence producer. No plan tool available;
  card/log carry work tracking. Start exact literal field/density identifications.

- C20.11a / F58 FINAL: 122-line `SteinhausEulerExactIdentities.lean`. All3 public
  axioms standard-only, final leaf warning-free, wired and index-visible. Latest
  lint exit1:10 unrelated unreachable modules. Logs
  `/tmp/bag-euler-exact-identities-{final,axioms,lint}.log`.
- Both identity and vertical-rotation deep searches completed nonpartial. Inspected
  all20 candidates+20 source arguments and each ingredient set; actual F46 log/exp,
  F53 partition, and existing character coordinate-rotation/add-phase results used.
  Snapshot warning, semantic coverage unmeasured, background refresh incomplete.
- Name probes `/tmp/BagEulerExactIdentitiesNames.lean` and F58 audit pass. Use explicit
  nat function and N in `Fin.prod_univ_eq_prod_range`; real projection of a complex
  sum is `Complex.re_sum`. Normalize all divisions with `simp only` when `1/2`
  occurs inside a larger expression, to avoid rewriting only the internal fraction.
- C20.11b / F59 scratch `/tmp/BagEulerVerticalBarrier.lean`: actual vertical rotation,
  product covariance for arbitrary complex s, exact density and centered-log
  transports, whole finite-barrier preimage, and literal restricted-energy identity
  for every final cutoff beyond tested heads. Single Lean job session57006. No assumed recurrence.

- C20.11b / F59 final leaf: 132 lines, warning-free and wired. Nine axiom audits and
  F60 name probes running in `/tmp/BagEulerVerticalBarrierAudit.lean`, session71799; latest lint exit1:11 unrelated unreachable modules.
- Variance-selected-barrier deep search partial at semantic retrieval; all20 candidates,
  all20 source arguments and proposed ingredient inspected. Reuse actual F49 variance
  divergence and F51/F52 survival/density results from source. No need to repeat search
  merely for full coverage; available results and direct source suffice.
- C20.12 paper proof recorded. F60 scratch `/tmp/BagEulerSelectedBarrier.lean` written,
  not yet compiled. Least actual variance-selected cutoffs, cofinality, all-point
  logarithmic barrier on the single good event, and exceptional probability bound.

- C20.11b / F59 FINAL: warning-free 132-line leaf, all9 public axioms standard-only,
  wired and exact-name index-visible. Logs `/tmp/bag-euler-vertical-barrier-{final,axioms,lint}.log`.
  F60 name probes pass in F59 audit. F60 scratch compile started; track handle from
  tool output, log `/tmp/bag-euler-selected-barrier-scratch.log`.

- C20.12 / F60 FINAL: 118-line leaf passes warning-free; all5 public axioms standard-only;
  wired and index-visible. Latest lint exit1:12 unrelated unreachable modules.
  Logs `/tmp/bag-euler-selected-barrier-{final,axioms,lint}.log`. Scratch passed first
  full compile. Auxiliary F61 probes corrected `measurableSet_iInter` to current
  `MeasurableSet.iInter`, and outer-measure generic universe counts; clean audit passes.
- C20.13 paper proof recorded. Scratch `/tmp/BagEulerCriticalMass.lean` now contains
  literal mass/restricted-mass definitions, joint measurability, exact expectation,
  mean one, good-event equality, all-final-cutoff probability bound, and probability
  convergence to zero. Its first compile is running; do not claim the limit yet.
- Spatial-mass deep search nonpartial; all20 candidates+20 source arguments+ingredient
  set inspected. No ready-made literal replacement. Semantic coverage unmeasured,
  refresh incomplete/background indexer. Relevant foundation is own F56 joint
  measurability plus verified Tonelli/indicator/Markov APIs.

- F61 first compile terminated with four elaboration errors. Fixed unification cost
  by giving `Nat.primesBelow N` explicitly before composing joint measurability;
  proved equality of the two indicator lambdas by function extensionality and
  membership cases; exposed set membership before rewriting the good-event equality;
  used `add_le_add le_rfl` for the final scalar comparison. No heartbeat change.
  Replacement compile session33091, same scratch/log path.
- Original C20.2/C20.5 source plan re-read: after critical-mass probability decay,
  unit mean must yield vanishing subunit moments, then the arithmetic Euler-product
  reduction still needs its actual sieve/Parseval dependencies. Weighted Abel and
  fixed-cofactor subtraction are downstream. No deterministic recurrence claim.


- F61 measurability timeout resolved without increasing heartbeats: construct the
  measurable composition, then `simpa only [Function.comp_def] using hcomp`.
  Direct definitional comparison had unfolded prime factorization inside X.
  Isolated probe and complete scratch both pass. 181-line final leaf now passes
  warning-free and is wired; all ten public axiom audits, lint and exact-name index
  checks started. C20.14 paper proof for every fractional moment recorded.
- All20 candidates and all20 source arguments from the critical-mass-square-root
  search inspected. No ready-made literal theorem; direct current mathlib source
  supplies `ENNReal.lintegral_mul_norm_pow_le`. Search nonpartial, semantic coverage
  unmeasured, background refresh incomplete. Probing the exact Holder/power APIs.

- F61 FINAL: warning-free, all10 axioms standard-only, wired/index-visible at line168.
  Lint exit1:14 unrelated unreachable modules. Final/audit/index logs retained under
  `/tmp/bag-euler-critical-mass-*`. F62 scratch `/tmp/BagEulerCriticalMoments.lean`
  written after successful exact-name probes; three public results: tail-controlled
  fractional moment, all-subunit-moment convergence, square-root specialization.
  Compile session42012. Arithmetic reduction deep search and primary Harper paper
  source inspection begun; no arithmetic theorem assumed.

- F62 FINAL: three public theorems, first scratch passed; final warning-free, axioms
  standard-only, wired/index-visible, lint15 unrelated unreachable. Logs retained
  `/tmp/bag-euler-critical-moments-*`. All owned Lean jobs exited.
- C20.15 fixed-prefix arithmetic proof recorded. Arithmetic-reduction search nonpartial;
  all20 candidates+20 source arguments+both ingredient steps inspected. Proposed
  global-summability Euler theorem is too strong at 1/2; direct Basic.lean supplies
  `summable_and_hasSum_smoothNumbers_prod_primesBelow_geometric`, requiring only
  local prime norm <1. Semantic coverage unmeasured, background refresh incomplete.
  Next formalize literal smooth Dirichlet expansion, then fixed-prefix arithmetic
  and whole-line Cauchy mass. This avoids quantitative moving sieve machinery.

- F63 FINAL: 76 lines, five public results, scratch and final warning-free, standard
  axioms, wired/index-visible; lint13 unrelated unreachable modules. Name probes
  and logs under `/tmp/bag-euler-smooth-series-*`. F64 translated mass scratch
  `/tmp/BagEulerTranslatedMass.lean` compile session25360. Rough-density deep search
  session45923. All earlier owned jobs terminal. Existing source provides exact
  `HTGeometry`-area Cauchy Fourier integral in `CauchyKernelFourier.lean`, line202;
  inspect namespace/signature and audit before using, no need to recreate contour proof.

- F64 FINAL: 73 lines, all7 axioms standard-only, final warning-free, wired/index-visible,
  lint12 unrelated unreachable modules. Initial audit launch from root cwd failed
  with unknown module prefix; rerun from formal passed, no source change needed.
- Rough-density search nonpartial; all20 candidates+20 source arguments+two ingredient
  steps inspected. A useful hit `roughDensity` led to the exact original `roughCount`,
  `roughDiscrepancy_eq`, and `abs_roughDiscrepancy_le` in ThetaCutoffCommutatorShell.
  C20.18 records direct normalized-coefficient limit. No new counting model needed.
  Search snapshot older generation, semantic coverage unmeasured, refresh background.

- F65 scratch now passes; final leaf `SteinhausEulerRoughCount.lean` passes warning-free
  and wired. First scratch required `simp only [inv_inv]` under the finite product,
  not root-only `rw`. Six public axioms and F66 API probes in progress, plus lint/index.
- F66 scratch `/tmp/BagEulerCompactMass.lean` written from C20.19, not yet compiled.
  C20.20 paper proof now records literal half-scale Cauchy whole-line mass and all
  subunit-moment decay; its density is <=1, so compact domination has no extra
  constant. Next compile F66, then formalize C20.20. No recurrence conclusion.

- F65 FINAL: 75 lines, all6 axioms standard-only; final/index pass; lint14 unrelated
  unreachable modules. F66 API probes all pass in F65 audit. F66 scratch compile
  session50706, only owned live Lean. F67 scratch `/tmp/BagEulerCauchyMass.lean`
  now written from C20.20; not yet compiled and not a repository leaf. Names for
  the Cauchy measure/density and finite-measure continuity still need a Lean probe.

- F66 second scratch passes. First two elaboration errors fixed by naming both the
  integer-indexed function and finite set in `Finset.sum_coe_sort`, and the entire
  integer-indexed integrand in `lintegral_finsetSum`; this prevents inference from
  confusing an integer index with its real cast. Final leaf now compiling, wired.
- Prefix-resampling search launched (session95567). Current mathlib source suggests
  exact law proof using an outer Bool-indexed independent pair of Steinhaus samples,
  `iIndepFun_uncurry_infinitePi'`, injective coordinate selector
  p -> (if p belongs to S then false else true,p), and
  `infinitePi_map_eval_prod` to identify the pair law with mu.prod mu. This avoids
  any unproved conditional-expectation premise. No resampling code written yet.

- F66 FINAL: 86 lines, warning-free, all4 axioms standard-only, wired; lint16
  unrelated unreachable modules. Corrected next-leaf API probe passes; index check
  running. F67 first complete scratch now compiling. Compact-mass proof unchanged.
- Prefix-resampling search partial; all20 candidates, all20 source arguments and
  both ingredient steps inspected. Semantic coverage unmeasured, older snapshot.
  Useful exact hit: `HTGeometry.map_sumPiEquivProdPi_infinitePi` in
  `InfinitePiSumSplit.lean:18`; actual source inspected. Together with current
  mathlib `Measure.map_infinitePi_infinitePi_of_inj`, this replaces the earlier
  Bool/double-independence plan by a direct sum-index selector. C20.21 proof recorded.

- F66 exact index check passes, limit theorem line72; frontier updated. F67 scratch
  required explicit probability measure in Holder and an explicitly typed tail-mean
  rewrite, avoiding simp normalization of the half-scale parameter. Latest scratch
  session25595 includes successful prefix-resampling API probes; awaiting terminal.
- Smooth/rough search nonpartial; all20 candidates+20 source arguments and both
  ingredient steps inspected. Useful sources are `Sieve/SmoothRough.lean` and
  `WeilLogSummableRigidity.lean`; actual split-source definitions/proofs read. Use
  the lighter sieve split with cutoff y-1, and prove its rough factorization equals
  the literal exterior factorization from F41. The suggested `Nat.roughNumbersUpTo`
  is only the nonsmooth complement and is inapplicable. Semantic coverage unmeasured,
  older source snapshot; proof applicability will be checked in Lean.

- F67 scratch and prefix-resampling name probes pass; 139-line final leaf now
  warning-free, wired/index-visible (moment limit line118). Public axiom audit and
  next arithmetic-name probes running in session70725. Lint exit1:10 unrelated
  unreachable modules. Logs under `/tmp/bag-euler-cauchy-mass-*`.
- F68 scratch `/tmp/BagPrefixResampling.lean` and F69 scratch
  `/tmp/BagSmoothRoughSplit.lean` are drafted, not compiled or repository leaves.
  F69 reuses sieve split and adds exact factorization/membership/uniqueness bridges;
  no duplicate smooth/rough definitions. Cauchy pair-kernel source search running.

- Cauchy pair-kernel search nonpartial: all20 candidates+20 source arguments+both
  proposed ingredient steps inspected. Most hits concern unrelated decay. Existing
  exact source `HTGeometry.integral_inv_sq_add_sq_mul_cexp_neg` is the applicable
  identity; its signature and normalization were inspected directly, with the
  probability-density conversion API. C20.23 records the complete normalized
  pair-kernel proof and the absolute smooth-series justification for interchange.

- F67 FINAL: five public axiom audits standard-only; all F69 arithmetic API probes
  also pass. Final139 lines warning-free, wired/index-visible, lint10 unrelated.
  F68 prefix-resampling first scratch compile started, sole owned live Lean.

- F68 first scratch errors were explicit function-composition reductions and
  measurable-equivalence evaluation. Product-law map proof itself elaborated.
  Corrected with `Function.comp_def`, literal joint test measurability, and `rfl`
  for sum-index evaluation; second scratch47506 running. No heartbeat change.
- F70 two-theorem scratch `/tmp/BagEulerCauchyKernel.lean` drafted for the literal
  half-scale Cauchy characteristic function and reciprocal-maximum power-pair
  kernel. Names file `/tmp/BagEulerCauchyKernelNames.lean` not compiled yet.

- F68 corrected scratch and final80-line leaf pass warning-free; wired/index-visible
  first-moment bound line62; lint10 unrelated unreachable. Axiom audit plus Cauchy
  kernel API probes running session49629. F69 scratch next, names already verified.
- C20.24 records exact finite multiplication bijection and character split for the
  summatory polynomial, followed by rough orthogonality and literal rough counting.
  Prior-research search for this reindex is running16145; no F71 code written yet.

- F68 public audits all standard-only, as is existing Cauchy Fourier theorem.
  Combined audit initially missed explicit `Bochner.ContinuousLinearMap` import
  for density conversion; corrected audit56762 running. F70 scratch/probes updated
  with that import. No F68 code changed after its final pass.
- Summatory reindex research16145 completed nonpartial; all20 candidates+20 source
  arguments+the generated proof idea+both ingredient steps inspected. Exact F41
  pair theorem is applicable; a supportMeanSquareRoughSet hit uses an equivalent
  empty-prime-filter predicate, whereas the planned direct finite set already
  matches roughCount exactly, so no extra model or conversion is needed.

- F69 corrected scratch passes warning-free; density-conversion root-name probe
  also passes. Final122-line leaf now compiling21998, wired; lint85045 and index
  launched. Four F68 public axiom checks were already standard; future API issue
  resolved here. F69 audit `/tmp/BagSmoothRoughSplitAudit.lean` prepared with all8
  public checks and exact F71 finite-sum API probes.
- F71 draft `/tmp/BagSmoothRoughSum.lean` written from C20.24; not compiled or a
  repository leaf. Proves finite multiplication reindex, smooth/rough frozen
  character identities, and exact polynomial separation. F70 Cauchy pair scratch
  still uncompiled. C20.25 records uniform deterministic pair-error route, avoiding
  separate outer expectation DCT; corresponding prior-research search launched.

- F69 FINAL: all8 audits standard-only, final122 lines warning-free, wired/index
  visible; lint12 unrelated unreachable modules. All F71 finite-sum API probes pass.
  F70 first Cauchy-kernel scratch now compiling, sole live owned Lean.
- Uniform-pair-error search partial; all20 candidates+20 source arguments+both
  ingredient steps inspected. Most hits irrelevant smooth-function derivatives;
  useful existing rough-count limit retained. Direct current mathlib source gives
  `tendsto_tsum_of_dominated_convergence` with an eventually uniform majorant,
  `Summable.mul_of_nonneg`, and exact integral/tsum interchange for summable
  integral norms. Signatures inspected; name probes pending. No F72 code yet.

- F70 third scratch passes. Complex numeral conjugation needs explicit
  `Complex.conj_ofNat` (not a simp lemma); that name probe passes too. Removed one
  unused `push_cast`; final70-line leaf now compiling54686, wired. Two public
  audits plus F72 exact API probes prepared in `/tmp/BagEulerCauchyKernelAudit.lean`.
  Lint3788 and exact index18751 running. F71 scratch still uncompiled.
- F72 `/tmp/BagSmoothPairError.lean` drafted from C20.25 with all-N majorant,
  absolute summability, nonnegativity and deterministic-error convergence.
  `/tmp/BagSmoothPairErrorNames.lean` prepares exact API probes. Current source
  distinguishes two-argument `abs_sub` from three-point `abs_sub_le`; draft uses
  the correct former. Explicit constant Tendsto type prevents limit metavariables.

- F70 final70-line leaf passes warning-free; wired/index-visible pair theoremline40;
  lint11 unrelated unreachable modules. Two public axiom audits and F72 names now
  compiling in `/tmp/BagEulerCauchyKernelAudit.lean`. F71 finite split next.

- F70 FINAL: both public audits standard-only; all F72 convergence/majorant APIs
  and future integral/tsum API pass. Final70 lines warning-free, wired/indexvisible,
  lint11 unrelated. F71 first scratch now compiling, includes an existing exact
  complex-coefficient Parseval theorem found/read in SteinhausComplexSecondMoment.
  Draft extended by literal rough-grouped frozen-prefix variance (fifth theorem);
  no need to reprove coefficient orthogonality. Added exact-name probe in scratch.

- F71 corrected scratch passes warning-free. Initial sole error was rewriting
  Finset.product notation; explicit `Finset.sum_product R A f` closes it directly.
  Final119-line leaf now passes warning-free, wired/index-visible variance line107;
  lint12 unrelated unreachable. All5 public audits and three future series API
  probes started. F72 scratch already drafted; all its names passed in F70 audit.

- F71 FINAL: all5 audits standard-only, future conjugate/tsum/product norm API
  probes pass. Final119 lines warning-free, wired/indexvisible; lint12 unrelated.
  F72 first complete scratch now compiling, sole owned Lean. F73 API file prepared
  `/tmp/BagEulerCauchySeriesNames.lean`, not yet compiled; no F73 implementation yet.

- F72 third scratch passes warning-free: unfold local real maximum before
  exact_mod_cast; use linarith for additive bound; explicitly unfold partially
  applied error definition before final Tendsto comparison (simp did not unfold
  the unsaturated definition). No mathematical change. Final109-line leaf now
  compiling72785, wired; five public audits plus F73 names prepared in
  `/tmp/BagSmoothPairErrorAudit.lean`; lint15391/index launched. Earlier memory
  estimate of six public results should read five theorems plus one definition.

- F72 final109-line leaf passes warning-free, wired/index-visible limitline90;
  lint10 unrelated unreachable. Five public audits and F73 exactAPI probes now
  compiling in `/tmp/BagSmoothPairErrorAudit.lean` (added Complex.norm_conj and
  root integral_complex_ofReal probes). No other owned jobs live.
- F73 complete scratch `/tmp/BagEulerCauchySeries.lean` written (~180lines), not
  compiled or a repository leaf. Private uniform bound/integrability of literal
  critical Euler norm²; pairwise Cauchy integration; summable integrated pair norms;
  exact squared Euler integral = smooth-pair maximum kernel; normalized mass
  identity with F67 via nonnegative Bochner/Lebesgue conversion. Imports F70/F67
  and direct sum/integral APIs; does not depend on F72's arithmetic count module.

- F72 FINAL: audit61911 exit0, all5 public results standard-only, all F73 API
  probes pass. Final109 lines warning-free, wired/indexvisible, lint10 unrelated.
- F73 first scratch8569 exit1: three coercion/function-normalization mismatches
  only (pointwise multiplication measurability, real-to-complex inverse cast,
  private criticalTerm under norm Summable). Explicit normalization now applied;
  second scratch next. F74 research found17 lexical roughCount hits, all inspected;
  no ready finite maximum-kernel cardinality identity. No F74 draft yet.

- F73 fourth scratch81316 exit0 warning-free. Measurable pointwise product needs
  explicit function extensionality after convert; targeted ofReal inverse/natCast
  simp preserves the natural maximum; explicit private-term Summable type closes
  the remaining mismatch. Both public identities and next finite-count APIs pass.
  Final179-line leaf written/wired, final check next. F74 complete scratch drafted
  `/tmp/BagSmoothRoughPairCount.lean`: finite quotient cardinality, zero count beyond
  cutoff, and literal frozen variance as finite rough-count smooth-pair sum.

- F73 FINAL: final66641 exit0 warning-free; audit61490 exit0, both public results
  standard-only and all finite-count name probes pass. Index mass identityline157;
  lint22132 exit1, twelve unrelated unreachable modules. F74 first scratch next.
- F75 prior research query returned20 ranked plus5 exploration hits, all inspected;
  broad lexical OR result is not exhaustive. Relevant fixed-prefix count/error and
  series results are our existing modules; no ready literal count-to-tsum identity.
  Mathlib finite-support HasSum and subtype-sum source signatures inspected next.

- F74 corrected scratch proves all three public results with no theorem errors or
  warnings. Combined run92988 exit1 solely from two future name probes: nonexistent
  HasSum.congr (unused), and norm_X needing full RHTower namespace. Removed/corrected
  probes; final111-line leaf written/wired, final check next. F75 scratch drafted
  `/tmp/BagSmoothRoughPairSeries.lean`: finite-support HasSum via bounded smooth
  subtypes, literal frozen variance HasSum, and all-N normalized coefficient HasSum.

- F74 FINAL: final64048 exit0 warning-free; audit17019 exit0, all3 public results
  standard-only, all corrected F75/series-bound name probes pass. Wired/indexvisible
  variance line98, lint6071 exit1 twelve unrelated unreachable modules. F75 scratch
  now compiling; includes forthcoming uniform-variance API probes.

- F75 second scratch78636 exit0 warning-free. Explicit HasSum type fixes a stuck
  summation-filter metavariable; targeted cast/div-mul simplification replaces an
  over-general convert. Both public results and all F76 bound APIs pass. Final69-line
  leaf written/wired; final check next. F76 `/tmp/BagFrozenVarianceCauchyLimit.lean`
  drafted: literal normalized variance definition, Cauchy finiteness/real identity,
  uniform deterministic total-error bound, and fixed-prefix variance limit.
  Exact F76 prior search returned3 error-object results, all inspected.

- F75 FINAL: final50816 exit0 warning-free; audit48733 exit0, both public results
  standard-only and all F76 names pass. Index98535 exit0 normalized line59;
  lint63269 exit1 twelve unrelated unreachable modules. F76 first scratch now
  compiling. F77 prior research first query empty; broadened first-moment query
  yields3 results, all inspected (F68 resampling, F62, F67 square-root mass limit).

- F76 second scratch30930 exit0 warning-free. Targeted complex cast simplification
  preserves natural max (unrestricted push_cast changes it to a real max); unfold
  local alpha/error before matching the final bound. All5 public results and F77
  names pass. Final leaf written/wired, final check next. F77 complete scratch
  `/tmp/BagSummatoryFirstMoment.lean` drafted: measurable literal normalized norm,
  exact conditional square, Cauchy/error first-mean bound, and all-N limit zero by
  selecting prefix first and arithmetic cutoff second. No recurrence claim.

- F76 FINAL: final1927 exit0 warning-free; audit35566 exit0 all5 results standard-only
  and all F77 names pass. Final104 lines, wired/indexvisible uniform boundline45;
  lint75300 exit1 twelve unrelated unreachable modules. F77 scratch extended with
  ordinary real first-mean identity and normalized-integral limit; first compilation
  next. F77 now6 public theorems plus one literal normalized-norm definition.

- F77 second scratch63080 exit0 warning-free, all6 public results and norm_norm
  name probe pass. Only first-run error was missing Function.comp_def when composing
  error convergence with ofReal/rpow. Ordinary first-mean limit is now proved in
  scratch, no imported probabilistic low-moment premise. Final151-line leaf written/
  wired; final check next. Audit includes exact finite Abel and subcritical power-sum
  source theorems and upcoming weighted-integral APIs.
- Weighted research `/tmp/bag-weighted-abel-source.json`: nonpartial, all20 candidate
  lemmas +20 source arguments inspected; no proof ideas/ingredient sets; 10 prose
  hits triaged, compiler coverage mostly pending/stale, semantic coverage unmeasured.
  Chosen lighter existing BourgainPartialSummation identity (source read); discarded
  heavier DirichletBlockAbel dependency. Existing SubCriticalPowerSum source read.
  New C20.26 paper proof records global-envelope simplification. No F78 code yet.

- F77 FINAL: final33557 exit0 warning-free; audit96259 exit0, all6 public results
  standard-only. Existing Bourgain finite Abel and SubCriticalPowerSum audits also
  standard-only; weighted integration APIs all pass after using current camel-case
  integral_finsetSum/integrable_finsetSum names. Final151 lines, wired/indexvisible
  real limitline138; lint67738 exit1 ten unrelated modules. All owned jobs terminal.
- F78 `/tmp/BagWeightedSummatoryAbel.lean` complete draft, not compiled: finite norm
  integrability, all-N ordinary mean ceiling, global C+epsilon*sqrt(n) envelope,
  actual weighted Abel mean bound, and transfer of that envelope. Existing exact
  Bourgain Abel identity reused. F79 stronger power-sum candidate found/read in
  HTGeometry/RpowPartialSumBound.lean (sum<=N^a/a); not yet Lean-name/axiom audited.

- F78 second scratch72343 exit0 warning-free. One initial error corrected by explicit
  add_le_add for the right-hand sum norm bound. All5 public results and next exact
  square-root/power-sum APIs pass. Final leaf written/wired without the future-only
  RpowPartialSumBound import; final check next. F79 `/tmp/BagAbelSqrtCost.lean`
  drafted: telescoped square-root cost, reciprocal-root increment bound, and sharper
  cost<=N^(1/2-beta)/(1/2-beta) from existing HTGeometry power-sum theorem. The cost
  bound itself needs no weight monotonicity; monotonicity remains in F78's mean
  inequality. F79 not compiled. Power-sum search:15 declarations+20 candidates+20
  source arguments inspected, nonpartial; compiler/semantic coverage still limited.

- F78 final82294 exit0 warning-free,129 lines, wired/indexvisible envelope line95;
  lint15822 exit1 ten unrelated unreachable modules. Audit87410 still running.
  F79 was accidentally launched before that audit terminated; immediately stopped
  only owned PIDs71795/71698, session18443 exit143, verified both PIDs absent.
  No replacement launched; wait for audit exit before restarting F79 scratch.
- F80 `/tmp/BagUniformWeightedMean.lean` drafted but not compiled: eventual bound
  uniformly over every admissible weight at each cutoff, then arbitrary varying
  weight-family limit. Prior search67712 completed nonpartial; all20 candidate+20
  source arguments inspected; relevant existing hit F78, no ready uniform theorem.

- F78 FINAL: audit87410 exit0, all5 public results and sharper existing power-sum
  theorem standard-only, all F79 APIs pass. No other owned Lean live. Restarting
  F79 scratch, with F80 rpow-limit API probes included. F80 remains uncompiled.

- F79 corrected scratch73426 exit0 warning-free, all3 public results and F80 names
  pass. Separate rpow-to-sqrt rewrite from one_div simplification (otherwise the
  exponent becomes2^-1 before matching sqrt). Power-atTop theorem is at root, not
  Real namespace; F80 corrected accordingly. Final leaf written/wired, without
  future-only asymptotics import; final check next. F80 complete draft waits.

- F79 final84417 exit0 warning-free,69lines, wired/indexvisible costboundline39.
  Audit now running. Lint96163 exit1: eleven unrelated unreachable modules plus
  two temporary proof-debt occurrences in unrelated WeilPrimeDeficitSetRigidity.lean
  lines353/354; no BAG error. Do not modify that other session's file. F80 next
  only after audit terminates. Gaussian prior search59359 completed nonpartial;
  all20 candidate+20source arguments inspected; actual cutoff positivity, upper1,
  zero imaginary part and antitonicity available in HighBlockCutoffMonotone.

- F79 FINAL: audit47955 exit0, all3 public results standard-only, all F80 names pass.
  Final69lines warning-free/wired/indexvisible; lint unrelated errors documented.
  F80 first scratch now compiling; appended exact Gaussian cutoff API probes using
  existing HighBlockCutoffMonotone. This import will remain scratch/audit-only inF80.

- F80 second scratch65512 exit0 warning-free, both public uniform/family limits
  and all F81 exact Gaussian APIs pass. First-run sole error was ring after
  field_simp already closed the algebraic goal. Final leaf written/wired; final
  check next. F81 `/tmp/BagGaussianWeightedMean.lean` complete uncompiled draft:
  actual real Gaussian weight, nonnegativity/power domination/monotone steps,
  exact complex coefficient equality, and all-positive-scale uniform mean decay.
  F80 audit also audits all four existing actual cutoff source properties.

- F80 FINAL: final39561 exit0 warning-free; audit69870 exit0, both public results
  and four actual Gaussian cutoff properties standard-only. Final65lines,
  wired/index-visible uniform theorem line13. Lint95133 exit1 twelve unrelated
  unreachable modules, no proof-debt errors. F81 scratch3137 now compiling alone.
  C20.27 records exact all-integer logarithmic rotation and first-mean transport;
  prior phase search20842 nonpartial, all20 candidate+20source arguments inspected.

- F81 corrected scratch99449 exit0 warning-free, five public actual Gaussian results
  and F82 exact names pass. Initial sole error fixed by unfolding the real-weight
  definition in the power-domination simpa. Final leaf written/wired, with future-
  only vertical-rotation import removed; final check next. F82 complete draft in
  /tmp/BagGaussianPhaseMean.lean, not compiled: all-integer logarithmic covariance,
  exact finite first-mean stationarity, actual Gaussian exponent transfer, and
  uniform mean decay over every phase/positive smoothing scale.

- Sequencing correction: F81 final30733 was still running when audit25656 was
  mistakenly launched. Audit immediately exited because the new olean did not
  yet exist; process inventory confirms only final30733 is live. Await explicit
  final exit_code before restarting audit or any other Lean command.

- F81 FINAL: final30733 exit0 warning-free; restarted audit15929 exit0, all5
  public results standard-only. Final80lines, wired/index-visible line59;
  lint54941 exit1 ten unrelated unreachable modules. All F82 names verified.
  F82 scratch launched only after audit terminal. F83 complete uncompiled draft
  /tmp/BagReflectedCarrierFirstMean.lean; C20.28 dependency-closed paper proof.
- Reflected source research43803: nonpartial, all20 candidate+20source arguments
  inspected but off-topic. Broadened lexical24468 inspected20 declarations,
  confirmed existing chi envelope and coefficient upper leaf; exact source bodies
  read. No imported first-mean premise. Semantic/compiler coverage remain limited.

- F82 corrected scratch28389 exit0 warning-free, four public phase-transport
  results and F83 names pass. Initial error was an uninferred measure parameter
  in integral_map_of_stronglyMeasurable; supplied the original probability law.
  Final leaf written/wired without future-only reflected-channel import; final
  check next. F83 draft ready. New C20.29 paper proof strengthens the background
  step: exact smooth projection contracts first mean for every retained cutoff,
  so no remainder subtraction is needed. F84 draft /tmp/BagSmoothCarrierProjection.lean
  uncompiled. Search59642 nonpartial, all20 candidates+20source arguments inspected;
  existing frozen kernel/resampling law apply. Search39124 second-moment candidates
  inspected; that weaker transfer is superseded by conditional-mean contraction.

- F82 FINAL: final11379 exit0 warning-free; audit79810 exit0 all4 public results
  standard-only. Existing exact coefficient/chi envelope also standard-only;
  F83/F84 core APIs pass. Final93lines, wired/index-visible line80. Lint44127
  exit1 ten unrelated unreachable modules. F83 scratch now running alone.
  F84 exact smooth projection and F85 finite-node smooth first-mean drafts wait.
  C20.30 records same-event positive-mass centre selection. Search94847 completed
  nonpartial, all20 candidates+20source arguments inspected, no ready theorem;
  exact mathlib real Markov and event difference inequalities read directly.

- F83 scratch23165: both public reflected-carrier proofs pass without warnings;
  only error is an appended future API probe using a wrong namespace for
  MeasurableSet.iInter (root, not MeasureTheory). Initial mathematical proof error
  was the rewrite direction of mul_div_assoc; corrected. Public leaf written/
  wired and final check next; corrected future probe moved into axiom audit.
  F84-F87 uncompiled drafts now record exact projection, finite-node first means,
  same-event mass retention and the actual covariance/centre intersection, including
  its small-prime dependence. These are not yet claimed as Lean results.

- F83 final64744 exit0 warning-free,79lines,wired/index-visible line40.
  Audit now running alone. Lint1224 exit1 ten unrelated unreachable modules.
  F84 next after audit terminal. C21 new paper candidate: finite affine circle
  densities prescribe exact means; product L2 cost plus Cauchy-Schwarz yields
  target-ball probability >=1/4*exp(-2*|v|²/lambda), once total variance is small
  and each prescribed circle mean has norm<=1/2. This would specialize to any
  desired power loss using C19/F45 and bounded centres. No local-target Lean
  code yet. Searches44318/58787 nonpartial; all20+20 candidates/source arguments
  inspected; no exact applicable theorem, broader Steinhaus text search agrees.

- F83 FINAL: audit97776 exit0, both public results standard-only; corrected
  MeasurableSet.iInter and all remaining F84-F87 named APIs pass. Final79lines
  warning-free/wired/index-visible, lint unrelated only. F84 scratch launched
  after audit terminal; all other owned jobs terminal.

- C21 source follow-up64450 completed nonpartial; all20 candidates+20source
  arguments inspected. Existing HTGeometry/CoerciveOperatorInverse.lean read
  completely (153lines): exists_inverse_of_coercive has precisely the complex
  Hilbert inverse norm bound needed for the Gram operator, without a spectral
  theorem. Not yet axiom/name-audited for this use. The finite affine circle law
  can use SteinhausModel.charInt on volume.restrict(Icc0,1); source read, alongside
  existing Euler tilt withDensity construction/change-of-measure pattern. No
  C21 Lean code yet; finish pending centre chain first.

- F84 corrected scratch99643 exit0 warning-free, all4 public projection results
  pass. Initial only error was unreduced lambda applications after integral_mono;
  dsimp only exposes the actual smooth sum before rewriting its inner-mean identity.
  Final leaf written/wired, final check next. This proves contraction for arbitrary
  retained finite sets, with no fixed-cofactor/size restriction. F85-F87 drafts wait.

- F84 final25875 exit0 warning-free,101lines,index-visible96. Audit23647 running.
  Lint66688 caught own new import missing after a concurrent umbrella rewrite;
  confirmed missing and restored it by append. Re-running lint for this new
  wiring change. That lint also reported eleven unrelated unreachable modules
  and a temporary sorry in unrelated WeilPrimitiveSetMeanSquare.lean:263; do not
  modify the other session's file. F77-F83 imports still present.

- F84 FINAL: audit23647 exit0 all4 public results standard-only and F85 APIs
  pass. Restored import remains present; rerun lint9127 exit1 eleven unrelated
  unreachable modules, previous unrelated proof-debt error gone. Final101lines
  warning-free/wired/index-visible96. F85 scratch now running alone.

- F85 corrected scratch86372 exit0 warning-free. First run passed the common
  height tau instead of actual node height tau+b_j to the scalar bound; fixing
  that application also removed its elaboration timeout without any heartbeat
  change. Both scalar/all-cutoff and finite-node summed first-mean statements
  pass. Final leaf written/wired by append; final check next. Prepared audit
  also checks C21's existing coercive inverse, finite product density, and exact
  one-circle Fourier integral sources. F86/F87 complete drafts wait.

- F85 FINAL: final46788 exit0 warning-free; audit19123 exit0 both public results
  standard-only. Final50lines,wired/index-visible23; lint21391 exit1 ten unrelated
  unreachable modules. C21 existing coercive inverse, finite product withDensity,
  and actual one-circle charInt also standard-only. F86 scratch now compiling
  alone. F87 complete draft awaits F86 final/audit. Future rank-one Gram APIs
  prepared in F86 audit; no C21 code yet.

- F86 corrected scratch31413 exit0 warning-free, all4 public centre-event results
  pass. Explicitly specifying the finite-sum function removed the isDefEq timeout
  at single_le_sum; no heartbeat change. Actual centre event is measurable and
  reads only the conditioning primes. Its discarded probability is at most the
  summed original first mean, giving half-mass retention inside any event of
  fixed positive mass. Final leaf written/wired by append; final check next.

- F86 final7717 exit0 warning-free; audit now running alone. F87 complete draft
  waits. C21 first source draft /tmp/BagFiniteTargetBiases.lean now written but
  uncompiled: exact finite rank-one Gram operator and energy identity; existing
  coercive inverse yields prescribed target biases with total energy <=norm(v)^2/lambda
  and pointwise norm <=norm(a_i)*norm(v)/lambda. All complex conjugations match
  inner's linear second argument. Exact APIs are being probed in F86 audit.

- F86 FINAL: final7717 exit0 warning-free,81lines,index-visible64; lint44846
  exit1 ten unrelated unreachable modules. Audit83707 prints all4 public and
  existing covariance-event axioms standard-only. Its only error was an appended
  future rankOne definition probe requiring noncomputable; and deprecated
  ContinuousLinearMap.sum_apply warned. Corrected to noncomputable probe/root
  sum_apply in F87 scratch, rather than repeating passed public axiom reports.
  F87 scratch now running alone, with corrected F88 probes appended. Final F87
  will omit these future-only imports/probes. F88 draft updated to root sum_apply.

- F87 corrected scratch48549 exit0 warning-free. Initial errors were missing
  ENNReal scope for infinity and an ambiguous future sum_apply probe (root vs
  Finset); corrected scope and explicit _root_.sum_apply. Actual covariance/
  bounded-centre event assembly passes, including fixed positive mass, finite
  prefix preservation, common-height window and small-prime dependence. Corrected
  rankOne/sum_apply/F88 probes pass. Final leaf written/wired, future-only imports
  and probes removed; final check next. Audit also probes exact next circle APIs.

- F87 statement audit caught a real interface omission: the existential selected
  event did not explicitly remain inside the prescribed rotated character cell,
  so its displayed preserved prefix centre was disconnected from the event.
  Added E subset that literal cell, with intersection_subset_left as the proof.
  The former final18308/audit17991 concern the weaker statement; F87 is NOT FINAL.
  Recheck the strengthened scratch, then rewrite/final-check/audit the exact
  stronger leaf. Future direct-edge constraints need this retained containment.

- The weaker F87 audit17991 printed the public theorem standard-only; its only
  future API error was integral_complex_ofReal placed under MeasureTheory.
  Source confirms it is root-level; corrected and explicitly imported the
  Bochner ContinuousLinearMap module in audit. Strengthened scratch66074 now
  running alone. Current repo F87 leaf remains the former weaker version until
  that strengthened scratch passes; do not mark it final or update frontier yet.

- Strengthened F87 scratch66074 exit0 warning-free. Exact selected-event subset
  of the prescribed rotated cell is now in the public statement and proof.
  Replaced the repository leaf with that stronger version; final/audit next.
  Earlier weaker checks are not used to claim this strengthened theorem verified.

- Strengthened F87 final45203 exit0 warning-free,80lines,index-visible12.
  Audit48890 running alone. Lint27021 exit1: ten unrelated unreachable modules
  plus two temporary proof-debt occurrences in unrelated ZetaNotchTruncatedDiagonal.lean
  lines46/73; no BAG error. Keep other session's files untouched. F88 finite
  target-bias source draft is complete and uncompiled; compile only after this
  exact strengthened F87 audit terminates. No F89 affine-circle draft exists yet.

- Strengthened F87 FINAL: audit48890 exit0, exact public theorem standard-only;
  all next circle APIs pass with root integral_complex_ofReal. Final80lines,
  warning-free/wired/index-visible12; lint unrelated errors documented. Actual
  E-subset-prescribed-cell assertion preserved. C20 bounded-centre gap closed.
  F88 scratch now running alone; no other owned process live.

- F88 first scratch11647: frame application/energy proofs checked, but lambda
  character is a reserved parser token in the binder; renamed the floor to c.
  Moved CompleteSpace instance to the inverse theorem to remove unused-section-
  variable warning. Corrected scratch now running alone. F89 complete uncompiled
  draft /tmp/BagAffineCircleMean.lean: original interval Fourier-character algebra,
  real affine density, nonnegativity, normalization, and exact prescribed complex
  first moment. Second density moment/product law still need their own proof.

- F88 corrected scratch33666 exit0 warning-free; exact frame apply/energy and
  target-bias synthesis all pass. Corrected binder/instance scopes; all needed
  complex norm API probes pass. Final leaf written/wired, final check next.
  F89 affine-circle normalization/prescribed-mean draft awaits this final/audit.

- F88 FINAL: final23446 exit0 warning-free; audit71154 exit0 all3 public results
  standard-only. Final57lines,wired/index-visible30; lint46838 exit1 twelve
  unrelated unreachable modules, no proof debt. F89 scratch now running alone;
  no other owned process live. No F90 draft yet.

- F89 first scratch24555 failed because conj notation requires the explicit
  ComplexConjugate scope. Added it; corrected scratch3434 running. All error-
  generated sorry terms were scratch elaboration fallout, never source proof
  placeholders or repository declarations. F90 /tmp/BagAffineCircleMeasure.lean
  complete uncompiled draft: exact density second moment 1+2*norm(m)^2,
  concrete withDensity probability law, generic integral change of measure and
  exact phase mean. F89 scratch includes exact F90 API probes.

- F89 corrected scratch95846 exit0 warning-free, all10 public results and F90
  APIs pass. Besides missing conj scope, fixed integral_add rewriting by giving
  explicit integrable partial-sum functions and coefficient constants; removed
  redundant ring after simp; withDensity-toReal integral API is root-level.
  Applied the same explicit-function fix to F90's uncompiled moment draft.
  Final F89 leaf written/wired, final check next.
- Density cost research26230 completed nonpartial; all20 candidates+20source
  arguments inspected. Useful candidates: HTGeometry.SquareIntegrableKernelOperator
  squared lintegral Cauchy and HTGeometry.FiniteWindowAverage; bodies not yet read.
  GaussianShiftInformation has product density infrastructure, not event cost.

- F89 FINAL: final11444 exit0 warning-free; all10 public reports in audit70466
  standard-only, as is the existing generic squared-lintegral Cauchy theorem.
  Audit exit1 only from future unavailable namespace probe
  MeasureTheory.lintegral_mono_measure. Read actual mathlib source: use
  lintegral_mono' with measure inequality and le_rfl. Corrected F91 draft.
  Lint81263 exit1 twelve unrelated unreachable modules, no proof debt/BAG error;
  exact normalization index83. F90 scratch48258 now sole live Lean.
  F91 density-event transfer remains an uncompiled /tmp draft.

- F90 first scratch48258 failed only at charFactor0 simplification and the
  generic change-of-measure lambda beta reduction. Added charFactor_zero and
  dsimp only; corrected scratch39324 exit0 warning-free. Final leaf now written
  and wired; sole final2571 running. F91 generic event-cost draft ready next.
  F92 complete uncompiled finite affine-product draft uses literal product
  density, exact second-moment factorization and exponential event transfer.
- Finite biased-sum research92852 completed nonpartial; all20 candidates and
  all20 source arguments inspected. Semantic coverage unmeasured; background
  indexer still running. Existing independent-coordinate mean-square theorem
  is scalar and countably indexed; read its proof as a finite orthogonality
  pattern. No ready actual affine-product vector local-target theorem found.
