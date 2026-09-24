# Route P facts (root)

- Literal matched-centroid excess atom is
  `w_n (centroid_n - 2 sqrt(n))`, with `w_n = Λ(n)/sqrt(n)`.
  From `centroid_n² = 4n + w_n²/4`, it is nonnegative and at most
  `w_n³/(16 sqrt(n)) ≤ log(n)³/(16 n²)` for `n>0`.
- The atom sequence is summable. The existing finite Route P
  `ccmActualHeadMatchedCentroidChebyshevExcess K` equals its prefix through
  `K+2`, is bounded by its total sum, and converges to that finite sum.
  Lean: `SPEQuantileRieszRoutePTerminalCentroidExcessSummability.lean`.
- Whole-route implication: at physical ratio one the nonnegative geometric
  correction is a finite constant, not a growing reservoir. The exact barrier
  remains `4 chebyshevError(x) + (mass-2 sqrt(x))² + 4 mass + O(1)`;
  its sign and the ordered-history graph intertwiner are still open.
- For normalized centroid variance, summable excess is amplified by
  barycentric recentering. Let `m_K` be critical mass, `p_K = ψ(K+2)`,
  `e_K` matched centroid excess, `q_K = Σ_{n≤K+2} w_n³/4`, and
  `c₀(n)=2 sqrt(n)`. Exact finite identity:
  `Var_K(matched) - Var_K(c₀) = q_K - (4 p_K e_K + e_K²)/m_K`.
  Lean: `SPEQuantileRieszRoutePIdealCentroidVarianceCorrection.lean`.
- `w_n→0` by `Λ(n)≤log n`, so Cesàro gives `m_K/(K+1)→0`.
  Unconditional PNT gives `p_K/(K+1)→1`; hence `p_K/m_K→∞`.
  Existing corpus cube summability bounds `q_K`, and the atom at `n=2`
  gives `e_K≥e₂>0`. Therefore
  `Var_K(matched) - Var_K(c₀)→-∞`, proved in
  `SPEQuantileRieszRoutePIdealCentroidVarianceEscape.lean`.
- Whole-route implication: finite local geometry is not negligible after
  global centering. Any cofinal nonnegative matched-minus-quantile variance
  must gain an unbounded compensating contribution from the ideal-minus-quantile
  term. This does not decide that term's sign or construct the ordered-history
  graph intertwiner; those remain the hard route obstacles.
- Equal-mass quantile cells tile one interval. Their normalized centroid
  variance is exactly `mass³/12 - widthCubePrefix/3`. Consequently the literal
  normalized prime-power history is `4 sqrtChebyshevMoment + 4 widthCubePrefix/3
  - (2 psi + centroidExcess)²/mass - mass³/12`.
  Lean: `SPEQuantileRieszRoutePArithmeticVarianceNull.lean`.
- Put `x=K+2`, `r=√x`, `μ=mass-2r`, `ε=psi(x)-x`, `e=centroidExcess`,
  `q=widthCubePrefix`, and `C=sqrtChebyshevMoment-(2/3)xr-rε`. Exact null law:
  `history/mass = 4C - 2re - (2ε+e-rμ)²/mass - (4r+mass)μ²/12 + 4q/3`.
  Thus linear endpoint mass error cancels; all remaining geometry except cubic
  width is negative. Lean: `SPEQuantileRieszRoutePWeightedChebyshevCredit.lean`.
- Finite Abel summation cancels terminal `psi(x)r` inside `C`:
  `C = x r/3 - Σ_{j<K} psi(j+2)(√(j+3)-√(j+2))`, equivalently deterministic
  lattice baseline minus the same Abel sum of `psi(j+2)-(j+2)`.
  Lean: `SPEQuantileRieszRoutePChebyshevAbelLattice.lean`.
- The geometric remainder `history/mass - 4C` tends to `-∞` unconditionally.
  Prime-two centroid excess gives a fixed positive lower floor, multiplied by
  `2√x`; cubic width is bounded and both square debts are nonnegative.
  Lean: `SPEQuantileRieszRoutePWeightedCreditEscape.lean`.
  Whole-route consequence: a nonnegative cofinal history must acquire growing
  signed Abel-integrated Chebyshev credit. Bounded-credit/geometry-only repairs
  cannot work. This does not establish the credit's sign or the independent
  ordered-history terminal graph intertwiner.
- The literal unit-Riesz source `S(t)` has unconditional quantitative
  two-sided excursions: for every real `B,T`, some `t>T` satisfies
  `S(t)>B exp(-t/2)`, and some `t>T` satisfies
  `S(t)<-B exp(-t/2)`. A hypothetical eventual floor yields a positive
  perturbed tail; its transform extends past the Hardy axis by the low-height
  Landau disk, after subtracting a correction pole at `-1/2`, contradicting
  the proved source nonextension. Lean:
  `SPEQuantileRieszRoutePSourceQuantitativeOscillation.lean`; leaf-only
  `lake --old build` passed; both theorem axiom audits show only
  `propext`, `Classical.choice`, `Quot.sound`.
- This source theorem alone does not bound Chebyshev and mass-mismatch square
  debts jointly and does not imply RH or the ordered-history intertwiner.
- Integer-cell transfer is sharp enough for the source floor: if `N≥2` and
  `N≤X≤N+1`, then `X·S(log X) - (log 4+5)√X ≤ N·S(log N)`.
  Consequently arbitrarily late integer `N` have `N·S(log N)>0`.
  Combined with `C=-(N/2)S(log N)` and
  `history/mass - 4C → -∞`, the complete normalized physical history is
  cofinally unbounded below: for every real `B` and natural `M`, some
  `K≥M` has `history/mass(K)<B`. Lean:
  `SPEQuantileRieszRoutePSourceIntegerHistoryNoGo.lean`; targeted
  `lake --old build` passed; all three theorem axiom audits show only
  `propext`, `Classical.choice`, `Quot.sound`.
- Whole-route no-go: unconditional global nonnegative physical-history
  passivity is impossible, even if RH happens to hold. Any surviving P/SP-E
  mechanism needs signed aperture selection, a source compensator that pays
  the coupled debts, and a coefficient-faithful ordered-history graph on a
  singular or meromorphic source domain.
- Exact cross-route identification at `x=K+2`:
  `C = x sqrt(x)/3 - (x/2)·unitRieszVonMangoldtRenewal(x,x)` and
  `C = -(x/2)·criticalMellinChebyshevResolventSource(log x)`.
  Lean: `SPEQuantileRieszRoutePUnitRieszRenewalBridge.lean`. Corpus already
  proves the source has a zeta-log-derivative Laplace weld and RH-equivalent
  boundedness; the new equality identifies P's only signed credit with that
  source, not with a free graph correction.
- SP-E's existing literal completed quantile transport equals `x` times the
  same resolvent source, so `C = -transport(x)/2` exactly. Therefore
  `history/mass + 2·transport(x) -> -∞` unconditionally.
  Lean: `SPEQuantileRieszRoutePTransportHistoryEscape.lean`.
  Whole-route consequence: scalar P history and SP-E completed transport are
  linked but have an unbounded negative geometric mismatch. A cofinal ordered
  graph action must carry that mismatch plus the independent terminal
  connection; this result does not construct it or settle RH.
- The literal source transform on `Re z>1/2` equals
  `F(z)=(-(logDeriv zetaResidueUnit (z+1/2)+1)/(z+1/2)-2/3)/(z+1)`.
  This follows algebraically from the corpus's already-proved complex defect
  weld, without a new analytic premise. Hardy's theorem supplies a positive
  critical-line ordinate where `F` is not even continuous, by transferring the
  nonzero boost-current residue through the exact factorization.
  Lean: `SPEQuantileRieszRoutePSourceSpectralPole.lean`; axiom audit only
  `[propext, Classical.choice, Quot.sound]`.
- Whole-route implication: P's signed credit and SP-E's completed transport
  share a genuine imaginary-axis spectral singularity. Their scalar source
  cannot be replaced by a globally holomorphic positive proxy. The later
  Landau and integer-cell results settle source signs and negative physical
  history excursions, but not debt payment or the ordered terminal graph.
- The required low-height analytic disk is now Lean-proved, not conjectural:
  `F` is analytic at every `z` with `Re z > -1/2` and `|Im z|≤4`, hence on
  `closedBall 1 (5/4)`. Lean:
  `SPEQuantileRieszRoutePLandauDisk.lean`. The disk reaches `Re z=-1/4`
  while staying clear of the `z+1`, `z+1/2` denominators and all zeta zeros.
  This supplies exact Landau continuation radius.
- For any eventual sign `epsilon * S(t) ≥ 0` on `t>T` with `T≥0`, the literal
  tilted tail is a positive measure. Its complex MGF is exactly the signed
  tail Laplace transform; the omitted compact head is entire. Landau's
  positive-measure theorem and the disk above force a `9/8` exponential
  moment at tilt `1`, hence tail convergence at Laplace parameter `-1/8`.
  Lean: `SPEQuantileRieszRoutePSourceLandauCarrier.lean` (direct `.olean`
  compiled). This is a conditional consequence of the sign hypothesis,
  not a claim that the sign hypothesis holds.
- The same moment makes the reconstructed literal source transform analytic
  on `Re z>-1/8`; it agrees with `F` on `Re z>1/2`. Lean:
  `SPEQuantileRieszRoutePSourceLandauExtension.lean` (direct `.olean`
  compiled).
- The reconstructed transform yields an analytic pole-filled zeta
  logarithmic derivative on `Re s>3/8` under any eventual fixed sign. The
  analytic differential identity and exact meromorphic order `-1` at a zeta
  zero exclude Hardy's unconditional critical-line zero. Therefore the
  literal source has positive and negative values arbitrarily far along the
  logarithmic ray. Lean:
  `SPEQuantileRieszRoutePSourceCofinalSignOscillation.lean` (direct `.olean`
  compiled); axiom audit only `[propext, Classical.choice, Quot.sound]`.
  This settled qualitative source-sign recurrence; the later quantitative
  source and integer-cell theorems strengthen it. The ordered terminal graph
  and joint debt payment remain open.
- The base-prime-2 Lorentz edges uniformly control the *anchored first
  displacement moment*, despite the corpus no-go that the total effective
  resistance diverges. Precisely, for `M_K = Σ_{n≤K} w_{n+2}(d_{n+2}-d_2)`
  there are fixed `A,B≥0` with `M_K² ≤ A+B·D_K`, where `D_K` is the literal
  full Lorentz graph dissipation. The proof uses the exact base-edge lever
  `n+2` and the summable reciprocal mass
  `Σ 2w_{n+2}/(w_2(n+2))`; no global resistance bound is used.
- The first physical square-debt argument is **exactly** `T_K-M_K`, with
  `T_K=m_K(2+m_K/2-√(K+2)-d_2)`. The `+2` is forced by the quantile
  mass-coordinate origin. Thus its physical ratio-one debt is bounded by
  `(2T_K²+A+B·D_K)/m_K`, uniformly in `K`. Lean:
  `SPEQuantileRieszRoutePAnchorGraphDebtControl.lean`; leaf-only
  `lake --old build <leaf>:olean` passed; six key axiom audits show only
  `[propext, Classical.choice, Quot.sound]`; formal lint passed.
- Whole-route meaning: the physical first square debt is controlled by a
  graph-quotient displacement moment plus one explicit terminal scalar. This
  is new positive salvage from the effective-resistance obstruction, but not signed
  payment: source credit must still dominate terminal scalar, graph energy,
  second mass-mismatch debt and centroid excess on selected physical heads;
  meromorphic ordered-history intertwiner is independent and open.
- The literal normalized variance flux is eventually opposite in sign to its
  centered matched-to-quantile displacement: the matched-offset factor is
  positive since its polar-scaled limit is `1`, while the similarly scaled
  centered displacement tends to `0`. The polar-scaled physical head mass
  tends to `2`. Lean:
  `SPEQuantileRieszRoutePLocalFluxOrientation.lean`; scratch direct Lean and
  targeted `--old` leaf `.olean` build passed. Axiom/lint audit is pending;
  do not infer it from compilation.
- Whole-route boundary: this is an exact late *local* orientation law, not a
  sign for cumulative flux or a signed payment of either physical square
  debt. A surviving P/SP-E argument must control the source-selected sum of
  centered displacements and independently construct a meromorphic
  coefficient-faithful ordered-history graph intertwiner.
- The normalized physical history is cofinally unbounded below, and its
  successor difference is exactly the one-atom flux. Hence negative flux
  occurs arbitrarily late; the eventual local orientation factor makes the
  centered matched-to-quantile displacement positive at arbitrarily late
  **prime-power** admissions. Lean:
  `SPEQuantileRieszRoutePForcedLocalRecurrence.lean`; scratch Lean, targeted
  `--old` leaf `.olean`, formal lint, and both axiom audits passed. Axioms:
  `[propext, Classical.choice, Quot.sound]`.
- Whole-route consequence: no compensator can rely on eventual nonpositive
  centered displacement at every prime-power admission. This is a forced
  arithmetic local recurrence, not a global signed debt payment or an RH
  proof; the cumulative positive/negative variation and meromorphic graph
  landing remain open.
- The complete finite strict-cross source current is exactly the all-ones
  quadratic form of its literal parabolic cross-kernel matrix: diagonal
  matched/quantile cancellation removes self-cells, and the off-diagonal sum
  is the original source pairing. Since normalized history is cofinally
  unbounded below and physical mass is positive, this matrix is **not**
  positive semidefinite at arbitrarily late physical heads. Lean:
  `SPEQuantileRieszRoutePStrictCrossNonpositive.lean`; scratch Lean, targeted
  `--old` leaf `.olean`, formal lint, and both axiom audits passed. Axioms:
  `[propext, Classical.choice, Quot.sound]`.
- Whole-route consequence: P-G206's positive rank-one completed-Xi
  environment block cannot equal the complete signed strict-cross current
  coefficient-faithfully on every late head. The exact all-ones quadratic
  identity is the positive survivor and constrains any replacement. A viable
  landing must retain an indefinite channel or add a genuinely source-derived
  compensator; neither global order law nor RH follows from this no-go.
- Quantitative source oscillation and the fixed `(log 4 + 5) sqrt X`
  integer-cell transfer loss give, for every real `B` and cutoff `M`, an
  integer `N≥M` with `N·S(log N)>B sqrt N`. Since the normalized physical
  history is eventually below `4C=-2N·S(log N)`, for every `B,M` some
  `K≥M` satisfies `history(K)<B sqrt(K+2)`. Lean:
  `SPEQuantileRieszRoutePSqrtScaleEscape.lean`; scratch check, targeted
  `lake --old` leaf `.olean` build, lint, and both axiom audits passed.
  Axioms: `[propext, Classical.choice, Quot.sound]`.
- Whole-route necessity: a uniformly `O(sqrt x)` source compensator cannot
  restore blanket nonnegative physical history. A sign-selected mechanism
  must tolerate arbitrarily large negative square-root-normalized excursions;
  the source-selected joint debt payment and meromorphic ordered graph remain
  open. This is a quantitative no-go, not an RH proof.
- A proposed monotone-`psi` triangular-area payment is insufficient as a
  standalone source argument: on every non-prime-power admission the corpus's
  exact normalized flux is zero, so Abel-credit movement and all geometric
  debt/baseline movement cancel in the physical history. Any actual payment
  must resolve active prime-power curvature, not only the zero-atom ramp.
- For every real `B` and cutoff `M`, some `K≥M` has normalized one-atom flux
  below `-B` times the physical square-root-clock increment. The witness can
  always be chosen at a prime-power admission, because zero-atom flux is
  exactly zero. Lean: `SPEQuantileRieszRoutePForcedRootClockFlux.lean`;
  scratch Lean, targeted `lake --old` leaf `.olean`, lint and two axiom audits
  passed. Axioms: `[propext, Classical.choice, Quot.sound]`.
- Whole-route necessity: no uniformly Lipschitz lower response in the
  physical square-root clock can realize the complete signed source history.
  A cofinal ordered graph must carry arbitrarily steep active arithmetic
  negative flux; this does not prove a sign-selected debt payment or RH.
- P-G186's canonical Burnol feature is **pointwise identical** to the
  source-native prime Burnol feature at every primitive `(p,e)`, ordinate,
  and half-line coordinate. The key arithmetic identity is
  `Λ(p^(e+1))=log p`, so their square-root amplitudes coincide; the
  conormal exponent is the same `-((log p^(e+1))+iκ)L`. Consequently their
  complete finite Gram matrices coincide, not only their diagonals.
  The corpus's pre-existing modular-support theorem therefore proves the
  actual P-G186 Gram is invertible on every injectively labelled packet;
  prime-log conjugation preserves invertibility. Lean:
  `RoutePPrimitiveBurnolGramModularFaithfulness.lean`; scratch and leaf
  `lake --old env lean`, targeted `lake --old ...:olean`, lint passed.
- Whole-route meaning: finite two-Julia `H*C*H` cannot erase a signed
  current merely by a null direction of `H`. This is finite faithfulness,
  **not** a uniform lower singular-value bound. Full active-head packet
  incidence and cofinal inverse/graph estimates remain open; without them
  negative physical current is not yet proved to survive graph closure.
- Every physical head admits an injective P-G186 packet containing exactly
  its active prime-power labels. Its five-profile cross-current agrees
  entrywise with the physical strict-cross kernel restricted to those labels;
  inactive rows and columns vanish. Hence the complete packet double sum is
  **exactly** the physical source current. Cofinal negative physical source
  excursions make these packet matrices non-PSD; invertible Hermitian
  prime-log P-G186 Gram congruence preserves non-PSD of the actual forward
  `H*C*H` two-Julia middle coefficient. Lean:
  `SPEQuantileRieszRoutePActiveHeadHistorySurvival.lean`; scratch check,
  leaf-only `lake --old env lean`, targeted `lake --old ...:olean`, formal
  lint, and axiom audit passed. Axioms:
  `[propext, Classical.choice, Quot.sound]`.
- Whole-route consequence: full finite source-to-P incidence and finite
  signed-history survival are closed. Positive Hodge/Xi environment cannot
  absorb the complete signed current merely by P-G186 null-space collapse.
  The hard remaining gate is a source-derived sign-sensitive compensator plus
  cofinal graph-form transport respecting source poles; finite Gram
  invertibility alone gives no uniform inverse or Xi divisor equality.
- At every positive-height zeta zero `rho` of multiplicity `m≥1`, the literal
  Route P source continuation has nonzero residue
  `-m/(rho*(rho+1/2))` at `rho-1/2`. If a continuous scalar gauge makes its
  product with that source continuous there, the gauge must vanish there.
  Lean: `SPEQuantileRieszRoutePSourcePoleResidue.lean`; scratch, leaf
  `lake --old env lean`, targeted `lake --old ...:olean` passed. This fixes
  necessary zero-divisor data for a meromorphic graph intertwiner; it does
  not construct that graph, pay signed debts, or prove RH.
- Hardy's formal critical-line zero theorem makes the quantized source-pole
  and forced gauge-zero conclusion unconditional: the same Lean leaf has a
  closed `exists_routePSourceLaplaceContinuation_quantized_critical_pole`
  theorem with no external assumptions. It still supplies only necessary
  meromorphic graph data, not cofinal graph transport or an RH implication.
- The source-intrinsic reciprocal, patched to zero at a positive-height zeta
  pole, has a nonzero first derivative equal to the inverse quantized source
  residue. If a differentiable gauge `g` vanishes at the pole and a separately
  patched continuous `h` agrees with `g·source` puncturedly, its center value
  is exactly `g'(pole)·residue`. By contrast, continuity of the **unpatched**
  totalized product forces `g'(pole)=0`; Hardy supplies a closed unconditional
  witness. Lean: `SPEQuantileRieszRoutePSourcePoleGaugeJet.lean`, scratch and
  targeted `--old` leaf build passed. This sharpens local graph patching and
  first-jet constraints but does not produce a cofinal graph or debt payment.
- Under any eventual one-sided constant bound
  `epsilon·source(t)+B ≥ 0`, the literal shifted tail defines a nonnegative
  measure. Its MGF is exactly the shifted source tail Laplace transform;
  source plus compact-head subtraction plus the constant-shift term is its
  analytic germ. Landau transfer supplies exponential moments for every
  tilt `<1`, so the reconstructed source transform is analytic on `Re z>0`
  and equals the literal continuation on `Re z>1/2`. Lean:
  `SPEQuantileRieszRoutePShiftedPositiveCarrier.lean`; scratch and targeted
  `--old` leaf build passed. This is conditional on the bound, not a proof of
  such a bound or an unconditional RH implication.
- Under the same one-sided bound with `epsilon ≠ 0`, the reconstructed
  logarithmic derivative is analytic on `Re s>1/2`, agrees with the actual
  regularized-zeta logarithmic derivative on `Re s>1`, and analytic-identity
  rigidity propagates the equality across `Re s>1/2`. A hypothetical
  regularized-zeta zero there would force an exact logarithmic-derivative
  pole and is excluded. Consequently the shifted positive-tail
  reconstruction equals the literal Route P continuation on **all**
  `Re z>0`. Lean: `SPEQuantileRieszRoutePShiftedAnalyticRigidity.lean`;
  scratch and targeted `--old` leaf build passed. This remains conditional
  on the one-sided source bound, which is unproved.
- For any positive real measure, if its real MGF has boundary Abel mass `B`
  at tilt `1` and its complex MGF has an imaginary-axis Abel residue `c` at
  the same tilt, then `‖c‖≤B`. This follows from the pointwise norm bound
  `‖complexMGF(z)‖≤mgf(Re z)` before taking boundary limits. Lean:
  `PositiveMGFBoundaryResidue.lean`; Mathlib-only scratch, direct Lean, and
  targeted `--old` leaf `.olean` passed. This is the core quantitative
  obstruction for a constant-shifted Route-P positive tail.
- At every positive-height critical-line zero, the source has a nonzero
  imaginary-axis residue `c=-m/(rho(rho+1/2))`. If an eventual one-sided
  constant shift `epsilon·S+B` were nonnegative, analytic rigidity welds its
  positive-tail MGF to the literal source for all `Re z>0`; its real boundary
  Abel mass is `B`, while its imaginary boundary residue is `epsilon·c`.
  The positive-MGF inequality forces `‖epsilon·c‖≤B`. Taking `epsilon=±1`
  and `B=‖c‖/2` proves a closed theorem: some fixed `δ>0` has both
  `S(t)>δ` and `S(t)<-δ` arbitrarily far out. Lean:
  `SPEQuantileRieszRoutePSourceFixedAmplitudeOscillation.lean`; scratch,
  direct Lean, and targeted `--old` leaf `.olean` passed. This strengthens
  the corpus's decaying-amplitude oscillation but does not synchronize the
  signed credit with terminal/square debts or construct the Xi graph.
- The fixed source amplitude survives integer-cell transfer: for some
  `δ>0`, arbitrarily large integer `N` satisfy
  `δ N < N·S(log N)`. Transfer loses at most `(log 4+5)√X`, asymptotically
  below the source's linear credit. Since the exact normalized history is
  `-2N·S(log N)` plus an eventually negative geometric remainder, some
  `c>0` has cofinal physical heads `K` with
  `history(K)/mass(K) < -c(K+2)`. Lean:
  `SPEQuantileRieszRoutePLinearHistoryEscape.lean`; scratch, direct Lean,
  targeted `--old` leaf `.olean`, and formal lint passed. This upgrades the
  prior square-root-scale escape: every sublinear positive compensator fails
  to restore blanket passivity. It does not imply that a linear or larger
  **signed, source-faithful** compensator exists, nor pay debts or prove RH.
- An eventual one-sided **upper** bound on the literal unit-Riesz source
  forces RH: the constant-shift positive-tail analytic reconstruction is
  holomorphic on the right half-plane, so its equality with the actual zeta
  logarithmic derivative excludes every right-strip zero. Contrapositively,
  if RH fails the source exceeds every prescribed height arbitrarily late.
  The integer-cell transfer loses only `O(√X)`; choosing a larger source
  height preserves arbitrary amplitude at integer heads. The exact history
  remainder is eventually negative, hence the closed Lean theorem
  `routeP_normalized_history_superlinear_escape_or_RH` proves: either RH,
  or for every real `B` the normalized physical history is `< -B(K+2)`
  at arbitrarily large heads. Lean:
  `SPEQuantileRieszRoutePLinearLowerThreshold.lean`; scratch Lean and targeted
  `lake --old -q build ...:olean` passed. Whole-route meaning: any universal
  eventual linear lower bound for this literal history would prove RH; no
  such bound or Xi graph has been constructed. The opposite RH⇒linear-bound
  direction would require a global inverse-square-root weighted prime-mass
  error estimate in addition to the corpus's RH⇒Chebyshev power bound.
- At `x=K+2`, the physical mass `m_K` is exactly Suzuki's Abel-weighted
  Chebyshev mass. Abel subtraction gives
  `m_K-(2√x-1)=x^(-1/2)(ψ(x)-x)+(1/2)∫₁ˣ t^(-3/2)(ψ(t)-t)dt`.
  From RH⇒`|ψ(t)-t|≤C t^(5/8)`, the new Lean theorem gives
  `|m_K-2√x|≤D x^(1/8)` for every `K`.
- The exact physical two-square decomposition, bounded centroid excess,
  nonnegative width cube, unconditional mass lower bound, and RH-bounded
  unit-Riesz source now yield `H_K≥-B(K+2)` for all `K≥3`. Combined with
  the preceding unconditional escape-or-RH theorem, the **closed Lean
  equivalence** is `RH ↔ ∃B≥0 ∀K≥3, H_K≥-B(K+2)`.
  Lean: `SPEQuantileRieszRoutePLinearFloorCriterion.lean`; scratch and
  targeted `lake --old -q build <leaf>:olean` passed; umbrella wired.
- Whole-route meaning: source credit is `-xS(log x)/2`, so its RH-controlled
  scale is *linear*, not `x^(3/4)`; the two square debts are at most
  `O(x^(3/4))` under RH. The corpus already proves cofinal fixed-amplitude
  negative linear excursions unconditionally. Hence the exact missing
  arithmetic obligation is a **uniform linear lower amplitude**, not a
  nonnegative or sublinear floor. This criterion does not prove that floor
  unconditionally, pay debts from source, or construct the meromorphic
  ordered-history graph.
