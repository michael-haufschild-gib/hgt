# Opus review 3010: the Lean frontier and where it points

Status: 30 October 2026, corpus `632f87ee3c` plus working tree. **RH is open; no wall is crossed.**

Scope: the six ledgers named in the task, the 55 programme READMEs, `scripts/formal_tools.py research`, and the Lean
statements and docstrings of every declaration quoted below. The corpus is the reference: RHTower 29,309 Lean files
(ThetaCusp 3,980, Sieve 3,084, Deninger 1,643, CCM 1,272, Suzuki 936, Hedenmalm 410), HTGeometry 18,918, and the
arithmetic programmes. No builds, no compilation checks, no axiom audits, no web searches, no external literature.
Research log: [`logs/opus-review-3010-research-2026-10-30.md`](../../../logs/opus-review-3010-research-2026-10-30.md).

| Label | Meaning |
|---|---|
| **[Lean]** | Statement or docstring read in Lean source during this review. Integration not assessed. |
| **[map]** | Taken from the frontier map, a ledger or a programme README. |
| **(inference)** | A conclusion of this review, not a Lean theorem. Each one says what would confirm or refute it. |

Companions: [walls](walls-ledger.md) · [route obstacles](route-obstacles.md) · [unification](route-unification-ledger.md) ·
[frontier map](../rh-current-frontier-map.md) · [killed mechanisms](../rh-killed-routes.md).

---

## 0. Answers in brief

1. **Mechanism against a wall.** The live wall is Σ1, the complete atomic Weil matrix at growing overlap. The corpus
   has turned it into explicit polynomial arithmetic in the overlap c: conductor floor c⁻⁷, defect reserve a/c⁷ against
   cost C c⁹, every negative unit vector with pole defect ≤ C c¹⁶, residual c⁵/log N, and an exponential conductor
   cutoff for defect-only confinement. (inference) Only the explicit Gram error is used below; on that basis
   defect-only confinement closes at best at c ≍ (log log N)^{1/16}. Reaching the tilted-spline RH receiver
   (log N)^{1/4+} needs a pole defect of (4/3) log c + O(1) on negative vectors, the defect of a conductor-c^{4/3} mode.
   The binary escape vectors of the no-go carry constant complete energy, so **energy capture**, not defect capture,
   is the mechanism the corpus leaves open (§2 M1). Three further mechanisms:
   - selection by the pole's single square at growing overlap (M2);
   - a confluent horizontal channel, which three programmes independently name as their missing object (M3);
   - a J² signed saving on integer-power meshes (M4).
2. **Wildly different.** The corpus already runs the usual "wild" frameworks as programmes with exact RH endpoints:
   theta-Hawking scattering, CCM, Suzuki, heat and resolvent Hankel forms, JAS, theta harmonic completeness, Lee–Yang
   and Herglotz, and Deninger's big-Witt Frobenius. A framework is worth running only if it brings an *unconditional
   producer* of criticality, precision or selection. Three corpus objects do (§3):
   - the ThetaCusp square-plus-null-Lagrangian identity;
   - Herglotz carrier rigidity;
   - theta harmonic completeness, which needs no positivity at all.
3. **Quasi-RH beyond 7/8.** The 7/8 claim is external and unvalidated [map]. The corpus states exact targets:
   - the 5/6 strip ⇔ power-mesh covariance (m = 6) ≤ C J^{5+ε};
   - the 3/4 strip ⇔ the same at m = 4, ≤ C J^{3+ε};
   - the positive envelope is ≍ J^{m+1} on both sides and never ≤ C J^m [Lean].

   (inference) On the m-th mesh the strip 1 − 1/m is a signed saving of exactly J² over the absolute envelope. Inside
   the CGL detector, 5/6 needs ν ≤ 1/15 and κ + 4ν ≤ 4/3, and the method floor is 29/36. CGL packets cannot carry
   reflection charge (horizontal-collision no-go). No gauge-invariant certificate beats 3/4 [Lean].
4. **75 % on the line.** The census stands at 0.67250071 [Lean]. At the unconditional bandwidth-one constant κ = 4/3,
   the joint (c = 2, c = 3) rank–trace functional equals exactly (3/4)N. On extremal frames it certifies 3/4 distinct
   critical zeros as soon as off-line pairs do not outnumber double critical zeros [Lean]. 75 % is therefore exactly
   the **coalescence blind spot**: double critical zeros and coalesced off-line pairs share one summed matrix. Breaking
   it needs a zero-side slack of at least (3/4 − H(λ))N, which tends to N/12 (Route I). Route II needs a prime surplus
   ≤ 1/18 at λ = 4/3, while positive majorants give 8/27. The 70 % target needs the shallow-Cauchy Ward budget below
   3N/20; the corpus proves it is O_α(N).
5. **Three questions.**
   - (Σ) Can the negative-vector pole defect C c¹⁶ be brought to log c + O(1), or replaced by energy capture at a
     polynomial conductor cutoff?
   - (Γ) Does the pole carry the unique selective square of the complete matrix at growing overlap?
   - (confluent) Is there an unconditional prime-side bound for a confluent (divided-difference or log-derivative)
     observable at depth ≍ 1/log T with the constants the census and the CGL merger need?
6. **New field.** *Confluent arithmetic index theory*: negative indices and Gram ranks of jet-augmented arithmetic
   forms, which do not drop under coalescence, together with prime-side budgets for those jets. The corpus has proved
   that coalescence is where index, census and the CGL merger all lose information (§7).

---

## 1. The frontier as the Lean corpus states it

### 1.1 Endpoint identities [map]

| Identity | Joins |
|---|---|
| `negIndex_zetaKernel_eq_zero_iff_count`: index of the Weil kernel = 0 ⇔ ψ(x) − x ≤ C√x log²x | Σ = Π |
| `riemannHypothesis_iff_collided_hecke_invariant`, `riemannHypothesis_iff_W_eq_collided` | Γ = Σ |
| Möbius gauge exponent at 0 equals Θ; RH ⇔ the trivial point is typical | Γ = Π |

The walls are one quantity at their endpoints and separate away from them. The frontier therefore sits wherever a
programme has made the separation quantitative. As of today that is Σ1 (§1.2), selection at one square (§1.3),
precision costs (§1.4), and coalescence (§1.5).

### 1.2 Σ1: the complete atomic Weil matrix at growing overlap

Setting: atoms of width w = c/N at horizon N, overlap c, profile φ; `completeWeilMatrix φ c N`; normalized Ramanujan
horizon vectors u_m; completed conductor energy E_m(c). Tilted unit spline unless stated otherwise.

| Statement | Source |
|---|---|
| Positive definite at every fixed c, uniformly on 0 < c ≤ K | [map] |
| **Conductor floor**: E_m(c) ≥ κ·(m/φ(m))·min(1, (m/c)⁷); constant once c ≤ m | [Lean] `tiltedUnitSpline_completedConductorEnergy_ge_conductor_scale`, `…_ge_above_overlap` |
| **Gram error**: \|⟨u_m, u_l⟩ − δ_{ml}\| ≤ (2ml + 1)/log N, explicit in m, l | [Lean] `normalizedRamanujan_gram_error_le` |
| **Residual**: ‖(W − E_m)u_m‖² ≤ K_m (c⁵/log N + c¹⁰(log N/N)²) for 4(e+3)²c² ≤ N; K_m not explicit in m | [Lean] `exists_completeWeil_completedConductor_residual_horizon_bound` (C² profiles), `exists_tiltedUnitSpline_completedConductor_residual_horizon_bound` |
| **Fixed packets**: every fixed distinct conductor family is positive at c = (log N)^α, α < 1/40 | [Lean] `eventually_tiltedWeil_growing_packet_pos` |
| **Gamma reserve**: archimedean form ≥ (κc⁻⁷ log N − bc)(c/N)M Σx²; bc is an archimedean low-frequency Gram-row cost | [Lean] `TheGammaReserveSurvivesGrowingOverlap` |
| **Defect reserve**: (a/c⁷)·poleDefect − C c⁹ Σx² ≤ normalized weilQuad, for N ≥ H c⁸ | [Lean] `exists_tiltedUnitSpline_complete_defect_reserve_polynomial` |
| **Negative vectors**: every unit x with complete energy ≤ 0 has poleDefect ≤ C c¹⁶ | [Lean] `exists_negative_completeWeil_poleDefect_polynomial_bound` |
| **Defect of a conductor mode**: prime energy of unit u_m tends to the adjunction energy γ + log m + (tame different); for m = 2^k it is exactly γ + (k+1) log 2 | [Lean] `tendsto_unitRamanujanHorizonVector_primeEnergy`, `ramanujanAdjunctionEnergy_two_pow`, `ConductorLogLaw` |
| **Defect-only confinement fails below 2^k**: some unit vectors with poleDefect ≤ γ + (k+1) log 2 + log 4 + 5 have arbitrarily small mass on conductors < 2^k | [Lean] `not_eventually_defect_coordinate_capture_below_binary_cutoff` |
| Shell sources: fixed-modulus control with every inverse-log rate; affine shell errors with a uniform harmonic budget (fifth-power overlap cost); active-shell counting makes the affine source linear | [Lean docstrings] `PrimeResidueSourcesHaveQuantitativeLogDecay`, `GrowingShellSourcesHaveLogarithmicRates`, `AffineShellErrorsHaveAUniformHarmonicBudget`, `CountingActiveShellsMakesTheAffineSourceLinear` |
| **RH receivers**: RH ⇔ eventual nonnegativity for C² profiles when c⁴/log N → ∞, so for the tilted spline at 2(log N)^α with α > 1/4. Smooth profiles reach (log N)^ε, Gevrey profiles (log log N)^s, and one Steklov profile L(log L)² log log L with L = log log N | [Lean] `riemannHypothesis_iff_completeWeilEnergy_nonneg_of_growthTwo`, `OverlapGrowthTwo`, `OverlapGrowthPow`, `OverlapGrowthGevrey`, `TheFixedProfileReachesAnIteratedLogEndpoint` |
| **Pole**: RH ⇔ the Markov form is nonnegative on the pole hyperplane at every root. Unconditionally the Markov form has a negative square at overlap (log N)^ε | [Lean] `ThePoleAtEveryRoot`, `exists_markovQuad_neg` in `ThePoleIsTheOnlyNegativeSquareBeyondTheThreshold` |

**Reading (inference).**

1. *Packets reach α < 1/19.* The packet theorem compares c⁷⟨W u_i, u_j⟩ with c⁷E_i δ_{ij}. The residual enters
   as c⁷ (c⁵/log N)^{1/2} = c^{19/2}(log N)^{−1/2}, and the Gram term as c⁷E_i/log N with c⁷E_i bounded at fixed m.
   Both vanish for α < 1/19. To confirm, rerun the packet argument of `WeilGrowingPackets` with the horizon-decay
   residual.
2. *Break-even of defect-only confinement.* Take a packet of all conductors up to Q and use the explicit Gram error
   in a Gershgorin bound. The off-diagonal mass of row m, relative to its diagonal, is ≲ mQ²/log N, so the packet
   needs Q³ ≪ log N. The binary no-go forces Q ≳ e^{D − O(1)} for a defect threshold D. With D = C c¹⁶ this gives
   c ≪ (log log N)^{1/16}: below the Steklov receiver, and far below the tilted-spline receiver (log N)^{1/4+}. At
   that receiver Q ≲ c^{4/3}, so a defect route needs **negative vectors with poleDefect ≤ (4/3) log c + O(1)**. That
   is the defect of a single conductor mode u_m with m ≤ c^{4/3}. The distance from C c¹⁶ to (4/3) log c is the
   Σ1 gap in defect units. A better off-diagonal bound than Gershgorin moves the 4/3 but not the conclusion.
3. *The escape vectors are not dangerous.* The vectors that defeat defect-only capture are conductor modes u_{2^k}.
   Their complete energy is E_{2^k}(c), which is bounded below by a constant once 2^k ≥ c. Defect is the wrong
   capture functional. The complete energy itself confines low energy to conductors ≲ c, provided the off-diagonal
   coupling between conductors is controlled uniformly in m. That uniformity, explicit K_m and an off-diagonal bound
   at Q ≍ c, is the missing estimate (§2 M1).

Elliptic localization is quantified exactly [Lean: `elliptic_sector_nonneg_below_conductor_horizon`,
`conductor_forcing_disjoint`]. Twisted positivity holds up to (4+ε)e^a + C ≤ log(1 + |γ|/8), with the sharp
constant 4. Forcing needs 768A log(|γ|+3) < e^{2δa}. The two conditions are disjoint for δ ≤ 1/2, so the elliptic
route cannot produce even a zero-free region at its horizon.

### 1.3 Γ: selection has shrunk to one square

| Statement | Source |
|---|---|
| κ(K_ζ) = number of distinct right zeros, and κ is even; RH ⇔ κ ≤ 1 | [map] HKT |
| Sign gauges act by congruence at atomic resolution, so every twin shares ζ's index ladder | [Lean] `hermNegIndex_gaugeAtom_eq` |
| One linear condition costs at most one square; the pole indices of two sign gauges differ by at most one, at every horizon and counterterm | [Lean] `hermNegIndex_le_negIndexOn_ker_add_one`, `poleNegIndex_gauge_le_add_one` |
| In the window L − 2 log 2 < D < L, L = log N − γ: pole index of ζ is 0, of the Liouville twin 1 | [Lean] `eventually_poleNegIndex_window` |
| Off the line a pair has one negative square for every depth t ≠ 0 and converges to an on-line point with none | [Lean] `coalescence_law` |
| No gauge-invariant bound on the Möbius exponent is below 3/4, at any point | [Lean] `threeQuarters_le_of_gaugeInvariant_bound` |
| Pure-point positive-definite kernels have Toeplitz energy ≤ εL on modulated blocks at most frequencies; absolutely continuous spectrum gives ≍ L | [Lean] `exists_frequency_thin` |
| Pointwise-closed shift-invariant statements are twin-blind; the trivial point is never better than typical; short shells (c ≤ 2) have no conductor | [map] AKLT, AGT |
| Deninger: a canonical big-Witt Frobenius ring endomorphism exists. Conformally scaled positive seminorms are compatible with off-line eigencharacters, so conformal Hodge positivity does not constrain the spectrum. Multiplicative submass, pairwise cyclic correction, cross-prime singular graph lifts, integral carrier lattices and bounded carrier spectra are each refuted | [Lean docstrings] `DeningerResolventCoreIsRiemannHypothesis`, `DeningerBigWittFrobeniusMultiplicativeSubmassNoGo`, `…PairwiseCyclicCorrectionNoGo`, `…CrossPrimeSingularGraphLiftNoGo`, `…CarrierNoIntegralLattice`, `…CompleteCarrierSpectrumBounded` |

**Reading (inference).** At atomic resolution the entire selective content of negative-index counting is one square,
and it is the pole's. Σ1 measures negative vectors by `poleDefect`. Γ selects by whether the pole carries the square.
Both frontiers are statements about the pole direction of the same quadratic form. A theorem identifying the complete
matrix's negative vectors with the pole's square at growing overlap would merge them (§2 M2).

### 1.4 Π: what precision costs

| Statement | Source |
|---|---|
| Full order-r mixed multiplicity on the q-torsion grid forces support ≥ 2^{qr}, attained by (X^q − 1)^r | [Lean] `AdamsMultiplicityResolution`, `TorsionArithmeticResolution` |
| Euler operators (valuation derivations) lower multiplicity by one; vertical cancellation does not give torus multiplicity; algebraic first vertical jets are faithful (Baker); two-prime homogeneous log rigidity | [Lean docstrings] `EulerOperatorsLowerMultiplicity`, `VerticalJetsMissTransverseDirections`, `AlgebraicVerticalFirstJets`, `TwoPrimeHomogeneousLogRigidity` |
| Periodic producers pay 2 log 2 per unit mass; integrality is Chebyshev-precise; a ceiling at precision θ < 1 is a zero-free strip | [map] AGT, ASRP |
| RH ⇔ the real-zero jets of the theta measure are dense in L¹_even(μ). An off-line zero α yields an explicit bounded even annihilator g, with k·g having transform F(z) z²/((1 − z²/α²)(1 − z²/ᾱ²))^m | [Lean] `ThetaEndpointHarmonicCompleteness`, `exists_offLine_annihilator` |
| Transcendence stack: Baker, Matveev, Gelfond–Schneider, six exponentials, stage-two Schanuel defect geometry | [Lean module headers] `RHTower/BakerGeneralProof`, `Matveev`, `GelfondSchneiderProof`, `SixExponentials`, `Schanuel` |

**Reading (inference).** Over ℤ every flatness-type producer the corpus has built pays an exact exponential: 2^{qr}
support for multiplicity r on a q-torsion grid, and 2 log 2 per unit mass for periodic valuations. Producing Π by
vanishing is therefore priced. Π enters the corpus's quasi-RH work only through signed savings (§4).

### 1.5 Where programmes converge: coalescence

Four programmes, each in its own language, name one missing object:

| Programme | What it proves | What it says is missing |
|---|---|---|
| Census (ACS) | Double critical zeros and coalesced off-line pairs share the summed matrix `extremalDiag`; the on-line Parseval identity and the off-line negative-part credit separate them only through the unsplit zero-side decomposition | a zero-side slack ≥ (3/4 − H(λ))N [Lean] |
| CGL | Reflection preserves ordinates, so fibre-separated packets cannot carry two reflected points; the Prop 4.6 envelope has source floor 288 against the collision quantum 2 | "a confluent horizontal channel (for example a reflection divided difference or logarithmic derivative)" [Lean] `ChenGuptaLiHorizontalCollisionNoGo` |
| ShallowCauchy | (α/log T)E_{α/log T} + R_deep = O_α(N(T,2T)) unconditionally; Σ m_j² ≤ C T log T for shallow off-line zeros | the constant: 70 % needs ≤ 3N/20 [Lean docstrings] |
| HKT / AKLT | Coalescence law; a finite index drops only through coalescence | an index that does not drop [Lean], [map] |

Heat flow supplies depth-resolved geometry. An unheated zero has a heat zero within distance d when t log X ≤ c d²,
and deep dyadic families are counted by log X times nonreal heat zeros under the same condition [Lean docstrings:
`HeatZeroDisplacement`, `HeatUniformDepthZeroDensity`].

(inference) Coalescence is the single place where census, quasi-RH packets and index all lose the information that
separates an off-line pair from a double critical zero. This is the strongest convergence in the corpus that does not
pass through Σ1.

---

## 2. Q1: mechanisms that circumvent or destroy a wall

### M1. Energy capture at a polynomial conductor cutoff (Σ1)

- **Target.** Close the defect route's gap between C c¹⁶ and (4/3) log c (§1.2 reading 2) without improving the
  defect bound. Confine negative vectors by complete energy instead.
- **Mechanism.** Conductor modes above the overlap carry constant energy (conductor floor). The binary escape vectors
  are such modes. Energy capture asks for a lower bound on the complete form on the orthogonal complement of
  span{u_m : m ≤ Q}, with Q a power of c, plus packet positivity on that span.
- **Steps.**
  1. Make K_m explicit, K_m ≤ K m^B. The m-dependence enters through `exists_primeResidual_norm_sq_log_bound` in
     `CompleteConductorResidualsRetainTheirHorizonDecay`.
  2. Packets of all conductors m ≤ Q = c^A at α > 0. This uses the explicit Gram error together with step 1.
  3. Complement coercivity: complete energy ≥ η(c)·mass on span{u_m : m ≤ Q}^⊥. The defect reserve already gives
     this off the vectors of small defect, so the remaining case is unit vectors with defect ≤ C c¹⁶ that are
     orthogonal to the low conductors.
- **Why no corpus no-go covers it.** `not_eventually_defect_coordinate_capture_below_binary_cutoff` concerns
  certificates that see only the defect. Its escape vectors have energy bounded below.
- **Risk.** Step 3 is where RH content can sit. The complement contains non-Ramanujan directions, and nothing in the
  corpus says they are spanned by conductor modes at growing overlap. A counterexample shape would be a unit vector
  with defect ≲ c¹⁶, orthogonal to conductors ≤ c^A, and complete energy o(c⁻⁷).

### M2. Selection by the pole's square at growing overlap (Γ, Σ)

- **Facts [Lean].**
  - Pole indices of sign gauges differ by at most one.
  - In the atomic window, ζ has pole index 0 and the Liouville twin 1.
  - At overlap (log N)^ε the Markov form has an unconditional negative square, and RH ⇔ the pole hyperplane carries
    none.
- **Mechanism.** Selection is the location of one square. Transport the window theorem
  `eventually_poleNegIndex_window` from the atomic kernel to `completeWeilMatrix` at fixed c ≤ K, then along growing
  c. At each stage the statement is "ζ's pole index of the complete form is 0 on a counterterm window".
- **Why it escapes twin-blindness.** The pole-index rigidity theorem says a twin differs by at most one square. The
  claim concerns which side of that one square ζ lies on, which is not a pointwise-closed property of the weights.
- **First theorem.** The complete-matrix pole-index window at fixed overlap, with the Liouville twin at index 1.
- **Risk.** The window width 2 log 2 is attained by flips p ≥ 11 [map: ACountP]. Growing overlap may close the window
  before the RH receiver.

### M3. A confluent horizontal channel (census, quasi-RH, index)

- **Target.** The object named in §1.5: a row or observable at the reflected pair (ρ, 1 − ρ̄) that is a divided
  difference or logarithmic derivative. It must separate a coalesced off-line pair from a double critical zero.
- **Corpus inputs.**
  - The divided-difference calculus of CCM: `ccmReflectionMatrix_commutes_dividedDifference`.
  - Suzuki's confluent Herglotz carrier: `suzukiXiCarrierHerglotzConfluentDividedDifference`.
  - ShallowCauchy's unconditional shallow energy.
  - The on-line Parseval identity and the off-line negative-part credit of ACS.
- **First theorem.** A confluent rank–trace functional, meaning (c = 2, c = 3) plus one divided-difference row, that
  takes different values on `doubleZeroBlockData` and `coalescedPairBlockData` from the summed matrix and one
  prime-side quantity, instead of the unsplit (P, Q).
- **Consumers.**
  - Census Route I: slack ≥ (3/4 − H(λ))N.
  - 70 %: the shallow-Cauchy budget ≤ 3N/20.
  - The CGL merger: reflection charge, quantum 2.
  - Finite index: no drop at coalescence.
- **Risk.** The prime-side dual of a horizontal jet carries log-weighted prime sums, whose budgets are the open
  constants.

### M4. A J² signed saving on integer-power meshes (Π, quasi-RH)

- **Facts [Lean].**
  - On the m-th power mesh the cumulative square exponent is 1 + 2m(Θ − 1/2).
  - 5/6 ⇔ `mobiusDivisorDilationPowerMeshCovariance 6 J ≤ C J^{5+ε}`; 3/4 ⇔ the same at m = 4 with exponent 3 + ε.
  - The paid diagonal costs ≤ 9/25 per scale.
  - The off-diagonal is the literal ordered pair sum with both Möbius signs, over the small-quotient range q < j,
    via the identity (j^m − 1)/(j^{m−1} + 1) = j − 1.
  - The positive envelope is ≍ J^{m+1} on both sides and never ≤ C J^m.
- **Reading (inference).** The envelope J^{m+1} is the trivial abscissa Θ = 1. The strip Θ needs a signed saving of
  J^{2m(1−Θ)}, which equals J² exactly at m = 1/(1 − Θ). Every strip 1 − 1/m is the same problem, a J² saving on its
  own mesh. m = 5 (strip 4/5 < 29/36) is the first mesh below the CGL detector's floor.
- **Corpus tools on this saving.**
  - Shifted sextic correlations have m-th-power degeneracy only on matching shift multisets, leaving 2H² − H
    exceptional quadruples (`QuasiRHShiftCorrelation`).
  - Complete-field character correlations retain the negative square of the coefficient sum
    (`QuasiRHCharacterCorrelation`).

  Transferring these to the Möbius covariance is open.
- **Risk.** The quotient range q < j carries the full Möbius randomness; a saving there is quasi-RH strength by
  construction.

---

## 3. Q2: wildly different approaches

The usual candidates are corpus programmes with exact RH endpoints:

| Framework | Endpoint or unconditional content | Source |
|---|---|---|
| Theta-Hawking scattering (ThetaCusp) | RH ⇔ real backreaction resonances, ⇔ all-pass winding rigidity, ⇔ mirror clock mixing, and further endpoints | [Lean] `riemannHypothesis_iff_thetaCuspHawkingBackreactionResonances_real`, `…AllPassWindingRigid` |
| Heat / resolvent Hankel | RH ⇔ heatHankel a P P ≥ 0 for all P; RH ⇔ resolvent Hankel forms nonnegative | [Lean] `riemannHypothesis_iff_heatHankel_nonneg`, `riemannHypothesis_iff_forall_xiResolventHankelForm_re_nonneg` |
| JAS | Positive at dressing 2 unconditionally; RH ⇔ JasDressedPSD 1 ∧ quasi-RH; under quasi-RH the abscissa is in {0} ∪ [½ + Θ, 2] | [Lean] `jasDressedPSD_two`, `riemannHypothesis_iff_jasDressedPSD_one_and_quasi`, `JointAncestryQuasiRHChainExclusion` |
| Deninger big-Witt | Canonical Frobenius exists; conformal positivity does not constrain the spectrum | [Lean docstrings] §1.3 |
| Lee–Yang / Herglotz | Stable self-reciprocal Dirichlet polynomials have critical zeros off ζ's zero set | [Lean] `exists_zero_stableDirichlet_riemannZeta_ne_zero` |
| Theta harmonic completeness | RH ⇔ density of real-zero jets in L¹_even(μ) | [Lean] `ThetaEndpointHarmonicCompleteness` |

An endpoint is not a producer. Of these frameworks, three carry unconditional mechanisms that no estimate-based route
has. Each is a candidate for an approach that does not pass through the walls.

### W1. Identity-level positivity: the null Lagrangian of the theta fibre form

At every center y the native signed fibre form of every finite section is a square plus an exact derivative:
Σ v_i v_j h_{i+j}(y) = |G_v(y)|² + B_v'(y) [Lean `ThetaCuspCenterTailSquareFlux`]. The tail form at x = r/2 is
2∫_{y>x} |G_v|² − 2B_v(x). At the seam the flux vanishes and this is the Plancherel Gram law. Size eight is proved at
every aperture 0 < a < 1/2 by exact piece certificates and an LDLᵀ factorization below r_c = log(5/π)
[Lean `ThetaCuspOddFourRankEight`].

(inference) Positivity of a signed section is a statement about one boundary flux B_v(r/2), a finite combination of
Φ^{(a)}Φ^{(b)} at a point. Rank-by-rank certificates do not scale. The uniform statement to aim for is a flux bound by
the bulk, or a calibration: a choice of center at which the flux has a sign for every v. This is the only object in
the corpus whose positivity is an identity with an explicit defect, which is the unification ledger's requirement
for Σ.

### W2. Selection by Herglotz carriers

Expand H = Σ_j log n_j (½ − z_j∂_jQ/Q) at z_j = n_j^{½−s}. Stability gives Re H ≥ 0 on Re s > ½. Self-reciprocity
makes Re H = 0 on the critical line away from the zeros of P. Carrier rigidity
(`eq_zero_of_herglotz_dirichlet_criticalCarrier`) then forbids the critical zero set from lying inside ζ's
[Lean `StableDirichletPolynomialPutnam`]. The corpus also has ζ/(2√6 Y_a) as an absolutely convergent Dirichlet series
for the two-prime Lee–Yang family [Lean `ZetaZerosLeeYangDirichletSeries`].

(inference) Carrier rigidity is an unconditional selection principle stated through positivity of a real part, not
through pointwise-closed weight conditions. The wild route uses it as Γ's producer: a Herglotz function built from
Euler data whose critical carrier is forced to be ζ's divisor. Risk: Euler factors are stable but not
self-reciprocal, and the functional equation supplies reciprocity only after completion.

### W3. RH without positivity: harmonic completeness

RH is a density statement for the real-zero jets in L¹_even of the theta measure, and its failure is witnessed by an
explicit bounded annihilator [Lean]. (inference) This is the only RH form in the corpus with no sign, no count and no
selection step. A proof is a uniqueness theorem for dominated sources: no real even s with |s| ≤ Ck has transform
F(z) z²/((1 − z²/α²)(1 − z²/ᾱ²))^m for a non-real α. Under RH, the converse step uses only relative-source rigidity,
which is unconditional. The open half concerns domination after dividing out one complex zero pair.

**Not recommended.** More RH endpoints of the theta-Hawking type. They multiply reformulations without producing any
of the three properties.

---

## 4. Q3: Quasi-RH beyond 7/8

### 4.1 Status

- No strip is proved [map]. The 7/8 statement is an external manuscript claim [map: [E]].
- The CGL modules formalize Guth–Maynard extended to characters: Theorem 1.1, the cubic trace Lemma 4.5,
  Proposition 4.6, and the principal Guth–Maynard form of Lemma 6.2 [Lean module headers].
- **JAS reduction [Lean].** RH ⇔ JasDressedPSD 1 ∧ quasi-RH. Under quasi-RH, off-line chains are impossible below
  σ = ½ + Θ, and the abscissa law is bimodal.
- **Lindelöf reduction [Lean].** Under LH, quasi-RH ⇔ cos(hD)Ξ is real-rooted for some h < ½. The forward direction
  is unconditional.

### 4.2 Exact targets

| Target | Equivalent statement | Source |
|---|---|---|
| 5/6 strip | power-mesh covariance (m = 6) ≤ C J^{5+ε}; normalized Chebyshev Cesàro mean-square energy subpower | [Lean] `xi_zero_five_sixths_strip_iff_powerMeshCovariance_subpower`, `five_sixths_strip_iff_chebyshevNormalizedCesaroMeanSquareEnergy_subpower`, `xi_zero_five_sixths_strip_iff_dilationCovariance_subpower` |
| 3/4 strip | power-mesh covariance (m = 4) ≤ C J^{3+ε} | [Lean] `xi_zero_three_quarters_strip_iff_powerMeshCovariance_subpower` |
| Any strip by absolute values | impossible: positive envelope ≍ J^{m+1} on both sides, never ≤ C J^m | [Lean] `exists_mobiusDivisorDilationPositiveMeshEnergy_two_sided`, `not_mobiusDivisorDilationPositiveMeshEnergy_le_pow` |
| Any strip by multiplicative data | impossible below 3/4 | [Lean] `threeQuarters_le_of_gaugeInvariant_bound` |
| BVI seven-way TFAE; cyclotomic remainder O(N^{5/3+ε}) ⇔ 5/6, O(N^{3/2+ε}) ⇔ 3/4 | — | [map] |

### 4.3 The CGL detector's exponent algebra [Lean]

The boundary is 5/6 + (x − slots)/6 + max(0, ν(1 − slots − 2x), (κ − 1)(1 − slots) − (2κ − 1)x)/2
+ reflectedLoss/2, with Gram profile 1 + P^ν + P^κ/Y. Published parameters (17/48, 1/6, 1/6, 2) give 7/8.

| Change | Best boundary | Lean |
|---|---|---|
| Gram power saving s | 7/8 − s/16 | `gram_power_saving_boundary` |
| ν → 0, κ = 2 | 23/27 at x = 5/18 | `ordinaryGramBoundary_sharp_minimum` |
| 5/6 | ⇔ ν ≤ 1/15 ∧ κ + 4ν ≤ 4/3 | `gramProfile_five_sixths_feasible_iff` |
| Both nonunit terms removed | 29/36 | `unitGramBoundary_sharp_minimum` |
| 3/4 | never | `gramProfileBoundary_gt_three_quarters` |

The detector cannot carry horizontal reflection charge. Its Prop 4.6 envelope sits at 288 against the collision
quantum 2 before any S₁, S₂, S₃ estimate [Lean `cglProposition46_rhs_ge_288`, `cglProposition46_rhs_not_lt_two`].

### 4.4 Recommendation (inference)

1. Treat the power-mesh J² saving (M4) as the detector-independent target. The meshes m = 5 (4/5) and m = 4 (3/4)
   lie below the detector's floor 29/36.
2. Inside the detector, the 5/6 condition κ + 4ν ≤ 4/3 is a statement about the large-values term of the packet Gram,
   which the formalized Guth–Maynard layer bounds. State which CGL lemma fixes κ = 2 before choosing a lever.
3. Any merger of CGL with the reflection structure must add M3's confluent channel first; the no-go rules out
   finishing S₂/S₃ as a route.
4. Run the CGL dependency audit, since the chain is [E].

---

## 5. Q4: at least 75 % of zeros on the line

### 5.1 Status [Lean]

- Simple critical proportion ≥ 0.67250071 − ε (`simple_critical_proportion_ge_67250071`).
- At least 4/5 − ε of ordinates carry a critical zero (`Zeta23CriticalOrdinateCensus`).
- 70 % dichotomy: failure forces ≈ 0.2725N simple off-line zeros within A/log T of the line
  (`Zeta23SeventyPercentOrSimpleNearLine`).
- Pinching: disjoint simple pairs yield an exact quadratic overlap gain 2⟨v_x, v_y⟩² by rotation (`DisjointPairSchurSlack`).
  The cosine kernel has a non-lattice floor 1/250 outside two intervals, so every span-3 triple has a pair with
  |K| ≥ 1/250 (`CosineKernelNonLatticeFloor`).

### 5.2 The exact form of 3/4 [Lean `BreakingTheCoalescenceBlindSpotAndThreeQuarters`]

- At κ = 4/3, the unconditional bandwidth-one constant, jointRankTrace23 = (14 tr Â − 3‖Â‖_F² − 7N)/4 = (3/4)N
  (`jointRankTrace23_at_four_thirds`).
- On extremal frames it equals s₁ + (d₂ + p)/2. Hence 3/4 distinct critical zeros follow if p ≤ d₂, and 3/4 with
  multiplicity if p ≤ 3d₂ (`three_quarters_of_broken_blind_spot_at_four_thirds`).
- Double-zero and coalesced-pair frames share `extremalDiag`. The on-line Parseval identity gives onSlack = d₂ on
  double-zero frames, i.e. (5/6)N certified there. The negative-part credit 2 tr(Q₋) is positive iff Q is not PSD.
- **Route I** (`zeta_three_quarters_of_spectralSlack`): (3/4 − ε)N ≤ N₀* whenever the zero-side spectral slack is at
  least (3/4 − H(λ))N, which tends to N/12 as λ → 1, half the N/6 slack of double-zero frames.
- **Route II** (`kappa_five_fourths_iff_three_quarters`, `zeta_three_quarters_from_prime_surplus`): 3/4 ⇔ κ ≤ 5/4. At
  λ = 4/3 the diagonal, archimedean and pole constant is 43/36 = 5/4 − 1/18, and the prime–pole cross term is
  O(T^{5/6} log²T). The prime surplus must be ≤ 1/18. Its Hardy–Littlewood value is −1/144; positive majorants give
  8/27 [map].
- **Mollifier** (`ZetaCGGMollifierOptimum`): 3/4 ⇔ (1+θ)³ ≥ 4 for a simple-zero ratio with conditional main terms. This
  is not a critical-line census.

### 5.3 Reading (inference)

The census is complete at the level of finite matrices. 75 % is exactly the coalescence blind spot: an off-line pair
that coalesces is Gram-equivalent to a double critical zero (coalescence law), and the summed matrix cannot tell
them apart. Both routes are prime-side inputs:

- Route II needs a pair-correlation-type surplus at λ = 4/3.
- Route I needs a zero-side slack. Its natural carrier is M3's confluent row, because the slack it asks for, N/12,
  is half of what double-zero frames carry by the Parseval identity.

The 70 % step is the same object at lower cost. The shallow-Cauchy Ward budget is a log-derivative energy at depth
α/log T. It is proved O_α(N); 70 % needs ≤ 3N/20.

---

## 6. Q5: three questions to focus on

### Question 1 (Σ): confine negative vectors at a polynomial conductor cutoff

Every negative unit vector of the complete tilted-spline form has poleDefect ≤ C c¹⁶. Can this be improved to
log c + O(1)? Or can confinement be done by complete energy, with explicit K_m and complement coercivity on
span{u_m : m ≤ c^A}^⊥?

- **Why.** With the explicit Gram error and the binary no-go, the defect route closes at best at
  c ≍ (log log N)^{1/16}. The tilted-spline receiver needs (log N)^{1/4+} (§1.2).
- **Success test.** Positivity of the complete form at c = (log N)^α for some fixed α > 0, beyond fixed packets.
- **Failure shape.** A unit vector of defect ≲ c¹⁶, orthogonal to conductors ≤ c^A, with complete energy o(c⁻⁷).

### Question 2 (Γ): the pole's square at growing overlap

Is ζ's pole index of `completeWeilMatrix` equal to 0 on a counterterm window at fixed overlap, and does that window
survive along growing c up to an RH receiver?

- **Why.** Selective content is one square at every horizon (`poleNegIndex_gauge_le_add_one`). RH ⇔ the pole
  hyperplane carries no negative square at every root, and a negative square exists unconditionally at (log N)^ε.
- **Success test.** The window theorem for the complete matrix, with the Liouville twin at index 1.

### Question 3 (coalescence): a confluent observable with prime-side constants

Is there a divided-difference or log-derivative observable at (ρ, 1 − ρ̄) whose prime-side bound is unconditional,
with constants at least as good as the following?

- shallow-Cauchy Ward budget ≤ 3N/20 (70 %);
- zero-side slack ≥ N/12 (75 %, Route I);
- carrying horizontal reflection charge below the quantum 2 (CGL merger).

- **Why.** Four programmes name it (§1.5), and it is the only open object shared by census, quasi-RH and index.
- **Success test.** A functional separating `doubleZeroBlockData` from `coalescedPairBlockData` using ζ-specific
  input.

**Runner-up.** The J² signed saving for the m = 4 power-mesh covariance (M4), i.e. the 3/4 strip.

---

## 7. Q6: the new field. Confluent arithmetic index theory

### 7.1 The problem the field answers

Every index, rank and Gram invariant the corpus uses is lower semicontinuous in the wrong direction at coalescence.
An off-line pair has one negative square at every depth t ≠ 0 and none in the limit (coalescence law). Double
critical zeros and coalesced pairs share one summed matrix (census). Reflection collapses two packet rows to one
(CGL). A finite index drops only through coalescence [map]. The field studies invariants of arithmetic quadratic forms
that are **continuous through coalescence**, together with the prime-side budgets that bound them.

### 7.2 Objects

1. **Confluent frames.** Evaluation frames augmented by divided differences at reflected pairs (ρ, 1 − ρ̄) and at
   coincident ordinates. Corpus anchors: `ccmReflectionMatrix_commutes_dividedDifference`,
   `suzukiXiCarrierHerglotzConfluentDividedDifference`.
2. **Jet indices.** The negative index of a form restricted to confluent frames. For a pair at depth t, the jet
   records the square that the plain index loses as t → 0.
3. **Confluent Gram matrices.** The ACS zero-side decomposition (P, Q) with a jet block, so that onSlack and the
   negative-part credit become functions of the summed matrix and the jet block.
4. **Prime-side duals.** Log-weighted prime sums dual to horizontal jets, with the shallow-Cauchy energy as the first
   computed instance.
5. **Depth geometry.** Heat displacement at t log X ≤ c d² as the transport that moves a zero to depth d.

### 7.3 Principles

1. **No information lost at coincidence.** Every invariant is continuous along coalescing families, and its value at
   a double critical zero differs from its value at a coalesced pair.
2. **One square at a time.** Selection is located on single squares, as in the pole-index rigidity theorem, never on
   counts.
3. **Budgets in units of N(T, 2T).** Every prime-side bound is stated as a constant times the zero count, so that
   3N/20, N/12 and the quantum 2 are directly comparable.
4. **Calibration.** Over 𝔽_q, multiple zeros of the Frobenius characteristic polynomial and the Hodge index are
   compatible; the theory must reproduce that compatibility.

### 7.4 Acceptance criteria

1. Separates `doubleZeroBlockData` from `coalescedPairBlockData`.
2. Recovers the census at 0.67250071 and the onSlack identity as special cases.
3. Supplies the reflection charge the CGL no-go asks for.
4. Gives an index that does not drop at coalescence, and agrees with the HKT pole index away from coincidences.
5. Unconditional Lean statements with every input discharged.

### 7.5 First theorems

1. The confluent rank–trace functional on abstract frames, with its value on both coalescence frames.
2. The jet index of the HKT coalescence family, constant in t including t = 0.
3. A prime-side bound for one confluent observable at depth α/log T with an explicit constant, to compare with 3/20.

### 7.6 Relation to the corpus

The Σ1 tools are being built in CACT, CAF and RAPT: conductor floors, residuals and defect reserves. The field does
not replace them. Its chapters exist in ACS (census frames), HKT (pole index, coalescence law), ShallowCauchy (shallow
energy), CGL (packets), Heat (displacement), and CCM/Suzuki (divided differences). What it adds is the invariant that
these programmes lack in common: a jet index, continuous through coalescence, with prime-side budgets.

---

## 8. Evidence

**Documents read in full:** `docs/reports/rh-current-frontier-map.md`, `docs/reports/rh-killed-routes.md`,
`docs/reports/review-3010/route-unification-ledger.md`, `route-obstacles.md`, `walls-ledger.md`,
`docs/reports/research-programmes.md`, and the 55 programme READMEs it lists.

**Lean source read** (statements and docstrings), by area:

- **Σ1:**
  - `CompletedArithmeticForms/WeilGrowingPackets`, `WeilGrowingOverlap`, `ConductorLogLaw`
  - `CriticalArithmeticCorrelationTheory/CompleteConductorResidualsRetainTheirHorizonDecay`,
    `TheCompleteWeilReserveHasPolynomialOverlapCost`, `ConductorScaleControlsTheCompletedEnergy`,
    `ConductorOverlapDecay`, `ExactSuccessorShellWindows`, `AffineShellErrorsHaveAUniformHarmonicBudget`,
    `CountingActiveShellsMakesTheAffineSourceLinear`, `UpwardPrimeErrorsRetainTheirHorizonDecay`
  - `RenormalizedArithmeticPotentialTheory/PrimeDefectConfinementMustRetainLowEnergyConductors`,
    `LogarithmicOverlapOfTheCompleteWeilMatrixIsTheRiemannHypothesis`, `TheGammaReserveSurvivesGrowingOverlap`, the
    residue and shell source modules
  - `SpacingScaleHarmonicAnalysis/TheCriticalExponent`, `TheSecondOrderSynthesis`, `TheOverlapLawAtEveryRoot`,
    `TheGevreyWindow`, `TheFixedProfileReachesAnIteratedLogEndpoint`, `GrowingOverlapHasNoUniformGramFloor`,
    `ThePoleAtEveryRoot`, `ThePoleIsTheOnlyNegativeSquareBeyondTheThreshold`
  - `ArithmeticPolarization/ThePriceOfEllipticLocalization`, `ConjugateDiagonalGeometry/TheConductorForcingGap`
- **Γ:**
  - `HeckeKreinToeplitz/TheSelectiveIndexOfTheAtomicKernelIsOneSquare`, `APurePointSpectrumIsThinAtMostFrequencies`,
    `TheIndexUnderRotationDampingAndCoalescence`
  - `ArithmeticGaugeTheory/TheExponentIsNotGaugeInvariant`, `TheShortShellsHaveNoConductor`,
    `TheShellsHaveLevelOfDistributionOneHalf`
  - Deninger big-Witt and no-go modules
- **Π:** all of `ArithmeticHarmonicAnalysis/`, `RHTower/ThetaEndpointHarmonicCompleteness`, Schanuel module headers.
- **Quasi-RH:**
  - `RHTower/QuasiRHDetectorScaleBudget`, `QuasiRHDetectorGramTradeoff`, `QuasiRHPowerMeshMeanSquareAbscissa`,
    `QuasiRHHighDilationPositiveEnvelope`, `QuasiRHDilationCovarianceAbscissa`, `QuasiRHQuotientHeadBoundary`,
    `QuasiRHPowerMeshSquareSampleAndObserverJetAbscissaLaw`, `QuasiRHShiftCorrelation`, `QuasiRHCharacterCorrelation`
  - `JointAncestryQuasiRHChainExclusion`, `JointAncestryQuasiRHAmplification`, `JointAncestryQuasiRHCore`,
    `LindelofQuasiRHCosineThreshold`
  - CGL: `ChenGuptaLiHorizontalCollisionNoGo`, `…Lemma62PrincipalGuthMaynardForm`, `…Lemma45`, `…Proposition46`,
    `…Proposition51`, `…CharacterLargeValues`, `…FiniteZeroDetector`, `…ZeroDensityExponents`,
    `…ModulusCrossover`, `…PositiveWindowZeroDensity`
- **Census:**
  - `RHTower/Zeta23CriticalOrdinateCensus`, `Zeta23SeventyPercentOrSimpleNearLine`, `ZetaCGGMollifierOptimum`,
    `LevinsonLinearOptimization`
  - `ArithmeticCastelnuovoSeveri/BreakingTheCoalescenceBlindSpotAndThreeQuarters`
  - `IncommensurableGaborPinching/DisjointPairSchurSlack`, `CosineKernelNonLatticeFloor`
  - `ShallowCauchyPrimeEnergy/ShallowCauchyImplications`, `ShallowCauchyEnergyBound`
  - the displacement and spectral-slack modules
- **Heat and theta:**
  - `RHTower/Heat/HeatZeroDisplacement`, `HeatUniformDepthZeroDensity`, `HeatMeanFieldZeroDensity`,
    `HeatZeroFreeWindow`, `HeatExteriorForce`
  - `RHTower/ThetaCusp/ThetaCuspCenterTailSquareFlux`, `ThetaCuspOddFourRankEight`
  - `RHTower/StableDirichletPolynomialPutnam`, `ZetaZerosLeeYangDirichletSeries`

**Corpus searches** (`scripts/formal_tools.py research`):

- in words: growing overlap and defect confinement; power-mesh covariance strips; confluent divided differences at
  reflected zeros; signed Hankel sections and RH; theta-radical annihilators; Lee–Yang and Herglotz carriers; census
  routes to 3/4; quasi-RH detector levers;
- lexical: `JasDressedPSD`, `jointRankTrace23_at_four_thirds`, `threeQuarters_le_of_gaugeInvariant_bound`,
  `coalescence_law`.
