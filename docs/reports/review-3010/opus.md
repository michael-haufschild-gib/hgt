# Opus review 3010: the Lean frontier and where it points

Status: 30 October 2026, corpus `632f87ee3c` plus working tree. **RH is open; no wall is crossed.**

Scope:

- Sources: the six ledgers named in the task, the 55 programme READMEs, `scripts/formal_tools.py research`, the Lean
  statements, docstrings and proofs quoted below, and one live pipeline card
  (`1-in-progress/quasi-rh-from-effective-conductor-confinement.md`).
- Corpus size: RHTower 29,309 Lean files, HTGeometry 18,918, plus the arithmetic programmes.
- New Lean: one module, `RHTower/HolomorphicCarriersCannotBeQuantized.lean`, checked with `lake --old env lean`
  (standard axioms only). Its cards are `3-formalized/holomorphic-carriers-cannot-be-quantized.md` and
  `5-failed/hc-quantization-as-producer.md`.
- Not done: no builds or axiom audits of other modules, no web searches, no external literature.

Research log: [`logs/opus-review-3010-research-2026-10-30.md`](../../../logs/opus-review-3010-research-2026-10-30.md).

| Label | Meaning |
|---|---|
| **[Lean]** | Statement, docstring or proof read in Lean source during this review. Integration not assessed. |
| **[map]** | From the frontier map, a ledger or a programme README. |
| **[card]** | From the live pipeline card named above. |
| **(inference)** | A conclusion of this review, with its derivation. Not a Lean theorem. |

Companions: [walls](walls-ledger.md) · [route obstacles](route-obstacles.md) · [unification](route-unification-ledger.md) ·
[frontier map](../rh-current-frontier-map.md) · [killed mechanisms](../rh-killed-routes.md).

---

## 0. Answers in brief

1. **Mechanisms against a wall.**
   - **Σ1.** The corpus has reduced the complete atomic Weil matrix at growing overlap to three open estimates
     [card, Lean]:
     - a signed defect reserve with logarithmic cost;
     - a residual estimate weighted over growing conductor families;
     - effective confinement of negative eigenvectors.

     The proved reserve, read from its Lean proof, has the following anatomy:
     - the defect coefficient δ ∝ c⁻⁷ comes from the Fourier reserve;
     - the non-ratio and pole sources are paid by Young's inequality at ε = δ/8, each costing ∝ c²/ε;
     - hence the cost is ∝ c⁹ and the negative-vector defect bound is c²/δ² ∝ c¹⁶.

     M1 pays those two sources by signed shell repayment instead of Young's inequality. M1b removes the √φ(m) sup loss
     from the prime-residual conductor cost.
   - **Ruled out: quantized collision carriers.** The horizontal-collision (HC) endpoint RH ⇔ (collision charge < 2)
     is not a producer route [Lean, this review]. Every carrier computable from explicit formulas is a holomorphic
     linear or sesquilinear sum over the zeros. Any such sum that vanishes on critical configurations vanishes on all
     configurations, and its off-line signal at depth δ is at most 2ε^{1−δ/Δ}M^{δ/Δ}. The carriers that keep the
     quantum are non-holomorphic in the zero and have no source formula (§2).
2. **Wildly different.** No framework in the corpus is a producer (§3).
   - The carrier test shows why the observable-level shortcut fails: arithmetic single observables are holomorphic
     and blind off the line.
   - The Λ-positive models with the exact Riemann functional equation and off-line zeros show that selection must use
     discreteness of the prime measure [Lean].
   - A genuinely different approach would need a positivity family or a spectral realization, built from the discrete
     prime measure. This review proposes none that meets those requirements.
3. **Quasi-RH beyond 7/8.**
   - Exact targets: 5/6 ⇔ power-mesh covariance (m = 6) ≤ C J^{5+ε}, and 3/4 ⇔ the same at m = 4 with exponent
     3 + ε.
   - The absolute envelope is ≍ J^{m+1} on both sides and never ≤ C J^m [Lean].
   - (inference) The strip 1 − 1/m is a signed saving of exactly J² on the m-th mesh.
   - Inside the CGL detector, 5/6 needs ν ≤ 1/15 and κ + 4ν ≤ 4/3, and the method floor is 29/36. CGL packets
     cannot carry horizontal reflection charge. No gauge-invariant certificate beats 3/4 [Lean].
4. **75 % on the line.**
   - The census stands at 0.67250071 [Lean].
   - At κ = 4/3, the joint (c = 2, c = 3) rank–trace functional equals (3/4)N. On extremal frames it certifies 3/4
     distinct critical zeros whenever off-line pairs do not outnumber double critical zeros [Lean].
   - Two exact routes remain: zero-side slack ≥ N/12 (Route I) and prime surplus ≤ 1/18 at λ = 4/3 (Route II).
   - The collision inequality N₀ ≥ N − O(T) [Lean] gives no third route. The computable finite-height carriers are
     Montgomery's pair form, so they lead to pair correlation, i.e. Route II. They also weight a near-line zero by
     4 sinh²(δ log X), which is blind at depth ≪ 1/log X.
5. **Three questions.**
   - (Σ) A signed payment of the non-ratio and pole sources that brings the negative-vector defect bound from C c¹⁶
     to O(log c); its selective form is persistence of the pole ground line.
   - (Π, quasi-RH) The J² signed saving for the m = 4 power-mesh covariance, i.e. the 3/4 strip.
   - (census) Route I slack or Route II surplus.
6. **New field.** *Successor-shell arithmetic*.
   - Four corpus results fix what a missing tool must be:
     - holomorphic rigidity forces a positivity family, not a carrier;
     - the off-line Λ-positive models force use of discreteness;
     - the RH-receiver equivalence forces square-root precision;
     - the coalescence law forces visibility at depth o(1/log T).
   - The complete Weil form at growing overlap meets all four by construction. Its unpaid part is the successor-shell
     block.
   - The field is the signed additive–multiplicative arithmetic of that block beyond conductor modes (§7).

---

## 1. The frontier as the Lean corpus states it

### 1.1 Endpoint identities [map]

| Identity | Joins |
|---|---|
| `negIndex_zetaKernel_eq_zero_iff_count`: index of the Weil kernel = 0 ⇔ ψ(x) − x ≤ C√x log²x | Σ = Π |
| `riemannHypothesis_iff_collided_hecke_invariant`, `riemannHypothesis_iff_W_eq_collided` | Γ = Σ |
| Möbius gauge exponent at 0 equals Θ; RH ⇔ the trivial point is typical | Γ = Π |

### 1.2 Σ1: the complete atomic Weil matrix at growing overlap

Setting: atoms of width c/N on the horizon {1, …, N}, overlap c, profile φ; W = `completeWeilMatrix φ c N`;
normalized Ramanujan vectors u_m; completed conductor energies E_m(c). Tilted unit spline unless stated otherwise.

**At fixed overlap the problem is solved [Lean]:**

- W is eventually positive definite at every fixed c > 0. This holds for every C² profile supported in [0, 1] whose
  Fourier transform has no real zeros (`eventually_noRealZero_completeWeilMatrix_posDef`).
- Its low spectrum is counted by the conductor energies: #{eigenvalues < T} = #{m : E_m < T}
  (`eventually_completeWeil_spectral_count_eq_of_reserve_quasimodes`).
- Exactly one eigenvalue lies below the conductor-one gap, and its line captures the normalized pole vector
  (`eventually_tiltedUnitSpline_completeWeil_ground_count_one`,
  `eventually_tiltedUnitSpline_completeWeil_ground_near_pole`).
- For every level T there is a finite conductor set S with W ≥ T on span{u_m : m ∈ S}^⊥
  (`exists_finite_orthogonal_gap`).
- The set S comes from `exists_finite_ramanujan_approximation_of_poleDefect_le`. That construction takes a prime
  threshold P > exp(2C(K+1)/η) and all divisors of the valuation-box modulus `primeValuationBoxModulus P L`.

**At growing overlap c = c_N:**

| Statement | Source |
|---|---|
| Conductor floor E_m(c) ≥ κ (m/φ(m)) min(1, (m/c)⁷); E_m(c) ≤ C_m c² | [Lean] `tiltedUnitSpline_completedConductorEnergy_ge_conductor_scale`, `exists_completedConductorEnergy_polynomial_bound` |
| Pairwise Gram error \|⟨u_m, u_l⟩ − δ_{ml}\| ≤ (2ml + 1)/log N | [Lean] `normalizedRamanujan_gram_error_le` |
| **Square-root horizon**: Σ_{n≤N}(Σ_{m≤Q} a_m r_m(n))² ≥ (log(N+1) − 2 log Q) Σ a_m², for Q ≥ 2 | [Lean] `ramanujanPoleProfile_family_squareRoot_lower` |
| Residual ‖(W − E_m)u_m‖² ≤ K_m (c⁵/log N + c¹⁰(log N/N)²) for 4(e+3)²c² ≤ N. K_m collects eight component constants, each obtained per m | [Lean] `exists_completeWeil_completedConductor_residual_horizon_bound` |
| Prime part of the residual, explicit in m: family bound B·(Σ_m cost(m)²)(Σ_m b_m²), with cost(m) = √φ(m)(1 + 4 log m) | [Lean] `exists_uniform_ramanujanPrimeResidual_family_bound`, `ramanujanResidualConductorCost` |
| Fixed packets positive at c = (log N)^α, α < 1/40 | [Lean] `eventually_tiltedWeil_growing_packet_pos` |
| Gamma reserve: archimedean form ≥ (κc⁻⁷ log N − bc)(c/N)M Σx², with bc an archimedean low-frequency cost | [Lean] `TheGammaReserveSurvivesGrowingOverlap` |
| Defect reserve (a/c⁷)D − C c⁹ Σx² ≤ normalized weilQuad for N ≥ H c⁸; negative unit vectors have D ≤ C c¹⁶ | [Lean] `exists_tiltedUnitSpline_complete_defect_reserve_polynomial`, `exists_negative_completeWeil_poleDefect_polynomial_bound` |
| Defect-only capture fails below 2^k at defect γ + (k+1) log 2 + log 4 + 5 | [Lean] `not_eventually_defect_coordinate_capture_below_binary_cutoff` |
| RH ⇔ eventual nonnegativity for C² profiles when c⁴/log N → ∞, hence for the tilted spline at α > 1/4. Receivers also exist for smooth profiles at (log N)^ε, Gevrey profiles at (log log N)^s, and one Steklov profile | [Lean] `riemannHypothesis_iff_completeWeilEnergy_nonneg_of_growthTwo`, `OverlapGrowthPow`, `OverlapGrowthGevrey`, `TheFixedProfileReachesAnIteratedLogEndpoint` |

**Open items [card].** Three estimates are open:

- **Effective negative-eigenvector confinement.** Defect-only capture is intrinsically exponential: the binary
  no-go above. The binary witnesses are not negative eigenvectors, and the signed eigenvalue equation is the
  missing input.
- **A weighted residual estimate over growing conductor families.** It has the form Σ_{m∈S} ‖R_m‖²/(E_m + B)²
  < 1/18.
- **A signed reserve with logarithmic cost.** The candidate is W ≥ a c⁻⁷(D − C log(2c)‖x‖²). The card records it as
  unproved.

**Anatomy of the c¹⁶ (read from `tiltedUnitSpline_complete_defect_reserve_explicit`).**

- weilQuad/G splits into an arithmetic part and an archimedean part.
- The archimedean part satisfies archForm/G ≥ log N·S − (1 − δ/2)D − cost·S, with δ = min(growingMassConstant, 1/2)/c⁷.
- The arithmetic part keeps D through the ground-state identity P_N + D ≤ (log N + log 4 + 4)S. It must also pay the
  non-ratio form and the pole moments:
  - `abs_nonRatioForm_le_relative_defect` bounds the non-ratio form by εD + nonRatioRelativeCost(c, ε)·S;
  - `two_mul_abs_poleMoments_le_relative_defect` bounds the pole moments by εD + poleRelativeCost(c, ε)·S;
  - both costs carry a term ∝ c²/ε, and ε = δ/8.
- So the reserve keeps δ/4 of D at cost ∝ c²/δ ∝ c⁹. The negative-vector bound is cost/coefficient ∝ c²/δ² = c¹⁶.

(inference) Both exponents come from paying the two sources in absolute value against a defect fraction that the
Fourier reserve makes ∝ c⁻⁷. The logarithmic-cost candidate needs those sources paid with their sign.

**Readings (inference).**

1. *Fixed packets reach α < 1/19.* In the packet proof the entry error is
   c⁷⟨(W − E_i)u_i, u_j⟩ + c⁷E_i(⟨u_i, u_j⟩ − δ_{ij}).
   - With the horizon-decay residual, the first term is ≤ c^{19/2}(log N)^{−1/2} up to constants.
   - With E_i ≤ C c², the second term is O(c⁹/log N).
   - Both vanish for 19α < 1.
   - To confirm, rerun `eventually_tiltedWeil_growing_packet_pos` with
     `exists_tiltedUnitSpline_completedConductor_residual_horizon_bound`.
2. *The Gram is not the bottleneck.* The square-root horizon keeps conductor families conditioned up to Q < √N. The
   binding inputs are the residual weights and confinement. The explicit prime part has family cost
   Σ_{m≤Q} φ(m)(1 + 4 log m)² ≍ Q² log² Q against log N. The other seven components of K_m are not explicit in m in
   the Lean statements.

Elliptic localization [Lean: `elliptic_sector_nonneg_below_conductor_horizon`, `conductor_forcing_disjoint`]:

- Twisted positivity holds up to (4+ε)e^a + C ≤ log(1 + |γ|/8), with sharp constant 4.
- Forcing needs 768A log(|γ|+3) < e^{2δa}.
- The two conditions are disjoint for δ ≤ 1/2.

### 1.3 Γ: selection

| Statement | Source |
|---|---|
| κ(K_ζ) = number of distinct right zeros, κ even; RH ⇔ κ ≤ 1 | [map] HKT |
| Atomic index ladder, L = log N − γ: κ = 0 for D ≥ L + ε; κ = 1 on [L − 2 log 2 + ε, L − ε), with the square carried by the pole; κ ≥ 2 below, where the second square is the conductor-2 mode at γ + 2 log 2; every adjunction energy is a rung | [Lean] `TheMarginIsTheWidthOfTheIndexOneWindow` |
| Sign gauges share the ladder. Pole indices of two gauges differ by ≤ 1. In the window, ζ has pole index 0 and the Liouville twin 1 | [Lean] `hermNegIndex_gaugeAtom_eq`, `poleNegIndex_gauge_le_add_one`, `eventually_poleNegIndex_window` |
| Shrinking atomic schedules reach the whole index; whether the explicit schedule (log log N)^α/N does is left open | [Lean] `exists_shrinking_schedule` |
| Coalescence law: an off-line pair has one negative square for t ≠ 0 and none in the on-line limit | [Lean] `coalescence_law` |
| No gauge-invariant bound on the Möbius exponent is below 3/4 | [Lean] `threeQuarters_le_of_gaugeInvariant_bound` |
| An entire completed function with the exact Riemann functional equation, a nonnegative generalized von Mangoldt measure, and zeros off the line; Beurling systems with off-line zeros | [Lean docstrings] `EntireFunctionalEquationOffLine`, `LambdaPositiveFunctionalEquationOffLine`, `BeurlingRegularIntegersOffLineZeros` |
| Discrete Beurling systems with the Riemann functional equation are rigid | [Lean docstring] `BeurlingRiemannFunctionalEquationRigidity` |
| Deninger: canonical big-Witt Frobenius exists; conformal Hodge positivity does not constrain the spectrum; five further no-gos | [Lean docstrings] `DeningerResolventCoreIsRiemannHypothesis` and the big-Witt no-go modules |

**Reading (inference).**

- At fixed overlap, selection at complete resolution is already settled: W is positive definite and its ground line
  is the pole (§1.2). The atomic ladder shows what the pole selects against: the next rung is conductor 2.
- A selective question survives only along growing overlap, as persistence of the pole ground line with energy
  E_1(1 + o(1)). That statement is positivity, so it is Σ1 in selective form.
- The off-line Λ-positive models show what selection must use. Positivity of Λ plus the functional equation does not
  force the line. Discreteness of the prime measure does single out ζ.

### 1.4 Π: what precision costs

| Statement | Source |
|---|---|
| Full order-r mixed multiplicity on the q-torsion grid forces support ≥ 2^{qr}, attained by (X^q − 1)^r | [Lean] `AdamsMultiplicityResolution`, `TorsionArithmeticResolution` |
| Euler operators lower multiplicity; vertical cancellation does not give torus multiplicity; algebraic first vertical jets are faithful (Baker); two-prime log rigidity | [Lean docstrings] `ArithmeticHarmonicAnalysis/` |
| Periodic producers pay 2 log 2 per unit mass; a ceiling at precision θ < 1 is a zero-free strip | [map] AGT, ASRP |
| RH ⇔ real-zero jets of the theta measure are dense in L¹_even(μ); an off-line zero gives an explicit bounded annihilator | [Lean] `ThetaEndpointHarmonicCompleteness`, `exists_offLine_annihilator` |

### 1.5 Coalescence and the horizontal-collision programme

| Statement | Source |
|---|---|
| Collision charge O(T) = Σ_ρ m_ρ(H_ρ − m_ρ) ∈ 2ℕ dominates the off-line mass. RH ⇔ O(T) < 2 on every window ⇔ O(T) = 0 | [Lean] `riemannHypothesis_iff_forall_horizontalCollisionCharge_lt_two`, `…_eq_zero` |
| N₀(T) ≥ N(T) − O(T) | [Lean] `xiStripWindowTotalOrder_sub_collisionCharge_le_lineOrder` |
| Carriers that keep the quantum (two-prime Cesàro, Prime–Cayley, Ward–Green, exterior, Gauss–Hodge) have zero-side summands non-holomorphic in ρ: functions of Im ρ (p^{ρ−ρ̄}), of Re ρ (`realCayley(2 Re ρ − 1)`, (½ − Re ρ) log 2), or (Re ρ − ½)⁻² (`thetaXiWardTransverseGreenWeight_eq`). None has a source formula | [Lean] `XiHorizontalCollision*` |
| **Growth dichotomy**: the explicit-formula clock is holomorphic; its excess vanishes on all-critical windows and is unbounded on any window with an off-line zero | [Lean] `XiHolomorphicTwoPrimePencilGrowthDichotomy` |
| An entire weight vanishing on the critical line is zero: "beta-sensitivity and arithmetic evaluability are mutually exclusive" | [Lean] `entire_vanishing_on_criticalLine_eq_zero` (`AnalyticityExcludesBetaSensitivity`) |
| **Holomorphic carrier rigidity**: a holomorphic linear or sesquilinear carrier that vanishes on critical configurations vanishes on every reflection-symmetric configuration in the strip | [Lean, this review] `linearCarrier_eq_zero`, `sesquilinearCarrier_eq_zero` |
| **Three-lines tradeoff**: with on-line bound ε and bound M on Re s = ½ + Δ for h(s) + h(1−s), an off-line quartet at depth δ ≤ Δ carries ≤ 2ε^{1−δ/Δ}M^{δ/Δ}; if 2ε < q, no quartet near the line carries q | [Lean, this review] `norm_quartet_le_interp`, `exists_depth_without_quantum` |
| Montgomery's unconditional pair form is the log-scale mean square of the holomorphic zero power sum Σ y^{ρ−½}; its leading order is proved for 0 < α < 1 | [Lean] `MontgomeryFormLogScaleMeanSquare`, `MontgomeryPairCorrelationLeadingOrder` |
| Constraints on any collision observable: orientation is never created by transport; oriented displacement cancels under exchange; no scalar reporter exact on collisions is lower semicontinuous; even readers lose the first jet | [Lean] `PairwiseFirstCoalescenceLaw`, `XiHorizontalCollisionExchangeOrientationNoGo`, `XiHeatCassiniWoldOrbitChargeLowerSemicontinuousCollisionNoGo`, `evenReader_firstJet_zero` |
| CGL packets cannot carry two reflected points; the Prop 4.6 envelope is ≥ 288 against the quantum 2 | [Lean] `ChenGuptaLiHorizontalCollisionNoGo` |
| Census frames: double critical zeros and coalesced pairs share `extremalDiag` | [Lean] `BreakingTheCoalescenceBlindSpotAndThreeQuarters` |
| ShallowCauchy: (α/log T)E_{α/log T} + R_deep = O_α(N(T,2T)) | [Lean docstrings] `ShallowCauchyImplications` |

**Reading (inference).** Quantization is an RH-equivalent reformulation, not a producer route.

- The carriers that see the quantum depend non-holomorphically on the zeros and have no arithmetic evaluation.
- The carriers the explicit formula computes are holomorphic sums, which are rigid on critical configurations and
  bounded off the line by three lines.
- The computable side, at absolute precision, is square-root precision for prime counts in windows of relative width
  1/T: the Π class.
- At finite height and N-normalized, the computable mean square is Montgomery's pair form: pair correlation.
- The coalescence blind spot reappears as the weight 4 sinh²(δ log X).

---

## 2. Q1: mechanisms that circumvent or destroy a wall

### M1. Signed payment of the non-ratio and pole sources (Σ1)

- **Target.** The card's logarithmic-cost reserve W ≥ a c⁻⁷(D − C log(2c)‖x‖²). With it, every negative vector
  has D = O(log c).
- **Why the proved reserve misses it.** The c⁹ cost comes entirely from Young's inequality against the defect
  fraction ε = δ/8 ∝ c⁻⁷ (§1.2 anatomy).
- **Mechanism.** On conductor modes the shells repay exactly. The Möbius signs collapse to coprimality, so
  E_m(c) = (2/(Mφ(m))) Σ_{(a,m)=1} (m/a) ∫_{ac/m}^∞ |φ̂(2πt)|² ≥ 0 [Lean `TheShellsRepayEveryConductor`]. The
  proposal bounds the non-ratio form, the pole moments and the archimedean shell deficit jointly, with that sign
  retained, instead of each in absolute value.
- **First theorem.** The joint signed bound on span{u_m : m ≤ Q} with cost O(log c) per unit mass. It would use
  shell repayment, the square-root horizon, and the explicit prime residual.
- **Risk.** Off the conductor span the signed structure is unknown. This is where the RH content of Σ1 sits at
  growing c.

### M1b. Removing the sup loss from the prime-residual conductor cost (Σ1)

- **Fact [Lean].** The conductor factor √φ(m) in `ramanujanResidualConductorCost` enters through the pointwise bound
  |normalized mode| ≤ √φ(m) (`abs_normalizedRamanujanMode_le_sqrt_totient`). Each row is weighted by
  primeMertensRemainderProfile(N/n)²/n.
- **Proposal (inference).** Over a full period Σ_{n mod m} c_m(n)² = mφ(m), so the normalized mode has mean square
  1. On blocks where N/n is constant and the block length is ≥ m, the sup bound can be replaced by this mean square.
  That would turn the family cost Σ φ(m) log² m into Σ log² m.
- **Check required.** The `poleProfileCorrection` term in the residual identity must admit the same averaging.

### M2. Persistence of the pole ground line (Γ)

At fixed c the ground line is the pole [Lean]. The statement to carry along c_N: exactly one eigenvalue lies below
(E_1 + E_2)/2, it equals E_1(1 + o(1)), and its eigenline converges to the pole vector. Since E_1 > 0 this is
positivity, so M2 is Σ1 in selective form, not an independent mechanism. The atomic ladder shows the competing rung
is conductor 2 [Lean].

### M3. A J² signed saving on integer-power meshes (Π, quasi-RH)

- **Facts [Lean].**
  - On the m-th mesh the cumulative square exponent is 1 + 2m(Θ − 1/2).
  - 5/6 ⇔ `mobiusDivisorDilationPowerMeshCovariance 6 J ≤ C J^{5+ε}`; 3/4 ⇔ the same at m = 4 with exponent 3 + ε.
  - The positive envelope is ≍ J^{m+1} on both sides and never ≤ C J^m.
  - The diagonal costs ≤ 9/25 per scale. The off-diagonal is the literal ordered pair sum with both Möbius signs,
    and "no improved bound for the off-diagonal is assumed or asserted".
- **Reading (inference).** The saving needed is J^{(m+1) − (1 + 2m(Θ − 1/2))} = J^{2m(1−Θ)}, which equals J² at
  Θ = 1 − 1/m.
- **Related corpus work.** The damped-divisor covariance balance (`PMPowerDampedMobiusLogConvolution`, with no sign
  assumed). Sextic shift and character correlations (`QuasiRHShiftCorrelation`, `QuasiRHCharacterCorrelation`).

### Ruled out: quantized collision carriers

The full record is the card `5-failed/hc-quantization-as-producer.md`. The six tests:

1. **Classification.** No carrier is both computable from arithmetic and quantized.
   - The carriers that keep the quantum depend on the zero through Im ρ, Re ρ or (Re ρ − ½)⁻² alone.
   - The exterior carrier's prime–Gamma formula covers only its Weil-matrix entries; the quantum appears after
     per-zero normalization.
   - The holomorphic pencil is computable but unquantized.
2. **Rigidity.** Holomorphic carrier rigidity and the three-lines tradeoff are proved in Lean (§1.5).
3. **Finite height.** By the explicit formula, the computable carrier is square-root-precision prime counting in
   windows of relative width 1/T: Π. Its normalized mean square is Montgomery's form: pair correlation.
4. **Selection.** The carriers exist for every zero set with the reflection symmetry. A source law using only the
   functional equation and Λ ≥ 0 holds for the off-line models of §1.3, so it cannot prove RH.
5. **𝔽_q.** The holomorphic clock is −(N_n − qⁿ − 1)/q^{n/2}. Its bound is exactly the point-count bound: Π.
6. **Census.** Near-line zeros enter with weight 4 sinh²(δ log X), invisible at depth ≪ 1/log X.

---

## 3. Q2: wildly different approaches

| Framework | What the corpus proves | Producer status |
|---|---|---|
| Quantization (HC) | RH ⇔ O(T) < 2; reflection-faithful carriers | Reformulation: the computable side is Π, the zero side has no source formula [Lean] |
| Theta-Hawking scattering | RH ⇔ real backreaction resonances, ⇔ all-pass winding rigidity, and further endpoints | Endpoints |
| Heat / resolvent Hankel | RH ⇔ heatHankel a P P ≥ 0; RH ⇔ resolvent Hankel forms nonnegative; Λ is the extinction time of the Weil index | Endpoints |
| JAS | Positive at dressing 2; RH ⇔ JasDressedPSD 1 ∧ quasi-RH | Gap from dressing 2 to 1 |
| Herglotz | Full-cone Weil positivity ⇒ Herglotz positivity of the Weil function on Re s > ½. Carrier rigidity for stable self-reciprocal Dirichlet polynomials. The centered prime-tail carrier preserves the divisor but not positivity | Herglotz positivity is the endpoint |
| Theta completeness | RH ⇔ density of real-zero jets; explicit annihilator off the line | Endpoint; the producer would be domination rigidity |
| ThetaCusp fibre form | Square plus null Lagrangian at every center; size eight at every aperture by certificates. The lawful degree-twelve flux has one-sided tail debt | Finite-rank identities; no uniform flux bound |
| Deninger big-Witt | Canonical Frobenius; conformal positivity is spectrum-blind | No-go |

Sources [Lean]:

- `riemannHypothesis_iff_forall_horizontalCollisionCharge_lt_two`, `XiHolomorphicTwoPrimePencilGrowthDichotomy`,
  `linearCarrier_eq_zero`, `sesquilinearCarrier_eq_zero`
- `riemannHypothesis_iff_thetaCuspHawkingBackreactionResonances_real`, `riemannHypothesis_iff_heatHankel_nonneg`,
  `riemannHypothesis_iff_forall_xiResolventHankelForm_re_nonneg`, `WeilIndexExtinctionTime`
- `jasDressedPSD_two`, `riemannHypothesis_iff_jasDressedPSD_one_and_quasi`
- `herglotzWeilPositive_of_weilPositiveFull`, `exists_zero_stableDirichlet_riemannZeta_ne_zero`,
  `CriticalCenteredPrimeTailEntireCarrier`
- `ThetaEndpointHarmonicCompleteness`
- `ThetaCuspCenterTailSquareFlux`, `ThetaCuspOddFourRankEight`, `ThetaCuspDegreeTwelveFluxBoundary`
- `DeningerResolventCoreIsRiemannHypothesis`

**Reading (inference).** No row is a producer, and the corpus results say why the shortcuts fail.

- **Observables.** An arithmetic single observable of the zeros is a holomorphic linear or sesquilinear sum. It sees
  only data fixed on the critical line, and its off-line signal is bounded by three lines (`AnalyticityExcludesBetaSensitivity`,
  `HolomorphicCarriersCannotBeQuantized`).
- **Positivity plus the functional equation.** These do not select ζ: Λ-positive models with the exact functional
  equation have off-line zeros (`EntireFunctionalEquationOffLine`).
- **Conformal Hodge positivity.** It is spectrum-blind (`DeningerResolventCoreIsRiemannHypothesis`).

What remains for a genuinely different approach:

- a positivity family over tests, or a spectral realization whose traces give same-point zero sums;
- built from the discrete prime measure.

The positivity-family option leads back to the Weil form, i.e. Σ1. The spectral-realization option is the CCM line
of the corpus (1,272 modules), not audited in this review. This review proposes no framework that is genuinely
different and meets these requirements.

**Not recommended.**

- More endpoints of the theta-Hawking type.
- Any carrier-level observable, by the rigidity theorem.

---

## 4. Q3: Quasi-RH beyond 7/8

### 4.1 Status

- No strip is proved [map]. The 7/8 statement is an external claim [map: [E]].
- The CGL modules formalize Guth–Maynard extended to characters: Theorem 1.1, Lemma 4.5, Proposition 4.6, and the
  principal Guth–Maynard form of Lemma 6.2 [Lean module headers].
- RH ⇔ JasDressedPSD 1 ∧ quasi-RH. Under quasi-RH off-line chains are impossible below σ = ½ + Θ [Lean].
- Under LH, quasi-RH ⇔ cos(hD)Ξ is real-rooted for some h < ½ [Lean].

### 4.2 Exact targets [Lean]

| Target | Equivalent statement | Lean |
|---|---|---|
| 5/6 strip | power-mesh covariance (m = 6) ≤ C J^{5+ε}; Chebyshev Cesàro energy subpower; dilation covariance subpower | `xi_zero_five_sixths_strip_iff_powerMeshCovariance_subpower`, `five_sixths_strip_iff_chebyshevNormalizedCesaroMeanSquareEnergy_subpower`, `xi_zero_five_sixths_strip_iff_dilationCovariance_subpower` |
| 3/4 strip | power-mesh covariance (m = 4) ≤ C J^{3+ε} | `xi_zero_three_quarters_strip_iff_powerMeshCovariance_subpower` |
| Any strip by absolute values | impossible: envelope ≍ J^{m+1}, never ≤ C J^m | `exists_mobiusDivisorDilationPositiveMeshEnergy_two_sided`, `not_mobiusDivisorDilationPositiveMeshEnergy_le_pow` |
| Any strip by multiplicative data | impossible below 3/4 | `threeQuarters_le_of_gaugeInvariant_bound` |

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

### 4.4 Recommendation (inference)

1. Treat the J² saving (M3) as the detector-independent target. The meshes m = 5 (4/5) and m = 4 (3/4) lie below the
   detector floor 29/36.
2. Inside the detector, find which CGL lemma fixes κ = 2 before choosing a lever. The 5/6 condition
   κ + 4ν ≤ 4/3 concerns the large-values term of the packet Gram.
3. Do not pursue a CGL merger with reflection charge. The horizontal-collision no-go rules out finishing S₂/S₃, and
   the carrier rigidity theorem rules out a computable carrier for that charge.
4. Audit the CGL dependency chain, which is [E].

---

## 5. Q4: at least 75 % of zeros on the line

### 5.1 Status [Lean]

- Simple critical proportion ≥ 0.67250071 − ε (`simple_critical_proportion_ge_67250071`).
- At least 4/5 − ε of ordinates carry a critical zero (`Zeta23CriticalOrdinateCensus`).
- 70 % dichotomy: failure forces ≈ 0.2725N simple off-line zeros within A/log T (`Zeta23SeventyPercentOrSimpleNearLine`).
- Pinching: disjoint simple pairs give an exact overlap gain by rotation (`DisjointPairSchurSlack`). The cosine
  kernel has a non-lattice floor of 1/250 on span-3 triples (`CosineKernelNonLatticeFloor`).

### 5.2 The exact form of 3/4 [Lean `BreakingTheCoalescenceBlindSpotAndThreeQuarters`]

- **κ = 4/3.** jointRankTrace23 = (14 tr Â − 3‖Â‖_F² − 7N)/4 = (3/4)N (`jointRankTrace23_at_four_thirds`). On
  extremal frames it equals s₁ + (d₂ + p)/2. So 3/4 distinct critical zeros follow if p ≤ d₂, and 3/4 with
  multiplicity if p ≤ 3d₂ (`three_quarters_of_broken_blind_spot_at_four_thirds`).
- **Route I** (`zeta_three_quarters_of_spectralSlack`): requires a zero-side spectral slack ≥ (3/4 − H(λ))N, which
  tends to N/12. The on-line Parseval identity gives the double-zero frames slack N/6.
- **Route II** (`kappa_five_fourths_iff_three_quarters`, `zeta_three_quarters_from_prime_surplus`): 3/4 ⇔ κ ≤ 5/4. At
  λ = 4/3 the margin left for the prime surplus is 1/18. Its Hardy–Littlewood value is −1/144; positive majorants
  give 8/27 [map].
- **Mollifier** (`ZetaCGGMollifierOptimum`): 3/4 ⇔ (1+θ)³ ≥ 4, for a simple-zero ratio with conditional main terms.

### 5.3 Reading (inference)

The census gap is a coalescence gap. At the kernel level an off-line pair coalescing onto the line equals a double
critical zero (`coalescence_law`). Two exact routes remain:

- Route I: zero-side slack ≥ N/12.
- Route II: pair-correlation surplus ≤ 1/18 at λ = 4/3.

The collision inequality N₀ ≥ N − O(T) turns 75 % into O(T) ≤ N/4, but no computable carrier delivers it.

- At finite height the computable mean square is Montgomery's pair form, so a bound there is a pair-correlation
  statement. That is Route II again.
- Such a carrier weights an off-line pair at depth δ by 4 sinh²(δ log X), so the near-line core of the 70 %
  dichotomy can sit below its resolution.

The 70 % shallow-Cauchy step is proved O_α(N); it needs ≤ 3N/20.

---

## 6. Q5: three questions to focus on

### Question 1 (Σ): signed payment at growing overlap

Can the non-ratio form, the pole moments and the archimedean shell deficit of the complete form be bounded jointly,
with sign, so that the reserve cost drops from C c⁹ to a c⁻⁷·O(log c)? Equivalently: can the negative-vector defect
bound drop from C c¹⁶ to O(log c)?

- **Why.** The c¹⁶ is the ratio c²/δ² produced by two absolute-value payments (§1.2). The card's open items
  (confinement, weighted residual) become polynomial once the defect is logarithmic.
- **Selective form.** Persistence of the pole ground line along c_N (M2). At fixed c it is a theorem.
- **First step.** The bound on the span of conductors m ≤ Q (M1), with M1b for the residual weights.

### Question 2 (Π, quasi-RH): the J² saving on the fourth-power mesh

Is `mobiusDivisorDilationPowerMeshCovariance 4 J ≤ C J^{3+ε}`, i.e. a J² signed saving over the absolute envelope?

- **Why.** This is the 3/4 strip exactly [Lean]. Absolute values cannot give it, and the CGL detector cannot reach it.

### Question 3 (census): Route I or Route II

Is there a zero-side spectral slack ≥ (3/4 − H(λ))N → N/12, or a prime surplus ≤ 1/18 at λ = 4/3?

- **Why.** These are the two exact routes to 75 % [Lean]. The collision route reduces to Route II (§5.3).

**Runner-up (Γ).** A functional that is nonnegative for the discrete prime measure of ζ and fails for the continuous
Λ-positive models with the Riemann functional equation and off-line zeros. Any proof of RH must use a property that
fails for those models.

---

## 7. Q6: the new field. Successor-shell arithmetic

### 7.1 What the missing tools must be [Lean]

| Requirement | Forced by |
|---|---|
| R1. A positivity family over tests, not a single carrier | `linearCarrier_eq_zero`, `sesquilinearCarrier_eq_zero`, `norm_quartet_le_interp`, `entire_vanishing_on_criticalLine_eq_zero` |
| R2. Use of discreteness of the prime measure, not only Λ ≥ 0 and the functional equation | `EntireFunctionalEquationOffLine`, `LambdaPositiveFunctionalEquationOffLine`, `BeurlingRiemannFunctionalEquationRigidity` |
| R3. Square-root precision | `negIndex_zetaKernel_eq_zero_iff_count`, `riemannHypothesis_iff_completeWeilEnergy_nonneg_of_growthTwo` |
| R4. Visibility at depth o(1/log T) | `coalescence_law`, `exists_depth_without_quantum` |
| R5. No conformal positivity alone | `DeningerResolventCoreIsRiemannHypothesis` |

### 7.2 The object that meets them (inference)

The complete atomic Weil form at growing overlap meets R1 to R4 by construction:

- **R1.** It is a quadratic form over all coefficient vectors.
- **R2.** It is built on the integers, with atoms at log n and the prime kernel Λ(k)/√k.
- **R3.** Its positivity at c⁴/log N → ∞ is RH.
- **R4.** Weil positivity detects off-line zeros at every depth.

Its unpaid part is the successor-shell block: pairs n = km + h with |h| < c and weight Λ(k)/√k, the non-ratio form of
§1.2. On conductor modes the shells repay exactly. Off them, the corpus pays the block in absolute value, and that
payment is the whole c¹⁶.

### 7.3 The field

*Successor-shell arithmetic*: signed cancellation in the shell block of the complete Weil form, for general
coefficient vectors, at growing overlap. Additive structure (h) and multiplicative structure (k, m) meet at the atomic
scale.

**Objects.**

1. Shell forms, schematically Σ_k Λ(k) k^{−1/2} Σ_{|h|<c} x_{km+h} x_m weighted by the atom overlap.
2. Ramanujan expansions of shell coefficients, c_m(h).
3. Residue and growing shell sources.
4. The prime defect as the multiplicative Dirichlet energy.

**Known theorems [Lean or map].**

- Exact repayment on conductor modes (`TheShellsRepayEveryConductor`).
- Fixed-modulus shell sources with inverse-log rates (`PrimeResidueSourcesHaveQuantitativeLogDecay`,
  `GrowingShellSourcesHaveLogarithmicRates`).
- A uniform harmonic budget for affine shell errors (`AffineShellErrorsHaveAUniformHarmonicBudget`).
- The large-sieve half of level 1/2 for shells (AGT).
- Short shells c ≤ 2 have no conductor [map].
- The uniform Dirichlet zero-free region needed for Siegel–Walfisz on shells
  (`DirichletLUniformZeroFreeRegion`; the remaining steps are an in-progress card).

**Central open theorem.** Signed repayment off the conductor span: the non-ratio form plus the archimedean shell
deficit is ≥ −a c⁻⁷ O(log c)·mass − (small)·defect. This is Question 1.

**Acceptance criteria.**

1. Recovers the conductor-mode repayment and the fixed-c spectral count.
2. Fails for the continuous Λ-positive models with off-line zeros (R2).
3. Gives a growing-c reserve with cost below c⁹.
4. Unconditional Lean statements.

**Relation to the corpus.** The field is the common core of CACT, CAF, RAPT, AGT's shell work and the SW/BV card. What
it adds is the target: signed shell payment beyond conductor modes as the single estimate that controls the reserve
cost.

---

## 8. Evidence

**Documents read:** the six ledgers and indexes named in the task, the 55 programme READMEs, and the card
`docs/drafts/pipeline/1-in-progress/quasi-rh-from-effective-conductor-confinement.md`.

**Lean source read** (statements, docstrings and the proofs cited), by area:

- **Σ1:**
  - `CompletedArithmeticForms/WeilGrowingPackets`, `WeilGrowingOverlap`, `ConductorLogLaw`
  - CACT:
    - `CompleteConductorResidualsRetainTheirHorizonDecay` (full proof), `TheCompleteWeilReserveHasPolynomialOverlapCost`
      (cost definitions and the explicit reserve proof)
    - `ConductorScaleControlsTheCompletedEnergy`, `GrowingRamanujanFamiliesHaveASquareRootHorizon`,
      `TheCompleteWeilGroundStateIsThePole`, `EveryProfileWithoutRealFourierZerosIsPositiveAtEveryOverlap`
    - `MacroscopicOverlapPositivityAtEveryOverlap`, `WeilReplacementErrorsHavePolynomialCost`,
      `NearGammaDownwardCancellationHasPolynomialGrowth`, `UpwardPrimeErrorsRetainTheirHorizonDecay`,
      `DirectedPrimeRowsPreserveTheDefect`
  - RAPT: `PrimeDefectConfinementMustRetainLowEnergyConductors`,
    `BoundedPrimeDefectHasFiniteRamanujanApproximation` (full proof),
    `ATwistedCompleteWeilMatrixIsDecidedByItsRamanujanPackets`,
    `TheBoundedCompleteWeilSpectrumIsTheCompletedShellSpectrum`, `TheShellsRepayEveryConductor`,
    `TheDeficitOfThePrimeFormIsADirichletEnergy`, `LogarithmicOverlapOfTheCompleteWeilMatrixIsTheRiemannHypothesis`
  - `SignedArithmeticHodgeTheory/OneArithmeticRemainderControlsEveryRamanujanResidual`,
    `TheArithmeticResidualBudgetIsUniformInTheHorizon`
  - `ArithmeticLorentzianGeometry/ThePoleIsInfinitesimalRelativeToThePrimeDefect`
  - SSHA overlap-law modules
- **Γ:**
  - HKT: `TheMarginIsTheWidthOfTheIndexOneWindow`, `TheSelectiveIndexOfTheAtomicKernelIsOneSquare`,
    `ShrinkingAtomsCarryTheWholeIndex`, `TheIndexUnderRotationDampingAndCoalescence`,
    `APurePointSpectrumIsThinAtMostFrequencies`
  - `ArithmeticGaugeTheory/TheExponentIsNotGaugeInvariant`
  - Off-line models: `EntireFunctionalEquationOffLine`, `LambdaPositiveFunctionalEquationOffLine`,
    `BeurlingRegularIntegersOffLineZeros`, `ArithmeticPositiveDuality/BeurlingRiemannFunctionalEquationRigidity`
  - Deninger modules
- **Π:** `ArithmeticHarmonicAnalysis/`, `RHTower/ThetaEndpointHarmonicCompleteness`.
- **Coalescence:**
  - RHTower collision carriers: `XiHorizontalCollisionChargeEndpoint`, `…TwoPrimeCesaroCarrier`,
    `…PrimeCayleyInformationLoss`, `…WardGreenCayleyQuantum`, `…WardGreenExteriorSourceCarrier`,
    `…GaussHodgePrimeCurrent`, `…OrderedPrimeCrossCurvature`, `…ExchangeOrientationNoGo`,
    `XiHolomorphicTwoPrimePencilGrowthDichotomy`
  - RHTower collision no-gos and supporting modules: `XiHeatCassiniWoldOrbitChargeLowerSemicontinuousCollisionNoGo`,
    `XiResolventLineReflectionDefect`, `PrimeBurnolMixedReflectedCollision`,
    `SourceHorizontalGammaSixTameReaderTransgression`, `AnalyticityExcludesBetaSensitivity`
  - Carrier definitions: `thetaXiWardTransverseGreenWeight` (Hedenmalm Ward modules),
    `sourceZeroHorizontalPrimeCarrier`, `gaussHodgeMassCurrent`, `primeDepthBVWoldXiCenteredRate`,
    `burnolPrimeCharacter`, `HedenmalmCriticalFeatureExteriorPrimeGammaSource`
  - Montgomery: `MontgomeryFormLogScaleMeanSquare`, `MontgomeryPairCorrelationLeadingOrder`
  - HTGeometry: `PairwiseFirstCoalescenceLaw`, `ReflectedChannelProjectiveFlow`, `AutonomousStripSeparant`,
    `StripThreeLinesTransfer`
  - `HilbertMetric/CoherentCollisionJet`
- **Quasi-RH:**
  - QuasiRH: `QuasiRHDetectorScaleBudget`, `QuasiRHDetectorGramTradeoff`, `QuasiRHPowerMeshMeanSquareAbscissa`,
    `QuasiRHHighDilationPositiveEnvelope`, `QuasiRHDilationCovarianceAbscissa`, `QuasiRHShiftCorrelation`,
    `QuasiRHCharacterCorrelation`
  - JAS and Lindelöf: `JointAncestryQuasiRHChainExclusion`, `LindelofQuasiRHCosineThreshold`
  - `PMPowerDampedMobiusLogConvolution`
  - CGL headers and `ChenGuptaLiHorizontalCollisionNoGo`
- **Census:**
  - `Zeta23CriticalOrdinateCensus`, `Zeta23SeventyPercentOrSimpleNearLine`, `ZetaCGGMollifierOptimum`
  - `BreakingTheCoalescenceBlindSpotAndThreeQuarters`
  - `DisjointPairSchurSlack`, `CosineKernelNonLatticeFloor`
  - `ShallowCauchyImplications`
- **Other:**
  - Heat: `HeatZeroDisplacement`, `HeatUniformDepthZeroDensity`, `WeilIndexExtinctionTime`
  - ThetaCusp: `ThetaCuspCenterTailSquareFlux`, `ThetaCuspOddFourRankEight`, `ThetaCuspDegreeTwelveFluxBoundary`
  - Herglotz and Putnam: `StableDirichletPolynomialPutnam`, `WeilFullConeHerglotzCriticalHalfPlane`,
    `CriticalCenteredPrimeTailEntireCarrier`, `EulerLogPrimePowerHerglotzMass`

**Lean written and checked:** `RHTower/HolomorphicCarriersCannotBeQuantized.lean`.

- `linearCarrier_eq_zero`
- `sesquilinearCarrier_eq_zero`
- `norm_quartet_le_interp`
- `exists_depth_without_quantum`

`lake --old env lean` passes; the axioms are `propext`, `Classical.choice`, `Quot.sound`.

**Corpus searches** (`scripts/formal_tools.py research`), one per claim checked:

- Σ1 and Γ: complement coercivity; graded reserves; successor shell norms; uniform quasimodes; negative eigenvector
  pole coordinate; pole index of the complete matrix; ground eigenline at growing overlap; weighted conductor
  residuals; effective confinement; packets with the horizon-decay residual; shrinking atomic schedules.
- Coalescence and carriers:
  - collision observables: confluent channels; coalescence-stable indices; terminal recovery after coalescence;
    even-reader first jets; HC source carriers; pre-divisor source laws; normalized collision census; prime-side
    bounds for oriented collision observables;
  - analytic tools: symmetrized holomorphic weights on the critical strip; reflection-invariant zero sums; three
    lines on vertical strips; identity theorem on the critical strip.
- Selection and pair correlation: Davenport–Heilbronn-type models; Beurling systems with off-line zeros; Montgomery
  pair correlation.
- Other frameworks: ThetaCusp flux at every size; Herglotz carriers from Euler data; power-mesh covariance tools.
