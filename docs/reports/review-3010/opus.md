# Opus review 3010: the Lean frontier and where it points

Status: 30 October 2026, corpus `632f87ee3c` plus working tree. **RH is open; no wall is crossed.**

Scope:

- Sources: the six ledgers named in the task, the 55 programme READMEs, `scripts/formal_tools.py research`, the Lean
  statements, docstrings and proofs quoted below, and one live pipeline card
  (`1-in-progress/quasi-rh-from-effective-conductor-confinement.md`).
- Corpus size: RHTower 29,309 Lean files, HTGeometry 18,918, plus the arithmetic programmes.
- Not done: no builds, compilation checks, axiom audits, web searches or external literature.

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
   - **Coalescence.** The horizontal-collision (HC) programme reduces RH to an absolute bound below the indivisible
     quantum 2 on explicit reflection-faithful carriers. It also proves that the explicit-formula clock of the
     two-prime pencil has no finite quantum. M3 states the producer this leaves.
2. **Wildly different.** The corpus's genuinely different form of RH is quantization: the collision charge lies in
   2ℕ, so any eventual bound below 2 is RH [Lean]. Its limit is also proved: for the two-prime pencil the quantum
   margin exists only on the zero-indexed side, and the source-realizable holomorphic excess reads ∞·K(T) [Lean]. The
   other frameworks in the corpus (theta-Hawking, Hankel, JAS, Herglotz, theta completeness, Deninger) are endpoints
   or identities without a producer (§3).
3. **Quasi-RH beyond 7/8.**
   - Exact targets: 5/6 ⇔ power-mesh covariance (m = 6) ≤ C J^{5+ε}, and 3/4 ⇔ the same at m = 4 with exponent
     3 + ε.
   - The absolute envelope is ≍ J^{m+1} on both sides and never ≤ C J^m [Lean].
   - (inference) The strip 1 − 1/m is a signed saving of exactly J² on the m-th mesh.
   - Inside the CGL detector, 5/6 needs ν ≤ 1/15 and κ + 4ν ≤ 4/3, and the method floor is 29/36. CGL packets
     cannot carry horizontal reflection charge, whose quantum is the HC quantum 2. No gauge-invariant certificate
     beats 3/4 [Lean].
4. **75 % on the line.**
   - The census stands at 0.67250071 [Lean].
   - At κ = 4/3, the joint (c = 2, c = 3) rank–trace functional equals (3/4)N. On extremal frames it certifies 3/4
     distinct critical zeros whenever off-line pairs do not outnumber double critical zeros [Lean].
   - The corpus also proves N₀(T) ≥ N(T) − O(T), where O(T) is the collision charge [Lean]. (inference) An eventual
     bound O(T) ≤ N(T)/4 gives 75 % with multiplicity, and O(T) ≤ 3N(T)/10 gives 70 %.
5. **Three questions.**
   - (Σ) A signed payment of the non-ratio and pole sources that brings the negative-vector defect bound from C c¹⁶
     to O(log c).
   - (Γ) Persistence of the pole ground line of the complete matrix along growing overlap.
   - (HC) A prime-side bound on one reflection-faithful carrier: O(N) with constant < 1/4 for the census, absolute
     < 2 for RH.
6. **New field.** *Hilbertian explicit formulas*.
   - Weil's explicit formula computes reflection-paired zero sums: the Weil form.
   - RH is the equality of that form with the same-point Hilbert norm, and their gap is an exact line-reflection
     defect [Lean].
   - The corpus shows that same-point clocks are not produced by explicit formulas [Lean].
   - The field asks for arithmetic identities and bounds for same-point zero sums (§7).

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
| Deninger: canonical big-Witt Frobenius exists; conformal Hodge positivity does not constrain the spectrum; five further no-gos | [Lean docstrings] `DeningerResolventCoreIsRiemannHypothesis` and the big-Witt no-go modules |

**Reading (inference).** At fixed overlap, selection at complete resolution is already settled: W is positive
definite and its ground line is the pole (§1.2). The atomic ladder shows what the pole selects against: the next rung
is conductor 2. A selective question survives only along growing overlap, as persistence of the pole ground line with
its energy E_1(1 + o(1)). That statement is positivity, so it is Σ1 in selective form.

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
| Two-prime Cesàro carrier (labels 2, 3, both reflection orientations, multiplicities kept): its source excess converges to O(T). An absolute bound below 2 proves RH; a normalized o(N(T)) bound does not | [Lean] `XiHorizontalCollisionTwoPrimeCesaroCarrier` |
| The excess is exactly the mean-square cost of quotienting the coefficient-faithful carrier by line reflection | [Lean] `XiHorizontalCollisionPrimeCayleyInformationLoss` |
| The Ward–Green normalized source energy dominates 16 times the canonical reflection charge; an absolute bound below 32 proves RH | [Lean] `XiHorizontalCollisionWardGreenCayleyQuantum` |
| Exterior source carrier with off-line quantum 4(96/145)², coefficients from an explicit prime–Gamma source formula | [Lean] `XiHorizontalCollisionWardGreenExteriorSourceCarrier` |
| Summability of the multiplicity-faithful Gauss–Hodge prime current ⇔ RH | [Lean] `riemannHypothesis_iff_forall_summable_horizontalCollisionGaussHodgePrimeCurrent` |
| **Growth dichotomy**: the explicit-formula clock χ_p(ρ)² is holomorphic. Its excess vanishes on all-critical windows and is unbounded on any window with an off-line zero. "The quantum margin of two exists only on the zero-indexed side" | [Lean] `XiHolomorphicTwoPrimePencilGrowthDichotomy` |
| Constraints on any collision observable: (1) orientation is preserved or lost by transport, never created; (2) oriented displacement cancels under exchange, and only the squared displacement survives; (3) no scalar reporter exact on collisions is sequentially lower semicontinuous, so collision-stable additive weights are linear in multiplicity; (4) even readers lose the first jet at anti-phase collision | [Lean] (1) `PairwiseFirstCoalescenceLaw`, (2) `XiHorizontalCollisionExchangeOrientationNoGo`, (3) `XiHeatCassiniWoldOrbitChargeLowerSemicontinuousCollisionNoGo`, (4) `evenReader_firstJet_zero` |
| Resolvent mass is one quarter of the squared Hilbert distance between a resolvent evaluation and its line reflection, i.e. the gap between the Hilbert norm and the Weil form. Source closure contains the defect, but "an additional source law must force the two reconstructed orientations to agree" | [Lean] `XiResolventLineReflectionDefect` |
| CGL packets cannot carry two reflected points; the Prop 4.6 envelope is ≥ 288 against the quantum 2 | [Lean] `ChenGuptaLiHorizontalCollisionNoGo` |
| Census frames: double critical zeros and coalesced pairs share `extremalDiag` | [Lean] `BreakingTheCoalescenceBlindSpotAndThreeQuarters` |
| ShallowCauchy: (α/log T)E_{α/log T} + R_deep = O_α(N(T,2T)); Σ m_j² ≤ C T log T for shallow off-line zeros | [Lean docstrings] `ShallowCauchyImplications` |

**Reading (inference).** Census, the CGL merger and RH all ask for the same kind of input: an arithmetic bound on a
reflection-faithful source carrier.

- RH needs an absolute bound below a quantum.
- The census needs an N-normalized one, because N₀ ≥ N − O(T).
- The CGL merger needs reflection charge below the same quantum 2.

The corpus has built the carriers and proved the constraints any carrier must meet. For the two-prime pencil it has
proved that the clock the explicit formula produces has no finite quantum. The open item is a source law that bounds
a carrier with a quantum.

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

### M3. A source law for a quantized carrier (coalescence, census, RH)

- **Target.** An arithmetic bound on one of the HC carriers:
  - the two-prime Cesàro carrier, below 2;
  - the Ward–Green normalization, below 32;
  - the exterior carrier, below its quantum.

  For the census: an N-normalized bound with constant < 1/4.
- **Constraints the corpus imposes [Lean].** Orientation must be kept upstream of every transport step. Exchange
  symmetry must be broken by a source label or an ordered structure; the ordered-prime cross curvature
  `XiHorizontalCollisionOrderedPrimeCrossCurvature` is a corpus instance. Collision-stable scalar weights are linear
  in multiplicity.
- **Obstruction [Lean].** For the two-prime pencil, explicit formulas produce the holomorphic clock, whose excess has
  no finite quantum. A producer must evaluate the same-point (holomorphic × antiholomorphic) carrier, or a carrier
  whose quantum survives source realization (§7).

### M4. A J² signed saving on integer-power meshes (Π, quasi-RH)

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

---

## 3. Q2: wildly different approaches

| Framework | What the corpus proves | Producer status |
|---|---|---|
| Quantization (HC) | RH ⇔ O(T) < 2; carriers with prime labels, Cayley phases, Ward–Green weights | Quantum exists only zero-side for the two-prime pencil [Lean] |
| Theta-Hawking scattering | RH ⇔ real backreaction resonances, ⇔ all-pass winding rigidity, and further endpoints | Endpoints |
| Heat / resolvent Hankel | RH ⇔ heatHankel a P P ≥ 0; RH ⇔ resolvent Hankel forms nonnegative; Λ is the extinction time of the Weil index | Endpoints |
| JAS | Positive at dressing 2; RH ⇔ JasDressedPSD 1 ∧ quasi-RH | Gap from dressing 2 to 1 |
| Herglotz | Full-cone Weil positivity ⇒ Herglotz positivity of the Weil function on Re s > ½. Carrier rigidity for stable self-reciprocal Dirichlet polynomials. The centered prime-tail carrier preserves the divisor but not positivity | Herglotz positivity is the endpoint |
| Theta completeness | RH ⇔ density of real-zero jets; explicit annihilator off the line | Endpoint; the producer would be domination rigidity |
| ThetaCusp fibre form | Square plus null Lagrangian at every center; size eight at every aperture by certificates. The lawful degree-twelve flux has one-sided tail debt | Finite-rank identities; no uniform flux bound |
| Deninger big-Witt | Canonical Frobenius; conformal positivity is spectrum-blind | No-go |

Sources [Lean]:

- `riemannHypothesis_iff_forall_horizontalCollisionCharge_lt_two`, `XiHolomorphicTwoPrimePencilGrowthDichotomy`
- `riemannHypothesis_iff_thetaCuspHawkingBackreactionResonances_real`, `riemannHypothesis_iff_heatHankel_nonneg`,
  `riemannHypothesis_iff_forall_xiResolventHankelForm_re_nonneg`, `WeilIndexExtinctionTime`
- `jasDressedPSD_two`, `riemannHypothesis_iff_jasDressedPSD_one_and_quasi`
- `herglotzWeilPositive_of_weilPositiveFull`, `exists_zero_stableDirichlet_riemannZeta_ne_zero`,
  `CriticalCenteredPrimeTailEntireCarrier`
- `ThetaEndpointHarmonicCompleteness`
- `ThetaCuspCenterTailSquareFlux`, `ThetaCuspOddFourRankEight`, `ThetaCuspDegreeTwelveFluxBoundary`
- `DeningerResolventCoreIsRiemannHypothesis`

**Reading (inference).** The one form in the table that differs in kind from positivity is quantization. RH becomes
an O(1) statement with margin 2 instead of a sign at zero margin. The corpus has located its obstruction precisely:
explicit formulas produce reflection-paired or holomorphic clocks, and the quantum lives on the same-point clock. An
approach that does not touch the walls would have to compute same-point zero sums arithmetically. That is the content
of §7.

**Not recommended.** More endpoints of the theta-Hawking type: they add reformulations without a producer.

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

1. Treat the J² saving (M4) as the detector-independent target. The meshes m = 5 (4/5) and m = 4 (3/4) lie below the
   detector floor 29/36.
2. Inside the detector, find which CGL lemma fixes κ = 2 before choosing a lever. The 5/6 condition
   κ + 4ν ≤ 4/3 concerns the large-values term of the packet Gram.
3. A CGL merger with reflection structure must meet the HC constraints of §1.5 first. The no-go rules out finishing
   S₂/S₃ as a route.
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
critical zero (`coalescence_law`). The corpus gives three exact routes:

- Route I needs zero-side slack ≥ N/12.
- Route II needs a pair-correlation surplus ≤ 1/18 at λ = 4/3.
- Through the HC inequality N₀ ≥ N − O(T), an eventual bound O(T) ≤ N/4 gives 75 % with multiplicity, and
  O(T) ≤ 3N/10 gives 70 %.

The third route turns the census into an N-normalized estimate on the same carriers that RH needs at absolute
precision. That makes the census the natural first test of any HC source law (M3). The 70 % shallow-Cauchy step is
proved O_α(N); it needs ≤ 3N/20.

---

## 6. Q5: three questions to focus on

### Question 1 (Σ): signed payment at growing overlap

Can the non-ratio form, the pole moments and the archimedean shell deficit of the complete form be bounded jointly,
with sign, so that the reserve cost drops from C c⁹ to a c⁻⁷·O(log c)? Equivalently: can the negative-vector defect
bound drop from C c¹⁶ to O(log c)?

- **Why.** The c¹⁶ is the ratio c²/δ² produced by two absolute-value payments (§1.2). The card's open items
  (confinement, weighted residual) become polynomial once the defect is logarithmic.
- **First step.** The bound on the span of conductors m ≤ Q (M1), with M1b for the residual weights.

### Question 2 (Γ): the pole ground line along growing overlap

Does the complete matrix keep exactly one eigenvalue below (E_1 + E_2)/2, equal to E_1(1 + o(1)) and with eigenline
converging to the pole vector, along c_N = (log N)^α for some α > 0?

- **Why.** This is the selective form of Σ1. At fixed c it is a theorem.

### Question 3 (HC): a source law for a quantized carrier

Is there an arithmetic bound on one reflection-faithful carrier that is
- N-normalized with constant < 1/4 (census 75 %), or
- absolute and below its quantum (RH)?

- **Why.** Census, the CGL merger and RH reduce to this. The carriers and the constraints are built.
- **Known obstruction.** For the two-prime pencil the explicit-formula clock has no finite quantum.

**Runner-up.** The J² signed saving for the m = 4 power-mesh covariance (M4), i.e. the 3/4 strip.

---

## 7. Q6: the new field. Hilbertian explicit formulas

### 7.1 The gap the field addresses [Lean]

- (inference) The Weil quadratic form is a reflection-paired zero sum: it pairs ĝ at a zero with ĝ at its line
  reflection.
- The resolvent mass is exactly the gap between that form and the same-point Hilbert norm. RH ⇔ the two agree on every
  nonnegative resolvent carrier (`XiResolventLineReflectionDefect`).
- The HC quantum lives on a same-point clock, holomorphic × antiholomorphic at ρ. The explicit formula produces only
  the holomorphic clock, whose excess has no finite quantum (`XiHolomorphicTwoPrimePencilGrowthDichotomy`).
- (inference) A route that ends at a quantized endpoint therefore needs an arithmetic evaluation of same-point zero
  sums, while the explicit formula supplies reflection-paired ones.

### 7.2 Objects

1. Same-point zero sums Σ_ρ m_ρ F(ρ)\overline{F(ρ)} for source-built F, against their reflection-paired companions
   Σ_ρ m_ρ F(ρ)\overline{F(1 − ρ̄)}.
2. Reflection-faithful carriers: the two-prime Cesàro carrier, Cayley-phase carriers, Ward–Green and exterior carriers.
3. The line-reflection defect as a quadratic form on sources.
4. Source labels and ordered structures that break exchange symmetry, such as ordered prime clocks.

### 7.3 Principles (from corpus no-gos)

1. Orientation is carried from the source and never reconstructed downstream (`PairwiseFirstCoalescenceLaw`).
2. Exchange symmetry is broken by data beyond an unlabelled pair (`XiHorizontalCollisionExchangeOrientationNoGo`).
3. Collision weights are linear in multiplicity (`XiHeatCassiniWoldOrbitChargeLowerSemicontinuousCollisionNoGo`).
4. No even reader is used at an anti-phase collision (`evenReader_firstJet_zero`).
5. Bounds are stated at the quantum: absolute for RH, N-normalized for the census.

### 7.4 Acceptance criteria

1. Produces a same-point zero sum from arithmetic data for at least one nontrivial carrier.
2. Over 𝔽_q, reproduces the agreement of the same-point and reflection-paired forms from Frobenius eigenvalues of
   modulus √q.
3. Fails for Beurling systems with an off-line zero and for the Liouville twin.
4. Recovers N₀ ≥ N − O(T) and gives a census constant.
5. Unconditional Lean statements with every input discharged.

### 7.5 First theorems

1. For one carrier, an identity expressing the same-point sum as the reflection-paired sum plus an explicit source
   term. The defect is then a source quantity.
2. An N-normalized bound on that source term with constant < 1/4.
3. The 𝔽_q calibration.

### 7.6 Relation to the corpus

The Σ1 tools (conductor floors, residuals, reserves) are being built in CACT, CAF and RAPT, and the field does not
replace them. Its chapters exist:

- HC carriers and endpoints (RHTower `XiHorizontalCollision*`);
- reflected-channel geometry and collision no-gos (HTGeometry, RHTower);
- the resolvent line-reflection defect;
- the census frames (ACS).

What the field adds is the target these chapters share: arithmetic access to same-point zero sums. The searches run
for this review surfaced no module that supplies it.

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
  - Deninger modules
- **Π:** `ArithmeticHarmonicAnalysis/`, `RHTower/ThetaEndpointHarmonicCompleteness`.
- **Coalescence:**
  - RHTower: `XiHorizontalCollisionChargeEndpoint`, `…TwoPrimeCesaroCarrier`, `…PrimeCayleyInformationLoss`,
    `…WardGreenCayleyQuantum`, `…WardGreenExteriorSourceCarrier`, `…GaussHodgePrimeCurrent`,
    `…OrderedPrimeCrossCurvature`, `…ExchangeOrientationNoGo`, `XiHolomorphicTwoPrimePencilGrowthDichotomy`,
    `XiHeatCassiniWoldOrbitChargeLowerSemicontinuousCollisionNoGo`, `XiResolventLineReflectionDefect`,
    `PrimeBurnolMixedReflectedCollision`, `SourceHorizontalGammaSixTameReaderTransgression`
  - HTGeometry: `PairwiseFirstCoalescenceLaw`, `ReflectedChannelProjectiveFlow`
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

**Corpus searches** (`scripts/formal_tools.py research`), one per claim checked:

- Σ1 and Γ: complement coercivity; graded reserves; successor shell norms; uniform quasimodes; negative eigenvector
  pole coordinate; pole index of the complete matrix; ground eigenline at growing overlap; weighted conductor
  residuals; effective confinement; packets with the horizon-decay residual; shrinking atomic schedules.
- Coalescence and §7: confluent channels; coalescence-stable indices; terminal recovery after coalescence;
  even-reader first jets; HC source carriers; pre-divisor source laws; normalized collision census; prime-side
  bounds for oriented collision observables.
- Other frameworks: ThetaCusp flux at every size; Herglotz carriers from Euler data; power-mesh covariance tools.
