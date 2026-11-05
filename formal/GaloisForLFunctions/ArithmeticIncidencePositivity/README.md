# Arithmetic Incidence Positivity (AIP)

Namespace `GaloisForLFunctions.ArithmeticIncidencePositivity`; umbrella `ArithmeticIncidencePositivity.lean`
(76 modules). Base objects (ω, atoms, gauges, zero form, Weil functional) come from `RHTower` and
`ArithmeticCriticalityTheory` (ACT); do not redefine them.

---

## 1. Motivation

The zero form of ζ in a gauge is a **jump form**: Z(Φωu) = J_M(u) + V_μ(u), M = Φω, μ = M sinh(x/2)
(ACT `zeroForm_phiDoob_mul_eq_signedJump_add_varianceEnergy`). Read pair by pair it is a weighted graph
on ℝ whose edges carry archimedean density ω, prime atoms Λ(n)/√n at distance log n, and the polar
weight. AIP asks: **on which pairs is the conductance negative, how large is the negative part, and what
in the arithmetic of the integers pays it?** Every statement names the pairs it concerns. The global
version of the question is RH (`riemannHypothesis_iff_globalIncidenceAllocation`); AIP's work is to
settle it locally, measure exactly how far local payment globalizes, and identify the residue.

---

## 2. Objects

| Object | Meaning | Lean |
|---|---|---|
| ω, atom | archimedean density ω(t) = 1/(4sinh(t/2)) + 1/(4cosh(t/2)); Λ(n)/√n | `RHTower.archLevyDensity`, `vonMangoldtAtom` |
| Pair kernel | k(x,y) = dm(|x−y|) + 2sinh(x/2)sinh(y/2); archimedean part, crossing symbol S(s) = cosh(s/2) − ω(s) | `archPairKernel`, `crossingSymbol`, `crossingThreshold` |
| Lattice atoms | ratio Λ(b/a)/√(b/a), product Λ(ab)/√(ab), net = ratio − product | `ratioAtom`, `productAtom`, `netAtom`, `skeletonEnergy` |
| Polar weight | P_s(a) = 2sinh(a/2)sinh((s−a)/2) = cosh(s/2) − cosh(s/2 − a) on crossing pair (−a, s−a) | `crossingPolarWeight` |
| Collars, moduli | collar {P_s < ω(s)}; five moduli {2,3,4,5,7}; nine moduli {2,3,4,5,7,8,9,11,13} | `antiDiagonalCollar`, `atomDominatedModuli`, `totalDominatedModuli`, `unpaidSet` |
| Plateau gauge | P = 1 on [−r,r], 0 off (−R,R) | `aperturePlateau`, `plateauPotentialFloor` |
| Strip, odd part | S_n = [log n − r, r]; α(a) = (F(a) − F(log n − a))/2 | `reflectedOddPart`, `stripBoxEnergy` T(p,r), `stripSurplus` |
| Surplus kernel | k(x,y) = ω(|x−y|) − ω(x+y) ≥ 0 (same-side minus crossing partner) | `surplusKernel` |
| Ledger pieces | pool 2S_P, crossing potential 4∫F²Π_P, even gain 2(Λ/√n)∫_{S_n}F², odd cost 4(Λ/√n)∫_{S_n}α², gauge remainder, pole charge 2(∫F sinh(x/2))² | `surplusPool`, `crossingPotentialTerm`, `evenStripGain`, `oddStripCost`, `gaugeRemainder`, `poleCharge` |
| Joint cost | Σcost − Σgain + pole | `reflectedPrimePolarCost`, `incidenceBudget` |
| Translate calculus | ⟪A,B⟫ = ∫AB; A(t) = ∫F(x)F(x+t); trains | `testPairing`, `autoCorrelation` (ACT `autoCorr`, definitionally equal), `translateComb`, `geoTrain` |
| Tower charge | C_p = log p Σ_k p^{−k/2}A(k log p) | `towerCharge`, `geoLagCharge`, `primeSideCharge` |
| Lag ledger | prefix of a source in lag s = log x; two-pole weight w(s) = e^s + s − 1; E(s) = w(s) − ψ(e^s); receiver D(s) = ∫₀^s(e^u − ψ(e^u)) | `lagPrefix`, `lagSourceDefect`, `chebyshevTwoPoleDefect`, `criticalScalePrefix` |
| Spectral | |F̂|²; symbol Σw cos(2πaξ); polar kernel K_T | `spectralDensity`, `lagSymbol`, `primeSymbol`, `coshCosKernel` |
| Euler comb | F − λF(·+a), weight w = 2λ/(1+λ²) | `eulerStep`, `eulerComb`, `eulerPayment`, `eulerMultiplier` |

---

## 3. Language

- **Same-side** pair: xy > 0; **crossing**: x < 0 < y; sum s = |x| + y; **anti-diagonal of n**: s = log n.
- In an odd gauge M(x)M(y) < 0 on crossing pairs, so **k > 0 on a crossing pair = negative conductance**.
- **Payment**: a nonnegative term ≥ a negative conductance (pointwise, integrated against a gauge, or in L²).
- **Strip** S_n: crossing pairs on anti-diagonal log n inside [−r,r]; atom n acts iff log n < 2r.
- **Window r**: odd tests supported in [−r,r]. **Light cone**: atoms with 2r − 2δ ≤ log n < 2r.
- **Source**: a weight a(n); its **defect** = calibration − prefix. ζ ↔ Λ; **receiver** = second-order defect D.
- **Resonant train**: disjoint bump copies at a progression; extremal for tower envelopes.
- **Rate σ**: deficit Ce^{2σr}∫F²; σ = ½ (e^r) is trivial (SRT `GradedIncidenceAllocation`).

---

## 4. Mechanisms

### A. Pair geometry (lattice)
1. **Crossing sign law**: k_arch > 0 ⟺ cosh((x+y)/2) > S(y−x); S increasing, root s₀ ∈ (log5, log6). Below s₀
   every crossing pair has negative conductance; beyond, only pairs within 3e^{−3s/4} of an axis.
2. **Lattice**: k_arch(−log a, log b) closed form; for a,b ≥ 2 negative only at {2,2},{2,3}; axis pairs
   (a = 1) always negative; reflected pairs only a = 2. With atoms: exactly {2,2},{2,3},{2,4},{3,3}
   (`totalLatticeCrossingKernel_pos_iff`).
3. **Dominance**: product pairs lie on one tower; `productAtom a b = ratioAtom a b / a`; skeleton = nonnegative
   Laplacian; net pair conductance > 0 for all 2 ≤ a < b (`totalLatticeNetKernel_pos`).
4. **Windows**: in (X/2, 2X) divisor relations are ×2, ×3; crossings (p^i,p^{i+1}), p ∈ {2,3}, atom < 2log3/X.
   Across windows: multiplier band Y/(4X) < m < 4Y/X, ratio atoms < 2log(4Y/X)√(X/Y), crossings ≤ (2/X)·ratio;
   partial-matching Schur bounds.

### B. Polar compensation (continuum)
5. **Anti-diagonal**: k_arch = ω(s) − P_s(a). P vanishes at axes, peaks 2sinh²(s/4) at midpoint. Collar sandwich:
   inner end ω(s)/sinh(s/2) ≈ 2e^{−s}, second-order ratio c/ℓ = 1 + e^{−s} + O(e^{−2s}); unpaid archimedean
   mass O(e^{−3s/2}); off collars the variance pays the archimedean crossing energy for every profile.
6. **Atom vs pole, pointwise**: atom beats P everywhere ⟺ n ∈ {2,3,4,5,7} ⟺ (√n−1)² < 2Λ(n); with ω added
   ⟺ n ∈ nine moduli; otherwise unpaid set = two axis intervals of inner end 2Λ(n)/(n−1); quarter point paid
   ⟺ n ∈ {10,12} ∪ [14,∞) \ {17}.
7. **Atom vs pole, integrated against gauges** (three tiers): all positive log-concave gauges pay ⟺
   n ∉ {2,3,4,5,7,11,13}; first-jet log-concave (log(M/x) concave) ⟺ n ∉ {2,3,4,5,7,11}; shifted ground states
   m_a (double-exponential midpoint concentration, explicit thresholds) ⟺ n ∉ {2,3,4,5,7}. On {2,3,4,5,7}
   every nonnegative gauge leaves a deficit; their only interior lattice crossing (2,2) sits where the jump
   vanishes ⇒ they must be paid by ratio atoms (4/3, 3/2, 5/4, 7/5) and shared surplus.

### C. Odd fold, surplus, window certificates
8. **Fold**: every archimedean crossing conductance is paid by its same-side partner at the same distance,
   leaving killing 4F²(Ω(x) − Ω(x+r)) (Ω = ∫_y^∞ω); exact at every aperture:
   J_P(F) = 2S_P(F) + 4∫F²Π_P (`archJump_eq_two_mul_surplus_add_crossingPotential`).
9. **Ground-state transform** of the surplus in polynomial gauges (closed forms: odd gauge parts meet the
   reflected pole ⇒ logarithms that cancel the killing logarithm; even parts ⇒ polynomials); second-order ω
   expansion; Schur lending moves potential between rectangles (origin hub, strip hub).
10. **Micro-fold Harnack**: the atom acts only through α (∫FF(·+L) = 2∫_Sα² − ∫_SF²): the even part is a GAIN.
    Strip surplus pays α with constant → 2 (regional log kernel 1/(2|x−y|), linear odd ground state); every
    prime-power atom (Λ/√n ≤ 2/e) is paid by its own strip for ½log n < r ≤ ½log n + 1/12. Variants: shell
    (nested strips), wide (exact rates), harmonic (shared band), even-part interpolation.
11. **Odd-part wall**: near r = log2 no box payment by α alone exists (linear profile: quotient 12 − 16log2 + …
    < √2 log2) ⇒ the even part / outside surplus is mandatory.
12. **Certified odd windows** (Ẑ(F) ≥ c∫F², full form incl. pole): 7/25 (1/40), 17/50 (1/100), 347/1000 (first
    prime paid, 1/100), 7/20, 353/1000, 356/1000, 9/25, **181/500 = 0.362 (1/1000)**. Prime-only joint Harnack
    for atoms 2, 3: 221/400 and **23/40** (pole not paid there).

### D. Strip allocation
13. Strips share the edge r and are nested; summing Harnack bounds double counts. Union and telescoping chain
    allocations; shell needed for {23,25}. **Light cone** shares one surplus copy at width δ ≤ c₀e^{−r}
    (Selberg sieve + one proper prime power per exponent) and fails cofinally at δ = Ce^{−r}, C ≥ 64000:
    **square-root scale is exact**. Shared surplus has **logarithmic capacity**
    (7/(10log6))log(1/(12ε)) ≤ Cap(r,ε) ≤ 2log(4/ε) + 84.
14. **Edge tents** (width ε at the edge) zero every thin-band atom yet each odd part is ½∫F²: odd-part sharing
    cannot globalize; **bipolar dipole** keeps all thin-band products ≥ 0 and still beats one surplus copy:
    keeping even parts does not save band sharing. Global allocation: light cone from surplus, every other
    atom charged to its strip mass (`tsum_primeShift_le_globalAllocation`).

### E. The ledger at every aperture
15. **Incidence ledger** (identity): Ẑ(F) = pool + crossing potential + Σgain − Σcost + gauge remainder − pole;
    remainder purely archimedean ≥ −(27/5)∫F²; Ẑ = incidenceBudget − reflectedPrimePolarCost.
16. **Joint cost = Chebyshev pairing**: rate-1 prime and polar terms cancel identically:
    cost = ∫₀^{2r}E(s)·2e^{−s/2}(A′ − A/2) = −∫(D + s²/2 − s)w″, D + s²/2 − s = ∫₀^sE; second-order factor is
    the correlation of the pole-tilted derivatives F′ ± F/2.
17. **Sizes**: pole ≤ (2sinh r − 2r)∫F² (sharp); bipartite halving |A(t)| ≤ ½∫F² for t ≥ r (odd);
    |cost| ≤ (35e^r + 34e^{r/2} − 2r)∫F², PNT (3+ε)e^r; de la Vallée Poussin: Ke^{r−c√r}(∫F² + ½∫F′²) or
    pole-tilted (¼∫F² + ∫F′²). Derivative bill cannot be removed (compression F(ax)). GIA unconditional on
    (0, 181/500]; edge tents: pole ≍ ε⁴e^r outgrows stripBox + any linear budget ⇒ pole and prime channel
    cannot be decoupled.

### F. Translate calculus and towers
18. Gram identity ⟪ΣαF(·+c), ΣβF(·+d)⟫ = ΣαβA(d − c); A = cosine transform of |F̂|² (positive definite).
19. **Tower law** (p−1)C_p ≤ log p(A(0) + √pA(log p)); Liouville twin log p(A(0) − √pA(log p)); envelopes sharp
    (resonant / alternating trains) ⇒ content = fold discount and the **sign of A(log p)**. Prime powers reduce
    to primes (`fullZeroForm_ge_primeOnlyLedger`). Bi-tower law; bi-lattice train: aligned towers resonate,
    envelopes add, cross-prime aggregate > 0.
20. **Multi-shift positivity**: two-shift coupling (edge weight θ ≤ ½ exact), three-shift Gram, two-atom law
    (A(a) + A(b))² ≤ 2A(0)(A(0) + A(b−a)) (+ parity twist, weighted forms); squarefree subset forms; divisor
    Gram PSD for every modulus (Möbius row blind on resonant directions).
21. **Comb / defect coordinates**: cost² ≤ A(0)·combEnergy (diagonal + cross-prime ratio correlations);
    shifts past aperture charge ≤ ¾ (odd ½) of ℓ¹ unconditionally.

### G. Lag Chebyshev calculus (any source, any pole)
22. **Universal balance**: Σa(n)h(log n) − ∫W′h = ∫(W − prefix)h′ (first order), second order via ramp sums.
    For ζ: imbalance = ∫Eh′ = −∫(D + s²/2 − s)h″; quiet zone below log2; horizon: aperture r reads E on (0,2r].
23. **Source rigidity**: prefix ⟺ source; atoms = prefix jumps = slope kinks of D; defect cannot hide an atom.
    Among sources ≤ Λ, Λ is closest to the two-pole calibration.
24. **Calibration dictionary**: integer sources calibrate exactly poles ρ ≤ 1 (defect ≤ 1/ρ + log2; ρ > 1
    impossible); bounded defect ⇒ density e^{ρs} (exponent of density = pole position), atom in every gap,
    bounded gaps; two-pole rigidity (no source accurate at two poles); double pole not matchable. Critical
    line of pole ρ is ρ/2 (normalisation n^{−ρ/2} forced).
25. **Weil form structure**: depends only on (correlation, pole plane M₋M₊); pole plane = rank one, perfect
    negative square on odd tests at every pole; Weil form additive over even/odd parts ⇒ positivity ⟺ both
    sectors; comparing two sources cancels the pole plane.
26. **Test-geometry bounds** (all constant-factor): half law A(t) ≤ ½A(0) past aperture; ladder
    cos(π/(⌊2r/t⌋+2)); quadratic gap A(u) ≤ A(0)(1 − u²/8r²); triangle/square laws for displacement.
27. **Receiver arithmetic**: D(log(N+1)) = D(log N) + 1 − ψ(N)log(1+1/N); D sawtooth-convex; positive on first
    cells; propagation ⟺ ψ(N)/N < 1 + D(log N) (PNT with margin).
28. **Spectral form**: charge = ∫S(ξ)|F̂|²; Chebyshev pairing = 2∫(primeSymbol − 2K_{2r}(2πξ))|F̂|²; a pointwise
    symbol floor c gives pairing ≥ 2cA(0) for every test (at ξ = 0: ΣΛ(n)/√n − 4sinh r). The pole pays only on
    |ξ| ≤ 1/(8r) (and costs at ξ = 3/(8r)); odd tests put ≤ π²‖F‖₁²/(192r) there.
29. **Euler comb**: comb factor multiplies |F̂|² by 1 − w cos(2πaξ); sequential first-power payment ≤ mass for
    all weights ≤ 1 (Λ(n)/√n ≤ 2/e qualifies), strict, residual = comb energy; raw charge = mass − comb energy
    + ratio/product cross-charges (exact).
30. **Hyperbola/Möbius**: prefix of a Dirichlet convolution = translation average; Σμ(d)⌊x/d⌋ = 1,
    |Σμ(d)/d| ≤ 1, ψ(x) = Σμ(d)log(⌊x/d⌋!).

### H. Bridges
31. **Bump bridge**: single-bump archimedean self-energy ~ M(α)²∫β²·w log(1/w); off-diagonal O(w²); prime part
    O(w); after subtracting self-energies the scale-w limit is the lattice incidence form in `netAtom`.
    Lattice trains: Weil energy ≥ 0 for resolution beyond exp(O(N log N)) (not uniform in N).
32. **Crossing-to-ratio bridge**: continuum crossing priced by variance + ratio jump at log m + archimedean jump;
    near-axis crossing mass suppressed cubically (K²c³/3).
33. **Sign blindness**: complete-period sieve quadratic forms see only (ℤ/2)^{N−1} sign orbits; comb energy
    and trans-horizon readouts separate the orbit (difference 4A(log 3/2)).

### I. Selectivity
34. Shifted pair ζ(s−a)ζ(s+a): odd form negative on [−13/125, 13/125] (Hankel form of ω − 2cosh(t/2)) while ζ is
    coercive on [−21/200, 21/200]. Liouville twist: for every r ≥ 23/40 smooth odd F with W_ζ > (1/25)∫F² and
    W_{λΛ} < −(3/10)∫F²; Catalan (8,9) form has opposite signs; geometric Beurling ledgers miss ζ's calibration
    at main-term size.

---

## 5. Pillar theorems

1. Lattice skeleton positive; net pair conductance positive — `skeletonEnergy_nonneg`, `totalLatticeNetKernel_pos`.
2. Atom vs pole classifications (five / nine / seven / six moduli) — `sqrt_sub_one_sq_lt_two_vonMangoldt_iff`,
   `totalAntiDiagonalKernel_pos_forall_iff`, `forall_logConcave_collarAtomMass_lt_iff`,
   `forall_div_id_logConcave_collarAtomMass_lt_iff`, `exists_collarAtomMass_lt_collarPolarMass_shiftedGroundState_iff`.
3. Every prime-power atom paid by its own strip; odd-part wall at log2 — `two_mul_primePowerShift_le_stripSurplus`,
   `two_mul_primePowerShift_le_stripSurplus_sub_evenPart`, `not_forall_oddPart_le_stripSurplus_logTwo`.
4. Odd positivity past the first prime — `fullZeroForm_ge_of_odd_support_le_threeHundredSixtyTwoThousandths`.
5. Exact fold and incidence ledger; RH ⟺ global allocation — `archJump_eq_two_mul_surplus_add_crossingPotential`,
   `fullZeroForm_eq_incidenceLedger`, `riemannHypothesis_iff_globalIncidenceAllocation`.
6. Square-root light cone and logarithmic capacity — `exists_squareRoot_lightCone_allocation`,
   `frequently_lightConeBox_oddPart_sharing_fails_at_squareRoot`, `sum_le_of_isPayableOddPartFamily`,
   `exists_payableOddPartFamily_log_lower_bound`.
7. Joint cost is the Chebyshev pairing — `reflectedPrimePolarCost_eq_chebyshevTwoPoleDefect`,
   `reflectedPrimePolarCost_eq_criticalScalePrefix`, `testBalance`.
8. Tower laws read the sign of A(log p) — `sub_one_mul_towerCharge_le`, `sub_one_mul_twistedTowerCharge_le`,
   `geoLagCharge_resonantTrain_ge`, `geoLagCharge_alternatingTrain_ge`.
9. Source rigidity and pole calibration — `eq_of_lagPrefix_eq`, `abs_lagSourceDefectAt_idealSourceAt_le`,
   `defect_half_cell_lower_bound`, `card_ge_of_poleAt_defect_le`.
10. Spectral symbol criterion; Euler comb payment — `chebyshev_pairing_eq_spectral`,
    `chebyshev_pairing_ge_of_symbol_ge`, `eulerPayment_eq_integral_multiplier`, `eulerPayment_lt_mass`.
11. Bump bridge — `tendsto_calibratedSignedJumpEnergy_latticeBumpProfile_netAtom`.
12. Selectivity — `markovWindow_selective`, `smooth_odd_selectivity_of_ge_twentyThreeFortieths`.
13. Arbitrary-radius multi-prime dilation modulus, openness across prime-power entries, and infinite strictly increasing Weil-floor aperture tower — `fullZeroForm_dilation_bound_of_radius`, `fullZeroForm_ge_of_dilated_radius`, `weilFloorApertureTower_strictMono`, `fullZeroForm_ge_of_support_le_weilFloorApertureTower`, `zetaZeroConfig_re_W_ge_of_aperture_le_weilFloorApertureTower`.

---

## 6. Tools

**Developed (reuse, do not rebuild)**
- Pair-kernel algebra: `archPairKernel`, sign law, lattice closed forms, collar sandwich/second-order ends.
- Fold identity + surplus kernel + ground-state potential with closed-form cubic/quartic gauge integrals;
  tangent-line interval certificates on 7-smooth log anchors; Schur rectangle lending.
- Micro-fold families: `sharpMicroFold_strip_ge`, `sharpMicroFold_shell_ge`, `harmonicMicroFold_strip_ge`,
  general `foldedStrip_ge`; strip allocation `sum_primeStripCharge_le_union` / `_chain`.
- Ledger: `fullZeroForm_eq_incidenceLedger`, `fullZeroForm_ge_explicitLedgerFloor`, `incidenceBudget`,
  `poleCharge_le_two_sinh_sub_two_r_mul_sq`, `abs_autoCorrelation_le_half_of_le`.
- Translate calculus: `testPairing_comb`, `geoTrain_resolvent`, tower/bi-tower laws, train witnesses.
- Lag Abel calculus for any source and pole: `sum_weight_sub_calibration_eq_defect`,
  `sum_weight_sub_calibration_eq_rampDefect`, `testBalanceAt_source`, `genTestBalanceAt`, calibration matching.
- Spectral: `autoCorrelation_eq_integral_spectral`, `spectralDensity_eulerComb`, anti-concentration
  `mass_outside_window_ge`, odd-test origin suppression.
- de la Vallée Poussin pairing bounds (`exists_abs_reflectedPrimePolarCost_le_exp_sub_sqrt_mul_sobolev`).

**To build**
- A joint budget paying all strip masses + pole + remainder on every odd test (one inequality, not per strip).
- A lower bound on primeSymbol_N(ξ) − 2K_{2r}(2πξ) on frequencies an aperture-r test can reach, with the norm stated.
- A coherent subtraction for the cross-prime comb (Euler comb cross-charges are the candidate) with a
  Schur/ℓ² bound for the remainder.
- Gauges paying {2,3,4,5,7} through ratio atoms 4/3, 3/2, 5/4, 7/5.
- Positive windows past 23/40 that pay the pole jointly with several strips.

---

## 7. Open questions and research topics

1. **Global payment**: one budget for every odd compact test at every aperture. Odd-part routes end before
   log2; edge tents force even parts; the pole must be paid jointly with the prime channel.
2. **Rate**: deficit Ce^{2σr}∫F² with σ < ½. Unconditional: σ = ½ with PNT constant 3 + ε and dlVP factor
   e^{−c√r}. Lower the exponent, not the constant.
3. **Signed Chebyshev pairing**: bound ∫₀^{2r}E·w_F′ using cancellation between E and test curvature, not |E|.
4. **Cross-prime aggregate**: Σ_{p≠q}w_pw_qA(log(q/p)) is the single scalar carrying the exponential demand;
   positive on aligned (bi-lattice) tests. Find the right subtraction/norm.
5. **Half-power family** √p log p/(p−1): ℓ¹ exponential, ℓ² polynomial — its aggregate is open.
6. **Five moduli** {2,3,4,5,7} and the near misses 8, 9, 11, 13, 17: classify paying gauges.
7. **Windows across scales**: turn inter-window Schur bounds and light-cone capacity into a multiscale budget.
8. **Selectivity audit**: test every new positivity statement on shifted pair, Liouville, geometric Beurling.

---

## 8. Traps

| Trap | Truth |
|---|---|
| k > 0 means positive conductance | on crossing pairs it is negative conductance |
| Polar weight sinh·sinh without the 2 | every classification changes |
| Collar is always thin | below s₀ ∈ (log5, log6) every crossing pair is negative |
| Pole pays atoms near axes | P vanishes at axes; the prime obstruction is an axis phenomenon of small n |
| Five moduli = nine moduli | atom alone vs atom + ω; integrated tiers are 7 and 6 moduli |
| Midpoint comparison = payment | integrated payment depends on the gauge class |
| Summing per-strip Harnack bounds | strips are nested; allocation needed (fails for {23,25} under union) |
| Odd-part allocation globalizes | edge tents refute it; bipolar dipole refutes signed band sharing |
| Window certificates at 221/400, 23/40 are positivity | prime-only Harnack; `fullZeroForm_ge_twentyThreeFortieths_complete` still subtracts the pole |
| The ledger proves positivity | it is an identity; positivity only where certificates exist |
| `GlobalIncidenceAllocation`, D(T) ≤ B(1+T)e^{T/2}, Mertens bound | each is RH-equivalent; restating it is not progress |
| Rate ½ / dlVP results are progress on sign | they are deficit bounds with nonzero deficit |
| Oddness, support, half law, ladder, quadratic gap give power savings | constant factors only; rate stays e^r |
| Ratio off-diagonal ≤ 0, bounded Schur constant, cross ≤ 0 | replacement hypotheses (conditional); false on aligned towers |
| Comb-energy reduction bounds the cost | raw comb energy ~ 4e^{2r}A(0) (ArithmeticCompensationTheory `tendsto_combEnergy_rescaledTest_div_exp`) |
| Tower law estimates the prime side | envelope attained; only the fold discount and sign of A(log p) carry information |
| Bound E by its size | E is unbounded; use increments / curvature (gauge invariance) |
| Dilation-invariant criteria | dilation changes the source (λ-power Beurling system, pole 1/λ) |
| Lattice skeleton is the form | it is the O(w) term under the w log(1/w) self-energy |
| Header constants | read the Lean statement (`collarEnd_second_order` proves 8ℓ³, header says 14ℓ³) |

---

## 9. Context

| Direction | Programme | Link (verified imports) |
|---|---|---|
| uses | RHTower | ω, atoms, CHMD polar, Weil–Lévy pole Gauss, phiDoob, Riemann kernel bounds, Selberg sieve, PNT, ψ error |
| uses | ArithmeticCriticalityTheory | gauges, ground states, zero form, pole-free variation, window Weil positivity, Z-type law |
| uses | SquareRootThreshold | lag prime windows, aperture prime sums, graded ledger |
| uses | BiScaleUncertainty, HTGeometry | chord cascade; compact-support integration by parts |
| uses | SAEI, SelectivePositivityAndThresholdLaws, ArithmeticOrientationTheory | canonical-path calibration; Catalan two-prime separation; orientation-blind period forms |
| feeds | SquareRootThreshold (5) | window certificates, lag-window incidence, graded ledger by zero width |
| feeds | ArithmeticCriticalityTheory (4) | folded conductance, past-plastic fold, shifted-pair selectivity, atom–pole law |
| feeds | ArithmeticCompensationTheory (4) | prime comb as translation, dlVP residual, compensated ledger |
| feeds | ArithmeticCastelnuovoSeveri (3) | odd Hodge index past first prime; Riemann–Roch for ℤ via reflected ledger |
| feeds | RAPT (2), AOT (2), TTPC, THIM, SAEI, SSIC, CACT, BiarithmeticGeometry, BVI, ArithmeticIndexDescent | bump bridge, lattice law, Schur lending window, nine-modulus bridge, train witnesses, ledger unit, Chebyshev ledger |

AIP is the **incidence face** of the programme family: conductance by conductance, with the pole as the only
positive source on crossing pairs; its lag Chebyshev calculus is the common receiver language shared with
ACT, SRT, ACompT and ArithmeticIndexDescent.

---

## 10. Big picture

AIP shows that the Weil form is overwhelmingly positive **locally**. The lattice skeleton is a nonnegative
Laplacian; the pole pays the archimedean continuum except on exponentially thin axis collars; every prime-power
atom is paid by the surplus of its own reflection strip; and odd windows are certified through the first prime
up to 0.362. Positivity is also **selective**: it already distinguishes ζ from the shifted pair, the Liouville
twist and geometric Beurling systems at small apertures, so it reads zero positions, not merely Euler product,
functional equation and Dirichlet structure.

The failure is **globalization**. Strips are nested and share one surplus only inside a square-root light cone
with logarithmic capacity; odd-part allocation provably cannot cover all atoms; the pole grows like e^r and
cannot be paid separately from the prime channel. When everything is kept together, the identity
Ẑ = budget − cost collapses the whole global problem to one functional: the two-pole Chebyshev defect
E(s) = e^s + s − 1 − ψ(e^s) paired against the test's lag curvature — equivalently one spectral symbol. Every
test-geometric saving (oddness, support, half law, ladder, bipartite halving) is a constant factor; the rate
is fixed by the size of ψ(x) − x. For the RH research this means: incidence geometry can organize and localize
the problem completely, but it cannot supply the decisive input — that input is a signed, cancellation-based
estimate of the prime–polar balance at PNT precision, concentrated on multiplicatively aligned tests and on
the smallest moduli. Any route that bounds pieces separately, or by absolute values, is already ruled out here.
