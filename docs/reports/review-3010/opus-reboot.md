# Opus reboot: what the Lean corpus says when nothing is assumed

Status: 30 October 2026, corpus working tree on `3ad5dbf37a`. **RH is open.** No builds, no axiom audits,
no web searches. Sources: the 58 programme entries of `docs/reports/research-programmes.md` (all READMEs read),
Lean statements, docstrings and proofs in `formal/GaloisForLFunctions`, and the corpus search tool. The
review-3010 reports were read for orientation only; nothing below rests on them.

Facts log (one fact per line, each with its Lean anchor): [`opus-reboot-facts.md`](opus-reboot-facts.md).

| Label | Meaning |
|---|---|
| **[L]** | Lean declaration, statement or module docstring read for this report |
| **(inference)** | This report's interpretation; the derivation is given |

---

## 0. The answer in brief

1. **The corpus has stopped being an estimation problem without saying so.** Every unconditional
   forcing theorem in it has one shape: positivity, an exact self-dual identity (Poisson, theta, the
   functional equation) and an integer give a rigid object. Every failed route failed at an estimate.
   The obstacle summaries list walls; the Lean corpus has *proved* what the walls are.

2. **The walls are one proven fact: the Weil cone has at most one point.** Any real weight
   `lam : ℕ → ℝ` that makes the full Weil functional nonnegative equals `Λ` on `n ≥ 2`, with no
   hypothesis on `lam` or on `ζ` (`RHTower.WeilSpectral.eq_vonMangoldt_of_weilPositiveFull`) [L].
   Selection (Γ) and precision rigidity (Π in its positivity form) are this theorem. Zero margin (Σ)
   comes from the object that proves it (§3.1).

3. **That theorem was proved on the modular surface.** Its proof is a minimum principle for a
   stream equation on the half fundamental domain of `SL₂(ℤ)` (`twistedArcMinimumPrinciple_holds`).
   The principle produces a test whose autocorrelation vanishes at every `log n` and whose transform
   vanishes at every zero of `ζ`. That test is a null vector of *every* candidate Weil form at once
   [L]. It is the only global, unconditional theorem about the Weil cone in the corpus, and it uses
   neither primes, nor estimates, nor anything resembling Frobenius.

4. **RH has a prime-free form in the corpus.** RH ⇔ the archimedean + pole part of the Weil functional
   is nonnegative on every nonnegative combination of autocorrelations that vanish at every `±log n`
   (`riemannHypothesis_iff_primeBlindPositive_unconditional`) [L]. Sharper still, RH ⇔ the archimedean
   symbol `Re ψ(¼ + ir/2) − log π` integrates nonnegatively against such combinations of zero total
   pole mass (`riemannHypothesis_iff_zeroPoleBlindPositive`) [L]. No prime, no `Λ`, no Euler product
   and no zero appears. The only arithmetic left is the node set `{log n}`.

5. **The primes are an output.** Under RH the archimedean energy needed to realize a node vector `v`
   is `Σ Λ(n)v_n`: `Λ` is the shadow price of the node `log n` in an archimedean minimization problem
   (`nodeValue_eq_vonMangoldtPairing`) [L]. The integers themselves are forced by positivity plus
   Riemann's theta law (`measure_eq_of_measureTheta_relation`) [L]. The pole weight `1` is forced by
   positivity (`eq_one_of_weilPositiveFull`, level windows squeezing to `{1}`) [L].

6. **None of this appears in the review-3010 reports.** None of them cites prime-blind positivity, the
   twisted arc minimum principle, cone uniqueness or the node value function. The "wildly different
   route" of the obstacle summary (§2.4, classify the crystalline partners of `log ℕ`) is already
   classified in the corpus. Beurling theta rigidity makes the convex set it asks about a single point
   (`eq_riemannPrimeMeasure_of_beurling_theta_relation`). Cone uniqueness leaves only `Λ` among weights
   with a positive partner. What remains is RH.

7. **What it hints at (inference).** Weil's 𝔽_q proof is the wrong template, and the corpus says
   precisely why. Over 𝔽_q there is no archimedean place: blind tests have uniform periodization, no
   test can be blind and vanish at every zero, and the Weil-positive weights form a large convex set
   (all positive measures of mass `2g` on the circle). Geometry over a family of curves applies. Over
   ℤ the archimedean place and the functional equation produce a universal null vector and shrink the
   cone to a point. There is no family to argue over. So the archimedean place is not the subsidy to
   remove (APT's framing); it is the source of the rigidity. A proof must be a rigidity or existence
   argument built on the archimedean–modular structure (Poisson, theta, `SL₂(ℤ)`), with the primes
   recovered at the end.

8. **Where to look.** The proved half of the problem (uniqueness) and the open half (existence) are
   the two sides of one linear program with no primes in it. The half that was won was won by
   potential theory on `SL₂(ℤ)\ℍ`, the one place in the corpus where the two selective structures meet.
   Those structures are the integer successor (`T: z ↦ z + 1`) and the functional-equation inversion
   (`S: z ↦ −1/z`). The first place to look is the open half, attacked with the same kind of tool
   (§6 D1).

---

## 1. How the corpus was read

- **Phase 1–3 (collection).** All programme READMEs, in the order of `research-programmes.md`. For every
  structural claim that recurs across programmes, the Lean source behind it was read: the RHTower
  prime-blind layer (`WeilConeUniquenessUnconditional`, `TwistedArcMinimumPrincipleProof`,
  `TwistedArcN1Reduction`, `TwistedArcGenerator`, `TwistedArcMomentPositiveRH`,
  `WeilConeXiDivisibleBlindTest`, `WeilFullConeOneSidedCriterion`, `ArchimedeanPoleValueFunction`,
  `ArchimedeanNodeValueFunction`, `WeilPoleWeightWindow`, `PrimeBlindFiniteLevelFarkas`,
  `PrimeBlindPoleWeightLevelWindow`, `PrimeBlindNonnegativeConeReduction`,
  `PrimeBlindPoleCriticalZetaDefect`, `BlindArchimedeanNodeTwoCertificate`), APD (Hecke states,
  affine induction, theta rigidity), AOT (lattice balance), RHTower off-line models
  (`PoleOrderTwoRealStray`, `EntireFunctionalEquationOffLine`), RHTower `InfiniteSymmetry`, ACT
  (harmonic identity).
- **Phase 4 (interpretation).** Questions put to each mechanism: why it holds, what it uses, what
  happens if one ingredient changes. The answers are in §3 and §4. The forest is in §5.
- **Not done.** No compilation and no audit of anyone's modules. Theorem names cited in this report were
  checked to exist in the source tree; their statements were read, not re-proved.

---

## 2. What the corpus has established

### 2.1 The arithmetic of ℤ is an output of the archimedean place

| Theorem [L] | What is forced | From what |
|---|---|---|
| `measure_eq_of_measureTheta_relation` (APD) | a positive measure on `[1,∞)` is `c·Σ_k δ_{k+1}`, the integers | positivity + Riemann's theta law |
| `eq_riemannPrimeMeasure_of_beurling_theta_relation` (APD) | a Beurling prime measure is `Σ Λ(n)/log n·δ_n` | the theta law |
| `completedPositiveSystem_one_iff` (SBWF) | a completed positive system of pole order one is `ℝ^×·ζ` | height positivity + FE + simple pole |
| `eq_vonMangoldt_of_weilPositiveFull` (RHTower) | a Weil-positive weight is `Λ` | Weil positivity alone |
| `eq_one_of_weilPositiveFull`, `exists_level_forall_abs_sub_one_lt` (RHTower) | the pole weight is `1` | Weil positivity; level windows squeeze to `{1}` unconditionally |
| `zeroPoleBlindPositiveOn_iff` (BSU) | the node set must contain every prime power (removing `log 4` is fatal, removing `log 6` is free) | positivity on a node set |
| `nodeValue_eq_vonMangoldtPairing` (RHTower, under RH) | `Λ(n)` = marginal archimedean energy of node `log n` | archimedean energy minimization |
| `boundary_forcing_law` (MPG) | `ζ(1 + it) ≠ 0`; dropping any of (N), (Z), (S), (I) admits a boundary zero | PD + integer divisor + simple pole + isolation |

Positivity, the Gamma factor, the functional equation and a simple pole determine the integers, the
von Mangoldt weights and `ζ`. APD states the shape itself: "Everything the corpus has forced about ζ
has one shape: positivity + an exact self-dual identity + an integer ⇒ rigidity" [L].

### 2.2 RH without primes

- **Prime-blind positivity (PBAP).** `PrimeBlindPositive`: for every finite nonnegative combination
  of autocorrelations `k_f` whose symmetric values vanish at every `±log n`, `n ≥ 2`, the pole and
  archimedean part is `≥ 0`. "No prime enters" (docstring) [L].
- **Duality.** `exists_weilPositiveFull_iff_primeBlindPositive`: the Weil cone is nonempty ⇔ PBAP. This
  is the M. Riesz extension / finite feasibility theorem [L].
- **Equivalence.** `riemannHypothesis_iff_primeBlindPositive_unconditional` [L].
- **Zero-pole form.** `riemannHypothesis_iff_zeroPoleBlindPositive`: on blind combinations of total pole
  mass zero, the functional is the archimedean symbol alone [L].
- **Finite levels.** At level `L` (tests in `[−L, L]`) only nodes `log n < 2L` are visible, and Farkas
  is exact (`levelBlindNonneg_iff_exists_weights`, `levelFloors_eq_levelMargins`). RH ⇔ every level
  window of admissible pole weights is nonempty
  (`riemannHypothesis_iff_forall_level_exists_mem_levelWindow`). The windows are compact intervals that
  squeeze to `{1}` [L].
- **One node.** RH ⇔ for one node `m`, the least archimedean energy carrying `+1` at `log m` plus the
  least carrying `−1` there is `≥ 0` (`riemannHypothesis_iff_nodeFibre_add_neg_nonneg`) [L].
- **Spectral reading.** For blind `f` the prime-blind energy is
  `(1/π)∫|𝓜f(½+it)|²(θ'(t) + 1 − Re ζ(½+it))dt`. Violators concentrate on large values of `|ζ|` on the
  line (`pole_ge_of_blind_secondMoment`) [L].
- **Nonnegative tests.** A nonnegative blind function has positivity set of measure `≤ log 2`, and
  quantile transport reduces PBAP on it to one archimedean window `(0, log 2)`
  (`weilArchRe_nonneg_of_primeBlind`). That window inequality is proved unconditionally on `(0, 12/25)`,
  69% of `(0, log 2)` (`windowPositive_twelve_twenty_fifths`) [L].

### 2.3 The walls are a theorem about one point

| Wall in the reports | What the Lean corpus proves | Anchor [L] |
|---|---|---|
| Σ: positivity at zero margin | The Weil cone has no interior: it is `{Λ}` or `∅` | `weilPositiveFull_iff_riemannHypothesis_and_eq_vonMangoldt` |
| Γ: selection at the trivial gauge point | Every weight other than `Λ` (every twin, flip, mixture, `Λ + εn^{−η}`) leaves the cone | same; `exists_negIndex_towerKernel_ne_zero` (HKT) |
| Π: square-root precision (positivity form) | Tower positivity has stabilizer `{0}`; the count has stabilizer the square-root class | `towerIndexZero_add_iff`, `count_add_iff_mem_sqrtClass` (ASRP) |

(inference) The three walls of positivity routes are not three missing estimates. They are three
consequences of one proved shape: the feasible set of the problem is at most a point. A method that
needs room cannot work, and the corpus proves there is no room. §3.1 shows where the point comes from.

### 2.4 Every unconditional global theorem is an exact identity, mostly of Poisson type

| Mechanism | Positivity it produces | Anchor [L] |
|---|---|---|
| Minimum principle on the modular half-domain | Weil cone `⊆ {Λ}` | `twistedArcMinimumPrinciple_holds`, `HTGeometry.le_of_halfDomainStreamMinimum` |
| Fejér pairing + Poisson | integers from the theta law | `measure_eq_of_measureTheta_relation` |
| Möbius collapse + Poisson over the shift lattice | complete Weil matrix PD at every fixed overlap, energies `E_m(c) ≥ 0` | `hasSum_completedConductorEnergy`, `eventually_noRealZero_completeWeilMatrix_posDef` |
| Cyclotomic norm `≥ 1` + AM–GM | conductor-uniform curvature floor `A_m(t)/φ(m) ≥ {t}(1−{t})` | `CyclotomicNormGivesAConductorUniformCurvatureFloor` |
| Unique factorization | the lattice odd ledger is balanced (no frustration) | `isBalanced_lattice` |
| PD + integer values | sign characters; `ζ(1+it) ≠ 0` | `intValued_posDef_iff_signCharacter`, `boundary_forcing_law` |
| Fekete (roots of unity) | torsion is the stable log-energy equilibrium | `sum_sum_log_norm_sub_le` |
| Commensurability index | Hecke states on Aff(ℚ) PD exactly from `s = ½` | `isPosDefOnGroup_heckeState_iff` |
| Farkas / M. Riesz / Hahn–Banach | RH ⇔ prime-free feasibility; `Λ` as shadow price | `exists_weilPositiveFull_iff_primeBlindPositive`, `nodeValue_eq_vonMangoldtPairing` |

None of these spends a margin, and none uses an estimate of a prime sum.

### 2.5 Every failure is an estimate

Depth homogeneity: amplification gains on depth exactly what it pays in length (AKT
`norm_productResponse_le`). The rank law: orthogonal families cancel their gain at rank `π(x)` (ART).
Producers are precision-blind (`producers_are_precision_blind`). Absolute shell payment costs `c²/ε`
and gives the `c¹⁶` confinement (SSh anatomy). Gauge-invariant data stop at `3/4`
(`threeQuarters_le_of_gaugeInvariant_bound`). Holomorphic carriers are rigid
(`eq_weilWeight_of_calibrated`). Positive parts never pay a hyperbolic pair
(`negIndex_add_pairKernel_eq_one`). Each is a theorem about what an estimate cannot do.

### 2.6 ℤ versus 𝔽_q: one difference, the rank of the value group

Every place where the corpus compares the two traces back to `log|𝔽_q(T)^×| = ℤ·log q` (rank one,
discrete) against `{log p}` independent over ℚ (rank ∞, dense):

| Phenomenon | Over 𝔽_q | Over ℤ | Anchor [L] |
|---|---|---|---|
| Comb coercivity | uniformly coercive lattice comb | defeated by concentrated tests | ACT-comp mech. 12 |
| Kronecker rank of zeros | 1: defect 0 or ∞ | ∞ | ACS |
| Frobenius progressions | places of one degree share one | each prime has its own; vanishing costs `N − ⌊N/p⌋` | `finrank_divisibleLT_eulerFactor`, `finrank_sections_eq` |
| Parity twin | a vertical shift, `(−1)^{deg}` at every place | a shift is `−1` at ≤ one prime; twin only in the Bohr closure | `shiftChar_eq_neg_one_subsingleton` |
| Twist tower | base changes complete the count | every prime has degree one; levels ≥ 1 invisible | `unitary_iff_twistTower_upper`, `twistLevel_mem_sqrtClass` |
| Mertens / pole vector | exact eigenvector, ceiling `N log q` | ceiling `log N − γ`; `γ` is the archimedean defect | `atomFq_nonneg_iff` |
| Amplifier rank | `2g` | `π(x)` | ART rank law |
| Square-root cancellation | a count, `|Σχ(x)ψ(x+1)|² = q` | at each finite level a count; uniformity at the arithmetic point open | `norm_sq_charSuccCorr`, AET |

Rank ∞ also helps. Two primes carry the whole index (`negIndex_orbitKernel_twoPrime`). Positivity on
infinitely many prime towers forces index zero (`negIndex_eq_zero_of_posDef_on_infinitely_many_towers`).
`ζ`'s growing zero density is what makes fixed-overlap positivity possible: a tempered single off-line
pair fails at every overlap (`isolatedPairConfig_atomic_negative_every_ratio`) [L].

---

## 3. Taking the proofs apart

### 3.1 Why the Weil cone is a point

Read from `WeilConeXiDivisibleBlindTest` and `WeilConeUniquenessUnconditional` [L]:

1. The modular minimum principle produces an (N1) object `F`. Its autocorrelation vanishes at every
   `log n`, `n ≥ 2` (prime-blind). Its transform vanishes at every zero of `ζ` (Ξ-divisible) and is
   nonzero elsewhere on ℝ.
2. For **every** weight `lam`, the prime sum of `W_lam(F)` is zero, so `W_lam(F) = A(F) = W_Λ(F)`. Its
   zero side is `Σ|F̂(γ_ρ)|² = 0`. So `F` is a null vector of every candidate form at once.
3. If `W_lam ≥ 0`, its null vector lies in its radical: `W_lam(F, g) = 0` for all `g`. Since
   `W_Λ(F, g) = 0` as well (Ξ-divisibility), `Σ(lam − Λ)(n)ℓ_n(F, g) = 0` for all `g`. Because `F̂` vanishes
   nowhere else, these pairings separate the nodes, and `lam = Λ`.

(inference) Zero margin and uniqueness are one phenomenon. The universal null vector makes the
infimum zero and pins the weights. The corpus's Σ (no margin) and Γ (only `Λ` works) are both caused
by a single modular object.

**What if there were no such object?** Over 𝔽_q the node set is the lattice `ℤ·log q`. A test blind at
every nonzero multiple of `log q` has spectral measure whose periodization mod `2π/log q` is constant
(Poisson). Such a test cannot vanish at every translate of a zero angle while being nonzero. So no (N1)
object exists, and the Weil-positive weights form the large convex set `curve_rh_tfae` describes:
positive-definite trace sequences, i.e. positive measures on the circle with mass `2g` (inference
from the APD and HKT statements). The 𝔽_q problem has room. Weil's argument applies to a whole
family, and the actual curve is one member that geometry places inside the cone.

### 3.2 Why the critical exponent is ½

Three unconditional theorems put ½ in place without any zero:

- **Hecke–Bessel law.** A PD function on Aff(ℚ) with integer successor obeys
  `nd·|φ(dilation u)|² ≤ 1` (`integer_successor_hecke_weight`). Hecke states `(nd)^{−s}·1[db ∈ ℤ]` are PD
  iff `s ≥ ½` (`isPosDefOnGroup_heckeState_iff`). "The integer successor costs exactly half a unit of
  exponent" [L]. (inference) `nd` is the commensurability index of `ℤ` and `uℤ`, so ½ is the Hecke
  normalization: the critical line is the unitary axis of the ax+b Hecke pair.
- **Kakutani.** The prime Poisson measure is absolutely continuous w.r.t. Haar on the prime torus iff
  `s > ½` (`heckeState_kakutani_wall`) [L].
- **ℓ² thresholds.** Cell budgets `n^{−1/2}·n^{−1}` are summable exactly above ½ (BSU). Horizon-limit
  commutation and sign-blind payment hold exactly from damping ½ (`horizonLimit_commutes_with_receiver_iff`,
  `parity_barrier`). The coefficient tail from exponent `r+1` is summable iff `r ≥ 2`
  (`CriticalEulerCoefficientMassStartsAtCubes`) [L].

(inference) ½ is where square-summability against the integers begins. The boundary of the critical
Wiener algebra `W_{1/2}` (AOT: `μ_ε` is a unit iff `ε > ½`), the Hecke unitary axis and the Kakutani
threshold coincide. RH asks the zeros
to sit on this structural boundary. The corpus explains the boundary; it does not explain the zeros.

### 3.3 Why positivity holds at every fixed overlap and not beyond

- On a Ramanujan conductor mode a successor shell of shift `h` acts by `c_m(h)`. Möbius collapse
  `c_m(h) = Σ_{d|(m,h)} μ(m/d)d` and Poisson summation over each `dℤ` turn the shell symbol into a
  coprimality indicator:
  `E_m(c) = (2/(Mφ(m)))Σ_{(a,m)=1}(m/a)∫_{ac/m}^∞ |φ̂(2πt)|² ≥ 0` (`hasSum_completedConductorEnergy`) [L].
- The source of the conductor energies is one exact identity:
  `Σ_{a|n} Λ(a)c_m(n/a) = log n·c_m(n) − J_m(n)`, with
  `J_m(m) = φ(m)(log m + tameDifferent(m))` (`TheDownwardPrimeRowIsAnExactLogarithmicDivisorJet`).
  That is `Λ ⋆ 1 = log`, read on additive characters [L].
- The continuum average of the shells is exactly the pole charge. Only the integrality of the shift
  repays `log c` (`exists_overlap_all_nonpolar_reference_energies_negative`) [L].
- The conductor spectrum has heat threshold `Σ_m e^{−βE_m} < ∞ ⇔ β > 1` and `E_m/log m → 1`
  (`summable_completedConductorHeatWeight_iff`, `tendsto_completedConductorEnergy_div_log_one`) [L].

(inference) At fixed overlap the Weil form is a positive Hamiltonian diagonal over the torsion orbits of
the circle (conductors), with energies `≈ log m`. Its partition function has the threshold `β = 1`, the
same threshold APD meets as the Bost–Connes temperature (`bc_successor_hecke_exponent`). The lattice
`{log n}` is rigid, and the rigidity pays. Growing overlap is the passage to the archimedean continuum.
There the modular null vectors of §3.1 become visible and the margin `E_1(c) ≍ c^{−7}` tends to zero.
The Σ1 route approaches the rigid point from the lattice side.

### 3.4 Why the lattice is balanced and the continuum is not

On positions `log a`, a crossing (prime-sum) relation `ab = p^k` forces `a = p^i`, `b = p^j`. The pair is
then also a ratio pair with larger weight: `Λ(p^{i+j})/√p^{i+j} ≤ Λ(p^{|i−j|})/√p^{|i−j|}`
(`primeKernel_log_add_le`). Unique factorization removes every frustrated cycle. Between lattice points
a sum `x + y = log n` forces nothing, and the prime triangle at half-integer positions has frustration
index 2 [L]. (inference) Arithmetic structure (unique factorization) is a source of positivity on the
lattice. The difficulty is entirely in the continuum, the archimedean place.

### 3.5 Why selection comes only from the pole, the Gamma factor and the successor

- Weil positivity is closed under pointwise convergence of weights. Every unitary completely
  multiplicative twist is a pointwise limit of vertical shifts (Kronecker). So any statement on the
  weights that is closed and holds for all shifts holds for every twin (`liouvilleTwin_mem_of_isClosed`,
  `flip_mem_of_isClosed`) [L].
- Hence selectivity lives in the terms that do not move with the weights, the pole and the Gamma factor
  (AKLT). The only other source is additive structure: non-ratio lags, the successor, cells (SSHA, AGT,
  RBG). The trivial point is the only gauge point compatible with addition (`eq_one_of_eventually_periodic`).
  Catalan `{1, 2, 3, 4}` is the minimal gauge-fixing plaquette (`catalan_holonomy_two`) [L].

(inference) The two selective structures are the additive translation by integers and the archimedean
place with its functional equation. Read on the upper half-plane these are `T: z ↦ z + 1` and
`S: z ↦ −1/z`, the generators of `SL₂(ℤ)`. The twisted arc witnesses need exactly these two conditions:
integer Fourier blindness `∫h'(x)sin(2πmx)dx = 0` for `m ≥ 2`, and inversion `h(1/x) = |x|h(x)`
(`exists_decayClass_fullLineWitness`) [L].

### 3.6 Why Λ-positive functions with the exact FE can leave the line

`F(s) = ζ(s)((s − ½)² − w²)/(s(s−1))` has nonnegative generalized von Mangoldt measure, the exact FE, an
entire order-one completion and real zeros `½ ± w`, at pole order two. Its correction density
`(e^{u/2} − e^{wu})(e^{u/2} − e^{−wu})` is continuous (`PoleOrderTwoRealStray`) [L]. (inference) Every such
model leaves the discrete node set `{log n}`. For continuous support the blind cone is trivial, and PBAP
says nothing. Discreteness of the node set is what makes the prime-free formulation non-vacuous. Pole
order one is what the cone-uniqueness theorem needs (pole weight forced to 1).

### 3.7 Why the archimedean symbol alone is not enough

`BlindSymbolSlack(−γ(0) − 2)` holds unconditionally: blindness at node 2 alone improves the anomaly
`γ(0) ≈ −5.37` by 2. `BlindSymbolSlack M` fails for every `M ≤ 0`. RH ⇔ `ZeroPoleBlindSymbolSlack M`
for every `M > 0` (`BlindArchimedeanNodeTwoCertificate`) [L]. (inference) On the blind cone the symbol
keeps a definite negative part of size at most `3.37` per unit mass, and the pole constraint must remove
all of it. RH in this form is a statement about how the single pole constraint interacts with blindness
to `{log n}`.

---

## 4. What-if questions

| What if … | The corpus answers [L] | Where it leads (inference) |
|---|---|---|
| the weight is perturbed by `δ ≠ 0` at one node? | It leaves the cone (`not_weilPositiveFull_vonMangoldtSingleIndexPerturbation_of_ne_zero`) | Positivity is exact in every coefficient; no estimate with tolerance can prove it |
| the pole weight is `β ≠ 1`? | No weights work beyond some level; windows squeeze to `{1}` | The residue is forced by positivity; it is not an input |
| the node set loses `log 4` (a prime power) or `log 6`? | Fatal at `log 4`, free at `log 6` (`zeroPoleBlindPositiveOn_iff`) | The node set is the prime powers; it is forced by the theta law |
| the prime measure has a continuous part? | Off-line zeros at pole order 2 (§3.6) | Discreteness and pole order one are the selective inputs |
| there is no archimedean place (𝔽_q)? | Lattice nodes, exact Mertens, coercive comb, `γ` disappears (`atomFq_nonneg_iff`) | No universal null vector; the cone is large; geometry over a family works |
| only nonnegative tests are allowed? | One archimedean window `(0, log 2)`, proved to `12/25` | A purely archimedean inequality, finite and prime-free |
| overlap is fixed? | PD, spectrum = conductor energies, ground line = pole | Lattice rigidity with margin |
| overlap grows like `(log N)^{1/4}` (tilted spline) or `(log log N)(log log log N)^β` (Steklov)? | RH (`riemannHypothesis_iff_completeWeilEnergy_nonneg_of_growthTwo`, `riemannHypothesis_iff_steklovDCProfile_nonneg_superGevrey`) | The continuum limit is where the null vectors live |
| only finitely many off-line zeros are asked for? | LH-deep; local data give index 0 or ∞ (`negIndex_localAssembly_eq_top`) | Finite index is not a weaker local problem |
| one wants a deformation family, as over 𝔽_q? | Positive deformations at pole order one: none (`simple_pole_nonneg_laplace_refund_rigidity`); chirality | ζ is isolated; arguments over a family have no family |
| a same-point (Hilbert) formula replaces the explicit formula? | No holomorphic weight computes it (`eq_weilWeight_of_calibrated`) | Same-point data need non-holomorphic or modular input |
| one wants Frobenius on ℤ? | Bounded-defect ring endomorphisms are the identity or gauge points (`approxRingEndomorphism_classification`); `x^q = x` lives on the gauge torus as Adams fixed points; `0` is the unique fixed twist of `ψ²` (`isAdamsFixed_two_iff`) | The "Frobenius" of ℤ is not a map of ℤ |

---

## 5. The forest

### 5.1 A rigidity problem, not an estimation problem

The obstacle reports describe RH as three walls a missing input must cross with zero margin, square-root
precision and selectivity. The Lean corpus proves something stronger and different:

- the feasible set of Weil-positive weights is at most a point (cone uniqueness, unconditional);
- the point, if it exists, is `Λ`, and `Λ` is the shadow price of an archimedean energy problem on the
  node set `{log n}`;
- RH is the statement that the point exists, and that statement has a form with no primes in it.

(inference) Positivity proofs with margin cannot exist; this is a theorem, not a pattern. Estimates are
the wrong instrument for a point-feasibility question. The instruments that do work on point-feasibility
questions are the ones the corpus has used successfully: exact identities, duality and extremal
principles. That covers Poisson and theta rigidity, Farkas, and minimum principles.

### 5.2 Three layers, and where the theorems come from

| Layer | Objects | What the corpus proves there |
|---|---|---|
| Multiplicative | primes, `Λ`, Euler products, the gauge torus, Hecke dilations | Blindness: gauge-invariant, precision-blind, twin-blind, depth-homogeneous. Selection is impossible here (ACG, BGG, AKT, ART). |
| Additive lattice | integers, successor, Bézout, Ramanujan sums, torsion orbits, cyclotomic integers | Exact positivity at bounded overlap: Möbius collapse, cyclotomic norm floor, lattice balance, conductor Hamiltonian (RAPT, CACT, AOT, TMWP). |
| Archimedean–modular | Gamma factor, pole, theta, FE, `SL₂(ℤ)\ℍ` | Global rigidity: theta rigidity, cone uniqueness, pole weight `1`, Hecke normalization ½, the prime-free form of RH (APD, RHTower PBAP layer). |

(inference) The prime-free form of RH lives entirely in the second and third layers: the node set `{log n}`
(the integers), the archimedean symbol and the pole. The first layer appears only as the answer. The
corpus spent most of its effort in the first layer, where it proved that nothing can be found.

### 5.3 Why the 𝔽_q template fails, and what the right template looks like

Weil's theorem over 𝔽_q is a statement inside a large convex cone: positive measures on the circle of
mass `2g`. The actual curve is placed inside by geometry (Hodge index on `C × C`) or by a count
(Stepanov, which needs `x^q = x`). The corpus has checked every layer of that argument over ℤ
(ACS, AOG, ACP, AET, AIT, AKLT, ALG):

- the identities (Lefschetz, adjunction, Rosati, budget `δ(x,x)`) transfer and hold on the golden datum,
  so they cannot place a point;
- the placing tools (Riemann–Roch on the surface, Frobenius, the twist tower, Stepanov's flatness) have no
  ℤ-analogue, and the corpus proves each absence (`thetaEffectivity_not_riemannInequality`,
  `approxRingEndomorphism_classification`, `twistLevel_mem_sqrtClass`, `le_one_of_dvd_choose`).

(inference) Over ℤ the cone is not large. The question is not "is ζ inside a big cone?" but "is the unique
candidate point feasible?". The template that fits is the one the corpus itself used for the half it
proved: a duality (Farkas: feasible ⇔ no blind certificate of negative energy) plus an extremal principle
on the archimedean–modular side (minimum principle on `SL₂(ℤ)\ℍ`). This is the shape of a linear
programming bound with a modular extremal object, not of an intersection-theoretic positivity.

### 5.4 `SL₂(ℤ)` is generated by the two selective structures

The corpus identifies exactly two sources of selection (§3.5): additive translation by integers, and the
archimedean place with its functional equation. On the upper half-plane they generate `SL₂(ℤ)`. The only
unconditional global theorem about the Weil cone was proved on `SL₂(ℤ)\ℍ`, from a minimum principle for
`y(Z_xx + Z_yy) − Z_y = 0` with wall, cusp and arc conditions (`HTGeometry.le_of_halfDomainStreamMinimum`)
[L]. Its witnesses carry the two selective structures and nothing else: integer Fourier blindness and
inversion symmetry. The divisor transfer `logNode_blind_of_fourier_vanishes` converts additive integer
blindness into multiplicative `log n` blindness [L].

(inference) Here the comparison of `+` and `×` that the reports search for (`S = W`, theta versus primes)
is realized as a theorem: Poisson summation over the integers plus inversion produces exactly the
prime-blind objects that pin `Λ`. A minimum principle propagates a sign from the boundary without spending
a margin. Among the corpus's positivity instruments it is the one that reached a global statement.

### 5.5 The open routes in this light

| Route family | Reading (inference) |
|---|---|
| Σ1 complete Weil matrix (RAPT, CACT, TMWP, SSh, CAF) | Approaches the point from the lattice side. Fixed overlap is lattice rigidity with margin. Growing overlap meets the modular null vectors, so the margin must vanish. The signed shell payment (Q1 of the summary) is the lattice-to-continuum transfer. |
| Index (HKT, AKLT, EAHT) | The index counts hyperbolic pairs. Finite index is LH-deep. The point-feasibility reading says index zero is attained only at the cone's single point. |
| Same-point (HEF, CDG, APol, AES) | `S` is computed from theta prefixes, `W` from primes. Their equality is the existence half seen through the zero side. |
| Counting producers (ASRP, AET, AKLT) | Integrality is exact at the floor; precision is lost in Möbius inversion. A producer is a primal construction of the point, the hardest possible route. |
| Gauge and selection (ACG, AGT, BGG, SMAP, ACountP) | Proved that selection must come from the pole, Gamma and the successor: the two `SL₂(ℤ)` generators. |
| PBAP layer (RHTower) | The prime-free core. Uniqueness is proved; existence is RH. Missing from the review-3010 reports. |

---

## 6. Where to look

Each direction says what to prove first, why the corpus points there, and what it must survive.

### D1. The existence half on the modular side (first priority)

- **Target.** Prove `PrimeBlindPositive`, or `ZeroPoleBlindPositive`, or a level-window statement, with the
  instrument that proved cone uniqueness: potential theory on `SL₂(ℤ)\ℍ`.
- **Why.** It is the open half of the only linear program in the corpus that contains no primes. Its other
  half was won exactly this way. The PBAP data (blindness at `{log n}`, the archimedean symbol, the pole
  constraint) are the `T` and `S` data that the modular surface carries.
- **First theorems.**
  1. Derive the blind cone from modular objects in the other direction: blindness at every `log n`
     ⇒ integer Fourier vanishing plus inversion, the converse of `logNode_blind_of_fourier_vanishes`.
     This would identify the blind cone with a cone of functions on the half-domain.
  2. A modular-potential proof of `WindowPositive` on all of `(0, log 2)`: the nonnegative blind cone,
     purely archimedean, numerically certified to `12/25`.
  3. A minimum principle whose conclusion is nonnegativity of the archimedean symbol on one nontrivial
     signed blind family, for example the arc witnesses themselves with a sign-changing arc measure.
- **Battery.** Over 𝔽_q the blind cone is periodic and no (N1) object exists: the construction must
  degenerate there. Continuous-support Λ-positive models make the blind cone trivial: the construction must
  use discreteness. Pole order two models must fail: the construction must use pole weight one.

### D2. An uncertainty principle for blind measures on the prime torus

- **Target.** A positive measure `μ` on ℝ with `∫n^{it}dμ = 0` for every `n ≥ 2` and zero pole mass must
  charge `{γ > 0}` (roughly `|t| ≳ 6.3`) at least as much as `γ`'s negative part. This is RH
  (`riemannHypothesis_iff_zeroPoleBlindPositive`).
- **Why.** Pushed to the prime torus, blindness says the Fourier coefficients vanish on the positive orthant
  `ℕ^P∖0` and its negative. Mixed-sign frequencies (ratios `m/n`) are free. This is a Bohr–Helson question
  about one-sided spectra, and the corpus owns the tools: `isPosDefOnGroup_posUnits_iff`, the critical
  Wiener algebra, Kronecker density, Baker separation.
- **First theorems.** Quantitative spread: blind measures have `∫min(|t|, T₀)dμ ≥ c·mass`. The
  `node-N` slack sequence `c_N` (blindness at nodes `≤ N`) generalizing the node-2 gain of 2 in
  `BlindArchimedeanNodeTwoCertificate`. Its limit compared with `−γ(0)`.
- **Must survive.** The Fejér barrier (pointwise certificates are capped at `a₁ ≤ 2a₀`). Use measures,
  not pointwise minorants.

### D3. `Λ` as a shadow price

- **Target.** Study the archimedean value function `V(v)` on node vectors directly: its domain, its
  subdifferential at `0`, its behaviour on finite node sets as the level grows. RH ⇔ `V` is finite at one
  point ⇔ `V` is linear with gradient `Λ`.
- **Why.** It turns the primes into derived quantities of a convex problem over the archimedean place. Any
  structural property of `V` that holds unconditionally (convexity is free; finiteness is RH) is a
  property of the archimedean place alone.
- **First theorem.** An unconditional description of `V` restricted to the nodes `log n < 2L` at level `L`,
  for example monotonicity of its level restrictions or a formula for its asymptotic cone.

### D4. The level windows as finite problems

- **Target.** RH ⇔ every level window is nonempty. At a fixed level, nonemptiness is weaker than
  positivity of `ζ`'s own form at that level, since the weights are re-chosen (inference from the
  definitions). A proof may construct weights `w_L ≠ Λ` with `w_L → Λ`.
- **Why.** It replaces "ζ is positive" by "some object with ζ's archimedean data, pole weight near 1 and
  nodes `{log n < e^{2L}}` is positive at level `L`". Objects with known real zeros and the same Gamma
  factor are natural candidates.
- **Caution.** The windows are nested and decreasing, so the extension no-go (`extension_forces_positivity`)
  still forbids monotone continuation in `L`. A construction must be level-by-level.

### D5. Bring Σ1 under the same roof

- **Target.** Identify the conductor Hamiltonian at fixed overlap (energies `≈ log m`, threshold `β = 1`)
  with the archimedean–modular objects, and describe the growing-overlap limit as convergence toward the
  modular null vectors.
- **Why.** It would explain why the margin `E_1(c)` must vanish (inference §3.3), and it would tell the
  signed shell payment which vectors to avoid: the ones that approximate (N1).
- **First theorem.** Compute the complete Weil energy of the truncated (N1) object on atomic families at
  overlap `c`, as a function of `c` and `N`. This is the explicit null direction of Σ1.

---

## 7. What the corpus says is not the way

- Any estimate that spends a margin: the cone is a point (§2.3).
- Multiplicative-only constructions: gauge orbits, Beurling-universal (ACG, BVI, THIM class I).
- Explicit formulas with holomorphic weights for same-point data (HEF calibration rigidity).
- Amplification over ℤ by families or tensor powers: depth homogeneity and the rank law (AKT, ART).
- A Frobenius on ℤ: bounded-defect endomorphisms are trivial (AGT).
- Counting producers by divisibility: parity-blind, capped at simple vanishing above `√N` (AKLT).
- Local constituents: positive definite up to the identity term, twin-invariant, index 0 or ∞ on finitely
  many places (AKLT).
- Pole-order bookkeeping of zeros: counts inserted charge exactly and intrinsic charge not at all (APD,
  SBWF).
- Finite-aperture or bounded-overlap certificates as evidence: window-determined, weight-blind below
  `log 2/2` (ASRP, SSIC).

---

## 8. Questions this reading raises

1. Is the blind cone exactly the cone of modular objects on the half-domain? That is, is there a converse of
   the divisor transfer?
2. Does the twisted arc minimum principle have a dual whose conclusion is a lower bound on the archimedean
   symbol rather than the existence of a null vector?
3. Over 𝔽_q, what replaces the half-domain? Is the degeneration of the modular construction (no (N1) object,
   a large cone) itself a theorem one can state and use as calibration?
4. Is the conductor Hamiltonian of the complete Weil matrix the restriction of a modular operator? Its
   threshold `β = 1` and APD's Hecke exponent suggest the Bost–Connes pair; the corpus has not tested this.
5. What is the smallest node set and the weakest archimedean datum for which cone uniqueness still holds?
   The answer marks exactly what rigidity uses.
6. Can the shadow-price characterization of `Λ` be computed level by level unconditionally, giving
   `Λ(m)` from the Gamma function at finite level with an explicit error that vanishes only under RH?
7. Why is the prime `2` both the bottleneck of the selective margin (`2 log 2`, the conductor-2 rung) and the
   first node whose blindness improves the archimedean anomaly by 2? Over `𝔽_q[T]` the window width
   `(q/(q−1))log q` equals `2 log 2` at `q = 2` (AKLT §9.7).

---

## Evidence

**READMEs read (all 58 entries, 53 distinct programmes):** APT, BSU, THIM, BVI, ACT, SRT, AIP, ACCE, SSIC,
ACT-comp (ACCC), ACS, SAEI, TTPC, AOT, AOG, ALDG, SSA, ADR, BG, MPG, APD, SBWF, ACG, AKT, ACP, APol, AET, BGG,
CDG, SPTL, AES, AIT, RAPT, RBG, SSHA, ALG, IGP, AID, SAHT, SMAP, ACountP, HKT, AKLT, ASRP, CACT, TMWP, EAHT, AHA,
HEF, SSh, ART in full. CAF: first half and the clock, spectral-band and research sections. AGT: question,
mechanisms, pillars and status table. ShallowCauchyPrimeEnergy has no README; its module list was read.

**Lean modules read beyond docstrings or statements:** RHTower `WeilConeUniquenessUnconditional`,
`TwistedArcMinimumPrincipleProof`, `TwistedArcN1Reduction`, `TwistedArcGenerator`, `TwistedArcMomentPositiveRH`,
`WeilConeXiDivisibleBlindTest`, `WeilFullConeOneSidedCriterion`, `ArchimedeanPoleValueFunction`,
`ArchimedeanNodeValueFunction`, `WeilPoleWeightWindow`, `PrimeBlindFiniteLevelFarkas`,
`PrimeBlindPoleWeightLevelWindow`, `PrimeBlindNonnegativeConeReduction`, `PrimeBlindPoleCriticalZetaDefect`,
`BlindArchimedeanNodeTwoCertificate`, `PoleOrderTwoRealStray`, `EntireFunctionalEquationOffLine`,
`SelfReciprocalBoundaryDensity`, `InfiniteSymmetry/*` (6 modules); APD
`TheCriticalLineIsThePositivityThresholdOfTheIntegerSuccessor`, `AffinePositivityIsInducedFromTheDilations`,
`PositiveMeasureHamburgerRigidity`; AOT `TheLatticeOddLedgerIsBalanced`; HTGeometry
`ModularHalfDomainStreamMinimumPrinciple` (statement).

**Theorem names checked to exist in the tree:** every name cited in §2–§4, including
`hasSum_completedConductorEnergy`, `eventually_noRealZero_completeWeilMatrix_posDef`, `boundary_forcing_law`,
`completedPositiveSystem_one_iff`, `riemannHypothesis_iff_nodeFibre_add_neg_nonneg`,
`nodeValue_eq_vonMangoldtPairing`, `eq_one_of_weilPositiveFull`, `riemannHypothesis_iff_one_positive_square`,
`isGreatest_zeta_hyperplaneGap`, `exists_level_forall_abs_sub_one_lt`,
`riemannHypothesis_iff_forall_level_exists_mem_levelWindow`, `zeroPoleBlindPositiveOn_iff`,
`approxRingEndomorphism_classification`, `isAdamsFixed_two_iff`,
`exists_overlap_all_nonpolar_reference_energies_negative`,
`riemannHypothesis_iff_completeWeilEnergy_nonneg_of_growthTwo`, `extension_forces_positivity`,
`coalescence_law`, `atomFq_nonneg_iff`.

**Corpus searches (`scripts/formal_tools.py research`):** Weil cone uniqueness; prime-blind positivity of
the archimedean pole functional; modular fundamental domain minimum principle and stream functions; Hecke
state threshold on the affine group; harmonic theta span and the Riemann kernel; curve-datum calibration
of the blind cone; modular-surface positivity and theta cusp; `isBalanced_lattice`; `WindowPositive` (all
window results); prime-blind finite-level and pole-weight results.

**Report check:** a search of `docs/reports/review-3010/*.md` for "prime-blind", "primeBlind", "blind
positiv" and "twisted arc" returns no match.
