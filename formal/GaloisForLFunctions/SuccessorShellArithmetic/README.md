# Successor-Shell Arithmetic (SSh)

Namespace `GaloisForLFunctions.SuccessorShellArithmetic`; umbrella `SuccessorShellArithmetic.lean`.

**Question.** The complete atomic Weil form at growing overlap is a positivity family, built on the
integers, at square-root precision, and it sees zeros at every depth. At fixed overlap it is solved:
conductor modes are quasimodes with nonnegative energies, because the *successor shells*
`n = km + h` repay the logarithmic loss of the reference energy exactly. Past fixed overlap the
corpus pays the shells in absolute value, and that payment is the whole polynomial loss `c¹⁶` in
the confinement of negative vectors. What is the signed arithmetic of the shell block for vectors
that are not conductor modes, and can it be paid at logarithmic cost?

SSh is the arithmetic of that block: the additive shift `h` and the multiplicative data `(k, m)`
meeting at the atomic scale. Everything is unconditional; RH appears only inside equivalences.

---

## 1. Motivation

**What a missing tool must be.** Corpus theorems fix the shape of any producer of RH-strength
positivity:

| Requirement | Forced by |
|---|---|
| R1. A positivity family over tests, not a single carrier | holomorphic carrier rigidity (`linearCarrier_eq_zero`, `sesquilinearCarrier_eq_zero`, `entire_vanishing_on_criticalLine_eq_zero`) |
| R2. Use of discreteness, not only `Λ ≥ 0` and the functional equation | Λ-positive models with the exact functional equation and off-line zeros (`EntireFunctionalEquationOffLine`, `LambdaPositiveFunctionalEquationOffLine`) |
| R3. Square-root precision | `negIndex_zetaKernel_eq_zero_iff_count`, `riemannHypothesis_iff_completeWeilEnergy_nonneg_of_growthTwo` |
| R4. Visibility at depth `o(1/log T)` | `coalescence_law`, `exists_depth_without_quantum` |
| R5. More than conformal positivity | `DeningerResolventCoreIsRiemannHypothesis` |

The complete Weil form `W_{N,c}` meets R1–R4 by construction: it is a quadratic form over all
coefficient vectors; its atoms sit at `log n` and its prime kernel is `Λ(k)/√k`; its nonnegativity
when `c⁴/log N → ∞` is RH; Weil positivity sees off-line zeros at every depth.

**Where the loss sits.** The proved reserve `W ≥ (δ/4)D − C(c)S`, `δ ∝ c⁻⁷`, `C(c) ∝ c⁹`
(`tiltedUnitSpline_complete_defect_reserve_explicit`) gives `D ≤ C'c¹⁶ S` on negative vectors. Its
anatomy: the archimedean part keeps only `δ/2` of the prime defect `D`; the non-ratio form and the
pole moments are each paid by Young's inequality at `ε = δ/8`, each costing `c²/ε`. The open
estimates of the growing-overlap route (effective confinement, a weighted residual over growing
conductor families) become polynomial once the defect bound on negative vectors is logarithmic.

**What SSh has settled about this loss.** The separate payment is sharp: no payment of the shells by
themselves, even one-sided, costs less than `κ c²/ε` (§5, pillar 4). At the reserve fraction
`ε ∝ c⁻⁷` that is `c⁹`. So the polynomial confinement exponent is intrinsic to paying the shells
apart from the pole and the archimedean shells. On the witness that forces the floor, the shells and
the pole cancel to `O(G(1 + log N))` (§5, pillar 6): the only way below the floor is joint, signed
payment, and it removes the obstruction there.

**Why the shells.** A shell pairs `m` with `km + h`: a multiplicative relation broken by a bounded
additive shift. On the pole vector unique factorization collapses every prime power into `log ℓ`,
so the shells see only the integer lattice (§5, pillar 4). Their repayment is Poisson summation over
the shift lattice `ℤ`, and the whole logarithmic repayment is carried by the unit gap between the
ratio pair `h = 0` and the first shell (§5, pillar 2). That is a use of discreteness of exactly the
kind R2 demands.

---

## 2. Objects

Fix a `C²` profile `φ` supported in `[0, 1]`, `M = ∫φ²`, `q = (∫φ)²/M`, autocorrelation
`G(u) = ∫φ(v)φ(v + u) dv`, spectrum `P(t) = |φ̂(2πt)|²`. Horizon `N`, overlap ratio `c`, atom width
`w = c/N`, atoms `a_n = φ((· − log n)/w)` for `1 ≤ n ≤ N`, atom autocorrelation `β = β_w`,
coefficients `x`, mass `S(x) = Σ x_n²`.

| Object | Meaning | Lean |
|---|---|---|
| Complete Weil form | `W_{N,c}(x) = weilQuad(Σ x_n a_n)/(wM)` = archimedean − ratio − shells + pole | `completeWeilMatrix`, `completeWeilEnergy` |
| Ratio block | `P_N(x) = 2Σ_{mt ≤ N} Λ(t)t^{−1/2} x_m x_{mt}` | `atomicWeilForm` |
| Prime defect | `D(x) = Σ_{mt ≤ N} Λ(t)(x_{mt} − x_m/√t)²`: the multiplicative Dirichlet energy of the pole relation | `poleDefect` |
| Pole vector | `b_n = n^{−1/2}`, ground state of `P_N` | `poleVector` |
| Successor shell | a triple `(k, m, h)`, partner `n = km + h`, `h ≠ 0`; `h = 0` is a ratio pair | — |
| Shell lag, shell form | `shellLag_{k,h}(x) = Σ_{n = km+h} x_m x_n β(log k − log(n/m))`; `Sh_h = 2Σ_k Λ(k)k^{−1/2} shellLag_{k,h}` | `shellLag`, `shellForm` |
| Shift range | `H = ⌊N(e^w − 1)⌋`, the shifts `0 < |h| ≤ H` | `shellRange`, `shellShifts` |
| Non-ratio form | `NR = Σ_h Sh_h` | `nonRatioForm` |
| Archimedean shells | the overlap pairs `(n, n + h)` of the archimedean pairing (`k = 1`) | overlap matrix of `completeWeilMatrix_eq_decomposition_at_every_overlap` |
| Convolved source | `y = Λ_w ⋆ x`; a shell pairs `y(ℓ)` with `x(ℓ + h)` | AGT `truncConv`, `primePairForm_eq_convolved` |
| Top band | `T = {n ≤ N : N e^w < 2n}`: partners of shells that are never bases | `topBand` |
| Pole row | `R(n) = Σ_{ℓ ≠ n} b_ℓ Λ_N(ℓ) β(log ℓ − log n)`, prime-free (`Λ_N(ℓ) = log ℓ`) below overlap `N log 2` | `shellPoleRow`, `shellPoleRow_eq_log` |
| Conductor mode | `u_m(n) = c_m(n)/√(φ(m) n)`, normalized by `√log N` | `ramanujanPoleProfile`, `normalizedRamanujanHorizonVector` |
| Shell coefficient | the Ramanujan sum `c_m(h)`, period average of `c_m(ℓ)c_m(ℓ + h)` | `ramanujanLagCoefficient` |
| Shell weight | `F_c(h) = ∫_{h/c}^1 G(u)/u du`: the top-band average of the `h`-th shell | `shellSum`, `shellCorrection` |
| Reference energy | `E_m^ref(c) = log(1/(2πc)) + β(φ)/M + log m + τ(m) − γ + [m = 1]cq` | `completeWeilAdjunctionEnergy` |
| Completed conductor energy | `E_m(c) = E_m^ref(c) − (2/(Mφ(m)))Σ_{1≤h<c} c_m(h)F_c(h) ≥ 0` | `completedConductorEnergy` |
| Continuum completion | the shell sum with the integer shift replaced by `h ∈ (0, c)` | `continuumShellSum`, `continuumShellEnergy`, `continuumConductorEnergy` |
| Lattice gain | actual minus continuum energy: what the integrality of `h` pays | `latticeGain` |
| Twin shell | the shell of a sign gauge `ω`, weighted by the successor disagreement `1 − ω(km)ω(km + h)` | `twinShellForm` |

---

## 3. Language

*Shift* `h`, *dilation* `k`, *base* `m` of a shell. *Top band*: the atoms near the horizon, the only
partners of shells; the shift `h` needs a partner `n ≥ |h|/(e^w − 1) ≈ |h|N/c`. *Ratio block*:
everything at `h = 0`. *Repayment*: the shell symbol cancels the `−log c` of the reference energy.
*Continuum shells*: the shell sum averaged over a continuous shift; they carry exactly the pole
charge. *Lattice gain*: the difference between the lattice and the continuum, worth `log(2πc)`.
*Separate payment*: a bound of the shells alone by `εD + CS`. *Joint payment*: a bound of the shells
together with the pole and the archimedean shells, keeping signs. *Reserve*: an inequality
`W ≥ δD − CS`; its *exponents* `(θ, κ)` when `δ ≍ c^{−θ}`, `C ≍ c^κ`. *Confinement exponent*: the
power of `c` in the defect bound for negative vectors (`16 = κ + θ` now, target `log c`).
*Conductor span*: the span of finitely many conductor modes; *off the span*: its complement.
*Successor sign* of a gauge: `σ_h(ℓ) = ω(ℓ)ω(ℓ + h)`; *disagreement*: `σ_h = −1`.

---

## 4. Mechanisms

1. **Overlap identity.** For a bump of width `w`, the prime form of an atomic test is the ratio block
   at `‖g‖²` plus the non-ratio form (`primeSum_atomicTest_eq_ratio_add`).
2. **Shell decomposition.** A non-ratio pair of nonzero weight has `|n − km| ≤ min(n, km)(e^w − 1)`,
   so its shift is unique and bounded; the non-ratio form is a finite sum of shell forms
   (`nonRatioForm_eq_sum_shellForm`), exactly `2⌊c⌋` of them at large `N`, living on the top band.
3. **Ramanujan averaging.** On a conductor-`m` mode a shell of shift `h` acts by the period average
   of `c_m(ℓ)c_m(ℓ + h)`, which is `c_m(h)` (`ramanujan_complete_additive_correlation`,
   `normalizedRamanujanMode_affine_unit_average`); distinct conductors do not mix.
4. **Möbius collapse.** `c_m(h) = Σ_{d∣(m,h)} μ(m/d)d` regroups the shells along `dℤ`; Poisson
   summation on each `dℤ` and Möbius inversion turn the shell symbol into the coprimality indicator:
   `E_m(c) = (2/(Mφ(m)))Σ_{(a,m)=1}(m/a)∫_{ac/m}^∞ P ≥ 0` (`hasSum_completedConductorEnergy`).
5. **Lattice versus continuum.** The continuum shell sum is `∫_0^c F_c = c(∫φ)²/2`, so continuum
   shells carry exactly the pole charge `cq`; the lattice omits the cell `0 < h < 1`, which holds
   `M log c` of shell weight. The repayment is the unit gap of the integers.
6. **Ground-state transform.** `P_N + D = Σ(A(⌊N/n⌋) + log n)x_n²` (`atomicWeilForm_add_poleDefect`):
   the ratio block is the top of the prime form minus the multiplicative Dirichlet energy.
7. **Base collapse.** On vectors that are the pole vector on every base, the shells reduce to pole
   rows `NR(x) = 2Σ_n x_n R(n)`, and `R` is an integer-lattice sum with weights `log ℓ`
   (`nonRatioForm_eq_of_pole_on_bases`, `shellPoleRow_eq_log`).
8. **Top-band Cauchy–Schwarz.** The top band fits in a log-window of length `log 2`, so its Gram sum
   is at least `(|T|∫g)²/log 2`; the shells read `≍ cq log N` per unit perturbation of the pole there,
   while the defect of the perturbation costs only `log N` per unit mass.
9. **Directed payment.** Up rows cost mass, down rows cost `(m/N) log m · x_m²`, which the defect pays;
   Young's inequality gives `|NR| ≤ εD + O(c²/ε)S` (`abs_nonRatioForm_le_relative_defect`). By
   mechanism 8 this is sharp in order.
10. **Pole rows are Laplace moments.** A first-order cell comparison and the substitution `t = n e^u`
    give `b_n R(n) = a₋a₊ log n + ∫ u e^{u/2}β − G log n/n + O(...)`, because `∫ e^{u/2}β = a₋a₊`
    is the factorization of the autocorrelation's Laplace transform at `½`
    (`integral_exp_half_mul_bumpCorr`, `abs_poleRow_sub_le`). The pole moments of the witness carry the
    same `a₋a₊`.
11. **Gauge defect.** For a completely multiplicative sign `ω`, the twin's prime form minus `ζ`'s
    prime form of the gauged vector is weighted by `ω(k) − ω(m)ω(n) = ω(k)(1 − ω(km)ω(n))`: zero on
    ratio pairs, twice the successor disagreement on shells.
12. **Fourier reserve and horizon decay.** `E_m(c) ≥ κ(m/φ(m))min(1, (m/c)⁷)` for the tilted spline;
    `‖(W − E_m)u_m‖² ≤ K_m(c⁵/log N + c¹⁰(log N/N)²)`; the Gram of conductor modes up to `√N` is
    conditioned (`ramanujanPoleProfile_family_squareRoot_lower`).

**Heuristic anatomy of the shell block (paper level, not formalized).** In ground-state coordinates
`x = b f`, replacing `x(ℓ + h)` by `x(ℓ)` and the shift sum by its integral splits the shells into:
(i) a continuum part `(2cq/N)Σ_ℓ (Λ⋆f)(ℓ)f(ℓ)`, which the pole term `(2cq/N)(Σf/n)(Σf)` cancels up
to a prime-number-theorem discrepancy `Σ_m f(m)[(1/m)Σ_n f(n) − Σ_k Λ(k)f(km)]` read on the top
band; (ii) a lattice part with symbol `σ(s) − sq`, `s = cℓ/N`, of size `O(log c)`, which repays;
(iii) a successor-variation part `Σ_h y(ℓ)(x(ℓ + h) − x(ℓ))β`, an additive Dirichlet form of `x` on
the top band, controlled by neither `D` nor `S`. Conductor modes are exactly the vectors on which
(iii) is diagonal. Q1 is the joint, signed control of (i)–(iii) with the archimedean shells.

---

## 5. Pillar theorems

**Inherited from the corpus.**

- Repayment on conductor modes: `completedConductorEnergy_eq_reference_sub_shells`,
  `hasSum_completedConductorEnergy` (RAPT).
- Fixed-overlap spectral theory: `eventually_completeWeil_spectral_count_eq_of_reserve_quasimodes`,
  `exists_finite_orthogonal_gap`, `eventually_tiltedUnitSpline_completeWeil_ground_count_one`.
- Growing-overlap endpoint: `riemannHypothesis_iff_completeWeilEnergy_nonneg_of_growthTwo`.
- Polynomial reserve: `tiltedUnitSpline_complete_defect_reserve_explicit`,
  `exists_negative_completeWeil_poleDefect_polynomial_bound` (CACT).
- Defect-only capture is exponential: `not_eventually_defect_coordinate_capture_below_binary_cutoff`.
- Shell calculus for a general kernel: `primePairForm_eq_ratioPart_add_shellPart`,
  `largeSieve_shellPart`, `sum_shellPart_dirichletGauge_eq_zero_of_kernel_short` (AGT).

**SSh pillars.**

1. **The shell decomposition** (`TheNonRatioFormIsAFiniteSumOfShells`). `NR = Σ_{0<|h|≤H} Sh_h`
   (`nonRatioForm_eq_sum_shellForm`); exactly `2⌊c⌋` shells at large `N`
   (`eventually_shellRange_eq_floor`), at most `2c e^{c/N}` always (`card_shellShifts_le`); the
   shift `h` reads only partners `n ≥ |h|N/(c e^{c/N})` (`shellForm_eq_zero_of_vanish_on_top_band`);
   no shells below the spacing (`nonRatioForm_eq_zero_of_shellRange_eq_zero`).
2. **The integrality of the shift repays the logarithm**
   (`TheIntegralityOfTheShiftRepaysTheLogarithm`). Continuum shells are the pole charge,
   `∫_0^c F_c = c(∫φ)²/2` (`continuumShellSum_eq`); the continuum conductor-one energy is
   `log(1/(2πc)) + β/M → −∞` (`continuumShellEnergy_eq`, `tendsto_continuumShellEnergy_atBot`),
   negative past `e^{β/M}/(2π)`; the lattice gain is `log(2πc) − β/M + E(c) ≥ log(2πc) − β/M` and
   equals `log(2πc) − β/M + o(1)` (`latticeGain_eq`, `latticeGain_ge`,
   `tendsto_latticeGain_sub_log`). For every conductor the period mean of `c_m` is `[m = 1]`, the
   continuum energy is the nonpolar reference energy, unbounded below, and the gain is
   `log(2πc) − β/M − log m − τ(m) + γ + o(1)` (`continuumConductorEnergy_eq`,
   `conductorLatticeGain_ge`, `tendsto_conductorLatticeGain_sub_log`).
3. **Conductor packets below the nineteenth root**
   (`FixedConductorPacketsArePositiveBelowTheNineteenthRoot`). Every fixed family of distinct
   conductors is positive for all coefficients along `c_N = (log N)^α`, `0 < α < 1/19`
   (`eventually_tiltedWeil_packet_pos_of_lt_one_nineteenth`), improving `1/40`; some unbounded,
   non-effective range `Q(N) → ∞` keeps `span{u_1, …, u_{Q(N)}}` positive
   (`exists_growing_packet_pos_of_lt_one_nineteenth`).
4. **The shells alone cost the square of the overlap** (`TheShellsAloneCostTheSquareOfTheOverlap`).
   For every nonnegative profile: if `NR(x) ≤ G(εD(x) + CS(x))` for all `x` at all large `N`, then
   `C ≥ A⁺²/(2ε)`, `A = cq/(4 log 2) − 1/2` (`le_of_nonRatioForm_payment`); at the reserve fraction
   `a c⁻⁷` this is `C ≥ A⁺²c⁷/(2a)`, order `c⁹` (`le_of_nonRatioForm_payment_at_reserve`). The
   witness is the pole vector perturbed on the top band; its computation is prime-free
   (`shellPoleRow_eq_log`).
5. **The twin defect is a successor-disagreement shell**
   (`TheTwinDefectIsASuccessorDisagreementShell`). For every completely multiplicative sign gauge,
   the twin's prime form minus `ζ`'s on the gauged vector is `Σ_h` of shells weighted by
   `ω(k)(1 − ω(km)ω(km + h))` (`twistedPrimeSum_sub_primeSum_eq_sum_twinShellForm`); shifts on which
   the gauge agrees with its successor are invisible (`twinShellForm_eq_zero_of_agree`); below the
   spacing the twins coincide (`twistedPrimeSum_eq_of_shellRange_eq_zero`).
6. **The shells and the pole cancel on the top band** (`TheShellsAndThePoleCancelOnTheTopBand`).
   Along the witness `b + ηb1_T` the joint block `2·Pole − NR` is a quadratic in `η`
   (`jointBlock_topWitnessVector`) whose linear coefficient is `≤ K G (1 + log N)` for every `C²`
   profile, `K` depending on `c` and the profile (`exists_abs_jointWitnessCoefficient_le`), while
   the shell and pole parts separately are `≍ Gcq log N`. This is the positive survivor of pillar 4.

---

## 6. Traps

| Trap | Truth |
|---|---|
| The shells are an error term | They repay `log c` exactly on conductor modes; without them every nonpolar reference energy is negative past touching (`exists_overlap_all_nonpolar_reference_energies_negative`) |
| A continuum of shifts repays as well | Continuum shells carry exactly the pole charge; the continuum energy is `log(1/(2πc)) + β/M → −∞` (pillar 2) |
| The repayment is a property of the primes | On the pole vector the shells are prime-free; the repayment is the unit gap of the shift lattice (pillars 2, 4) |
| Better Young constants remove `c¹⁶` | Every separate payment of the shells costs `≥ κc²/ε`, hence `c⁹` at the reserve fraction (pillar 4) |
| The floor witness is a negative direction | Jointly with the pole the shells cancel on it to `O(G(1 + log N))` (pillar 6) |
| One-sided bounds escape the floor | The floor holds for the one-sided bound `NR ≤ G(εD + CS)` |
| Shells help on nonnegative data | Diamagnetism: they are maximal at the trivial point and enter Weil's form with a minus sign (AGT) |
| Repayment on conductor modes is repayment | Off the conductor span the signed structure is the open core (Q1) |
| Defect bounds confine | Defect-only capture is exponential (binary witnesses) |
| Fixed overlap is close to RH | Fixed overlap is solved; RH needs `c⁴/log N → ∞` |
| Positive packets at growing `c` are confinement | Packets are fixed (or non-effectively growing) families; confinement must reach every negative vector |
| The Gram of conductor modes is the bottleneck | The square-root horizon conditions families up to `√N`; the residual rate and the floor set the range `1/19` |
| Twins differ by their primes | They differ only on shells, and only where the gauge disagrees with its successor (pillar 5) |

---

## 7. Questions

| # | Question | Status |
|---|---|---|
| Q1 | **Signed repayment off the conductor span (central).** Is there a reserve `W ≥ a c⁻⁷(D − C log(2c)S)` with an effective horizon, i.e. `D = O(log c)` on negative vectors? Its selective form is persistence of the pole ground line along `c_N`. | Open. Pillar 4 proves it cannot come from separate payment; the heuristic anatomy (§4) names the three parts a joint payment must control |
| Q2 | The exact shell decomposition of the literal non-ratio form, the number of shells, the band each shift lives on | Answered (pillar 1) |
| Q3 | How much of the repayment is the integrality of the shift, for every conductor? | Answered: all of it; continuum shells are the pole charge, the gain is `log(2πc) − β/M + o(1)` (pillar 2) |
| Q4 | Is `c²/ε` the floor of every separate payment of the shells? | Answered: yes, even one-sided, for every nonnegative profile (pillar 4); on the floor witness the joint shell–pole block costs only `O(G(1 + log N))` (pillar 6) |
| Q5 | How far do conductor packets stay positive along `c = (log N)^α`? | Fixed packets: `α < 1/19` (pillar 3). Effective growing ranges need conductor-explicit residual constants; seven of the eight residual components are not explicit in `m` |
| Q6 | Mean-square conductor costs: replace `√φ(m)` in the prime residual by the period mean square | Open. Blocks `⌊N/n⌋ = y` have length `≍ N/y²`; averaging works for `y ≤ √(N/m)`, and the short blocks need a quantitative Mertens remainder, which the uniform budget (`tendsto_primeMertensRemainderProfile`, rate `o(1)`) does not supply |
| Q7 | Which models fail repayment? | Continuum: fails (pillar 2). Sign twins: differ exactly on disagreeing shells (pillar 5). Beurling generators: open |
| Q8 | Growing-modulus control of the affine prime windows `Σ_k Λ(k)e(a(km + h)/q)` | Owned by card `agt-siegel-walfisz-and-bv-for-shells` (zero-free region formalized; Siegel–Walfisz and assembly open) |

---

## 8. Tools

| Tool | State |
|---|---|
| Shell calculus for the literal complete form: decomposition, support, count, top band | Built (pillar 1) |
| Lattice–continuum comparison for every conductor | Built (pillar 2) |
| Base collapse and prime-free pole rows | Built (pillar 4) |
| Witness method for payment floors (top-band perturbation of the pole, Cauchy–Schwarz on a `log 2` window) | Built (pillar 4); reusable for any separately paid source |
| First-order cell comparison and Laplace-moment evaluation of pole rows | Built (pillar 6) |
| Growing-packet machinery with explicit range | Built for fixed packets (pillar 3) |
| Gauge-defect shells | Built (pillar 5) |
| A joint payment ledger tracking reserve exponents `(θ, κ)` for shells + pole + archimedean shells | Open |
| Conductor-explicit residual constants (all eight components) | Open |
| Mean-square conductor costs | Open (Q6) |
| The successor-variation form and its relation to the multiplicative defect | Open |

---

## 9. Open research topics

1. **Joint shell–pole payment beyond the witness.** On the top-band witness the joint block is
   paid (pillar 6). For general vectors the joint block still contains the PNT discrepancy and the
   successor variation of topics 2 and 3.
2. **The PNT discrepancy form.** `Δ(f) = Σ_m f(m)[(1/m)Σ_n f(n) − Σ_k Λ(k)f(km)]` on the top band:
   its size relative to `D` and `S` is where the prime number theorem (and RH) enters the joint block.
3. **The successor-variation form.** `Σ_h Σ_ℓ y(ℓ)(x(ℓ + h) − x(ℓ))β`: an additive Dirichlet energy
   on the top band. Which inequality between it and the multiplicative defect `D` is true, and does
   it fail for Beurling systems?
4. **Archimedean shells.** The archimedean part keeps only the fraction `c⁻⁷` of the defect; its
   overlap pairs `(n, n + h)` are the `k = 1` shells. Their signed interaction with the prime shells
   and the pole is the third member of the joint block.
5. **Effective growing packets.** Conductor-explicit versions of the seven non-prime residual
   components; then a range `Q(N)` with an explicit rate.
6. **Successor signs of twins.** With pillar 5, a twin separates from `ζ` only through the density of
   disagreeing successors on the top band. Combine with the one-third floor of Signed Successor
   Arithmetic (`TheOneThirdSuccessorFloor`) to bound the twin defect.
7. **Beurling generators.** Shell repayment for generalized integers whose successor gaps are not
   unit: the gap size sets the gain (pillar 2 suggests `log(c/gap)`).

---

## 10. Place in the research

SSh is the common core of RAPT, CACT, CAF and AGT's shell work. What it adds is the target, made
precise by its own pillars: signed, joint payment of the shell block beyond conductor modes is the
single estimate that controls the reserve cost, and separate payment provably cannot do it.

| Programme | Interface |
|---|---|
| RenormalizedArithmeticPotentialTheory (RAPT) | Completed conductor energies, shell form, repayment law, fixed-overlap spectral theory, pole-profile collapse, binary no-go |
| CriticalArithmeticCorrelationTheory (CACT) | Polynomial reserve, directed rows, residual horizon decay, affine shell sources, square-root horizon |
| CompletedArithmeticForms (CAF) | Growing overlap and growing packets (`1/40`, improved here to `1/19`) |
| ArithmeticGaugeTheory (AGT) | Shell calculus for a general kernel, gauge charge, short shells, level of distribution `1/2` |
| SpacingScaleHarmonicAnalysis | Overlap identity, non-ratio rows, gauge defect identity |
| SignedSuccessorArithmetic | Successor signs of completely multiplicative functions; pillar 5 makes them the carriers of the twin defect |
| TransMetzlerWeilPositivity | Bounded-overlap positivity of the complete matrix |
| SignedArithmeticHodgeTheory | Uniform residual budgets for Ramanujan families |
| ArithmeticLorentzianGeometry | The pole relative to the prime defect |
| BezoutValuationIncidence | Ramanujan lag coefficients, successor incidence |
| HeckeKreinToeplitz | Atomic index ladder: the pole selects against the conductor-`2` rung |

---

## 11. Success criteria and contributions

**Success.** A reserve at growing overlap with cost below `c⁹`, obtained by a joint signed payment of
the shell block, or a proof that no payment from a stated class of shell data can reach it.

**A contribution**

1. recovers the conductor-mode repayment and the fixed-overlap spectral count where it applies;
2. states what it gives in the continuum completion and for sign twins, and fails there when it
   claims a selective inequality (R2);
3. tracks its reserve exponents `(θ, κ)` and its horizon;
4. is not a separate payment of the shells (pillar 4 bounds those);
5. is an unconditional Lean statement, with every prime power, both poles and the Gamma factor kept.

**Principles.** Identities first, sign last; keep the shift `h` explicit; compare every lattice sum
with its continuum average; pay jointly what cancels jointly; record the positive survivor of every
no-go; a reformulation is not a reduction.
