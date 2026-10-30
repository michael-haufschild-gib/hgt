# Successor-Shell Arithmetic (SSh)

Namespace `GaloisForLFunctions.SuccessorShellArithmetic`; umbrella `SuccessorShellArithmetic.lean`.

**Question.** The complete atomic Weil form at growing overlap is the one object in the corpus that
is a positivity family, is built on the integers, works at square-root precision and sees zeros at
every depth. At fixed overlap it is solved: conductor modes are quasimodes whose energies are
nonnegative because the *successor shells* `n = km + h` repay the logarithmic loss of the reference
energy exactly. Past fixed overlap the corpus pays the shells in absolute value, and that payment is
the whole polynomial loss `c¹⁶` in the confinement of negative vectors. What is the signed arithmetic
of the shell block for vectors that are not conductor modes, and can it be paid at logarithmic cost?

SSh is the arithmetic of that block: additive structure (the shift `h`) and multiplicative structure
(the prime power `k`, the base `m`) meeting at the atomic scale. Everything is unconditional; RH
appears only inside equivalences.

---

## 1. Why

**Five requirements for a missing tool.** Corpus theorems fix what a producer of RH-strength
positivity must look like:

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

**Where the loss sits.** The proved reserve (`tiltedUnitSpline_complete_defect_reserve_explicit`) is
`W ≥ (δ/4)D − C(c)‖x‖²`, `δ ∝ c⁻⁷`, `C(c) ∝ c⁹`, hence `D ≤ C' c¹⁶‖x‖²` on negative vectors
(`exists_negative_completeWeil_poleDefect_polynomial_bound`). Read from its proof:

- the archimedean part keeps only `δ/2` of the prime defect `D`, with `δ` the Fourier reserve of the
  profile, `∝ c⁻⁷` for the tilted spline;
- the non-ratio prime form and the pole moments are each paid by Young's inequality at `ε = δ/8`
  (`abs_nonRatioForm_le_relative_defect`, `two_mul_abs_poleMoments_le_relative_defect`), each costing
  `∝ c²/ε`.

So the exponent `16 = 2 + 2·7` is the price of paying the shells and the pole *in absolute value*
against a defect fraction `∝ c⁻⁷`. On conductor modes the same sources cancel with sign; off them
nothing is known. The open estimates of the growing-overlap route (effective confinement, a weighted
residual over growing conductor families) become polynomial once the defect bound is logarithmic.

**Why the shells and not the zeros.** The shells are where `+` and `×` meet in the form: a shell pairs
`m` with `km + h`, a multiplicative relation broken by a bounded additive shift. Their repayment on
conductor modes is Poisson summation over the shift lattice `ℤ`. That is a use of discreteness of
exactly the kind R2 demands, and it is absent in every continuous model.

---

## 2. Objects and language

Fix a `C²` profile `φ` supported in `[0, 1]`, `M = ∫φ²`, `q = (∫φ)²/M`, autocorrelation
`G(u) = ∫φ(v)φ(v + u) dv`, spectrum `P(t) = |φ̂(2πt)|²`. Horizon `N`, overlap ratio `c`, atom width
`w = c/N`, atoms `a_n = φ((· − log n)/w)` for `1 ≤ n ≤ N`, coefficients `x`, mass `S(x) = Σ x_n²`.

| Object | Meaning | Lean |
|---|---|---|
| Complete Weil form | `W_{N,c}(x) = weilQuad(Σ x_n a_n)/(wM)` = archimedean − ratio − shells + pole | `completeWeilMatrix`, `completeWeilEnergy` |
| Ratio block | `P_N(x) = 2Σ_{mt ≤ N} Λ(t)t^{−1/2} x_m x_{mt}` | `atomicWeilForm`, `atomicWeilForm_eq_edges` |
| Prime defect | `D(x) = Σ_{mt ≤ N} Λ(t)(x_{mt} − x_m/√t)²`, the Dirichlet energy of the pole relation | `poleDefect` |
| Pole vector | `b_n = n^{−1/2}`, the ground state of `P_N` | `poleVector` |
| Successor shell | a triple `(k, m, h)` with partner `n = km + h`; `h = 0` is a ratio pair | — |
| Prime shell form | `Sh_h(x) = 2Σ_k Λ(k)k^{−1/2} Σ_m x_m x_{km+h} β_w(log(km/(km+h)))`, `β_w` the atom autocorrelation | `shellForm` |
| Non-ratio form | `NR = Σ_{h ≠ 0} Sh_h` | `nonRatioForm` |
| Archimedean shells | the overlap pairs `(n, n + h)`, `h ≠ 0`, of the archimedean pairing (`k = 1`) | overlap matrix of `completeWeilMatrix_eq_decomposition_at_every_overlap` |
| Convolved source | `y = Λ_w ⋆ x`, `Λ_w(k) = Λ(k)/√k`; `Sh_h` pairs `y(ℓ)` with `x(ℓ + h)` | AGT `truncConv`, `primePairForm_eq_convolved` |
| Conductor mode | `u_m(n) = c_m(n)/√(φ(m) n)`, normalized by `√log N` | `ramanujanPoleProfile`, `normalizedRamanujanHorizonVector` |
| Shell coefficient | the Ramanujan sum `c_m(h)`: the average of `c_m(ℓ)c_m(ℓ + h)` over a period | `ramanujanLagCoefficient` |
| Shell weight | `F_c(h) = ∫_{h/c}^1 G(u)/u du`, the top-band average of the `h`-th shell | `shellSum`, `shellCorrection` |
| Reference energy | `E_m^ref(c) = log(1/(2πc)) + β(φ)/M + log m + τ(m) − γ + [m = 1]cq` | `completeWeilAdjunctionEnergy` |
| Completed conductor energy | `E_m(c) = E_m^ref(c) − (2/(Mφ(m)))Σ_{1≤h<c} c_m(h)F_c(h)` | `completedConductorEnergy` |
| Continuum shell completion | the shell sum replaced by its integral over the shift `h ∈ (0, c)` | `continuumShellEnergy` |
| Lattice gain | `E(c) −` continuum energy: what the integrality of `h` pays | `latticeGain` |
| Reserve | an inequality `W ≥ δ D − C S`; exponents `(θ, κ)` when `δ ≍ c^{−θ}`, `C ≍ c^κ` | — |

**Words.** *Shift* `h`, *dilation* `k`, *base* `m` of a shell. *Top band*: the atoms `n ≥ N/c`, the only
place where shells live. *Ratio block*: everything at `h = 0`. *Repayment*: the shell symbol cancels
the `−log c` of the reference energy. *Absolute payment*: a bound on `|Sh|` by `εD + C(ε)S`. *Signed
payment*: a one-sided bound that keeps the sign of the shells, possibly jointly with the pole and the
archimedean shells. *Conductor span*: the span of finitely many conductor modes. *Off the span*: its
orthogonal complement, where the binary witnesses of the defect-only no-go live. *Confinement
exponent*: the power of `c` in the defect bound for negative vectors (`16` now, target `log c`).

---

## 3. Mechanisms

1. **Overlap identity.** For a bump of width `w` the prime form of an atomic test is the ratio block at
   `‖g‖²` plus the non-ratio form (`primeSum_atomicTest_eq_ratio_add`). Below the spacing `NR = 0`.
2. **Shell decomposition.** Every non-ratio pair has a unique shift `h = n − km ≠ 0`; only
   `|h| ≤ N(e^w − 1) ≤ c e^{c/N}` occur, and shift `h` needs `km ≥ |h|/(e^w − 1)`. The non-ratio form is
   a finite sum of shell forms living on the top band.
3. **Ramanujan averaging.** On a conductor-`m` mode a shell of shift `h` acts by the average of
   `c_m(ℓ)c_m(ℓ + h)`, which is `c_m(h)`; distinct conductors do not mix. Conductor modes are the joint
   eigenvectors of dilation and successor averaging.
4. **Möbius collapse.** `c_m(h) = Σ_{d∣(m,h)} μ(m/d)d` regroups the shells along `dℤ`; Poisson summation
   on each `dℤ` and Möbius inversion turn the shell symbol into the coprimality indicator:
   `E_m(c) = (2/(Mφ(m)))Σ_{(a,m)=1}(m/a)∫_{ac/m}^∞ P ≥ 0` (`hasSum_completedConductorEnergy`).
5. **Lattice versus continuum.** The shell sum is the lattice part of Poisson's formula. Its continuum
   average is exactly the pole charge `cq`; the lattice correction is what repays `log c`.
6. **Ground-state transform.** `P_N + D = Σ(A(⌊N/n⌋) + log n)x_n²` (`atomicWeilForm_add_poleDefect`):
   the ratio block is the top of the prime form minus the multiplicative Dirichlet energy.
7. **Directed payment.** Up rows of the shells cost mass, down rows cost `(m/N) log m · x_m²`, which the
   defect pays (`sum_top_le_poleDefect`); Young's inequality with independent directions gives
   `|NR| ≤ εD + O(c²/ε)S` (`abs_nonRatioForm_le_relative_defect`).
8. **Fourier reserve.** The coprime tail gives `E_m(c) ≥ κ(m/φ(m))min(1, (m/c)⁷)` for the tilted spline
   (`tiltedUnitSpline_completedConductorEnergy_ge_conductor_scale`): the reserve fraction `c⁻⁷` is the
   decay of `P`.
9. **Square-root horizon.** Conductor families up to `Q < √N` stay conditioned
   (`ramanujanPoleProfile_family_squareRoot_lower`).
10. **Horizon decay of residuals.** `‖(W − E_m)u_m‖² ≤ K_m(c⁵/log N + c¹⁰(log N/N)²)`
    (`exists_completeWeil_completedConductor_residual_horizon_bound`).

---

## 4. Pillar theorems

Inherited from the corpus:

1. **Repayment on conductor modes** — `completedConductorEnergy_eq_reference_sub_shells`,
   `hasSum_completedConductorEnergy` (RAPT).
2. **Fixed-overlap spectral theory** — `eventually_completeWeil_spectral_count_eq_of_reserve_quasimodes`,
   `exists_finite_orthogonal_gap`, `eventually_tiltedUnitSpline_completeWeil_ground_count_one`.
3. **Growing-overlap endpoint** — `riemannHypothesis_iff_completeWeilEnergy_nonneg_of_growthTwo`.
4. **Polynomial reserve and its anatomy** — `tiltedUnitSpline_complete_defect_reserve_explicit`,
   `exists_negative_completeWeil_poleDefect_polynomial_bound`.
5. **Defect-only capture is exponential** — `not_eventually_defect_coordinate_capture_below_binary_cutoff`.
6. **Shell calculus at the gauge level** — `primePairForm_eq_ratioPart_add_shellPart`,
   `integral_primePairForm_gaugeTransform`, `largeSieve_shellPart`,
   `sum_shellPart_dirichletGauge_eq_zero_of_kernel_short` (AGT).

SSh's own pillars are listed in §6 with the questions they answer.

---

## 5. Traps

| Trap | Truth |
|---|---|
| The shells are an error term | They repay `log c` exactly on conductor modes; without them every nonpolar reference energy is negative past touching (`exists_overlap_all_nonpolar_reference_energies_negative`) |
| A continuum of shifts repays as well | The continuum average of the shells is the pole charge; only the lattice part repays |
| Shells help on nonnegative data | Diamagnetism: they are maximal at the trivial point and enter Weil's form with a minus sign (AGT) |
| Repayment on conductor modes is repayment | Off the conductor span the signed structure is unknown; that is the RH content of the growing-overlap route |
| Better Young constants remove `c¹⁶` | Any absolute payment against a defect fraction `∝ c⁻⁷` costs a power of `c`; the sign must be used |
| Defect bounds confine | Defect-only capture is exponential (binary witnesses) |
| Fixed overlap is close to RH | Fixed overlap is solved; RH needs `c⁴/log N → ∞` |
| Positive packets at growing `c` are confinement | Packets are fixed finite families; confinement must reach every negative vector |
| The Gram of conductor modes is the bottleneck | The square-root horizon conditions families up to `√N` |
| The exponent `7` is an artifact | It is the decay of `|φ̂|²` read at conductor `2`; another profile changes it, not its role |

---

## 6. Questions, pillars to build, open topics

**Q1 — Signed repayment off the conductor span (central).** Is the non-ratio form plus the archimedean
shell deficit `≥ −a c⁻⁷ O(log c)·S − (small)·D` for every coefficient vector, with an effective
horizon? Equivalently, is there a reserve `W ≥ a c⁻⁷(D − C log(2c)S)`, giving negative vectors
`D = O(log c)`? Its selective form is persistence of the pole ground line along `c_N`.

**Q2 — Shell decomposition and support.** The exact finite decomposition of the literal non-ratio form
into shells, their number, and the band each shift lives on.

**Q3 — Discreteness.** How much of the repayment is the integrality of the shift? Exact comparison of
the shell sum with its continuum average, for every conductor.

**Q4 — The price of absolute payment.** Is `c²/ε` the floor of every absolute payment of the shells,
so that the polynomial confinement exponent is intrinsic to absolute methods?

**Q5 — Conductor span at growing overlap.** How far do fixed and growing conductor packets stay
positive along `c = (log N)^α`? What is the joint signed bound on `span{u_m : m ≤ Q}`?

**Q6 — Mean-square conductor costs.** Replace the sup bound `√φ(m)` in the prime residual by the
period mean square, turning the family cost `Σφ(m)log²m` into `Σ log²m`.

**Q7 — Selectivity.** Which models fail repayment: the continuum, Beurling generators, twisted sources
(Liouville, Dirichlet gauges)? A contribution to Q1 must fail on them.

**Q8 — Affine prime windows at growing modulus.** The shell coefficients of non-conductor vectors are
affine prime sums `Σ_k Λ(k)e(a(km + h)/q)`; their growing-modulus control is Siegel–Walfisz and
Bombieri–Vinogradov for shells.

**Tools to build.** A shell calculus for the literal complete form (decomposition, support, convolved
sources); the shell symbol of conductor modes and its continuum comparison; a payment ledger that
tracks reserve exponents `(θ, κ)`; mean-square conductor costs; growing-packet positivity with explicit
ranges; a selectivity battery for shell repayment.

---

## 7. Place in the research

| Programme | Interface |
|---|---|
| RenormalizedArithmeticPotentialTheory (RAPT) | Completed conductor energies, shell form, repayment law, fixed-overlap spectral theory, binary no-go |
| CriticalArithmeticCorrelationTheory (CACT) | Growing-overlap machinery: polynomial reserve, directed rows, residual horizon decay, affine shell sources, square-root horizon |
| CompletedArithmeticForms (CAF) | Growing overlap, growing packets, conductor log law |
| ArithmeticGaugeTheory (AGT) | Shell calculus for a general kernel: convolved form, gauge charge, short shells, level of distribution `1/2` |
| SpacingScaleHarmonicAnalysis | Overlap identity, non-ratio rows at bounded overlap |
| TransMetzlerWeilPositivity | Bounded-overlap positivity of the complete matrix |
| SignedArithmeticHodgeTheory | Uniform residual budgets for Ramanujan families |
| ArithmeticLorentzianGeometry | The pole relative to the prime defect |
| BezoutValuationIncidence | Ramanujan lag coefficients, successor incidence |
| SignedSuccessorArithmetic | The successor `n ↦ n + 1` read through completely multiplicative signs; SSh reads it through the shifts of the Weil form |
| HeckeKreinToeplitz | Atomic index ladder: the pole selects against the conductor-`2` rung |

The SW/BV card `agt-siegel-walfisz-and-bv-for-shells` owns Q8's growing-modulus input. SSh is the
common core of RAPT, CACT, CAF and AGT's shell work; what it adds is the target: signed shell payment
beyond conductor modes as the single estimate that controls the reserve cost.

---

## 8. Success criteria and principles

**Success.** A reserve at growing overlap with cost below `c⁹`, obtained by a signed payment of the
shell block, or a proof that no payment from a stated class of shell data can reach it.

**A contribution**

1. recovers the conductor-mode repayment and the fixed-overlap spectral count where it applies;
2. states what it gives in the continuum completion and for twisted sources, and fails there when it
   claims a selective inequality (R2);
3. tracks its reserve exponents `(θ, κ)` and its horizon;
4. is an unconditional Lean statement, with every prime power, both poles and the Gamma factor kept.

**Principles.** Identities first, sign last; keep the shift `h` explicit; compare every lattice sum with
its continuum average; pay jointly what cancels jointly; a reformulation is not a reduction.
