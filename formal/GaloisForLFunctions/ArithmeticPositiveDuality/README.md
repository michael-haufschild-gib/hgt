# Arithmetic Positive Duality (APD)

**One question.** The explicit formula is a Poisson summation formula between two measures on the
line: the prime measure, positive because `Λ ≥ 0`, and the zero measure, positive exactly when RH
holds. Everything the corpus has ever *forced* about `ζ` has one shape: positivity, an exact
self-dual identity and an integer together give rigidity. What is the complete rigidity theory of
positive arithmetic distributions under Poisson self-duality and integer quantization, and what can
it force on the zero side?

Working subtitle: *positivity on both sides of the explicit formula.*

APD is the rigidity theory of **positive Poisson pairs**: pairs `(μ, μ̂)` of measures, one side
carrying arithmetic support (`± log n`, lattices, `S`-unit groups `ℤ log p₁ + ⋯ + ℤ log p_r`), the
other a spectrum. Its basic objects are positive-definite functions on groups of finite rank and
their Fourier measures on tori. Its basic mechanism is the **spectral gap identity**: an exact sum
of nonnegative terms equals a computable constant, and integrality or self-duality turns the
identity into rigidity.

Namespace `GaloisForLFunctions.ArithmeticPositiveDuality`; umbrella `ArithmeticPositiveDuality.lean`.
Everything is unconditional; RH appears only inside equivalences.

---

## 1. Place in the research

The walls of the frontier are three readings of one sentence: *what forces the actual arithmetic
source to be blind to off-line zeros?* (rate W1, transfer W3, carrier W14). Over `𝔽_q` the three
answers are one object, an intersection theory with integer pairing, finite rank and positivity
from counting sections. Over `ℤ` the corpus has the pairing, the Lefschetz and adjunction
identities, the signature law and the maximal blind carrier, and it has proved that the missing
ingredient is a structure, not an estimate.

The corpus's exhaustion theorems cover these classes:

| Class of mechanism | Exhausting theorem |
|---|---|
| Quadratic positivity on a sharp-stable convolution ideal of the scaling flow | lies in the maximal blind ideal (`isGreatest_meyerSharpPositiveIdeal`) |
| Quadratic positivity on a scale-shift-invariant test space | blind (`zeta_blindOffLine_of_scaleShift_subspace_weil_nonneg`) |
| Finite harmonic (multiplicative) coupling by a nonnegative cosine polynomial | Fejér barrier, interior needs growth input (MPG) |
| Finitely many linear readings, with or without mass | cannot supply Bézout (ACS) |
| Finite-dimensional affine-unitary carriers | trivial (`finite_affine_unitary_rigidity`) |

APD adds four classes to this table, each with an exact theorem:

| Class | APD theorem |
|---|---|
| Multi-channel positive certificates (several heights, primes, harmonics) | a direct sum of one-channel problems, one per rational fibre |
| Integer positive-definite boundary data on groups of any rank | sign characters of subgroups; isolation forces `δ₀` iff no 2-torsion |
| Positive functionals on the affine (successor and dilation) group | induced from the dilations; the successor part is free |
| Integer quantization in de la Vallée Poussin's coupling | no budget below the first (even) quantum at the critical line |

Two theorems of the corpus are *forcing* theorems, and they share one shape:

- **boundary forcing** (MPG): the boundary divisor of nonnegative Euler log-coefficients is an even
  positive-definite function on `ℝ`; integer values and a unit pole make it a sign character of a
  subgroup; pole isolation makes it `δ₀`, so `ζ(1+it) ≠ 0` (`boundary_forcing_law`);
- **theta forcing** (this programme): a positive measure on `[1, ∞)` whose theta transform obeys
  Riemann's self-dual law is a Dirac comb on the positive integers; on a Beurling system the
  functional equation forces `ζ` itself (`measure_eq_of_measureTheta_relation`,
  `beurlingSystem_rigidity_of_completed_functional_equation`).

APD is the field in which these are the first two instances of one law (P1–P7 below). Its third
instance in the strip is the open core.

| Programme | Interface |
|---|---|
| [MultiplicativePositivityGeometry](../MultiplicativePositivityGeometry/README.md) | The rank-one height side: boundary divisor, Fejér barrier, growth-to-forcing law. APD extends its positive-definite calculus to every rank, computes the multi-channel barrier and the quantum budget. |
| [ArithmeticOrientationGeometry](../ArithmeticOrientationGeometry/README.md) | The scale side: orientation is positive definiteness of the orbit correlation; the spline orbit and its two-prime Hecke orbit decide RH. APD reads the two-prime orbit as a Bochner problem on `T²`. |
| [ArithmeticCastelnuovoSeveri](../ArithmeticCastelnuovoSeveri/README.md) | Maximal blind ideal, Meyer source, Frobenius span, golden datum; `ArithmeticForcesBlindness` uses this programme's Hamburger rigidity. APD settles the topology of the blind ideal and restates the span Hodge index as positive definiteness on `ℤ`. |
| [BiarithmeticGeometry](../BiarithmeticGeometry/README.md), [SignedSuccessorArithmetic](../SignedSuccessorArithmetic/README.md) | The successor and the affine action. APD proves that affine positivity is induced from the dilations. |
| [ScaleSignedIncidenceCriticality](../ScaleSignedIncidenceCriticality/README.md) | Prices every reading; a finite box of `ℤ²` is a bounded-aperture condition. |
| [BiScaleUncertainty](../BiScaleUncertainty/README.md), [TransThresholdPairCorrelation](../TransThresholdPairCorrelation/README.md) | Bi-scale uncertainty and the threshold face; the signed close-prime-pair surplus is a prime-side Fourier coefficient the zero side cannot see. |
| HTGeometry, RHTower | Hamburger's theorem, Bochner on `ℝ`, the tent transform, Kronecker density, the Weil criterion in Bochner form (`weilPositiveFull_iff_forall_exists_spectralMeasure`), the natural Fréchet topology of the Meyer source. |

---

## 2. Why

**The explicit formula is a Poisson pair.** For an even test `g`,

`Σ_ρ ĝ(γ_ρ) = ĝ(i/2) + ĝ(−i/2) − Σ_n Λ(n) n^{−1/2} (g(log n) + g(−log n)) + (archimedean term)`,

with `γ_ρ = (ρ − ½)/i`. The left side integrates `ĝ` against the zero measure
`μ_Z = Σ m_ρ δ_{γ_ρ}`, the right side integrates `g` against the prime measure
`μ_P = Σ Λ(n) n^{−1/2} (δ_{log n} + δ_{−log n})` corrected by the archimedean density and the pole.
`μ_P ≥ 0` by arithmetic. RH says `μ_Z` is a positive measure on `ℝ`; in Bochner form this is
Weil's criterion: every spectral kernel `y ↦ W(τ_y(f ⋆ f̃))` is the characteristic function of a
positive measure.

**The two positivities are Fourier dual.** In the height variable,
`u ↦ Re(−ζ'/ζ)(σ + iu) = Σ Λ(n) n^{−σ} cos(u log n)` is positive definite because `μ_P ≥ 0`
(MPG). In the scale variable, `t ↦ Re W(f, f(· − t))` is positive definite iff `|f̂|² μ_Z` is a
positive measure (AOG). One side is known; the other is the theorem.

**Forcing is rigidity.** Neither forcing theorem is an inequality with a constant. Each is an exact
identity whose two sides have different regularity, a sum of nonnegative terms against a
computable constant, followed by quantization:

- boundary: `|D(u)| ≤ D(0) = 1` with `D` integer valued; a three-point Gram form makes the support
  a subgroup;
- theta and tents: pairing a self-dual identity with the Fejér tent `max(0, 1 − |x|)`, whose
  transform `sinc(πξ)²` vanishes exactly on `ℤ ∖ {0}`, leaves a sum of nonnegative terms equal to
  zero; positivity puts the measure on the lattice.

Weil's theorem for curves is the calibration: the normalized trace sequence of a curve is positive
definite on `ℤ`, with integer mass `2g`, and Weil proves it by counting.

**Rank matters, on one side only.** Rank one in the height variable forces only the boundary.
Rank in the height variable adds nothing per channel: a multi-channel certificate splits into
rational fibres. Rank one in the scale variable is blind (a single prime tower is Toeplitz-blind
to symmetric Wolff configurations), and rank two in the scale variable decides RH. Rank helps on the
zero side, not on the prime side.

---

## 3. Objects and language

| Object | Meaning | Lean |
|---|---|---|
| Poisson pair | `(μ, ν)` with `∫ 𝓕g dμ = ∫ g dν` on a stated test class; *self-dual* when `ν = μ` | `IsTentSelfDual` |
| Gap | `(−a, a) ∖ {0}` carrying no mass | hypothesis `μ (Ioo (-1) 1 \ {0}) = 0` |
| Fejér tent | `max(0, 1 − |x|)`, transform `sinc(πξ)²` | `tentAt`, `modTent`, `fourier_tentAt` |
| Dirac comb | `Σ_{n ∈ ℤ} δ_n` | `diracComb` |
| Positive-definite function | all Gram forms nonnegative, on `ℤ^ι`, on a group, on an additive group (real, even) | `IsPosDefOnLattice`, `IsPosDefOnGroup`, `IsEvenPosDef` |
| Fourier measure | finite measure on `ℝ^ι` read through `θ ↦ e^{i⟨m, θ⟩}`, `m ∈ ℤ^ι` | `fourierCoeff`, `latticeChar` |
| Kronecker line | `t ↦ (γ_i t)_i`; restriction to `{⟨m, γ⟩}` is push-forward along it | `kroneckerLine` |
| Certificate, fibre | `Σ c_i cos(λ_i t) ≥ 0`; the modes with `λ_i ∈ ℤω` | `fibreCoeff`, `Resonant` |
| Independent channels | `ℚ`-independent frequencies `γ_j`, spectrum `⟨k, γ⟩` | `channelFreq` |
| Sign character | `χ : H → {±1}` additive to multiplicative, extended by zero | `IsSignCharacter`, `extendByZero` |
| Quantum budget | `b(η) = (√A + √(Gη))²/B`: the largest admissible zero order at distance `η` | `quantumBudget` |
| Affine group of `ℚ` | `x ↦ ax + b`; dilations and successor | `AffineGroupQ`, `dilation`, `successor` |
| Critical-jet topology | coarsest topology making all critical Meyer jets continuous | `criticalJetTopology` |
| Battery | golden datum `1 − 5X + 5X²`, curves, Wolff configurations, Beurling countermodels | `goldenDatum`, `CurveDatum` |

**Words.** *Positive side* / *spectral side*: the side with known positivity / the side whose
positivity is the theorem. *Forcing*: an unconditional theorem whose conclusion is a vanishing on
the spectral side. *Receiver*: an RH-equivalent reformulation; it never produces its own input.
*Height side* / *scale side*: the two Fourier-dual variables of the explicit formula.

---

## 4. Mechanisms

1. **Spectral gap identity.** Pair a Poisson identity with a nonnegative test supported in the gap
   of the dual side; what is left is a sum of nonnegative terms equal to the polar constant
   (`fejer_pairing_identity`, `integral_sincSq_shift_eq`).
2. **Zero set of the tent transform.** `sinc(πξ)²` vanishes exactly on `ℤ ∖ {0}`; a vanishing gap
   identity puts a positive measure on the lattice (`exists_int_of_sincSq_eq_zero`).
3. **Lattice evaluation.** On an integer-supported measure, a test equal to `δ_k` on `ℤ` integrates
   to the atom at `k`; the tent translates read the atoms, their transforms read the atom at `0`
   (`integral_eq_of_isIntSupported`).
4. **Gram quantization.** For integer-valued positive-definite `φ` with `φ(0) = 1` the support is a
   subgroup and `φ` a sign character; conversely a sign character factors through coset
   representatives, `φ(x − y) = [r x = r y] ε(x) ε(y)`, and its Gram form is a sum of squares
   (`extendByZero_sub_eq`).
5. **Bohr projection.** Averaging a certificate along `t + k·2π/ω` keeps exactly the modes
   resonant with `ω`, with bounded error `Σ |c_i|/|sin(πλ_i/ω)|`; nonnegativity survives
   (`fibre_projection_nonneg`).
6. **Product extremals.** `Q₁(γ₁t) Q₂(γ₂t)` is a nonnegative two-channel certificate whose fibres
   are `Q₁` and `Q₂` with a common pole weight (`productCertificate_eq`, `productCoeff_fibreCoeff`).
7. **Fejér means on lattices.** The density `Σ_{j,k ∈ [0,N]^ι} φ(k − j) e^{−i⟨k−j, θ⟩}` is a Gram
   form; its coefficients are `φ(m) Π_i c_N(m_i)`, the window count factorizing over coordinates;
   Prokhorov on one compact box gives the measure (`sum_window_pairs`,
   `fourierCoeff_latticeFejerMeasure`).
8. **Restriction and push-forward.** Restricting a characteristic function to `{⟨m, γ⟩}` is the
   push-forward of its measure along the Kronecker line (`fourierCoeff_map_kroneckerLine`).
9. **Induction from a subgroup.** Writing `x = r(x) h(x)` with a left-coset representative, the
   Gram form of an extension by zero splits into one Gram form per coset
   (`isPosDefOnGroup_extendFromSubgroup`).
10. **Critical interpolation.** Critical single-jet sources lie in the blind ideal and match any
    finitely many critical jets exactly (`exists_mem_blind_eq_on`).
11. **Budget arithmetic.** The growth-to-forcing law read as a bound on an integer: `m B ≤
    (√A + √(Gη))²`; an integer below one is zero, an even integer below two is zero
    (`admissible_iff_le_quantumBudget`).

---

## 5. Pillar theorems

| Pillar | Statement | Lean |
|---|---|---|
| **P1 Theta rigidity of positive measures** | A Borel measure on `[1, ∞)` with finite `u^{−2}` moment whose theta transform obeys Riemann's degree-one law (or Hamburger's completed FE) is `c Σ_{k≥1} δ_k`, `c = −2 Re α ≥ 0`. | `measure_eq_of_measureTheta_relation`, `measure_eq_of_completed_functional_equation` |
| **P2 Nonnegative frequency rigidity** | Nonnegative generalized Dirichlet series with frequencies `≥ 1` and Riemann's theta law have integer active frequencies; normalized, they are `ζ`. | `nonneg_freq_rigidity_of_theta_relation`, `freqDirichlet_eq_riemannZeta_of_completed_functional_equation` |
| **P3 Complex Fejér–tent law** | For arbitrary complex coefficients a self-dual theta relation forces `α + β = 0` and `Σ a_n (sin πλ_n/πλ_n)² = 0`. | `tsum_sin_sq_div_sq_eq_zero_of_freqTheta_relation` |
| **P4 Beurling selectivity** | A Beurling prime measure generates integers with Riemann's theta law iff it is `Σ (Λ(n)/log n) δ_n`. | `eq_riemannPrimeMeasure_of_beurling_functional_equation` |
| **P5 The degree-one FE-complete class is `{ζ}`** | A countable Beurling system with Riemann's completed FE has the simple pole forced, integers = positive integers, `beurlingZeta = ζ`, labels = rational primes. | `beurlingSystem_rigidity_of_completed_functional_equation` |
| **P6 Poisson rigidity** | A locally finite positive measure with gap `(−1, 1) ∖ {0}` is self-dual on the tent translates iff it is `μ{0} Σ_n δ_n`; a wider gap forces `μ = 0`. | `tentSelfDual_iff_eq_smul_diracComb`, `eq_zero_of_wide_gap` |
| **P7 One-sided density law** | If only the dual side has the gap, `μ ⋆ sinc(π·)² ≡ ν{0}` and `μ[s − ½, s + ½] ≤ (π²/4) ν{0}`. | `integral_sincSq_shift_eq`, `measure_Icc_le_of_poissonPair` |
| **P8 Integer classification** | On every abelian group: integer-valued even positive definite with `φ(0) = 1` ⇔ sign character of a subgroup; isolation forces `1_{0}` ⇔ no 2-torsion. | `intValued_posDef_iff_signCharacter`, `isolation_forces_dirac_iff` |
| **P9 Herglotz–Bochner on `ℤ^ι`** | Positive definite on `ℤ^ι` ⇔ coefficients of a finite positive measure on the torus; restriction is Kronecker push-forward. | `isPosDefOnLattice_iff`, `fourierCoeff_map_kroneckerLine` |
| **P10 The barrier of a certificate is the barrier of its fibre** | Weight on `±ω` ≤ `2cos(π/(K+2))` × weight at `0`, `K` the fibre degree; attained on every spectrum containing `0, …, Kω`. | `fibre_purchase_le_fejer`, `multiFrequency_purchase_le_fibre_fejer`, `fibre_barrier_attained` |
| **P11 Independent channels** | No channel raises another's barrier; for two channels the joint barrier is the product, attained by product extremals; two zeros at equal depth are excluded iff `√A + √(Gη) < √(B₁+B₂)`, width below `(1 − (ρ_K+ρ_L)^{−1/2})²/L < 1/(4L)`. | `independentChannel_purchase_le_fejer`, `twoChannel_joint_barrier_attained`, `twoChannel_width_cap` |
| **P12 The two-prime orbit is a Bochner problem** | RH ⇔ the spline correlation on `ℤ log p + ℤ log q` is positive definite on `ℤ²` ⇔ it is the coefficient sequence of a positive measure on `T²`. | `riemannHypothesis_iff_isPosDefOnLattice_twoPrimeCorr`, `riemannHypothesis_iff_exists_torusMeasure` |
| **P13 Restriction–induction** | A function on a subgroup extends to a positive-definite function on the group iff it is positive definite; RH ⇔ some positive-definite function on the affine group of `ℚ` restricts to the spline correlation on the dilations. | `exists_isPosDefOnGroup_extension_iff`, `riemannHypothesis_iff_exists_affine_posDef` |
| **P14 Topology of the blind ideal** | Closed in the natural Fréchet topology, unconditionally; dense in the critical-jet topology; closed there (or in any coarser topology) iff RH. | `isClosed_meyerTraceBoundedIdeal`, `dense_meyerTraceBoundedIdeal_criticalJet`, `isClosed_criticalJet_iff`, `rh_of_isClosed_of_criticalJetTopology_le` |
| **P15 Quantum budget** | Admissible zero orders are exactly `m ≤ (√A + √(Gη))²/B`; forcing iff budget `< 1` (`< 2` for even invariants); boundary budget `A/B > ½`; at `η = ½` the budget of every Fejér certificate is `≥ 1` once `L ≥ 2(1 − 2^{−1/2})²` and `≥ 2` once `L ≥ 1`. | `admissible_iff_le_quantumBudget`, `forces_zero_iff_quantumBudget_lt_one`, `forces_even_zero_iff_quantumBudget_lt_two`, `fejer_quantumBudget_half` |
| **P16 Weil over `𝔽_q` is positive definiteness on `ℤ`** | For a curve datum: RH ⇔ the trace sequence is positive definite on `ℤ` ⇔ `|τ| ≤ 2g` ⇔ Hasse–Weil ⇔ span Hodge index; the golden datum fails, on every group. | `curve_rh_tfae`, `not_isEvenPosDef_goldenDatum_traceSeq`, `not_exists_posDef_golden` |

The Hamburger input of P1, P4, P5 is part of the statement: the remainder `E` is holomorphic on the
strip `(−½, 3/2)` with `O(1/(1 + t²))` decay. Cite it as "FE in Hamburger's form".

---

## 6. The questions and their answers

1. **Rank-`r` boundary law.** *Classify integer-valued even positive-definite functions with unit
   mass at every rank.* They are the sign characters of subgroups, on every abelian group, and
   isolation leaves only `1_{0}` exactly on groups without 2-torsion (P8). The classification is
   rank-independent; the sharpness models are the order-two sign characters and MPG's realized
   boundary data. For `ζ`, `D_ζ = 1_{0}` on `ℝ` restricts to `1_{0}` on every subgroup: rank two
   forces nothing beyond rank one.
2. **Interior continuation.** *Which positive-definiteness constraints survive into the strip when
   coupled across several heights or primes?* For positive certificates: exactly the rank-one
   constraints of the rational fibres (P10). Incommensurable channels are independent, and their
   joint barrier is the product of the single barriers (P11). Multi-channel positivity is a direct
   sum of one-channel problems; any interior gain must come from the growth input.
3. **Prime-side Bochner.** *Characterize the positive measures on `T²` with coefficients the
   two-prime orbit correlations.* They exist iff RH (P12); when the correlation extends to a
   characteristic function on `ℝ`, the measure is the Kronecker push-forward of its spectral
   measure (P9). This is a receiver: it fixes the object a rank-two forcing law must construct.
4. **Quantized budget.** *Which integer plays the pole's role at the critical line?* On `Re s = 1`
   the zero order, with budget `A/B ∈ (½, 1]`. In multiplicative positivity there is no budget below
   the first quantum at `Re s = ½`, and parity does not rescue it, at every height scale `L ≥ 1`
   (P15). On the quadratic side the integer is the Hodge defect, even, with the pole plane's single
   positive square as budget: RH ⇔ defect `≤ 1` (`riemannHypothesis_iff_splineOrbit_negIndex_le_one`).
5. **Poisson rigidity.** *Which exact sums of nonnegative terms equal a constant, and what do they
   force?* On a self-dual positive pair with a gap: lattice support and equal atoms, with the unit
   gap as threshold (P6); the theta law is the same mechanism tested on Gaussians (P1). On a pair
   with the gap on the side opposite the positivity: only uniform local mass (P7). On the Weil pair
   the prime side carries both the positivity and the prime-free gap, so only density statements
   are available there.
6. **Non-commutative carrier.** *Does a positive functional on the affine group carry more than the
   Weil form?* No. Positivity on the affine group is induced from the dilations: a prescribed
   dilation restriction extends iff it is positive definite, and the successor part can be set to
   zero (P13). The opening closes as a source of positivity; a forcing law there must prescribe the
   successor coordinates from the arithmetic source.
7. **Topology.** *Which completion keeps every critical jet and closes the blind ideal?* The natural
   Fréchet topology of the Meyer source does both, unconditionally. No topology built from critical
   data alone closes it unless RH (P14): closedness of the blind ideal is information about the
   off-line divisor.

**Calibration.** Over `𝔽_q` every step is Weil's: the prime side is a positive-definite function on
`ℤ` of integer mass `2g`, the two-point Gram form is Hasse–Weil, and the golden datum fails (P16).

---

## 7. Traps

| Trap | Truth |
|---|---|
| FE + positivity is an axiom system with many models | At degree one on Beurling systems its only model is `ζ` (P5) |
| Hamburger's theorem uses only the FE | The remainder must be holomorphic on the strip with quadratic decay |
| The FE is a self-duality of the Weil pair | It is a self-duality of the integer measure; on the Weil pair positivity and gap sit on the same side (P7) |
| A self-dual positive measure with any gap is a lattice | Only with the unit gap; a wider gap kills it (P6) |
| Coupling more heights or primes buys more per zero | The barrier of each channel is the barrier of its fibre (P10) |
| Independent channels share one barrier | Their barriers add: the joint barrier is the product (P11) |
| Rank two decides RH, so rank-two positivity is progress | The two-prime Bochner problem is a receiver (P12) |
| A non-commutative carrier adds positivity | Affine positivity is induced from the dilations (P13) |
| Closedness of the blind ideal is a critical property | Critical data make it dense (P14) |
| Parity rescues quantization at the critical line | Not for `L ≥ 1` (P15) |
| Integer values force vanishing | Only with unit mass and positive definiteness, and isolation needs no 2-torsion (P8) |
| Integer point counts force RH over `𝔽_q` | The golden datum has them and fails positive definiteness (P16) |
| A finite box of `ℤ²` is a rank-two theorem | It is a bounded-aperture condition with width resolution `½` |

---

## 8. Tools

Built:

- Fejér-tent pairing for Laplace identities, real and complex coefficients; measure-theoretic
  Hamburger theorem; Beurling prime measures and their theta law;
- tent transforms, integer-supported measures, the Dirac comb, the gap calculus;
- positive-definite functions on `ℤ^ι` with complex coefficients; lattice Fejér densities;
  Herglotz–Bochner on `ℤ^ι`; Kronecker push-forward;
- positive-definite functions on groups; restriction, pull-back, induction from subgroups; the
  affine group of `ℚ`;
- sign characters of subgroups and coset factorization;
- Bohr projection of certificates onto rational fibres; independent-channel fibres; product
  certificates; two-zero exclusion and width caps;
- the quantum budget calculus;
- the critical-jet topology of the Meyer source and critical interpolation;
- the trace sequence of a curve datum.

To build: rank-`r` arithmetic realization of boundary profiles by `ζ`-twists; Bochner–Schwartz
for the Weil distribution beyond characteristic functions; Fourier analysis on the full group
`ℚ_{>0}` (infinite rank).

---

## 9. Open research topics

1. **The third forcing instance in the strip.** An exact identity on the Weil pair whose two sides
   have different regularity, with a quantization step, not available from P6–P15.
2. **Prescribed successor coordinates.** A positive functional on the affine group whose successor
   part is fixed by the arithmetic source (a Hecke or Bost–Connes state), and the positivity it
   forces on the dilations.
3. **Rank-`r` realization.** Which positive-definite profiles on `ℤ^r` are boundary profiles of
   integral (Beurling) systems.
4. **Positive crystalline measures beyond degree one.** Self-dual positive pairs with gaps under
   `Γ_ℝ^d` self-duality; degree-`d` abundance as the control group.
5. **Integer budgets in the strip.** Torsion orders, finite affine quotients, Hecke-cycle lattices:
   an integer invariant bounded by a computable budget below its first nonzero value, on a carrier
   outside multiplicative positivity.
6. **Spectral synthesis in the blind ideal.** Is the span of critical jet sources dense in the blind
   ideal for the natural topology? (Its closure is a limit statement of exhaustion.)
7. **Signed additive prime correlations** at the square-root threshold as the analytic face of the
   duality (TTPC).

---

## 10. Success criteria and contribution standard

The criteria of the founding proposal and their status:

- a rank-two boundary law with sharpness models (P8), and an interior law with explicit growth input
  and barrier (P11);
- a quantized inequality in the strip, or a proof that a stated class has none: the multiplicative
  class has none at the critical line (P15); the quadratic class has the parity law of the Hodge
  defect;
- a topology on the Meyer source in which the maximal blind ideal is closed (P14);
- the reduction over `𝔽_q` to Weil's theorem with the integer budget `2g` (P16);
- every rigidity theorem formalized with no RH-equivalent hypothesis.

Open: the third forcing instance in the strip (topic 1); the reproduction in APD coordinates of
analytic output beyond the classical zero-free regions (zero-density exponents, pair correlation).

A contribution must:

1. be an unconditional Lean theorem;
2. name its positive side, its spectral side, its gap and its integer;
3. state an exact identity, a classification, a sharp barrier or a rigidity law, not a new
   equivalent of RH;
4. say what it gives on the battery: curves (must reproduce Weil), the golden datum (must fail),
   Beurling countermodels;
5. record the positive survivor of every no-go.

Principles: positivity on one side is known, positivity on the other is the theorem; rigidity
before estimates; every forcing step names its integer and its budget; rank helps on the zero side,
not on the prime side; calibrate over `𝔽_q`.

---

## 11. Modules

| Module | Content |
|---|---|
| `PositiveMeasureHamburgerRigidity` | Theta and Mellin transforms of measures; Fejér pairing; measure-theoretic Hamburger rigidity; Beurling prime-measure selectivity |
| `BeurlingRiemannFunctionalEquationRigidity` | Complex Fejér–tent law; nonnegative generalized Dirichlet series; rigidity of countable Beurling systems |
| `PositiveSelfDualMeasuresWithAGapAreDiracCombs` | Poisson rigidity, the unit-gap threshold, the one-sided density law |
| `IntegerPositiveDefiniteFunctionsAreSignCharacters` | Integer classification on abelian groups; isolation and 2-torsion |
| `HerglotzBochnerOnLattices` | Positive-definite functions on `ℤ^ι`; Fejér measures; Herglotz–Bochner; Kronecker push-forward |
| `TheBarrierOfACertificateIsTheBarrierOfItsFibre` | Bohr projection; exact fibre barrier; independent channels; joint barrier; rank-two interior law |
| `TheTwoPrimeSplineOrbitIsABochnerProblemOnTheTorus` | Toeplitz structure of spline Grams; RH ⇔ positive measure on `T²` |
| `AffinePositivityIsInducedFromTheDilations` | Positive definiteness on groups; restriction–induction; the affine group of `ℚ`; the golden datum on any group |
| `TheBlindIdealIsClosedOnlyWhereOffLineZerosAreSeen` | Natural topology closes the blind ideal; critical-jet topology makes it dense |
| `TheQuantumBudgetOfMultiplicativePositivity` | Quantum budget, parity, boundary and critical-line budgets |
| `WeilsTheoremForCurvesIsPositiveDefinitenessOnZ` | The `𝔽_q` calibration with budget `2g` |
