# Arithmetic Positive Duality (APD)

**One question.** The explicit formula is a Poisson summation formula between two measures on the
line: the prime measure, positive because `Λ ≥ 0`, and the zero measure, positive exactly when RH
holds. Everything the corpus has ever *forced* about `ζ` has one shape: positivity, an exact
self-dual identity and an integer together give rigidity. What is the complete rigidity and
capacity theory of positive arithmetic distributions under Poisson self-duality and integer
quantization? What can positivity on the prime side force on the zero side, how much zero charge
can each positive structure carry, and which structure carries none?

Working subtitle: *positivity on both sides of the explicit formula.*

APD is the rigidity theory of **positive Poisson pairs**: pairs `(μ, μ̂)` of measures, one side
carrying arithmetic support (`± log n`, lattices, `S`-unit groups `ℤ log p₁ + ⋯ + ℤ log p_r`), the
other a spectrum. Its basic objects are positive-definite functions on groups of finite rank and
their Fourier measures on tori. Its basic mechanism is the **spectral gap identity**: an exact sum
of nonnegative terms equals a computable constant, and integrality or self-duality turns the
identity into rigidity. Its basic measurement is **capacity**: the zero charge a positive
structure can carry at a given distance from the line of positivity, and the integer that pays for
it.

The theory separates two kinds of zero charge. **Inserted** charge is created by deforming a
positive system; the pole pays for it exactly. **Intrinsic** charge is the zero set of `ζ` itself;
no pole count reaches it, and it is paid, if at all, by oscillation of the zero sum. RH is the
statement that the intrinsic off-line charge of `ζ` is zero.

Namespace `GaloisForLFunctions.ArithmeticPositiveDuality`; umbrella `ArithmeticPositiveDuality.lean`.
Everything is unconditional; RH appears only inside equivalences.

---

## 1. Place in the research

The walls of the frontier are three readings of one sentence: *what forces the actual arithmetic
source to be blind to off-line zeros?* (rate W1, transfer W3, carrier W14). Over `𝔽_q` the three
answers are one object: an intersection theory with integer pairing, finite rank, positivity from
counting sections, and a base over which tensor powers have nonnegative traces. Over `ℤ` the corpus
has the pairing, the Lefschetz and adjunction identities, the signature law and the maximal blind
carrier, and it has proved that the missing ingredient is a structure, not an estimate.

The exhaustion theorems of the corpus cover these classes:

| Class of mechanism | Exhausting theorem |
|---|---|
| Quadratic positivity on a sharp-stable convolution ideal of the scaling flow | lies in the maximal blind ideal (`isGreatest_meyerSharpPositiveIdeal`) |
| Quadratic positivity on a scale-shift-invariant test space | blind (`zeta_blindOffLine_of_scaleShift_subspace_weil_nonneg`) |
| Finite harmonic (multiplicative) coupling by a nonnegative cosine polynomial | Fejér barrier; interior gain only from growth input (MPG) |
| Multi-channel positive certificates (several heights, primes, harmonics) | a direct sum of one-channel problems, one per rational fibre (P10, P11) |
| Height-coupled positivity in completed positive systems | boundary capacity and a `1/log T` collar with at most `κ²` exceptions (SBWF) |
| Integer quantization in de la Vallée Poussin's coupling | no budget below the first (even) quantum at the critical line (P15) |
| Pole order on positive relative deformations | exact index–pole conservation; pays inserted charge only (RHTower) |
| Positive relative deformations of `ξ` at pole order one | none: `E = cξ` (SBWF) |
| Positive functionals on the affine (successor and dilation) group | induced from the dilations; the successor part is free (P13) |
| Finitely many linear readings, with or without mass | cannot supply Bézout (ACS) |
| Finite-dimensional affine-unitary carriers | trivial (`finite_affine_unitary_rigidity`) |

Two theorems of the corpus are *forcing* theorems, and they share one shape:

- **boundary forcing** (MPG): the boundary divisor of nonnegative Euler log-coefficients is an even
  positive-definite function on `ℝ`; integer values and a unit pole make it a sign character of a
  subgroup; pole isolation makes it `δ₀`, so `ζ(1+it) ≠ 0` (`boundary_forcing_law`);
- **theta forcing** (P1–P5): a positive measure on `[1, ∞)` whose theta transform obeys Riemann's
  self-dual law is a Dirac comb on the positive integers; on a Beurling system the functional
  equation forces `ζ` itself (`measure_eq_of_measureTheta_relation`,
  `beurlingSystem_rigidity_of_completed_functional_equation`).

Two theorems are *capacity* laws, and they share one shape as well:

- **boundary capacity** (MPG, SBWF): a pole of order `k` carries at most `⌊k/2⌋` boundary zeros,
  every placement realized; in completed positive systems `κ < 2Σm` forces a zero off `Re s = 1`;
- **relative conservation** (RHTower, SBWF): for positive deformations of `ζ`, the Weil-index
  increment equals the pole-order increment plus the critical traffic `R_crit − I_crit`; at pole
  order one no deformation exists.

APD is the field in which these four are instances of one law. Its open core is the **third forcing
instance in the strip**: a law that bounds intrinsic charge. The capacity laws locate it. Whatever
it is, its integer is not pole charge, and its gain cannot scale with its arithmetic cost.

| Programme | Interface |
|---|---|
| [MultiplicativePositivityGeometry](../MultiplicativePositivityGeometry/README.md) | The rank-one height side: boundary divisor, Fejér barrier, growth-to-forcing law, boundary capacity. APD extends its positive-definite calculus to every rank, computes the multi-channel barrier and the quantum budget. |
| [StripBochnerWeilForcing](../StripBochnerWeilForcing/README.md) | The strip side of height positivity: the coupled strip Bochner–Weil form, completed positive systems, collective boundary capacity, gauge collapse, pole-order-one rigidity. |
| RHTower deformations (`PoleOrderTwoRealStray`, `RefundedComplexStray`, `WeilIndexConservation`, `TwinRigidityPoleOrder`) | The battery of positive relative deformations and their exact bookkeeping. |
| [ArithmeticOrientationGeometry](../ArithmeticOrientationGeometry/README.md) | The scale side: orientation is positive definiteness of the orbit correlation; the spline orbit and its two-prime Hecke orbit decide RH. APD reads the two-prime orbit as a Bochner problem on `T²`. |
| [ArithmeticCastelnuovoSeveri](../ArithmeticCastelnuovoSeveri/README.md) | Maximal blind ideal, Meyer source, Frobenius span, golden datum; `ArithmeticForcesBlindness` uses this programme's Hamburger rigidity. APD settles the topology of the blind ideal and restates the span Hodge index as positive definiteness on `ℤ`. |
| [BiarithmeticGeometry](../BiarithmeticGeometry/README.md), [SignedSuccessorArithmetic](../SignedSuccessorArithmetic/README.md) | The successor and the affine action. APD proves that affine positivity is induced from the dilations. |
| [ArithmeticDefectRigidity](../ArithmeticDefectRigidity/README.md), ArithmeticContinuationAndCriticalEnergy | The limits: cofactor modules and their escape states, averaged and aperture-flow positivity. APD supplies their spectral readings. |
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
positive measure (AOG). One side is known; the other is the theorem. The prime-free gap
`|x| < log 2` lies on the known side, so gap rigidity on the Weil pair yields density statements,
not lattice support (P7, P17).

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

**Capacity is counted by the pole, on the boundary and for inserted charge.** On `Re s = 1` the
Følner Gram forms of the boundary divisor bound the total zero mass at any finite set of heights by
`D(0)/2`: a pole of order `k` pays for `⌊k/2⌋` zeros. Inside the strip, a positive deformation of
`ζ` is a reflection-antisymmetric correction of its logarithmic measure. Local finiteness at `x = 1`
forces the trace condition, and the trace condition makes the pole order count the inserted
frequency pairs minus the removed ones. Each critical pair removed refunds one unit, so pole order
two buys a real off-line pair, or a complex quartet with one refund. At pole order one the
reflection `s ↦ 1 − s` and Landau's continuation leave no room: a positive Laplace correction of
`ξ` with the functional equation is zero.

**Intrinsic charge is not counted by the pole.** The bookkeeping identity is an equality between
increments. Applied to `ζ` it gives only lower bounds on the Weil index of `ζ`, never an upper bound,
and the absolute inequality `ind₋ ≤ ord₁F − 1` is false. The zeros of `ζ` itself are not the result
of a deformation of anything; their payment is the oscillation of the zero sum, which the pole does
not see. The third forcing instance must read that oscillation.

**Rank matters, on one side only.** Rank one in the height variable forces only the boundary.
Rank in the height variable adds nothing per channel: a multi-channel certificate splits into
rational fibres, and in completed systems coupling heights gives boundary capacity only. Rank one in
the scale variable is blind (a single prime tower is Toeplitz-blind to symmetric Wolff
configurations), and rank two in the scale variable decides RH. Rank helps on the zero side, not on
the prime side.

**Amplification is depth-homogeneous over `ℤ`.** Harmonic twists `n^{−ikt}` are tensor powers of
unitary characters: their zeros keep the real part while the growth input rises with the degree.
Følner coupling gains on a zero's depth only through `1 − β`. Family averages and absolute tensor
powers gain on depth as fast as they pay in arithmetic length. Over `𝔽_q` Deligne's argument escapes
this through a base: even tensor powers of a self-dual system have nonnegative traces, their pole
part is computed by monodromy invariants, and the loss over the base is fixed, so it disappears
under `2k`-th roots. A forcing step over `ℤ` needs a term that does not scale with its
amplification.

---

## 3. Objects and language

| Object | Meaning | Lean |
|---|---|---|
| Poisson pair | `(μ, ν)` with `∫ 𝓕g dμ = ∫ g dν` on a stated test class; *self-dual* when `ν = μ` | `IsTentSelfDual` |
| Gap | `(−a, a) ∖ {0}` carrying no mass | hypothesis `μ (Ioo (-1) 1 \ {0}) = 0` |
| Fejér tent | `max(0, 1 − |x|)`, transform `sinc(πξ)²` | `tentAt`, `modTent`, `fourier_tentAt` |
| Dirac comb | `Σ_{n ∈ ℤ} δ_n` | `diracComb` |
| Prime measure | `½ Σ Λ(n) n^{−1−x} (δ_{log n} + δ_{−log n})`, `x > 0` | `primeMeasure` |
| Positive-definite function | all Gram forms nonnegative, on `ℤ^ι`, on a group, on an additive group (real, even) | `IsPosDefOnLattice`, `IsPosDefOnGroup`, `IsEvenPosDef` |
| Fourier measure | finite measure on `ℝ^ι` read through `θ ↦ e^{i⟨m, θ⟩}`, `m ∈ ℤ^ι` | `fourierCoeff`, `latticeChar` |
| Kronecker line | `t ↦ (γ_i t)_i`; restriction to `{⟨m, γ⟩}` is push-forward along it | `kroneckerLine` |
| Certificate, fibre | `Σ c_i cos(λ_i t) ≥ 0`; the modes with `λ_i ∈ ℤω` | `fibreCoeff`, `Resonant` |
| Independent channels | `ℚ`-independent frequencies `γ_j`, spectrum `⟨k, γ⟩` | `channelFreq` |
| Sign character | `χ : H → {±1}` additive to multiplicative, extended by zero | `IsSignCharacter`, `extendByZero` |
| Quantum budget | `b(η) = (√A + √(Gη))²/B`: the largest admissible zero order at distance `η` | `quantumBudget` |
| Boundary capacity divisor | `kδ₀ − Σ m_z(δ_z + δ_{−z})`, `2Σ m_z ≤ k` | `capacityDivisor` (MPG) |
| Completed positive system | `F` positive definite in the heights on `Re s > 1`; entire order-one `Λ = (s(s−1))^κ Γ_ℝ^d F` with `Λ(1−s) = Λ(s)` | `CompletedPositiveSystem` (SBWF) |
| Relative deformation | reflection-antisymmetric correction of `ζ`'s log measure; frequency pairs inserted `I_off, I_crit`, removed `R_off, R_crit` | `poleIncrement`, `indexIncrement` (RHTower) |
| Refund | removal of a critical pair, returning one unit of pole budget | `refundTransform` (RHTower) |
| Inserted / intrinsic charge | off-line zeros created by a deformation / the off-line zeros of `ζ` itself | — |
| Coefficient system over a base | a self-dual system `F` over a base `B` whose even tensor powers have nonnegative log-coefficients and computable pole part | — (over `𝔽_q`: Deligne) |
| Coupled scale carrier | a test space or source coupling several dilation channels (two dilated copies, `ζ(s)ζ(s+iτ)`, `Λ ⋆ Λ`) | — |
| Spectral profile | the function whose Fourier transform is a source's Mellin data on `Re s = ½`; for the cofactor Gram, `G(s) = ζ(s)(1/ζ(s+ε) − 1/ζ(1+ε))/s` | — |
| Affine group of `ℚ` | `x ↦ ax + b`; dilations and successor | `AffineGroupQ`, `dilation`, `successor` |
| Critical-jet topology | coarsest topology making all critical Meyer jets continuous | `criticalJetTopology` |
| Battery | golden datum `1 − 5X + 5X²`, curves, Wolff configurations, Beurling countermodels, pole-order-two strays, refunded quartets, twisted boundary systems | `goldenDatum`, `CurveDatum` |

**Words.** *Positive side* / *spectral side*: the side with known positivity / the side whose
positivity is the theorem. *Forcing*: an unconditional theorem whose conclusion is a vanishing on
the spectral side. *Capacity*: the largest zero charge a stated positive structure admits at a
stated distance. *Receiver*: an RH-equivalent reformulation; it never produces its own input.
*Height side* / *scale side*: the two Fourier-dual variables of the explicit formula. *Inserted* /
*intrinsic*: charge created by deformation / charge of the source itself. *Dominated payment* /
*oscillatory payment*: a zero paid by a pole unit through a nonnegative density / a zero paid by
cancellation in the zero sum. *Depth-homogeneous*: a gain on a zero's depth that scales with the
arithmetic cost of the amplification producing it.

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
12. **Følner capacity.** The sets `{Σ n_z z : 0 ≤ n_z < N}` grow polynomially, so some step grows by
    at most `1 + ε`; their Gram forms see every zero with weight about `|F_N|`, which bounds the
    total zero mass by `D(0)/2` (`total_zero_mass_le`). In a completed system, Hadamard's zero-pair
    series turns the same Gram forms into `Σ m(Re 1/(s−ρ) + Re 1/(s−ρ̄)) ≤ Re(Λ'/Λ)(s)`
    (`sum_orbit_resolvent_le_re_logDeriv`).
13. **Trace bookkeeping.** Local finiteness of a positive log measure at `x = 1` forces the
    coefficients of a reflection-antisymmetric correction to sum to zero; the pole order is the
    coefficient at the admissible frequency `½`, and every other frequency pair is an inserted or
    removed zero (`poleOrderBudget`).
14. **Refund rigidity.** A positive Laplace correction of `ξ'/ξ` continues to the whole real axis by
    Landau's theorem; evaluated under `s ↦ 1 − s` at two points it vanishes on `(0, ∞)`
    (`simple_pole_nonneg_laplace_refund_rigidity`).

---

## 5. Pillar theorems

| Pillar | Statement | Lean |
|---|---|---|
| **P1 Theta rigidity of positive measures** | A Borel measure on `[1, ∞)` with finite `u^{−2}` moment whose theta transform obeys Riemann's degree-one law (or Hamburger's completed FE) is `c Σ_{k≥1} δ_k`, `c = −2 Re α ≥ 0`. | `measure_eq_of_measureTheta_relation`, `measure_eq_of_completed_functional_equation` |
| **P2 Nonnegative frequency rigidity** | Nonnegative generalized Dirichlet series with frequencies `≥ 1` and Riemann's theta law have integer active frequencies; normalized, they are `ζ`. | `nonneg_freq_rigidity_of_theta_relation`, `freqDirichlet_eq_riemannZeta_of_completed_functional_equation` |
| **P3 Complex Fejér–tent law** | For arbitrary complex coefficients a self-dual theta relation forces `α + β = 0` and `Σ a_n (sin πλ_n/πλ_n)² = 0`. | `tsum_sin_sq_div_sq_eq_zero_of_freqTheta_relation` |
| **P4 Beurling selectivity** | A Beurling prime measure generates integers with Riemann's theta law iff it is `Σ (Λ(n)/log n) δ_n`. | `eq_riemannPrimeMeasure_of_beurling_functional_equation` |
| **P5 The degree-one FE-complete class is `{ζ}`** | A countable Beurling system with Riemann's completed FE has the simple pole forced, integers = positive integers, `beurlingZeta = ζ`, labels = rational primes. | `beurlingSystem_rigidity_of_completed_functional_equation` |
| **P6 Poisson rigidity** | A locally finite positive measure with gap `(−1, 1) ∖ {0}` is self-dual on the tent translates iff it is `μ{0} Σ_n δ_n`; a wider gap forces `μ = 0`; for every gap `a < 1` the dual lattices `Σ δ_{am} + a⁻¹ Σ δ_{k/a}` are self-dual and no comb, so the unit gap is sharp. | `tentSelfDual_iff_eq_smul_diracComb`, `eq_zero_of_wide_gap`, `exists_tentSelfDual_not_comb` |
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
| **P17 Positivity on both sides** | The damped prime measure `½ Σ Λ(n) n^{−1−x}(δ_{log n} + δ_{−log n})` is finite positive with characteristic function `Re(−ζ'/ζ)(1+x+iu)`, unconditionally; RH ⇔ every scale function `y ↦ W(τ_y(f ⋆ f̃))` is the characteristic function of a finite positive measure; on prime-free tests Weil's functional has no prime term; the two-prime correlation at `s` reads only `n` with `|log n ∓ s| ≤ 8`. | `positive_duality_of_the_explicit_formula`, `charFun_primeMeasure`, `weilFullFunctional_of_prime_free`, `splineCorr_prime_term_eq_zero` |
| **P18 The integer successor forces the Hecke weight** | A positive-definite `φ` on `Aff(ℚ)` with successor part `1_ℤ` satisfies `nd Σ_b ‖φ(x ↦ ux + b)‖² ≤ 1` at `u = ±n/d`, over classes `b` of `ℚ/(1/d)ℤ`; the adelic Haar state `(nd)^{−1/2}·1[db ∈ ℤ]` is positive definite and attains it. A successor part `c·1_ℤ` with a dilation part continuous at `1` forces `c = 0`; the spline correlation never meets the integer successor. | `heckeBessel`, `integer_successor_hecke_weight`, `successor_scale_eq_zero_of_continuousAt`, `splineCorr_zero_of_integer_successor` |
| **P19 The critical line is the positivity threshold of the integer successor** | The Hecke state `(nd)^{−s}·1[db ∈ ℤ]` on `Aff(ℚ)` is positive definite iff `s ≥ 1/2`, while the dilation weights `(nd)^{−s}` alone are positive definite for every `s ≥ 0`; the slope weights `(nd)^{−t}`, `t ≥ 0`, multiply positive definiteness, through `gcd^{2t} = Σ_{d∣L} J_{2t}(d)1[d∣A]1[d∣A']` with the Jordan totient `J_α ≥ 0`. | `isPosDefOnGroup_heckeState_iff`, `isPosDefOnGroup_dilation_powerWeight`, `IsPosDefOnGroup.mul_slopeWeight`, `jordan_nonneg` |
| **P20 The Bost–Connes temperature is the Hecke exponent** | For any positive-definite `φ` on `Aff(ℚ)` with `ℤ`-periodic successor `ψ`, `‖φ(x ↦ ux)‖² ≤ A_ψ(n)A_ψ(d)`, where `A_ψ(q)` is the mass of `qẐ` under the spectral measure of `ψ`. The Bost–Connes successor `ψ_β = Z_β⁻¹Σ m^{−β}e(m·)`, `β > 1`, has `A(q) = q^{−β}`, so it forces `(nd)^{−β/2}`; the ground state of `ℓ²(ℚ)` attains it. At `β = 1` the law is P18. | `normSq_dilation_le_successorDensity`, `bcDensity`, `isPosDefOnGroup_bcState`, `bc_successor_hecke_exponent` |
| **P21 The extremals of the Hecke law are twisted Haar states** | A positive-definite `φ` on `Aff(ℚ)` with integer successor attains `nd‖φ(x ↦ ux)‖² = 1` at every dilation iff `φ(g) = φ_*(g)χ(slope g)` with `φ_*` the adelic Haar state and `χ` a unitary character of `ℚ^×`; equality forces the two-scale relation `[x ↦ x/m] = m⁻¹λ_m Σ_{j<m}[x ↦ x + j/m]` in the GNS space, which makes the normalized dilation coefficients multiplicative. | `heckeExtremal_iff`, `twistedHaar_posDef`, `IsPosDefOnGroup.null_orth` |
| **P22 A Mautner phenomenon for `Aff(ℚ)`** | If `φ` is positive definite on `Aff(ℚ)`, its successor has one nonzero period (`φ(x ↦ x + h) = φ(1)`) and its dilation part on `ℚ_{>0}` is continuous at `1`, then the successor is constant. For an integer-periodic successor the densities decrease along multiples, `A(kq) ≤ A(q) ≤ φ(1)`, and the successor law along `u = (kq+1)/(kq) → 1` forces `A(q) = φ(1)`. | `translation_eq_of_continuousAt_dilation`, `translation_eq_of_period`, `successorDensity_mul_le` |
| **P23 Herglotz–Bochner on `ℚ_{>0}`** | A function on `ℚ_{>0}` is positive definite iff it is `u ↦ ∫ χ_x(u) dμ(x)` for a finite positive measure on the prime torus `Π_p ℝ/ℤ`, `χ_x(u) = Π_p e^{2πi v_p(u)x_p}`; the measure is unique. | `isPosDefOnGroup_posUnits_iff`, `exists_measure_ratChar`, `finiteMeasure_ext_of_ratChar` |
| **P24 Archimedean positive-definite functions live on the Kronecker line** | If `f(u) = F(log u)` is positive definite on `ℚ_{>0}` with `F` continuous, its spectral measure is the image of a finite measure `ν` on `ℝ` under `x ↦ (x log p/2π)_p`, an injection of `ℝ` (`log 2/log 3 ∉ ℚ`), and `f(u) = ∫ u^{ix} dν(x)`. | `spectralMeasure_eq_map_archPoint`, `spectralMeasure_compl_range_archPoint`, `injective_archPoint` |
| **P25 The integer successor forces a Kronecker-null dilation spectrum** | If `f((N+b)/(N+a)) → 0` for all `a ≠ b`, every spectral measure of `f` gives the Kronecker line mass zero. The integer and Bost–Connes successors force this decay, so the dilation part of such a state dominates no nonzero archimedean positive-definite function. | `spectralMeasure_range_archPoint_eq_zero`, `integer_successor_kronecker_null`, `bc_successor_kronecker_null`, `eq_zero_of_archimedean_le_integer_successor` |
| **P26 Atomic archimedean spectra blind the successor** | If `φ` is positive definite on `Aff(ℚ)` with dilation part `Σ_k c_k u^{iγ_k}` on `u > 0` (`c_k ≥ 0`, distinct `γ_k`, finitely many), then `φ(ux + b) = Σ_k u^{iγ_k}·(c_k if b = 0, α_k if b ≠ 0)` with `0 ≤ α_k ≤ c_k`: a translation-invariant state plus a state induced from the dilations, and every such choice occurs. For a summable countable spectrum, the shape of Weil's correlation under RH, the successor is `α + (φ(1) − α)δ₀`. | `extension_of_finite_archimedean`, `isPosDefOnGroup_archExtension`, `successor_blind_of_finite_archimedean`, `successor_blind_of_atomic_archimedean` |

The Hamburger input of P1, P4, P5 is part of the statement: the remainder `E` is holomorphic on the
strip `(−½, 3/2)` with `O(1/(1 + t²))` decay. Cite it as "FE in Hamburger's form".

**Foundations from sibling programmes.** The capacity half of the theory rests on these theorems,
proved in the programmes that own their objects.

| Foundation | Statement | Lean |
|---|---|---|
| **F1 Boundary forcing** (MPG) | Nonnegative weights, integer divisor, simple pole and pole isolation force `D = δ₀`; each invariant is necessary, with a realized datum. | `boundary_forcing_law` |
| **F2 Boundary capacity** (MPG) | For even positive-definite `D ≤ 0` off zero, `Σ_{z ∈ Z} −D(z) ≤ D(0)/2` at any finite set of positive heights; integer `D` with `D(0) = k` is exactly `kδ₀ − Σ m_z(δ_z + δ_{−z})`, `2Σ m_z ≤ k`, and every placement is realized by nonnegative twisted-Λ weights. | `total_zero_mass_le`, `isolated_boundary_classification`, `capacity_isBoundaryDivisor` |
| **F3 Completed-system capacity** (SBWF) | In a completed positive system, `κ < 2Σm` for zeros at distinct positive ordinates forces one of them off `Re s = 1`; twisting `ζ` at `r` boundary heights realizes `κ = 2r + 1` with `r` boundary zeros; at most `κ²` `Δ`-separated zeros in `[Δ, T]` lie in a collar of width `≍_{κ,Δ} 1/(d log T)`. | `collective_half_pole_interior_forcing`, `exists_completedPositiveSystem_boundary_zeros_at_half_pole`, `card_separated_collar_zeros_le_sq_poleOrder` |
| **F4 Gauge collapse** (SBWF) | An entire finite-order `E = (s(s−1))^κ G` with `E(1−s) = εE(s)`, `G` bounded on a right half-plane and `G(σ) → 1`, is a monic polynomial of degree `2κ`; its off-critical quartets obey `2Σm ≤ κ`. | `exists_monic_poly_of_completed_gauge`, `completed_gauge_zero_and_quartet_budget` |
| **F5 Pole-order-one rigidity** (SBWF) | A nonzero entire `E` with `E(1−s) = εE(s)` and `−E'/E + ξ'/ξ = Laplace(ν)`, `ν ≥ 0`, on a right ray is `cξ`, with `ν|_{(0,∞)} = 0`. | `simple_pole_nonneg_laplace_refund_rigidity` |
| **F6 Inserted charge at pole order two** (RHTower) | A real off-line pair at pole order two; a complex off-line quartet at pole order two after removing one critical pair, for `0 < a ≤ 1/4`. | `lambdaPositive_poleOrderTwo_not_criticalLine`, `lambdaPositive_refunded_complex_stray` |
| **F7 Index–pole conservation** (RHTower) | Weil-index increment = pole-order increment `+ R_crit − I_crit`; the absolute inequality `ind₋ ≤ ord₁F − 1` fails; every deformation bounds the index of `ζ` only from below. | `indexIncrement_eq`, `absolute_inequality_fails`, `indexZeta_lower_bound` |
| **F8 Maximality** (ACS) | Every sharp-stable positive convolution ideal of the Meyer source lies in the off-line-blind ideal, which is the whole source iff RH. | `isGreatest_meyerSharpPositiveIdeal` |

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
   joint barrier is the product of the single barriers (P11). In completed systems the coupled
   height form gives the boundary capacity and a `1/log T` collar (F3). Any interior gain from
   height positivity must come from the growth input.
3. **Prime-side Bochner.** *Characterize the positive measures on `T²` with coefficients the
   two-prime orbit correlations.* They exist iff RH (P12); when the correlation extends to a
   characteristic function on `ℝ`, the measure is the Kronecker push-forward of its spectral
   measure (P9). On the prime side the correlation at `s = k log p + l log q` reads only the prime
   powers in the window `p^k q^l e^{±8}` (P17): rank-two positive definiteness is a statement about
   primes near the `{p, q}`-units. This is a receiver: it fixes the object a rank-two forcing law
   must construct.
4. **Quantized budget.** *Which integer plays the pole's role at the critical line?* On `Re s = 1`
   the zero order, with budget `A/B ∈ (½, 1]` and capacity `⌊k/2⌋` per pole of order `k` (F2). In
   multiplicative positivity there is no budget below the first quantum at `Re s = ½`, and parity
   does not rescue it, at every height scale `L ≥ 1` (P15). On the quadratic side the integer is the
   Hodge defect, even, with the pole plane's single positive square as budget: RH ⇔ defect `≤ 1`
   (`riemannHypothesis_iff_splineOrbit_negIndex_le_one`).
5. **Poisson rigidity.** *Which exact sums of nonnegative terms equal a constant, and what do they
   force?* On a self-dual positive pair with a gap: lattice support and equal atoms, with the unit
   gap as threshold (P6); the theta law is the same mechanism tested on Gaussians (P1). On a pair
   with the gap on the side opposite the positivity: only uniform local mass (P7). On the Weil pair
   the prime side carries both the positivity and the prime-free gap (P17), so only density
   statements are available there.
6. **Non-commutative carrier.** *Does a positive functional on the affine group carry more than the
   Weil form?* No. Positivity on the affine group is induced from the dilations: a prescribed
   dilation restriction extends iff it is positive definite, and the successor part can be set to
   zero (P13). The opening closes as a source of positivity; a forcing law there must prescribe the
   successor coordinates from the arithmetic source.
   Prescribing the successor by the integers forces exactly the Hecke weight `(nd)^{−1/2}` on the
   dilations (P18): the integer successor sees the dilations only `p`-adically, with the critical
   weight `p^{−|k|/2}`, and no archimedean dilation correlation, Weil's included, is compatible
   with it.
   The coupling costs exactly half a unit of exponent: with the integer successor the power weights
   `(nd)^{−s}` survive exactly for `s ≥ 1/2` (P19).
   For the Bost–Connes successor at inverse temperature `β > 1` the forced weight is `(nd)^{−β/2}`
   (P20): the critical temperature `β = 1` of the Bost–Connes system is the critical line.
   Equality in the Hecke law is rigid: its states are the adelic Haar state twisted by unitary
   characters of `ℚ^×` (P21).
   No periodic successor meets an archimedean dilation part: a single period and continuity at `1`
   make the successor constant (P22).
   On the prime torus the two worlds are mutually singular: archimedean dilation correlations,
   Weil's included, are carried by the Kronecker line (P24), while every dilation part forced by the
   integer or Bost–Connes successor gives it mass zero (P25).
   Conversely an atomic archimedean dilation part admits only the two trivial extensions,
   translation-invariant and induced (P26), and Weil's own correlation admits only blind
   successors (`weil_successor_blind`). Every dilation correlation splits canonically into its
   archimedean and Kronecker-null parts (`kronecker_decomposition`), and the critical exponent of
   the integer successor is the Kakutani wall of the prime-Poisson laws
   (`heckeState_kakutani_wall`).
7. **Topology.** *Which completion keeps every critical jet and closes the blind ideal?* The natural
   Fréchet topology of the Meyer source does both, unconditionally. No topology built from critical
   data alone closes it unless RH (P14): closedness of the blind ideal is information about the
   off-line divisor.
8. **What does the pole pay for?** *Does pole order bound off-line zeros?* For inserted charge,
   exactly: the index–pole conservation identity holds, pole order one admits no positive
   deformation and pole order two admits every off-line type (F5–F7). For intrinsic charge, not at
   all: the absolute inequality fails, and every deformation bounds the index of `ζ` only from
   below. The pole is a complete invariant of positive deformations and silent about `ζ`'s own
   zeros.

**Calibration.** Over `𝔽_q` every step is Weil's: the prime side is a positive-definite function on
`ℤ` of integer mass `2g`, the two-point Gram form is Hasse–Weil, and the golden datum fails (P16).

---

## 7. Traps

| Trap | Truth |
|---|---|
| FE + positivity is an axiom system with many models | At degree one on Beurling systems its only model is `ζ` (P5) |
| Hamburger's theorem uses only the FE | The remainder must be holomorphic on the strip with quadratic decay |
| The FE is a self-duality of the Weil pair | It is a self-duality of the integer measure; on the Weil pair positivity and gap sit on the same side (P7, P17) |
| A self-dual positive measure with any gap is a lattice | Only with the unit gap; a wider gap kills it, a narrower one admits two dual lattices (P6) |
| Coupling more heights or primes buys more per zero | The barrier of each channel is the barrier of its fibre (P10); in completed systems coupling buys boundary capacity only (F3) |
| Independent channels share one barrier | Their barriers add: the joint barrier is the product (P11) |
| Rank two decides RH, so rank-two positivity is progress | The two-prime Bochner problem is a receiver (P12) |
| A non-commutative carrier adds positivity | Affine positivity is induced from the dilations (P13) |
| Prescribing the successor from `ℤ` constrains Weil's dilation correlation | It excludes it: the integer successor forces `p`-adic Hecke decay, incompatible with any dilation part continuous at `1` (P18) |
| Some successor prescription carries Weil's correlation | Only blind successors do (`weil_successor_blind`); arithmetic successors force Kronecker-null dilation spectra (P25) |
| Closedness of the blind ideal is a critical property | Critical data make it dense (P14) |
| Parity rescues quantization at the critical line | Not for `L ≥ 1` (P15) |
| Integer values force vanishing | Only with unit mass and positive definiteness, and isolation needs no 2-torsion (P8) |
| Integer point counts force RH over `𝔽_q` | The golden datum has them and fails positive definiteness (P16) |
| A finite box of `ℤ²` is a rank-two theorem | It is a bounded-aperture condition with width resolution `½` |
| Pole order bounds the off-line zeros | It counts inserted charge exactly and intrinsic charge not at all (F7) |
| A complex off-line quartet needs pole order three | Pole order two suffices after one critical refund (F6) |
| `ξ` has positive deformations with the same pole | None at pole order one (F5) |
| A completed gauge can hide an infinite budget | Without an archimedean factor it is a polynomial of degree `2κ` (F4) |
| A larger amplification gives a rate | Over `ℤ` every tested amplification is depth-homogeneous; a rate needs a term that does not scale |

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
- the prime measure and the Bochner form of Weil's criterion;
- the critical-jet topology of the Meyer source and critical interpolation;
- the trace sequence of a curve datum;
- Fourier analysis on `ℚ_{>0}`: Herglotz–Bochner on the prime torus and the Kronecker line;
- the pre-Hilbert space of a positive-definite function on a group;
- in sibling programmes: Følner capacity, completed positive systems and their Hadamard pairing,
  gauge collapse, refund rigidity, deformation bookkeeping.

To build:

- an **oscillatory capacity calculus**: a positive structure whose integer counts intrinsic charge,
  with dominated and oscillatory payment kept apart;
- **coupled scale positivity**: positivity theorems for Weil and Meyer forms on several dilation
  channels at once, and the maximality theorems that delimit them;
- **base constructions**: coefficient systems over `Spec ℤ` with nonnegative even tensor powers and
  a computable pole part;
- **spectral readings of limits**: averaged positivity on height windows as a statement about the
  spectral measure; escape states of cofactor modules as spectral profiles;
- rank-`r` arithmetic realization of boundary profiles by `ζ`-twists and by Beurling systems;
- Bochner–Schwartz for the Weil distribution beyond characteristic functions;

---

## 9. Open research topics

1. **The third forcing instance in the strip.** An exact identity on the Weil pair whose two sides
   have different regularity, with a quantization step, that bounds **intrinsic** charge. The
   capacity laws fix its shape: an integer invariant bounded by a computable budget below its first
   nonzero value, on a carrier outside multiplicative positivity, whose integer is not pole charge.
   Candidate integers: torsion orders, finite affine quotients, Hecke-cycle lattices, the Hodge
   defect with its pole-plane budget.
2. **Oscillatory capacity.** A positive structure that measures the oscillatory payment of `ζ`'s own
   zeros and carries a capacity. Its calibration: zero capacity for `ζ` would be RH; the battery's
   inserted charge must be visible to it with the conservation identity as its relative case.
3. **Coupled scale positivity.** Answered for point-stable carriers coupled by divisor multipliers
   (`CoupledPositivityIsIsotropy`): positivity forces the fibres at `ρ` and `ρ*` to be orthogonal
   for the coupling matrix, not to vanish. Positive convolution ideals without `♯`-stability are
   half-blind; the left-blind ideal (bounded backward flow) is positive and not blind; exhaustion of
   every such carrier is RH. Open: carriers that are not point-stable (Rankin–Selberg sources,
   cones without convolution closure).
4. **A base over `Spec ℤ`.** A base `B` with a simple pole and no zeros; a self-dual system `F` whose
   even tensor powers have nonnegative log-coefficients; a computable pole part of
   `L(B, F^{⊗2k})`; `ζ`'s zeros among those of `L(B, F)`. Then `Re ρ ≤ ½ + O(1/k)` for every `k`.
   Systems definable from multiplicative structure alone are expected to fail on over-regular
   Beurling countermodels; the base must carry more.
5. **Depth homogeneity as a law.** For each amplification class (harmonic twists, Følner coupling,
   family averages over `χ mod q`, absolute tensor powers), a theorem that its gain on depth scales
   with its arithmetic cost, with the positive survivor of each.
6. **Prescribed successor coordinates.** For the integer successor the forced positivity is the
   Hecke weight (P18); its dilation spectra are Kronecker-null (P25), and atomic archimedean
   dilation parts admit only blind successors (P26), so no successor prescription couples the two.
   Open: the classification of the dilation parts compatible with `1_ℤ` (they are not the Hecke
   weight times positive-definite functions); the extensions of continuous archimedean spectra.
7. **Rank-`r` realization.** Which positive-definite profiles on `ℤ^r` are boundary profiles of
   integral (Beurling) systems.
8. **Positive crystalline measures beyond degree one.** Self-dual positive pairs with gaps under
   `Γ_ℝ^d` self-duality; degree-`d` abundance as the control group; the completed positive systems
   of degree `d` as the class.
9. **Equality case of completed capacity.** Whether a completed positive system with even `κ`
   carries boundary zeros of total multiplicity `κ/2`.
10. **Spectral synthesis in the blind ideal.** Answered (`SpectralSynthesisInTheBlindIdeal`):
    every divisor-order ideal is the closure of its jet sources plus the Poisson boundary; the
    critical jet sources synthesize the full-jet blind ideal, which is the blind ideal iff every
    off-line zero is simple, and is everything iff RH.
11. **Spectral readings of the limits.** Short height windows are answered for `H ≥ Γ^{99/100}`
    (ACS `ShortWindowAveragedWeilPositivity`); the negative part at one height is read by the off-line
    field `Φ(γ) = Σ_q (Re q − 1/2)²/(1 + (Im q − γ)²)²`, small at almost every height and almost every
    zero ordinate of such windows (`AlmostEveryHeightIsNearlyWeilPositive`,
    `AlmostEveryZeroOrdinateIsNearlyWeilPositive`). Open: the escape states of cofactor modules as
    horizon Grams of the profile `G(s) = ζ(s)(1/ζ(s+ε) − 1/ζ(1+ε))/s`.
12. **Signed additive prime correlations** at the square-root threshold as the analytic face of the
    duality (TTPC), in particular signed near-coincidence cancellation at one height.

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

The capacity criteria:

- the boundary capacity of a pole and its realization (F2), and its completed-system form (F3);
- the exact accounting of inserted charge by the pole (F6, F7) and the rigidity of pole order one
  (F5);
- open: a capacity for intrinsic charge (topics 1–2); a coupled scale carrier or a coupled
  maximality theorem (topic 3); a base over `Spec ℤ` (topic 4); the reproduction in APD coordinates
  of analytic output beyond the classical zero-free regions (zero-density exponents, pair
  correlation).

A contribution must:

1. be an unconditional Lean theorem;
2. name its positive side, its spectral side, its gap and its integer;
3. say whether its integer counts inserted or intrinsic charge;
4. say how its gain on a zero's depth scales with its arithmetic cost;
5. state an exact identity, a classification, a sharp barrier, a capacity or a rigidity law, not a
   new equivalent of RH;
6. say what it gives on the battery: curves (must reproduce Weil), the golden datum (must fail),
   Beurling countermodels, the pole-order-two strays and refunded quartets (must be separated from
   `ζ`), pole-order-one rigidity (must be reproduced);
7. record the positive survivor of every no-go.

Principles: positivity on one side is known, positivity on the other is the theorem; rigidity
before estimates; every forcing step names its integer and its budget; the pole pays for inserted
charge, oscillation for intrinsic charge; rank helps on the zero side, not on the prime side; a
rate needs a term that does not scale; calibrate over `𝔽_q`.

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
| `PositivityOnBothSidesOfTheExplicitFormula` | The prime measure and its characteristic function; Weil's criterion in Bochner form; the prime-free gap; the two-prime window |
| `TheIntegerSuccessorForcesTheHeckeWeight` | Hermitian symmetry and bi-invariance of positive-definite functions; affine coordinates; the Hecke–Bessel law; the adelic Haar state; incompatibility with archimedean dilation parts |
| `TheCriticalLineIsThePositivityThresholdOfTheIntegerSuccessor` | Jordan totients and GCD-power kernels; slope weights as multipliers; Hecke states and their threshold `s = 1/2` |
| `TheBostConnesTemperatureIsTheHeckeExponent` | Successor densities and the general successor law; Bost–Connes successors; the ground state on `ℓ²(ℚ)` |
| `TheExtremalsOfTheHeckeLawAreTwistedHaarStates` | Null vectors of Gram forms; Hecke-extremal states; the two-scale relation; Hecke characters; twisted Haar states |
| `AMautnerPhenomenonForTheAffineGroupOfQ` | Boundedness of positive-definite functions; monotone successor densities; Mautner rigidity for one period |
| `HerglotzBochnerOnThePositiveRationals` | Valuation vectors and characters of `ℚ_{>0}`; finite-rank stages; Herglotz–Bochner on the prime torus; uniqueness |
| `ArchimedeanPositiveDefiniteFunctionsLiveOnTheKroneckerLine` | The Kronecker line; positive definiteness on `ℝ` by density; spectral measures of archimedean functions |
| `TheIntegerSuccessorForcesAKroneckerNullDilationSpectrum` | Heights of near-identity rationals; decay detects the Kronecker line; integer and Bost–Connes successors; the archimedean dichotomy |
| `GramSpaceOfAPositiveDefiniteFunction` | The pre-Hilbert space of a positive-definite function on a group; translations as isometries |
| `AFiniteArchimedeanSpectrumBlindsTheSuccessor` | Archimedean characters; Lagrange eigenvectors; covariance and block doubling; vanishing cross coefficients; the extensions of a finite archimedean correlation |
| `AnAtomicArchimedeanSpectrumBlindsTheSuccessor` | Two-prime box averages; dilation combinations and their spectral weights; limit states; blindness for summable spectra |
| `TheKroneckerDecompositionOfPositiveDefiniteFunctionsOnQ` | Archimedean and Kronecker-null parts of spectral measures; uniqueness; the largest archimedean minorant |
| `TheCriticalLineOfTheIntegerSuccessorIsTheKakutaniWall` | Local Poisson moments at primes; spectral measures of Hecke weights; the Kakutani wall of Hecke states |
| `WeilsCorrelationCarriesNoSuccessor` | Countable reindexing of atoms; the atomic expansion of Weil's correlation; blindness of its extensions |
