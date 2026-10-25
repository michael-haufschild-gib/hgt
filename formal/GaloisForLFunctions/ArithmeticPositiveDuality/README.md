# Arithmetic Positive Duality (APD)

**One question.** The explicit formula is a Poisson summation formula between two measures on the
line: the prime measure, positive because `Λ ≥ 0`, and the zero measure, positive exactly when RH
holds. Everything the corpus has ever *forced* about `ζ` has one shape: positivity, an exact
self-dual identity, and an integer, together give rigidity. What is the complete rigidity theory of
positive arithmetic distributions under Poisson self-duality and integer quantization, and what can
it force on the zero side?

Working subtitle: *positivity on both sides of the explicit formula.*

APD is the rigidity theory of **positive Poisson pairs**: pairs `(μ, μ̂)` of measures or tempered
distributions, one side carrying arithmetic support (`± log n`, lattices, `S`-unit groups
`ℤ log p₁ + ⋯ + ℤ log p_r`), the other side carrying a spectrum. Its basic objects are
positive-definite functions on groups of finite rank and their Fourier measures on tori. Its basic
mechanism is the **spectral gap identity**: an exact sum of nonnegative terms equals a computable
constant, and integrality turns the identity into rigidity.

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

The exhaustion theorems of the corpus cover these classes:

| Class of mechanism | Exhausting theorem |
|---|---|
| Quadratic positivity on a sharp-stable convolution ideal of the scaling flow | lies in the maximal blind ideal (`isGreatest_meyerSharpPositiveIdeal`) |
| Quadratic positivity on a scale-shift-invariant test space | blind (`zeta_blindOffLine_of_scaleShift_subspace_weil_nonneg`) |
| Finite harmonic (multiplicative) coupling by a nonnegative cosine polynomial | Fejér barrier, interior needs growth input (MPG) |
| Finitely many linear readings, with or without mass | cannot supply Bézout (ACS) |
| Finite-dimensional affine-unitary carriers | trivial (`finite_affine_unitary_rigidity`) |

Two theorems of the corpus are *forcing* theorems, not exhaustion theorems, and they share one
shape:

- **boundary forcing** (MPG): the boundary divisor of nonnegative Euler log-coefficients is an even
  positive-definite function on `ℝ`; integer values and a unit pole make it a `±1` character on a
  subgroup; pole isolation makes it `δ₀`, so `ζ(1+it) ≠ 0` (`boundary_forcing_law`,
  `harmonic_quantized_zero_vanishing`);
- **theta forcing** (this programme): a positive measure on `[1, ∞)` whose theta transform obeys
  Riemann's self-dual law is a Dirac comb on the positive integers; on a Beurling system the
  functional equation forces `ζ` itself (`measure_eq_of_measureTheta_relation`,
  `beurlingSystem_rigidity_of_completed_functional_equation`).

APD is the field in which these two theorems are the first two instances of one law, and whose
research task is the third instance of that law in the critical strip.

| Programme | Interface |
|---|---|
| [MultiplicativePositivityGeometry](../MultiplicativePositivityGeometry/README.md) | The rank-one height side: positive definiteness of the prime side in the height variable; Fejér barrier; growth-to-forcing law. APD extends its positive-definite calculus to groups of finite rank and to tori. |
| [ArithmeticOrientationGeometry](../ArithmeticOrientationGeometry/README.md) | The scale side: orientation is positive definiteness of the orbit correlation; the spline orbit and its two-prime Hecke orbit decide RH. APD reads the two-prime orbit as a Bochner problem on `ℤ²`. |
| [ArithmeticCastelnuovoSeveri](../ArithmeticCastelnuovoSeveri/README.md) | Maximal blind ideal, Wolff tower obstruction, golden datum, `𝔽_q` calibration; `ArithmeticForcesBlindness` (pole-saturated defect annihilation, quantized defect, Fejér saddle ceiling) uses this programme's Hamburger rigidity. |
| [BiarithmeticGeometry](../BiarithmeticGeometry/README.md), [SignedSuccessorArithmetic](../SignedSuccessorArithmetic/README.md) | The successor and the finite affine quotient: the only carriers using both ring operations. |
| [ScaleSignedIncidenceCriticality](../ScaleSignedIncidenceCriticality/README.md) | Prices every reading; a finite box of `ℤ²` is a bounded-aperture condition. |
| [BiScaleUncertainty](../BiScaleUncertainty/README.md), [TransThresholdPairCorrelation](../TransThresholdPairCorrelation/README.md) | Bi-scale uncertainty and the threshold face; the signed close-prime-pair surplus is the prime-side Fourier coefficient the zero side cannot see. |
| HTGeometry, RHTower | Hamburger's theorem, Bochner on `ℝ`, Kronecker density on prime tori, the Weil criterion, Beurling systems. |

---

## 2. Why

**The explicit formula is a Poisson pair.** For an even test `g`,

`Σ_ρ ĝ(γ_ρ) = ĝ(i/2) + ĝ(−i/2) − Σ_n Λ(n) n^{−1/2} (g(log n) + g(−log n)) + (archimedean term)`,

with `γ_ρ = (ρ − ½)/i`. The left side integrates `ĝ` against the zero measure
`μ_Z = Σ m_ρ δ_{γ_ρ}`, the right side integrates `g` against the prime measure
`μ_P = Σ Λ(n) n^{−1/2} (δ_{log n} + δ_{−log n})` corrected by the archimedean density and the pole.
`μ_P ≥ 0` by arithmetic. RH says `μ_Z` is a positive measure on `ℝ`; by Bochner–Schwartz this is
Weil's criterion. RH is the statement that one specific Poisson pair is positive on both sides.

**The corpus's two positivities are Fourier dual.** In the height variable,
`u ↦ Re(−ζ'/ζ)(σ + iu) = Σ Λ(n) n^{−σ} cos(u log n)` is positive definite because `μ_P ≥ 0`
(MPG). In the scale variable, `t ↦ Re W(f, f(· − t))` is positive definite iff `|f̂|² μ_Z` is a
positive measure (AOG). One side is known, the other is the theorem.

**Forcing is rigidity.** Neither forcing theorem is an inequality with a constant. Each is an exact
identity whose two sides have different regularity, a sum of nonnegative terms against a
computable constant, followed by quantization:

- boundary: `|D(u)| ≤ D(0) = 1` with `D` integer valued; a three-point Gram form makes the support
  a subgroup;
- theta: pairing the self-dual theta law against the Fejér tent `1 − |τ|` on `[−1, 1]` gives
  `Σ a_n (sin πλ_n / πλ_n)² = −(α + β) = 0`; with `a_n ≥ 0` every active frequency is an integer.

Weil's theorem for curves is the calibration: the normalized trace sequence of a curve is positive
definite on `ℤ`, with integer mass `2g`, and Weil proves it by counting.

**Rank matters.** Rank one in the height variable forces only the boundary (MPG: interior zeros are
invisible to boundary data). Rank one in the scale variable is blind (a single prime tower is
Toeplitz-blind to symmetric Wolff configurations). Rank two in the scale variable decides RH
(`riemannHypothesis_iff_splineTwoPrime_negIndex_eq_zero`). APD is a theory of finite-rank
sub-couplings exhausting an infinite-rank object, and must say on which side rank helps.

---

## 3. Objects and language

| Object | Meaning |
|---|---|
| Poisson pair | `(μ, ν)` with `∫ ĝ dμ = ∫ g dν` on a stated test class; *self-dual* when `ν = μ` (up to the polar terms) |
| Positive side, spectral side | the side with known positivity; the side whose positivity is the theorem |
| Gap | an interval `(−a, a) ∖ {0}` carrying no mass on one side |
| Spectral gap identity | pairing with a test supported in the gap: a sum of nonnegative terms equals a constant |
| Fejér tent | `1 − |τ|` on `[−1, 1]`, transform `(sin πu/πu)²`; the extremal test of every gap identity |
| Positive-definite function | `φ : G → ℝ` (or `ℂ`) with all Gram forms nonnegative, `G` abelian of finite rank (`ℤ^r`, `ℝ`, `S`-unit groups) |
| Fourier measure | the positive measure on the dual torus `T^r` whose coefficients are `φ` (Herglotz–Bochner) |
| Kronecker line | `t ↦ (t log p₁, …, t log p_r) mod 2π` in `T^r`; dense, since the `log p_i` are `ℚ`-independent |
| Rational fibre | the frequencies of a finite spectrum that are rational multiples of a target frequency |
| Purchase ratio, barrier | `a(γ)/a(0)` of a nonnegative certificate; its maximum over a spectrum |
| Quantum, budget | the integer an invariant must reach to be nonzero; the computable bound it is held under |
| Battery | golden datum `1 − 5X + 5X²`, curves over `𝔽_q`, shifted pairs, Wolff configurations, Beurling countermodels (double pole, periodic pole, over-regular), degree-`d` abundance |

**Words.** *Forcing*: an unconditional theorem whose conclusion is a vanishing on the spectral
side. *Receiver*: an RH-equivalent reformulation; it never produces its own input.
*Height side* / *scale side*: the two Fourier-dual variables of the explicit formula. *Rank* of a
coupling: rank of the group carrying the positive-definite function.

---

## 4. Mechanisms

1. **Spectral gap identity.** Pair a Poisson identity with a nonnegative test supported in the gap
   of the dual side. Everything in the gap vanishes; what is left is a sum of nonnegative terms
   equal to the polar constant. (`fejer_pairing_identity`,
   `tsum_sin_sq_div_sq_eq_neg_add_of_freqSeries_eq`.)
2. **Zero set of the tent transform.** `(sin πu/πu)²` vanishes on `[1, ∞)` exactly at the
   integers, so a vanishing gap identity puts a positive measure on the lattice
   (`measure_compl_nat_succ_eq_zero_of_sinc_sq`).
3. **Periodicity extraction.** Once the support is a lattice, self-duality makes the dual
   transform periodic and residue extraction equalizes all masses
   (`coeff_eq_of_hamburgerSeries_periodic_re_pos`).
4. **Gram quantization.** For integer-valued positive-definite `φ` with `φ(0) = 1`: the two-point
   form gives `φ ∈ {−1, 0, 1}`, the three-point form gives translation invariance by a point of
   modulus one, so the support is a subgroup and `φ` is a `±1` character (MPG,
   `intValued_mul`, `nonvanishingSubgroup`).
5. **Pole saturation.** A nonnegative observable plus a nonnegative defect under a nonpositive
   pole budget vanishes; an integer defect under a budget below its first quantum vanishes
   (`measure_defect_eq_zero_of_pole_saturated`, `quantized_defect_eq_zero_of_pole_dominated`).
6. **Bohr projection.** Averaging an almost-periodic polynomial along a progression keeps
   exactly the modes resonant with the step; nonnegativity survives the average. This projects a
   multi-frequency certificate onto a sub-spectrum without losing positivity.
7. **Restriction and push-forward.** Restricting a positive-definite function on `ℝ` to a
   finite-rank subgroup pushes its spectral measure to the dual torus along the Kronecker line.
8. **Fejér means.** A positive-definite function on `ℤ^r` is the coefficient sequence of the weak
   limit of its nonnegative Fejér means; this is how positivity passes from Gram forms to measures.

---

## 5. Pillar theorems

| Pillar | Statement | Lean |
|---|---|---|
| **P1 Theta rigidity of positive measures** | A Borel measure on `[1, ∞)` with finite `u^{−2}` moment whose theta transform obeys Riemann's degree-one law (or whose `Γ_ℝ`-completed Dirichlet integral has Hamburger's functional equation) is `c Σ_{k≥1} δ_k`, with `β = −α`, `c = −2 Re α ≥ 0`. | `measure_eq_of_measureTheta_relation`, `measure_eq_of_completed_functional_equation` |
| **P2 Nonnegative frequency rigidity** | Nonnegative generalized Dirichlet series with frequencies `≥ 1` and Riemann's theta law have integer active frequencies and equal mass at every integer; normalized, they are `ζ`. | `nonneg_freq_rigidity_of_theta_relation`, `freqDirichlet_eq_riemannZeta_of_completed_functional_equation` |
| **P3 Complex Fejér–tent law** | For arbitrary complex coefficients, a self-dual theta relation forces `α + β = 0` and `Σ a_n (sin πλ_n/πλ_n)² = 0`. | `tsum_sin_sq_div_sq_eq_neg_add_of_freqSeries_eq`, `tsum_sin_sq_div_sq_eq_zero_of_freqTheta_relation` |
| **P4 Beurling prime-measure selectivity** | A Beurling prime measure on `(1, ∞)` generates integers satisfying Riemann's theta law (or completed functional equation) iff it is `Σ (Λ(n)/log n) δ_n`; the polar constants are forced. | `eq_riemannPrimeMeasure_of_beurling_theta_relation`, `eq_riemannPrimeMeasure_of_beurling_functional_equation` |
| **P5 The degree-one FE-complete class is `{ζ}`** | A countable Beurling system whose zeta has Riemann's completed functional equation has the simple pole forced, integers = positive integers with multiplicity one, `beurlingZeta = ζ` on `Re s > 1`, and labels in norm-preserving bijection with the rational primes. | `beurlingSystem_rigidity_of_completed_functional_equation` |

The Hamburger input of P1, P4 and P5 is part of the statement: the remainder `E` is holomorphic on
the strip `(−½, 3/2)` with `O(1/(1 + t²))` decay. Cite it as "FE in Hamburger's form".

---

## 6. Questions the programme answers

Each question is stated so that a theorem settles it: an exact law, a classification with
sharpness models, or a no-go with its positive survivor.

1. **Rank-`r` boundary law.** Classify integer-valued even positive-definite functions with unit
   mass on abelian groups of every rank, with and without pole isolation, and realize each class by
   a nonnegative arithmetic datum. Expected: the classification is rank-independent, and for `ζ`
   rank two forces nothing beyond rank one.
2. **Interior continuation.** Which positive-definiteness constraints on
   `Re(−ζ'/ζ)(σ + iu)`, `σ > 1`, survive into `½ < σ < 1` when coupled across several primes or
   heights with growth input? The test case is the exact barrier of a multi-frequency certificate
   and its restriction to the Kronecker line of two primes.
3. **Prime-side Bochner.** Characterize the positive measures on `T²` whose Fourier coefficients
   are the two-prime orbit correlations `c(k, l) = Re W(B, B(· − k log p − l log q))`, and identify
   them with the Kronecker push-forward of the zero measure.
4. **Quantized budget.** Which integer plays the pole's role at the critical line, and is there
   an inequality `(integer invariant) × (coefficient) ≤ (budget)` with budget below the first
   quantum on a finite sub-coupling?
5. **Poisson rigidity.** Which exact sums of nonnegative terms equal a computable constant on a
   Poisson pair, and what do they force? For self-dual positive pairs with a gap the expected answer
   is lattice support; for the Weil pair, where positivity and gap sit on the same side, the answer
   must say what survives.
6. **Non-commutative carrier.** Does the Weil form extend to a positive functional on the affine
   semigroup algebra (successor and dilation) that is not a quadratic form in the test? What is its
   restriction to the finite affine quotient, and does it fail on the golden datum?
7. **Topology.** Which completion of the Meyer source keeps every critical jet continuous and makes
   the trace-bounded ideal closed, so that exhaustion becomes a limit statement?

Calibration questions: the reduction over `𝔽_q` of every APD statement to Weil's theorem, with the
integer budget identified as `2g`; the reproduction of the known analytic output (the boundary
line, the classical zero-free regions) in APD coordinates.

---

## 7. Traps

| Trap | Truth |
|---|---|
| FE + positivity is an axiom system with many models | At degree one, on Beurling systems, its only model is `ζ` (P5); any proof must use features of `ζ` itself |
| Hamburger's theorem uses only the FE | The remainder must be holomorphic on the strip with quadratic decay |
| The FE is a self-duality of the Weil pair | It is a self-duality of the integer measure (theta). The explicit formula pairs primes with zeros; on the Weil pair positivity and the prime-free gap sit on the same side |
| Positivity of the prime side says something in the strip | It is the height-side positive definiteness; on its own it forces only on the boundary line |
| Integer values force vanishing | Only with unit mass and positive definiteness, or with self-duality |
| Rank two decides RH, so rank-two positivity is progress | The two-prime criterion is a receiver; the question is what rank two forces that rank one does not |
| A finite box of `ℤ²` is a rank-two theorem | It is a bounded-aperture condition with width resolution `½` |
| Positive definite means nonnegative | A positive-definite function is the transform of a positive measure; it can take negative values |
| Bost–Connes symmetry at `Re s = 1` is information about the strip | Its phase transition sits on the line where multiplicative forcing already works |

---

## 8. Tools

Built:

- Fejér-tent pairing on the half-plane Laplace identity, real and complex coefficients;
- measure-theoretic Hamburger theorem, automatic `σ`-finiteness, theta and Mellin transforms of
  measures on `[1, ∞)`;
- multiplicative convolution exponential of Beurling prime measures and its theta law.

To build:

- positive-definite functions on `ℤ^r`; Herglotz–Bochner on `ℤ^r` with measures on `T^r`;
- Bohr projection of almost-periodic polynomials onto rational fibres; exact multi-frequency
  barriers; transfer between the Kronecker line and the torus;
- the integer positive-definite classification on arbitrary abelian groups and its realization;
- Poisson rigidity of positive self-dual measures with a gap;
- restriction of positive-definite functions to `S`-unit groups and push-forward of spectral measures;
- the APD reading of Weil's theorem for curves.

---

## 9. Open research topics

1. Positive-definite functions on `ℤ^r` with arithmetic Fourier supports: barriers, extremal
   measures, quantized classification.
2. The Fourier duality of MPG (height) and AOG (scale) as one theorem about the Weil pair.
3. Spectral gap identities for the Weil distribution against lattices and `S`-unit groups.
4. Integer budgets: torsion orders `#(ℤ/Q_N ℤ)`, finite affine quotients, Hecke-cycle lattices, and
   which admit a theorem-of-the-square substitute (the naive one fails,
   `heckeCorrespondence_no_square_relation`).
5. Positive crystalline measures with theta self-duality beyond degree one; degree-`d` abundance as
   the control group.
6. Non-commutative positivity on the affine semigroup: finite-horizon functionals,
   infinite-dimensional carriers, Bost–Connes symmetries.
7. Signed additive prime correlations at the square-root threshold as the analytic face of the
   duality.

---

## 10. Success criteria and contribution standard

The field exists when it has:

- a rank-two boundary law with sharpness models, and an interior law with explicit growth input and
  barrier;
- a quantized inequality in the strip, or a proof that no finite sub-coupling of a stated class has
  one;
- a topology on the Meyer source in which the maximal blind ideal is closed, or a proof that none
  exists;
- the reduction over `𝔽_q` to Weil's theorem with the integer budget `2g`;
- every rigidity theorem formalized with no RH-equivalent hypothesis.

A contribution must:

1. be an unconditional Lean theorem;
2. name its positive side, its spectral side, its gap and its integer;
3. state an exact identity, a classification, a sharp barrier or a rigidity law, not a new
   equivalent of RH;
4. say what it gives on the battery: curves (must reproduce Weil), the golden datum (must fail),
   Beurling countermodels;
5. record the positive survivor of every no-go.

Principles: positivity on one side is known, positivity on the other is the theorem; rigidity before
estimates; every forcing step names its integer and its budget; rank matters; both ring operations
or neither; calibrate over `𝔽_q`.

---

## 11. Modules

| Module | Content |
|---|---|
| `PositiveMeasureHamburgerRigidity` | Theta and Mellin transforms of measures; Fejér pairing; measure-theoretic Hamburger rigidity; Beurling prime-measure selectivity |
| `BeurlingRiemannFunctionalEquationRigidity` | Complex Fejér–tent law; nonnegative generalized Dirichlet series uniqueness; rigidity of countable Beurling systems |
