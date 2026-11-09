# Arithmetic Weight Theory of Spec ℤ (AWT)

Namespace `GaloisForLFunctions.ArithmeticWeightTheory`; umbrella `ArithmeticWeightTheory.lean`.

Notation. `z = ρ − ½` for a zero `ρ`; `b = sup Re z` the **weight** (zero width) of a configuration;
`B = U₁^{⋆4}` the cubic spline; `t(d) = 2 Re S(log d)` the spline trace at degree `d`
(`lagStructure zetaZeroConfig (boxSpline 1 3)`); `M = Σ_z e_z ℤ(−z)` the virtual motive of the
zeros, whose Frobenius at `n` acts on the `z`-line by `n^z`; `G = (ℝ/ℤ)^ℕ` the gauge torus with
twists `χ_x` and Haar measure; `T_x(u) = e^{−u/2} Σ_p log p · χ_x(p) · B(log p − u)` the twisted
spline trace of the fibre `x`.

## 1. Motivation

Deligne's proof of purity over `𝔽_q` has six moves: positivity of the even tensor powers
`F^{⊗2k}`, the Rankin square, Landau–Pringsheim at the real pole, base change, the absence of a
real eigenvalue on the blind side, and the a priori location of the poles of `L(F^{⊗2k}, T)`
uniformly in `k`. Over `ℤ` the first five are theorems in the corpus (`SurfaceOfSpecZ`): the traces
`t(p)` are point counts of `M`, the moments `Σ_{p≤N} log p · t(p)^{2k}` are nonnegative, the
Rankin square has abscissa `1 + 2b`, a one-sided bound at the primes is RH because `ζ` has no
real zero in the strip, and RH ⇔ the tensor powers have a common half-plane of convergence. The
sixth move is missing. Over a curve it is the computation `H²_c(U, F^{⊗2k}) = (F^{⊗2k})_{π₁^geo}(−1)`:
the poles come from the coinvariants of the geometric monodromy, on which Frobenius acts with a
weight fixed by a Frobenius-equivariant pairing.

AWT starts from the exact reason the sixth move has no analogue for `M` alone.

**Geometric constancy.** The Frobenius of `M` at `n` depends on `n` only through `log n`. Every
constituent of `M^{⊗2k}` is a Tate twist `ℤ(−w)`, `w = z₁ + ⋯ + z_{2k}`, whose L-function
`ζ(s − w)` has a pole. There is no geometric monodromy, so the coinvariants are all of
`M^{⊗2k}` and the tensor trick reads the weight and nothing else. The same is true of one curve
over `𝔽_q`: its `H¹` is geometrically constant over `Spec 𝔽_q`. Deligne's uniformity in `k`
comes from families — Lefschetz pencils on `X^k`, whose vanishing cycles have big geometric
monodromy — and from the specialization of weights from the generic to the special fibre.

So the field is a theory of **families of Euler products**: a parameter space carrying a
monodromy (an averaging that kills non-invariant tensors), `ζ` as a special fibre, a pure
generic fibre, and a topology in which weights specialize. The gauge torus is the first
candidate: twisting by `χ_x` is a geometric direction, Haar orthogonality of twists is big
monodromy, and Haar-almost every fibre is zero-free on `Re s > ½`.

## 2. Objects

| Object | Lean | Meaning |
|---|---|---|
| Zero configuration, weight | `zetaZeroConfig`, `zetaZeroWidth`, `TopDepth` (SRT) | zeros of `ζ`; `b`; all exponents `≤ b` |
| Spline trace | `lagStructure Z (boxSpline 1 3)` (AOG) | `S_Z(u) = Σ_z e_z e^{zu}`; `t(d) = 2 Re S(log d)` |
| Tensor moments | `primeTraceMoment`, `tensorLogDerivTerm` (SoSZ) | `Σ_{p≤N} log p · t(p)^{2k}`; `−L′/L(M^{⊗2k}, σ)` |
| Trace zeta | `traceDirichlet`, `traceZetaOf` (SoSZ) | `Σ_n t(k log n) n^{−s} = Σ_z e_z ζ(s − kz)` |
| Gauge torus, twist, Haar | `GaugeTorus`, `twist`, `gaugeHaar` (ACG) | the family; `χ_x(n)`; the monodromy measure |
| Gauge moments | `twistSum`, `powSupport`, `powCoeff` (ACG) | `Σ a_n χ_x(n)`; its `k`-th power as a twisted polynomial |
| Fibres of the hull | `gaugeFibre` (PTT) | `ζ_x(s) = Σ χ_x(n) n^{−s}` |
| Twisted spline trace | to be defined here | `T_x(u)`; `T_0(u)` carries the pole |
| Trace constant | to be defined here | `K_a(x) = sup_p |T_x(log p)| p^{−a}` |
| Moment weight | to be defined here | least `A` with `Σ_{p≤N} log p |T_x(log p)|^{2k} ≪_k N^{1+A}` for all `k` |
| Calibrations | `abs_card_points_sub_le_hyperelliptic` (CTH) | Hasse–Weil for every hyperelliptic curve |
| Fakes | `one_off_violates_stepanov_bound` (ALST), `coshModel` (IRWT), `riemannHeat_zeros_im_sq_le` (RHTower) | integer-norm one-off; FE without Euler product; heat family |

## 3. Language

- **Weight** of a configuration: `b = sup Re z`. **Pure**: `b = 0`. **Top**: the exponents of
  real part `b`; **attained** if nonempty.
- **Trace** at degree `d`: `t(d)`; **Stepanov side**: `t ≥ −K`; **other side**: `t ≤ K`.
- **Tensor power**: `t^{2k}`; its series has nonnegative coefficients without hypothesis.
- **Family**: a probability space `(Y, ν)` with traces `T_y(d)`; **fibre** `y`; **special
  fibre**: the point that is `ζ`; **generic**: `ν`-almost every.
- **Monodromy, coinvariants**: the `ν`-average of tensor monomials; on `G` it keeps exactly the
  monomials whose two products coincide (multiplicative pairings).
- **Big monodromy**: the coinvariants of the `2k`-th tensor power have weight `0` and size
  `≤ k!` times the `k`-th power of the second moment.
- **Jump**: a coinvariant present at the special fibre and absent generically (the pole).
- **Specialization**: a topology on `Y` and the behaviour of weights at the special fibre.
  **Deligne direction**: special weight `≤` generic weight. **Coherent direction**: special `≥`
  generic.
- **Constant versus exponent**: a trace bound `|T_y(log p)| ≤ K p^a` has a constant `K` and an
  exponent `a`; over `𝔽_q` only exponents exist (finitely many eigenvalues, any constant
  self-improves).
- **Sample**: a set of degrees; **power-saving gap set**: meets every `[x, x + x^θ]`, `θ < 1`.

## 4. Mechanisms

**Built on (corpus, unconditional).**
1. Tensor trick over `ℤ`: RH ⇔ `∃A ∀k` the moments are `≪_k N^{1+A}` ⇔ the tensor series have a
   common abscissa (`riemannHypothesis_iff_moments_primeTraces`,
   `riemannHypothesis_iff_tensorPowers_commonAbscissa`); the same at every power-saving gap set
   for configurations without real zeros (`onLine_iff_tensorPowers_commonAbscissa_of_powGaps`).
2. Rankin square: abscissa `1 + 2b` at an attained top (`not_summable_rankinSquare_of_max`).
3. Width law: `b ≤ a` ⇔ `t(p) ≥ −Kp^a` at every prime, `0 ≤ a < ½`
   (`zetaZeroWidth_le_iff_bddBelow_primeDegrees`); the Stepanov side is blind exactly to real
   zeros (`stepanov_side_blind_to_real_zeros`), the other side sees every zero
   (`onLine_of_two_re_lagStructure_le`).
4. Base change: RH ⇔ the traces at the degrees `n^k` are bounded below
   (`riemannHypothesis_iff_bddBelow_powerDegrees`); the zero-free strip improves by the factor
   `1 + 1/k` per Landau step (`riemannHypothesis_iff_bddBelow_kthPrimePowers`).
5. Gauge monodromy: the gauge `2k`-th moment of `Σ a_n χ_x(n)` is the multiplicative diagonal
   `Σ_N |a^{*k}(N)|²` (`integral_normSq_twistSum_pow`); monomials average to their value on
   coinciding products and to zero otherwise (`integral_monomial_twist`).
6. Generic fibre: Haar-a.e. `ζ_x` extends zero-free to `Re s > ½` (`ae_fibre_extends_zeroFree`)
   with natural boundary `½` (`ae_natural_boundary`); the Möbius exponent is `½` a.e.
   (`ae_gaugeExponent_moebius_eq_half`), `1` on a null residual set
   (`moebius_exponent_one_residual_and_null`), and RH ⇔ the trivial point is typical
   (`riemannHypothesis_iff_trivialPoint_eq_typical`).
7. Strip specialization: RH ⇔ `ζ` is strongly recurrent, i.e. a locally uniform limit of its own
   vertical shifts on the strip (`riemannHypothesis_iff_zetaStronglyRecurrent`); Hurwitz on
   locally uniform limits (HTGeometry).

**To discover.** The uniform pole bound for a family in which `ζ` specializes, and the topology
in which weights specialize in Deligne's direction.

## 5. Questions

1. **Family.** Which family carries `ζ` as a fibre with big monodromy: the gauge torus, Dirichlet
   twists, vertical shifts, or a deformation keeping an Euler product? What does each give at
   the special fibre?
2. **`H²_c`.** What is the analogue of the coinvariants, the a priori control of the top pole of
   `L(F^{⊗2k})`, for `M` and for each family?
3. **Semicontinuity.** In which topology on the family are weights semicontinuous, and in which
   direction? Haar-generic exponent `½` against Baire-generic `1` shows the product topology fails.
4. **Constants.** Deligne's argument needs only exponents; over `ℤ` the generic trace bounds carry
   random constants. Which family keeps the constants bounded near the special fibre?
5. **Jump.** The pole is a coinvariant present only at the special fibre. Is there a family with a
   continuous pole subtraction whose pole-free traces are pure generically?
6. **`X^k`.** What object over `ℤ` plays the product `X^k` of Deligne's induction, whose middle
   cohomology contains `H¹^{⊗k}` with a loss independent of `k`?
7. **Milestone M4.** Is `A_k = o(k)` for `ζ` weaker than RH?

## 6. Tools

**Built on.** Tensor moments and tensor series at primes and gap sets; width law; Rankin
square; trace zeta at the power degrees; gauge moments as multiplicative diagonals; hull,
natural boundary and zero-free extension of fibres; gauge exponent and its zero-one law; strong
recurrence; Hurwitz.

**To build.**
- Big-monodromy calculus for prime-supported sources: Gaussian moment bounds for the gauge
  family.
- Generic uniform weights: almost-sure tensor moment bounds for twisted spline traces.
- Trace constants on the family; their semicontinuity and the jump at the special fibre.
- Specialization classes of Euler-product deformations (which deformations move zeros).
- Tensor-power trace series of `M` as sums over tuples of exponents.
- Calibration on curves: the same dictionary for one curve and for families of curves.

## 7. Pillar theorems

| Theorem | Lean | Status |
|---|---|---|
| Tensor trick over `ℤ` | `riemannHypothesis_iff_moments_primeTraces` (SoSZ) | RH-equivalence, built on |
| Common abscissa of tensor powers | `riemannHypothesis_iff_tensorPowers_commonAbscissa` (SoSZ) | RH-equivalence, built on |
| Rankin square at twice the top weight | `not_summable_rankinSquare_of_max` (SoSZ) | unconditional, built on |
| Gauge moments are multiplicative diagonals | `integral_normSq_twistSum_pow` (ACG) | unconditional, built on |
| Generic fibre zero-free on `Re s > ½` | `ae_fibre_extends_zeroFree` (PTT) | unconditional, built on |
| Strip specialization is RH | `riemannHypothesis_iff_zetaStronglyRecurrent` (RHTower) | RH-equivalence, built on |
| Big monodromy of the gauge family | — | target |
| Generic uniform weights (M2) | — | target |
| The jump at the special fibre | — | target |

## 8. Open research topics

- A family through `ζ` with exact coinvariants and a special fibre of positive mass.
- A continuous pole subtraction on the gauge family.
- The analogue of `X^k`: diagonal versus external tensor powers of `M`.
- Weight specialization along vertical shifts below and past the Kronecker scale.
- The status of M4 and of the classical saving `√p e^{−√(log p)/10}` in the tensor language.

## 9. Traps

| Trap | Truth |
|---|---|
| The tensor trick over `ℤ` is weaker than over `𝔽_q` | On one curve it is equally tautological; the uniformity is in the family |
| Positivity of `t^{2k}` is the content | Free on every configuration, also on fakes |
| A Stepanov bound suffices | Blind to real zeros; over `ℤ` the absence of real zeros of `ζ` is the twist |
| One Frobenius, finitely many Frobenii, density-zero samples decide | Aliasing; unattained tops pass |
| Haar-generic purity transfers to `ζ` | `ζ` is a null, meagre point of the family |
| The product topology specializes | Typical exponent `½`, residual exponent `1` |

## 10. Criteria

**Calibrations.** Reproduce Deligne on curves over `𝔽_q`. Respect the sampling boundary: one
Frobenius aliases; finitely many Frobenii, the very smooth degrees and the primes off density-zero
sets admit unattained tops; power-saving gap sets and power-thin exceptions decide. Start from the
classical saving `√p e^{−√(log p)/10}` and the VK width.

**Fakes.** A mechanism claimed to bound the weight of `ζ` must use the Euler product and the
functional equation: it must fail on the integer-norm one-off (Euler product, violates the
Stepanov bound for every constant), on the `cosh` models (FE, no Euler product) and on the heat
family `H_t`, `t < 0`.

**A contribution** is an unconditional Lean theorem about weights, tensor powers, families,
coinvariants or specialization that either proves a piece of the dictionary, answers one of the
questions of §5 with a sharp boundary, or develops a tool listed in §6; it states its behaviour on
the calibrations and the fakes. RH-equivalences count only when they expose a new mechanism.

**Success.** The questions of §5 answered by theorems; the tools of §6 built; the main conjecture
reduced to one explicitly named family statement, or the field's route closed with its strongest
positive survivor formalized.

## 11. Context

| Neighbour | Interface |
|---|---|
| SurfaceOfSpecZ | tensor trick, Rankin square, width law, base change, sampling theorems |
| ArithmeticCorrelationGeometry | gauge torus, twists, orthogonality, gauge moments |
| ArithmeticGaugeTheory | gauge exponent, zero-one law, typical and special points |
| PrimeTorusTheory | hull, fibres, natural boundary, Kronecker orbit |
| ArithmeticKunnethTheory | the archimedean line reproduces gauge diagonals below the square-root threshold |
| RHTower | strong recurrence, de Bruijn–Newman flow |
| CountingHolography, ArithmeticScatteringHolography | curve calibration (Hasse–Weil for hyperelliptic curves) |
| ArithmeticBaseChange (§2.10) | vertical transport of zeros; AWT is the horizontal (weight) side |

## 12. Big picture

Over `𝔽_q` purity is a family statement specialized to a point. Over `ℤ` every step of Deligne's
argument at the point is formalized, and the step that is missing is exactly the one a point
cannot supply. AWT moves the problem to families: it proves the Deligne mechanism where it can
work (the generic fibre of a family with big monodromy) and measures, family by family, what
prevents the special fibre from inheriting the weight.
