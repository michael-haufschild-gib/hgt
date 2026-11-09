# Arithmetic Weight Theory of Spec ℤ (AWT)

Namespace `GaloisForLFunctions.ArithmeticWeightTheory`; umbrella `ArithmeticWeightTheory.lean`; 7 modules.
All results unconditional; RH appears only inside equivalences.

Notation. `z = ρ − ½` for a zero `ρ`; `b = sup Re z` the **weight** (zero width) of a configuration;
`B = U₁^{⋆4}` the cubic spline; `t(d) = 2 Re S(log d)` the spline trace of the zeros at the degree `d`;
`M = Σ_z e_z ℤ(−z)` the virtual motive of the zeros, whose Frobenius at `n` acts by `n^z`;
`G = (ℝ/ℤ)^ℕ` the gauge torus with twists `χ_x` and Haar measure; for a window `g` and radius `R`,
`T_x(u) = e^{−u/2} Σ_{p ≤ e^{u+R}} log p · g(log p − u) · χ_x(p)` the window trace of the fibre `x`.

## 1. Motivation

Deligne's purity proof over `𝔽_q` has six moves: positivity of the even tensor powers `F^{⊗2k}`, the
Rankin square, Landau–Pringsheim at the real pole, base change, the absence of a real eigenvalue on
the blind side, and the a priori location of the poles of `L(F^{⊗2k}, T)` uniformly in `k`. Over `ℤ`
the first five are theorems (`SurfaceOfSpecZ`); RH ⇔ the tensor powers of `M` have a common
half-plane of convergence. The sixth move is missing. Over a curve it is
`H²_c(U, F^{⊗2k}) = (F^{⊗2k})_{π₁^geo}(−1)`: poles come only from coinvariants of the geometric
monodromy, whose Frobenius weight a pairing fixes; the non-invariant constituents sit in `H¹_c` and
have no poles.

AWT asks what plays this role over `ℤ` and answers it in three steps.

1. **`M` alone has no `H²_c`.** Its Frobenius acts through `log n`; every constituent of `M^{⊗2k}` is
   a Tate twist `ℤ(−z₁−⋯−z_{2k})` whose L-function `ζ(s − Σz_i)` has a pole. The top pole of the
   `2k`-th tensor series sits exactly at `1 + 2kb` for every `k` (§5). The tensor trick for `M`
   reads the weight and nothing else; one curve over `Spec 𝔽_q` is the same.
2. **Families supply it generically.** On the gauge torus, twisting is a geometric direction and Haar
   orthogonality is big monodromy: the coinvariants of the `2k`-th tensor power are multiplicative
   pairings, at most `k!`, of weight zero. Deligne's argument then runs: Haar-almost every fibre has
   uniform tensor weights (milestone M2).
3. **The special fibre does not inherit it.** `ζ` is the trivial fibre, the bad character of this
   Mellin family. Its pole is a coinvariant jump, and the jump locus is exactly the pretentious
   neighbourhood of the archimedean line `n^{it}`; trace constants specialize but blow up there;
   exponents do not specialize; Baire-generic fibres carry the pole; isozeric deformations are
   null; and any family with exact coinvariants prices every fibre at the trivial bound.

The field therefore locates the missing input precisely: a specialization that is neither measure
nor category, nor positivity against orthogonality — a map from the generic to the special fibre
of the kind cohomology supplies over `𝔽_q` (middle extension, invariants of local monodromy).

## 2. Objects

| Object | Lean | Meaning |
|---|---|---|
| Configuration, weight, top | `ZeroConfig`, `zetaZeroWidth`, `TopDepth` (SRT, SoSZ) | zeros; `b`; exponents `≤ b` |
| Spline trace | `lagStructure Z (boxSpline 1 3)` (AOG) | `S_Z(u) = Σ_z e_z e^{zu}` |
| Tensor series | `tensorTerm`; `tensorLogDerivTerm`, `primeTraceMoment` (SoSZ) | `Λ(n) t(log n)^{2k} n^{−σ}`; moments at primes |
| Gauge family | `GaugeTorus`, `twist`, `gaugeHaar`, `twistSum` (ACG) | fibres `x`, `χ_x(n)`, monodromy measure |
| Window trace, moment | `windowPrimes`, `windowWeight`, `fibreTrace`, `fibreMoment` | `T_x(u)`; `Σ_{p≤N} log p |T_x(log p)|^{2k}` |
| Trace constant | `traceConstantSet g R K a` | fibres with `|T_x(log p)| ≤ K p^a` at every prime |
| Fibre L-function | `gaugeFibre` (PTT) | `ζ_x(s) = Σ χ_x(n) n^{−s}`; `gaugeFibre 0 = ζ` (`gaugeFibre_trivial`) |
| Euler deformation | `deformationPrimeSum`, `deformationExponent`, `isozericClass` | `ζ_x = ζ e^F`; summable prime perturbations |
| Orthonormal family | `TwistOrthonormalOn ν s` | a probability family with exact coinvariants on `s` |
| Reset fibre | `resetOutside I x` | agrees with `x` on `I`, trivial elsewhere |
| Pretentious distance | `pretTerm`, `pretSum`, `polePoint` | `1 − Re(χ_x(p)p^{−iτ})`; `D_δ = Σ_p p^{−1−δ}·pretTerm`; `1 + δ + iτ` |

## 3. Language

- **Weight**: `b = sup Re z`; **pure**: `b = 0`; **top attained**: some zero has real part `½ + b`.
- **Tensor power**: `t^{2k}`; its series has nonnegative coefficients on every configuration.
- **Family**: probability space of fibres with traces at every degree; **special fibre**: `ζ`
  (the trivial point); **generic**: Haar-almost every; **Baire-generic**: residual.
- **Coinvariants**: monodromy averages of tensor monomials; on `G` the multiplicative pairings.
- **Jump**: a coinvariant present only at the special fibre (the pole of `ζ`).
- **Constant / exponent**: in `|T_x(log p)| ≤ K p^a`, `K` and `a`. Over `𝔽_q` only exponents exist.
- **Specialize (Deligne direction)**: special `≤` generic. **Coherent direction**: special `≥` generic.
- **Isozeric**: same zeros with multiplicities on a half-plane.
- **Pricing**: the bound a family transfers to one fibre by positivity.
- **Jump locus**: fibres with a pole on `Re s = 1`; **pretentious** to `n^{iτ}`: `Σ_p (1 − Re χ_x(p)p^{−iτ})/p < ∞`.

## 4. Mechanisms

**Built on (corpus).**
1. Tensor trick, common abscissa, Rankin square at `1 + 2b`, width law, base change at `n^k`, the
   Stepanov side's blindness to real zeros, sampling at power-saving gap sets (SoSZ).
2. Gauge moments are multiplicative diagonals; monomials average to their pairing part (ACG).
3. Generic fibres extend zero-free to `Re s > ½` with natural boundary; the fibre logarithm is
   `Σ_p x_p p^{−s}` plus a remainder analytic on `Re s > ½`; Hurwitz on domains (PTT).
4. Gauge exponent: typical `½`, residual `1`, trivial point never better than typical (AGT).
5. Steinhaus bound for prime-supported polynomials (TAPO).

**Proved here.**
6. *Big monodromy.* `∫|Σ_p a_p χ_x(p)|^{2k} ≤ k!(Σ|a_p|²)^k`; window coinvariants
   `≤ k!(log 4 · e^R (u + R))^k` uniformly in fibre and degree (Chebyshev).
7. *Generic uniform weights.* Markov at dyadic degrees + Borel–Cantelli: for a.e. fibre, every `k`,
   every `ε > 0`, `Σ_{p≤N} log p |T_x(log p)|^{2k} ≪ N^{1+ε}`; traces `p^{o(1)}`.
8. *Jump.* `θ(e^{u+1}) − θ(e^{u−1}) ≥ e^u` for `u ≥ 200` gives `|T_0(log p)| ≥ c√p`; trace-constant
   sets are closed (lower semicontinuity of constants), conull in union, disjoint from a
   neighbourhood of `0`.
9. *Category.* Resetting all but finitely many coordinates to `0` reproduces the pole at large
   primes up to `2Σ_{q∈I} log q`; trace-constant sets are nowhere dense.
10. *Isozeric deformations.* `ζ_x = ζ e^F` on `Re s > 1` for every fibre; `F` analytic on
    `Re s > σ₀` when `Σ_p |χ_x(p) − 1| p^{−σ₀} < ∞`; the residue of `ζ` at `1` excludes such fibres
    from the a.e. zero-free set.
11. *Exact tensor weight.* Weighted AM–GM
    `c² x^{−(σ/k + (1+δ)(1−1/k))} ≤ (1/k) c^{2k} x^{−σ} + (1−1/k) x^{−(1+δ)}` dominates the Rankin
    square by the `2k`-th tensor series.
12. *Pricing.* Exact orthonormality on `s` gives `ν{x₀} · #s ≤ 1`; with Cauchy–Schwarz on the
    `k`-fold products, `ν{x₀}(Σ a_n)^{2k} ≤ ∫|S|^{2k} dν`.
13. *Jump locus.* `|ζ_x(1 + δ + iτ)| = |ζ(1 + δ)| e^{−D_δ + O(1)}` with the fibre-logarithm remainder
    bounded by `2Σ p^{−2}` and `δζ(1 + δ) → 1`; `D_δ` stays below `D²` or tends to infinity.

## 5. Pillar theorems

| Theorem | Lean | Status |
|---|---|---|
| Big monodromy of the gauge family | `integral_norm_twistSum_pow_le`, `integral_norm_fibreTrace_pow_le` | unconditional |
| Generic fibre has uniform weights (M2) | `ae_fibreMoment_le`, `ae_norm_fibreTrace_le` | unconditional |
| Pole at the trivial fibre, exponent `½` | `mul_sqrt_le_trivial_fibreTrace`, `exists_prime_mul_rpow_lt_trivial_fibreTrace` | unconditional |
| Constants specialize, blow up at `ζ` | `isClosed_traceConstantSet`, `tendsto_measure_traceConstantSet`, `trivial_fibre_is_the_jump` | unconditional |
| Baire-generic pole, Haar-generic purity | `isNowhereDense_traceConstantSet`, `residual_and_null_of_traceExponent` | unconditional |
| Every fibre is `ζ e^F`; isozeric deformations | `gaugeFibre_eq_zeta_mul_exp`, `exists_isozeric`, `analyticOrderAt_isozeric` | unconditional |
| Isozeric class is Haar-null | `gaugeHaar_isozericClass_eq_zero` | unconditional |
| Tensor powers have exactly their weight | `summable_tensorTerm`, `not_summable_tensorTerm_of_max`, `summable_tensorTerm_iff_of_max` | unconditional |
| Moment exponent `A_k ≥ 2k·width − 1`; M4 ⇔ RH | `zetaZeroWidth_le_of_primeTraceMoment_le`, `riemannHypothesis_iff_tensorExponent_sublinear` | unconditional; RH-equivalence |
| Uncertainty and pricing | `measureReal_singleton_mul_card_le`, `measureReal_singleton_mul_pow_le` | unconditional |
| Pole iff pretentious; poles have order `≤ 1` | `pole_iff_pretentious`, `tendsto_mul_norm_gaugeFibre_of_not_pretentious`, `eventually_mul_norm_gaugeFibre_le` | unconditional |
| Jump locus contains the archimedean line, is Haar-null | `pretentious_archimedeanLine`, `gaugeHaar_jumpLocus_eq_zero` | unconditional |
| Tensor trick, common abscissa (M1) | `riemannHypothesis_iff_moments_primeTraces`, `riemannHypothesis_iff_tensorPowers_commonAbscissa` (SoSZ) | RH-equivalence, built on |
| Strip specialization is RH | `riemannHypothesis_iff_limits_zeroFree` (PTT), `riemannHypothesis_iff_zetaStronglyRecurrent` (RHTower) | RH-equivalence, built on |

## 6. Answers to the questions of the field

**Q1. Which family carries `ζ` as a fibre with big monodromy?** None in Deligne's sense.
- *Gauge torus.* Exact big monodromy (pairings, `≤ k!`); generic fibre has uniform weights; `ζ` is
  the trivial fibre: a Haar-null, meagre point carrying a coinvariant jump (§7).
- *Any probability family with exact coinvariants* (Haar, finite Dirichlet families exact up to the
  needed length, any `ν`): every fibre has mass `≤ 1/length`, and positivity transfers at best the
  trivial bound `(Σ a_n)^{2k}` (`measureReal_singleton_mul_pow_le`). Exactness at tensor power `k`
  costs volume `≥ length^k`; over `𝔽_q` a finite group is exact at every power with fixed volume.
- *Vertical shifts.* Every fibre is `ζ`; moments are the gauge diagonal below the square-root
  threshold and exceed it by a nonnegative off-diagonal past it (`integral_pairTransform_mul_normSq_pow_eq_diag`,
  `integral_normSq_pow_eq_diag_add_offDiag_nonneg`, AKT): weights constant, information only in the
  mean.
- *Dirichlet twists.* Each point reads its own GRH; the special locus is typical on average
  (`dirichletGRH_iff_dirichletGauge_typical`, `card_atypical_dirichletGauge_le_rpow`, AGT); pricing
  applies.
- *Euler deformations keeping the pole.* Isozeric: same zeros and multiplicities on `Re s > σ₀`;
  the class is Haar-null for `σ₀ < 1`. Deformations that move zeros leave every analytic class of `ζ`.

**Q2. What is the analogue of `H²_c`?** For `M`: all of `M^{⊗2k}`; the top pole is at exactly
`1 + 2kb` for every `k` at an attained top (`summable_tensorTerm_iff_of_max`), so no a priori control
exists and M4 is RH. For the gauge family: the multiplicative pairings, weight `0`, size `≤ k!`
(`integral_norm_twistSum_pow_le`). At the special fibre the jump is the pole, computed by the FE
(the explicit formula subtracts it exactly; `ThePrimeNumberTheoremInEveryWindow`, SoSZ); the FE also
supplies Deligne's weight-zero pairing `z ↔ −z`, but not big monodromy. The jump locus of the family
— fibres with a pole on `Re s = 1` — is the pretentious neighbourhood of the archimedean line
(`pole_iff_pretentious`): the analogue of generic vanishing, with the line `n^{it}` as subtorus and
finite pretentious distance as torsion translation; it is Haar-null.

**Q3. In which topology are weights semicontinuous?**
- *Product topology on `G`.* Constants specialize in Deligne's direction (closed sets) but tend to
  infinity at `ζ`; exponents do not: for `0 < a < ½` the fibres without a constant at exponent `a`
  are residual and Haar-null. The Baire-generic fibre looks like the special one (the pole), the
  Haar-generic fibre is pure.
- *Strip topology (locally uniform convergence on `Re s > ½`).* Weights are lower semicontinuous
  (Hurwitz); `ζ` is a limit of zero-free fibres or translates iff RH (PTT, RHTower).
- *Direction.* Over `ℤ` every natural family runs coherently, special `≥` generic: the trivial point
  is never better than typical (AGT), the heat flow lowers weights (de Bruijn, RHTower), isozeric and
  vertical families are constant. Over `𝔽_q[T]` the trivial point is better than typical (AGT
  calibration): Deligne's direction is a property of the function field.

**Milestones.** M1 built on. M2 proved (`ae_fibreMoment_le`). M3: the principle holds in the strip
topology; its application to `ζ` is RH. M4 is RH (`riemannHypothesis_iff_tensorExponent_sublinear`):
`A_k ≥ 2k·width − 1`, so `A_k = o(k)` forces width `0`. M5 RH.

## 7. Tools

**Developed.**
- Big-monodromy calculus for prime-supported twisted polynomials and window traces.
- Almost-sure tensor moment bounds (dyadic Borel–Cantelli) and trace bounds at the generic fibre.
- Trace-constant sets: closedness, exhaustion in measure, nowhere density, residual/null dichotomy.
- Chebyshev window bound `θ(e^{u+1}) − θ(e^{u−1}) ≥ e^u` and the pole at the trivial fibre.
- Euler-deformation exponent `F`, isozeric continuation and analytic order transfer.
- Exact abscissa of every tensor power at an attained top; AM–GM transfer between tensor powers.
- Uncertainty and pricing for arbitrary probability families of twists.
- Pole detection on `Re s = 1` by pretentious distance; order-one bound for every fibre.

**To build.**
- A coinvariant computation that is not orthogonality of a measure (a trace formula for a family
  with a spectral side whose non-invariant part carries no poles).
- A specialization map from generic to special fibre that preserves Frobenius (middle extension).
- The Gaussian (Sato–Tate) law of the gauge family: moments `∼ k! σ^{2k}`.

## 8. Open research topics

1. **Middle extension at `0`.** The off-line `H¹` of the gauge family has generic stalk `0` and
   special stalk the off-line zeros of `ζ`; RH says it is a middle extension at the trivial point.
   Which structure on `G` forces middle extensions?
2. **Non-geometrically-constant motives.** An object over `Spec ℤ` whose local Frobenius eigenvalues
   at `p` are not functions of `log p` and whose global `H¹` contains the zeros of `ζ` (the role of
   `R^{n−1}f_*` in a Lefschetz pencil).
3. **`X^k`.** For `k = 2` the product is the arithmetic surface (SoSZ, ACS), where the input is the
   Hodge index (⇔ RH). Is there a fibration of the surface with loss independent of `k`?
4. **Finite top layer.** Under ¬AAL the top layer is finite-dimensional; Deligne's semicontinuity
   is a statement about finitely many eigenvalues. Does a family specialize a finite top layer?
5. **Families with torsion monodromy.** Exactness over `ℤ` lives on torsion; can a family of finite
   order twists be exact at every tensor power with volume independent of `k`?

## 9. Traps

| Trap | Truth |
|---|---|
| The tensor trick over `ℤ` is weaker than over `𝔽_q` | On one curve it is equally tautological; Deligne's uniformity is a family statement |
| Positivity of `t^{2k}` is the content | Free on every configuration and on the fakes |
| Uniform tensor moments `A_k = o(k)` are a step below RH | They are RH (`riemannHypothesis_iff_tensorExponent_sublinear`) |
| The FE supplies `H²_c` | It supplies the pairing and the pole; every constituent of `M^{⊗2k}` still has a pole |
| Big monodromy transfers to `ζ` | Exact coinvariants price every fibre at the trivial bound |
| Generic purity specializes in the product topology | Constants do, exponents do not; residual fibres carry the pole |
| Haar-generic and Baire-generic agree | Exponent `0` against `½` at every `a < ½` |
| Euler deformations move zeros | Analytically controlled ones are isozeric; the rest leave the class |
| The trivial fibre is a limit of generic ones in measure | It is Haar-null and every constant blows up there |
| Haar averages see zeros | Gauge averages carry only unique factorization |

## 10. Criteria

**Calibrations.** Deligne on curves: over `𝔽_q[T]` the trivial point is better than typical
(`sum_monicOfDeg_polyMoebius`, AGT); Hasse–Weil for every hyperelliptic curve
(`abs_card_points_sub_le_hyperelliptic`, CTH); towers of a curve are its base changes (ACS). Sampling
boundary: one Frobenius aliases; finitely many Frobenii, very smooth degrees and density-zero
exceptions admit unattained tops; power-saving gap sets and power-thin exceptions decide (SoSZ).
Classical saving `√p e^{−√(log p)/10}` (SoSZ).

**Fakes.** A mechanism bounding the weight of `ζ` must use the Euler product and the FE: it must
fail on the integer-norm one-off (`one_off_violates_stepanov_bound`, ALST), the `cosh` models
(`coshModel`, IRWT) and the heat family `H_t`, `t < 0` (`riemannHeat_zeros_im_sq_le`, RHTower).

**A contribution** is an unconditional Lean theorem about weights, tensor powers, families,
coinvariants or specialization that proves a piece of the dictionary, answers a question of §6 with a
sharp boundary, or builds a tool of §7, and states its behaviour on the special fibre. RH-equivalences
count only when they expose a mechanism.

**Success.** A family statement strictly weaker than RH that, with the machinery here, implies the
uniform weights for `ζ`; or a proof that every family-plus-positivity route prices `ζ` at the trivial
bound, with the cohomological input named.

## 11. Context

| Direction | Programmes (module imports) |
|---|---|
| Uses | ArithmeticCorrelationGeometry 3, SurfaceOfSpecZ 2, PrimeTorusTheory 2, TailArithmeticOfThePrimeOrbit 1, mathlib (Chebyshev, Borel–Cantelli, Baire) |
| Cites | ArithmeticGaugeTheory, ArithmeticKunnethTheory, RHTower, CountingHolography, ArithmeticCastelnuovoSeveri |

| Neighbour | Interface |
|---|---|
| SurfaceOfSpecZ | Deligne's moves over `ℤ`; AWT adds the missing sixth move's analysis |
| ArithmeticGaugeTheory | exponents on `G`; AWT adds tensor weights, constants, jump, pricing |
| PrimeTorusTheory | hull and fibres; AWT adds `ζ_x = ζ e^F` and isozeric classes |
| ArithmeticKunnethTheory | vertical family below/above the square-root threshold |
| ArithmeticBaseChange (§2.10) | vertical transport of zeros; AWT is the horizontal (weight) side |

## 12. Big picture

Over `𝔽_q` purity is a family statement specialized to a point. AWT proves that over `ℤ` the family
half works and the specialization half is exactly what is missing. The gauge torus is a genuine
Deligne family: big monodromy with weight-zero coinvariants and uniform tensor weights at the
generic fibre. `ζ` is its trivial fibre, and every route from the family to that fibre is closed by
a theorem: the virtual motive of the zeros is geometrically constant and its tensor powers have
exactly their weight; the pole is a jump whose locus is the pretentious archimedean line;
constants specialize but blow up; exponents are not
semicontinuous (residual against null); analytically connected fibres keep the zeros; and positivity
against any exact monodromy returns the trivial bound. What remains is the structure that over `𝔽_q`
is cohomology: a Frobenius-preserving specialization from the generic to the special fibre.
