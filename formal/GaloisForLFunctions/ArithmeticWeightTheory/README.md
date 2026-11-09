# Arithmetic Weight Theory of Spec ℤ (AWT)

Namespace `GaloisForLFunctions.ArithmeticWeightTheory`; umbrella `ArithmeticWeightTheory.lean`; 12 modules.
All results unconditional; RH appears only inside equivalences.

Notation. `z = ρ − ½` for a zero `ρ`; `b = sup Re z` the **weight** (zero width) of a configuration;
`B = U₁^{⋆4}` the cubic spline; `t(d) = 2 Re S(log d)` the spline trace of the zeros at the degree `d`;
`M = Σ_z e_z ℤ(−z)` the virtual motive of the zeros, whose Frobenius at `n` acts by `n^z`;
`G = (ℝ/ℤ)^ℕ` the gauge torus with twists `χ_x`, Haar measure and fibres `ζ_x(s) = Σ χ_x(n) n^{−s}`;
for a window `g` and radius `R`, `T_x(u) = e^{−u/2} Σ_{p ≤ e^{u+R}} log p · g(log p − u) · χ_x(p)` the
window trace of the fibre `x`; `x_t = (p^{it})_p` the archimedean line, whose fibres are `ζ(s − it)`.

## 1. Motivation

Deligne's purity proof over `𝔽_q` has six moves: positivity of the even tensor powers `F^{⊗2k}`, the
Rankin square, Landau–Pringsheim at the real pole, base change, the absence of a real eigenvalue on
the blind side, and the a priori location of the poles of `L(F^{⊗2k}, T)` uniformly in `k`. Over `ℤ`
the first five are theorems (`SurfaceOfSpecZ`): RH ⇔ the tensor powers of `M` have a common
half-plane of convergence. The sixth move is missing. Over a curve it is
`H²_c(U, F^{⊗2k}) = (F^{⊗2k})_{π₁^geo}(−1)`: poles come only from coinvariants of the geometric
monodromy, whose Frobenius weight a pairing fixes; the non-invariant constituents sit in `H¹_c` and
carry no poles.

AWT determines what plays this role over `ℤ`, in three steps.

1. **`M` alone has no `H²_c`.** Its Frobenius acts through `log n`; every constituent of `M^{⊗2k}`
   is a Tate twist whose L-function `ζ(s − Σz_i)` has a pole. The top pole of every tensor power
   sits exactly at `1 + 2kb`. The tensor trick for `M` reads the weight and nothing else; one curve
   over `Spec 𝔽_q` is the same.
2. **Families supply it generically.** On the gauge torus twisting is a geometric direction and Haar
   orthogonality is big monodromy: the coinvariants of the `2k`-th tensor power are the `k!`
   permutation pairings, of weight zero, and the Frobenius of the generic fibre is Gaussian.
   Deligne's argument runs: almost every fibre has uniform tensor weights.
3. **The special fibre does not inherit it.** `ζ` is the trivial fibre, the bad character of this
   Mellin family. Its pole is a coinvariant jump, and the jump locus is exactly the pretentious
   neighbourhood of the archimedean line. Along that line `ζ`'s Frobenius has the generic law and,
   below the square-root threshold, the generic moments; beyond it the non-invariant part only adds.
   Constants specialize but blow up at `ζ`; exponents do not specialize; isozeric deformations are
   null; and any family that computes its coinvariants by orthogonality prices every fibre at the
   trivial bound.

The missing input is located: a specialization that is neither measure, nor law, nor category, nor
positivity against orthogonality — a map from the generic to the special fibre of the kind
cohomology supplies over `𝔽_q` (middle extension, invariants of local monodromy).

## 2. Objects

| Object | Lean | Meaning |
|---|---|---|
| Configuration, weight, top | `ZeroConfig`, `zetaZeroWidth`, `TopDepth` (SRT, SoSZ) | zeros; `b`; exponents `≤ b` |
| Spline trace | `lagStructure Z (boxSpline 1 3)` (AOG) | `S_Z(u) = Σ_z e_z e^{zu}` |
| Tensor series | `tensorTerm`; `tensorLogDerivTerm`, `primeTraceMoment` (SoSZ) | `Λ(n) t(log n)^{2k} n^{−σ}`; moments at primes |
| Gauge family | `GaugeTorus`, `twist`, `gaugeHaar`, `twistSum` (ACG); `gaugeFibre` (PTT) | fibres, `χ_x(n)`, monodromy measure, `ζ_x` |
| Window trace, moment | `windowPrimes`, `windowWeight`, `windowWeightReal`, `fibreTrace`, `fibreMoment` | `T_x(u)`; `Σ_{p≤N} log p |T_x(log p)|^{2k}` |
| Variance, pairings | `windowVariance`, `injSum`, `tupleWeight` | `V(u) = ∫|T_x(u)|²`; sums over injective tuples |
| Trace constant | `traceConstantSet g R K a` | fibres with `|T_x(log p)| ≤ K p^a` at every prime |
| Euler deformation | `deformationPrimeSum`, `deformationExponent`, `isozericClass` | `ζ_x = ζ e^F`; summable prime perturbations |
| Orthonormal family | `TwistOrthonormalOn ν s` | a probability family with exact coinvariants on `s` |
| Reset fibre | `resetOutside I x` | agrees with `x` on `I`, trivial elsewhere |
| Edge distances | `pretTerm`, `antiTerm`, `pretSum`, `antiSum`, `polePoint` | `1 ∓ Re(χ_x(p)p^{−iτ})`; damped sums; `1 + δ + iτ` |
| Prime restriction | `primeRestrict`, `windowObservable` | `G → (ℝ/ℤ)^{primes}`; `φ` of a window sum |

## 3. Language

- **Weight**: `b = sup Re z`; **pure**: `b = 0`; **top attained**: some zero has real part `½ + b`.
- **Tensor power**: `t^{2k}`; its series has nonnegative coefficients on every configuration.
- **Family**, **fibre**, **special fibre** (`ζ`, the trivial point), **generic** (Haar-a.e.),
  **Baire-generic** (residual), **archimedean line** (`x_t`, the vertical shifts of `ζ`).
- **Coinvariants**: monodromy averages of tensor monomials; on `G` the multiplicative pairings.
- **Gaussian Frobenius**: `2k`-th moments `∼ k!·V^k` (Sato–Tate law of a full-torus monodromy).
- **Jump**: a coinvariant present only at special fibres (a pole on `Re s = 1`).
- **Edge divisor**: poles and zeros of a fibre on `Re s = 1`. **Pretentious** to `±n^{iτ}`:
  `Σ_p (1 ∓ Re χ_x(p)p^{−iτ})/p < ∞`.
- **Constant / exponent**: in `|T_x(log p)| ≤ K p^a`, `K` and `a`. Over `𝔽_q` only exponents exist.
- **Specialize (Deligne direction)**: special `≤` generic. **Coherent direction**: special `≥` generic.
- **Isozeric**: same zeros with multiplicities on a half-plane. **Pricing**: the bound a family
  transfers to one fibre by positivity.

## 4. Mechanisms

**Built on (corpus).** Tensor trick, common abscissa, Rankin square at `1 + 2b`, width law, base
change, Stepanov blindness, sampling at gap sets (SoSZ); gauge moments as multiplicative diagonals
(ACG); hull, natural boundary, fibre logarithm, Hurwitz (PTT); gauge exponent (AGT); Steinhaus bound
(TAPO); windowed product moments below/above the square-root threshold (AKT); Kronecker–Weyl on the
prime torus (HTGeometry); Chebyshev bounds, Borel–Cantelli, Baire category (mathlib).

**Proved here.**
1. *Big monodromy.* `∫|Σ_p a_p χ_x(p)|^{2k} ≤ k!(Σ|a_p|²)^k`.
2. *Pairings attained.* An injective tuple and its `k!` rearrangements share their product, so
   `Σ_N (a^{*k}(N))² ≥ k! Σ_{t injective} Π a_{t_i}²`; each new distinct prime avoids `≤ k` values,
   giving `Σ_{t injective} Π w ≥ (V − kM)^k`.
3. *Generic uniform weights.* Markov at dyadic degrees + Borel–Cantelli.
4. *Jump.* `θ(e^{u+1}) − θ(e^{u−1}) ≥ e^u` (`u ≥ 200`) gives `|T_0(log p)| ≥ c√p`; trace-constant
   sets are closed, exhaust `G` in measure, avoid a neighbourhood of `0`, and are nowhere dense
   (resetting all but finitely many coordinates reproduces the pole).
5. *Isozeric deformations.* `ζ_x = ζ e^F` on `Re s > 1`; `F` analytic where the prime perturbation is
   summable; the residue of `ζ` at `1` excludes such fibres from the a.e. zero-free set.
6. *Exact tensor weight.* Weighted AM–GM dominates the Rankin square by any tensor power.
7. *Pricing.* Exact orthonormality on `s` gives `ν{x₀}·#s ≤ 1`; Cauchy–Schwarz on the products.
8. *Edge divisor.* `|ζ_x(1+δ+iτ)| = |ζ(1+δ)| e^{−D_δ + O(1)}` and
   `|ζ(1+δ)||ζ_x(1+δ+iτ)| = e^{A_δ + O(1)}`; the remainder of the fibre logarithm is bounded by
   `2Σp^{−2}`, uniformly over the family.
9. *Vertical family.* The window trace of `x_t` is `ζ`'s smoothed prime sum at height `t`; the
   restriction to prime coordinates is a measure-preserving surjective homomorphism; the prime
   frequencies `log p` are rationally independent (unique ergodicity); the windowed vertical moment
   is the multiplicative diagonal below the threshold plus a nonnegative off-diagonal above it.

## 5. Pillar theorems

| Theorem | Lean | Status |
|---|---|---|
| Big monodromy of the gauge family | `integral_norm_twistSum_pow_le`, `integral_norm_fibreTrace_pow_le` | unconditional |
| Generic fibre has uniform weights (M2) | `ae_fibreMoment_le`, `ae_norm_fibreTrace_le` | unconditional |
| Gaussian (Sato–Tate) law of the generic Frobenius | `factorial_mul_pow_le_moment`, `moment_le_factorial_mul_variance_pow`, `tendsto_moment_ratio` | unconditional |
| Pole at the trivial fibre, exponent `½` | `mul_sqrt_le_trivial_fibreTrace`, `exists_prime_mul_rpow_lt_trivial_fibreTrace` | unconditional |
| Constants specialize, blow up at `ζ` | `isClosed_traceConstantSet`, `tendsto_measure_traceConstantSet`, `trivial_fibre_is_the_jump` | unconditional |
| Baire-generic pole, Haar-generic purity | `isNowhereDense_traceConstantSet`, `residual_and_null_of_traceExponent` | unconditional |
| Every fibre is `ζ e^F`; isozeric deformations; null class | `gaugeFibre_eq_zeta_mul_exp`, `exists_isozeric`, `analyticOrderAt_isozeric`, `gaugeHaar_isozericClass_eq_zero` | unconditional |
| Tensor powers have exactly their weight | `summable_tensorTerm_iff_of_max` | unconditional |
| `A_k ≥ 2k·width − 1`; M4 ⇔ RH | `zetaZeroWidth_le_of_primeTraceMoment_le`, `riemannHypothesis_iff_tensorExponent_sublinear` | unconditional; RH-equivalence |
| Uncertainty and pricing | `measureReal_singleton_mul_card_le`, `measureReal_singleton_mul_pow_le` | unconditional |
| Pole iff pretentious; jump locus null, contains `x_t` | `pole_iff_pretentious`, `pretentious_archimedeanLine`, `gaugeHaar_jumpLocus_eq_zero` | unconditional |
| Edge zero iff anti-pretentious; simple poles and zeros | `edgeZero_iff_antiPretentious`, `eventually_mul_norm_gaugeFibre_le`, `eventually_mul_le_norm_gaugeFibre`, `not_pretentious_and_antiPretentious` | unconditional |
| Edge divisor of `ζ`: one simple pole; `ζ(1+iτ) ≠ 0 ⇔ Σ_p (1+cos(τ log p))/p = ∞` | `edgeDivisor_zeta`, `riemannZeta_ne_zero_iff_not_antiPretentious` | unconditional |
| Vertical family has the generic moments below the threshold, more above | `vertical_moment_eq_generic`, `generic_moment_le_vertical_moment` | unconditional |
| Vertical Frobenius of `ζ` has the generic law | `tendsto_verticalAverage_fibreTrace` | unconditional |
| Tensor trick, common abscissa (M1) | `riemannHypothesis_iff_moments_primeTraces`, `riemannHypothesis_iff_tensorPowers_commonAbscissa` (SoSZ) | RH-equivalence, built on |
| Strip specialization is RH | `riemannHypothesis_iff_limits_zeroFree` (PTT), `riemannHypothesis_iff_zetaStronglyRecurrent` (RHTower) | RH-equivalence, built on |

## 6. Answers to the questions of the field

**Q1. Which family carries `ζ` as a fibre with big monodromy?** None in Deligne's sense.
- *Gauge torus.* Exact big monodromy: coinvariants are the `k!` pairings, attained, Gaussian law;
  generic fibre has uniform weights. `ζ` is the trivial fibre: Haar-null, meagre, a jump.
- *Vertical shifts* (the archimedean line, every fibre a shift of `ζ`). Big monodromy in law at every
  degree (`tendsto_verticalAverage_fibreTrace`) and in moments up to the square-root threshold
  (`vertical_moment_eq_generic`); beyond it the vertical moments exceed the generic ones
  (`generic_moment_le_vertical_moment`). Weights are constant along the line; the specialization is
  in law, where a single zero has measure zero.
- *Any probability family with exact coinvariants*: every fibre has mass `≤ 1/length`, and positivity
  transfers at best the trivial bound (`measureReal_singleton_mul_pow_le`). Over `𝔽_q` Deligne does
  not compute coinvariants by orthogonality: cohomology bounds the non-invariant constituents.
- *Dirichlet twists.* Each point reads its own GRH; the special locus is typical on average
  (`dirichletGRH_iff_dirichletGauge_typical`, `card_atypical_dirichletGauge_le_rpow`, AGT).
- *Euler deformations keeping the pole.* Isozeric on `Re s > σ₀`, a Haar-null class.

**Q2. What is the analogue of `H²_c`?** For `M`: all of `M^{⊗2k}`; the top pole is at exactly
`1 + 2kb` for every `k` at an attained top, so no a priori control exists and M4 is RH. For the
gauge family: the multiplicative pairings, weight `0`, dimension `k!` on distinct primes, with
Gaussian Frobenius. The jump locus — fibres with a pole on `Re s = 1` — is the pretentious
neighbourhood of the archimedean line, Haar-null (the analogue of generic vanishing: the line
`n^{it}` plays the subtorus, finite pretentious distance the torsion translation). Every fibre's edge
divisor is classified: simple pole (pretending `n^{iτ}`), simple zero (pretending `−n^{iτ}`), or
neither, with uniform order-one bounds coming from the Euler product. At `ζ` itself the jump is one
simple pole at `1` and nothing else; edge non-vanishing of `ζ` is exactly `Σ_p (1+cos(τ log p))/p = ∞`.

**Q3. In which topology are weights semicontinuous?**
- *Product topology on `G`.* Constants specialize (closed sets) but tend to infinity at `ζ`;
  exponents do not: below `½` the fibres without a constant are residual and Haar-null.
- *Law along the archimedean line.* `ζ`'s vertical Frobenius has exactly the generic law; this sees
  densities, not individual zeros.
- *Strip topology.* Weights are lower semicontinuous (Hurwitz, `eventually_eq_zero_of_limit`, PTT);
  every limit of vertical translates of `ζ` is zero-free or `0` iff RH, and `ζ` returns to itself on
  compacta iff RH.
- *Direction.* Over `ℤ` natural families run coherently, special `≥` generic: the trivial point is
  never better than typical (AGT), vertical moments exceed generic ones past the threshold, the heat
  flow lowers weights (RHTower); isozeric and vertical families are constant. Over `𝔽_q[T]` the
  trivial point is better than typical (`sum_monicOfDeg_polyMoebius`, AGT): Deligne's direction is a
  property of the function field.

**Milestones.** M1 built on. M2 proved (`ae_fibreMoment_le`), with the Gaussian law. M3: the
principle holds in the strip topology; at `ζ` it is RH. M4 is RH: `A_k ≥ 2k·width − 1`. M5 RH.

## 7. Tools

- Big-monodromy calculus for prime-supported twisted polynomials and window traces; pairing lower
  bounds via permutations of injective tuples; distinct-prime estimates.
- Almost-sure tensor moment bounds (dyadic Borel–Cantelli) and trace bounds at the generic fibre.
- Gaussian (Sato–Tate) moment law of the generic Frobenius.
- Trace-constant sets: closedness, exhaustion in measure, nowhere density, residual/null dichotomy.
- Chebyshev window bound and the pole at the trivial fibre; window variance `≥ c²(u − 1)`.
- Euler-deformation exponent `F`, isozeric continuation and analytic order transfer.
- Exact abscissa of every tensor power; AM–GM transfer between tensor powers.
- Uncertainty and pricing for arbitrary probability families of twists.
- Edge divisor by (anti-)pretentious distance; uniform order-one bounds; classical form at `ζ`.
- Specialization along the archimedean line: in law (Kronecker–Weyl through the prime restriction)
  and in moments (exact below the square-root threshold, coherent above).

## 8. Open research topics

These are the residual problems the field isolates; each is at least as hard as the RH-equivalences
of §5 and is stated with the reduction AWT proves.

1. **Middle extension at `0`.** The off-line zeros of the gauge family have generic stalk `0` and
   special stalk the off-line zeros of `ζ`. In the strip topology the special fibre is a limit of
   zero-free fibres iff RH (PTT). Which structure on `G`, finer than law and Haar measure, forces a
   middle extension?
2. **Non-orthogonal coinvariants.** Every family whose coinvariants are computed by orthogonality is
   priced at the trivial bound; along the archimedean line the non-invariant part is nonnegative.
   The sixth move needs a family identity whose non-invariant part is pole-free (cohomology over
   `𝔽_q`).
3. **Non-geometrically-constant motives.** An object over `Spec ℤ` whose local Frobenius at `p` is not
   a function of `log p` and whose global `H¹` contains the zeros of `ζ`. Unimodular twists are
   invisible to Rankin powers (`|χ_x(n)|² = 1`), so the twist must change local weights.
4. **`X^k`.** For `k = 2` the product is the arithmetic surface (SoSZ, ACS), whose input is the
   Hodge index (⇔ RH). A fibration of the surface with loss independent of `k` is open.
5. **Finite top layer.** Under ¬AAL the top layer is finite-dimensional and the `2k`-th tensor
   abscissa is exactly `1 + 2kb`; whether a family specializes a finite top layer is open.

## 9. Traps

| Trap | Truth |
|---|---|
| The tensor trick over `ℤ` is weaker than over `𝔽_q` | On one curve it is equally tautological; Deligne's uniformity is a family statement |
| Positivity of `t^{2k}` is the content | Free on every configuration and on the fakes |
| `A_k = o(k)` is a step below RH | It is RH |
| The FE supplies `H²_c` | It fixes the edge divisor of `ζ` (one simple pole) and the pairing; every constituent of `M^{⊗2k}` still has a pole |
| Big monodromy transfers to `ζ` | Exact coinvariants price every fibre at the trivial bound |
| `ζ`'s vertical Frobenius is generic, so `ζ` is pure | Generic in law and in moments below the threshold; a single zero has measure zero |
| Generic purity specializes in the product topology | Constants do, exponents do not; residual fibres carry the pole |
| Haar-generic and Baire-generic agree | Exponent `0` against `½` at every `a < ½` |
| Euler deformations move zeros | Analytically controlled ones are isozeric; the rest leave the class |
| Poles on `Re s = 1` are special to `ζ` | Every fibre pretending to some `n^{iτ}` has one; the locus is null |
| Haar averages see zeros | Gauge averages carry only unique factorization |

## 10. Criteria

**Calibrations.** Deligne on curves: over `𝔽_q[T]` the trivial point is better than typical
(`sum_monicOfDeg_polyMoebius`, AGT); Hasse–Weil for every hyperelliptic curve
(`abs_card_points_sub_le_hyperelliptic`, CTH); towers of a curve are its base changes (ACS). Sampling
boundary: one Frobenius aliases; finitely many Frobenii, very smooth degrees and density-zero
exceptions admit unattained tops; power-saving gap sets and power-thin exceptions decide (SoSZ).
Classical saving `√p e^{−√(log p)/10}` (SoSZ); edge non-vanishing of `ζ` (`edgeDivisor_zeta`).

**Fakes.** A mechanism bounding the weight of `ζ` must use the Euler product and the FE: it must
fail on the integer-norm one-off (`one_off_violates_stepanov_bound`, ALST), the `cosh` models
(`coshModel`, IRWT) and the heat family `H_t`, `t < 0` (`riemannHeat_zeros_im_sq_le`, RHTower).

**A contribution** is an unconditional Lean theorem about weights, tensor powers, families,
coinvariants, edge divisors or specialization that proves a piece of the dictionary, answers a
question of §6 with a sharp boundary, or builds a tool of §7, and states its behaviour on the special
fibre. RH-equivalences count only when they expose a mechanism.

**Success.** A family statement strictly weaker than RH that, with the machinery here, implies the
uniform weights for `ζ`; or a proof that a named class of family routes prices `ζ` at the trivial
bound, with the missing input named. The second is achieved for orthogonality, measure, law and
category; §8 names what remains.

## 11. Context

| Direction | Programmes (module imports) |
|---|---|
| Uses | ArithmeticCorrelationGeometry, SurfaceOfSpecZ, PrimeTorusTheory, TailArithmeticOfThePrimeOrbit, ArithmeticKunnethTheory, SquareRootThreshold, HTGeometry, RHTower; mathlib (Chebyshev, Borel–Cantelli, Baire, `ζ` non-vanishing) |
| Cites | ArithmeticGaugeTheory, CountingHolography, ArithmeticCastelnuovoSeveri |

| Neighbour | Interface |
|---|---|
| SurfaceOfSpecZ | Deligne's moves over `ℤ`; AWT analyses the missing sixth move |
| ArithmeticGaugeTheory | exponents on `G`; AWT adds tensor weights, constants, jump, edge divisors, pricing |
| PrimeTorusTheory | hull and fibres; AWT adds `ζ_x = ζ e^F`, isozeric classes, pole/zero classification |
| ArithmeticKunnethTheory | windowed moments; AWT reads them as specialization along the archimedean line |
| ArithmeticBaseChange (§2.10) | vertical transport of zeros; AWT is the horizontal (weight) side |

## 12. Big picture

Over `𝔽_q` purity is a family statement specialized to a point. AWT proves that over `ℤ` the family
half works completely and the specialization half is exactly what is missing. The gauge torus is a
genuine Deligne family: big monodromy with weight-zero coinvariants, Gaussian Frobenius and uniform
tensor weights at the generic fibre; its jump locus is the pretentious archimedean line and every
fibre's edge divisor is classified. `ζ` is its trivial fibre, and every route from the family to that
fibre is closed by a theorem: the virtual motive of the zeros is geometrically constant and its
tensor powers have exactly their weight; the pole is a jump; `ζ`'s vertical Frobenius is generic in
law and in moments, which sees no individual zero; constants specialize but blow up; exponents are
not semicontinuous; analytically connected fibres keep the zeros; and positivity against any exact
monodromy returns the trivial bound. What remains is the structure that over `𝔽_q` is cohomology: a
Frobenius-preserving specialization from the generic to the special fibre.
