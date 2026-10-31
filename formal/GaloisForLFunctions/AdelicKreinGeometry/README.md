# Adelic Krein Geometry (AKG)

**Arithmetic signature theory: indefinite harmonic analysis on the dilation–translation system.**

Namespace `GaloisForLFunctions.AdelicKreinGeometry`; umbrella `AdelicKreinGeometry.lean`.

**Question.** Every open problem of the corpus asks to pay an infinite-rank arithmetic debt through
one rank-one channel, the archimedean place, at zero margin and at the exponent `1/2`. Positive
harmonic analysis on `Aff(ℚ)` cannot do it: Weil's correlation carries no successor. The indefinite
theory of the Weil kernel (HKT, AKL) lives on the multiplicative group alone. AKG asks:

> *Which Hermitian forms of finite negative index live on the dilation–translation system
> `ℚ^×_{>0} ⋉ 𝔸 ⊃ Aff(ℚ)`? How is their index computed from local constituents glued at the
> archimedean place, and how do their additive (successor, Haar, theta) and multiplicative
> (dilation, Euler, Mellin) readings compare?*

The basic object is a **Pontryagin state**: a Hermitian function `φ` on a group with finitely many
negative squares `κ(φ) = sup ν(φ(x_a⁻¹x_b))`. The programme's first result is that **support and
decay decide type**. A state whose arithmetic support or decay lets translates escape every finite
family has index `0` or `∞`. A finite nonzero index needs a carrier that never escapes; over `ℚ`
that carrier is the archimedean place. Everything is unconditional; RH appears only inside
equivalences.

---

## 1. Place in the research

The diagnosis (`docs/reports/review-3010/obstacles-summary.md` §2.6): a crossing input must be
critical, square-root precise and selective at once, and all coupling between primes and between
`+` and `×` passes through the archimedean place. Existing fields supply two features each:

| Field | Supplies | Lacks |
|---|---|---|
| Hodge theory | index theorem at zero margin | finite rank, conformal Frobenius |
| Harmonic analysis on groups | Plancherel positivity | `+` and `×` are spectrally singular on `Aff(ℚ)` |
| Krein / Pontryagin spaces | exact negative indices, finite-rank perturbation | arithmetic producers of the index |
| Probability on the gauge torus | Kakutani dichotomies, zero–one laws | the trivial point |
| Analytic number theory | precision | spends a margin |

AKG is **indefinite** (index replaces positivity), **affine** (both ring operations act) and
**adelic** (local factors at every place, glued at `∞`). It is the indefinite counterpart of APD's
affine positivity and the affine counterpart of HKT/AKL's multiplicative index theory.

| Programme | What AKG takes | What AKG adds |
|---|---|---|
| ArithmeticPositiveDuality | positive states on `Aff(ℚ)`, Hecke and Haar states, the Kakutani wall, Mautner rigidity, `splineCorr_zero_of_integer_successor` | what finite negative index changes on `Aff(ℚ)` |
| HeckeKreinToeplitz | `negIndex`, Gram calculus, orthogonal translates, Pontryagin decomposition, `zetaKernel` and its index | induction, escape, mixing on arbitrary groups; the index of Weil's affine extensions |
| ArithmeticKreinLangerTheory | zero-or-infinity for axis-supported kernels, twin-blind locality | the non-commutative escape law behind both; the separable signature formula |
| RenormalizedArithmeticPotentialTheory | the matched local Hodge index at one prime and on finite sieves (`Signature/TheMatchedPrimeFormHasOnePositiveDirection`) | the gluing formula of which it is an instance |
| ArithmeticLorentzianGeometry | Frobenius is conformal, Hecke is a boost (`frobeniusPullback_conformal`, `boost_isometry`) | where conformal symmetry can live: one negative square on the additive side |
| ArithmeticPolarization, HilbertianExplicitFormulas | `W` = collided form ⇔ RH; explicit formulas read only `W` | the additive side as a carrier of index (decay forces `0`/`∞`) |
| SuccessorShellArithmetic, CriticalArithmeticCorrelationTheory | successor shells, conductor modes | open interface (sum-of-squares on shells, §7 Q6) |

---

## 2. Why

**Over `𝔽_q` one object supplies everything.** The Frobenius graph on `C × C` carries the sign
(Hodge index), the count (`Γ_F·Δ = N₁`) and the selection; Frobenius is conformal with factor `q`;
all data sit on one tower.

**Over `ℤ` the corpus has the pieces but not the object.** A positive state with Weil's dilation
part has a blind successor; the integer successor forces Hecke decay and a Kronecker-null dilation
spectrum; a `ℤ`-periodic successor with continuous dilation part is constant. Indefiniteness is
studied only on `ℚ_{>0}`, where tower-supported assemblies have index `0` or `∞`. Local Hodge
indices exist prime by prime and on finite sieves. The two readings of the divisor, `S` from theta
prefixes and `W` from primes, are never compared.

**What AKG establishes.**

1. *Indefiniteness constrains the successor.* In the positive theory successor coordinates are free;
   in the indefinite theory the free (regular) extension multiplies the index by the number of
   cosets, and the index-minimal extension is the blind one.
2. *Support and decay decide type.* Escape (exact, by Hecke support; approximate, by height decay or
   mixing) forces `κ ∈ {0, ∞}`. The Kakutani wall of the Hecke states is a jump from `0` to `∞`.
3. *Integer support and Weil's correlation are incompatible at every finite index.* A Hecke-supported
   Pontryagin state is positive, so with Weil's dilation part its successor is blind. Slope
   corrections do not help: a positive carrier with the integer successor is invisible to the index,
   and with a dilation reading continuous at `1` the slope part has infinite index.
4. *Signatures glue through a shared pole.* For separable assemblies the global index is the sum of
   the local polar indices plus at most one square; for the prime kernel the counterterm must run
   with the horizon.
5. *The additive side counts exactly.* On `ℤ/N` the index is the number of negative conductor
   coefficients; a negative Ramanujan coefficient of conductor `d` costs `φ(d)` squares.
6. *Conformal symmetry costs one negative square.* Positive states admit none; for every exponent
   `0 < s ≤ 1` the conformal successor `−|b|^s` has exactly one, over `ℚ` and over `𝔽_q[T]`.
7. *The index is twin-blind.* Unitary twists are Gram congruences.
8. *The boost and the conformal successor are one state.* The pole pair `|u|^{1/2} + |u|^{−1/2}` of
   Weil's kernel and the archimedean successor `2 − c|b|` are the two readings of one index-one
   state of `Aff(ℚ)`. Every place `v` carries such a state, with boost `|u|_v^{±s/2}` and successor
   `−|b|_v^s`: the boost exponent is half the conformal exponent.
9. *Kernels invisible on both axes are finite-dimensional.* A nonzero affine kernel vanishing on
   translations and dilations has at least two negative squares, is polynomial of degree `< κ` on
   translation fibres and has rank at most `κ²`; every index `≥ 2` occurs.

So the finite stratum is reached by archimedean-continuous carriers that escape no translate and
are not separable: the pole–successor states. What is missing is a carrier of Weil's full dilation
data with an integer successor.

---

## 3. Objects and language

| Weil over `𝔽_q` | AKG object | Over `ℚ` | Lean |
|---|---|---|---|
| intersection form on `C × C` | Pontryagin state, index `κ` | Hermitian `φ` on `Aff(ℚ)` | `HeckeKreinToeplitz.negIndex`, `IsHermKernel` |
| Frobenius tower | dilation part | Weil's correlation = `K_ζ` | `ratCorr`, `ratCorr_eq_zetaKernel` |
| additive structure | successor | Haar state `1_ℤ`, Hecke states | `heckeState`, `HasIntegerSuccessor` |
| — | blind / regular extension | `ratCorr(|a|)` / zero off dilations | `blindWeilState`, `regularWeilState` |
| integrality of points | Hecke support | `φ(ax + b) ≠ 0 ⇒ den(a)b ∈ ℤ` | `IsHeckeSupported` |
| — | height decay, mixing | decay in `|num a|·den a` | `HasHeightDecay`, `slopeHeight` |
| local factor | local constituent, polar index | `κ₀(k)` on `Σc = 0` | `polarIndex`, `totalMass` |
| `H + V` | shared pole direction | the constant function | `separable` |
| conformal Frobenius | conformal successor | `−|b|^s`, factor `|u|^s`; `−|·|_∞`, factor `q` | `absRat`, `negPowKernel`, `negAbsInf` |
| — | near coincidence | rationals near `1` have large denominators | `one_le_den_mul_abs_sub_one` |
| conductor | Fourier coefficient on `ℤ/N` | `a_ξ = N⁻¹ Σ e(−xξ/N) k(x)` | `fourierCoeff` |
| — | Ramanujan coefficient of conductor `d` | `A_d = a_{N/d}` on unit-invariant kernels | `ramanujanCoeff`, `IsConductorInvariant` |
| quadratic twist | unitary twist | `φ · χ(slope)` | `slopeChar` |
| Frobenius eigenvalues `1, q` (the poles of `Z`) | boost pair at the fixed points `0`, `∞` of `ℙ¹` | `|u|^{1/2} + |u|^{−1/2}` | `slopePow`, `poleSuccessor` |
| — | conformal induction | `|a|_v^{−s/2} ψ(b)` | `conformalInduction`, `IsConformal` |
| places | local pole–successor state | `−|b|_v` at `v = ∞, p`; `|f|_∞ = q^{deg f}` on `𝔽_q(T)` | `negUltra`, `Rat.AbsoluteValue.padic`, `inftyAbs` |
| — | axis-invisible kernel | zero on translations and dilations | `Haar/AxisInvisibility`, `mixedPowerKernel` |

**Words.**

- *Witness family*: a finite family on which the Gram matrix attains `κ` (`IsWitness`). *Witness
  complement*: coefficient vectors orthogonal to every witness point; it is positive.
- *Escape*: a translate `t` with `φ(x_a⁻¹ t y_b) = 0` for given finite families; *approximate
  escape*: along a sequence `t_j`, `φ(x_a⁻¹ t_j y_b) → 0`. *Mixing*: one sequence that escapes
  every two-sided translate.
- *Blind extension*: pullback along `g ↦ |slope g|`, constant successor. *Regular extension*:
  extension by zero off a subgroup.
- *Polar index*: negative squares on the polar hyperplane of the constant direction. *Gluing
  square*: the at most one square the pole adds when local polar indices are assembled.
- *Separable assembly*: `Σ_p k_p(g_p)` on `Π_p H_p`. *Axis family*: block `p` on the `p`-th axis.
- *Conformal factor*: `λ` with `φ ∘ α = λφ` for an endomorphism `α`.
- *Twin*: the product of a state with a unitary character of its slope.
- *Point vectors*: `k_t` (`t ∈ ℚ`) and `k_∞`, with `[k_s, k_t] = ψ(t − s)`, `[k_∞, k_t] = 1`,
  `[k_∞, k_∞] = 0`; `x ↦ ax + b` acts by `k_t ↦ |a|^{−s/2} k_{at+b}`, `k_∞ ↦ |a|^{s/2} k_∞`.
- *Boost pair*: the dilation coefficient `|u|^{s/2} + |u|^{−s/2}` of `k_0 + k_∞`.
- *Pole–successor state*: the coefficient of `k_0 + k_∞`; *conformal induction*: the coefficient of
  `k_0`.
- From the corpus: Hecke states, Haar state, Kakutani wall, matched counterterm, successor shells,
  conductor modes, collision charge, rate = depth.

---

## 4. Mechanisms

1. **Induction formula** (`TheIndexOfAnInducedState`). Pullback along a surjective homomorphism keeps
   `κ` (`negIndex_comp_of_surjective`); no extension has smaller index than its restriction
   (`negIndex_le_of_extension`); the blind extension along a retraction attains it
   (`negIndex_comp_retraction`). Orthogonal translates carry copies of a whole negative subspace
   (`card_mul_le_negIndex_of_orthogonal_translates`), so the regular extension has
   `κ(ext₀ψ) = [G : H]·κ(ψ)` (`negIndex_extendFromSubgroup`): one copy of the witnesses per coset,
   and the squares that pay `ψ` pay `ext₀ψ` once per coset (`negIndex_extendFromSubgroup_le`). Off
   an infinite-index subgroup a non-positive `ψ` has a regular extension of infinite index
   (`negIndex_extendFromSubgroup_eq_top`).
2. **Witness complements and escape** (`TheWitnessComplementIsPositive`). A vector orthogonal to a
   witness family has nonnegative form (`hermQuad_nonneg_of_orthogonal_witness`); the translate of
   any family into the complement has the same Gram matrix, so escape forces a finite index to be
   zero (`negIndex_eq_zero_or_top_of_escape`).
3. **Arithmetic escape** (`HeckeSupportedStatesHaveIndexZeroOrInfinity`). Translation by `1/P` for a
   prime `P` above all denominators: `d(β + 1/P)/α ∈ ℤ` would force `P ∣ d·den α·den β`
   (`den_ne_one_of_prime`). Hence the affine zero-or-infinity law
   (`negIndex_eq_zero_or_top_of_isHeckeSupported`), Hecke-supported Pontryagin states are positive
   (`isPosDefOnGroup_of_isHeckeSupported`), and the Kakutani wall is an index wall
   (`negIndex_heckeState`: `0` for `s ≥ 1/2`, `∞` for `s < 1/2`).
4. **Mixing** (`MixingKillsNegativeSquares`). Block additivity (`hermNegIndex_add_le_fromBlocks`) and
   lower semicontinuity of the index turn approximate escape into `κ ∈ {0, ∞}`
   (`negIndex_eq_zero_of_tendsto_escape`, `negIndex_eq_zero_or_top_of_mixing`). On `ℤ` and on the
   translations of `ℚ`, decay at `+∞` suffices (`negIndex_eq_zero_or_top_of_tendsto_int`,
   `negIndex_eq_zero_or_top_of_tendsto_rat`). On `Aff(ℚ)` the doubling dilations escape every state
   that decays with the slope height, which is submultiplicative (`ratHeight_mul_le`,
   `negIndex_eq_zero_or_top_of_heightDecay`); the Hecke states decay for `s > 0`
   (`hasHeightDecay_heckeState`, `negIndex_heckeState_eq_top_of_mixing`).
5. **Weil's affine extensions** (`ThePontryaginExtensionsOfWeilsCorrelation`). `ratCorr` is the Weil
   kernel `K_ζ` (`ratCorr_eq_zetaKernel`, `negIndex_ratCorr`). Every extension has index at least
   `κ(K_ζ)` (`negIndex_le_of_weil_extension`), the blind one exactly `κ(K_ζ)`
   (`negIndex_blindWeilState`); the regular one has index `0` under RH and `∞` otherwise
   (`negIndex_regularWeilState`); a Hecke-supported extension of finite index proves RH
   (`riemannHypothesis_of_isHeckeSupported_weil_extension`); with successor `c·1_ℤ`, `c ≠ 0`, every
   Hecke-supported extension has infinite index (`negIndex_eq_top_of_weil_haarSuccessor`,
   `negIndex_eq_top_of_weil_integerSuccessor`).
6. **Outside Hecke support** (`Haar/OneNegativeSquare`). The Haar state minus `4(log₂|a|)²` keeps the
   integer successor and has exactly one negative square (`negIndex_haarOneNegativeSquare`); it is
   not Hecke-supported (`not_isHeckeSupported_haarOneNegativeSquare`) and its dilation reading is
   discontinuous at `1` (`haarOneNegativeSquare_dilation_discontinuous`). A positive carrier `p` with
   the integer successor is invisible to the index: `κ(p + ψ ∘ slope) = κ(ψ)`
   (`negIndex_add_slope_of_integer_successor`), because rational translates average its Gram
   matrices to `0`; its dilations obey `|p(D_q)|² ≤ |q − 1|` (`normSq_dilation_le_abs_sub_one`), so a
   dilation reading continuous at `1` forces `κ = ∞` (`negIndex_add_slope_eq_top_of_continuous_dilation`),
   in particular for Weil's correlation (`negIndex_add_slope_eq_top_of_weil_dilation`). Kernels zero
   on both axes (`Haar/AxisInvisibility`, `Haar/PolynomialPerturbations`, `Haar/FiniteRankPerturbations`,
   `Haar/PowerKernels`): index `≥ 2` unless zero (`two_le_negIndex_of_zero_axes`), polynomial of
   degree `< κ` on each translation fibre (`exists_polynomial_translation_fibre_lt_index`), Gram rank
   `≤ κ²` (`rank_gram_le_square_of_zero_axes`); `γ(1 − a^{−d})b^d` has index `d + 1`, also after adding
   any positive state (`negIndex_posDef_add_canonicalMixedPower`), so the Haar state carries every
   index `≥ 2` with both axis readings unchanged (`negIndex_haarMixedPowerState`); its quadratic
   member is not positive plus a slope function (`haarMixedQuadraticState_not_positive_add_slope`).
7. **Signature of separable assemblies** (`TheSignatureOfASeparableAssembly`). Mean-zero blocks on
   different axes are orthogonal and the local forms add (`hermQuad_gram_axes`); a maximal polar
   negative subspace leaves a nonnegative complement (`hermQuad_nonneg_of_orth_maximal`), so a sum of
   forms has at most one square beyond the sum of its polar indices (`hermNegIndex_sum_le`). Hence
   `Σ_p κ₀(k_p) ≤ κ(Σ_p k_p ∘ π_p) ≤ Σ_p κ₀(k_p) + 1` (`polarIndex_sum_le_negIndex_separable`,
   `negIndex_separable_le_polarIndex_sum_add_one`). The minimum kernel is a sum of squares, so `−|m|`
   is conditionally positive on `ℤ` (`hermQuad_gram_negAbsKernel_eq`, `polarIndex_negAbsKernel`) and
   the weighted negative log-height `−Σ a_p|m_p|`, e.g. `−log(nd)` on `S`-units, has exactly one
   negative square (`negIndex_negLogHeight`).
8. **Conformal symmetry** (`ConformalSymmetryNeedsANegativeSquare`). Endomorphisms fix the identity,
   so a positive state with `φ ∘ α = λφ`, `λ ≠ 1`, vanishes
   (`eq_zero_of_conformal_of_isPosDefKernel`, `eq_zero_of_conformal_successor`). Conformal successors
   are homogeneous (`conformal_successor_eq`). On `ℚ`, `−|b|` is conditionally positive after one
   integral rescaling (`exists_gram_negAbsRat_eq`, `polarIndex_negAbsRat`), strictly so on distinct
   points (`hermQuad_gram_negAbsKernel_pos`); so `−|b|` has index one (`negIndex_negAbsRat`), `|b|` is
   negative definite on every polar hyperplane (`hermQuad_gram_absRat_neg`) and has index `∞`
   (`negIndex_absRat`), and `κ(c|b|) = 0, 1, ∞` for `c = 0, < 0, > 0` (`negIndex_mul_absRat`).
9. **The adelic product state** (`TheAdelicProductState`). Schur products of positive-definite
   kernels are positive (`IsPosDefKernel.mul`, via Hadamard products, `posSemidef_gram_iff`); every
   product with the Haar state is Hecke-supported, so `κ ∈ {0, ∞}`
   (`negIndex_mul_haarState_eq_zero_or_top`). The product of Weil's archimedean correlation with the
   Haar state, the candidate second bridge, has index `0` or `∞`, and `0` under RH
   (`negIndex_adelicWeilState_eq_zero_or_top`, `negIndex_adelicWeilState_of_riemannHypothesis`).
10. **The running counterterm** (`NoFixedCountertermMakesThePrimeKernelPontryagin`). Weil's prime
   kernel on `ℚ_{>0}` restricts on the atoms `1, …, N` to the atomic prime form
   (`gram_countertermKernel`); translation by a product `PQ` of two new primes escapes it
   (`primeLatticeKernel_escape`); the truncated pole vector beats any fixed counterterm. Hence
   `κ(D·δ₁ − P) = ∞` for every real `D` (`negIndex_counterterm_sub_primeLatticeKernel`), while on each
   window the running counterterm `log N − γ` leaves one positive direction (RAPT).
11. **Archimedean continuity against height decay** (`ArchimedeanContinuityAgainstHeightDecay`). A
   rational `q ≠ 1` has `den q ≥ 1/|q − 1|` (`one_le_den_mul_abs_sub_one`), so near-coincident points
   `(K + i)/K` have ratios close to `1` with huge denominators: a state continuous at `1` minus a
   state decaying with the denominator and positive at `1` has infinite index
   (`negIndex_sub_eq_top`). Spreading over the translates `x ↦ x + j/P` removes any Hecke-supported
   part (`den_ne_one_of_prime_mul`), so `κ(s) ≤ κ(s(|a|) + ψ)` (`negIndex_le_negIndex_slope_add`).
   Hence a slope correction of a positive Hecke-supported state with the integer successor has
   infinite index as soon as its dilation part is continuous at `1` (`negIndex_slope_add_eq_top`),
   in particular when it is Weil's correlation (`negIndex_eq_top_of_weil_slope_add`).
12. **The additive index law** (`TheAdditiveIndexLaw`). On `ℤ/N` a Hermitian kernel is the Fourier
   sum `Σ_ξ a_ξ e(xξ/N)` with real coefficients (`kernel_eq_sum_fourierCoeff`,
   `conj_fourierCoeff`); its Gram forms are `Σ_ξ a_ξ |Σ_b c_b e(y_b ξ/N)|²`
   (`gramForm_eq_sum_fourierCoeff`), so `κ(k) = #{ξ : a_ξ < 0}` exactly (`negIndex_zmod_eq_card`);
   unit-invariant kernels have coefficients constant on conductor classes (`fourierCoeff_unit_mul`).
   On `ℚ/ℤ` (`TheAdditiveIndexLawOnQModZ`) a `1`-periodic successor state has its level-`N` Gram
   matrices on `(1/N)ℤ/ℤ` (`gram_levelKernel`), every family lives at one level
   (`negIndex_le_iSup_level`), and `κ(ψ) = sup_N #{negative conductor coefficients at level N}`
   (`negIndex_eq_iSup_card_negCoeffs`). Ramanujan form (`TheRamanujanIndexLaw`): every `ξ` is a unit
   multiple of `N/ord ξ` (`exists_unit_mul_conductorRep`, from `ZMod.eq_unit_mul_divisor`), so a
   unit-invariant kernel has one coefficient `A_d` per conductor `d ∣ N` and
   `κ = Σ_{d ∣ N, A_d < 0} φ(d)` (`negIndex_zmod_eq_sum_totient`); a periodic successor invariant
   under multipliers prime to the denominator has `κ = sup_N Σ_{d ∣ N, A_d^{(N)} < 0} φ(d)`
   (`negIndex_eq_iSup_sum_totient`).
13. **Stable conformal successors** (`StableConformalSuccessors`). Poisson subordination
   `|m|^s = I_s(|m|)/I_s(1)`, `I_s(t) = ∫_0^∞ (1 − e^{−rt}) r^{−1−s} dr` (`subordination_eq`,
   `abs_rpow_eq_subordination`), writes the polar form of `−|m|^s` as an integral of Poisson Gram
   forms, hence nonnegative (`hermQuad_gram_negPow_nonneg`): for `0 < s < 1`, `κ(−|m|^s) = 1`
   (`negIndex_negPow`) and the dilations act with factor `|u|^s` (`negPowKernel_conformal`).
14. **The function-field conformal successor** (`TheFunctionFieldConformalSuccessor`). On `K[X]` the
   ultrametric `|p|_∞ = b^{deg p}` decomposes into equivalence kernels of the high parts
   (`absInf_sub_eq_sum`, `re_sum_ite_eq_nonneg`), so `κ(−|·|_∞) = 1` (`negIndex_negAbsInf`), and `X`
   acts with factor `b` (`absInf_X_mul`); over `𝔽_q`, `b = q`.
15. **Twin-blindness** (`TheIndexIsTwinBlind`). `χ(x_a⁻¹x_b) = conj χ(x_a)χ(x_b)` makes a unitary twist a
   diagonal congruence (`negIndex_mul_unitaryChar`); on `Aff(ℚ)` slope twists keep the index, Hecke
   support and height decay (`negIndex_mul_slopeChar`, `isHeckeSupported_mul_slopeChar`,
   `hasHeightDecay_mul_slopeChar`), and every twin of a Hecke state has the same wall
   (`negIndex_heckeState_mul_slopeChar`).
16. **The pole as a Krein state** (`ThePoleIsAKreinStateOfTheAffineGroup`). The positive affine maps
   are the Borel subgroup of `SL(2, ℝ)`, which preserves `h(x, y) = i(x̄₀y₁ − x̄₁y₀)` of signature
   `(1, 1)`. Its coefficient `a^{1/2} + a^{−1/2} − i b a^{−1/2}` (`poleState_inv_mul`) has Gram
   matrices `Wᴴ h W` (`gram_poleState`), nonnegative on the line `x₀ = i x₁`, so it has exactly one
   negative square (`negIndex_poleState`): the pole pair on the dilations, `2 − ib` on the
   translations, with the odd conformal factor `u` (`poleState_conformal`).
17. **Conformal induction and the pole–successor state**
   (`TheHeckeBoostAndTheConformalSuccessorAreOneState`, over any field `K` with the affine group of
   `TheAffineGroupOfAField`). For an absolute value `v` of `K` and `ψ` conformal of exponent `s`
   (`IsConformal`), the Gram matrices of `|a|_v^{−s/2} ψ(b)` are diagonal
   congruences of those of `ψ` (`hermQuad_gram_conformalInduction`), so `κ(Φ_ψ) = κ(ψ)`
   (`negIndex_conformalInduction`). Adding the boost pair gives the Gram form `2 Re(X̄Y)` plus the
   form of `ψ` with total mass `X` (`hermQuad_gram_poleSuccessor`): on `X = 0` only `ψ`'s polar form
   remains, so a conditionally positive `ψ` gives exactly one negative square
   (`negIndex_poleSuccessor`). At the real place: `|a|^{1/2} + |a|^{−1/2} − c|a|^{−1/2}|b|`
   (`negIndex_poleSuccessorState`) and its stable analogues `−c|b|^s`, `0 < s < 1`
   (`negIndex_poleSuccessor_negPowRat`); the readings are the boost pair and `2 + ψ(b)`
   (`poleSuccessor_dilation`, `poleSuccessor_translation`).
18. **Every place** (`EveryPlaceCarriesAPoleSuccessorState`). For a nonarchimedean `v` the balls
   `{|z|_v ≤ r}` are subgroups (`ballSubgroup`), so ball kernels are equivalence kernels
   (`re_sum_ite_ball_nonneg`); the layer cake `R − t = ∫_0^R 1[t ≤ r] dr`
   (`integral_indicator_Ici_eq`) writes the polar form of `−|b|_v` as an integral of ball forms
   (`hermQuad_gram_negUltra_nonneg`). Hence each `p`-adic place carries the index-one state
   `|a|_p^{1/2} + |a|_p^{−1/2} − c|a|_p^{−1/2}|b|_p` (`negIndex_padicPoleSuccessor`), and
   `−|a|_p^{−1/2}|b|_p` has index one (`negIndex_padicInduction`). Over `F(X)` the place at infinity
   `|f|_∞ = b^{deg f}` is ultrametric (`inftyAbs`, `isUltra_inftyAbs`), its pole–successor state has
   index one (`negIndex_inftyPoleSuccessor`), and the dilation by `X` is the boost
   `b^{1/2} + b^{−1/2}` (`inftyPoleSuccessor_dilation_X`); over `𝔽_q`, `b = q`.

---

## 5. Pillar theorems

1. **Induction formula**: `κ(ext₀ψ) = [G : H]·κ(ψ)`; blind extensions are index-minimal
   (`negIndex_extendFromSubgroup`, `negIndex_comp_retraction`).
2. **Escape and mixing laws**: exact or approximate escape forces `κ ∈ {0, ∞}`
   (`negIndex_eq_zero_or_top_of_escape`, `negIndex_eq_zero_of_tendsto_escape`).
3. **The affine zero-or-infinity law and the Kakutani index wall**
   (`negIndex_eq_zero_or_top_of_isHeckeSupported`, `negIndex_heckeState`).
4. **Weil's affine extensions**: minimum `κ(K_ζ)`; Hecke support plus the Haar successor costs
   infinitely many squares (`negIndex_blindWeilState`, `negIndex_eq_top_of_weil_haarSuccessor`).
5. **Separable signature formula** (`polarIndex_sum_le_negIndex_separable`,
   `negIndex_separable_le_polarIndex_sum_add_one`, `negIndex_negLogHeight`).
6. **Conformal symmetry needs exactly one negative square** (`eq_zero_of_conformal_of_isPosDefKernel`,
   `negIndex_mul_absRat`).
7. **Twin-blindness of the index** (`negIndex_mul_unitaryChar`).
8. **No fixed counterterm** (`negIndex_counterterm_sub_primeLatticeKernel`): the matched prime kernel
   has no Pontryagin realization on the Hecke lattice at any fixed renormalization.
9. **Archimedean continuity against height decay** (`negIndex_sub_eq_top`,
   `negIndex_le_negIndex_slope_add`, `negIndex_slope_add_eq_top`): `+` and `×` cannot be subtracted
   at finite index on the dilations.
10. **The additive index law** (`negIndex_zmod_eq_card`, `negIndex_eq_iSup_card_negCoeffs`,
   `negIndex_zmod_eq_sum_totient`): on `ℤ/N` the index is the number of negative conductor (Fourier)
   coefficients, on `ℚ/ℤ` its supremum over levels; for unit-invariant kernels a negative Ramanujan
   coefficient of conductor `d` costs exactly `φ(d)` squares.
11. **Conformal successors of every exponent** (`negIndex_negPow`, `negIndex_negAbsInf`): index one,
   factor `|u|^s` over `ℚ` and `q` over `𝔽_q[T]`.
12. **Conformal induction** (`negIndex_conformalInduction`): `κ(|a|_v^{−s/2}ψ(b)) = κ(ψ)` for every
   place `v` and every conformal `ψ`.
13. **The pole–successor law** (`negIndex_poleSuccessor`, `negIndex_poleSuccessorState`,
   `negIndex_padicPoleSuccessor`): boost pair plus a conditionally positive conformal successor has
   index exactly one, at every place.
14. **Invisibility of positive integer-successor carriers** (`negIndex_add_slope_of_integer_successor`,
   `negIndex_add_slope_eq_top_of_weil_dilation`): `κ(p + ψ ∘ slope) = κ(ψ)`, and `∞` with Weil's
   dilation part.

---

## 6. Traps

| Trap | Truth |
|---|---|
| Successor coordinates are free | Only at index zero; the regular extension costs `[G : H]` copies of every negative square (`negIndex_extendFromSubgroup`) |
| An indefinite carrier escapes APD's positive no-gos | A Hecke-supported Pontryagin state is positive (`isPosDefOnGroup_of_isHeckeSupported`) |
| The integer successor forbids a finite nonzero index | It does not: `haarOneNegativeSquare` has index one, outside Hecke support |
| Weil's correlation and the Haar successor meet at finite index | Not within Hecke support (`negIndex_eq_top_of_weil_haarSuccessor`), nor for any slope correction of a positive Hecke-supported state (`negIndex_eq_top_of_weil_slope_add`); beyond that, open |
| A slope correction can repair the Haar state's dilation reading | Only by keeping it discontinuous at `1` (`negIndex_slope_add_eq_top`) |
| The Kakutani wall is a gradual change of index | It is a jump `0 → ∞` (`negIndex_heckeState`) |
| A decaying state can carry a few negative squares | Mixing kills them (`negIndex_eq_zero_or_top_of_mixing`) |
| Local positivity glues positively | Conditionally positive local pieces glue with one negative square (`negIndex_negLogHeight`) |
| Local polar indices add exactly | Up to one gluing square, carried by the pole (`negIndex_separable_le_polarIndex_sum_add_one`) |
| Conformal Frobenius has a positive analogue | Positive states admit no conformal symmetry (`eq_zero_of_conformal_of_isPosDefKernel`) |
| Conformal symmetry separates `ℤ` from `𝔽_q` | The index-one conformal successor exists on both (`negIndex_negPow`, `negIndex_negAbsInf`); only the factor set differs |
| A conformal successor can have any index | Exponent one: only `0`, `1`, `∞` (`negIndex_mul_absRat`) |
| Support or decay laws select `ζ` | They are twin-blind (`negIndex_mul_unitaryChar`) |
| The matched local Hodge indices assemble on `ℚ_{>0}` | Every fixed counterterm leaves infinitely many squares (`negIndex_counterterm_sub_primeLatticeKernel`) |
| The adelic product of the two readings is a new carrier | It is Hecke-supported: index `0` or `∞` (`negIndex_adelicWeilState_eq_zero_or_top`) |
| Finite index on `Aff(ℚ)` is a positive state plus slope data | The Haar mixed quadratic state is not (`haarMixedQuadraticState_not_positive_add_slope`); the pole–successor's negative square couples slope and shift |
| The boost and the conformal factor act on different objects | They are the two readings of one index-one state (`negIndex_poleSuccessorState`) |
| The Hecke normalization `|u|^{1/2}` is a convention | It is forced: the boost exponent is half the exponent of `−|b|` (`poleSuccessor_dilation`) |
| Only the archimedean place carries a negative square | Every `p`-adic place carries an index-one pole–successor state (`negIndex_padicPoleSuccessor`) |
| A new RH equivalence is progress | A contribution computes, bounds or excludes an index |

---

## 7. Questions

1. **Is there a signature formula `κ(K_ζ) = Σ_p (local defect) − (archimedean gluing)`?**
   *Answered for separable assemblies*: `κ = Σ_p κ₀(k_p) + ε`, `ε ∈ {0, 1}`, with the pole as the only
   gluing direction (Pillar 5). Tower-supported assemblies have index `0` or `∞` (AKL); separable ones
   have the sum formula; on the gauge torus the two are dual (inference: axis support on `⊕_p ℤ` is
   separability of the spectral density, as for the Euler log-derivative). The local signature of
   the pole is `1` at every place: each `v` carries an index-one pole–successor state (Pillar 13).
   *Open*: the Weil kernel is neither tower-supported nor separable; its archimedean part is
   continuous in `log a` and couples all axes.
2. **Do the matched local Hodge indices share one positive direction for every finite sieve?**
   *Yes*, uniformly in the sieve (`RenormalizedArithmeticPotentialTheory.eventually_sieveHodgeGram_one_positive_direction`).
   The scalar counterterm `log N − γ` plays the shared pole, as in Pillar 5. *What obstructs the
   infinite assembly*: the counterterm runs. On the whole Hecke lattice `D·δ₁ − P` has infinite index
   for every fixed `D` (Pillar 8), so the assembly has no Pontryagin limit at fixed renormalization;
   the archimedean place must supply a counterterm growing like `log N`. *Open*: the transfer to the
   complete form, where the counterterm is the archimedean operator, which is not separable.
3. **Is there a Pontryagin state with Weil's dilation part and the Haar successor at the critical
   temperature, and is its index `κ(K_ζ)`?** *Within Hecke support: no*; such a state has infinite
   index, unconditionally (`negIndex_eq_top_of_weil_haarSuccessor`). The least index of any affine
   extension is `κ(K_ζ)`, attained by the blind extension (`negIndex_blindWeilState`). Outside Hecke
   support the integer successor admits index one (`negIndex_haarOneNegativeSquare`), but that
   state's dilation reading is discontinuous at `1`, and this is forced: every slope correction `s(|a|) + ψ` of a positive Hecke-supported state `ψ` with
   the integer successor has infinite index once its dilation part is continuous at `1`
   (`negIndex_slope_add_eq_top`), so Weil's correlation is excluded on the whole class
   (`negIndex_eq_top_of_weil_slope_add`). The mechanism is the near coincidence of the two
   topologies: rationals near `1` have large denominators (`negIndex_sub_eq_top`). The Hecke support
   of the positive part is not needed: every positive carrier with the integer successor is
   invisible to the index, and Weil's dilation part then costs infinitely many squares
   (`negIndex_add_slope_eq_top_of_weil_dilation`). Kernels vanishing on both axes leave both readings
   unchanged and are finite-dimensional (`rank_gram_le_square_of_zero_axes`). *Open*: states whose
   negative squares couple slope and shift in infinite rank (the general indefinite Mautner
   theorem).
4. **What replaces conformal Frobenius over `ℤ`?** No positive state is conformal; a conformal
   successor of exponent one has finite index only as `−c|b|`, `c > 0`, with exactly one negative
   square, and the dilation by `u` acts on it with factor `|u|` (Pillar 6). Every exponent
   `0 < s < 1` gives an index-one successor `−|m|^s` with factor `|u|^s` (`negIndex_negPow`); at
   `s = 1/2` the factor is the Hecke normalization `|u|^{1/2}`. Calibration: over `𝔽_q[T]` the
   index-one successor `−|·|_∞` is conformal for `X` with factor exactly `q` (`negIndex_negAbsInf`,
   `absInf_X_mul`). So the conformal part of Frobenius lives on the additive side with one negative
   square, and the boost on the multiplicative side (ALG). *Answered*: the two are one state. The
   pole–successor state `|a|^{1/2} + |a|^{−1/2} − c|a|^{−1/2}|b|` has index one
   (`negIndex_poleSuccessorState`); on `×` it is the Hecke boost, on `+` the conformal successor, and
   the dilations act on the additive point vectors with the Hecke factor `|u|^{−1/2}`. The boost
   exponent is half the conformal exponent (`negIndex_poleSuccessor`), and every place carries such
   a state (`negIndex_padicPoleSuccessor`). The substitute for conformal Frobenius over `ℤ` is this
   hyperbolic pair at the fixed points `0, ∞` of `ℙ¹(ℚ)`. Calibration: over `𝔽_q(T)` the same
   state at the place at infinity has index one with boost `q^{±1/2}` under `X`
   (`negIndex_inftyPoleSuccessor`, `inftyPoleSuccessor_dilation_X`), the eigenvalues of Frobenius on
   `H⁰` and `H²` after the Hecke twist.
5. **Is there an integer invariant on the additive side equal to the number of off-line zeros?**
   *Partial.* On the additive side the index is exactly a count of negative conductor coefficients at
   every finite level (`negIndex_zmod_eq_card`), so such an invariant would be a count of negative
   conductor modes. No decaying additive state, no Hecke-supported or height-decaying affine state,
   and not the adelic product state of the two readings can carry a finite nonzero number of squares
   (Pillars 2–3, `negIndex_adelicWeilState_eq_zero_or_top`). The surviving candidate is the heat
   collision charge (`ArithmeticOrientationGeometry.TheIndexExit`, AKL `waveNumber_collision_law`), a
   time-direction carrier. Conformal induction transports any additive count to the affine group
   unchanged (`negIndex_conformalInduction`). *Open*: its theta-prefix reading.
6. **Is there an exact sum-of-squares decomposition of the complete Weil form indexed by
   successor-agreement shells?** *Open.* AKG supplies the model mechanisms: axis orthogonality on
   mean-zero blocks (`hermQuad_gram_axes`) and the tail-sum identity for `−|m|`
   (`hermQuad_gram_negAbsKernel_eq`).

---

## 8. Tools

| Tool | Built | Open |
|---|---|---|
| Pontryagin index theory on groups | induction formula, witness complements, escape, approximate escape, block additivity, twist invariance, conformal induction, Krein compressions (`Wᴴ h W`) | Krein–Langer structure on `Aff(ℚ)` in infinite rank |
| Local–global signature calculus | polar index, separable signature formula, matched counterterms as the gluing square, the pole–successor law at every place | non-separable glue; the archimedean operator; a restricted product of local states |
| Kakutani–Hellinger dichotomies | the measure dichotomy is APD's (`heckeState_kakutani_wall`); AKG adds the index wall and its twin-blindness | local Hellinger affinities at each prime |
| Mautner/Howe–Moore phenomena | indefinite Howe–Moore: mixing and height decay kill negative squares; near coincidence and dilution; invisibility of positive integer-successor carriers; axis-invisible kernels (degree and rank laws) | indefinite Mautner in infinite rank |
| Bost–Connes/KMS at the critical temperature | Hecke states at every exponent, Haar state | BC states below `β = 1` |
| Ramanujan Plancherel on `ℤ̂`, conductor Hamiltonian | the additive index law on `ℤ/N` and `ℚ/ℤ`; the Ramanujan index law `κ = Σ_{A_d < 0} φ(d)`; conductor energies: CACT | the spectral measure on `ℤ̂` itself |
| Successor-shell calculus | — (corpus: SSH) | shell sum-of-squares (Q6) |
| Lyapunov methods for the dBN flow | — (corpus: `RHTower/Heat`, localized flux) | a global functional |
| Linear independence of logarithms | — (corpus: friable Vandermonde) | quantitative bounds in the pre-ergodic regime |

---

## 9. Open research topics

1. **Indefinite Mautner theorem**: finite index, integer successor and a dilation part continuous at
   `1`. Positive case: APD; positive integer-successor carriers plus slope data: excluded
   (`negIndex_add_slope_eq_top_of_continuous_dilation`); axis-invisible additions are of finite rank.
   Open: states whose negative part is not of finite rank modulo slope data.
2. **Krein–Langer structure on `Aff(ℚ)`**: finite index does not force positive part plus slope data
   (`haarMixedQuadraticState_not_positive_add_slope`, the pole–successor states). Open: is every
   Pontryagin state a positive state plus a coefficient of a finite-dimensional or
   conformally induced Pontryagin representation (the Borel's `Sym^d`, `−|b|_v^s`)?
3. **Non-separable gluing**: a signature formula with the archimedean operator in place of a scalar
   counterterm, tested first on the complete atomic Weil matrix at fixed overlap.
4. **Weil's dilation data on a pole–successor carrier**: the pole pair is glued to `−|b|`; glue the
   prime and archimedean parts of Weil's kernel to successors in the same way, place by place, and
   compute the index of the result.
5. **Calibration over `𝔽_q(T)`**: the Hecke states of `Aff(𝔽_q(T))` and their wall (the conformal
   successor and the pole–successor state are calibrated: `negIndex_negAbsInf`,
   `negIndex_inftyPoleSuccessor`).
6. **Additive carriers of the collision charge** (Q5).
7. **Shell sum-of-squares** (Q6).

---

## 10. Success criteria and contributions

**The field is real, not a reformulation, when it has** (criteria of the field assessment, with
status):

1. intrinsic objects defined from `ℤ` without zeros — Hecke support, height, polar index, separable
   assemblies, conformal successors;
2. a local signature theorem at each prime and a global gluing theorem — finite sieves (RAPT) and
   the separable formula; the Weil kernel open;
3. an additive–multiplicative comparison theorem proved as an identity — for the pole: the boost
   coordinate is the total mass of the additive weights (`hermQuad_gram_poleSuccessor`); for Weil's
   full kernel open;
4. a conformal symmetry with factor `≠ 1`, or a proof that none exists and its substitute — none on
   positive states; the substitute is the index-one pole–successor state, boost on `×` and conformal
   successor on `+` (`negIndex_poleSuccessorState`);
5. calibration over `𝔽_q[T]` — the conformal successor (`negIndex_negAbsInf`, factor `q`), the
   pole–successor state of `𝔽_q(T)` at infinity with boost `q^{±1/2}` (`negIndex_inftyPoleSuccessor`),
   the local states at every place of `ℚ` (`negIndex_padicPoleSuccessor`); the Kakutani wall over
   `𝔽_q(T)` open;
6. selectivity — the index laws are twin-blind (theorem), so selectivity must come from the dilation
   data;
7. edge control — the renormalized limit of the matched prime kernel has no Pontryagin realization at
   a fixed counterterm (`negIndex_counterterm_sub_primeLatticeKernel`); the running counterterm is
   forced; a nontrivial null cone in the limit is open.

**A contribution** is an unconditional theorem about Hermitian forms of finite negative index on a
stated group or assembly. It names its local data and its glue; computes, bounds or excludes an
index (not a new RH equivalence); says what it gives for the twins and over `𝔽_q`; and records the
positive survivor of every no-go.

**Principles.** Index before sign. Support and decay decide type. Localize, then glue at the pole.
Indefiniteness is spent, not assumed: every negative square needs a carrier that escapes nothing.
A reformulation is not a reduction.
