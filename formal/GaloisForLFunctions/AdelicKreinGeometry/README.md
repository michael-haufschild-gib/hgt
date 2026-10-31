# Adelic Krein Geometry (AKG)

**Arithmetic signature theory: indefinite harmonic analysis on the dilation–translation system of `ℚ`.**

Namespace `GaloisForLFunctions.AdelicKreinGeometry`; umbrella `AdelicKreinGeometry.lean`. Haar successors,
period defects and cyclic projections belong in `Haar/`. Index laws are unconditional; RH assumptions
in positivity corollaries are explicit.

> **The question.** Which Hermitian forms of finite negative index live on the dilation–translation system
> `ℚ^×_{>0} ⋉ 𝔸 ⊃ Aff⁺(ℚ)` and on its places? How is their index computed from local constituents glued at
> the archimedean place, and how do their additive readings (successor, Haar, theta) compare with their
> multiplicative readings (dilation, Euler, Mellin)?

The basic object is a **Pontryagin state**: a Hermitian function `φ` on a group, `φ(g⁻¹) = conj φ(g)`, whose
Gram matrices `(φ(x_a⁻¹x_b))` have a bounded number of negative eigenvalues; the bound is its **index** `κ(φ)`.
Positivity is the case `κ = 0`. AKG replaces the search for a positive object by an index calculation.

---

## 1. Why this field

**The diagnosis.** Every open problem of the corpus asks to pay an infinite-rank arithmetic debt through one
rank-one channel, the archimedean place, at zero margin and at the exponent `1/2`. A crossing input must be
critical, square-root precise and selective at once; all coupling between primes, and between addition and
multiplication, passes through the archimedean place (`docs/reports/review-3010/obstacles-summary.md`).

**Existing fields supply two features each.**

| Field | Supplies | Lacks |
|---|---|---|
| Hodge theory | an index theorem at zero margin | finite rank, a conformal Frobenius |
| Harmonic analysis on groups | Plancherel positivity | `+` and `×` separately; on `Aff(ℚ)` the two are spectrally singular |
| Krein / Pontryagin spaces | exact negative indices, finite-rank perturbations | arithmetic producers of the index |
| Probability on the gauge torus | Kakutani dichotomies, zero–one laws | statements at the trivial point |
| Analytic number theory | precision | estimates that spend a margin |

**What the missing field must contain.** Indefinite structures, because positive states on `Aff(ℚ)` cannot carry
Weil's correlation with a visible successor (APD: the successor is blind). A local-to-global signature theory with
the archimedean place as the glue. A conformal symmetry or its substitute: Hecke dilations are isometric boosts,
power maps and the successor are not conformal (ALG). Access to both readings at the same point. Renormalization
at edges with a counterterm of nontrivial null cone.

**Hence AKG is**

- *indefinite*: the index replaces positivity; the index of a natural arithmetic state is computed, bounded or
  shown to be `0` or `∞`;
- *affine*: both ring operations act, translations and dilations in `x ↦ ax + b`;
- *adelic*: local constituents at every place, `p`-adic and archimedean, are glued at `∞`.

---

## 2. What AKG establishes

1. **Support and decay decide type.** Escape (exact by Hecke support, approximate by mixing or height decay)
   forces `κ ∈ {0, ∞}`. The Kakutani wall of the Hecke states is an index jump `0 → ∞` at `s = 1/2`.
2. **The integer successor and continuous dilation data never meet at finite index.** Every Hermitian kernel on
   `Aff(ℚ)` with the integer (Haar) successor and a dilation reading continuous at `1` has infinite index; Weil's
   correlation is such a dilation reading. The mechanisms are the near coincidence of the two topologies
   (rationals near `1` have large denominators), Haar averaging over rational translates, and polynomial
   corrections with zero axis readings.
3. **The pole carries a finite nonzero index.** The pole pair `|u|^{1/2} + |u|^{−1/2}` of Weil's kernel extends to
   an index-one state of the whole affine group whose successor is `2 − c|b|`. It is the hyperbolic pair of the
   fixed points `0, ∞` of `ℙ¹(ℚ)`: a boost on `×` glued to a conformal successor on `+`, with the boost exponent
   half the conformal exponent. This is the substitute for conformal Frobenius over `ℤ`.
4. **Every place carries such a state, and its signature formula is exact.** For every conformal successor `ψ` at
   every place of every field, `κ = κ₀(ψ) + 1`: the polar index of the successor plus the pole's square. Poles at
   different places add; a shared pole (separable assemblies) adds at most one square.
5. **The archimedean place glues by a hyperplane.** Dilation data `K` glued to the archimedean successor have
   index `κ^{(½)}(K) + 1`, where `κ^{(½)}` counts the negative squares of `K` orthogonal to the boost character
   `u^{−1/2}`. The hyperplane is free for prime towers and for data that grow slower than the boost.
6. **Weil's archimedean state counts the zeros.** `κ(ratCorr(|a|) − c|a|^{−1/2}|b|) = #{zeros of ζ right of the
   critical line} + 1`, unconditionally, and likewise for every primitive Dirichlet `L(s, χ)`. Weil's dilation data
   are carried at finite index when glued at `∞`, never when glued at the integers.
7. **The additive side counts exactly.** On `ℤ/N` the index is the number of negative Fourier coefficients; a
   negative Ramanujan coefficient of conductor `d` costs `φ(d)` squares; on `ℚ/ℤ` the index is the supremum over
   levels.
8. **The index is twin-blind.** Unitary slope twists are Gram congruences; selectivity must come from the dilation
   data, which the archimedean states read zero by zero.

---

## 3. Objects

| Object | Meaning | Lean |
|---|---|---|
| Pontryagin state, index | Hermitian `φ` on a group, `κ(φ) = sup ν(gram φ x)` | `negIndex`, `IsHermKernel`, `gram` (HKT) |
| Witness family | a finite family attaining `κ` | `IsWitness` |
| Affine group | `x ↦ ax + b` over `ℚ` or any field `K` | `AffineGroupQ` (APD), `AffineGroupOf`, `slopeOf`, `shiftOf` |
| Readings | dilation reading `u ↦ φ(x ↦ ux)`, successor `b ↦ φ(x ↦ x + b)` | `dilation`, `translation`, `dilationOf`, `translationOf` |
| Hecke support | `φ(ax + b) ≠ 0 ⇒ den(a)·b ∈ ℤ` | `IsHeckeSupported` |
| Hecke and Haar states | `(nd)^{−s}·1[db ∈ ℤ]`; the case `s = 1/2` | `heckeState`, `haarState`, `HasIntegerSuccessor` (APD) |
| Height decay | decay in `|num a|·den a` | `HasHeightDecay`, `slopeHeight` |
| Weil's correlation | dilation correlation `ratCorr = K_ζ` on `ℚ_{>0}` | `ratCorr`, `zetaKernel` |
| Blind / regular extension | `ratCorr(|a|)`; extension by zero off the dilations | `blindWeilState`, `regularWeilState` |
| Polar index | negative squares on mean-zero vectors, `κ₀ ≤ κ ≤ κ₀ + 1` | `polarIndex`, `totalMass` |
| Separable assembly | `Σ_p k_p(g_p)` on `Π_p H_p` | `separable`, `axisFamily` |
| Prime lattice kernel | Weil's prime kernel `Λ(u)u^{−1/2}` with counterterm `D·δ₁` | `primeLatticeKernel`, `countertermKernel` |
| Conformal successor | `ψ(ub) = |u|_v^s ψ(b)` at a place `v` | `IsConformal`; `negAbsRat`, `negPowRat`, `negUltra`, `negAbsInf` |
| Boost pair, point vectors | `|a|_v^{±s/2}` at the fixed points `0, ∞`; vectors `k_t`, `k_∞` of `ℙ¹` | `slopePow`, `boostChar` |
| Conformal induction | `|a|_v^{−s/2}ψ(b)`, the coefficient of `k_0` | `conformalInduction` |
| Pole–successor state | boost pair plus conformal induction, the coefficient of `k_0 + k_∞` | `poleSuccessor`, `poleState` |
| Places | real, `p`-adic, `∞` of `F(X)` | `Rat.AbsoluteValue.real`, `Rat.AbsoluteValue.padic`, `inftyAbs`, `IsUltra` |
| Boost coordinate, boost-polar index | `ℓ(w) = Σ w_i u_i^{−1/2}`; negative squares of `K` on `ℓ = 0` | `boostMassU`, `boostPolarIndex` |
| Archimedean gluing | `K(|a|) − c|a|^{−1/2}|b|`; for `K = ratCorr` the archimedean Weil state | `archGlue`, `weilArchState` |
| Orbit kernel of a zero configuration | `K_f(u) = W_Z(f, f(· − log u))` | `orbitCorr`, `orbitKernel` (HKT) |
| Conductor data | Fourier and Ramanujan coefficients on `ℤ/N`, level kernels on `ℚ/ℤ` | `fourierCoeff`, `ramanujanCoeff`, `levelKernel` |
| Agreement shells | balls `|x − y|_v ≤ r`; half-lines `(−∞, t)` at `∞` | `ballOf`, `shellSquares`, `tailSum` |
| Unitary twist | `φ·χ(slope)` | `slopeChar` |
| Haar carriers | Haar state plus slope, log-slope or axis-invisible corrections | `haarOneNegativeSquare`, `haarMixedPowerState` |
| Axis-invisible kernel | zero on every translation and every dilation | `mixedPowerKernel`, `kernelColumnSpan` |
| Period defects | `col(b + 1) − col(b)` and its affine orbit | `translationPeriodDefect`, `affinePeriodSpace` |

---

## 4. Language

- **Type** of a state: `κ ∈ {0, ∞}` (escaping) or finite nonzero (Pontryagin proper).
- **Escape**: a translate `t` with `φ(x_a⁻¹ t y_b) = 0` for given finite families; *approximate escape* along a
  sequence; *mixing*: one sequence escaping every two-sided translate.
- **Near coincidence**: a rational `q ≠ 1` has denominator at least `1/|q − 1|`.
- **Blind extension**: pullback along `g ↦ |slope g|`; its successor is constant. **Regular extension**: zero off
  a subgroup.
- **Gluing square**: the at most one square that a shared constant (pole) direction adds to local polar indices.
- **Boost**: a dilation acting with eigenvalues `|a|^{∓s/2}`; **conformal factor**: `λ` with `φ ∘ α = λφ`.
- **Pole–successor state**: the coefficient of `k_0 + k_∞`; it carries one negative square at every place.
- **Boost hyperplane**: `ℓ = 0`, where the archimedean successor sees no mass; **sub-boost data**: data growing
  slower than `u^{1/2}`.
- **Agreement shell**: a class of points agreeing to radius `r`; **running counterterm**: a counterterm growing
  with the cutoff (`log N − γ` for the prime kernel, `cR` for the shell forms).
- **Axis readings**: the restrictions to translations and to dilations; **axis-invisible**: both vanish.
- **Twin**: the product of a state with a unitary character of its slope.

---

## 5. Mechanisms

**A. Index calculus on groups.**

- *Induction.* Pullback along a surjection keeps `κ`; restriction never raises it; orthogonal translates carry one
  copy of a negative subspace per coset, so `κ(ext₀ψ) = [G : H]·κ(ψ)` (`TheIndexOfAnInducedState`).
- *Witness complements.* A vector orthogonal to a witness family has nonnegative form; translating a family into
  the complement keeps its Gram matrix, so escape forces a finite index to vanish
  (`TheWitnessComplementIsPositive`).
- *Mixing.* Block additivity and lower semicontinuity of the index turn approximate escape into `κ ∈ {0, ∞}`
  (`MixingKillsNegativeSquares`).
- *Twist invariance.* `χ(x_a⁻¹x_b) = conj χ(x_a)χ(x_b)`: a unitary twist is a diagonal congruence
  (`TheIndexIsTwinBlind`).

**B. Arithmetic escape and incompatibility.**

- *Hecke escape.* Translation by `1/P`, `P` a prime above all denominators, escapes every Hecke-supported state;
  hence the affine zero-or-infinity law and the index wall (`HeckeSupportedStatesHaveIndexZeroOrInfinity`).
- *Height decay.* The slope height is submultiplicative; doubling dilations escape height-decaying states.
- *Running counterterm.* Translation by a product of two new primes escapes the prime lattice kernel, and the
  truncated pole vector beats any fixed counterterm (`NoFixedCountertermMakesThePrimeKernelPontryagin`).
- *Near coincidence and dilution.* A state continuous at `1` minus one decaying with the denominator has infinite
  index; spreading over `x + j/P` removes Hecke-supported parts (`ArchimedeanContinuityAgainstHeightDecay`).
- *Haar averaging and polynomial correction.* Rational translates average a positive integer-successor carrier to
  zero, so it is invisible to the index. For an arbitrary finite-index kernel with the integer successor, the
  translation-period defects span an isotropic space of dimension at most `κ²`; its polynomial primitive has zero
  axis readings, and subtracting it restores integer invariance on both sides. Cyclic orbits of dilation columns
  then make fixed projections tend to `J − I` under continuous dilations, which has unbounded negative index
  (`Haar/`).

**C. The additive side.**

- *Fourier.* On `ℤ/N` the Gram form is `Σ_ξ a_ξ|Σ_b c_b e(y_bξ/N)|²`; unit invariance makes `a_ξ` constant on
  conductor classes of size `φ(d)`; on `ℚ/ℤ` every family lives at one level (`TheAdditiveIndexLaw`,
  `TheAdditiveIndexLawOnQModZ`, `TheRamanujanIndexLaw`).
- *Conditional positivity.* `−|m|` is a sum of tail squares; `−|m|^s` by Poisson subordination
  `|m|^s = I_s(|m|)/I_s(1)`; `−|b|_v` for nonarchimedean `v` by ball subgroups and the layer cake
  `R − t = ∫_0^R 1[t ≤ r] dr`; `−|·|_∞` on `F[X]` by high parts (`TheSignatureOfASeparableAssembly`,
  `StableConformalSuccessors`, `EveryPlaceCarriesAPoleSuccessorState`, `TheFunctionFieldConformalSuccessor`).

**D. Conformal structure and the pole.**

- *No positive conformal symmetry.* Endomorphisms fix the identity, so a positive state with factor `λ ≠ 1`
  vanishes; `−|b|` is conformal with one negative square (`ConformalSymmetryNeedsANegativeSquare`).
- *Point vectors.* `[k_s, k_t] = ψ(t − s)`, `[k_∞, k_t] = 1`, `[k_∞, k_∞] = 0`; `x ↦ ax + b` acts by
  `k_t ↦ |a|^{−s/2}k_{at+b}`, `k_∞ ↦ |a|^{s/2}k_∞`. The Gram form of the pole–successor state is `2Re(X̄Y)` plus the
  form of `ψ` at weights of total mass `X = Σ w_g|a_g|^{−s/2}`
  (`TheHeckeBoostAndTheConformalSuccessorAreOneState`).
- *The Borel model.* The positive affine maps sit in `SL(2, ℝ)`, which preserves a form of signature `(1, 1)`;
  the coefficient at `(1, −i)` is the pole state (`ThePoleIsAKreinStateOfTheAffineGroup`).
- *Exact signature.* On `X = 0` only the polar form of `ψ` remains; a polar negative subspace on translations and
  the boost pair on dilations `u^N, u^{N+1}` decouple as `N → ∞` (`ThePoleSuccessorSignatureFormula`).
- *Distinct places.* Each boost pair is the pair kernel of its boost character; a unit separating the characters
  gives one square per place (`LocalSignaturesAddOverDistinctPlaces`).
- *Shells.* Equivalence kernels are sums of squares of class sums, so the local pole–successor form is a hyperbolic
  pair renormalized by a running counterterm plus shell squares (`TheShellDecompositionOfAPoleSuccessorForm`).

**E. Gluing at the archimedean place.**

- *The boost hyperplane.* The successor's form is nonnegative on `ℓ = 0`; a negative subspace of `K` on `ℓ = 0`
  decouples from the pair `1, x ↦ x + L` because the successor cross terms are `ψ(±L)·ℓ = 0`
  (`TheArchimedeanGluingFormula`).
- *Free hyperplanes.* A negative family dilated by `λ` and corrected at the slope `1` by `−λ^{−1/2}ℓ` lies on
  `ℓ = 0` and tends to the original family when the data are sub-boost; for data periodic under `v₀ ≠ 1` the family
  `F ⊔ v₀F` with weights `c, −v₀^{1/2}c` does it exactly (`PrimeTowersGlueAtFullIndex`).
- *Zeros against the boost.* On the zero side `K_f(u) = Σ_ρ u^{1/2−ρ}w_ρ` with summable weights;
  `u^{−1/2}|u^{1/2−ρ}| = u^{−Re ρ}` and `Re ρ > 0`, so dominated convergence makes `K_f` sub-boost
  (`WeilsArchimedeanStateCountsTheZeros`).

---

## 6. Pillar theorems

| Theorem | Lean |
|---|---|
| Induction formula `κ(ext₀ψ) = [G : H]·κ(ψ)`; blind extensions are index-minimal | `negIndex_extendFromSubgroup`, `negIndex_comp_retraction` |
| Escape, mixing and height decay force `κ ∈ {0, ∞}` | `negIndex_eq_zero_or_top_of_escape`, `negIndex_eq_zero_or_top_of_mixing`, `negIndex_eq_zero_or_top_of_heightDecay` |
| Affine zero-or-infinity law; the Kakutani wall is an index wall | `negIndex_eq_zero_or_top_of_isHeckeSupported`, `negIndex_heckeState` |
| Weil's affine extensions: minimum `κ(K_ζ)`; Hecke support with the Haar successor costs `∞` | `negIndex_blindWeilState`, `negIndex_eq_top_of_weil_haarSuccessor` |
| **Every nonzero integer-Haar multiple with a continuous dilation reading has infinite index** (every Hermitian kernel) | `negIndex_eq_top_of_nonzero_haar_continuous_dilation` |
| Positive integer-successor carriers are invisible: `κ(p + ψ ∘ slope) = κ(ψ)` | `negIndex_add_slope_of_integer_successor` |
| Period defects of an integer successor of index `r` span at most `r²` dimensions | `finite_affinePeriodSpace_of_integerSuccessor` |
| No fixed counterterm makes the prime kernel Pontryagin | `negIndex_counterterm_sub_primeLatticeKernel` |
| Separable signature formula `Σκ₀ ≤ κ ≤ Σκ₀ + 1` | `polarIndex_sum_le_negIndex_separable`, `negIndex_separable_le_polarIndex_sum_add_one` |
| Additive and Ramanujan index laws | `negIndex_zmod_eq_card`, `negIndex_zmod_eq_sum_totient`, `negIndex_eq_iSup_card_negCoeffs` |
| Conformal symmetry needs exactly one negative square; `κ(c|b|) ∈ {0, 1, ∞}` | `eq_zero_of_conformal_of_isPosDefKernel`, `negIndex_mul_absRat`, `negIndex_negPow` |
| Conformal induction keeps the index | `negIndex_conformalInduction` |
| **Pole–successor signature formula** `κ = κ₀(ψ) + 1` at every place of every field | `negIndex_poleSuccessor_eq`, `negIndex_padicPoleSuccessor`, `negIndex_inftyPoleSuccessor` |
| Distinct places add: `κ(Φ_∞ + Φ_p) = 2` | `negIndex_placeAssembly_eq`, `negIndex_real_add_padic` |
| **Archimedean gluing formula** `κ(K(|a|) − c|a|^{−1/2}|b|) = κ^{(½)}(K) + 1`; prime towers give `κ(k) + 1` | `negIndex_archGlue_eq`, `negIndex_archGlue_eq_of_subBoost`, `negIndex_archGlue_tower` |
| **Weil's archimedean state counts the zeros**; also every Dirichlet `L(s, χ)` | `negIndex_weilArchState_eq_rightZeros`, `negIndex_archGlue_orbitCorr`, `negIndex_archGlue_dirichlet` |
| Shell decomposition of the local pole–successor forms | `hermQuad_gram_poleSuccessor_negUltra_eq`, `hermQuad_gram_poleSuccessorState_eq` |
| Axis-invisible kernels: zero or `κ ≥ 2`, rank `≤ κ²`, polynomial fibres of degree `< κ`; every `κ ≥ 2` occurs | `two_le_negIndex_of_zero_axes`, `rank_gram_le_square_of_zero_axes`, `negIndex_haarMixedPowerState` |
| The index is twin-blind | `negIndex_mul_unitaryChar`, `negIndex_heckeState_mul_slopeChar` |

---

## 7. Questions

1. **Is there a signature formula `κ(K_ζ) = Σ_p (local defect) − (archimedean gluing)`?**
   *Answered for the glue.* Local constituents sharing the pole glue with at most one square (separable
   assemblies); a conformal successor glues to its pole with exactly one (`κ₀ + 1`); distinct places add; the
   archimedean place glues dilation data by the boost hyperplane, `κ^{(½)}(K) + 1`, and for prime towers and for
   Weil's correlation the hyperplane is free, so the archimedean term is exactly one square. *Open*: the
   decomposition of `κ(K_ζ)` itself into prime defects; the Weil kernel is neither tower-supported nor separable.
2. **Do the matched local Hodge indices share one positive direction for every finite sieve, and what obstructs the
   infinite assembly?** *Yes*, uniformly in the sieve
   (`RenormalizedArithmeticPotentialTheory.eventually_sieveHodgeGram_one_positive_direction`); the counterterm
   `log N − γ` plays the shared pole. The obstruction is the running counterterm: at any fixed counterterm the
   prime kernel on `ℚ_{>0}` has infinite index.
3. **Is there a Pontryagin state whose dilation part is Weil's correlation and whose successor is the Haar state?
   Is its index `κ(K_ζ)`?** *No* for the Haar (integer) successor: every Hermitian kernel with the integer
   successor and a dilation reading continuous at `1` has infinite index. *Yes* for the archimedean successor:
   `ratCorr(|a|) − c|a|^{−1/2}|b|` has index `κ(K_ζ) + 1`. The second bridge between the towers is archimedean.
4. **What replaces conformal Frobenius over `ℤ`?** No positive state is conformal. The substitute is the
   pole–successor state: the hyperbolic pair at `0, ∞` of `ℙ¹`, a boost `|u|^{±1/2}` on `×` glued to the conformal
   successor `−|b|` on `+`, with one negative square. Over `𝔽_q(T)` the same state at `∞` has boost `q^{±1/2}`
   under `X`, the Frobenius eigenvalues on `H⁰` and `H²` after the Hecke twist.
5. **Is there an integer invariant computable on the additive side that equals the number of off-line zeros?**
   *Partial.* An affine invariant exists: the index of Weil's archimedean state minus one. On the additive side
   alone the index is a count of negative conductor coefficients, and decaying, Hecke-supported and
   height-decaying carriers have index `0` or `∞`. *Open*: a purely additive carrier (the collision charge, a
   Toeplitz Fredholm index).
6. **Is there an exact sum-of-squares decomposition of the complete Weil form indexed by successor-agreement
   shells?** *Answered for the local pole–successor forms*: a renormalized hyperbolic pair plus squares of shell
   sums over balls (at `p`) or half-lines (at `∞`). *Open* for the complete Weil form.

---

## 8. Tools

| Tool | Developed | To develop |
|---|---|---|
| Pontryagin index theory on groups | induction, witness complements, escape, mixing, block additivity, twist invariance, Krein compressions, conformal induction | Krein–Langer structure on `Aff(ℚ)` |
| Local–global signature calculus | polar index, separable formula, pole–successor formula, additivity over places, boost-polar index and archimedean gluing | prime-local defects of the Weil kernel; non-separable glue |
| Kakutani–Hellinger dichotomies | the Kakutani wall as an index wall; zero-or-infinity laws as index zero–one laws | local Hellinger affinities at each prime |
| Mautner / Howe–Moore phenomena | indefinite Howe–Moore (mixing, height decay, near coincidence, dilution, Haar averaging); infinite index for every Haar kernel with continuous dilations | uniqueness of the Haar decomposition |
| Bost–Connes / KMS at the critical temperature | Hecke states at every exponent and their index wall | states below `β = 1` |
| Ramanujan Plancherel, conductor Hamiltonian | additive index law on `ℤ/N`, `ℚ/ℤ`; Ramanujan law `Σ_{A_d<0} φ(d)` | the spectral measure on `ℤ̂` |
| Successor-shell calculus | shell decompositions at every place with running counterterms | shells of the complete Weil form |
| Lyapunov methods for the dBN flow | — (corpus: `RHTower/Heat`) | a link between heat counts and affine indices |
| Linear independence of logarithms | separating units for distinct places | quantitative bounds in the pre-ergodic regime |

---

## 9. Open research topics

1. **Prime-local defects.** Decompose `κ(K_ζ)` into contributions of the prime towers glued by the archimedean
   hyperplane, and compare them with the matched local Hodge indices.
2. **Krein–Langer structure on `Aff(ℚ)`.** Is every Pontryagin state a positive state plus coefficients of
   finite-dimensional or conformally induced Pontryagin representations? Known pieces: pole–successor states, the
   Borel's `Sym^d` (mixed power kernels), archimedean Weil states.
3. **The Haar decomposition.** Does every finite-index integer-Haar kernel decompose uniquely into a positive Haar
   kernel, a Hermitian slope kernel and a finite-rank polynomial kernel vanishing on both axes?
4. **Purely additive counters.** An index on the translations alone that equals the number of zeros right of the
   line, or a proof that none exists among natural classes.
5. **Calibration over `𝔽_q(T)`.** The Hecke states of `Aff(𝔽_q(T))` and their wall; the archimedean Weil state of
   a function field and its index.
6. **Shell identity for the Weil form.** Extend the local shell decomposition to the complete Weil form; the form
   of the archimedean Weil state is `K`'s form at the slopes plus the shell form at the shifts.
7. **Stable gluing.** At the successor `−|b|^s`, `0 < s < 1`, the hyperplane `Σ w_i u_i^{−s/2} = 0` is free when
   every zero has `Re ρ > (1 − s)/2`; determine what the index sees otherwise.

---

## 10. Traps

| Trap | Fact |
|---|---|
| Successor coordinates are free | only at index zero; the regular extension costs `[G : H]` copies of every square |
| An indefinite carrier escapes APD's positive no-gos | a Hecke-supported Pontryagin state is positive |
| The integer successor forbids a finite nonzero index | `haarOneNegativeSquare` has index one, with a discontinuous dilation reading |
| Some correction lets the integer successor carry continuous dilation data | never: every such Hermitian kernel has infinite index |
| The Kakutani wall is a gradual change of index | it is a jump `0 → ∞` |
| A decaying state can carry a few negative squares | mixing and height decay kill them |
| Local polar indices add exactly | up to one gluing square, carried by the shared pole |
| The successor can absorb the pole's square | never: `κ = κ₀(ψ) + 1` |
| Poles at different places glue like a shared pole | they add: `κ(Φ_∞ + Φ_p) = 2` |
| Conformal Frobenius has a positive analogue | positive states admit no conformal symmetry |
| The Hecke normalization `|u|^{1/2}` is a convention | it is the boost exponent of the archimedean successor `−|b|` |
| Gluing at the archimedean place costs an unknown amount | for towers and for Weil's correlation exactly one square |
| Index laws select `ζ` | they are twin-blind; only the dilation data select |
| The matched local Hodge indices assemble on `ℚ_{>0}` | every fixed counterterm leaves infinitely many squares |
| Finite index is a positive state plus slope data | the Haar mixed quadratic state and the pole–successor states are not |
| A new RH equivalence is progress | a contribution computes, bounds or excludes an index |

---

## 11. Place in the research

AKG is the indefinite counterpart of APD's affine positivity and the affine counterpart of the multiplicative index
theory of HKT and AKL. It is the field asked for in §2.6 of the obstacles review, and it addresses that review's
problems B8 (local-to-global signature) and B19 (a successor-carrying carrier) and its opportunities O2 (a Hasse
principle for the index) and O5 (a second bridge between the primes).

| Programme | What AKG uses | What AKG adds |
|---|---|---|
| ArithmeticPositiveDuality | positive states on `Aff(ℚ)`, Hecke and Haar states, the Kakutani measure dichotomy, Mautner rigidity | what finite negative index changes; the archimedean bridge |
| HeckeKreinToeplitz | `negIndex`, Gram calculus, hyperbolic pairs, `K_ζ` and its index, orbit kernels, column spaces | induction, escape and mixing on groups; Weil's affine extensions and archimedean states |
| ArithmeticKreinLangerTheory | zero-or-infinity for axis-supported kernels, twin-blind locality | the affine escape law; the separable signature formula |
| RenormalizedArithmeticPotentialTheory | the matched local Hodge index on finite sieves | the gluing formulas of which it is an instance; the running counterterm is forced |
| ArithmeticLorentzianGeometry | Frobenius is conformal, Hecke is a boost | boost and conformal successor are one state |
| ArithmeticCastelnuovoSeveri | finite-configuration Pontryagin law, tempered zero configurations | the archimedean gluing of Weil's data |
| ArithmeticOrientationGeometry | seen right zeros, the orientation index law | the zero count by an affine state |
| BiarithmeticGeometry | affine translation unipotence, polynomial coefficients | period defects and polynomial fibres of axis-invisible kernels |
| HilbertianExplicitFormulas, ArithmeticPolarization | explicit formulas read only Weil's form | the additive side as an index carrier |
| SuccessorShellArithmetic, CriticalArithmeticCorrelationTheory | successor shells, conductor energies | exact shell identities for the local forms |

---

## 12. Success criteria and contributions

**The field is real, not a reformulation, when it has** (criteria of §2.6, with status):

1. *intrinsic objects defined from `ℤ` without zeros*: Hecke support, height, polar and boost-polar indices,
   conformal successors, point vectors, agreement shells. Met.
2. *a local signature theorem at each place and a global gluing theorem*: the pole–successor formula at every
   place, additivity over places, the separable and archimedean gluing formulas. Met for the glue; the
   prime-local decomposition of `κ(K_ζ)` is open.
3. *an additive–multiplicative comparison proved as an identity*: the Gram identities of the pole–successor and
   archimedean states, and the index identity `κ = #{zeros right of the line} + 1`. Met for the archimedean
   comparison; `S = W` itself is not addressed.
4. *a conformal symmetry with factor `≠ 1`, or a proof that none exists and its substitute*: none on positive
   states; the substitute is the pole–successor state. Met.
5. *calibration over `𝔽_q[T]`*: the conformal successor and the pole–successor state at `∞` with boost `q^{±1/2}`.
   The Hecke wall over `𝔽_q(T)` is open.
6. *selectivity*: index laws are twin-blind; the archimedean states of different L-functions count their own
   zeros. Met at the level of dilation data.
7. *edge control*: running counterterms are forced (`log N − γ`) and exact in the local shell forms (`cR`). A
   nontrivial null cone in the limit of the Weil form is open.

**A contribution** is an unconditional theorem about Hermitian forms of finite negative index on a stated group,
assembly or place. It names its local data and its glue; computes, bounds or excludes an index, not merely an RH
equivalence; says what it gives for twins and over `𝔽_q`; and records the positive survivor of every no-go.

**Principles.** Index before sign. Support and decay decide type. Localize, then glue at the pole. A negative
square needs a carrier that escapes nothing. A reformulation is not a reduction.

---

## 13. Module map

- Index calculus: `TheIndexOfAnInducedState`, `TheWitnessComplementIsPositive`, `MixingKillsNegativeSquares`,
  `TheIndexIsTwinBlind`.
- Arithmetic types: `HeckeSupportedStatesHaveIndexZeroOrInfinity`, `ThePontryaginExtensionsOfWeilsCorrelation`,
  `TheAdelicProductState`, `NoFixedCountertermMakesThePrimeKernelPontryagin`,
  `ArchimedeanContinuityAgainstHeightDecay`.
- Signatures and the additive side: `TheSignatureOfASeparableAssembly`, `TheAdditiveIndexLaw`,
  `TheAdditiveIndexLawOnQModZ`, `TheRamanujanIndexLaw`.
- Conformal structure and places: `ConformalSymmetryNeedsANegativeSquare`, `StableConformalSuccessors`,
  `TheFunctionFieldConformalSuccessor`, `TheAffineGroupOfAField`, `ThePoleIsAKreinStateOfTheAffineGroup`,
  `TheHeckeBoostAndTheConformalSuccessorAreOneState`, `EveryPlaceCarriesAPoleSuccessorState`,
  `ThePoleSuccessorSignatureFormula`, `LocalSignaturesAddOverDistinctPlaces`,
  `TheShellDecompositionOfAPoleSuccessorForm`.
- Archimedean gluing: `WeilsCorrelationWithAnArchimedeanSuccessor`, `TheArchimedeanGluingFormula`,
  `PrimeTowersGlueAtFullIndex`, `WeilsArchimedeanStateCountsTheZeros`.
- Haar carriers (`Haar/`): `OneNegativeSquare`, `IndexPreservation`, `ContinuousDilationsNeedInfiniteIndex`,
  `MixedPolynomialPerturbation`, `AxisInvisibility`, `FiniteRankPerturbations`, `PolynomialPerturbations`,
  `PowerKernels`, `PeriodDefects`, `PolynomialCorrection`, `TranslationMovingPositivity`, `CyclicOrbits`,
  `CyclicHecke`, `CyclicGramLimit`, `FiniteIndexObstruction`, `ScaledHaarObstruction`,
  `PositiveAffineObstruction`.
