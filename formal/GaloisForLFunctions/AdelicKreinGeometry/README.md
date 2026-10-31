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
   forces `κ ∈ {0, ∞}`. The Kakutani wall of the Hecke states is an index jump `0 → ∞` at `s = 1/2`, and the wall
   is local: the Hecke state is the product of local states, one per prime, and each local state already jumps
   from `0` to `∞` at `s = 1/2`. Over `𝔽_q(X)` the local state at the place `∞` has the same wall, with `q` in the
   role of `p`.
2. **The integer successor and continuous dilation data never meet at finite index.** Every Hermitian kernel on
   `Aff(ℚ)` with the integer (Haar) successor and a dilation reading continuous at `1` has infinite index; Weil's
   correlation is such a dilation reading. The mechanisms are the near coincidence of the two topologies
   (rationals near `1` have large denominators), Haar averaging over rational translates, and polynomial
   corrections with zero axis readings. Every finite-index integer-Haar kernel has a unique split
   `k=p+ψ∘slope+Q`, with positive Haar `p`, Hermitian slope `ψ`, and finite-rank polynomial `Q` vanishing
   on both axes. Its exact index is `κ(k)=κ(ψ∘slope+Q)≥κ(ψ)`. Punctured dilation limits are exactly
   real `L≤0`, with minimum index zero at zero and one at every negative limit. For arbitrary subgroup
   successors `1_H`, finite-index continuous-dilation carriers exist exactly for `H={0}` or `H=ℚ`;
   both admit positive carriers.
3. **The pole carries a finite nonzero index.** The pole pair `|u|^{1/2} + |u|^{−1/2}` of Weil's kernel extends to
   an index-one state of the whole affine group whose successor is `2 − c|b|`. It is the hyperbolic pair of the
   fixed points `0, ∞` of `ℙ¹(ℚ)`: a boost on `×` glued to a conformal successor on `+`, with the boost exponent
   half the conformal exponent. This is the substitute for conformal Frobenius over `ℤ`.
4. **Every place carries such a state, and its signature formula is exact.** For every conformal successor `ψ` at
   every place of every field, `κ = κ₀(ψ) + 1`: the polar index of the successor plus the pole's square. Poles at
   different places add; a shared pole (separable assemblies) adds at most one square.
5. **The archimedean place glues by a hyperplane.** Dilation data `K` glued to the archimedean successor have
   index `κ^{(½)}(K) + 1`, where `κ^{(½)}` counts the negative squares of `K` orthogonal to the boost character
   `u^{−1/2}`. The hyperplane is free for prime towers and for data that grow slower than the boost. The gluing
   square is sharp: `κ(K) ≤ κ(glued) ≤ κ(K) + 1`, and both values occur. At every stable exponent `0 < s < 1`
   the same law holds for `K(|a|) − c|a|^{−s/2}|b|^s` with the boost `u^{−s/2}`; the pair the glue absorbs,
   `u^{±s/2}`, sits at `ρ = (1 ± s)/2` and is the pole pair `{0, 1}` exactly at the Hecke exponent `s = 1`. Every
   other real pair `u^{±s'/2}`, `s' ≠ s`, keeps its square: the glue detects exactly its own exponent.
6. **Weil's correlation glued at any place counts the zeros.** `κ(ratCorr(|a|) − c|a|^{−1/2}|b|) = #{zeros of ζ
   right of the critical line} + 1`, unconditionally, and likewise for every primitive Dirichlet `L(s, χ)`. The
   same count holds when Weil's correlation is glued to the `p`-adic successor `−c|a|_p^{−1/2}|b|_p` at any prime:
   the gluing formula holds at every place, and the zero count does not depend on the place of gluing. Weil's dilation data
   are carried at finite index when glued at `∞`, never when glued at the integers.
7. **The additive side counts exactly.** On `ℤ/N` the index is the number of negative Fourier coefficients; a
   negative Ramanujan coefficient of conductor `d` costs `φ(d)` squares; on `ℚ/ℤ` the index is the supremum over
   levels.
8. **The readings add, and the additive one is zero-blind.** The translation reading `K(1) − c|b|` of every glued
   state has exactly one square; the index of Weil's archimedean state is the index of its dilation reading
   (`#{zeros right of the line}`) plus that of its translation reading (`1`).
9. **The index is twin-blind.** Unitary slope twists are Gram congruences; selectivity must come from the dilation
   data, which the archimedean states read zero by zero.
10. **The glue selects by the order of the pole.** The boost hyperplane is the null direction of the simple pole
   pair: adding `u^{1/2} + u^{−1/2}` at any strength leaves the glued index unchanged. A double pole
   `log u·(u^{1/2} − u^{−1/2})` is not absorbed and costs a second square.
10. **The heat-deformed archimedean state is a source-defined Pontryagin homotopy.** From the Gaussian-weighted
    theta kernel `Φ_t(x) = Φ(x)e^{t x²}` of `H_t` alone (via tangent-disc Poisson–Jensen extraction on `D(−iR, R)`
    and Gaussian-damped contour integration on `Im z = ∓1`), `φ_c^{(t)} = archGlue(K_t, c)` is pointwise continuous
    in `t ∈ (0, ∞)` and satisfies `κ(φ_c^{(t)}) = #{nonreal right zeros of H_t with multiplicity} + 1 < ∞` for every
    `t > 0`, is lower semicontinuous and nonincreasing on `(0, ∞)`, equals `1` on `[1/8, ∞)`, and drops only at
    real-axis collisions by `⌊m_t(z)/2⌋` (one square per collided conjugate pair).

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
| Local Hecke state | `p^{−s|v_p(a)|}·1[v_p(b) ≥ min(0, v_p(a))]`: `aℤ_p + b` meets `ℤ_p` | `localHecke`, `slopeVal` |
| Local Hecke state at `∞` of `𝔽_q(X)` | `q^{−s|deg a|}·1[deg b ≤ max(0, deg a)]`: `aO_∞ + b` meets `O_∞` | `inftyHecke`, `slopeDeg`, `inftyCommKernel` |
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
| Gluing at a place | `K(|a|) + |a|_v^{−s/2}ψ(b)` for a gluing successor `ψ` (conformal, Hermitian, polar-positive, `Re ψ(1) < 0`); boost `ℓ_v = Σ w_i |u_i|_v^{−s/2}` | `glueAt`, `IsGluingSuccessor`, `placeMass`, `placePolarIndex`, `weilPadicState` |
| Jordan pair kernel | `P(log v)e^{−i u log v} + conj(P(−log v))e^{−i ū log v}` on `ℚ_{>0}` | `jordanPairKernel`, `jordanForward` |
| Heat-deformed archimedean state | `archGlue(heatDilationKernel t, c)` built from `Φ_t(x) = Φ(x)e^{t x²}` alone | `heatArchState`, `heatDilationKernel`, `heatCollisionPairs` |
| Simple and double pole pairs | `u^{1/2} + u^{−1/2}`; its `α`-derivative `log u·(u^{1/2} − u^{−1/2})` | `polePair`, `doublePole` |
| Stable gluing | `K(|a|) − c|a|^{−s/2}|b|^s`, boost `ℓ_s = Σ w_i u_i^{−s/2}`, index `κ^{(s/2)}` on `ℓ_s = 0`; pair `u^{±s/2}` | `archGlueAt`, `boostMassAt`, `boostPolarIndexAt`, `stablePair` |
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
- *Local walls.* Over a common denominator the local Haar state at `p` is the commensurability kernel of the
  classes `C_i + p^{v_p(A_i)}ℤ`, and the exponent splits off a Poisson kernel `r^{|v_p(a)|}` on the slope valuation;
  translation by `p^{−M}` escapes; below `1/2` the dilation by `1/p` against the `p` translations by `j/p` has form
  `p − p²·p^{−2s} < 0`. Since `nd = ∏ ℓ^{|v_ℓ(a)|}` and `db ∈ ℤ` is a condition at each prime, the global Gram
  matrix on a finite family is the Hadamard product of finitely many local ones (`TheIndexWallIsLocal`). At the
  place `∞` of `𝔽_q(X)` the local Haar state is the overlap kernel of the cosets `C_i + F[X]_{≤ deg A_i}`, a Gram
  matrix of cylinder indicators on coefficient vectors; translation by `X^M` escapes, and the dilation by `X`
  against the `q` translations by `cX` gives `q − q²·q^{−2s}` (`TheIndexWallOverAFunctionField`).
- *Height decay.* The slope height is submultiplicative; doubling dilations escape height-decaying states.
- *Running counterterm.* Translation by a product of two new primes escapes the prime lattice kernel, and the
  truncated pole vector beats any fixed counterterm (`NoFixedCountertermMakesThePrimeKernelPontryagin`).
- *Near coincidence and dilution.* A state continuous at `1` minus one decaying with the denominator has infinite
  index; spreading over `x + j/P` removes Hecke-supported parts (`ArchimedeanContinuityAgainstHeightDecay`).
- *Haar averaging and polynomial correction.* Signed translation quadrature removes a positive Haar summand
  without changing the index of a Hermitian polynomial-fibre kernel. For an arbitrary finite-index integer-Haar
  kernel, the translation-period defects have finite affine orbit of dimension at most `κ²`. Their canonical
  polynomial primitive has zero axis readings and restores integer invariance. The invariant factorial
  moving-form limit then gives the unique positive Haar and slope parts. Under continuous dilations, cyclic
  fixed-projection Grams instead tend to `J − I`, forcing infinite negative index (`Haar/`).

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
- *Absorption and selection.* The dilation reading of the glued state is `K`, so gluing never loses a square. The
  form of the pole pair is `2Re(ℓ̄m)`, `m = Σ w_i u_i^{1/2}`, which vanishes on `ℓ = 0`: the pole pair's square is
  the boost coordinate itself (`TheGluingSquareIsSharp`). The double pole's form is `2Re(ℓ̄M) − 2Re(L̄₁L₂)` with
  `L₁ = Σ w_i log u_i·u_i^{−1/2}`, `L₂ = Σ w_i u_i^{1/2}`; on `ℓ = 0` the second pair survives with one square
  (`TheGlueSeesTheOrderOfThePole`).
- *Every place.* The proof only uses that the successor is conformal at its place, Hermitian, conditionally
  positive and negative at `1`: the translation pair `1, x ↦ x + u₀^N` with `|u₀|_v > 1` and weights
  `|u₀^N|_v^{−s/2}` has form `→ 2Re ψ(1) < 0`. At a prime the boost sees `|a|_p`; Weil's correlation at slopes
  `p^{−N}` against `p^{−N/2}` is `Σ_ρ p^{−N(1 − Re ρ)}(…)`, which tends to `0` because every zero has `Re ρ < 1`
  (`TheGluingFormulaAtEveryPlace`).
- *Stable gluing.* With `σ_L = L^{−s/2}` the pair `1, x ↦ x + L` has form `4K(1)L^{−s} − 2c → −2c`; the stable
  successor's form is nonnegative on `Σ w_i u_i^{−s/2} = 0` by Poisson subordination. Against the stable boost
  `u^{−s/2}|u^{1/2−ρ}| = u^{(1−s)/2 − Re ρ}`, so a configuration with all `Re ρ > (1 − s)/2` is sub-boost
  (`TheStableGluingFormula`).
- *Jordan pairs and the heat homotopy.* A sum of lower-half-plane Jordan pair kernels `J_{u_i, P_i}` (`Im u_i < 0`,
  `P_i ≠ 0`) has index `Σ_i (deg P_i + 1)` via confluent exponential-polynomial Vandermonde inversion on a fine
  cyclic subgroup (`JordanPairKernelsOnDilations`). Tangent-disc Poisson–Jensen averaging on `D(−iR, R)` extracts
  the lower Blaschke boundary values of `H_t` from `Φ_t` without referencing zeros (`HeatTangentBlaschkeExtraction`),
  and Gaussian-damped contour integration on `Im z = ∓1` evaluates `K_t` as a Jordan pair sum over nonreal right
  zeros while keeping `t ↦ φ_c^{(t)}(g)` continuous across collisions (`HeatGaussianResidueKernel`,
  `TheHeatDeformedArchimedeanState`).

---

## 6. Pillar theorems

| Theorem | Lean |
|---|---|
| Induction formula `κ(ext₀ψ) = [G : H]·κ(ψ)`; blind extensions are index-minimal | `negIndex_extendFromSubgroup`, `negIndex_comp_retraction` |
| Escape, mixing and height decay force `κ ∈ {0, ∞}` | `negIndex_eq_zero_or_top_of_escape`, `negIndex_eq_zero_or_top_of_mixing`, `negIndex_eq_zero_or_top_of_heightDecay` |
| Affine zero-or-infinity law; the Kakutani wall is an index wall | `negIndex_eq_zero_or_top_of_isHeckeSupported`, `negIndex_heckeState` |
| **The index wall is local**: every local Hecke state jumps `0 → ∞` at `1/2`; `φ_s = ∏_ℓ φ_{ℓ,s}`; global positivity is the Schur product of local positivity | `negIndex_localHecke`, `heckeState_eq_prod_localHecke`, `isPosDefKernel_heckeState_of_local`, `negIndex_heckeState_eq_negIndex_localHecke` |
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
| **Jordan pair signature formula** `κ(Σ_i J_{u_i, P_i}) = Σ_i (deg P_i + 1)` and sub-boost gluing | `negIndex_sum_jordanPairKernel_eq`, `negIndex_archGlue_finset_sum_jordanPairKernel_eq` |
| **Heat-deformed archimedean state** `φ_c^{(t)}`: finite index `M(t) + 1`, lower semicontinuous, antitone, jumps by `1` per collided pair, `κ(φ_c) ≤ liminf_{t→0⁺} κ(φ_c^{(t)})` | `negIndex_heatArchState_eq`, `lowerSemicontinuousOn_negIndex_heatArchState`, `antitoneOn_negIndex_heatArchState`, `exists_left_negIndex_heatArchState_eq_add_collisionPairs`, `negIndex_weilArchState_le_liminf_heatArchState` |
| The gluing square is sharp: `κ(K) ≤ κ(glued) ≤ κ(K) + 1`; the pole pair is absorbed and the glue is blind to it at any strength | `negIndex_archGlue_eq_or`, `boostPolarIndex_polePair`, `negIndex_archGlue_add_polePair`, `negIndex_archGlue_ratCorr_add_polePair` |
| **The glue sees the order of the pole**: `κ^{(½)}(doublePole) = 1`, glued index `2` against `1` for a simple pole | `boostPolarIndex_doublePole`, `negIndex_archGlue_doublePole`, `negIndex_archGlue_smul_polePair` |
| **The index wall over `𝔽_q(X)`**: the local Hecke state at `∞` has `κ = 0` for `s ≥ 1/2` and `∞` below | `negIndex_inftyHecke`, `isPosDefKernel_inftyHecke`, `inftyCommKernel_gram` |
| **The archimedean Weil form is a shell identity**: `Q_Φ = Q_K(slopes) + 2c∫|tail sums|² − 2c Re(ℓ̄ Σβ(R − b))`; on `ℓ = 0` Weil's dilation form plus shell squares | `hermQuad_gram_archGlue_shell`, `hermQuad_gram_weilArchState_shell` |
| **The gluing formula at every place**: `κ(K(|a|) + |a|_v^{−s/2}ψ(b)) = κ_v(K) + 1` for every place `v` and gluing successor `ψ`; **Weil's correlation glued at any prime** has `κ = #rightZeros + 1` | `negIndex_glueAt_eq`, `negIndex_glueAt_eq_of_subBoost`, `negIndex_glueAt_padic_orbitCorr`, `negIndex_weilPadicState_eq_rightZeros`, `negIndex_glueAt_padic_dirichlet` |
| **Signature formula for prime towers**: `Σ_{p∈S} κ₀(k_p) + 1 ≤ κ(Σ_p k_p(v_p(|a|)) − c|a|^{−1/2}|b|) ≤ Σ_{p∈S} κ₀(k_p) + 2` | `towerSignature_lower`, `towerSignature_upper`, `valS_surjective`, `towerAssembly_periodic` |
| **The readings add**: `κ(Φ) = κ^{(½)}(K) + κ(Φ|_+)`, `κ(Φ|_+) = 1`; for Weil's state `κ = κ(Φ|_×) + κ(Φ|_+) = #rightZeros + 1` | `negIndex_archGlue_translation`, `negIndex_archGlue_eq_add_readings`, `negIndex_weilArchState_eq_add_readings`, `negIndex_weilArchState_sub_translation` |
| **The glue absorbs exactly its own pair**: `κ(u^{±s'/2} glued at s) = 1` if `s' = s`, else `2`; at `s = 1` only the pole pair is absorbed | `negIndex_archGlueAt_stablePair_eq`, `boostPolarIndexAt_stablePair_of_ne`, `negIndex_archGlue_stablePair_of_ne` |
| **Stable gluing formula** `κ(K(|a|) − c|a|^{−s/2}|b|^s) = κ^{(s/2)}(K) + 1`, `0 < s < 1`; absorbed pair `u^{±s/2}`; zero configurations with `Re ρ > (1 − s)/2` give `κ(K_Z) + 1`; a drop for `ζ` certifies a zero with `Re ρ ≤ (1 − s)/2` | `negIndex_archGlueAt_eq`, `negIndex_archGlueAt_eq_or`, `boostPolarIndexAt_stablePair`, `negIndex_archGlueAt_orbitCorr`, `exists_zero_le_of_negIndex_archGlueAt_ratCorr_ne` |
| Shell decomposition of the local pole–successor forms | `hermQuad_gram_poleSuccessor_negUltra_eq`, `hermQuad_gram_poleSuccessorState_eq` |
| **Canonical Haar splitting**: unique `k=p+ψ∘slope+Q`, with positive Haar `p` and finite-rank zero-axis polynomial `Q`; `κ(k)=κ(ψ∘slope+Q)≥κ(ψ)` | `exists_unique_haar_relative_split`, `finite_index_haar_iff_relative_split` |
| **Polynomial index preservation**: `κ(p+h)=κ(h)` for positive Haar `p` and Hermitian polynomial-fibre `h`, including infinite index | `negIndex_add_positive_haar_polynomial` |
| **Sharp punctured limits**: precisely real `L≤0`, with minimum index zero at zero and one at negative limits | `exists_finite_index_haar_punctured_limit_iff`, `exists_haar_negative_limit_index_one` |
| **Subgroup successor classification**: continuous-dilation finite-index carriers exist exactly for `H={0}` or `H=ℚ`, with positive witnesses | `exists_finite_index_continuous_subgroup_successor_iff` |
| Axis-invisible kernels: zero or `κ ≥ 2`, rank `≤ κ²`, polynomial fibres of degree `< κ`; every `κ ≥ 2` occurs | `two_le_negIndex_of_zero_axes`, `rank_gram_le_square_of_zero_axes`, `negIndex_haarMixedPowerState` |
| The index is twin-blind | `negIndex_mul_unitaryChar`, `negIndex_heckeState_mul_slopeChar` |

---

## 7. Questions

1. **Is there a signature formula `κ(K_ζ) = Σ_p (local defect) − (archimedean gluing)`?**
   *Answered for the glue.* Local constituents sharing the pole glue with at most one square (separable
   assemblies); a conformal successor glues to its pole with exactly one (`κ₀ + 1`); distinct places add; the
   archimedean place glues dilation data by the boost hyperplane, `κ^{(½)}(K) + 1`, and for prime towers and for
   Weil's correlation the hyperplane is free, so the archimedean term is exactly one square. For finitely many
   prime towers this gives the signature formula `κ = Σ_p κ₀(k_p) + 1 + ε`, `ε ∈ {0, 1}`: local defects, one
   archimedean square and at most one pole square; the pole terms
   contribute nothing to it at any strength, and every prime glues Weil's correlation the same way, with one square
   and the same zero count. For the Hecke states the local–global law is a product formula with
   identical local walls at every prime. *Open*: the decomposition of `κ(K_ζ)` itself into prime defects; the Weil
   kernel is neither tower-supported nor separable.
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
   *Partial.* An affine invariant exists: the excess of the index of Weil's archimedean state over the index of
   its translation reading. The translation reading itself is zero-blind (one square for every glued state). On
   the additive side alone the index is a count of negative conductor coefficients, and decaying,
   Hecke-supported and height-decaying carriers have index `0` or `∞`. *Open*: a purely additive carrier (the
   collision charge, a Toeplitz Fredholm index).
6. **Is there an exact sum-of-squares decomposition of the complete Weil form indexed by successor-agreement
   shells?** *Answered for the local pole–successor forms*: a renormalized hyperbolic pair plus squares of shell
   sums over balls (at `p`) or half-lines (at `∞`); and for the archimedean Weil state: on the boost hyperplane
   its form is Weil's dilation form plus the squares of the half-line shells of the shifts, so the successor
   side is an exact sum of squares. *Open* for Weil's dilation form itself, whose indefiniteness is the
   number of zeros right of the line.

---

## 8. Tools

| Tool | Developed | To develop |
|---|---|---|
| Pontryagin index theory on groups | induction, witness complements, escape, mixing, block additivity, twist invariance, Krein compressions, conformal induction | Krein–Langer structure on `Aff(ℚ)` |
| Local–global signature calculus | polar index, separable formula, pole–successor formula, additivity over places, boost-polar index and archimedean gluing | prime-local defects of the Weil kernel; non-separable glue |
| Kakutani–Hellinger dichotomies | the Kakutani wall as an index wall; zero-or-infinity laws as index zero–one laws; local walls at every prime and their Schur assembly; the local wall at `∞` of `𝔽_q(X)` | local walls at the places of higher degree of `𝔽_q(X)` and their product |
| Mautner / Howe–Moore phenomena | infinite index for Haar kernels with continuous dilations; unique canonical Haar decomposition and exact polynomial residual index | relative splitting for general nonzero proper rational successors |
| Bost–Connes / KMS at the critical temperature | Hecke states at every exponent and their index wall | states below `β = 1` |
| Ramanujan Plancherel, conductor Hamiltonian | additive index law on `ℤ/N`, `ℚ/ℤ`; Ramanujan law `Σ_{A_d<0} φ(d)` | the spectral measure on `ℤ̂` |
| Successor-shell calculus | shell decompositions at every place with running counterterms | shells of the complete Weil form |
| Lyapunov methods for the dBN flow | source-defined heat Pontryagin homotopy `φ_c^{(t)}` linking dBN collision counts to affine indices | a purely additive or `t → 0⁺` source bound without `ξ`-zero input |
| Linear independence of logarithms | separating units for distinct places | quantitative bounds in the pre-ergodic regime |

---

## 9. Open research topics

1. **Prime-local defects.** Decompose `κ(K_ζ)` into contributions of the prime towers glued by the archimedean
   hyperplane, and compare them with the matched local Hodge indices.
2. **Krein–Langer structure on `Aff(ℚ)`.** Is every Pontryagin state a positive state plus coefficients of
   finite-dimensional or conformally induced Pontryagin representations? Known pieces: pole–successor states, the
   Borel's `Sym^d` (mixed power kernels), archimedean Weil states.
3. **Relative splitting for rational subgroup successors.** The integer-Haar case has a unique positive,
   slope and zero-axis polynomial split with exact residual index. The
   [extension to general nonzero proper subgroups](../../../docs/drafts/pipeline/0-backlog/nonzero-proper-subgroup-carriers-have-a-canonical-relative-split.md)
   remains open.
4. **Purely additive counters.** An index on the translations alone that equals the number of zeros right of the
   line, or a proof that none exists among natural classes.
5. **Calibration over `𝔽_q(T)`.** The local wall at the place `∞` holds. Open: the places of higher degree, the
   product formula for the global Hecke state of `Aff(𝔽_q(T))`, and the archimedean Weil state of a curve and its
   index.
6. **Shell identity for the Weil form.** Extend the local shell decomposition to the complete Weil form; the form
   of the archimedean Weil state is `K`'s form at the slopes plus the shell form at the shifts.
7. **Stable gluing below the strip.** The stable gluing formula holds at every `0 < s < 1`, the hyperplane is free
   when every zero has `Re ρ > (1 − s)/2`, and for `ζ` a drop of the stable index to `κ(K_ζ)` certifies a zero
   with `Re ρ ≤ (1 − s)/2`. Such a zero does not force the drop: a real pair farther out keeps its square, and
   the glue at exponent `s` absorbs exactly the pair at `(1 ± s)/2`. Open: what the stable indices `s ↦ κ_s` read
   for infinite configurations that are not sub-boost.

---

## 10. Traps

| Trap | Fact |
|---|---|
| Successor coordinates are free | only at index zero; the regular extension costs `[G : H]` copies of every square |
| An indefinite carrier escapes APD's positive no-gos | a Hecke-supported Pontryagin state is positive |
| The integer successor forbids a finite nonzero index | `haarOneNegativeSquare` has index one, with a discontinuous dilation reading |
| Some correction lets the integer successor carry continuous dilation data | never: every such Hermitian kernel has infinite index |
| The Kakutani wall is a gradual change of index | it is a jump `0 → ∞` |
| The wall at `1/2` comes from the infinite product over primes | every single prime already carries it |
| The glue absorbs every pole term | only the simple pole pair; a double pole costs a square |
| A zero beyond the strip forces the stable glue to absorb | only the pair at exactly `(1 ± s)/2` is absorbed |
| The wall at `1/2` is special to `ℚ` | the place `∞` of `𝔽_q(X)` carries the same wall |
| A decaying state can carry a few negative squares | mixing and height decay kill them |
| Local polar indices add exactly | up to one gluing square, carried by the shared pole |
| The successor can absorb the pole's square | never: `κ = κ₀(ψ) + 1` |
| Poles at different places glue like a shared pole | they add: `κ(Φ_∞ + Φ_p) = 2` |
| Conformal Frobenius has a positive analogue | positive states admit no conformal symmetry |
| The Hecke normalization `|u|^{1/2}` is a convention | it is the boost exponent of the archimedean successor `−|b|` |
| Gluing at the archimedean place costs an unknown amount | for towers and for Weil's correlation exactly one square |
| Only the archimedean place can glue Weil's dilation data | every prime glues them at full index too |
| Index laws select `ζ` | they are twin-blind; only the dilation data select |
| The matched local Hodge indices assemble on `ℚ_{>0}` | every fixed counterterm leaves infinitely many squares |
| Finite index is a positive state plus slope data | the Haar mixed quadratic state and the pole–successor states are not |
| A new RH equivalence is progress | a contribution computes, bounds or excludes an index |

---

## 11. Place in the research

AKG is the indefinite counterpart of APD's affine positivity and the affine counterpart of the multiplicative index
theory of HKT and AKL. It is the field asked for in §2.6 of the obstacles review, and it addresses that review's
problems B8 (local-to-global signature) and B19 (a successor-carrying carrier) and its opportunities O2 (a Hasse
principle for the index) and O5 (a second bridge between the primes). Its answers there: the Hecke index wall is
the common wall of identical local walls; finite tower assemblies have a local signature formula; and Weil's
correlation, glued at the archimedean place or at any prime, has the same index, the number of zeros right of the
line plus one square for the place. The second bridge is the gluing at a place, not the integer successor.

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
   place, additivity over places, the separable and archimedean gluing formulas; for the Hecke family the local
   wall at every prime and the product formula; for finitely many prime towers the signature formula
   `Σ_p κ₀(k_p) + 1 ≤ κ ≤ Σ_p κ₀(k_p) + 2`. Met for the glue, the Hecke family and finite tower assemblies; the
   prime-local decomposition of `κ(K_ζ)` is open.
3. *an additive–multiplicative comparison proved as an identity*: the Gram identities of the pole–successor and
   archimedean states, the index identity `κ = #{zeros right of the line} + 1`, and its splitting
   `κ(Φ) = κ(Φ|_×) + κ(Φ|_+)` into the multiplicative and the additive reading. Met for the archimedean
   comparison; `S = W` itself is not addressed.
4. *a conformal symmetry with factor `≠ 1`, or a proof that none exists and its substitute*: none on positive
   states; the substitute is the pole–successor state. Met.
5. *calibration over `𝔽_q[T]`*: the conformal successor and the pole–successor state at `∞` with boost `q^{±1/2}`;
   the local Hecke wall at `∞`. The places of higher degree and the global product over `𝔽_q(T)` are open.
6. *selectivity*: index laws are twin-blind; the archimedean states of different L-functions count their own
   zeros; the glue absorbs a simple pole and charges a double one. Met at the level of dilation data.
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
- Arithmetic types: `HeckeSupportedStatesHaveIndexZeroOrInfinity`, `TheIndexWallIsLocal`,
  `ThePontryaginExtensionsOfWeilsCorrelation`,
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
  `PrimeTowersGlueAtFullIndex`, `WeilsArchimedeanStateCountsTheZeros`, `TheGluingSquareIsSharp`,
  `TheGlueSeesTheOrderOfThePole`, `JordanPairKernelsOnDilations`, `HeatTangentBlaschkeExtraction`,
  `HeatGaussianResidueKernel`, `TheHeatDeformedArchimedeanState`, `TheStableGluingFormula`,
  `TheGlueAbsorbsExactlyItsOwnPair`, `TheIndexWallOverAFunctionField`, `TheTwoReadingsAdd`,
  `ASignatureFormulaForPrimeTowers`, `TheGluingFormulaAtEveryPlace`, `TheArchimedeanWeilFormIsAShellIdentity`.
- Haar carriers (`Haar/`): `OneNegativeSquare`, `IndexPreservation`, `ContinuousDilationsNeedInfiniteIndex`,
  `MixedPolynomialPerturbation`, `AxisInvisibility`, `FiniteRankPerturbations`, `PolynomialPerturbations`,
  `PowerKernels`, `PeriodDefects`, `PolynomialCorrection`, `TranslationMovingPositivity`, `CyclicOrbits`,
  `CyclicHecke`, `CyclicGramLimit`, `FiniteIndexObstruction`, `ScaledHaarObstruction`,
  `PositiveAffineObstruction`, `FiniteAdelicReading`, `AdelicObstruction`.
- Canonical Haar splitting and residual index (`Haar/`): `GeneralOrbits`, `TranslationProjections`,
  `TranslationForms`, `MovingLimit`, `PositivePart`, `PositiveSlopeSplit`, `SplittingUniqueness`,
  `RelativeSplit`, `PolynomialIndexPreservation`, `Classification`.
- Sharp Haar dilation limits (`Haar/`): `PuncturedLimits`, `SharpDilationLimits`.
- Subgroup successors (`Haar/`): `TranslationSaturation`, `SubgroupEndpoints`, `SubgroupOrbits`,
  `SubgroupMovingBounds`, `SubgroupGramLimit`, `SubgroupClassification`.
