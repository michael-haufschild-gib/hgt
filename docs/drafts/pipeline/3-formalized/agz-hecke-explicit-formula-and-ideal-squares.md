# The explicit formula of a Hecke L-function and the square of a ring through its ideals

- **ID:** agz-hecke-ef
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) programme step
- **Source:** `docs/reports/review-1011/fable.md` §9.5 question 7, §9.8 step 4; programme card
  `../3-formalized/agz-absolute-geometry-of-spec-z.md`
- **Statement:** for a number field `K`, a modulus `𝔪` and a primitive ray class character `ψ`,
  the zeros of the completed `L(s, ψ)` satisfy Weil's explicit formula
  `Σ_ρ m_ρ H_k(ρ) = [ψ = 1](H_k(0) + H_k(1)) + (1/2π)∫ k̂(r) B_ψ(r) dr
  − Σ_n n^{−1/2}(a_ψ(n) k(log n) + conj a_ψ(n) k(−log n))`,
  `a_ψ(n) = Σ_{N𝔞 = n} Λ_K(𝔞) ψ(𝔞)`, and the square of a ring through its ideals (a class
  character; a ring that is not abelian over `ℚ`, through its Dedekind zeta function) has the
  index law.

## Goal
Question 7 of the `𝔽₁` programme: ideals as degree points, the characters of the class group,
and one ring that is not abelian. The tool that the corpus lacks is the explicit formula of a
Hecke `L`-function. The corpus has the completed functional equation
(`HeckeLFunctions.heckePoleClearedCompletion_reflection`), the Euler product, and the abstract
analytic tools below.

## Gates
- [x] P1 two lines weigh the zeros of an order-one function (abstract)
- [x] P2 arithmetic form: pole pair, archimedean factor moved to the critical line, two Dirichlet
      series (abstract, a function and its dual)
- [x] P3 Hecke inputs: (a) `−L'/L(s, ψ) = Σ Λ_ψ(n) n^{−s}`; (b) order one of the completed
      function; (c) zeros in the closed strip; (d) the archimedean term and its symbol
- [x] P4 the explicit formula of `L(s, ψ)`; the zero configuration; temperedness; the index law
- [x] P5 consumers: the pairing of the ideals as degree points at finite scale (jets of the
      places, counterterm, contacts `Re Λ_ψ`); every number ring through its ideals
- [x] P6 below the first contact: the places against the conductor; the inequality on the
      square of a number ring of large discriminant
- [x] P7 the class characters together: contacts on the principal prime powers, the pairing and
      the index of the sum
- [x] P9 one ring that is not abelian, in Lean: the splitting field of `X³ − 2` (group `S₃`),
      with its degree points and its Hodge index
- [ ] P8 the index of an Artin character (needs class field theory)

## Lean (folder `formal/GaloisForLFunctions/AbsoluteGeometryOfSpecZ/`)

| Gate | Module | Declarations |
|---|---|---|
| P1 | `TwoVerticalLinesWeighTheZerosOfAFunctionOfOrderOne` | `zeroOf`, `exists_hasSum_logDeriv`, `hasSum_zeros_two_lines` |
| P2 | `AFunctionOfOrderOneWithAFunctionalEquationHasWeilsExplicitFormula` | `hasSum_zeros_explicit` |
| P3a | `TheLogarithmicDerivativeOfAHeckeLSeriesRunsOverThePowersOfThePrimeIdeals` | `heckeMangoldt`, `log_mul_heckeCoeff_eq`, `norm_heckeMangoldt_le`, `lSeriesSummable_heckeMangoldt`, `logDeriv_heckeL` |
| P3b | `TheCompletedFunctionOfAPrimitiveHeckeCharacterHasOrderOne` | `StripBounded`, `stripBounded_heckeGammaCompletedRegularPart`, `norm_heckeGammaFactor_le`, `exists_orderOne_of_three_regions`, `exists_orderOne_heckePoleClearedCompletion`, `exists_orderOne_heckeCompletedLFunction` |
| P3c, P3d | `TheLogarithmicDerivativeOfACompletedHeckeFunctionIsItsPolesItsGammaFactorsAndItsPrimeIdeals` | `heckeXi`, `heckeXi_eq`, `heckeXi_one_sub`, `heckeXi_inv_conj`, `exists_orderOne_heckeXi`, `heckeXi_ne_zero`, `heckeArch`, `logDeriv_heckeXi`, `exists_norm_heckeArch_le` |
| P4 (abstract) | `TheZerosOfAFunctionOfOrderOneWithAReflectionFormATemperedConfiguration` | `analyticOrderAt_reflect_of_dual`, `zerosConfig`, `hasSum_zerosConfig`, `temperedConfig_zerosConfig`, `W_zerosConfig_eq` |
| P4 | `TheZerosOfAHeckeLFunctionSatisfyWeilsExplicitFormula` | `heckeZeros`, `temperedConfig_heckeZeros`, `heckeSymbol`, `heckeArch_bracket`, `W_heckeZeros_eq`, `exists_le_negIndex_heckeGram_iff`, `forall_negIndex_heckeGram_eq_zero_iff`, `heckeXi_eq_zero_iff` |
| P5 | `TheIdealsOfANumberRingPairAsDegreePointsWithTheZerosOfItsHeckeFunctions` | `placeDegree`, `heckeConjugatePlaces`, `heckeSymbol_eq`, `heckeZeroSum`, `heckePacketForm`, `heckeZeroSum_eq_heckePacketForm`, `heckeForm`, `tendsto_heckeForm_add_idealContact` |
| P5 | `TheSquareOfANumberRingThroughItsIdealsHasTheIndexOfItsDedekindZetaFunction` | `heckeFiniteConductor_trivialModulus`, `dedekindZeros`, `idealContact`, `ringForm`, `tendsto_ringForm_add_idealContact`, `tendsto_ringForm_add_classContact`, `exists_le_negIndex_dedekindGram_iff`, `forall_negIndex_dedekindGram_eq_zero_iff` |
| P6 | `BelowTheFirstContactALargeDiscriminantGivesTheInequalityOnANumberRing` | `packetAutocorr_log_eq_zero_of_short`, `archForm_add_log_mul_mass_nonneg`, `archForm_add_conjugateForm_add_log_mul_mass_nonneg`, `heckeZeroSum_ge_of_no_contact`, `heckeZeroSum_nonneg_of_no_contact`, `dedekindZeroSum_ge_zeroSum_of_no_contact`, `tendsto_ringForm_le_degrees_of_short` |
| P7 | `TheClassCharactersTogetherCarryTheContactsOfTheIdealsOfTrivialClass` | `sum_monoidHom_apply_eq_zero`, `sum_heckeValue_trivialModulus`, `classTrivialContact`, `sum_heckeMangoldt_trivialModulus`, `toClassGroup_trivialModulus_injective`, `forall_heckeValue_eq_one_iff_isPrincipal`, `classTrivialContact_eq`, `tendsto_ringForm_add_classTrivialContact`, `exists_le_negIndex_classGram_iff` |
| P9 | `TheRingOfTheCubeRootsOfTwoIsNotAbelianAndHasItsHodgeIndex` | `cube_ne_two`, `irreducible_cubeMinusTwo`, `card_rootSet_real_cubeMinusTwo`, `galActionHom_cubeMinusTwo_bijective`, `CubeRootsOfTwo`, `exists_not_commute_cubeRootsOfTwo`, `tendsto_ringForm_cubeRootsOfTwo`, `exists_le_negIndex_cubeRootsOfTwo_iff`, `forall_negIndex_cubeRootsOfTwo_eq_zero_iff` |

Each module: `lake --old env lean`, exit 0, no output. The statements hold for every number
field and every primitive ray class character; the trivial character is the Dedekind zeta
function.

## Paper proof of P5

Notation: `h` the autocorrelation of a real packet `f`, `F = f` as a complex function,
`k = F ⋆ F̃ = h`; `d = r₁ + 2r₂`; `c` the number of factors `Γ_ℝ(s + 1)` (real places where `ψ`
is odd, and the complex places); `N` = absolute discriminant times the norm of the conductor.

**Q1. The symbol.** On the critical line the logarithmic derivative of `N^{s/2} Γ_ℝ(s + κ)`,
taken at `½ ± it` and added, is `log N − log π + Re ψ(¼ + κ/2 + it/2)`. For `κ = 0` this is the
symbol `S₀(t)` of `ℤ`; for `κ = 1` the reflection formula of the digamma function adds
`π/cosh(πt)`. Summing over the places, `S_ψ = log N + d S₀ + c π/cosh(πt)`.

**Q2. The explicit formula on a packet.** In the explicit formula (P4) with `f = g`:
the pole pair is `m_ψ 2d₁d₂`; `k̂(t) = |F̂(t)|²`; by Plancherel `(1/2π)∫|F̂|² = h(0)`;
`(1/2π)∫|F̂|² S₀ = A(0)h(0) + ∫_{x>0} 2ω(x)(h(0) − h(x))dx` (the archimedean form of `ℤ` on a
packet); `(1/2π)∫|F̂|² π/cosh(πt) = ∫ h(x)/(2cosh(x/2)) dx`; `h` is real and even, so the two
prime sums add up to `2 Σ_n Re Λ_ψ(n) n^{−1/2} h(log n)`, a finite sum (`Λ_ψ(1) = 0`,
`h(log n) = 0` beyond the length of the packet). Hence

`Z_ψ(f) = m_ψ 2d₁d₂ + log N h(0) + d(A(0)h(0) + ∫ 2ω(h(0) − h)) + c∫ h/(2cosh(x/2))
  − 2 Σ_n Re Λ_ψ(n) n^{−1/2} h(log n)`.

**Q3. Finite scale.** On the degree points of the window `(N, (1 + 3K)N]`: the jets and the
counterterm of `ℤ` tend to `−(A(0)h(0) + ∫ 2ω(h(0) − h))`; the jets `1/(m + n)` tend to
`∫ h/(2cosh(x/2))`; the masses to `h(0)`; the contacts with a weight `w` to
`Σ_k w(k) k^{−1/2} h(log k)`. With the coefficients `d, −c, −log N, 2` and `w = Re Λ_ψ` the sum
of the limits is `m_ψ 2d₁d₂ − Z_ψ(f)` by Q2.

**Q4. The unit modulus.** The conductor of a character divides the modulus, so a character of
the unit modulus is primitive; it has no parity at a real place, `c = r₂`, `N = |d_K|`. For the
trivial character `Λ_1(n) = Σ_{N𝔭^k = n} log N𝔭` and `L(s, 1) = ζ_K(s)`.

**Q5. Below the first contact.** A prime ideal has norm `≥ 2`, so a packet of width `< log 2`
has `h(log n) = 0` for `n ≥ 2` and no contact enters Q2. Pointwise the symbol of `ℤ` satisfies
`S₀(t) + log 128π ≥ 0` and `S₀(t) + π/cosh(πt) + log 4π ≥ 0` (the digamma function at `¼ + it/2`
and `¾ + it/2` has its least real part at `t = 0`). With Plancherel,
`A(f) ≥ −log(128π) h(0)` and `A(f) + ∫h/(2cosh) ≥ −log(4π) h(0)` for the archimedean form `A`
of `ℤ`. Writing `d A + c ∫h/(2cosh) = (d − c)A + c(A + ∫h/(2cosh))`:
`Z_ψ(f) ≥ m_ψ 2d₁d₂ + (log N − (d − c) log 128π − c log 4π) h(0)`.
For the trivial character of the unit modulus, `Z_K(f) − Z_ζ(f) = log|d_K| h(0) + (d − 1)A +
r₂ ∫h/(2cosh) ≥ (log|d_K| − (r₁ + r₂ − 1) log 128π − r₂ log 4π) h(0)`, and
`Z_ζ(f) ≥ ∫f²/5000` on packets of width `≤ 181/250` (corpus certificate). Hence the inequality
on the square of the ring below the first contact when
`|d_K| ≥ (128π)^{r₁+r₂−1}(4π)^{r₂}`.

**Q6. The class characters together.** For a finite abelian group and `g ≠ 1` there is a
character `φ₀` with `φ₀(g) ≠ 1`; multiplying the sum `Σ_φ φ(g)` by `φ₀(g)` permutes its terms, so
the sum vanishes. For a nonzero ideal `I` with class `g_I` in the ray class group of the unit
modulus, `ψ(I) = ψ(g_I)`; hence `Σ_ψ ψ(I)` is `h` if every class character is `1` on `I` and `0`
otherwise. With `ψ(𝔭)^k = ψ(𝔭^k)`: `Σ_ψ Λ_ψ(n) = h Σ_{N𝔭^k = n, 𝔭^k of trivial class} log N𝔭`.
For the unit modulus an element of `K` satisfies no congruence and no sign condition, so the
ray class group injects into the class group and `g_I = 1` iff `I` is principal.
The contacts are linear in the weight and only `ψ = 1` has a pole plane, so the sum over `ψ` of
Q3 is: `h(jets + counterterm) + 2h(contacts of trivial class) → 2d₁d₂ − Σ_ψ Z_ψ(f)`. The index of
a sum of forms of tempered configurations is the number of distinct zeros to the right of the
line in their union (corpus).

**P9 (paper).** `X³ − 2` is irreducible over `ℚ`: a rational root of a monic integer polynomial
is an integer, and `n³ = 2` has no integer solution (`n ≤ 1` gives `n³ ≤ 1`, `n ≥ 2` gives
`n³ ≥ 8`). It has one real root (the cube is strictly increasing) and three complex roots, so
its Galois group, a transitive subgroup of `S₃` containing the transposition complex conjugation,
is `S₃`; two transpositions do not commute. P5 holds for every number field, hence for the
splitting field.

## Open after P5
- The index law per Artin character of a ring that is not abelian: it needs each Artin
  `L`-function as an entire function with its functional equation; for a monomial character this
  is the Hecke `L`-function of the inducing character, an identity of class field theory that
  the corpus does not have.
- The zeros of the completion as zeros of a continuation of `ζ_K` itself (for `ψ ≠ 1`:
  `heckeXi_eq_zero_iff`).

## Approach

Notation: `H_k(s) = ∫ k(u) e^{(s − 1/2)u} du` (`Zeta23.WeilEF.Hfn`), `ρ_q` the zeros of `E` with
multiplicity (`ZeroCopy (fun z => E (z + 2))`, shifted by `2`).

**P1.** Let `E` be entire with `‖E(s)‖ ≤ exp(C(1 + |s|) log(2 + |s|))`, `E(2) ≠ 0`, all zeros in
`0 ≤ Re s ≤ 1`, `1 < c ≤ 2`, and `H` entire with `|H(σ + it)| ≤ D(1 + t²)^{−2}` on
`−1 ≤ σ ≤ 2`. Then
`Σ_q H(ρ_q) = (1/2π)(∫ H(c + it) E'/E(c + it) dt − ∫ H(1 − c + it) E'/E(1 − c + it) dt)`.

*Proof.* Hadamard (`OrderOneHadamard.exists_expAffine_mul_hadamardProduct`) gives at every
non-zero `s`: `E'/E(s) = a + Σ_q (1/(s − ρ_q) + 1/(ρ_q − 2))`, absolutely convergent, with
`Σ_q |ρ_q − 2|^{−2} < ∞`. For one `q`, `two_line_simple_pole` gives
`∫ H(c + it)/(c + it − ρ_q) − ∫ H(1 − c + it)/(1 − c + it − ρ_q) = 2π H(ρ_q)`, and the two line
integrals of `H` agree (`vertical_line_shift`), so the constants `1/(ρ_q − 2)` and `a` drop out
of the difference of the two lines. Summation over `q` under the integral: on either line
`|s − ρ_q| ≥ c − 1` and `|ρ_q − 2| ≤ |s − ρ_q| + |s − 2|`, hence
`|1/(s − ρ_q) + 1/(ρ_q − 2)| ≤ |s − 2|(1 + |s − 2|/(c − 1)) / |ρ_q − 2|²`, which against the decay
of `H` is integrable in `t` and summable in `q`.

**P2.** Let moreover `E(1 − s) = W Ẽ(s)`, `W ≠ 0`, and on `Re s > 1`
`E'/E = m g₀ + G − Σ a(n) n^{−s}`, `Ẽ'/Ẽ = m g₀ + G − Σ ã(n) n^{−s}`,
`g₀(s) = 1/s + 1/(s − 1)`, `G` holomorphic on `Re s > 0` with `|G(σ + it)| ≤ C log(2 + |t|)` on
`1/2 ≤ σ ≤ 3/2`, both series absolutely convergent at `c`, `1 < c ≤ 3/2`. Then for `k ∈ C_c²`
whose transform decays to fourth order

`Σ_q H_k(ρ_q) = m(H_k(0) + H_k(1)) + (1/2π)∫ k̂(t)(G(1/2 + it) + G(1/2 − it)) dt
− Σ_n n^{−1/2}(a(n) k(log n) + ã(n) k(−log n))`.

*Proof.* `E'/E(1 − s) = −Ẽ'/Ẽ(s)`; substitute `t ↦ −t` on the left line. The pole pair is
`two_line_pair`, the factor `G` is `ThmE.line_shift_generic`, the series are
`hasSum_prime_side_line` for `k` and for `u ↦ k(−u)`.

**P3.** (a) `a_ψ = Σ_{N𝔞 = n} Λ_K(𝔞)ψ(𝔞)`; the convolution identity
`Σ_{𝔟 | 𝔞} Λ_K(𝔟) = log N𝔞` twisted by the multiplicative `ψ` gives
`a_ψ ⍟ c_ψ = log · c_ψ`, hence `L' = −L · Σ a_ψ(n) n^{−s}`. (b) On a vertical strip the
continued Mellin transforms `WeakFEPair.Λ₀` are bounded (the Mellin integral of the norm at the
two edges), the class weights are exponentials, so the pole-cleared completion is `O(|s|²)` on
`−1 ≤ Re s ≤ 2`; right of the strip the Gamma product is bounded by its value on the real axis
and the Dirichlet series is bounded; left of it the functional equation. (c) Euler product right
of `1`, functional equation left of `0`. (d) `E = [s(s − 1)] N^{s/2} Π_v Γ_ℝ(s + κ_v) Γ_ℂ(s)^{r₂} L`,
`Γ_ℂ(s) = Γ_ℝ(s)Γ_ℝ(s + 1)`; `ThmE.archChi_bracket` evaluates each factor on the critical line.

## Log
- 2026-11-10 — created; corpus tools located (Hadamard pairs, two-line pole identity, generic
  line shift, prime side on a line of absolute convergence).
- 2026-11-11 — P1–P4 formalized (seven modules).
- 2026-11-11 — P5 formalized (two modules); paper proof Q1–Q4.
- 2026-11-11 — P6 formalized; paper proof Q5.
- 2026-11-11 — P7 formalized; paper proof Q6.
