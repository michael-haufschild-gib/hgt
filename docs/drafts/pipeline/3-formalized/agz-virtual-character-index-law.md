# The index of a virtual configuration counts its zeros and its poles

- **ID:** agz-virtual-index (task A145 of `docs/reports/review-1111/obstacles-summary.md`)
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** obstacles-summary (review-1111) §2.14 question 4, construction IV; §2.1 A145
- **Statement:** for tempered zero configurations `A`, `B` with multiplicities `m_A`, `m_B`
  (zero off the carrier), the form `W_A − W_B` has `n` negative squares on some family of `n`
  compactly supported `C²` tests iff
  `#({Re ρ > ½, m_A(ρ) ≠ m_B(ρ)} ∪ {Re ρ = ½, m_A(ρ) < m_B(ρ)}) ≥ n` (in `ℕ∞`). It has no negative
  square on any family iff `m_A = m_B` right of the line and `m_B ≤ m_A` on it.

## Gates
- [x] V1 upper bound for a pair `(P, N)`
- [x] V2 the Krein form of a disjoint pair on the coordinates of the union
- [x] V3 attainment for a disjoint pair
- [x] V4 cancellation to a disjoint pair
- [x] V5 the law; quotients of products; the relative square of two number rings
- [ ] V6 the identification of induced characters with Hecke characters: invariance of Artin's
  Euler product under induction and the reciprocity law (Brauer's theorem is proved: card
  `3-formalized/brauer-induction-theorem.md`, `brauer_induction`)
- [x] V7 zeros minus poles: the neutral form of `ℤ` and of every number ring has index one plus
  the number of zeros right of the line
- [x] V8 the contacts of a number ring are its point counts over the finite fields; the relative
  square of two number rings at finite scale
- [x] V9 Artin's induction theorem: every virtual character of a finite group has a positive
  multiple in the lattice of the monomial characters
  (classical; not in the corpus): the law for every Artin character

## Paper proof

Notation of the corpus (`ArithmeticCastelnuovoSeveri`): `γ_ρ = (ρ − ½)/i`, reflection
`Rρ = 1 − ρ̄`, `γ_{Rρ} = conj γ_ρ`, `W_Z(f, g) = Σ_{ρ∈Z} m_ρ f̂(γ_ρ) conj ĝ(conj γ_ρ)`, Gram matrix
`G_Z(f)_{ij} = W_Z(f_i, f_j)`, `hermQuad G x = Re W(F, F)` for `F = Σ conj(x_i) f_i`.

**V1.** Let `D = {Re > ½} ∩ P ∪ {Re > ½} ∩ N ∪ {Re = ½} ∩ N`. If `F̂(γ_ρ) = 0` for `ρ ∈ D`:
each summand of `W_N(F, F)` vanishes (`ρ ∈ N` right of or on the line: the factor `F̂(γ_ρ)`;
left of the line: the factor `conj F̂(conj γ_ρ) = conj F̂(γ_{Rρ})`, `Rρ ∈ N` right), and
`Re W_P(F, F) ≥ 0` (corpus). The conditions are `#D` linear functionals of `x`, so the index of
`G_P − G_N` is at most `#D`.

**V2.** `P ∩ N = ∅`. `S = P ∪ N` with the multiplicities of its members is tempered. Zero-side
coordinates `X(f)_τ = √m_τ f̂(γ_τ) ∈ ℓ²(S)` have dense range (corpus). With `s_τ = +1` on `P`,
`−1` on `N` (invariant under `R`) and `(T x)_τ = s_τ x_{Rτ}`:
`⟨T X(g), X(f)⟩ = Σ_τ s_τ m_τ f̂(γ_τ) conj ĝ(conj γ_τ) = W_P(f, g) − W_N(f, g)`,
the last step by regrouping the absolutely convergent sums through indicators. `T` is additive
and `‖T x‖ = ‖x‖`.

**V3.** For distinct `ρ_1, …, ρ_k ∈ D` put `w_i = e_{ρ_i} − s_i e_{Rρ_i}`. Then
`T w_j = s_j e_{Rρ_j} − e_{ρ_j}` and
`⟨T w_j, w_i⟩ = s_j[Rρ_j = ρ_i] − s_j s_i[Rρ_j = Rρ_i] − [ρ_j = ρ_i] + s_i[ρ_j = Rρ_i]`.
For `i ≠ j` all four vanish: `Rρ_j = ρ_i` would give `Re ρ_i + Re ρ_j = 1` with both `≥ ½`, so
both on the line, where `R` is the identity. For `i = j`: `−2` if `Rρ_i ≠ ρ_i`; if `Rρ_i = ρ_i`
the point is on the line, in `N`, `s_i = −1`, value `−4`. Approximate `w_i` by `X(g_i)` within
`ε = 1/(5(k+1))`: the Gram matrix of `g` is within `5ε` of `diag(d_i)`, `d_i ≤ −2`, hence
`≤ −|x|²`.

**V4.** `P = {m_B < m_A}` with multiplicity `m_A − m_B`, `N = {m_A < m_B}` with `m_B − m_A`.
Both are configurations (the extended multiplicity is invariant under `R`; windows are finite),
tempered (dominated by `A`, `B`), disjoint, and `W_A − W_B = W_P − W_N` termwise:
`(m_A − m_B) u = [m_B < m_A](m_A − m_B)u − [m_A < m_B](m_B − m_A)u`.
`D(P, N) = {Re > ½, m_A ≠ m_B} ∪ {Re = ½, m_A < m_B}`.

**V5.** V1–V4. For families: the superposition has the sum of the multiplicities and the sum of
the forms.

**V7.** The configuration `B = {0, 1}` with multiplicity one is closed under `ρ ↦ 1 − ρ̄` and
lies in the closed strip; `γ_0 = i/2`, `γ_1 = −i/2`, so
`W_B(f, g) = h_f(i/2) conj h_g(−i/2) + h_f(−i/2) conj h_g(i/2)`, on a real packet twice the
product of the two charges. For a tempered `A` with `1 ∉ A` (then `0 ∉ A`): the defect points
of `A − B` are the points of `A` right of the line and the point `1` (net multiplicity `−1`);
no point on the line has negative net multiplicity. By V5 the index of `W_A − W_B` is
`1 + #{points of A right of the line}`, and it is `≤ 1` on every family iff `A` has no point
right of the line. `1 ∉ A` for the zeros of `ζ` (`Re ρ < 1`). For a number field `K`: right of
`1` the completed Dedekind zeta function with its poles cleared is
`s (s − 1) · (discriminant factor) · (Gamma factor) · ζ_K(s)`; it is continuous, so its value
at `1` is the limit from the right, `(discriminant factor)(1) · (Gamma factor)(1) · res`, and
none of the three vanishes (class number formula).

**V8.** `K` a number field, `O` its ring of integers, `Λ_K(n) = Σ_{N𝔭^k = n} log N𝔭`.

(a) If `N𝔭^k = p^m`, `k ≥ 1`, then `N𝔭 ∣ p^m`, so `N𝔭 = p^d` with `d ≥ 1` (`N𝔭 ≠ 1`) and
`dk = m`. The pairs `(𝔭, k)` with `N𝔭^k = p^m` are in bijection with the pairs `(d, 𝔭)`, `d ∣ m`,
`N𝔭 = p^d`, by `k = m/d`, and `log N𝔭 = d log p`. So `Λ_K(p^m) = N_m(p) log p` with
`N_m(p) = Σ_{d ∣ m} d a_d(p)`, `a_d(p)` the number of primes of norm `p^d`. If `n` is not a prime
power, no `N𝔭^k` equals `n` (`N𝔭` is the order of a finite field) and `Λ_K(n) = 0`.

(b) Let `F` be a field with `p^m` elements. A homomorphism `φ : O → F` has a prime kernel `𝔭`;
`p ∈ 𝔭` (`F` has characteristic `p`), so `𝔭 ≠ 0` and `O/𝔭` is a finite field embedded in `F`.
Homomorphisms with kernel `𝔭` are the homomorphisms `O/𝔭 → F` (a homomorphism of fields is
injective). Finite fields: a field `E` with `p^d` elements has characteristic `p`; ring
homomorphisms `E → F` are `𝔽_p`-linear (the prime field has one homomorphism to any ring), so
they are the `𝔽_p`-embeddings: none unless `d = [E : 𝔽_p]` divides `m = [F : 𝔽_p]`, and then `d`
(Galois theory of finite fields, Mathlib). So the kernels are the primes of norm `p^d`, `d ∣ m`,
each with `d` homomorphisms: `#Hom(O, F) = N_m(p)`.

(c) For two number fields subtract the two limits of the pairing of the ideals at finite scale
(corpus: jets, counterterm and twice the contacts tend to `2c₀c₁ − Z_K(f)`). The contacts are
linear in the weight. The pole planes cancel; the limit is `Z_K(f) − Z_L(f)`. The form at finite
scale has `([L:ℚ] − [K:ℚ])` jets, `(r₂(L) − r₂(K))` conjugate jets, the counterterm
`log|d_L| − log|d_K|` and the contacts `(N_m^L(p) − N_m^K(p)) log p`.

(d) The ring of integers of `ℚ` is `ℤ`, with one homomorphism to every ring: `N_m(p) = 1`. So
over `ℤ` the contacts of a number ring are `(#Hom(O, 𝔽_{p^m}) − 1) log p`.

**V9.** `G` finite, `R` its virtual characters with the integer pairing `⟨·,·⟩`, `μ_q` the
characters induced from linear characters of subgroups, `q` in a finite set. Corpus: `θ ∈ R`
with `⟨θ, μ_q⟩ = 0` for all `q` is zero (restriction to cyclic subgroups).

(a) *A symmetric rational matrix `Γ` maps onto `(ker Γ)^⊥`.* `range Γ ∩ ker Γ = 0`: if
`Γ(Γc) = 0` then `(Γc)·(Γc) = c·Γ(Γc) = 0`, so `Γc = 0`. With rank and nullity,
`range Γ + ker Γ` is everything. Write `y = Γc + k`, `Γk = 0`. If `y ⟂ ker Γ`:
`0 = k·y = k·Γc + k·k = (Γk)·c + k·k = k·k`, so `k = 0`.

(b) `Γ_{qq'} = ⟨μ_q, μ_{q'}⟩`, `y_q = ⟨θ, μ_q⟩`. For rational `c` with `Γc = 0` take a common
denominator `N` and `z = Nc` integral: `η = Σ z_q μ_q` has `⟨η, μ_{q'}⟩ = N(Γc)_{q'} = 0`, so
`η = 0` and `N(c·y) = ⟨θ, η⟩ = 0`. By (a) `y = Γc`; with `z = Nc` integral,
`⟨Σ z_q μ_q − Nθ, μ_{q'}⟩ = N(Γc)_{q'} − N y_{q'} = 0` for all `q'`, so `Nθ = Σ z_q μ_q`.

The index of a virtual configuration counts points: where the net multiplicity is not zero
right of the line, where it is negative on the line. So `n` copies of two families have the
index of the families, and the index law of a character needs `nχ` in the monomial lattice
only. The integral statement (Brauer, `brauer_induction`) gives the function `L(s, χ)` itself as
a quotient; the index does not need it.

## Lean

Folder `formal/GaloisForLFunctions/AbsoluteGeometryOfSpecZ/`.

| Step | Module | Declarations |
|---|---|---|
| V1–V5 | `TheIndexOfAVirtualConfigurationCountsItsZerosAndItsPoles` | `lineZeros`, `pairDefect`, `negIndex_sub_zeroGram_le` (V1); `pairUnion`, `temperedConfig_pairUnion`, `signOf`, `twist`, `norm_twist`, `twist_single`, `sub_W_eq_inner` (V2); `hermQuad_le_of_near_diag`, `exists_sub_zeroGram_negIndex_ge` (V3); `extMult`, `netPart`, `disjoint_netPart`, `temperedConfig_netPart`, `sub_W_eq_netPart`, `pairDefect_netPart` (V4); `virtualDefect`, `negIndex_sub_zeroGram_le_virtualDefect`, `exists_le_negIndex_sub_zeroGram_iff`, `forall_negIndex_sub_zeroGram_eq_zero_iff` (V5) |
| V5 | `TheIndexOfAQuotientOfLFunctionsCountsItsZerosAndItsPoles` | `extMult_superposeFamily`, `exists_le_negIndex_quotient_iff`, `mem_virtualDefect_superposeFamily`, `exists_le_negIndex_relativeSquare_iff`, `forall_negIndex_relativeSquare_eq_zero_iff` |

| V7 | `TheNeutralPartIsWeilsFormOfTheZerosMinusThePoles` | `poleConfig`, `poleConfig_W`, `poleConfig_W_ofReal`, `virtualDefect_poleConfig`, `exists_le_negIndex_sub_poleConfig_iff`, `rightZeros_eq_empty_iff_forall_negIndex_sub_poleConfig_le_one`, `exists_le_negIndex_neutralGram_iff`, `riemannHypothesis_iff_forall_negIndex_neutralGram_le_one` |
| V7 | `TheNeutralFormOfANumberRingHasTheIndexOfItsZetaFunctionPlusOne` | `heckeXi_trivialModulus_one_ne_zero`, `one_notMem_dedekindZeros`, `exists_le_negIndex_dedekind_sub_poleConfig_iff`, `forall_negIndex_dedekind_sub_poleConfig_le_one_iff` |
| V8 | `TheContactsOfANumberRingAreItsPointCountsOverTheFiniteFields` | `ringHom_finiteField`, `kerEquivQuotientHom`, `primesOfNorm`, `fibrePointCount`, `idealContact_prime_pow`, `idealContact_eq_zero`, `natCard_ringHom_ker_eq`, `ker_mem_biUnion_primesOfNorm`, `natCard_ringHom_eq_fibrePointCount`, `idealContact_prime_pow_eq_natCard_ringHom`, `fibrePointCount_rat`, `ringForm_sub`, `relativeContact_prime_pow`, `relativeContact_rat_prime_pow`, `tendsto_relativeForm_add_relativeContact` |

| V9 | `RHTower/Artin/ArtinMonomialRationalSpan` | `exists_mulVec_eq_of_orthogonal_ker`, `exists_int_multiple`, `exists_nsmul_mem_closure_range`, `finite_linearCharacter`, `exists_nsmul_mem_closure_monomial` |
| V9 | `APowerOfAQuotientOfLFunctionsHasTheIndexOfTheQuotient` | `sum_extMult_power`, `virtualDefect_superposeFamily_power`, `exists_le_negIndex_power_iff` |

## Open

- V6. With reciprocity (the `L`-function of an induced linear character is a Hecke
  `L`-function) and V9, a power of `L(s, ρ)` of an Artin character is a quotient of products of
  Hecke `L`-functions; with Brauer's theorem (proved) `L(s, ρ)` itself is. The law reads: the index of `ρ` is the number of zeros and
  poles of `L(s, ρ)` right of the line plus the number of its poles on the line; Bézout for `ρ`
  is the Riemann hypothesis of `L(s, ρ)` with Artin's conjecture on the line.
- The pairing at finite scale of a virtual character with members that are not trivial
  characters (contacts `Σ n_i Re Λ_{ψ_i}`): follows from the Hecke case by linearity; stated for
  the relative square of two number rings (V8).

## Log
- 2026-11-12 — proved and formalized (V1–V5, V7, V8, V9)
