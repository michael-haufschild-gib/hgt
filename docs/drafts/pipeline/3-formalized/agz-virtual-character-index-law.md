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
- [ ] V6 Brauer's theorem and the identification of induced characters with Hecke characters
- [x] V7 zeros minus poles: the neutral form of `ℤ` and of every number ring has index one plus
  the number of zeros right of the line
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

## Lean

Folder `formal/GaloisForLFunctions/AbsoluteGeometryOfSpecZ/`.

| Step | Module | Declarations |
|---|---|---|
| V1–V5 | `TheIndexOfAVirtualConfigurationCountsItsZerosAndItsPoles` | `lineZeros`, `pairDefect`, `negIndex_sub_zeroGram_le` (V1); `pairUnion`, `temperedConfig_pairUnion`, `signOf`, `twist`, `norm_twist`, `twist_single`, `sub_W_eq_inner` (V2); `hermQuad_le_of_near_diag`, `exists_sub_zeroGram_negIndex_ge` (V3); `extMult`, `netPart`, `disjoint_netPart`, `temperedConfig_netPart`, `sub_W_eq_netPart`, `pairDefect_netPart` (V4); `virtualDefect`, `negIndex_sub_zeroGram_le_virtualDefect`, `exists_le_negIndex_sub_zeroGram_iff`, `forall_negIndex_sub_zeroGram_eq_zero_iff` (V5) |
| V5 | `TheIndexOfAQuotientOfLFunctionsCountsItsZerosAndItsPoles` | `extMult_superposeFamily`, `exists_le_negIndex_quotient_iff`, `mem_virtualDefect_superposeFamily`, `exists_le_negIndex_relativeSquare_iff`, `forall_negIndex_relativeSquare_eq_zero_iff` |

| V7 | `TheNeutralPartIsWeilsFormOfTheZerosMinusThePoles` | `poleConfig`, `poleConfig_W`, `poleConfig_W_ofReal`, `virtualDefect_poleConfig`, `exists_le_negIndex_sub_poleConfig_iff`, `rightZeros_eq_empty_iff_forall_negIndex_sub_poleConfig_le_one`, `exists_le_negIndex_neutralGram_iff`, `riemannHypothesis_iff_forall_negIndex_neutralGram_le_one` |
| V7 | `TheNeutralFormOfANumberRingHasTheIndexOfItsZetaFunctionPlusOne` | `heckeXi_trivialModulus_one_ne_zero`, `one_notMem_dedekindZeros`, `exists_le_negIndex_dedekind_sub_poleConfig_iff`, `forall_negIndex_dedekind_sub_poleConfig_le_one_iff` |

## Open

- V6. With Brauer's theorem and reciprocity, `L(s, ρ)` of an Artin character is a quotient of
  products of Hecke `L`-functions and the law reads: the index of `ρ` is the number of zeros and
  poles of `L(s, ρ)` right of the line plus the number of its poles on the line; Bézout for `ρ`
  is the Riemann hypothesis of `L(s, ρ)` with Artin's conjecture on the line.
- The pairing of a virtual character at finite scale on the comb (contacts
  `Σ n_i Re Λ_{ψ_i}`): follows from the Hecke case by linearity; not stated.

## Log
- 2026-11-12 — proved and formalized (V1–V5, V7)
