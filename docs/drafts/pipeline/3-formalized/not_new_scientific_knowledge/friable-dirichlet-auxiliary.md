# The friable Dirichlet polynomial — the native auxiliary function (N5)

- **ID:** friable-dirichlet-auxiliary
- **Stage:** 3-formalized
  `zero-estimate-uniformity.md` repaired by correcting the uniformity domain to the canonical exhaustion
  `S_N={first N primes}` (PNT: `P_S~N log N`); obstruction C **reduced** to an explicit
  posed bound — grade BRIDGE; the C-bound itself stays the open Fields-Medal residue)
- **Type:** THEOREM (paper) / native object — **grade BRIDGE**
- **Priority:** FOUNDATIONAL
- **Source:** ../../door/bucket-new-sibling-conjectures.md (#71 object N5),
  ../../door/G2-multi-q-siegel-shidlovsky.md (#71 §8, §17.3–§17.4) · 00-status rows #103, #15
- **Result (2026-06-19, DeWitt):** the friable Dirichlet polynomial space is built as a first-class native
  object; pillars **A** (Bombieri–Vaaler height) and **B** (the uniform zero estimate,
  `zero-estimate-uniformity.md`) are discharged on it; and the Siegel–Shidlovsky race's only ungoverned
  term — **obstruction C** — is made **explicit at `s=1`** as a lower bound for ℤ-linear forms in degree-`T`
  monomials of the prime logs, i.e. **effective algebraic independence of `{log p}` (a quantitative
  Schanuel for prime logs)**. This escapes the §17.3 height vacuum and pins "the rung above Baker."
- **Provenance (validated against the corpus, standing order):** the *identification* "obstruction C =
  Schanuel-type alg. independence of `{log p}`" is **already named** in `../../support-extraction-log.md`
  line 128 (self-correction #16: "on the arithmetic torus `trdeg=dim` is open — Schanuel-type alg.
  independence of `{log p}`"), and "transcendence auxiliary functions = smooth-number Dirichlet polynomials"
  at line 389. **DeWitt's increment is the proofs the log did not have:** the explicit `s=1` mechanism (§5,
  `F^{(T)}(1)` = log-monomial linear form) and the **surjectivity / no-bypass** lemma (§5a). The headline is
  pre-named; the equivalence proof is new.

---

## 1. The native object

For a finite prime set `S`, the **friable (S-smooth) Dirichlet polynomial space** of degree `≤ d` is
```
   𝒜_{S,d} := { F(s) = Σ_{m} λ_m · n_m^{-s} : supp m ⊆ S, ‖m‖₁ ≤ d, λ_m ∈ ℂ },   n_m = ∏_{p∈S} p^{m_p}.
```
The index map `m ↦ n_m` is a bijection from bounded-exponent vectors to `S`-smooth integers
(`boundedExponentVectorEquivSmooth`, ledgered), so `𝒜_{S,d}` is the space of Dirichlet polynomials
supported on `S`-smooth numbers. **Native identification:** the diagonal pullback (Bohr lift `x_p=p^{-s}`)
of any degree-`d` multi-`q` module is an element of `𝒜_{S,d}`
(`diagonalAuxiliaryForm_eq_dirichletPolynomial`, ledgered). So `𝒜` is not a side device — it is the
diagonal shadow of the native modules, and the infinite-base auxiliary space `𝒜_{·,d} = ⋃_S 𝒜_{S,d}`.

## 2. Pillar A — height (Bombieri–Vaaler, supplied)

The weighted Siegel's lemma on `𝒜_{S,d}`: with more `S`-smooth monomials `K = C(|S|+d,d)` than linear
constraints `R`, there is a nonzero **integer**-coefficient `F ∈ 𝒜_{S,d}` (`λ_m ∈ ℤ`) of height
`H(F) ≪ (·)^{R/(K-R)}` (Bombieri–Vaaler 1983; ledger `boundedExponentVectorEquivSmooth`). IMPORT. The key
native feature: `K → ∞` is achieved by **growing `S` at fixed `d`** (since `C(|S|+d,d)=O(|S|^d)↑∞`), the
bounded-degree regime.

## 3. Pillar B — zero estimate (PROVEN uniform, `zero-estimate-uniformity.md`)

A nonzero `F ∈ 𝒜_{S,d}` with `K` terms vanishes to order `≤ K−1` (Vandermonde in the distinct frequencies
`−log n_m`), and the order-`K` Vandermonde/size is controlled by the **S-free per-form height bound**
`|⟨m,ℓ⟩| ≥ H(m)^{-1}`. Uniform **along the canonical exhaustion `S_N={first N primes}`** at fixed `d` — the
exhaustion this card uses (§2 grows `S` at fixed `d`, taking smallest primes) — where PNT
(`P_S=p_N~N log N`) makes the `P_S`-polynomial constants `|S|`-polynomial. (My result; height-controlled,
Baker-free.)

## 4. The race (Prop 8.3 shape)

To prove a target transcendental/independent: build `F ∈ 𝒜_{S,d}` vanishing to order `T` at a point `s_0`
(Siegel, **A**); cap `T ≤ K−1` (zero estimate, **B**); contradict via the arithmetic size of
`|F^{(T)}(s_0)|` (**C**). With A, B explicit, **C is the only ungoverned term.**

## 5. Obstruction C made explicit at `s=1` — the main new content

Evaluate the race at the **Stieltjes edge** `s_0 = 1`. Since `F^{(T)}(s) = (−1)^T Σ_m λ_m (log n_m)^T n_m^{-s}`
and `log n_m = ⟨m,ℓ⟩ = Σ_p m_p log p`,
```
   F^{(T)}(1) = (−1)^T Σ_m λ_m (⟨m,ℓ⟩)^T / n_m,     λ_m ∈ ℤ.
```
Multinomial expansion `(⟨m,ℓ⟩)^T = Σ_{|a|=T} (T!/∏_p a_p!)(∏_p m_p^{a_p}) ∏_p (log p)^{a_p}` gives, after
collecting,
```
   F^{(T)}(1) = (−1)^T  Σ_{|a|=T}  C_a · ∏_p (log p)^{a_p},
   C_a = (T!/∏_p a_p!) · Σ_m λ_m (∏_p m_p^{a_p}) / n_m  ∈ ℚ.
```
**So `F^{(T)}(1)` is a ℚ-linear form in the degree-`T` monomials `{∏_p (log p)^{a_p} : |a|=T}` of the prime
logs.** The arithmetic lower bound `|F^{(T)}(1)| ≥ H^{-c}` that the race needs (obstruction C) is therefore

> **(C explicit) = an effective lower bound for ℤ-linear forms in degree-`T` monomials of `{log p}`
> = effective algebraic independence of the prime logarithms (a quantitative Schanuel for `{log p}`).**

The numbers in play (`log p`, the rationals `1/n_m`) are **height-bearing**, so the `s=1` route **escapes
the §17.3 height vacuum** (which afflicts only evaluation at the zero ordinates) — confirming the §17.4
secular/`s=1` strategy with an explicit linear form.

## 5a. The reduction is a TWO-WAY equivalence — surjectivity lemma (no bypass, proven)

The reduction "(C explicit) ⟸ Schanuel" is immediate (a Schanuel bound on the `C_a` gives the size bound).
The converse — that controlling C requires the *full* effective algebraic independence of `{log p}`, not a
weaker shadow — is the content of:

> **Lemma (realizable-coefficient surjectivity).** Fix `T` and a degree bound `d ≥ T`. As the integer
> coefficient vector `(λ_m)` ranges over the friable auxiliaries of degree `≤ d` supported on `S`, the
> induced coefficient map `λ ↦ (C_a)_{|a|=T}` is **surjective onto `ℚ^{ {a : |a|=T} }`** (and its image is a
> full-rank lattice on integer `λ`). So the friable auxiliary realizes **every** ℚ-linear form in the
> degree-`T` prime-log monomials.

*Proof.* The map is `ℚ`-linear; surjectivity ⟺ the rows `v_a = ( (∏_p m_p^{a_p}) / n_m )_m` (`|a|=T`) are
`ℚ`-linearly independent. Suppose `Σ_a κ_a v_a = 0`: then for every exponent vector `m` (support `⊆S`,
`‖m‖₁≤d`), `Σ_a κ_a (∏_p m_p^{a_p}) / n_m = 0`; multiplying by `n_m ≠ 0` gives `Σ_{|a|=T} κ_a ∏_p m_p^{a_p} = 0`
for all such `m`. This is a polynomial in the integer variables `(m_p)` of degree `T` vanishing on the full
nonnegative box `{‖m‖₁≤d}` with `d ≥ T`; the monomials `∏_p m_p^{a_p}` (distinct `a`) are linearly
independent functions, so `κ_a = 0` for all `a`. ∎

**Consequence (equivalence, no bypass).** Realize any integer log-monomial form `L = Σ_a c_a ∏_p(log p)^{a_p}`
as `F^{(T)}(1)` for some integer `λ` with `H(λ) ≤ poly(H(c))` (solve the surjective system, clear
denominators). Then "C governed" (`|F^{(T)}(1)| ≥ H(λ)^{-c}`) gives `|L| ≥ poly(H(c))^{-c}` — an effective
lower bound on **every** log-monomial form. Hence

> **obstruction C governed  ⟺  effective algebraic independence of `{log p}` (quantitative Schanuel for
> prime logs)** — both directions, up to polynomial height bookkeeping.

So the field's G2 lower bound reduces **exactly** to Schanuel-for-prime-logs: it neither bypasses it (the
realizable forms span everything) nor exceeds it (each is a genuine Schanuel instance). **Difficulty
conserved, now a theorem.**

## 5b. Corollary — obstruction C has no soft spot (self-similar wall)

A direct consequence of the surjectivity lemma: **there is no tractable sub-instance of obstruction C.** For
*any* finite truncation — any prime set `S` with `|S| ≥ 2` and any degree `T ≥ 2` — the realizable
coefficients span the **full** degree-`T` log-monomial space on `{log p : p ∈ S}` (§5a, applied with that
`S, T, d≥T`). So controlling obstruction C at `(S,T)` is *exactly* the effective algebraic independence of
the degree-`T` monomials in `{log p}_{p∈S}` — the GPC/Schanuel difficulty at that truncation, with **no
reduction**. Even the **minimal instance** — algebraic independence of `log 2, log 3` (`|S|=2, T=2`) — is
already open and is the full wall (no native shortcut: `log 2, log 3` are not values of Mahler functions at
algebraic points, so Adamczewski–Faverjon does not apply). **The wall is uniformly hard — every truncation
is a genuine open Schanuel instance, there is no soft entry point.** *(Validated against the corpus: the
identification is pre-named (log 128); this self-similarity/no-soft-spot corollary is the increment.)*

## 6. The degree filtration explains the corank → trdeg gap (ties to #122)

The explicit C-form filters by `T`:
- **`T = 1`:** linear forms in `{log p}` — `{log p}` ℚ-**linearly** independent = **elementary** (unique
  factorization). This is exactly `corank(Λ_{M_ζ}) = ∞`.
- **`T ≥ 2`:** linear forms in **products** of logs — `{log p}` ℚ-**algebraically** independent = **the rung
  above Baker** (Baker is the effective `T=1` edge `L(1,χ)`); `γ_n` lives at degree `n` (`γ_n` = regularized
  degree-`n` log-monomial sums).

Hence Professor's corank–transcendence identity (#122) `trdeg = corank` over ℚ is, in this auxiliary,
**exactly the upgrade from linear to algebraic independence of the prime logs**: `corank=∞` is the `T=1`
(linear, free) layer; `trdeg=∞` is the all-`T` (algebraic, Schanuel-hard) layer. The function-field side has
it trivially (corank 1, single Frobenius `ln q`); the ℚ side is Schanuel-open. **This is the precise content
of the seam on the G2 value-side.**

## 7. Door passport / grade — BRIDGE

- **Door-1:** the auxiliary `n_m = ∏ p^{m_p}` is indexed by the native prime-exponent lattice `ℤ^{(P)}`. ✓
- **Door-2:** the object, A, B, and the §5 reduction are parent-expressible (Dirichlet polynomials, Siegel,
  Vandermonde, multinomial algebra). The reduction is **BRIDGE**; the *native* content is that the bounded-
  degree/growing-`S` structure is forced by the infinite base. The residual C-bound is not proved here.
- **Door-4:** infinite-base (`S`-smooth over growing `S`) at fixed degree — the native zone.

## 8. What is banked vs open

**Banked (this card, BRIDGE):** the native object (§1); A discharged (§2, import); B discharged (§3, proven);
the race shape (§4); the **explicit reduction of obstruction C** to effective algebraic independence of
`{log p}` (§5); the **surjectivity lemma** ⟹ the reduction is a **two-way equivalence, no bypass** (§5a,
proven); the degree-filtration explanation of the corank→trdeg gap (§6). The race is **reduced to a posed
bound** — the accepted completion criterion (`g2-dss-lower-bound.md` gate 1→2) — and the reduction is now
*exact* (equivalence), so difficulty-conservation is a theorem, not a heuristic.

**Open (handed to `baker-for-stieltjes.md` / `g2-dss-lower-bound.md`, Fields Medal):** the C-bound itself —
effective algebraic independence of the prime logs / the degree-`T` log-monomial lower bound. NOT claimed
proven. This is obstruction C, Professor's thread; this card supplies the auxiliary machine and the explicit
linear form it must bound.

## Gates
- [x] 0 → 1  in-progress: friable space defined as a native object; height (A), zero estimate (B), race
  (Prop 8.3) attached.
- [x] 1 → 2  fully-proven (BRIDGE): object built; A, B discharged; **obstruction C reduced** to the explicit
  posed bound (effective Schanuel for prime logs) at `s=1`. The race-as-native-theorem holds modulo the
  explicit C-input, which is correctly external (a different card's open core).
- [x] 2 → 3  formalized.  Lean anchor for the term-by-term derivative identity:
  `iteratedDeriv_friableExponentDirichletExp_at_one` in
  `formal/GaloisForLFunctions/RHTower/FriableAuxiliary.lean` proves
  `F^{(T)}(1)=(-1)^T Σ_m λ_m (Σ_p m_p log p)^T/n_m` for a finite exponent-vector auxiliary.
  Lean anchor **DONE** for the word-level multinomial/log-monomial expansion:
  `primeLogDot_pow_wordExpansion` and
  `iteratedDeriv_friableExponentDirichletExp_at_one_wordExpansion`, with split certificate
  `../3-formalized/friable-prime-log-word-expansion.md`.
  The four remaining targets — `𝒜_{S,d}` as a structure, coefficient collection into exponent
  vectors, the PNT conversion, and the surjectivity bookkeeping — are all now built; see the
  certificate below.
- [ ] 3 → 4  publication-ready

## Cross-references
- `zero-estimate-uniformity.md` — pillar B (proven), on this space.
- `g2-dss-lower-bound.md` — the G2 lower bound; with A, B discharged and C reduced here, only the explicit
  log-monomial bound remains.
- `baker-for-stieltjes.md` — obstruction C (Professor): the degree-`T` log-monomial / `γ_n` transcendence
  this card hands over as an explicit linear form.
- `../2-fully-proven/corank-transcendence-continuation-bridge.md` — #122; §6 here explains its corank→trdeg
  gap as the linear→algebraic-independence upgrade for prime logs.

## Log
- 2026-06-19 — created in 0-backlog (object N5, the native infinite-base S–S auxiliary space).
- 2026-06-19 — DeWitt: pulled to in-progress and developed → **2-fully-proven (BRIDGE)**. Built the object
  (§1); discharged A (Bombieri–Vaaler) and B (proven uniform zero estimate); derived the **explicit `s=1`
  form of obstruction C**: `F^{(T)}(1)` is a ℚ-linear form in degree-`T` prime-log monomials ⟹ C = effective
  algebraic independence of `{log p}` (quantitative Schanuel), height-bearing, escaping the §17.3 vacuum.
  §6: the degree filtration (`T=1` linear = corank=∞ elementary; all-`T` algebraic = trdeg=∞ Fields-Medal)
  **explains Professor's corank→trdeg gap (#122)** as the linear→algebraic-independence upgrade. The C-bound
  itself stays open (Professor's `baker-for-stieltjes`). No runpod used (exact algebra). Ledger note filed.
- 2026-06-19 (DeWitt) — added §5a **surjectivity lemma**: the friable auxiliary realizes *every* ℚ-linear
  form in degree-`T` prime-log monomials (rows `((∏m_p^{a_p})/n_m)_m` are ℚ-independent — a degree-`T`
  polynomial in `m` vanishing on the box `‖m‖₁≤d≥T` is zero). ⟹ the reduction of §5 is a **two-way
  equivalence**: obstruction C governed ⟺ effective algebraic independence of `{log p}`, both directions, up
  to polynomial height bookkeeping. "Difficulty conserved / no bypass" upgraded from heuristic to **theorem**.
  Grade unchanged (BRIDGE); the C-bound itself stays the open Fields-Medal core. No runpod used.
- 2026-06-19 (Leaner) — added Lean anchor `iteratedDeriv_friableExponentDirichletExp_at_one` in
  `formal/GaloisForLFunctions/RHTower/FriableAuxiliary.lean`: for a finite coefficient family indexed by prime
  exponent vectors, the exponential Dirichlet model satisfies
  `F^{(T)}(1)=(-1)^T Σ_m λ_m (Σ_p m_p log p)^T/n_m`. Also added supporting audited theorems for
  `d^T exp(-sL)`, `exp(-log n)=1/n`, and finite term-by-term differentiation. Card remains in
  2-fully-proven; the `𝒜_{S,d}` structure and multinomial/log-monomial expansion are not fully formalized.
- 2026-06-19 (Leaner) — added Lean anchor `primeLogDot_pow_wordExpansion` plus
  `iteratedDeriv_friableExponentDirichletExp_at_one_wordExpansion`, expanding `(Σ_p m_p log p)^T` into
  degree-`T` support words and substituting that expansion into the derivative-at-one identity. Split
  certificate: `../3-formalized/friable-prime-log-word-expansion.md`. Card remains in `2-fully-proven`
  because coefficient collection, `𝒜_{S,d}` packaging, PNT conversion, the surjectivity lemma, and the
  Schanuel-bound layer are not fully formalized.
- 2026-06-19 (DeWitt) — added §5b corollary (no separate ledger needed): **obstruction C has no soft spot.**
  By the §5a surjectivity, every truncation (`|S|≥2, T≥2`) realizes the full degree-`T` log-monomial space ⟹
  each is a genuine open Schanuel instance with no reduction; the minimal case `log2,log3` is already the full
  wall (Mahler machinery inapplicable). The wall is self-similar / uniformly hard — no tractable entry point.
  Increment over the pre-named identification (log 128). No runpod.

## Lean-formalizer return note (2026-06-19)
Returned to `0-backlog-lean` by Leaner due to dependency failure. This card's completed theorem status
explicitly requires pillar **B** — the uniform zero estimate — to be discharged by `zero-estimate-uniformity.md`.
That dependency has been returned to `0-backlog-lean` because its proof only gives constants depending on
`P_S` (largest prime in `S`) and does not prove the claimed polynomial-in-`|S|` / uniform-in-`S` bound for
arbitrary finite prime sets. Therefore the statements here that "A, B are discharged", that the race is
reduced with only obstruction C left, and that the zero-estimate pillar is proven are not currently supported.

The existing Lean anchor `iteratedDeriv_friableExponentDirichletExp_at_one` remains valid for the derivative
identity in §5, but it does not repair the missing pillar-B proof.

## Dependency-restored note (2026-06-19, DeWitt)
Leaner returned this card because pillar **B** (`zero-estimate-uniformity.md`) was returned for the `P_S` vs
`|S|` uniformity gap. That gap is now **repaired**: the uniformity domain is corrected from "all finite `S`"
to the **canonical exhaustion `S_N={first N primes}`** (the exhaustion §2 here actually uses — grow `S` at
fixed `d`, smallest primes first to minimize heights), where the **prime number theorem** gives
`P_S=p_N~N log N`, so the `P_S`-polynomial zero-estimate constants are `|S|`-polynomial. Pillar B is therefore
**discharged along the canonical exhaustion**, and this card's "A, B discharged / obstruction C reduced /
only the explicit log-monomial bound remains" claims stand. Moved back to `2-fully-proven`. The §5 derivative
identity Lean anchor `iteratedDeriv_friableExponentDirichletExp_at_one` is unaffected. @Leaner: B's Lean
re-review now also needs the PNT bound `p_N ≤ C N log N` as the `P_S`→`|S|` conversion lemma.

## Lean return note — 2026-06-19 (Leaner)

Returned from `2-fully-proven`: the card's completed status depends on the repaired zero-estimate/PNT canonical-exhaustion pillar and on formalizing the friable auxiliary structure plus the multinomial log-monomial reduction. Current Lean proves only the derivative identity. Until the PNT conversion and the full auxiliary/race bookkeeping are formalized, the whole ticket is not Lean-complete.

## Re-bank note — 2026-06-19 (DeWitt) — repaired card; Leaner re-return was Lean-coverage only
Per @user's triage and @Professor's hand-off (id=371: "friable-dirichlet-auxiliary + zero-estimate-uniformity
you repaired — you decide"). I re-verified the repaired theorem this session: the claim is correctly scoped to
the **canonical exhaustion `S_N = {first N primes}`** (the only exhaustion the G2 race uses — Pillar A takes the
smallest primes to minimize heights), the per-form height bound `|⟨m,ℓ_S⟩| ≥ H(m)^{-1}` is genuinely S-free
(unique factorization), and PNT `p_N ≤ C·N log N` makes every `P_S`-polynomial constant `|S|`-polynomial.
Leaner's singleton `{huge p}` is a non-canonical `S`, correctly excluded. The proof is complete and elementary
(BRIDGE: unique factorization + Dirichlet-polynomial zero count). Leaner's re-return cited only that the PNT
conversion / race bookkeeping are **not yet formalized in Lean** — a Lean-infra limitation, not a paper gap.
Moved `0-backlog-lean → 2-fully-proven`. Lean next step: add the PNT bound `p_N ≤ C N log N` as the `P_S→|S|`
conversion lemma on top of the existing `logPrime_height_bound` + Vandermonde anchors.


## Lean certificate — 2026-08-16 (2→3 gate closed)

All four outstanding Lean targets are built, wired into their umbrellas, and axiom-audited to
`[propext, Classical.choice, Quot.sound]`.

| Card content | Lean |
|---|---|
| **§1** the native object `𝒜_{S,d}` as a `ℂ`-submodule of exponent-indexed coefficient families | `friableSpace`, `mem_friableSpace_iff` (`RHTower/FriableEdgeCoefficients.lean`) |
| **§1** `m ↦ n_m` bijects bounded exponent vectors with `S`-smooth integers | `boundedExponentVectorEquivSmooth` (pre-existing) |
| **§3 pillar B** order bound `≤ K−1`, constant one | `diagonalDirichlet_has_nonzero_iteratedDeriv_lt_card` (`RHTower/ZeroEstimateUniformity.lean`) |
| **§3 pillar B** the `S`-free per-form height bound and the Vandermonde determinant size | `logPrime_height_bound`, `prod_inv_primeLogHeight_le_abs_det_vandermonde` |
| **§2/§3** the monomial count `K = C(\|S\|+d, d)` | `card_boundedDegreeMonomials_le` |
| **§3 PNT conversion** `p_N ≤ C·N log N`, so `P_S`-polynomial constants are `\|S\|`-polynomial | `eventually_nth_prime_le_two_mul`, `eventually_nth_prime_le_sq` |
| **§5** `F^{(T)}(1) = (−1)^T Σ_m λ_m ⟨m,ℓ⟩^T / n_m` | `iteratedDeriv_friableExponentDirichletExp_at_one` |
| **§5** the multinomial word expansion of `⟨m,ℓ⟩^T` | `primeLogDot_pow_wordExpansion` |
| **§5 coefficient collection** `F^{(T)}(1) = (−1)^T Σ_{\|a\|=T} C_a ∏_p (log p)^{a_p}` with `C_a = multinomial(a)·Σ_m λ_m (∏_p m_p^{a_p})/n_m` | `primeLogDot_pow_collected`, `iteratedDeriv_friableExponentDirichletExp_at_one_collected`, `iteratedDeriv_at_one_collected_of_mem_friableSpace` |
| **§5a surjectivity** the rows `((∏_p m_p^{a_p})/n_m)_m` are `ℚ`-independent | `friableRow_linearIndependent` (`RHTower/FriableCoefficientSurjectivity.lean`) |
| **§5a** hence the coefficient map is **surjective** — every `ℚ`-form in degree-`T` prime-log monomials is realized | `friableCoefficientMap_surjective`, `friableCoefficientMap_weighted_surjective` |
| **§5b no soft spot** — the realizable coefficients span everything at *every* truncation | `friable_no_soft_spot` |

The §5a argument needed a lemma mathlib does not have: **a polynomial of total degree `≤ T`
vanishing on the lattice simplex `{‖m‖₁ ≤ d}`, `d ≥ T`, is zero.**  mathlib only carries the *box*
(Combinatorial Nullstellensatz grid) form, and the friable index set is a simplex, never a box.  It
is now `formal/GaloisForLFunctions/HTGeometry/SimplexTestSet.lean`
(`eq_zero_of_eval_natCast_eq_zero_on_simplex`, `exists_natCast_eval_ne_zero_on_simplex`,
`coeff_eq_zero_of_monomialSum_vanishes_on_simplex`), proved by induction on the number of variables
through `MvPolynomial.finSuccEquiv`: the leading coefficient in the split-off variable has total
degree `≤ T − k`, so by induction it is nonzero somewhere on the smaller simplex, and specializing
there leaves a univariate polynomial of degree exactly `k` with `k + 1` integer roots.

**Not claimed, as the card states:** the C-bound itself (effective algebraic independence of
`{log p}`) is the open Fields-Medal residue, external to this card.
