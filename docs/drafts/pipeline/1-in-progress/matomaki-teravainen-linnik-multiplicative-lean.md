# Linnik's problem for multiplicative functions (Matomäki–Teräväinen) — full Lean formalisation

- **ID:** `MT-LINNIK-MULT-LEAN-001`
- **Stage:** 1-in-progress
- **Type:** FORMALISATION PROGRAMME (whole-paper)
- **Source:** arXiv:2605.27833, Kaisa Matomäki & Joni Teräväinen, *Linnik's problem for
  multiplicative functions*, 27 May 2026.  Local copy of the LaTeX source was fetched and read in
  full (2238 lines, `main.tex`).
- **Statement:** For a multiplicative `h : ℕ → ℝ` with `h(p) ≠ 0` for `p ∤ q`, every reduced residue
  class mod `q` contains square-free `n₁, n₂ ≤ q^{2+ε}` with `h(n₁) < 0 < h(n₂)`, unless `sgn h`
  pretends to be a real character mod `q`.
- **RH used:** no
- **Computation used:** no

## Mandate

Formalise *every* numbered lemma / proposition / theorem / corollary of the paper, unconditionally
and closed (no hypotheses, no axioms), in this Lean corpus.  Where the paper cites an external
result, that external result must itself be formalised here unless mathlib already owns it.

## Inventory of the paper's numbered statements

Numbering is `\numberwithin{theorem}{section}`; environments share one counter.

| # | Label | Statement | External inputs it quotes |
|---|---|---|---|
| 1.1 | `thm:generaleasy` | `R(h;q) ≤ q^{2+ε}` unless quadratic pretence | 5.2, 5.4, 5.8, 5.9, 3.7, 3.11, 3.14, 3.6 |
| 1.2 | `thm:general` | `R(h;q) ≤ q² Q₁` unless quadratic pretence | 7.2, 8.2, 9.3, 9.4, 3.14, 3.10, 9.2 |
| 1.3 | `cor:Liouville` | `R(μ;q) ≪ q²(L(q)^100 + B(q)) ≪ q^{2+ε₀}` | 1.2, 4.1, Siegel, Mertens |
| 1.4 | remark | reduction of non-coprime `a` | — |
| 3.1 | `lemma:le:multfunctsigns` | lower bounds for `∑_{n≤y, h₀(n)≷0} χ₀(n)|μ(n)|` | 3.2; Halász (bgs Cor 2.2); GS distance (mrt Lem C.1) |
| 3.2 | `le:sieveworks` | square-free variant of Granville–Koukoulopoulos–Matomäki "When the sieve works", Thm 1 | GKM Thm 1, Hypothesis P, Prop 4.1, §6, Lem 2.1 |
| 3.3 | `prop:f=g+h` | multiplicative dense model theorem (i)–(v) | MatoTeraEkq Prop 4.1 |
| 3.4 | `le:Burgess` | Burgess / Pólya–Vinogradov character sum bound | iw-kow Thm 12.5; Heath-Brown Lem 2.4 |
| 3.5 | `le:fundsieve` | fundamental lemma of the sieve, `λ^±` | Friedlander–Iwaniec Lem 6.8 |
| 3.6 | `le:P2` | `≥ (1/2 − ε)` of `z`-rough numbers `≤ R` lie in any index-2 coset | 3.4, 3.5 |
| 3.7 | `le:MVT` | mean value theorem for character sums | orthogonality (Montgomery Thm 6.2) |
| 3.8 | `le:Hal-Mon` | Halász–Montgomery for character sums on rough numbers | MatoTeraEkq Lem 3.8(ii) |
| 3.9 | `le:largevalue` | large-value count for prime character sums | KMT Lem 6.5 |
| 3.10 | `le:convolution` | `(1_A * 1_B)(c) ≥ |A|+|B|−|G|`; coset form | MatoTeraEkq Lem 3.4 |
| 3.11 | `le:Kneser` | **Kneser's theorem** | Tao–Vu Thm 5.5 |
| 3.12 | `le:popularkneser` | popular-Kneser dichotomy | MatoTeraEkq Lem 6.1 (Grynkiewicz) |
| 3.13 | `le:structure` | small product set ⇒ index-2-ish stabilizer | MatoTeraEkq Lem 6.3 |
| 3.14 | `le:KneserAppl` | triple-convolution lower bound dichotomy | 3.10, 3.12, 3.13 |
| 4.1 | `le:QRupper` | lower bound for `∑_{n≤y, (n,P(q^ε))=1}(1∗ψ)(n)` | 3.5, MatoTeraEkq Lem 9.3, Siegel |
| 5.1 | `rem:ShapeS` | shape of integers counted by `S` | — |
| 5.2 | `le:reductiontoBoundingSEasy` | `S ≫ …` ⇒ `a ∈ E_h^Δ(q^{2+ε})` | 5.1, divisor bounds |
| 5.3 | `def:gDeltadef` | definition of `g^Δ` | 3.3 |
| 5.4 | `lemma:le:STcomparisonEasy` | `|S − T|` bound | 3.3, 3.7, 3.8, 3.9 |
| 5.5 | `re:Smallprole` | remark on the role of `p` | — |
| 5.6 | `def:ADelta` | `A^Δ := {g^Δ ≥ ε²}` | 5.3 |
| 5.7 | `le:Aprop` | `|A⁺|+|A⁻| ≥ (1−ε)φ(q)`; coset lower bound | 3.3, 3.5 |
| 5.8 | `prop:AAA->E1` | generic case ⇒ `E_h^± = ℤ_q^×` | 5.2, 5.4, 3.1, PNT |
| 5.9 | `prop:AAA->E2` | index-2 case ⇒ `E_h^± = ℤ_q^×` | 5.2, 5.4, 3.1, PNT |
| 6.1 | `le:squarecontr` | mean square of `p²m` character sums | 3.7 |
| 6.2 | `le:shortscontr` | mean square of short-interval `m` character sums | 3.7, 3.5 |
| 6.3 | `le:amplify` | `∑_χ |Q(χ)|^{2ℓ}|A(χ)|²` bound | KMT Lem 6.6 |
| 6.4 | `le:KL=amodq` | `#{kℓ ≡ a (q)} ≪ φ(q)KL/q² + q^{1/2+ε}` | Poisson; Kloosterman (Weil) |
| 7.1 | `rem:ShapeSgen` | shape of `n = r₁r₂r₃p₁um` | — |
| 7.2 | `le:reductiontoBoundingS` | general reduction to bounding `S` | 7.1, 6.4 |
| 8.1 | `def:gkDef` | `g_k^Δ` | 3.3 |
| 8.2 | `lemma:le:STcomparison` | general `|S − T|` bound | 8.3, 3.7, 3.8, 3.9, 6.3, 3.3 |
| 8.3 | `le:ChiSumMsplit` | replacing `M` by `M̃` | 8.4, 6.1, 6.2, 3.7 |
| 8.4 | `lemma:le:decomp` | Ramaré decomposition of `M_{bH,v}^Δ` | — |
| 9.1 | `def:AkDelta` | `A_k^Δ` | 8.1 |
| 9.2 | `le:Akdeltabasics` | `k`-indexed version of 5.7 | 3.3, 3.5 |
| 9.3 | `le:Tlower(iii)` | generic-case lower bound for `T` | 3.1, 3.5, PNT, Mertens |
| 9.4 | `le:Tlower(iv)` | index-2-case lower bound for `T` | 3.1, 3.5, PNT, Mertens |

## Layer plan (bottom-up); each layer is dependency-closed on the ones below it

**L0 — additive combinatorics in a finite abelian group.**  Self-contained, no analysis.
- `L0.1` convolution lower bounds (paper 3.10)  — elementary.
- `L0.2` **Kneser's theorem** (paper 3.11) — *absent from mathlib* (mathlib has only
  `Combinatorics/Additive/CauchyDavenport.lean`) and absent from this corpus.  Must be built.
- `L0.3` popular Kneser via Grynkiewicz (paper 3.12).
- `L0.4` structure lemma (paper 3.13).
- `L0.5` triple convolution dichotomy (paper 3.14).

**L1 — character sums mod q, second-moment layer.**
- `L1.1` mean value theorem (paper 3.7) from orthogonality.  The corpus already owns
  `RHTower.DirichletCharacterOrthogonality.dirichletCharacterFamily_orthogonality`.
- `L1.2` `le:squarecontr` (6.1), `le:shortscontr` (6.2).
- `L1.3` `le:amplify` (6.3).

**L2 — sieve layer.**
- `L2.1` fundamental lemma of the sieve with `λ^±` (paper 3.5).  mathlib has
  `NumberTheory/SelbergSieve.lean` only.
- `L2.2` `le:sieveworks` (3.2) — needs GKM.
- `L2.3` `le:P2` (3.6), `le:QRupper` (4.1).

**L3 — deep analytic inputs.**  Each is itself a major formalisation.
- `L3.1` Pólya–Vinogradov, then **Burgess** (3.4) — needs Weil's RH for curves over finite fields.
- `L3.2` **Weil bound for Kloosterman sums** for 6.4.
- `L3.3` quantitative **Halász** theorem (bgs Cor 2.2) + Granville–Soundararajan distance lemma.
- `L3.4` **Siegel's theorem** `L(1,ψ) ≫_δ q^{-δ}` for 1.3 and 4.1.
- `L3.5` Halász–Montgomery for character sums on rough numbers (3.8); large values (3.9).

**L4 — transference.**
- `L4.1` multiplicative dense model theorem (3.3).

**L5 — assembly.**  5.2, 5.4, 5.7–5.9, 7.2, 8.2–8.4, 9.2–9.4, then 1.1, 1.2, 1.3.

## Progress ledger

| Item | State | Lean module / theorem |
|---|---|---|
| L0.1 | — | |
| L0.2 | — | |
| L0.3 | — | |
| L0.4 | — | |
| L0.5 | — | |

## Log
- 2026-08-21 — created; paper source fetched and read end to end; inventory and layer plan written.
  Corpus/mathlib audit: Kneser absent from both; fundamental lemma of the sieve absent; Burgess
  absent (only exponent bookkeeping in `HTGeometry.SmoothMultiplicativeDichotomy`); character-sum
  MVT mod `q` absent (corpus MVT is for Dirichlet polynomials over ordinates).
