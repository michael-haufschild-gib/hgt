# The multiplicative dense model theorem — Lean programme

- **ID:** `MULT-DENSE-MODEL-LEAN-001`
- **Stage:** 1-in-progress
- **Type:** FORMALISATION PROGRAMME (single external proposition)
- **Serves:** `matomaki-teravainen-linnik-multiplicative-lean.md`, layer **L4.1** — the paper's
  Proposition 3.3, which produces the dense models `g^Δ` (Definition 5.3) and `g_k^Δ`
  (Definition 8.1) and so gates Lemmas 5.4, 5.7, 8.2, 9.2 and both main theorems.
- **Source:** Matomäki–Teräväinen, *Products of primes in arithmetic progressions*
  (arXiv:2301.07679), Proposition 4.1; the Linnik paper's Proposition 3.3 is the same statement
  with `I = (N/e, N]` in place of `[1, N]` and with item (v) specialised to index two.
- **RH used:** no · **Computation used:** no

## Why this is the right next target

Its proof is completely elementary — a Bohr-set pigeonhole, character orthogonality, and the mean
value theorem — with no sieve, no Burgess, no Halász.  Both of its analytic inputs are now owned:

| Input | State |
|---|---|
| character orthogonality mod `q` | **owned** — `RHTower/DirichletCharacterOrthogonality.lean` |
| mean value theorem for character sums (paper Lemma 3.7) | **owned** — `RHTower/CharacterSumMeanValue.lean`, `meanValue_charSum` |
| the identity (★) | **owned** — `HTGeometry/AdditiveCombinatorics/BohrAverage.lean`, `bohr_convolution_identity` |
| `∑_χ ‖∑_{b ∈ B} χ(b)‖² = φ(q)·#B` | **owned** — `RHTower/BohrSetCharacterSum.lean`, `sum_normSq_setCharSum` |

## The construction

Fix `q`, `N`, and `f : [N]_q → ℝ≥0` majorised by `ν` as in (A1), with large spectrum
```
T = { χ mod q : |E_{n ∈ [N]_q} f(n) χ̄(n)| ≥ δ } ,      #T ≤ C δ^{-r}   (A2),
```
and multiplicative Bohr set
```
B = { b ∈ ℤ_q^× : |χ(b) − 1| ≤ δ/5 for all χ ∈ T } .
```
The model is
```
g(a) = φ(q) · E_{b₁,b₂ ∈ B} E_{n ∈ [N]_q} f(n) · 𝟙[ n ≡ a b₁ b₂⁻¹ (mod q) ] .
```

**The one identity everything rests on.**  For every character `χ mod q`,
```
E_{a ∈ ℤ_q^×} g(a) χ̄(a)  =  |E_{b ∈ B} χ(b)|² · E_{n ∈ [N]_q} f(n) χ̄(n) .          (★)
```
Proof: expand the indicator by orthogonality and separate the `b₁`, `b₂` and `n` averages.

Given (★):
- **(iii)** is immediate, since `|E_{b∈B} χ(b)| ≤ 1`.
- **(iv)** is (★) at `χ = χ₀`.
- **(ii)** splits on `χ ∈ T`: off `T` the difference is `|Ê f(χ)|(1 − |·|²) ≤ δ`; on `T` every
  `b ∈ B` has `|χ(b) − 1| ≤ δ/5`, so `|E_{b∈B} χ(b)| ≤ 1 + δ/5` and the difference is at most
  `(1+η)((1+δ/5)² − 1) ≤ δ` for `η < 1`, `δ < 1/10`.
- **(i)** bounds `g` by the same expansion applied to `ν`, isolating `χ₀` and using
  `∑_χ |E_{b∈B} χ(b)|² = φ(q)/#B` (orthogonality) together with the lower bound on `#B`.
- **(v)** expands `𝟙[a ∈ bH]` over the characters trivial on `H` and applies (ii)/(iii)
  termwise; for `χ ∈ T` one uses that `χ` takes `Y`-th root of unity values and `δ < 1/(2Y)`,
  which forces `χ(b) = 1` on `B`, so (★) is an equality with factor `1`.

**Bohr set lower bound.**  Writing `T = {χ₁,…,χ_k}` with `k ≤ Cδ^{-r}`, pigeonhole the map
`a ↦ (χ₁(a),…,χ_k(a))` into `(100/δ + 1)^k` cells of the polydisc; some cell `A` has
`#A ≥ (100/δ+1)^{-k} φ(q)`, and `x, y ∈ A ⟹ x/y ∈ B`.  With
`δ > (10 C r log log q / (ε log q))^{1/r}` this gives `#B ≥ q^{1−ε/2}`.

## Layer plan

- **D0 — the key identity is DONE.**  `HTGeometry/AdditiveCombinatorics/BohrAverage.lean`,
  `bohr_convolution_identity`: for a unimodular multiplicative `ψ` on a finite commutative group
  and any `B`, `∑_a (∑_{b₁,b₂ ∈ B} F(a b₁ b₂⁻¹)) conj(ψ a) = (∑_B ψ)·conj(∑_B ψ)·∑_c F c conj(ψ c)`.
  This is (★) before normalisation, and it is stated group-theoretically, so no arithmetic enters.
- **D0'** Normalised character averages: `Ê_f(χ) = E_{n ∈ [N]_q} f(n) χ̄(n)` and
  `Ê_g(χ) = E_{a ∈ ℤ_q^×} g(a) χ̄(a)`, with the inversion formula for `𝟙[n ≡ a]`.
- **D1** The Bohr set `B` and its pigeonhole lower bound.  (The Parseval half,
  `∑_χ ‖∑_{b∈B} χ(b)‖² = φ(q)·#B`, is done: `sum_normSq_setCharSum`.)
- **D2** The identity (★).
- **D3** Items (i)–(v).  **(ii) (large-spectrum half), (iii) and (iv) are DONE** in
  `RHTower/DenseModelBohr.lean`: `denseModel`, `denseModel_fourier`, `denseModel_fourier_real`,
  `norm_denseModel_fourier_le`, `norm_sub_denseModel_fourier_le`, `denseModel_mass`,
  `norm_bohrAvg_sub_one_le`, `norm_sub_denseModel_fourier_le_of_close`.
  Left: (i) — needs Fourier inversion on `(ZMod q)ˣ` plus `∑_χ ‖E_B χ‖² = φ(q)/#B` (have the
  numerator) — and (v) — needs the character expansion of `𝟙[a ∈ bH]`.

## Gates
- [ ] 0 → 1  in-progress: statement frozen, inputs owned
- [ ] 1 → 2  fully-proven on paper
- [ ] 2 → 3  formalized, `lake build` green, axioms ⊆ {propext, Classical.choice, Quot.sound}

## Log
- 2026-08-21 — **items (ii) (large-spectrum half), (iii) and (iv) are Lean-proved** in
  `RHTower/DenseModelBohr.lean`, axiom-clean and wired.  All of them are corollaries of the single
  Fourier identity `denseModel_fourier`.
- 2026-08-21 — **the Parseval input is Lean-proved** as `sum_normSq_setCharSum`
  (`RHTower/BohrSetCharacterSum.lean`), axiom-clean and wired.  What remains for the proposition
  itself is the Bohr-set pigeonhole lower bound (D1), the transfer of (★) to the arithmetic
  normalisation (D0'), and the case analysis (i)–(v) (D3).
- 2026-08-21 — **(★) is Lean-proved** as `bohr_convolution_identity` in
  `HTGeometry/AdditiveCombinatorics/BohrAverage.lean` (axiom-clean, wired).  Items (ii)–(iv) of the
  proposition are formal consequences of it; (i) additionally needs
  `∑_χ |∑_{b ∈ B} χ(b)|² = φ(q)·#B`, which is `dirichletCharacterFamily_bilinear` at `f = g = 𝟙_B`
  together with `conj_char`; (v) additionally needs the character expansion of `𝟙[a ∈ bH]`.
- 2026-08-21 — created; source proof (MTE Prop 4.1) read in full and transcribed above.  Both
  analytic inputs are now in the tree, so this proposition is dependency-closed and is the highest
  value remaining item of the Linnik programme after Grynkiewicz G4.
