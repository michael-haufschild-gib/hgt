# The friable log-moment ladder lands in a fixed finite-dimensional period space at every weight `T`

- **ID:** friable-moment-ladder-finite-dim
- **Stage:** 2-fully-proven (proven on paper; Lean-ready core in §A)
- **Type:** THEOREM (paper), **BRIDGE**. Two proven structural facts about the friable log-moment construction.
- **Priority:** FOUNDATIONAL (structural input to the exponential column of DSS-cross).
- **Owner:** Wheeler
- **Replaces:** the withdrawn `friable-moment-ladder-nogo` (its no-go **Corollary A was not proven** — see the
  correction box below). This card banks only the genuinely-proven, Lean-ready residue.

---

## Correction (why this card exists — the no-go is withdrawn, not banked)

The predecessor claimed a **no-go**: "finite-dimensional containment ⟹ no irrationality/transcendence measure
for `γ_E`." **That implication is false**, as Leaner correctly noted (2026-06-19): a fixed finite-dimensional
ℚ-space can contain sequences of arbitrarily small linear forms.
- *Witness:* Apéry's `ζ(3)` irrationality runs entirely inside the **2-dimensional** span `⟨1, ζ(3)⟩`; the
  integer forms `a_n + b_nζ(3)` decay geometrically and beat their denominators. Likewise continued-fraction
  convergents give small forms in `⟨1, α⟩` for any irrational `α`.

So finite-dimensionality alone is **not** an obstruction. The no-go would need an explicit
height/denominator lower bound on `γ_E`-retaining forms — which the predecessor did **not** supply, and which
is itself an open Diophantine question (it implies `γ_E ∉ ℚ`, open since Euler 1734). **That conjecture is not
decided here**; it remains the open second conjunct of DSS-cross and lives, honestly marked open, in
`../1-in-progress/relative-exponential-apex.md` §8/§16 (where the *single-integral* Padé family is shown to
fail numerically — `den·err→∞`, `n≤22` — strong evidence, not a proof for all combinations).

**What is banked here:** the two facts that genuinely *are* proven and Lean-ready — Theorem A (finite-dim
landing) and Theorem B (function-transcendence ⇏ value-transcendence). Neither asserts a no-go.

---

## §A Theorem A — the finite-dimensional moment-ladder theorem `[PROVEN; Lean-ready]`

**Setup.** Fix a finite prime set `S` and the friable measure `dμ_S = Σ_{n\ S\text{-smooth}} e^{−nx}\,dx`,
`ζ_S(s) = ∏_{p∈S}(1−p^{−s})^{−1} = Σ_{n\ S\text{-smooth}} n^{−s}`. Define the normalized log-moments
```
   M_j^{(T)} := \frac{∫_0^∞ x^j (\log x)^T\,dμ_S}{j!\,ζ_S(j+1)},   j = 0,1,2,…,  T = 0,1,2,….
```

**Theorem A.** For every finite `T`, all `M_j^{(T)}` (`j ≥ 0`) lie in the single **finite-dimensional**
ℚ-vector space
```
   V_T := \mathrm{span}_ℚ\{ γ_E^{a}\,ζ(2)^{b_2}\!\cdots ζ(T)^{b_T}\,(\log 2)^{c_2}(\log 3)^{c_3}\cdots :
                            a + 2b_2 + 3b_3 + \cdots + c_2 + c_3 + \cdots ≤ T \}.
```
`\dim V_T < ∞` holds **unconditionally** (the span is contained in an explicit finite monomial set,
irrespective of any ℚ-independence conjecture among those monomials).

*Proof.* Substitute `u = nx` in each `∫_0^∞ x^j(\log x)^T e^{−nx}dx`:
```
   ∫_0^∞ x^j(\log x)^T e^{−nx}dx = n^{−(j+1)} \sum_{t=0}^T \binom{T}{t} Γ^{(t)}(j+1)\,(\log n)^{T−t}\,(−1)^{T−t}.
```
By Faà di Bruno / the Bell-polynomial identity for `(\log Γ)`, `Γ^{(t)}(j+1) = j!\,B_t(ψ,ψ',…,ψ^{(t−1)})(j+1)`,
a polynomial with ℚ-coefficients in the values `ψ^{(k)}(j+1)`. At the integer point,
```
   ψ(j+1) = H_j − γ_E,    ψ^{(k)}(j+1) = (−1)^{k+1} k!\,(ζ(k+1) − H_j^{(k+1)})  (k ≥ 1),
```
so `Γ^{(t)}(j+1)/j!` is a `ℚ[\,H_j, H_j^{(2)},…\,]`-linear combination of monomials `γ_E^{a}ζ(2)^{b_2}\cdots ζ(t)^{b_t}`
of weight `≤ t`. Summing over `S`-smooth `n` and using `\sum_n n^{−s}(\log n)^m = (−1)^m ζ_S^{(m)}(s)`,
```
   M_j^{(T)} = \sum_{t=0}^T \binom{T}{t}\,\frac{Γ^{(t)}(j+1)}{j!}\,\frac{ζ_S^{(T−t)}(j+1)}{ζ_S(j+1)},
```
and `(ζ_S^{(m)}/ζ_S)(j+1)` is a `ℚ[j]`-polynomial in `{\log p : p∈S}` (each `\log ζ_S = Σ_{p}Σ_{k}p^{−ks}/k`,
so its derivatives at integer `s` are rational combinations of `\log p` via `p^{−s}/(1−p^{−s})` and its
derivatives — rational at integer `s`). Hence each `M_j^{(T)}` is a ℚ-linear combination of the stated
weight-`≤T` monomials. The monomial set is finite, so `\dim V_T < ∞`. ∎

**Numerical certification (artifact-safe).**
- `T=1`: `M_j = H_j − γ_E + r2_j\log2 + r3_j\log3` (`r∈ℚ`), `γ_E`-coeff `≡ −1`; `⟨1,γ_E,\log2,\log3⟩`,
  4-dim (verified dps=80; the dps=60 "relation" of `relative-exponential-apex` §14 vanished at dps=150/250 — spurious).
- `T=2`: 11-dim; closed form `=` direct friable summation (machine-zero, `j≥1`); `M_j^{(2)} =` predicted
  coefficient vector (machine-zero, `j=0..6`); PSLQ `j=0` returns exactly `3×` predicted (basis complete).
- `T=3`: closed form `=` monomial expansion in `{γ_E,ζ(2),ζ(3),\log2,\log3}` (machine-zero, `j=0..5`); the
  new weight-3 transcendental `ζ(3)` enters exactly as predicted; finite per weight.
- Archive: `computations/2026-06-19-wheeler-friable-moment-ladder-nogo.txt`, `…-friable-T2-secondmoment.py`,
  `…-friable-T3-thirdmoment.py` (and `…-friable-bypass-test.txt` for `T=1`).

**What Theorem A does and does not give.** It pins the *period content* of the friable moment family to a fixed
finite monomial basis per weight (a clean structural fact). It does **not** bound the heights of ℚ-combinations,
so — by the correction box — it carries **no** no-go. It is exactly the structural premise that a future
height-lower-bound argument (if one exists) would build on.

## §B Theorem B — difference-Galois function-transcendence ⇏ value-transcendence `[PROVEN, elementary]`

`relative-exponential-apex` §2 proves (van der Put–Singer): the digamma `ψ` is a non-rational `𝔾_a`-primitive
(transcendental over `ℂ(s)`, satisfying `σψ−ψ=1/s`, `1/s` not `σ`-summable). The apex wants the **value**
`γ_E = −ψ(1) ∉ \overline{𝓡}`.

**Theorem B.** Function-transcendence of `ψ` over `ℂ(s)` carries **no** information about the arithmetic nature
of the specialized value `ψ(1)`. *Proof.* Specialization `s ↦ 1` is a ring map out of the Picard–Vessiot ring
that is **not** difference-Galois-equivariant; the Galois group acts on the abstract primitive, not on its value
at a point. Witness (elementary, sufficient to defeat the implication): `\log s` is a primitive transcendental
over `ℂ(s)`, yet `\log 1 = 0 ∈ ℚ`. ∎

This is exactly the `F₁` value-lift wall of `relative-exponential-apex` §3, stated as a theorem: the missing
ingredient is genuinely arithmetic (a measure / a realization-injectivity), not group-theoretic.

## Door / grade
- **Door-2.** Theorem A is the Bell-polynomial/specialization structure of a classical moment family (single
  parent: gamma-integral asymptotics + `ζ_S`-derivatives) ⟹ **BRIDGE**. Theorem B is van der Put–Singer +
  elementary specialization ⟹ **BRIDGE**. Neither is native/C5; both are structural facts the native apex
  must build past.
- **Door-5.** Over `F_q(C)` the value-lift exists (single Frobenius, `K=1`), so the function⇏value gap (Thm B)
  is the ℚ-only phenomenon made explicit.

## Gates
- [x] 0 → 1: routes identified (friable moment ladder; difference-Galois value-lift).
- [x] 1 → 2: **proven** — Theorem A (finite-dim `V_T`, all `T`, Bell-polynomial proof, certified `T=1,2,3`) and
  Theorem B (function⇏value). Unconditional, artifact-safe. **No no-go is claimed** (predecessor's Corollary A
  withdrawn per the correction box).
- [ ] 2 → 3: formalizable core — `M_j^{(T)} ∈ V_T` for fixed small `T` (the `T=2` 11-monomial identity is a
  finite ℚ-linear identity, Lean-able like the existing finite Morita/Bohr anchors); the general-`T`
  finite-dimensionality is a Bell-polynomial statement. Theorem B is a one-line elementary Lean lemma.
- [ ] 3 → 4: folds into the exponential-column exposition as "the period content of the friable moment family."

## Cross-references
- `../1-in-progress/relative-exponential-apex.md` §8/§14/§15/§16 — the live apex lane; §8 shows the
  single-integral Padé family fails numerically (the route-failure evidence, not a proof); the no-go conjecture
  stays open there.
- `bigraded-corank-dss-cross.md` §G — `γ_E ∉ \overline{𝓡}` = the open second conjunct (not decided here).
- `dss-lower-bound-orbit-nogo.md`, `friable-dirichlet-auxiliary.md` — companion analyses on the **first**
  conjunct (prime-log Schanuel).
- `../1-in-progress/baker-for-stieltjes.md` (Professor) — if his `R_P = Σ a_j Γ(s+j)ζ(s+j)` is a pure
  moment/jet combination (no decaying-remainder kernel), Theorem A pins its period content to a fixed `V_T`.

## Log
- 2026-06-19 — Wheeler: **created to replace the withdrawn `friable-moment-ladder-nogo`.** Leaner (return note)
  correctly showed the predecessor's no-go (Corollary A) does **not** follow from finite-dimensionality —
  Apéry's `ζ(3) ∈ ⟨1,ζ(3)⟩` and continued-fraction convergents give small forms in fixed finite-dim spaces.
  The no-go conjecture is **withdrawn** (open, relocated to `relative-exponential-apex` §8/§16). Banked the
  genuinely-proven residue: **Theorem A** (finite-dim `V_T` landing, every `T`, Bell-polynomial proof, certified
  `T=1,2,3`, Lean-ready) and **Theorem B** (function-transcendence ⇏ value-transcendence, elementary). Both
  BRIDGE, unconditional, artifact-safe. No no-go is claimed.
