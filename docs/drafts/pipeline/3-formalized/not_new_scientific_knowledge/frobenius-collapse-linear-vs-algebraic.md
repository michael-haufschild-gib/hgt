# Two tiers of "single Frobenius": linear-F₁ (corank collapse) ⊊ algebraic-F₁ (trdeg collapse)

- **ID:** frobenius-collapse-linear-vs-algebraic
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean, elementary field theory + the certified §1 block computation) — a precision refinement
- **Owner:** Wheeler
- **Door grade:** **BRIDGE (substrate)** — refines the project's native `corank`/`F₁` language; imports are
  elementary transcendence-degree field theory.
- **Source / method:** reverse-move refinement of `corank-arithmeticity-not-cardinality.md` (the `B_dep`
  witness) and `corank-transcendence-continuation-bridge.md` (#125 corank/F₁). Entropy seed
  3050780354571332636; method=reverse (study the *maximal-collapse* case trdeg=1 instead of independence).
  Feeds `../../door/G2-multi-q-siegel-shidlovsky.md` and the seam-bucket "missing F₁" narrative.

---

## §0 The point in one line
The corpus's single notion **"missing single Frobenius F₁"** conflates two **strictly different** collapse
tiers; the witness `B_dep = {e^π, e^{π²}}` separates them, and **DSS over ℚ targets the *algebraic* tier**,
which is strictly weaker than the linear tier the F_q analogy suggests.

## §1 The two tiers `[PROVED HERE]`
Setup (from `corank-arithmeticity-not-cardinality.md` §1): a finite generalized-prime system
`{g_1,…,g_r}`, `L_i = log g_i`, continuation block `T_0 = ℚ̄(e_1(L),…,e_r(L)) ⊆ ℚ̄(L_1,…,L_r)`, with
`corank = dim_ℚ span_ℚ{L_i}` and (upper bound, proven there) `trdeg_ℚ̄ T_0 = trdeg_ℚ̄ ℚ̄(L_1,…,L_r) ≤ corank`.

- **Linear-F₁ (the F_q tier).** `corank = 1`: all `L_i ∈ ℚ·t` for one `t` (a common ℚ-multiple base).
  Over `F_q`, `t = ln q` and `L_i = −deg(v_i)·ln q` with `deg(v_i) ∈ ℤ ⊂ ℚ`. The whole multiplier group is
  `t^{ℚ}` — one Frobenius up to ℚ-powers.
- **Algebraic-F₁ (the value tier).** `trdeg_ℚ̄ ℚ̄(L_1,…,L_r) = 1`: all `L_i ∈ ℚ̄(t)`, **algebraic** over a
  single transcendental `t` (not necessarily ℚ-linear). The continuation block is `ℚ̄(t)`-rational,
  `trdeg = 1`.

**Containment, with strictness `[PROVED HERE]`.**
`{corank = 1} ⊊ {trdeg = 1}`.
- `⊆`: `corank=1 ⟹ all L_i ∈ ℚt ⊂ ℚ̄(t) ⟹ trdeg ≤ 1` (`=1` once some `L_i` is transcendental, e.g. `log` of
  an integer `≥2` by Lindemann). So linear-F₁ ⟹ algebraic-F₁.
- `⊊` (strict): **`B_dep = {e^π, e^{π²}}`**, `L_1 = π`, `L_2 = π²`.
  `L_2 = L_1² ∈ ℚ̄(L_1)` ⟹ `trdeg ℚ̄(L_1,L_2) = 1` (**algebraic-F₁ present**, base `t = π`); but
  `{π, π²}` is ℚ-**linearly** independent (`aπ+bπ²=0 ⟹ π=−a/b∈ℚ`, false) ⟹ `corank = 2`
  (**linear-F₁ absent**). ∎

So the F_q-style "single Frobenius" (linear, corank=1) is **strictly stronger** than what actually controls
the continuation transcendence (algebraic, trdeg=1). The collapse of value-transcendence needs only the
weaker algebraic-F₁.

## §2 Corollary — `B_dep` concretely DECOUPLES the function-axis from the value-axis `[PROVED HERE]`
The field splits its content into **(A)** function-level obstruction theory (corank / holonomicity, the
rank axis) and **(V)** value-relation theory (trdeg / DSS) — see `keystone-is-value-relational.md`. The
abstract O/V split lacked a concrete separating example. `B_dep` is one:
> `B_dep` has `corank = 2` (function-axis: **non-holonomic**, rank > 1) yet `trdeg = 1` (value-axis:
> **value-trivial**, a single transcendental generates the whole continuation).

Hence "non-holonomic by rank (corank>1)" does **not** imply "value-transcendence-rich (trdeg>1)": the two
axes are independent, with `B_dep` realizing the off-diagonal `(corank>1, trdeg=1)` corner. (The diagonal
corners are `F_q`: `(1,1)`; free Beurling: `(r,r)`; the open ℚ apex: `(∞,∞)`.)

## §3 What this sharpens for DSS / the apex `[orientation]`
- Over ℚ, `corank = ∞` (Baker / unique factorization, `{log p}` ℚ-linearly independent — **no linear-F₁**,
  proven). The DSS lower bound wants `trdeg = ∞` — i.e. **no algebraic-F₁ either**, indeed the maximal
  anti-collapse.
- So the "missing F₁" that the *value* apex needs ruled out is the **algebraic-F₁** (trdeg-1 collapse), a
  target **strictly between** Baker linear independence (`corank=∞`, have it) and full Schanuel. Phrasing the
  apex as "no algebraic-F₁ for `{log p}`" is sharper and lower than "Schanuel."
- It also pins the function/value confusion: the F_q intuition "one Frobenius ⟹ everything" is a **linear**
  collapse; importing it to ℚ as the value obstruction is a tier error. The value obstruction is algebraic.

## §4 Door passport
- **BRIDGE (substrate).** Refines native `corank`/`F₁`; proof is elementary field theory + the §1 block.
- **Door-5 ✓:** over `F_q` both tiers coincide (`corank = trdeg = 1`), recovering the classical single
  Frobenius; the tier distinction is a pure ℚ / arithmetic-base phenomenon.
- **Content beyond imports:** the **two-tier separation** with an explicit witness (`B_dep`), and the
  **axis-decoupling corollary** (corank>1 ∧ trdeg=1) giving the O/V dichotomy its first concrete separating
  example. A literature search produces neither.

## Gates
- [x] 0 → 1 → 2: tiers defined; containment + strictness proved (`B_dep` witness); decoupling corollary
  proved; DSS-target sharpening stated; Door passport. Fully proven (elementary + the certified §1 block).
- [x] 2 → 3: formalized unconditionally in
  `formal/GaloisForLFunctions/HTGeometry/LinearVersusAlgebraicCollapse.lean`; every declaration is
  `#print axioms`-clean and `lake build` is green.  The §1 block lemmas were built here rather than
  imported (they are not in Lean on the source card): `trdeg_adjoin_le_rank_span` is `trdeg ≤ corank`
  and `trdeg_adjoin_le_one_of_rationalMultiple` is the containment.  `B_dep_corank_two` is
  `linearIndependent_pair_pi_sq`; `B_dep_trdeg_one` is `pi_sq_mem_adjoin_pi` together with
  `trdeg_adjoin_pi_pair_le_one`.
- [ ] 3 → 4: pairs with the no-go card and #125 as "the missing F₁ for the value apex is algebraic-F₁, not
  linear-F₁."

## Notes / risk
- Pure precision/refinement: no transcendence frontier is crossed here. The ℚ apex (`trdeg{log p}=∞`)
  remains the open wall (four-exponentials / Schanuel territory), explicitly **not** touched.
- Honest scope: the field-theory facts (trdeg=1 ⟺ all `L_i ∈ ℚ̄(t)`) are elementary; the contribution is the
  *application* — that the project's F₁ notion is two-tiered and that `B_dep` separates the tiers and the
  axes. Novel in the project sense; not a standalone transcendence result.

## Log
- 2026-06-20 — Wheeler. Created directly in 2-fully-proven. reverse-move (study trdeg=1 maximal collapse)
  on the `B_dep` witness yielded the linear-F₁ ⊊ algebraic-F₁ separation and the corank⊥trdeg axis-decoupling
  corollary. Sharpens the DSS/value apex target to "no algebraic-F₁ for `{log p}`," strictly between Baker and
  Schanuel. Elementary proof; Door BRIDGE (substrate). The transcendence wall itself is untouched and flagged.


## Lean formalization — 2026-07-31

One module, `formal/GaloisForLFunctions/HTGeometry/LinearVersusAlgebraicCollapse.lean`, `lake build`
green and `#print axioms`-clean (`propext`, `Classical.choice`, `Quot.sound` only) on all sixteen
declarations.  No hypotheses are carried.  Everything is stated for an arbitrary commutative
`ℚ`-algebra `A`, so it applies to the real logarithms of the card and to any other base.

### The §1 block (built here, not imported)

| Declaration | Statement |
|---|---|
| `trdeg_adjoin_le_cardinalMk` | `trdeg ℚ (adjoin ℚ s) ≤ #s` — via the surjection from `MvPolynomial s ℚ` |
| `trdeg_adjoin_le_rank_span` | **`trdeg ≤ corank`**: the transcendence degree of the algebra generated by a set is at most the dimension of its rational span.  Proof: extract a rational basis of the span from the set itself; the algebra it generates already contains the set |
| `trdeg_adjoin_singleton_le_one` | one generator gives transcendence degree at most one |
| `trdeg_adjoin_le_one_of_subset_adjoin_singleton` | the algebraic tier from a single generator |
| `trdeg_adjoin_le_one_of_rationalMultiple` | **the containment `⊆`: `corank = 1 ⟹ trdeg ≤ 1`** |
| `trdeg_adjoin_singleton_eq_one` | at a transcendental generator the algebraic tier is exactly one |

### The separating witness

| Declaration | Statement |
|---|---|
| `linearIndependent_pair_sq_of_irrational` | **`x` and `x²` are ℚ-linearly independent whenever `x` is irrational — corank two** |
| `not_algebraicIndependent_pair_sq` | **`x` and `x²` are always algebraically dependent** — the polynomial `X₁ − X₀²` |
| `trdeg_adjoin_pair_sq_le_one`, `trdeg_adjoin_pair_sq_eq_one` | the pair generates an algebra of transcendence degree at most one, and exactly one at a transcendental `x` |
| `linearIndependent_pair_pi_sq` | **`B_dep_corank_two`: `{π, π²}` is ℚ-linearly independent** (from `irrational_pi`) |
| `pi_sq_mem_adjoin_pi`, `trdeg_adjoin_pi_pair_le_one` | **`B_dep_trdeg_one`: `π² ∈ ℚ[π]`, so the pair's algebraic invariant is at most one** |
| `isAlgebraic_int_rat`, `exists_transcendental_real` | an explicit transcendental real (a Liouville number), obtained by clearing denominators to pass from `Transcendental ℤ` to `Transcendental ℚ` |
| `exists_linearIndependent_pair_trdeg_one` | **the strictness `{corank = 1} ⊊ {trdeg = 1}`, unconditionally: a rationally independent real pair whose generated algebra has transcendence degree exactly one** |

### One scope note

At `π` the formalization gives `corank = 2` and `trdeg ≤ 1`, which is already the §2 decoupling
(function axis non-trivial, value axis trivial).  Pinning `trdeg = 1` *at `π`* additionally needs
`π` transcendental, and Mathlib currently has only the analytic half of Lindemann–Weierstrass, not
the transcendence of `π`.  The exact-value form of the strictness is therefore proved with an
explicit transcendental real instead — a Liouville number — which is unconditional and gives the
same theorem `{corank = 1} ⊊ {trdeg = 1}`.  Nothing in §1–§3 depends on the witness being `π`.
