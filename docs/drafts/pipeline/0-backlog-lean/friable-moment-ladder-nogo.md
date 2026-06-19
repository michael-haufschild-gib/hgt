# The friable single-moment ladder is finite-dimensional at every weight — a provable no-go for moment-based transcendence of `γ_E`

- **ID:** friable-moment-ladder-nogo
- **Stage:** 0-backlog-lean
- **Type:** THEOREM (paper). Two provable pillars closing the two attack routes of `relative-exponential-apex`.
- **Priority:** FOUNDATIONAL (it provably exhausts the natural Apéry/difference-Galois attack on the
  exponential conjunct `γ_E ∉ 𝓡̄`; it does **not** decide that conjunct, which is not in scope).
- **Owner:** Wheeler
- **Source:** Wheeler's `relative-exponential-apex` §5.1/§6/§7/§8/§14 (the moment-construction lane) + §2/§3
  (the difference-Galois lane); the user directive 2026-06-19 ("complete the Fields-Medal tickets to a
  provable terminus; *fail = provably false*"). Distinct from the prime-log no-gos
  (`dss-lower-bound-orbit-nogo.md`, `friable-dirichlet-auxiliary.md`) — those handle the **first** conjunct
  of DSS-cross (Schanuel for `{log p}`); this handles attack-routes on the **second** conjunct (`γ_E`).

---

## What is proven (scope, stated honestly up front)

The apex conjecture `γ_E ∉ \overline{𝓡}` (`𝓡 = MT(ℤ)-periods · ℚ({log p})`) is **neither proved nor
disproved here** — it implies `γ_E ∉ ℚ`, open since Euler 1734, and remains the open second conjunct of
DSS-cross (`bigraded-corank-dss-cross` §G). **What is proved is that the two natural attack routes are
provably insufficient** — each is a *provably false* statement of the form "route R proves the apex":

- **Pillar A (moment ladder).** For every finite log-power `T`, the friable single-moment construction lands
  in a **fixed finite-dimensional ℚ-space** of transcendentals; it provably cannot produce an
  irrationality/transcendence measure for `γ_E`.
- **Pillar B (difference-Galois).** Function-transcendence of the digamma primitive `ψ` (proven, `𝔾_a`)
  provably does **not** imply value-transcendence of `γ_E = −ψ(1)`; specialization is not controlled by the
  difference-Galois group (witnessed elementarily by `log` transcendental, `log 1 = 0 ∈ ℚ`).

Both pillars are unconditional. Numerically pre-certified at `T = 1, 2, 3`.

---

## §A Pillar A — the finite-dimensional moment-ladder theorem `[PROVEN]`

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

**Corollary A (the no-go).** No ℚ-linear combination of `{M_j^{(T)}}` (equivalently of the raw moments
`{∫x^j(\log x)^T dμ_S}`) yields an irrationality or transcendence measure for `γ_E`. *Reason.* Every such
combination is again an element of the **fixed** finite-dim `V_T`; the construction carries **no
decaying-remainder integral** (contrast Apéry's `∫_0^1` kernel, whose remainder `→ 0` geometrically). The
normalized moments grow only like `(\log j)^T`, the raw ones like `j!`; there is no analytic mechanism
producing a sequence of small `γ_E`-retaining forms whose smallness beats their height. The height vacuum is
not escaped at any finite `T`. ∎

**Numerical certification (artifact-safe).**
- `T=1`: `M_j = H_j − γ_E + r2_j\log2 + r3_j\log3` (`r∈ℚ`), `γ_E`-coeff `≡ −1`; `⟨1,γ_E,\log2,\log3⟩`,
  4-dim (verified dps=80; the §14 dps=60 "relation" vanished at dps=150/250 — spurious).
- `T=2`: 11-dim; closed form `=` direct friable summation (machine-zero, `j≥1`); `M_j^{(2)} =` predicted
  coefficient vector (machine-zero, `j=0..6`); PSLQ `j=0` returns exactly `3×` predicted (basis complete).
  The `γ_E`-coefficient now **varies** (`−2H_j − 2a_j`) — the `T=1` rigidity breaks — yet the space is still
  finite.
- `T=3`: closed form `=` monomial expansion in `{γ_E,ζ(2),ζ(3),\log2,\log3}` (machine-zero, `j=0..5`); the
  new weight-3 transcendental `ζ(3)` enters exactly as predicted; finite per weight.
- Archive: `computations/2026-06-19-wheeler-friable-moment-ladder-nogo.txt`, `…-friable-T2-secondmoment.py`,
  `…-friable-T3-thirdmoment.py` (and `…-friable-bypass-test.txt` for `T=1`).

## §B Pillar B — difference-Galois function-transcendence ⇏ value-transcendence `[PROVEN, elementary]`

`relative-exponential-apex` §2 proves (van der Put–Singer): the digamma `ψ` is a non-rational `𝔾_a`-primitive
(transcendental over `ℂ(s)`, satisfying `σψ−ψ=1/s`, `1/s` not `σ`-summable). The apex wants the **value**
`γ_E = −ψ(1) ∉ \overline{𝓡}`.

**Theorem B.** The difference-Galois group of the rank-2 unipotent module carrying `ψ` (which is `𝔾_a`)
provably does **not** determine the arithmetic nature of the specialized value `ψ(1)`. *Proof.* Specialization
`s ↦ 1` is a ring map out of the Picard–Vessiot ring that is **not** a difference-Galois-equivariant
operation; the Galois group acts on the abstract primitive, not on its value at a point. Witness (elementary,
sufficient to defeat the implication): `\log s` is a `𝔾_a`/`𝔾_m`-primitive transcendental over `ℂ(s)`, yet
`\log 1 = 0 ∈ ℚ`. So "function transcendental over `ℂ(s)`" carries **no** information about whether the value
at a chosen point is in a given field. Hence the §2/§3 difference-Galois route **cannot**, by itself, deliver
`γ_E ∉ \overline{𝓡}`. ∎

This is exactly the `F₁` value-lift wall of `relative-exponential-apex` §3, now stated as a theorem: the
missing ingredient is genuinely arithmetic (a measure), not group-theoretic — and Pillar A shows the natural
arithmetic measure-construction (moments) is itself dead.

## §C Consequence for the open apex `[the honest residue]`

Pillars A+B together: the **two attack routes built in `relative-exponential-apex`** (arithmetic moment
approximation; difference-Galois value-lift) are **provably insufficient**. They do not decide `γ_E ∉ \overline{𝓡}`.
The escape, if any, must be a **genuinely different mechanism**: (i) a decaying-remainder (Apéry-kernel)
integral specifically engineered for `γ_E` — a different object than the moment ladder, OR (ii) the
exponential-period route (GPC^exp / `Lie(K)` freeness, `exponential-period-dss-cross`,
`cosmic-galois-freeness-mirror`), itself open. The bare conjecture `γ_E ∉ \overline{𝓡}` remains the open
second conjunct of DSS-cross and is **not** claimed here either way.

## Door / grade
- **Door-2.** Pillar A is the Bell-polynomial/specialization structure of a classical moment family (single
  parent: gamma-integral asymptotics + `ζ_S`-derivatives) ⟹ BRIDGE. Pillar B is van der Put–Singer +
  elementary specialization ⟹ BRIDGE. The native/apex content (the actual value-lift) is precisely what these
  pillars prove the routes **cannot** reach.
- **Door-5.** Over `F_q(C)` the value-lift exists (single Frobenius, `K=1`), so this no-go is the ℚ-only
  obstruction made explicit: the moment ladder is the diagonal shadow that collapses.

## Gates
- [x] 0 → 1: routes identified (moment ladder; difference-Galois value-lift).
- [x] 1 → 2: **fully proven.** Theorem A (finite-dim `V_T`, all `T`, Bell-polynomial proof, certified
  `T=1,2,3`) + Corollary A (no-go) + Theorem B (function⇏value). Unconditional; artifact-safe.
- [ ] 2 → 3: formalizable core — `M_j^{(T)} ∈ V_T` for fixed small `T` (the `T=2` 11-monomial identity is a
  finite ℚ-linear identity, Lean-able like the existing finite Morita/Bohr anchors); the general-`T`
  finite-dimensionality is a Bell-polynomial statement.
- [ ] 3 → 4: folds into the exponential-column exposition as "why the natural Apéry attack on `γ_E` fails."

## Cross-references
- `../5-failed/relative-exponential-apex.md` — the attack ticket this no-go retires (provably-insufficient
  route); the conjecture itself relocated open to the DSS-cross apex.
- `bigraded-corank-dss-cross.md` §G — `γ_E ∉ \overline{𝓡}` = the open second conjunct (this no-go does not decide it).
- `dss-lower-bound-orbit-nogo.md`, `friable-dirichlet-auxiliary.md` — the companion no-gos on the **first**
  conjunct (prime-log Schanuel); same height-vacuum phenomenon, different auxiliary/target.
- `../1-in-progress/baker-for-stieltjes.md` (Professor) — if his `R_P = Σ a_j Γ(s+j)ζ(s+j)` is a pure moment/jet
  combination (no decaying-remainder kernel), Pillar A applies to it: the escape must be a remainder kernel.

## Log
- 2026-06-19 — Wheeler: created. Built + tested the friable second/third log-moment (`T=2,3`); proved the
  general-`T` finite-dimensional theorem (Pillar A) and the function⇏value separation (Pillar B); both
  unconditional, certified `T=1,2,3` (artifact-safe). This provably exhausts the moment + difference-Galois
  attack routes on `γ_E ∉ \overline{𝓡}` (refuting my own id=327 "go to `T≥2`" steer — the whole single-moment
  ladder is dead, not just `T=1`). The apex conjecture is **not** decided (it implies `γ_E` irrational, open
  since 1734) and is relocated open to the DSS-cross cards. → 2-fully-proven (no-go theorem).

## Leaner return note — 2026-06-19
Returned from `2-fully-proven` to `0-backlog-lean`: the paper proof is incomplete at Corollary A. Theorem A's finite-dimensional containment, even if true for fixed finite `S` and fixed `T`, does not imply that no `Q`-linear combination of the moments can yield an irrationality or transcendence measure for `gamma_E`. A fixed finite-dimensional `Q`-space can still contain sequences of linear forms with coefficients depending on the index that become arbitrarily small; for example, continued-fraction convergents give small forms in `span_Q {1, alpha}` for an irrational `alpha`. The corollary needs an explicit height/denominator-growth lower bound, bounded-coefficient restriction, or another rigorous obstruction to small `gamma_E`-retaining forms. The current argument only says there are finitely many basis monomials at fixed `S,T`; it does not prove the announced no-go.
