# A Baker for the Stieltjes constants

- **ID:** baker-for-stieltjes
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Priority:** FOUNDATIONAL (the concrete obstruction-C target)
- **Source:** ../../door/G2-multi-q-siegel-shidlovsky.md, ../../door/bucket-the-seam-archimedean-obstruction.md · 00-status rows #18, #19
- **Statement:** A transcendence / independence lower bound for the Stieltjes constants `γ_n` (the
  Laurent coefficients of `ζ` at `s=1`) — the rung just above Baker's solved edge `L(1,χ)`.
- **Sharpened form (2026-06-19):** `trdeg_ℚ\{γ_n\}_{n≥0} = corank(Λ_{M_ζ}) = ∞` — the **corank–
  transcendence identity** at the number-field instance. The provable structural half (FF side
  `trdeg=corank=1` exactly; the `{log p}`-feeding mechanism; the polynomial-case upper bound
  `trdeg ≤ corank`) is **proven** in `../2-fully-proven/corank-transcendence-continuation-bridge.md`. What
  remains here = the **lower bound** `trdeg\{γ_n\} = ∞` (the upper bound is vacuous over ℚ), i.e. the
  Stieltjes block realizes the full infinite corank as genuine independent transcendence = the analytic
  shadow of the missing single Frobenius (seam, #121 §3).

## Goal
The Stieltjes block is the genuinely-new, no-motive part of G2/DSS: `ℚ(\{P_k\}) = ℚ(π, \{ζ(odd)\},
\{γ_n\})`, and the `\{γ_n\}` are conjecturally not periods, so they sit beyond the Grothendieck period
conjecture. A transcendence result here is the concrete `s=1`-Laurent / archimedean attack on the DSS
open core. Source-pure: the `γ_n` are prime/continuation data, not the zeros.

---

## The reduction target — concretizing obstruction C (2026-06-19, Professor)

The amorphous "arithmetic of the L-values / height vacuum" (obstruction C, §17.3 of the G2 bucket) is
turned here into **one explicit Diophantine hypothesis `H_C`**, and the role of every other pillar is
pinned. The aim is the reduction theorem `A ∧ B′ ∧ H_C ⟹ trdeg_ℚ\{γ_n\}=∞`; this section establishes
the parts that are elementary and isolates exactly what is open.

### §A The friable auxiliary and the moment / weight expansion `[ELEMENTARY — proven]`
Native auxiliary space (object N5, `friable-dirichlet-auxiliary.md`): friable (S-smooth) Dirichlet
polynomials `F(s)=Σ_m λ_m n_m^{−s}`, `n_m=∏_{p∈S} p^{m_p}`, `λ_m∈ℤ`. Taylor-expand each term at `s=1`:
```
   n^{−s} = n^{−1} e^{−(s−1)\ln n} = n^{−1} Σ_{j≥0} (−(s−1)\ln n)^j / j! ,
   F(s)   = Σ_{j≥0} (s−1)^j/j! · c_j ,   c_j := (−1)^j Σ_m λ_m (\ln n_m)^j / n_m .
```
Write `R = ℚ[\{X_p\}_{p∈S}]`, `X_p ↦ \log p`. Since `\ln n_m = Σ_p m_p \log p`, each `(\ln n_m)^j ∈ R_j`
(degree-`j` homogeneous part), so `c_j` is a `ℚ`-point of `R_j` weighted by `λ_m/n_m`. **Weight grading:**
the auxiliary's `j`-th Taylor datum lives in log-weight `j`. The FF degeneration `X_p ↦ (\text{single }\log q)`
collapses every `R_j` onto `ℚ̄·(\ln q)^j`, recovering `trdeg ≤ 1` — consistency with the corank card §1.

### §B Where the `γ_n` enter — the pairing `F·(s−1)ζ` and the two-layer weld `[ANALYZED — the crux is the seam]`
The `γ_n` are Laurent coefficients of **ζ**, so they enter only by pairing the auxiliary with ζ. Take
`G(s) := (s−1)ζ(s) = 1 + Σ_{n≥0} a_n (s−1)^{n+1}`, `a_n = (−1)^n γ_n/n!`, and form `H := F·G` with
`F(s)=Σ_j (c_j/j!)(s−1)^j` (§A, `c_j∈R_j`). Then the `N`-th Taylor coefficient at `s=1` is **(verified)**
```
   [H]_N = c_N/N!  +  Σ_{n=0}^{N−1} (c_{N−n−1}/(N−n−1)!) · (−1)^n γ_n/n! .
```
So each `γ_n` appears with coefficient `c_{N−n−1}/(N−n−1)! ∈ R_{N−n−1}` — a **log-`p` transcendental of
weight `N−n−1`**, NOT an integer. The auxiliary's coefficients carry `{log p}`; the continuation data carry
`{γ_n}`. **The pairing welds the two transcendence layers.**

> **The concrete obstruction (verified algebra, 2026-06-19).** Try to isolate a clean `ℚ`-form in one
> `γ_{N−1}`: project onto the log-`p` weight-0 part by killing `c_1=…=c_{N−1}=0`. Then
> `[H]_N = c_N/N! + c_0·(−1)^{N−1}γ_{N−1}/(N−1)!` with `c_0=Σ_m λ_m/n_m ∈ ℚ` but a **residual top-weight
> term `c_N ∈ R_N`** (log-`p` transcendental) that **cannot be removed without killing the `γ` coupling**.
> A clean rational-coefficient form in the `γ_n` therefore does **not** exist from a single auxiliary:
> cancelling `c_N` forces a second construction in the `{log p}` layer. **Any clean `γ`-form is
> simultaneously a `{log p}`-form — the two layers are arithmetically welded.** This IS the seam
> (multiplicative `{log p}` layer ⊥ archimedean `{γ_n}` layer) realized *inside* the Stieltjes
> construction: #69/#71's "one archimedean obstruction" appears here as the impossibility of decoupling the
> `γ_n` from the multiplier logs.

> **Sharpening — the residual is irremovable, the target is joint (verified, 2026-06-19).** Killing the
> middle log-`p` weights `c_1=…=c_W=0` only **moves** the residual to the top:
> `[H]_{W+1} = c_{W+1}/(W+1)! + c_0·(−1)^W γ_W/W!`, still one top-weight log-`p` term `c_{W+1}∈R_{W+1}`
> beside the lone `γ_W`. Killing *all* weights forces `F≡const` (only the `n=1` Dirichlet coefficient
> survives, by linear independence of `\{n^{−s}\}` — trivial, no Diophantine content). So **nontrivial
> auxiliary ⟺ nonzero log-`p` residual**: the Stieltjes transcendence **cannot be isolated** from the
> multiplier-log transcendence by this construction. The structurally honest target is the **joint**
> statement `trdeg_ℚ ℚ(\{\log p\}∪\{γ_n\}) = ∞` with the `γ_n` contributing **beyond** `\{\log p\}`. Note
> even `\{\log p\}` *algebraic* independence is Schanuel-level (Baker gives only *linear* independence) —
> so DSS-cross is **Schanuel-entangled** through this weld, and `H_C` should be posed **jointly** (a measure
> on `ℤ`-polynomials in `\{\log p\}∪\{γ_n\}`), not on the `γ_n` alone.

> **Earlier wrong handle (kept for record).** The raw "F vanishes to order T ⟹ F^{(T)}(1) small" route is
> doubly wrong: `F^{(T)}(1)` grows like `T!(\ln X)^T`, and it contains no `γ_n` at all (they are ζ's
> coefficients). The pairing `F·(s−1)ζ` above is the correction that brings the `γ_n` in.

### §C The three pillars as Nesterenko-criterion inputs `[factorization — pinned]`
Applying Nesterenko's algebraic-independence criterion (IMPORT) to the Stieltjes point
`(γ_0,…,γ_d)` through the §B auxiliary needs exactly three inputs:
- **A — Siegel in ∞ variables** = Bombieri–Vaaler weighted Siegel's lemma on the friable space.
  **Supplied** (`friable-dirichlet-auxiliary.md`; ledger `boundedExponentVectorEquivSmooth`).
- **B′ — zero / multiplicity estimate, uniform in `S`** = Conjecture 5′. Finite-`S` **proven**
  (multivariate Mahler / Adamczewski–Faverjon); uniform-`S` **open** = DeWitt's lane
  (`zero-estimate-uniformity.md`).
- **C — the arithmetic lower bound** = `H_C` below. The genuine wall: the **height vacuum** — `γ_n` carry
  no number field, house, or Weil height, so no arithmetic lower bound is available a priori. This is the
  F₁ / missing-Frobenius residue (Door-2: over `F_q` the analogue is Papanikolas, single Frobenius supplies
  it; over `ℚ` it must be earned).

### §D `H_C` — the precise target ("a Baker / Nesterenko for the Stieltjes constants") `[stated]`
> **`H_C`.** There is `κ : ℕ³ → ℝ_{>0}` such that for every `d` and every nonzero `P ∈ ℤ[x_0,…,x_d]` of
> total degree `D` and logarithmic height `h`,
> `   |P(γ_0,…,γ_d)| ≥ exp(−κ(d,D,h))`,
> with `κ` strictly below the budget `β(d,D,h)` furnished by `A+B′` (the analytic+height side of §B/§E).
- **Linear sub-case** (`D=1`): a literal **Baker statement** — `\{1,γ_0,…,γ_d\}` linearly independent over
  `ℚ̄` with an effective measure. This is the "rung just above Baker": Baker gives the measure for the bare
  logs `\{\log p\}` (weight 1, no regularization); `H_C` asks it for the **regularized** weight-`n`
  combinations `γ_n`.
- **Concrete first sub-target:** irrationality of a single `γ_n` (the `d=0` rung — even `γ_0=Euler's γ` is
  open), then linear independence of `\{1,γ_0,γ_1\}` (`d=1`).

### §E The reduction theorem — status `[goal; partially established]`
> **Goal.** `A ∧ B′(Conj 5′) ∧ H_C ⟹ trdeg_ℚ\{γ_n\}_{n≥0}=∞` (Nesterenko's criterion on the Stieltjes
> point via the §B friable-Padé auxiliary).
- **Established:** A is dischargeable (Bombieri–Vaaler, §C); the moment/weight structure (§A); the
  obstruction **factorization** — the entire arithmetic gap is `\{B′ ∧ H_C\}`, cleanly split into DeWitt's
  lane (B′) and this lane (C = `H_C`).
- **Open (this card):** (i) §B shows the `{γ_n}`/`{log p}` layers **cannot be disentangled** without
  trivializing the auxiliary, so the target is **reframed to the joint statement**
  `trdeg_ℚ ℚ(\{\log p\}∪\{γ_n\})=∞` (γ_n beyond the logs), which is **Schanuel-entangled** and **= the
  seam** (#69/#71). `H_C` is correspondingly posed jointly. (ii) the budget `β > κ` (that A+B′ control the
  analytic side so the joint `H_C` is the **sole** arithmetic gap). The reduction becomes a theorem once
  the joint `H_C` + B′ feed Nesterenko's criterion on the joint point `(\{\log p\}, \{γ_n\})`.
- **No overclaim:** `trdeg\{γ_n\}=∞` itself stays the open wall; no RH/DSS consequence is asserted.

## Door passport
- **Door-1/3/4:** native difference-trdeg / `G_L`-orbit-dimension invariant; lives in the infinite/arithmetic
  base; the height vacuum **is** the infinite-base obstruction.
- **Door-2:** over `F_q(t)` the statement is Papanikolas's theorem (single Frobenius ⟹ finite difference
  equation); the ℚ-content `H_C` is the F₁ / missing-Frobenius residue no parent reaches.

## Gates
- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door sketch.
- [ ] 1 → 2  fully-proven: needs §B (the approximation functional) + §E budget closed, reducing the lower
  bound to `H_C` as the sole arithmetic gap. (Then the reduction theorem splits to 2-fully-proven; the
  unconditional `trdeg=∞` stays open as a stated `H_C`.)
- [ ] 2 → 3  formalized
- [ ] 3 → 4  publication-ready

## Cross-references
- `../2-fully-proven/corank-transcendence-continuation-bridge.md` — the proven structural half.
- `g2-dss-lower-bound.md` — the G2 open core this feeds (obstruction C).
- `zero-estimate-uniformity.md` — obstruction B′ (DeWitt), the second arithmetic input.
- `friable-dirichlet-auxiliary.md` — the native auxiliary space (object N5) carrying §A.

## Log
- 2026-06-19 — created in 0-backlog
- 2026-06-19 — Professor: pulled to in-progress, split off the provable structural half (proven →
  `../2-fully-proven/corank-transcendence-continuation-bridge.md`: FF `trdeg=corank=1` exact, feeding
  mechanism, upper bound), reframed as the **corank–transcendence identity** `trdeg\{γ_n\}=corank=∞`, and
  returned to 0-backlog.
- 2026-06-19 — Professor: reclaimed to in-progress. **Concretized obstruction C** into an explicit
  Nesterenko algebraic-independence measure `H_C` for the Stieltjes point (§D); pinned the pillar
  factorization (A supplied via Bombieri–Vaaler; B′=Conj 5′, DeWitt; C=`H_C`, this lane); identified the
  **correct mechanism** as a Hermite–Padé race against ζ's Laurent data at `s=1` (§B) and **ruled out** the
  naive high-Taylor-coefficient handle (it grows like `T!(\ln X)^T`, and the `γ_n` are ζ's coefficients not
  the auxiliary's). Reduction `A∧B′∧H_C⟹trdeg=∞` stated as goal (§E); remaining open = the §B functional +
  the §E budget. `trdeg=∞` stays the open wall.
- 2026-06-19 — Professor: worked §B explicitly. Verified the pairing `H=F·(s−1)ζ` coefficient
  `[H]_N = c_N/N! + Σ_{n<N}(c_{N−n−1}/(N−n−1)!)(−1)^nγ_n/n!`: each `γ_n` carries a **log-`p` transcendental
  coefficient `c_{N−n−1}∈R_{N−n−1}`, not an integer**. Showed (verified algebra) a single auxiliary cannot
  produce a clean `ℚ`-form in the `γ_n` — killing intermediate weights leaves a residual top-weight
  `c_N∈R_N` that cancels only by a second `{log p}`-layer construction. **Finding: the `{γ_n}` and
  `{log p}` transcendence layers are arithmetically welded; the disentanglement IS the seam (#69/#71)
  realized inside the Stieltjes construction.** §B/§E updated: the open analytic step is now precisely the
  two-layer separation, seam-coupled.
- 2026-06-19 — Professor: sharpened §B. Verified that killing middle weights only **moves** the log-`p`
  residual to the top (`[H]_{W+1}=c_{W+1}/(W+1)!+c_0(−1)^Wγ_W/W!`), and killing all weights forces
  `F≡const` (trivial). **Disentanglement is structurally impossible: nontrivial auxiliary ⟺ nonzero log-`p`
  residual.** Reframed the honest target to the **joint** `trdeg_ℚ ℚ(\{\log p\}∪\{γ_n\})=∞` (γ_n beyond the
  logs); noted it is **Schanuel-entangled** (Baker gives only linear independence of `\{\log p\}`); `H_C`
  reposed jointly. §B/§D/§E updated.
