# A Baker for the Stieltjes constants

- **ID:** baker-for-stieltjes
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
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

---

## §F The apex attack — the two moment families of `dt/(e^t−1)` (2026-06-19, Professor)

Pushing the attack (not deferring) revealed a clean structural finding — and corrected my own first framing.
Opened from the exponential-period realization (`../2-fully-proven/stieltjes-exponential-period-realization.md`).
**Headline:** the single measure `dμ=dt/(e^t−1)` carries the ζ-values as its *power*-moments and the `γ_n` as
its *log*-moments at `s=1` — the regular/wild (`𝓡`/`K`) Galois split realized analytically in one object; the
differential auxiliary closes the ζ-value (Apéry) lane and is killed by Hölder on the `γ_n` jet, forcing the
native difference (multi-`q` SS) auxiliary.

**The moment foundation `[VERIFIED, exact]`.** `Γ(s)ζ(s)=∫_0^∞ t^{s−1}/(e^t−1)dt`, so ζ's `s=1` Laurent data
is the analytic continuation of the moments of the **positive measure** `dμ(t)=dt/(e^t−1)` on `(0,∞)`:
```
   μ_j := ∫_0^∞ t^j/(e^t−1)\,dt = j!\,ζ(j+1)   (j≥1; j=0 is the pole).        [mpmath, |diff|≤1e−29]
```
So the moment sequence is **factorial × zeta-values** `{1!ζ(2), 2!ζ(3), 3!ζ(4),…}`. The Hankel determinants
`H_n=det[μ_{i+j+1}]_{0≤i,j<n}` are **positive** (`1.645, 4.902, 82.93, 16228, …`) ⟹ `dμ` is a bona-fide
Hamburger/Stieltjes moment measure with a well-defined orthogonal-polynomial system `{P_n(t)}`.

**The correction that makes this the right object `[did the math; found+fixed my own error]`.** The OP
system `{P_n}` of `dμ` is tuned to the **power**-moments `μ_j=j!ζ(j+1)`, so the resulting Hermite–Padé
approximants are to the **integer ζ-values** `(ζ(2),ζ(3),…)` — the **Apéry/Ball–Rivoal** world, *not* the
`γ_n`. The `γ_n` are not power-moments of `dμ`; they are its **logarithmic moments at `s=1`**: the `s=1` jet
of the Mellin transform,
```
   ζ-values:  μ_j = ∫_0^∞ t^j\,dμ = j!\,ζ(j+1)                 (POWER moments — Apéry lane)
   Stieltjes: ν_m = ⨍_0^∞ (\log t)^m\,dμ  (regularized) →  γ_n  (LOG moments — the s=1 jet of Γ(s)ζ(s)).
```
So the **same positive measure `dt/(e^t−1)` carries BOTH transcendence columns**, and the two moment families
**are** the two Galois columns (DeWitt `K`, Wheeler `corank^{(T,U)}`):

> **Finding (the regular/wild split is the power/log moment split of one measure).**
> - **Power-moments `μ_j=j!ζ(j+1)` → ζ-values = the REGULAR/motivic column** (`𝓡`, `K`-invariant). It has
>   **footholds**: Apéry (`ζ(3)∉ℚ`), Ball–Rivoal (`∞`-many `ζ(2k+1)∉ℚ`), Zudilin — proved by the
>   integer-point arithmetic (denominators `lcm(1..n)`, the prime structure).
> - **Log-moments `ν_m` → `γ_n` = the WILD/exponential column** (`K`, `K`-coordinates). It has **no
>   footholds**: even `γ_0=γ_E∉ℚ` is open. The `s=1` jet has **no clean denominators** — the *height vacuum*
>   (§C) is exactly the absence of the integer-point arithmetic that powers the Apéry lane.

**Why the foothold asymmetry — the differential→difference forcing `[the wall, located]`.** The Apéry/Rivoal
control of the ζ-value (power-moment) lane uses the **values at integers** `s=k`, where `Γ(s)ζ(s)` is
evaluated, and the Siegel–Shidlovsky-type control is differential. The `γ_n` lane lives at the **`s=1` jet**,
where the object is `Γ(s)ζ(s)` *as a function of `s`* — which is **hypertranscendental** (Hölder: no
algebraic differential equation). So the **differential** Siegel–Shidlovsky/Nesterenko that powers the Apéry
lane is **structurally unavailable** for the `γ_n` jet; the auxiliary must instead use the **difference**
structure — `Γ(s+1)=sΓ(s)` and the prime dilations `σ_p` — i.e. the native **multi-`q` Siegel–Shidlovsky
(G2)**. **The height vacuum = the un-mastered difference-arithmetic of the `s=1` jet.** This is the
constraint-not-flow principle made concrete in the auxiliary construction: the `γ_n` cannot be reached by a
*flow* (differential) auxiliary, only by the *constraint* (difference/recurrence) one.

**Net (the unification, banked as the §F structural finding):** `baker-for-stieltjes` (analytic `γ_n`) and the
native **G2 multi-`q` Siegel–Shidlovsky** are the **same** problem — the log-moment lane of `dt/(e^t−1)` —
because the differential auxiliary is killed by Hölder. The Apéry ζ-value lane is the regular sibling that
*does* close, on the **power**-moments of the **same measure**. This pins, analytically and in one object,
why the regular column has footholds and the wild column does not.

**Deconfliction.** Wheeler `relative-exponential-apex` = single-`γ_E` via `ψ`/`𝔾_a`-period; DeWitt
`exponential-period-dss-cross` = the `K`-column at the Galois level. This §F is the **analytic realization**:
the `K`-column = the **log-moment lane** of `dt/(e^t−1)`, the `𝓡`-column = its **power-moment (Apéry) lane**.
No overlap — one measure, the two of them read off it.

**Next concrete steps (this lane):** (1) build the **difference** auxiliary for the `s=1` jet from the
`Γ`-recurrence (the multi-`q` SS form), not the differential OP; (2) make precise the claim that the
power→log moment passage is the `𝓡→K` (regular→wild) passage at the level of the Hankel/Toeplitz data;
(3) identify what, if anything, of the Apéry integer-point arithmetic survives the passage to the `s=1` jet
(the exact point where footholds are lost). Archived: `computations/2026-06-19-stieltjes-moment-problem.py`.

## §G The concrete difference auxiliary `R_P(s)=Σ_j a_j Γ(s+j)ζ(s+j)` (2026-06-19, Professor)

§F said "the auxiliary must be difference-based." Here it is, explicit and verified `[mpmath, |diff|≤3e−31]`.
For a polynomial `P(t)=Σ_{j=0}^d a_j t^j` (`a_j∈ℤ`), the auxiliary form against the ζ-measure is
```
   R_P(s) := ∫_0^∞ P(t)\,t^{s−1}\,\frac{dt}{e^t−1}
           = Σ_{j=0}^d a_j\,Γ(s+j)\,ζ(s+j).                                                  (G1)
```
*(Proof: term `a_j t^j`, sub `u=kt` in `∫t^{s+j−1}e^{−kt}dt=k^{−(s+j)}Γ(s+j)`, sum `Σ_k k^{−(s+j)}=ζ(s+j)`.)*

**This is the difference auxiliary, concretely.** `R_P` is a finite `ℤ`-combination of the **integer-shifted**
Mellin objects `Γ(s+j)ζ(s+j)`; the shift `s↦s+j` is the **`Γ`-recurrence** `Γ(s+1)=sΓ(s)` (the archimedean
`∂_s`-integrated difference) and the `ζ(s+j)` carry the prime `σ_p` structure. So `{Γ(s+j)ζ(s+j)}_j` lives in
the completed `(σ_p,∂_s)`-module (N1⁺); the auxiliary is **native by construction**, not a differential OP.

**The `s=1` jet — the retention tension, explicit.** At `s=1`:
- `j=0`: `Γ(s)ζ(s)=\frac1{s−1}+Φ(s)`, `Φ(s)=Σ_m \frac{I_m+J_m}{m!}(s−1)^m` carries the **`γ_n`** (realization
  card eq. (8));
- `j≥1`: `Γ(s+j)ζ(s+j)` is **regular** at `s=1`, value `j!\,ζ(j+1)` (the **ζ-values** / power-moments).

So `a_0` is the **`γ_n`-retention switch** (Wheeler's exact criterion, ζ-measure form): `a_0=0 ⟹` `R_P` is a
pole-free `ℤ`-linear form in `{j!ζ(j+1)}` = the **Apéry/ζ-value** lane; `a_0≠0 ⟹` the `γ_n` are retained **but
a pole appears**. The `γ_n`-retaining, pole-free auxiliary is the §B subtraction
`A_P(s):=R_P(s)−a_0/(s−1)=a_0Φ(s)+Σ_{j≥1}a_jΓ(s+j)ζ(s+j)`, whose `s=1` jet is the **joint** `ℤ`-form mixing
`{γ_n}` (from `a_0Φ`) with `{ζ(k)}` (from `j≥1`) — exactly the §B weld / #124 no-isolation, now produced by a
**single explicit auxiliary**.

**Where the apex now sits (sharp).** The Nesterenko inputs are concrete:
- *forms:* `A_P(s)` and its `s=1` derivatives, `P` ranging over `ℤ`-polynomials of degree `d` — a
  `(d+1)`-parameter family of joint `{γ_n}∪{ζ(k)}` forms;
- *growth (analytic):* `|A_P|` is controlled by `|P|` and the `Γ(s+j)ζ(s+j)` asymptotics — tractable;
- *the wall (arithmetic):* the **lower** bound on `|A_P^{(T)}(1)|` is the height vacuum — the `γ_n` part
  carries no denominator, while the `ζ(k)` part has the `lcm(1..n)` (Apéry) arithmetic. The **difference**
  between the two columns is exactly the `s↦s+1` shift behaviour: regular shifts (`j≥1`) have the prime/lcm
  arithmetic, the `j=0` jet does not. **The missing exp-F₁ = the arithmetic of the `j=0` (un-shifted) jet of
  `Γ(s)ζ(s)`** relative to its integer shifts.

This is the native difference auxiliary made fully explicit; the open core is its `s=1`-jet arithmetic
(obstruction C), now pinned to the single object `Γ(s)ζ(s)` and its integer shifts. Verified:
`computations/2026-06-19-stieltjes-moment-problem.py`.

## §H The auxiliary family is the `σ`-orbit of `Γζ` — native structure = G1, open apex = G2 (2026-06-19, Professor)

The §G family `{f_j}_{j≥0}`, `f_j(s)=Γ(s+j)ζ(s+j)`, has an exact native description under the shift
`σ:s↦s+1`:
```
   σ f_j = Γ(s+1+j)ζ(s+1+j) = f_{j+1}      ⟹   {f_j} = the σ-ORBIT of  f_0 = Γ(s)ζ(s) = Λ_+(s).   (H1)
```
`[verified, |diff|=0]`. So the §G auxiliary lives in the **`σ`-difference module generated by `Λ_+=Γζ`** —
the native completed object N1⁺ (additive completion). Its structure splits the problem cleanly along the
gatekeepers:

- **Difference-independence of `{f_j}` = G1 (difference-Hölder), PROVEN, BRIDGE.** `f_0=Γ(s)ζ(s)` satisfies
  **no finite-order `σ`-recurrence**: `σf_0/f_0 = s·ζ(s+1)/ζ(s)`, and `ζ(s+1)/ζ(s)` is **not a rational
  function of `s`** `[verified]`, so there is no first-order difference relation; the orbit is
  infinite-dimensional. This is exactly difference-Hölder (00-status #3: `ζ` has no finite `q`/shift-difference
  equation), already proven and **graded BRIDGE** (single archimedean shift; Door-2). **No new native content
  (no C5) hides in the auxiliary's difference structure.**
- **Value-independence at `s=1` = G2 / obstruction C, OPEN (the apex).** The §G remainder `A_P^{(T)}(1)` is a
  `ℤ`-form in the `s=1` *values* of the orbit — `{γ_n}` (from `f_0`'s jet) and `{ζ(k),ζ^{(m)}(k)}` (from
  `f_{j≥1}`). Difference-independence of the *functions* (G1, have it) does **not** give algebraic
  independence of their *values* (G2, the missing F₁ value-lift, #142). This is the function→value gap, here
  on the explicit `σ`-orbit of `Γζ`.

**Net (the §G–§H facet, complete).** The Stieltjes auxiliary is the `σ`-orbit of `Λ_+=Γζ`; its **function**
level is the proven BRIDGE G1 (difference-Hölder), and the entire open content is the **value** level at `s=1`
= G2 / obstruction C. So baker-for-stieltjes is, precisely, **G2 restricted to the `Λ_+`-orbit at `s=1`** —
confirming, on a fully explicit native object, the team verdict that the function/flow level is BRIDGE and the
sole apex is value-relations (DeWitt `K`, Wheeler saddle). Verified: `computations/2026-06-19-stieltjes-moment-problem.py`.

## Log (continued)
- 2026-06-19 — Professor: **reclaimed to in-progress to attack the apex** (not bank a shell; per user steer
  via chat id=236). First §F draft used the OPs of `dμ=dt/(e^t−1)` (moments `μ_j=j!ζ(j+1)`, verified exact).
- 2026-06-19 — Professor: **did the math, found+corrected my own error** (Anti-Cage). The power-moments
  `μ_j=j!ζ(j+1)` are the **integer ζ-values** (Apéry/Rivoal), **not** the `γ_n`; the `γ_n` are the
  **log-moments / `s=1` jet** of `Γ(s)ζ(s)`. **Finding (new, banked in §F):** the one measure `dt/(e^t−1)`
  carries **both** transcendence columns — power-moments = ζ-values = regular/motivic `𝓡` (Apéry footholds),
  log-moments = `γ_n` = wild/exponential `K` (no footholds) — so the abstract `𝓡/K` split (DeWitt #K /
  Wheeler `corank^{(T,U)}`) is the **power/log moment split of one measure**. The foothold asymmetry is
  located: the differential Siegel–Shidlovsky closes the ζ-value lane but is **killed by Hölder** on the
  `γ_n` jet (`Γζ` hypertranscendental), forcing the **difference** (multi-`q` SS / native G2) auxiliary —
  so `baker-for-stieltjes` ≡ native G2 on the log-moment lane, and the **height vacuum = the
  difference-arithmetic of the `s=1` jet**. `trdeg=∞` stays open; the attack is now the difference auxiliary,
  not the (dead) differential OP. Deconflicted with Wheeler (γ_E/ψ) and DeWitt (K-Galois): §F is the analytic
  realization of their split.
- 2026-06-19 — Professor: **built the difference auxiliary concretely** (§G), continuing the apex attack.
  `R_P(s)=∫P t^{s−1}/(e^t−1)dt=Σ_j a_j Γ(s+j)ζ(s+j)` (verified, |diff|≤3e−31): a finite ℤ-combination of
  integer-shifted `Γζ` (shift = `Γ`-recurrence = the difference structure; native `(σ_p,∂_s)`-module). `a_0`
  is the `γ_n`-retention switch (Wheeler's criterion, ζ-measure form); the pole-free `γ_n`-retaining auxiliary
  `A_P=R_P−a_0/(s−1)` gives joint `{γ_n}∪{ζ(k)}` ℤ-forms from a single explicit object. Apex pinned: the
  missing exp-F₁ = the `s=1`-jet arithmetic of `Γ(s)ζ(s)` (`j=0`) relative to its integer shifts (`j≥1`, which
  carry the Apéry `lcm` arithmetic). Builds on Wheeler's γ-blindness Lemma 5.1 (his `e^{−x}` atom; my measure
  is the integer-weighted `Σ_k e^{−kt}`). `trdeg=∞` open; the auxiliary is now explicit, native, difference-based.
- 2026-06-19 — Professor: **§H — located the native vs apex split on an explicit object.** The §G family
  `{Γ(s+j)ζ(s+j)}` is the `σ`-orbit (`σ:s↦s+1`) of `Λ_+=Γζ` (verified `σf_j=f_{j+1}`, `|diff|=0`); `f_0` has
  no finite `σ`-recurrence (`σf_0/f_0=s·ζ(s+1)/ζ(s)` not rational) = difference-Hölder (G1, proven BRIDGE). So
  the auxiliary's **function/difference** structure is the known BRIDGE G1, and the **only** open content is
  **value-independence at `s=1`** = G2/obstruction C. baker-for-stieltjes = G2 restricted to the `Λ_+`-orbit at
  `s=1`. Confirms (on a fully explicit native object) that the function level is BRIDGE and the sole apex is
  value-relations. No C5 hides in the auxiliary structure; the apex is purely the value-lift (#142).
