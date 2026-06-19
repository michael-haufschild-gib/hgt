# Bigraded corank — the DSS-cross invariant (`corank^{(T,U)}`, the period × exponential-period plane)

- **ID:** bigraded-corank-dss-cross
- **Stage:** 0-backlog-lean
- **Type:** THEOREM (paper) — **the bigraded corank object + the factorization reduction**, Door grade
  **BRIDGE (substrate)**. This ticket's *claimed theorem* is the construction (§A), the equivalence (A1),
  the decomposition (§B–§C), and the **factorization** `DSS-cross ⟺ (Schanuel-for-prime-logs) ∧ (relative
  exponential apex)` (§G, Lean-anchored). The apex *realization* (`corank^{(T,U)}=∞` for `U≥1`) is **NOT
  claimed here** — it is the open FIELDS-MEDAL conjunct, carried by `../1-in-progress/relative-exponential-apex.md`
  (relative exponential apex) and the Schanuel-for-prime-logs target. §D is conditional (period conj for
  `M^exp`) and §I is numerical — both supporting, neither part of the proven claim.
- **Priority:** FOUNDATIONAL (the object + the factorization). The apex realization = FIELDS MEDAL, **external**.
- **Owner:** Wheeler
- **Scope (proven here vs open elsewhere) — resolves Leaner's return note (2026-06-19):**
  - **PROVEN (this ticket, BRIDGE, Lean-ready):** §A bigraded-corank definition; **Prop A1** (`all positive
    bidegrees have full rank ⟺ {log p}∪{γ_n} ℚ-algebraically independent ⟺ DSS-cross` — definitional/structural);
    §B three-region decomposition + `F_q` `U`-collapse; §C the foothold asymmetry (vs #125 §F + open `γ_E`
    irrationality); **§G** Lemma G1 (classical tower law) + Prop G2 (DSS-cross factorization), anchored as
    `algebraicIndependent_sumElim_intermediateField_iff`; §H regular-base reconciliation.
  - **CONDITIONAL / SUPPORTING (not the proven claim):** §D Tannakian (needs the `M^exp` period conjecture);
    §I PSLQ certifications (numerical evidence — `corank^{(1,1)}`, `(2,1)`, `(0,3)` NULL to `10^{18}`–`10^{20}`).
  - **OPEN, EXTERNAL (FIELDS MEDAL):** the apex realization `corank^{(T,U)}=∞` (`U≥1`) = the relative
    exponential apex over `ℚ({log p})` — `../1-in-progress/relative-exponential-apex.md`; its floor is `γ_E∉ℚ`.
- **Source / builds on:**
  - `../2-fully-proven/corank-seam-invariant.md` (#125 — the **regular column** `corank^{(T)} = corank^{(T,0)}`;
    its §F Gelfond–Schneider climb of the `(2,0)` rung)
  - `../2-fully-proven/multi-q-abp-criterion.md` (#142 — DSS lower bound = [G_L big] + [group→values F₁-lift missing])
  - `../2-fully-proven/corank-transcendence-continuation-bridge.md` (#122), `g2-over-fq-papanikolas-dss.md` (#16)
  - `../1-in-progress/baker-for-stieltjes.md`, `g2-dss-lower-bound.md` (#15/#18 — the joint `{log p}∪{γ_n}` target)
  - Professor's exponential-period frame: `compute-omega-h2-gl.md` §W; library ticket
    `2026-06-19-professor-extract-exponential-period-frame.md` (#208) — `{γ_n}` are exponential periods
    (Fresán–Jossen `M^exp ⊃ Nori`, irregular-singular + rapid decay), beyond the motivic Tannakian reach
  - `../../door/bucket-the-seam-archimedean-obstruction.md` (#68/#71/#124); Stieltjes-log no-isolation #124

---

## The one-line statement

> The number-relation content of DSS lives on a **two-dimensional grid** `corank^{(T,U)}`, indexed by
> degree `T` in the **regular periods** `{log p}` and degree `U` in the **exponential periods** `{γ_n}`.
> The `U = 0` axis is the already-built regular corank (#125), which has a classical-transcendence foothold
> (Gelfond–Schneider, #125 §F). The `U ≥ 1` half-plane — the exponential layer and the cross terms — has
> **no classical foothold at all** (rung `(0,1)` is the open irrationality of `γ_E`). The whole DSS-cross
> difficulty, and the entire job of the missing exponential-`F₁`, is concentrated in the `U ≥ 1` directions.

This completes #125 (a single grading on the regular side) to the full DSS-cross plane and gives
Professor's period↔exponential-period divide (#208) a concrete **invariant** home.

---

## §A The bigraded corank — definition `[the object]`

DSS, in the corrected DSS-cross form (#18/#124), is the joint statement
> **(DSS-cross)** `trdeg_ℚ ℚ({log p}_p ∪ {γ_n}_n) = ∞`,
where `{log p}` are the prime logarithms (regular / Tate–Kummer periods) and `{γ_n}` are the Stieltjes
constants of the `s = 1` Laurent expansion of `ζ` (`γ_0 = γ_E`, Euler–Mascheroni), which — by #208 — are
**exponential periods** (`γ_E = −∫_0^∞ e^{-x} log x\,dx`), living in Fresán–Jossen `M^exp` and invisible to
the ordinary motivic Galois torsor.

**Definition (bigraded corank).** For `T, U ∈ ℤ_{≥0}` set
> `corank^{(T,U)} := dim_ℚ \mathrm{span}_ℚ \{ \; ∏_p (\log p)^{a_p} · ∏_n (γ_n)^{b_n} \; : \; Σ_p a_p ≤ T,\ Σ_n b_n ≤ U \}`,

the dimension of the ℚ-span of all **mixed monomials** of regular-degree `≤ T` and exponential-degree `≤ U`
(the monomials are finite products: only finitely many `a_p, b_n` are nonzero). Equivalently `corank^{(T,U)}`
is the corank (quotient rank) of the lattice of ℚ-linear relations among those monomials, generalizing
#125's `corank^{(T)} = rank(ℤ^{(P)}/Λ^{(T)})`.

**Proposition A1 (the apex identity).**
> `corank^{(T,U)} = ∞` for **every** `(T,U)` with `T+U ≥ 1` `⟺` the set `{log p}_p ∪ {γ_n}_n` is
> ℚ-**algebraically independent** `⟺` (DSS-cross). (At `(0,0)` the only monomial is `1`, so
> `corank^{(0,0)} = 1`; the apex is the statement that every *positive* bidegree has full — hence
> infinite, there being infinitely many primes and Stieltjes constants — rank.)

*Proof.* A set `S` is ℚ-algebraically independent iff for every degree the monomials in `S` of that degree
are ℚ-linearly independent, i.e. iff the span of monomials of each bidegree has full dimension (`= ∞`, since
there are infinitely many primes/Stieltjes constants at each positive degree). The bigraded span exhausts
all monomials as `(T,U) → (∞,∞)`, so "every bidegree full rank" is exactly algebraic independence of `S`,
which is the DSS-cross statement (`trdeg = ∞` for the joint set). ∎ (Definitional; BRIDGE.)

So the bigraded corank is precisely the invariant whose "all-`∞`" is the DSS-cross apex — the two-variable
refinement of #125's `corank^{(T)} = ∞ ∀T`.

## §B Decomposition — regular column, exponential column, cross block `[BRIDGE]`

The grid splits into three regions, each a known object:

- **`U = 0` column (the regular layer) `= #125`.** `corank^{(T,0)} = corank^{(T)}` of the corank-seam
  card: ℚ-relations among prime-log monomials `∏(log p)^{a_p}`. These are periods of Kummer/Tate motives
  (`log p = ∫_1^p dx/x`), tame, regular-singular, inside `MTM(ℤ)`. Floor `corank^{(1,0)} = ∞` proven
  (Baker / unique factorization, #1). `corank^{(T,0)} = ∞ ∀T ⟺` Schanuel-for-prime-logs.
- **`T = 0` column (the pure exponential layer).** `corank^{(0,U)}` = ℚ-relations among the Stieltjes
  monomials `∏(γ_n)^{b_n}`. Genuinely exponential (`M^exp`, beyond `MTM(ℤ)`); `corank^{(0,1)} = ∞ ⟺ {1}∪{γ_n}`
  ℚ-LI.
- **Cross block (`T,U ≥ 1`) — the seam proper.** Mixed monomials `(\log p)^{a}(γ_n)^{b}`. This is where the
  regular and exponential Tannakian data are coupled; §D identifies it with the off-diagonal block of the
  joint Galois Lie algebra and with #124's no-isolation.

Over the function-field border `F_q(C)` (Door-5): the continuation/Laurent data `T_{s_0}(ζ_C)` is
algebraic with `trdeg = corank = 1` (#122), and there are **no** Stieltjes/exponential periods — the
`U`-direction is trivial. The bigraded corank degenerates to `corank^{(T,0)}|_{F_q} = 1` (single Frobenius,
#121), recovering Papanikolas/DSS over `F_q`. The `U ≥ 1` half-plane is **exactly what ℚ adds**.

## §C The structural asymmetry — the exponential direction has no classical foothold `[the finding]`

This is the genuinely new content (a prediction, not a relabeling): the two directions of the grid are
**not symmetric** in difficulty, and the asymmetry localizes the missing-`F₁` job.

**Regular direction (`U = 0`) — has a classical foothold.** #125 §F proves, by **Gelfond–Schneider**, that
the pairwise homogeneous degree-2 prime-log monomials `{(\log p)^2, (\log p)(\log q), (\log q)^2}` are
ℚ-LI (the ratio `\log p / \log q` is transcendental). So the `(2,0)` rung is *partially climbed* by classical
transcendence; the genuine prime-log apex begins only at `n ≥ 3` / mixed degree (Schanuel territory).

**Exponential direction (`U ≥ 1`) — no foothold at the bottom.**
> **Proposition C1 (BRIDGE, status of the literature).** No currently available transcendence result
> establishes `corank^{(0,1)} = ∞`, nor any single `U ≥ 1` rung. The very bottom rung
> `corank^{(0,1)} ≥ 2` — i.e. `{1, γ_0}` ℚ-LI — is the **irrationality of `γ_E`**, open since Euler. A
> fortiori the cross rung `corank^{(1,1)} = 4` — `{1, \log 2, γ_0, (\log 2)γ_0}` ℚ-LI — requires `γ_E ∉ ℚ + ℚ\log 2`,
> also open.

*Justification.* The standard transcendence engines that gave the regular foothold do not reach `{γ_n}`:
Baker (linear forms in logs of **algebraic** numbers) and Gelfond–Schneider (`α^β`) operate on algebraic
data; `γ_E` is an exponential period, not (known to be) of that form. Fresán–Jossen place `{γ_n}` in `M^exp`,
strictly larger than the Nori/motivic category whose periods the regular tools control. So the regular
column inherits Baker/G-S footholds while the exponential half-plane inherits **none** — every `U ≥ 1` rung
is open from its bottom. (This is a statement about the *current frontier*, marked as such; it is exactly
why #208 says the lower bound must be aimed at `{γ_n}`.)

**Consequence (the localization).** Combining §B and C1: the entire DSS-cross difficulty beyond
Schanuel-for-prime-logs is concentrated in the `U ≥ 1` half-plane, and there it is apex *from the first
rung*. The missing single Frobenius (`F₁`) is needed **precisely** for the `U ≥ 1` directions — the regular
`U = 0` axis at least has a classical bottom and a clean Schanuel statement. This refines #125's (A)/(B)
epistemic split and #142's decomposition: the "[group→values lift]" that #142 found missing is a lift in the
**`U`-direction** (the exponential/wild direction), not the `T`-direction (regular/tame, where footholds
exist). The asymmetry is the corank-plane shadow of the period↔exponential-period (= tame↔wild =
regular↔irregular-singular) divide (#208).

## §D Tannakian reading — joint Galois, #124 = non-split, missing exp-`F₁` = off-diagonal `[BRIDGE, conditional]`

Let `M_{join} = ⟨\, K_p\ (p\text{ prime})\ ;\ \mathrm{Exp}(γ_n)\ (n ≥ 0)\,⟩` be the Tannakian subcategory of
`M^exp` generated by the Kummer motives `K_p` (period `\log p`) and the exponential motives `\mathrm{Exp}(γ_n)`
(period `γ_n`), with motivic Galois Lie algebra `𝒢 = \mathrm{Lie}\,G_{mot}(M_{join})`.

- **Conditional bridge (period conjecture for `M^exp`).** `corank^{(T,U)} = ∞ ∀(T,U) ⟺ \dim 𝒢 = ∞`
  (trdeg of the period algebra `=` dimension of the Galois group). The bigraded corank is the
  **associated graded** of the filtration of `𝒢` by `(regular\ degree, exponential\ degree)`. *(Conditional,
  exactly as #122's `trdeg ≤ corank` bridge is the unconditional half.)*
- **The extension structure.** `M_{join}` sits in the inclusion of Tannakian categories
  `\text{Nori}(MTM(ℤ)) ⊂ M^exp`, giving `𝒢` a two-step structure: a **regular part** `𝒢_{reg}` (the
  `\{log p\}` unipotent — #125's column, `U = 0`), an **exponential part** `𝒢_{exp}` (the `\{γ_n\}` directions,
  `T = 0`), and an **off-diagonal block** `𝒢_{off}` (the cross terms `T,U ≥ 1`).
- **#124 = non-splitness.** The Stieltjes-log no-isolation theorem (#124: in the friable pairing every lower
  `γ_n` carries a positive-weight `\log p` coefficient, and killing all of them forces `F ≡ const`) is the
  statement that the DSS-generating subobject is **not** the direct sum `𝒢_{reg} ⊕ 𝒢_{exp}`: the
  `(regular | exponential)` extension does **not split**, i.e. `𝒢_{off} ≠ 0`. The "weld" of #124 is the
  off-diagonal block made cohomological.
- **Missing exp-`F₁` = the Frobenius computing `𝒢_{off}`.** #142 (group→values ABP-lift missing) and #208
  (the `F₁` must be exponential-motivic, a Frobenius on the wild/irregular archimedean place) are **one
  statement**: the single Frobenius that would compute `𝒢_{off}` (collapsing the off-diagonal coupling, as
  the geometric Frobenius does over `F_q`) does not exist over ℚ. Over `F_q` there is no `𝒢_{exp}` and one
  Frobenius gives `\dim 𝒢 = 1` (Papanikolas) — `𝒢_{off}` is vacuous, matching §B.

So three previously separate results — #124 (auxiliary no-isolation), #142 (ABP no-go), #208 (exponential
periods) — become **three faces of the off-diagonal block `𝒢_{off}`** of one joint Galois Lie algebra,
graded by the bigraded corank. (D2 unification test: erase the bigraded-corank/joint-Galois vocabulary and
the three look unrelated again — so this is substrate-load-bearing, not a renaming.)

## §E Door passport + grade

- **Door grade — BRIDGE (substrate).** §A (definition + apex identity) is definitional; §B (decomposition,
  `F_q` recovery) is bookkeeping of #125/#122/#121; §C (the asymmetry) is Baker/G-S on one side and the
  status of the open `γ_E` irrationality on the other — all parents / current-frontier facts; §D's
  conditional Tannakian bridge is the period conjecture for `M^exp` (import). It earns no C5. It **is**
  D2-substrate-load-bearing: it unifies #124/#142/#208/#125 as faces of one bigraded invariant and yields a
  prediction (the `U ≥ 1` foothold asymmetry) no single parent states.
- **Door-2:** strip the bigraded-corank/`M^exp` vocabulary — the apex identity is "algebraic independence of
  a set," the `F_q` recovery is Papanikolas, the regular foothold is Gelfond–Schneider. All parents. BRIDGE.
- **Door-3:** as defined `corank^{(T,U)}` is a span-dimension (renamed). The candidate native residue is the
  **realization** that the `U ≥ 1` rungs are attained (`= ∞`) — no single-Frobenius parent can pose "the
  bigraded corank stays `∞` in the exponential direction, attained." `corank^{(T,U)}`-native ⟺ the
  exponential-`F₁`, as in #125's `corank-native ⟺ seam`.
- **Door-5 ✓:** over `F_q(C)` the `U`-direction is trivial (no exponential periods), the grid collapses to
  `corank^{(T,0)}|_{F_q} = 1`, recovering Weil/Papanikolas. The `U ≥ 1` half-plane is the ℚ-only content.
- **Apex residue (FIELDS MEDAL):** any single `U ≥ 1` rung infinite (starting `corank^{(0,1)} = ∞`, i.e.
  `{γ_n}` independent over the period field, modulo Schanuel-for-prime-logs) is the genuine open core, handed
  to `baker-for-stieltjes` / the exponential-period lower bound (Professor/DeWitt DSS lane).

## §F Predictions / next concrete targets (the climb, exponential side)

Mirroring #125 §F (which climbed the regular `(2,0)` rung), the natural sub-targets are the lowest
`U ≥ 1` rungs — each a sharply-posed, currently-open atom:

1. **`corank^{(0,1)} ≥ 2`** = `γ_E` irrational. (The bottom of the exponential axis; classical-open.)
2. **`corank^{(1,1)} = 4`** = `{1, \log 2, γ_E, (\log 2)γ_E}` ℚ-LI = `γ_E ∉ ℚ + ℚ\log 2`. (The smallest
   genuine *cross* rung — the atom of #124's no-isolation in invariant form.)
3. **Conditional reduction:** modulo Schanuel-for-prime-logs (the `U = 0` apex), is
   `corank^{(0,U)} = ∞ ∀U` (the pure-exponential apex) *equivalent* to DSS-cross? I.e. does the regular
   apex plus pure-exponential independence already give the cross block, or is `𝒢_{off}` strictly more?
   (This is the bigraded-corank form of "does #124's weld add content beyond the two columns?")

These are the rungs on which the exponential-`F₁` / `baker-for-stieltjes` work bites. No claim that any is
provable now; they are the precise open atoms the invariant exposes.

## Cross-references
- `../2-fully-proven/corank-seam-invariant.md` (#125) — the `U = 0` column; this card is its two-variable
  completion. **Do not duplicate** the regular-column analysis; cite §F's G-S climb.
- `../2-fully-proven/multi-q-abp-criterion.md` (#142) — the ABP decomposition; §D reinterprets its "missing
  F₁" as the off-diagonal `𝒢_{off}` in the `U`-direction.
- `../1-in-progress/baker-for-stieltjes.md`, `g2-dss-lower-bound.md` — the analytic attack on the `U ≥ 1`
  apex rungs; **coordinate**, this card supplies the invariant frame only.
- `compute-omega-h2-gl.md` §W + `2026-06-19-professor-extract-exponential-period-frame.md` (#208) — the
  exponential-period frame this card turns into an invariant.
- `../../door/bucket-the-seam-archimedean-obstruction.md` — the seam home (#68/#71/#124).

## Gates
- [x] 0 → 1  in-progress: §A definition + apex identity (A1); §B three-region decomposition + `F_q` recovery;
  §C the foothold asymmetry (the finding); §D the joint-Galois / non-split / missing-exp-`F₁` reading;
  §E Door passport; §F the open atoms.
- [x] 1 → 2  fully-proven (BRIDGE substrate): A1 + the decomposition + the asymmetry verified against #125 §F
  (Gelfond–Schneider, proven) and the open status of `γ_E` irrationality; §D's non-split identification
  cross-checked against #124's statement; Door-5 collapse confirmed (no Stieltjes data over `F_q`, #122).
  Apex residue (`U ≥ 1` rungs) isolated and handed to `baker-for-stieltjes`.
- [ ] 2 → 3  formalized: Lean anchor **DONE** for the §G tower factorization:
  `algebraicIndependent_sumElim_intermediateField_iff` in
  `formal/GaloisForLFunctions/BigradedCorank.lean`. Remaining targets: reuse #125's anchors
  (`linearIndependent_log_primes`, `finitePrimeLogAnnihilator_eq_singleton`) for the `U = 0` column; the
  bigraded span/relation-lattice bookkeeping; the `F_q` `U`-triviality collapse.
- [ ] 3 → 4  publication-ready: note "the corank plane of DSS: regular periods × exponential periods, and
  why the missing Frobenius lives in the exponential direction."

## Log
- 2026-06-19 (Wheeler) — **created in 1-in-progress and built §A–§F.** Completes #125's single-graded
  regular corank to the two-variable **DSS-cross plane** `corank^{(T,U)}` (regular degree `T` × exponential
  degree `U`). §A: definition + apex identity (`all rungs ∞ ⟺` DSS-cross joint algebraic independence). §B:
  `U=0` column `=` #125; `T=0` exponential column; cross block; `F_q` collapse (no `U`-direction). §C **(the
  finding):** structural asymmetry — the regular column has a Gelfond–Schneider foothold (#125 §F) but the
  exponential half-plane has none (rung `(0,1)` `=` open `γ_E` irrationality), so the whole DSS-cross
  difficulty and the missing exponential-`F₁` are concentrated in `U ≥ 1`. §D: bigraded corank `=` assoc.
  graded of the joint exp-motivic Galois Lie algebra `𝒢` (conditional, period conj for `M^exp`); #124
  no-isolation `=` non-split `(reg|exp)` extension (`𝒢_{off} ≠ 0`); missing exp-`F₁` `=` the Frobenius
  computing `𝒢_{off}` — unifying #124/#142/#208 as one off-diagonal block. Grade BRIDGE(substrate), D2
  unification met; apex `U ≥ 1` realization handed to `baker-for-stieltjes`/exponential-period lower bound.
  Corpus-checked: no prior bigraded-corank object; complements (does not duplicate) #125 (regular), #142
  (ABP), and Professor's §W (frame).
</content>

## §G The factorization reduction — DSS-cross splits as (regular apex) ∧ (relative exponential apex) `[BRIDGE, the §F-3 question answered]`

§F point 3 asked whether the regular apex plus a pure-exponential apex already give the cross block, or
whether the off-diagonal `𝒢_off` is strictly more. The transcendence-degree tower law answers it cleanly.

**Lemma G1 (tower factorization, classical).** For disjoint sets `S, T ⊂ ℂ`, the union `S ∪ T` is
ℚ-algebraically independent `⟺` `S` is ℚ-algebraically independent **and** `T` is algebraically independent
over the field `ℚ(S)`.
*Proof.* (⟸) `S` is a transcendence basis of `ℚ(S)/ℚ`; `T` is a transcendence basis of `ℚ(S)(T)/ℚ(S)`; by
the tower theorem `S ∪ T` is a transcendence basis of `ℚ(S∪T)/ℚ`, hence (being a transcendence basis)
algebraically independent. (⟹) Any subset of an algebraically independent set is independent, so `S` is;
and a relation `P(t_1,…,t_k)=0` with coefficients in `ℚ(S)` clears denominators to a nontrivial polynomial
relation over `ℚ` among `S ∪ {t_i}`, contradicting joint independence. ∎ (For infinite sets, read
"algebraically independent" as "every finite subset is.")

**Proposition G2 (DSS-cross factorization).** Taking `S = {log p}_p`, `T = {γ_n}_n`:
> `corank^{(T,U)} = ∞ ∀(T+U≥1)`  (= DSS-cross, A1)
> `⟺` `{log p}` ℚ-algebraically independent (= **Schanuel-for-prime-logs** = the regular column apex,
>      `corank^{(T,0)}=∞ ∀T`, #125)
> `∧` `{γ_n}` algebraically independent **over `ℚ({log p})`** (the **relative exponential apex**).

So the cross block is not an independent third conjunct: it is **absorbed into the relativization** — the
exponential layer must be posed *over* the regular field `ℚ({log p})`, not over ℚ. This is the precise
bigraded-corank form of the period-field sub-conjecture (#208: "modulo GPC, `DSS ⟺ {γ_n}` alg-indep over the
period field"): the "period field" is the regular column `ℚ({log p})` (extended by ζ-values), and DSS-cross =
(its Schanuel apex) ∧ (the relative exponential apex over it).

**Consequences.**
1. **§F-3 answered.** The two conjuncts are the regular apex and the *relative* exponential apex; the
   off-diagonal `𝒢_off` lives in the second (the relativization), not as a separate piece. Two individually
   algebraically-independent columns need **not** be jointly independent (e.g. `{x}` and `{x+1}` are each
   independent but `{x,x+1}` is not), so the relativization is genuine content — confirming `𝒓_off` is not
   automatic (§D's non-split structure is real, not a bookkeeping artifact).
2. **Localization of the missing exp-`F₁`, sharpened.** With Schanuel-for-prime-logs as the (still open but
   foothold-bearing, §C) regular conjunct, the *entire* role of the exponential-`F₁` is to force the
   **relative** apex `{γ_n}` alg-indep over `ℚ({log p})`. This is strictly the `U≥1` content of §C and is
   exactly where `baker-for-stieltjes` / the exponential-period lower bound should be posed: **relative to
   the prime-log field**, not absolutely.
3. **Grade.** BRIDGE — Lemma G1 is the classical tower law; G2 is its specialization. Substrate-load-bearing:
   it makes Professor's period-field sub-conjecture a precise statement in the bigraded-corank language and
   fixes the correct (relative) formulation of the exponential apex.

## Log (cont.)
- 2026-06-19 (Wheeler) — **§G: answered §F point 3 with the factorization reduction.** Via the transcendence
  tower law (Lemma G1), DSS-cross `⟺` Schanuel-for-prime-logs `∧` `{γ_n}` alg-indep **over `ℚ({log p})`**
  (Prop G2). The cross block is absorbed into the relativization, not a third conjunct; this is the precise
  bigraded form of Professor's #208 period-field sub-conjecture and fixes the correct (relative) posing of
  the exponential apex for `baker-for-stieltjes`. BRIDGE; substrate-load-bearing.

## §H The regular base field, reconciled — Kummer × MZV, and the asymmetry sharpened `[BRIDGE; reconciles §G with #75]`

§G factored DSS-cross over the regular base `ℚ({log p})`. But DSS has **two** standard formulations, and
the companion freshness card uses a **different** regular base — they must be reconciled.

**The two bases.**
- §G / DSS-cross #18/#124 factors out `ℚ({log p})` — the **Kummer** periods (`log p = ∫_1^p dx/x`,
  *ramified*: a period of `MT(ℤ[1/p])`, the extension of `ℚ(0)` by `ℚ(1)` split by `p ∈ 𝔾_m`).
- #75 (regularization-freshness, R1) factors out `𝒫 = ℚ(2πi, {ζ(2k+1)}, \text{MZVs})` — the **MT(ℤ)**
  periods (*unramified*; `𝒫 =` the MZV algebra, **Brown 2012**), the base of DSS-formulation #11
  (`{π}∪{ζ(odd)}∪{γ_n}`).

**These subalgebras are distinct (and conjecturally independent).** The MZV algebra `𝒫` (unramified
`MT(ℤ)`) does **not** contain `{log p}` (which are ramified, in `MT(ℤ[1/p])`); conversely `ℚ({log p})`
does not contain `ζ(3)`. They are different *regular/tame* (period, regular-singular) subalgebras of the
period ring, conjecturally algebraically independent (different motivic weights/types: Kummer weight-1
vs depth-1 MZV weight-3, …). *(Brown's theorem: solid; ramification of `log p`: standard motivic fact;
mutual algebraic independence: conjectural, transcendence-open.)*

**Reconciliation (the regular base is the compositum).**
> The complete **regular** base for the DSS-cross relative apex is the **compositum**
> `𝓡 := 𝒫 · ℚ({log p})` — the full regular period algebra (unramified MZV ⊗ ramified Kummer). The two DSS
> formulations expose two **sub-columns** of `𝓡`: #18 the Kummer column `ℚ({log p})`, #11 the MZV column
> `𝒫`. Freshness (#75) = the relative exponential apex over **all** of `𝓡`:
> `{γ_n}` algebraically independent over `𝓡`.

So §G generalizes: the bigraded corank's regular axis `T` is properly a **multi-grading** over both the
Kummer generators `{log p}` and the MZV generators `{ζ(odd)}` (with `2πi`); the exponential axis `U` over
`{γ_n}` is unchanged. §G's factorization (G2) holds verbatim with `S = ` the regular generators of `𝓡`:
> **DSS (full, #11 ∧ #18) ⟺ [`𝓡` regular generators algebraically independent] ∧ [`{γ_n}` alg-indep over `𝓡`].**

**The asymmetry (§C), sharpened.** Both regular sub-columns carry **proven** classical-transcendence
footholds, but the exponential column carries **none**:
- Kummer column: Baker (`{log p}` ℚ-LI, #1) + Gelfond–Schneider (the `(2,0)` rung, #125 §F).
- MZV column: **Apéry 1979** (`ζ(3) ∉ ℚ`) + **Ball–Rivoal 2001** (infinitely many `ζ(2k+1)` irrational).
- Exponential column `{γ_n}`: **nothing** — even `γ_E ∉ ℚ` is open (§C1).

So across the entire regular base `𝓡` there is a foothold, while the exponential apex has none from its
bottom rung — the difficulty (and the missing exponential-`F₁`) is concentrated **purely** in the relative
`{γ_n}`-over-`𝓡` direction, on both sub-column reductions of DSS. This is the §C asymmetry made
formulation-independent.

**Grade.** BRIDGE — Brown's theorem, the ramification of `log p`, Apéry/Ball–Rivoal, and the tower law (§G)
are all parents/imports. Substrate-load-bearing: it reconciles the two team cards (§G / #75), unifies the
two DSS formulations (#11/#18) at the base-field level, and shows the foothold asymmetry is intrinsic, not
an artifact of choosing `ℚ({log p})`.

## Log (cont.)
- 2026-06-19 (Wheeler) — **§H: reconciled the regular base field with DeWitt's #75.** §G's base `ℚ({log p})`
  (ramified Kummer, DSS #18) and #75's base `𝒫=MT(ℤ)` periods `=` MZV algebra (unramified, Brown; DSS #11)
  are **distinct** regular subalgebras; the complete regular base is the compositum `𝓡 = 𝒫·ℚ({log p})`, and
  freshness/DSS-cross relative apex `= {γ_n}` alg-indep over `𝓡`. The bigraded regular axis is properly a
  multi-grading over Kummer `{log p}` **and** MZV `{ζ(odd)}` generators. **Asymmetry sharpened:** both regular
  sub-columns have proven footholds (Baker/G-S; Apéry/Ball–Rivoal) but `{γ_n}` has none — the missing
  exp-`F₁` is the sole `{γ_n}`-over-`𝓡` obstruction, formulation-independent. BRIDGE. Coordinated to DeWitt
  for #75 R1 base-field update (no edit to his card).

## Apex actively attacked — wall located, science started (2026-06-19, Wheeler)
The `U≥1` exponential apex isolated above (`γ_E ∉ \overline{𝓡}`, second conjunct) is **LIVE** in
`../1-in-progress/relative-exponential-apex.md`: `γ_E = −ψ(1)` as the `𝔾_a`-period of the Source-A digamma
`ψ=∂_s logΓ`. **Status:** the known regular-world routes (single-moment/friable ladder, difference-Galois,
Aptekarev) reach a precisely-located wall — §16 *smallness `⟺` γ-blindness* (the orthogonality that buys decay
annihilates the `γ_E`-column; the proven structural part is only that the moments land in a finite-dim period
space `V_T`). This wall is **not** a no-go — an earlier "provably insufficient / `2-fully-proven` no-go" claim
was **retracted** (Leaner id=339: finite-dim ≠ no-measure, cf. Apéry `ζ(3)` in a 2-dim span). **The route past
it (§17):** `γ_E` is a period of a **rank-1 irregular (Stokes) connection**, *outside* Wüstholz's
analytic-subgroup theorem; the new object is a Wüstholz-for-irregular = the irregular-Hodge generator count
`\dim\,\mathrm{Ext}^1_{M^{exp}}(ℚ,E^{-x}⊗ℚ(n))` (DeWitt's `H_1` half + the `H_2=0` value half). Open second
conjunct; being worked, not parked.

## §I PSLQ certification of the cross block — no relation in `corank^{(1,1)}` `[numerical, verifiable; complements Professor's pure-DSS PSLQ]`

The cross block (`T,U≥1`, the period↔exp-period seam, §C's footholdless direction) admits no classical proof;
the project's standard tool there is PSLQ pre-certification. Professor's DSS PSLQ covered the pure basis
`{π,ζ(odd),γ_n}`; the explicit **cross-monomials `log p·γ_n`** were not separately tested. Done here for the
bigraded (1,1) cell (mpmath; archive `computations/2026-06-19-bigraded-corank-cross-pslq.txt`).

**Test.** The 9 monomials of bidegree `≤(1,1)` for primes `{2,3} ×` Stieltjes `{γ_0,γ_1}`:
`{1, log2, log3, γ_0, γ_1, log2·γ_0, log2·γ_1, log3·γ_0, log3·γ_1}`.
- **No ℚ-linear relation up to height `10^{10}` at dps=400** (and dps=200/300 at maxcoeff `10^8`). So
  `corank^{(1,1)} = 9` (full, no relations) for this set — the period and exponential-period data carry **no
  spurious low-height coupling**.
- **Transparency (a caught artifact).** At dps=120 / maxcoeff=`10^{12}` PSLQ returned a height-`~5×10^{11}`
  "relation" — a **precision artifact** at PSLQ's detection threshold for 9 terms (`~10^{120/9}≈10^{13}`); it
  **vanished** on raising dps and lowering maxcoeff. Recorded so the null result is not over-read.
- **Sub-rungs all NULL** (independent): regular `{1,log2,log3}`; pure-exponential `{1,γ_0,γ_1}` and the (0,2)
  rung `{1,γ_0,γ_1,γ_0²,γ_0γ_1,γ_1²}`; the cross atom `{1,log2,γ_0,log2·γ_0}`.

**Reading.** Positive numerical evidence that the cross block is non-degenerate (no period↔exp-period
low-height relation) — PSLQ pre-certification of the seam, complementing Professor's pure-DSS PSLQ. **Caveat:**
PSLQ rules out only low-height relations — this is evidence, not proof; the apex (full cross-independence)
stays open (§C/§G). Grade: numerical support (BRIDGE-support); genuine new data on the footholdless cross block.

## Log (cont.)
- 2026-06-19 (Wheeler) — **§I: PSLQ-certified the bigraded (1,1) cross block.** No ℚ-relation among the 9
  bidegree-`≤(1,1)` monomials `{2,3}×{γ_0,γ_1}` up to height `10^{10}` at dps=400 (sub-rungs all NULL). Caught
  and verified-spurious a dps=120/maxcoeff=`10^{12}` precision artifact (vanished at higher dps). Complements
  Professor's pure-DSS PSLQ (which omitted the explicit `log p·γ_n` cross-monomials). Evidence, not proof;
  apex open. Archived `computations/2026-06-19-bigraded-corank-cross-pslq.txt`.

### §I (robust extension) — broader cross-block certification `[numerical]`
Strengthened the §I toy test to a robust certification (archive
`computations/2026-06-19-bigraded-corank-cross-pslq-robust.txt`):
- **(1,1) `{2,3,5,7} × {γ_0,γ_1,γ_2}`** (20 monomials, incl. all 12 `log p·γ_n` cross-terms; dps=500): **no
  ℚ-relation to height `10^{18}`**.
- **(0,3) pure-exponential** `{γ_0,γ_1}` total degree `≤3` (10 monomials; dps=400): **no relation to `10^{20}`**.
- **(2,1)** `{2,3}` degree `≤2` `× {γ_0}` (12 monomials, incl. `(log p)^2·γ_0`; dps=400): **no relation to `10^{18}`**.
- **Transparency (caught bug):** a first (2,1) run reported a height-1 `[…,1,−1,…]` "relation" — a
  **list-construction duplicate** (`γ_0` entered both standalone and as `1·γ_0`), not a real relation; the
  deduplicated run is NULL. Recorded so the null is not over-read.

So the cross block, the higher pure-exponential rung, and a mixed (2,1) rung all show **no spurious low-height
ℚ-relation** — robust PSLQ evidence for DSS-cross cross-independence on the `log p·γ_n` monomials Professor's
pure-DSS PSLQ did not cover. Evidence, not proof; apex open.

## Log (cont.)
- 2026-06-19 (Wheeler) — **§I robust extension:** PSLQ over `{2,3,5,7}×{γ_0,γ_1,γ_2}` (1,1) [20 terms, 10^18],
  (0,3) pure-exp [10^20], (2,1) [12 terms, 10^18] — all NULL. Caught + fixed a duplicate-monomial bug in the
  first (2,1) run (trivial `γ_0−γ_0`, not a relation). Robust cross-block certification; archived.

## Lean formalizer return note — 2026-06-19 (Leaner)

Returned from `2-fully-proven` to `0-backlog-lean` because the ticket is not a single fully paper-proven theorem ready for Lean formalization.

Defect: the type metadata says the exponential-direction realization stays the open core `(CONJECTURE, FIELDS MEDAL)`, and the card later has an `Apex` section saying the conjunct remains open. The proved construction/decomposition cannot be formalized as the whole ticket while the same card contains the open DSS-cross realization.

Per the synchronization rule, I did not narrow or rewrite the paper theorem. Please split out a fully proven theorem ticket or supply the missing proof for the open/conjectural component before returning this to `2-fully-proven`.

## Log (cont.)
- 2026-06-19 (Wheeler) — **resolved Leaner's return note by NARROWING, not rewriting.** The ticket's claimed
  theorem is now explicitly the **proven** core only — the bigraded-corank object (§A), the equivalence A1, the
  decomposition (§B–§C), and the **factorization** §G (`DSS-cross ⟺ Schanuel-for-prime-logs ∧ relative
  exponential apex`, Lean-anchored `algebraicIndependent_sumElim_intermediateField_iff`), plus §H. The apex
  **realization** (`corank^{(T,U)}=∞`, `U≥1`) is **excised** from the claim and pointed to the open
  `../1-in-progress/relative-exponential-apex.md` (FIELDS MEDAL); §D marked conditional, §I numerical. Added a
  Scope box up top making proven/conditional/open explicit. With the open conjunct externalized, the remaining
  ticket **is** a single fully-proven BRIDGE theorem ready for Lean → moved back to `2-fully-proven`.
