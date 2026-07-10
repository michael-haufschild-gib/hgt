# Corank as the unifying seam invariant — the `∞ − 1` identity (G1 ∧ G2 ∧ G4, one number)

- **ID:** corank-seam-invariant
- **Stage:** 0-backlog-lean
- **Type:** THEOREM (paper) — **the unified corank object + the level-separation theorem**, Door grade
  **BRIDGE**. This ticket's *claimed theorem* is the unified-corank construction (§A), the **level-separation**
  (§B: `corank` is linear and `< trdeg` algebraic — the three faces are NOT equivalent), the graded-corank
  filtration (§C) with the proven floor `corank^{(1)}=∞`, and the §F Gelfond–Schneider degree-2 partial climb.
  The apex **realization** (`corank^{(T)}=∞` for `T≥2` = Schanuel-for-prime-logs) is **NOT claimed here** — it
  is the open FIELDS-MEDAL conjunct, carried by the regular-column Schanuel target
  (`../1-in-progress/baker-for-stieltjes.md`, `../1-in-progress/g2-dss-lower-bound.md`).
- **Priority:** FOUNDATIONAL (the object + level separation). The apex realization = FIELDS MEDAL, **external**.
- **Scope (proven here vs open elsewhere) — resolves Leaner's return note (2026-06-19):**
  - **PROVEN (this ticket, BRIDGE, Lean-ready):** §A unified corank (one number, three faces; **border collapse
    proven** — `corank=1` over `F_q`, all faces degenerate to Weil/Papanikolas/Deligne–Katz); **§B
    level-separation theorem** (`corank=∞` ⟺ `{log p}` ℚ-LINEARLY independent, PROVEN via Baker/unique
    factorization; this does NOT force `trdeg=∞`, since `trdeg ≤ corank` only — #122 — so G1 linear floor ⊊
    G2/G4 algebraic apex); §C graded-corank filtration with floor `corank^{(1)}=∞` PROVEN; §F the
    Gelfond–Schneider pairwise homogeneous degree-2 rung.
  - **OPEN, EXTERNAL (FIELDS MEDAL):** the realization `corank^{(T)}=∞` for `T≥2` = Schanuel-for-prime-logs =
    the missing single Frobenius F₁; first open rung `corank^{(2)}=∞` is open even for `{log 2, log 3}`. Handed
    to `../1-in-progress/baker-for-stieltjes.md` / `g2-dss-lower-bound.md`. (The exponential column is the
    sibling apex `../1-in-progress/relative-exponential-apex.md`.)
- **Source:** the proven corank trilogy
  `../2-fully-proven/G3-corank-dichotomy.md`,
  `../2-fully-proven/holonomicity-limit-nonclosure.md` (#119),
  `../2-fully-proven/function-field-holonomicity-degeneration.md` (#121),
  `../2-fully-proven/g4-over-fq-deligne-katz.md` (#122),
  `../2-fully-proven/corank-transcendence-continuation-bridge.md`,
  `../2-fully-proven/g2-over-fq-papanikolas-dss.md`;
  ../../door/bucket-the-seam-archimedean-obstruction.md · 00-status rows #20, #76, #119, #121, #122
- **Statement (to shape).** Let `Λ_M ⊂ ℤ^{(P)}` be the relation lattice of an infinite-base multi-`q`
  module and `corank(Λ_M) = rank(ℤ^{(P)}/Λ_M) = dim⟨g⟩-closure` (G3). For the arithmetic module `M_ζ`:
  > **(Unification — one number, three faces)** `corank(Λ)` simultaneously controls
  > **(G1)** holonomicity (`< ∞ ⟺` holonomic, #119/G3),
  > **(G2)** continuation/period transcendence (`trdeg(T_{s_0}) ≤ corank`, the FF instance exact = 1,
  >   `corank-transcendence-continuation-bridge`), and
  > **(G4)** the weight/Tate torus (`dim W = corank`, `g4-over-fq-deligne-katz` §2).
  > **(Border collapse — proven)** Over every finite border and over `F_q(C)`, `corank` is **finite**
  > (`= 1` over `F_q`: all multipliers are powers of one `q`, `Λ_ff = \ker\deg`, #121); the three faces
  > all degenerate to their classical (Weil / Papanikolas / Deligne–Katz) answers.
  > **(Seam identity — conjecture)** Over ℚ, `corank(Λ_{M_ζ}) = ∞` (unique factorization, `{log p}`
  > ℚ-LI), and the gap `corank(Λ_ℚ) − corank(Λ_ff) = ∞ − 1` is **exactly** the structure the archimedean
  > place / `F₁`-Frobenius must supply: a single unifying Frobenius would force all three faces finite
  > (holonomic `ζ`, DSS-provable periods, rank-1 weight torus), contradicting G1. So
  > **`ζ` non-holonomic ⟺ no single Frobenius ⟺ `corank = ∞` ⟺ archimedean seam non-trivial**, with the
  > infinite corank *realized* as genuine transcendence on all three faces at once.

  **One sentence:** the corank of the difference-Galois lattice is the number-theoretic shadow of the
  missing single Frobenius — `1` where it exists (`F_q`), `∞` where it does not (ℚ) — and the `∞ − 1`
  gap is the archimedean seam itself, the same gap on the holonomy, transcendence, and weight faces.

## Goal
The proven layer computes `corank` and proves its **upper-bound / border** half on each face separately
(the three bridges above). What no card yet states as one object is that these are **one invariant with
three faces**, and that the *open* content is a **single lower-bound realization** over ℚ: that
`corank = ∞` is not merely an upper bound that goes vacuous but is **attained as actual transcendence /
non-holonomicity / weight-torus-rank** simultaneously. Banking this would discharge, in one stroke, the
number-field exclusivity of G1 (already proven, but as an *upper-bound* phenomenon), obstruction C of G2
(`baker-for-stieltjes`), and the ℚ weight-torus rank of G4. It gives the seam — currently only a **door
bucket** — a concrete pipeline home as a *corank* problem, which is the form in which it is actually
computable.

## Door passport
- **Door-3 (the live question):** as currently defined `corank` is a torus-closure dimension — a renamed
  classical algebraic-group invariant, graded **BRIDGE / fails Door-3** (G3 verdict). The conjecture is
  that corank becomes **NATIVE exactly at the seam**: the *realization* (lower bound) that `corank = ∞`
  is genuine independent transcendence is Door-3-surviving content, because no single-prime / single-
  Frobenius parent can pose "the corank is infinite **and attained**." So **corank-native ⟺ seam
  non-trivial** — the corank-face analogue of the proven `C3-native ⟺ C5★`.
- **Door-2:** the FF computation (`corank = 1`) and the per-face upper bounds are BRIDGE (Weil /
  Papanikolas / Deligne–Katz + unique factorization, all parents). The ℚ lower-bound realization is the
  candidate native residue.
- **Door-5 ✓:** restricted to the FF border the invariant **recovers** the known answers on all three
  faces (`corank = 1`: rational `ζ_C`, DSS=Papanikolas, rank-1 weight torus).
- **Relation to C5★ (keep distinct):** C5★ is the *branchhood* lock (combination-mode Baker
  reducibility, `../1-in-progress/combination-mode-baker-reducibility.md`); this seam-corank identity is
  the *archimedean* lock (the `∞−1` Frobenius gap). They are siblings, not the same theorem — flag any
  surfaced overlap rather than merging.

## Approach
1. **Write the unified statement.** Pin one definition of `corank(Λ_M)` and prove (assemble from #119/
   #121/#122) the single proposition "`corank` controls G1, G2, G4 faces" — the three-faces lemma that is
   currently implicit across three cards. This half is essentially **bookkeeping of proven results** and
   should clear 0 → 1 cleanly.
2. **State the lower-bound realization precisely** on each face over ℚ and identify their common core: is
   "`trdeg{γ_n} = ∞`" (G2, `baker-for-stieltjes`) **equivalent** to "weight torus has infinite corank"
   (G4) and to "`ζ` non-holonomic" (G1)? G1 is **proven** (non-holonomic), so use it as the **anchor**:
   does G1's `corank = ∞` already *force* the G2/G4 realizations, or are they strictly stronger? Settling
   this implication structure is the first real theorem and may itself be bankable (a BRIDGE reduction
   "G1 ⟹ partial G2/G4 realization").
3. **Localize the irreducible residue.** Whatever does **not** follow from G1 alone is the genuine seam
   content (obstruction C). Door-2 it: finite-border = parents (BRIDGE); infinite-base uniform attainment
   = the archimedean obstruction. Hand the irreducible core to the seam bucket / `baker-for-stieltjes`
   rather than duplicating their analytic work here.
4. **Pre-certify numerically** (mpmath, archive in `computations/`) before any Lean: the FF `corank = 1`
   collapse and the ℚ corank-growth `c_T = |T| ↑ ∞` on truncations, as the floor under the identity.

## Cross-references
- `../2-fully-proven/corank-transcendence-continuation-bridge.md` — the **G2 face** (proven upper bound +
  exact FF `trdeg = corank = 1`); this card is the **unified invariant**, that card the transcendence
  realization. Coordinate; do not duplicate the Stieltjes analysis.
- `../1-in-progress/baker-for-stieltjes.md` — the **analytic ℚ instance** of the G2 lower bound. This
  card supplies the *unifying corank framing*; that card does the Stieltjes transcendence.
- `../2-fully-proven/g4-over-fq-deligne-katz.md` (§2 weight/angle split), `#121` (FF collapse),
  `#119`/`G3` (the dichotomy) — the **G1/G4 faces**.
- `../../door/bucket-the-seam-archimedean-obstruction.md` — the seam home; this card is its pipeline
  realization on the corank face.

## Gates
- [x] 0 → 1  in-progress: unified `corank` definition + the three-faces proposition assembled from
  #119/#121/#122 (BUILD §A); the ℚ lower-bound realization stated per face; Door-3 sharpened (§D); seam
  coupling pinned.
- [x] 1 → 2  fully-proven (BRIDGE): **implication structure RESOLVED (G1-anchored, §B)** — `corank` is
  LINEAR (`=∞ ⟺ {log p} ℚ-LI`, proven, G1), the G2/G4 realizations are ALGEBRAIC (`trdeg=∞ ⟺ Schanuel`);
  `corank=∞` does NOT force `trdeg=∞` (G1 floor ⊊ G2/G4 apex; gap = Schanuel = missing F₁). Object built as
  the **graded corank** (§C). Irreducible residue (`corank^{(T)}=∞`, `T≥2`) isolated and **handed to
  `baker-for-stieltjes`/#103** (DeWitt) and `#128` (Professor) with a definite verdict (FIELDS MEDAL apex).
- [ ] 2 → 3  formalized: Lean targets — `corank(Λ_ff) = 1` (reuse #121, `\deg` onto) and the directed-sup
  corank growth `c_T = |T| ↑ ∞` for `M_ζ` (reuse `finitePrimeLogAnnihilator_eq_singleton`,
  `linearIndependent_log_primes`, both ledgered)
- [ ] 3 → 4  publication-ready: standalone note "corank = the missing single Frobenius," the one-number
  unification of the three FF-degeneration cards + the seam identity

## Log
- 2026-06-19 — created in 0-backlog. Promotes the seam-corank `∞ − 1` conjecture from a door bucket to a
  concrete pipeline ticket on the **corank** face: unifies the three proven corank bridges (G1
  non-holonomicity #119, G2 transcendence, G4 weight torus #122) as one invariant and isolates the open
  content as a **simultaneous lower-bound realization over ℚ**, G1-anchored. Door-3 question: corank-native
  ⟺ seam non-trivial (the corank analogue of the proven `C3-native ⟺ C5★`). Kept distinct from C5★
  (branchhood lock) — this is the archimedean lock. First step = assemble the three-faces proposition.
</content>

---

# BUILD — the F₁/Schanuel object as the graded corank (Wheeler, 2026-06-19)

User directive: *"build the F₁/Schanuel object."* The four facets DeWitt synthesized (flow→BRIDGE,
constraint→algebraic-corank, localization→RH, transcendence→DSS) are one object; below it is **constructed**
as the **graded corank**, with its proven linear floor, its algebraic apex (= Schanuel = the missing F₁),
and the separation that answers this card's Step 2.

## §A The unified corank — one number, three faces `[assembled, BRIDGE — Step 1]`
For an infinite-base multi-`q` module `M`, `Λ_M ⊂ ℤ^{(P)}` is the multiplicative relation lattice of the
multipliers `{g_p}` and `corank(M) := rank(ℤ^{(P)}/Λ_M) = rank⟨g_p⟩`. Assembling the proven trilogy:
- **(G1 face, #119/G3)** `corank < ∞ ⟺ M` holonomic. For `M_ζ`: `g_p=p^{-1}`, `Λ_{M_ζ}=\{m:∏p^{m_p}=1\}=\{0\}`
  (unique factorization) ⟹ `corank=∞` ⟹ `ζ` non-holonomic. **Proven.**
- **(G2 face, #122 `corank-transcendence-continuation-bridge`)** `trdeg(T_{s_0}) ≤ corank` (upper bound;
  exact `=1` over `F_q`).
- **(G4 face, #123 `g4-over-fq-deligne-katz` §2)** `dim W = corank` (the weight/Tate torus; `=1` over `F_q`).
- **(Border, #121)** over `F_q(C)` all multipliers are powers of one `q` ⟹ `Λ_ff=\ker\deg`, `corank=1`;
  all three faces collapse to Weil/Papanikolas/Deligne–Katz.
So `corank` is **one invariant with three faces**, finite (`=1`) over `F_q`, `∞` over ℚ. (Bookkeeping of
proven results — BRIDGE.)

## §B The level-structure theorem — corank is LINEAR; the realization is ALGEBRAIC `[Step 2, bankable]`
**This answers the card's open Step 2 ("does G1's `corank=∞` force the G2/G4 realizations?"): NO — they are
separated by the linear→algebraic gap, which is exactly Schanuel-for-prime-logs.**

`corank(Λ_M)=rank⟨g_p⟩` counts **ℤ-LINEAR** relations among the multipliers: `∏g_p^{m_p}=1 ⟺ Σm_p\log p=0`.
Hence
> **`corank(Λ_ℚ)=∞ ⟺ \{\log p\} is ℚ-LINEARLY independent`** — PROVEN (#1, Baker/unique factorization).
This is an inherently **linear** (multiplicative-group-rank) invariant: the **G1 face = the LINEAR floor.**

The G2/G4 **realizations** are **ALGEBRAIC**:
> `trdeg=∞ ⟺ \{\log p\} ℚ-ALGEBRAICALLY independent` (Schanuel-for-prime-logs); `\dim W=∞` likewise.

Since `corank` (linear) is only an **upper bound** for `trdeg` (algebraic, #122), `corank=∞` gives the
**vacuous** `trdeg≤∞` and does **not** force `trdeg=∞`:
> **Theorem (level separation, BRIDGE).** ℚ-linear independence of `\{\log p\}` (proven, `corank=∞`) does
> **not** imply ℚ-algebraic independence (`trdeg=∞`). So **G1 (linear floor) ⊊ G2/G4 (algebraic apex)**; the
> three faces are **not** equivalent, and the gap between the proven floor and the realization is **exactly
> Schanuel-for-prime-logs = the missing F₁**.

*Proof.* `corank` is the rank of the abelian group `⟨g_p⟩`, a linear datum equivalent to ℚ-linear
independence of `{\log p}`; `trdeg` is the transcendence degree of the period algebra. Linear independence
is strictly weaker than algebraic independence (e.g. `{\log 2,\log 3}` are ℚ-LI by Baker, yet their
**algebraic** independence is open). The bridge `trdeg≤corank` (#122) makes `corank` an upper bound, never a
lower bound, for the realization. ∎ (BRIDGE: Baker + the definition of algebraic independence + #122.)

**Why this is the F₁ structure.** Over `F_q` the single Frobenius forces `corank=trdeg=1` — the linear and
algebraic levels **coincide** (one multiplier, `q^{-deg v}`, generates everything). Over ℚ there is **no
single Frobenius**, the linear floor (`corank=∞`, proven) and the algebraic apex (`trdeg=∞`, Schanuel) are
**separated**, and the separation **is** the missing single Frobenius (F₁). So "`F₁` collapses ℚ to a curve"
= "`F₁` would force the algebraic level down to the linear level," exactly as over `F_q`.

## §C The graded corank — the object, built `[the construction]`
Refine `corank` by a **degree filtration** that interpolates the linear floor and the algebraic apex:
> `corank^{(T)} := \dim_ℚ \big(\text{span}_ℚ\{∏_p(\log p)^{a_p} : Σ_p a_p ≤ T\}\big)`-defect
> `= ` the number of ℚ-**linear** relations among the degree-`≤T` prime-log **monomials**.

- `corank^{(1)}=∞`  — `\{\log p\}` ℚ-LI — **PROVEN** (the §B floor; G1).
- `corank^{(T)}=∞\ ∀T ⟺` all degree-`T` prime-log monomials ℚ-LI `⟺ \{\log p\}` ℚ-algebraically independent
  `⟺ trdeg=∞ ⟺` **DSS** `⟺` **Schanuel-for-prime-logs** `⟺` the **F₁-realization** (G2/G4 apex).

So the **F₁/Schanuel object is the graded corank** `\{corank^{(T)}\}_{T≥1}`: a ladder from the proven linear
floor (`T=1`, the BRIDGE shadow shared by all four facets) to the algebraic apex (`all T=∞`, the missing
Frobenius). **First open rung:** `corank^{(2)}=∞` = ℚ-linear independence of the **degree-2** monomials
`\{(\log p)^2, \log p·\log q\}` = algebraic independence of `\{\log p\}` at degree 2 — **open even for
`\{\log 2,\log 3\}`.**

**Exact tie to the analytic apex (DeWitt #103).** The friable obstruction-C form `F^{(T)}(1) = (-1)^T Σ_m
λ_m (m·ℓ)^T/n_m` is a ℚ-**linear form in degree-`T` prime-log monomials** `∏(\log p)^{a_p}`; the bound it
needs is precisely `corank^{(T)}=∞`. So the graded corank is the structure underneath `friable-dirichlet-
auxiliary` / `baker-for-stieltjes`: each degree `T` is one rung, and the analytic Stieltjes/log work is the
attack on the rungs `T≥2`.

## §D Grade, apex residue, coordination
- **Door grade — BRIDGE** for the BUILD (§A assembly + §B separation + §C filtration): Baker (`T=1`), #122,
  and the definition of algebraic independence — all parents/bookkeeping. The **native residue** is the
  realization (any rung `T≥2`, i.e. the lower bound `corank^{(T)}=∞`), = Schanuel-for-prime-logs = the F₁
  apex (FIELDS MEDAL), handed to `baker-for-stieltjes`/#103 (DeWitt) and the F₁=∂_s collapse #128 (Professor).
- **Door-3:** the graded corank's floor (`T=1`) is BRIDGE (renamed linear independence); the **realization**
  (`T≥2`) is the Door-3-surviving candidate (no single-Frobenius parent can pose "the graded corank stays
  `∞` at every degree, attained"). corank-native ⟺ the realization ⟺ the missing F₁ (distinct from C5★).
- **Coordination:** this card = the unified object + level structure + filtration (Wheeler);
  `baker-for-stieltjes`/#103 = the analytic attack on the `T≥2` rungs (DeWitt); `archimedean-corank-collapse`
  #128 = the F₁=∂_s collapse mechanism (Professor). No overlap with the Stieltjes analytics.

## Log (cont.)
- 2026-06-19 (Wheeler) — **Built the F₁/Schanuel object as the graded corank** (user directive). §A: assembled
  the three-faces proposition (corank controls G1/G2/G4; `=1` over `F_q`, `∞` over ℚ) — Step 1, bookkeeping.
  §B: **answered the card's Step 2** — `corank` is inherently LINEAR (`=∞ ⟺ {log p} ℚ-LI`, proven), the G2/G4
  realizations are ALGEBRAIC (`trdeg=∞ ⟺ {log p} ℚ-alg-indep = Schanuel`); since `trdeg≤corank` (#122) is an
  upper bound, `corank=∞` does **NOT** force `trdeg=∞` — **G1 (linear floor) ⊊ G2/G4 (algebraic apex)**, gap
  = Schanuel = missing F₁. Over `F_q` the single Frobenius collapses linear=algebraic (`=1`); over ℚ the
  missing Frobenius is the separation itself. §C: the **graded corank** `corank^{(T)}` (rank of ℚ-relations
  among degree-`≤T` prime-log monomials) interpolates floor (`T=1`, proven) → apex (`all T=∞` ⟺ Schanuel ⟺
  F₁-realization); first open rung `corank^{(2)}=∞` (open even for {log2,log3}); exact structure under
  DeWitt's #103 `F^{(T)}(1)`. Grade BRIDGE (build); apex residue (`T≥2`) handed to baker-for-stieltjes/#128.

## §E Epistemic framing — the object joins the field's only two contents (user, 2026-06-19)
A "founding principle" (a generative rule from which all follows) **is** an algebraic differential equation;
hypertranscendence is its absence (Hölder 1887, the founding theorem — *negative*). So the field has no
generative rule and exactly two kinds of content, and the graded corank instantiates **both**:
- **(A) Obstruction theory** — *why no rule exists*: the **function-level** corank=∞ (linear, proven; G1
  non-holonomicity, the `T=1` floor). Every "what equation does Λ satisfy" attack is necessarily a
  certification of *absence* (BRIDGE) — correct content, now mapped.
- **(B) Value-relation theory** — *relations among the values*: the **value-level** `trdeg=∞` (algebraic;
  G2 multi-q Siegel–Shidlovsky / DSS, the `T≥2` apex). This is the field's analog of **Airy = SL₂** (a
  transcendence keystone, not a rule), and it is where **C5** lives.
The level-separation (§B) is exactly the (A)/(B) divide; the graded corank (§C) is the ladder from the
obstruction floor to the value-relation apex. The keystone is climbing it — DSS / Schanuel — not a rule.

## §F The first algebraic rung, partially climbed — Gelfond–Schneider reaches pairwise homogeneous degree 2 (Wheeler, 2026-06-19)

The graded corank (§C) has a proven linear floor (`corank^{(1)}=∞`, Baker) and an apex (`corank^{(T)}=∞ ∀T`
= Schanuel). The **first algebraic rung** `corank^{(2)}` is not a monolithic wall: its bottom stratum is
**provable by classical transcendence**, which localizes the genuine obstruction.

**Proposition (BRIDGE, Gelfond–Schneider).** For distinct primes `p ≠ q`, the homogeneous degree-2 prime-log
monomials `(log p)², (log p)(log q), (log q)²` are **ℚ-linearly independent**.
*Proof.* A relation `a(log p)²+b(log p)(log q)+c(log q)²=0` (`a,b,c∈ℚ` not all 0) gives, dividing by
`(log q)²`, `a t²+b t+c=0` with `t=log p/log q` — so `t` is algebraic of degree ≤2. But `t` is irrational
(`t=m/n ⟹ p^n=q^m`, impossible) and, by **Gelfond–Schneider**, transcendental: were `t` algebraic
irrational, `q^t = q^{log p/log q}=p` would be transcendental (`α=q` algebraic `≠0,1`, `β=t` algebraic
irrational ⟹ `α^β` transcendental), contradicting `p` algebraic. So `t` is transcendental ⟹ `a=b=c=0`. ∎

**Stratification of `corank^{(2)}` (the localization).** The algebraic level is not all apex:
- **pairwise homogeneous degree 2** — `{(log p)²,(log p)(log q),(log q)²}` ℚ-LI — **PROVEN** (G-S, above), **BRIDGE**;
- **multi-prime homogeneous degree 2** (`Σ_{i≤j} a_{ij}\log p_i \log p_j = 0`, `n≥3`) — **OPEN, and NOT
  reachable by six-exponentials/Baker** (verified 2026-06-19): six-exponentials is a *rank* statement for a
  matrix of logarithms (linear/bilinear in single logs), and Baker gives linear independence of logs over the
  algebraic numbers — neither handles a *quadratic form in products* of logs. Dividing by `L_n²` reduces the
  `n≥3` relation to a quadratic among the ratios `t_i=\log p_i/\log p_n`, which vanishes only if the `t_i` are
  algebraically *dependent* — i.e. the case needs **algebraic independence of ratios of prime-logs**, open
  (Schanuel territory; even alg. independence of `\log 2,\log 3` is open). So `n≥3` is genuinely the apex;
- **mixed degree** (e.g. is `(\log 2)² = \log 3` excluded? — degree-2 = degree-1) — open, part of Schanuel.
So the genuine `corank^{(2)}` obstruction (hence the DSS/Schanuel apex) is the **multi-prime (`n≥3`) /
mixed-degree** structure; the pairwise-homogeneous bottom falls to Gelfond–Schneider. This refines the (A)/(B)
picture (§E): even within the value-relation level (B), there is a sub-stratification — a classical-transcendence
-accessible bottom (G-S, BRIDGE) under the genuine Schanuel core (the apex). It is the first concrete climb of
the corank ladder above the Baker floor, and it pins where the real difficulty starts (`n≥3` / mixed degree).

## Log (cont.)
- 2026-06-19 (Wheeler) — **§F: first algebraic rung partially climbed.** Proved (Gelfond–Schneider) that the
  pairwise homogeneous degree-2 prime-log monomials `{(log p)²,(log p)(log q),(log q)²}` are ℚ-LI (via
  `log p/log q` transcendental). Stratifies `corank^{(2)}`: pairwise-homogeneous = BRIDGE (G-S); multi-prime
  (`n≥3`) / mixed-degree = the open Schanuel core. Localizes the DSS apex: the real obstruction begins at
  `n≥3` / mixed degree, not at the bottom of the algebraic ladder. BRIDGE. Corpus-checked (no prior
  G-S/log-ratio content). Feeds DeWitt's DSS lane (#103/baker-for-stieltjes).
- 2026-06-19 (Wheeler) — **flag resolved (WebSearch):** six-exponentials does NOT reach the `n≥3` homogeneous
  case — it is a rank statement for matrices of single logs, not for quadratic forms in *products* of logs;
  the `n≥3` relation reduces to a quadratic among ratios `t_i=\log p_i/\log p_n` needing their algebraic
  independence (open, Schanuel). So the BRIDGE stratum is **exactly** pairwise-homogeneous-degree-2; `n≥3`
  and mixed-degree are the genuine apex. §F tightened (uncertain flag removed).

## Apex actively attacked — wall located, science started (2026-06-19, Wheeler)
The Fields-Medal apex this BRIDGE card reduces to is **LIVE**, not parked. The two conjuncts (bigraded-corank
§G): the **regular column** = Schanuel-for-prime-logs (`../1-in-progress/baker-for-stieltjes.md` /
`g2-dss-lower-bound.md`); the **exponential column** = `{γ_n}` over the regular base — `γ_E` as the
`𝔾_a`-period of the Source-A digamma `ψ=∂_s logΓ`, worked in `../1-in-progress/relative-exponential-apex.md`.
**Status:** the regular-world routes (difference-Galois; Beukers/Aptekarev moment/friable) reach a
precisely-located wall — §16 *smallness `⟺` γ-blindness* — whose only **proven** part is the finite-dim
landing. This is **not** a no-go: an earlier "provably insufficient" claim was retracted (Leaner id=339;
finite-dim ≠ no-measure). The route past the wall (§17): `γ_E` is an **irregular (Stokes) period** outside
Wüstholz — the new object is a Wüstholz-for-irregular / irregular-Hodge generator count. The conjunct
`γ_E ∉ \overline{𝓡}` is **open** (believed true; implies `γ_E∉ℚ`, open since 1734). This card is the BRIDGE
skeleton; the open science is the two conjuncts.

## Lean formalizer return note — 2026-06-19 (Leaner)

Returned from `2-fully-proven` to `0-backlog-lean` because the ticket is not a single fully paper-proven theorem ready for Lean formalization.

Defect: the type metadata says the F1/Schanuel object is built but the algebraic-apex realization stays the open core `(CONJECTURE, FIELDS MEDAL)`. Later sections explicitly mark multi-prime degree-2 and mixed-degree cases as open/Schanuel territory. The card is not a single fully proven theorem.

Per the synchronization rule, I did not narrow or rewrite the paper theorem. Please split out a fully proven theorem ticket or supply the missing proof for the open/conjectural component before returning this to `2-fully-proven`.

## Log (cont.)
- 2026-06-19 (Wheeler) — **resolved Leaner's return note by NARROWING, not rewriting** (same fix as
  `bigraded-corank-dss-cross`). The claimed theorem is now the **proven** core only — §A unified corank (with
  proven `F_q` border collapse), **§B level-separation** (`corank` linear `= {log p}` ℚ-LI, PROVEN, ⊊ `trdeg`
  algebraic apex), §C graded-corank filtration with proven floor `corank^{(1)}=∞`, §F the GS degree-2 rung. The
  apex **realization** (`corank^{(T)}=∞`, `T≥2` = Schanuel-for-prime-logs / missing F₁) is **excised** and
  pointed to the open regular-column targets `../1-in-progress/baker-for-stieltjes.md` /
  `g2-dss-lower-bound.md`. Added a Scope box up top. With the open conjunct externalized, the remaining ticket
  **is** a single fully-proven BRIDGE theorem ready for Lean → moved back to `2-fully-proven`.
