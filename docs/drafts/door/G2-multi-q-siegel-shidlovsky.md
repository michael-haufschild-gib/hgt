# Bucket G2 — Multi-q Siegel–Shidlovsky / DSS

**Bucket grade:** organizational (SEARCH channel). Sorted from `docs/support-extraction-log.md`.
Source air-marks preserved.
**Scope (one line).** `trdeg_F F(diagonal values) = dim of the G_L-orbit` ⟹ linear independence /
algebraic independence of the zeros (DSS). The field's **native problem** (charter P4).
**Work package this seeds.** Prove the **lower bound** via a Nesterenko-type multiplicity estimate on
the *heighted* secular coordinates `P_k` — landing DSS on the concrete joint-independence of
`{π} ∪ {ζ(odd)} ∪ {Stieltjes γ_n}`.

---

## The conjecture

> **G2 — Multi-q Siegel–Shidlovsky:** `trdeg = G_L-orbit dim ⟹ LI of zeros` (= DSS, = #68's C3).

The "free half" and the "hard half" are cleanly separated everywhere in the corpus: the **orbit
dimension is FREE** (`dim G_L-orbit = ∞`, by Weyl equidistribution + unique factorization, *not*
Baker); the **trdeg equality is the conjecture** (the Grothendieck-period-conjecture-shaped hard
half).

---

## What belongs here

### Statement + the free/hard split (#67)
- §4 and §16-Wing-B(b) state G2 verbatim ("`trdeg{γ_n}` over the period field = `dim G_L`-orbit;
  `G_L ⊇ 𝕋^∞⋊ℤ/2` infinite-dim ⟹ LI").
- Brick #3/#8: the diagonal flow's pro-algebraic closure is all of `𝕋^∞` (Weyl + FTA) ⟹ orbit
  dimension is FREE; the hard part is `trdeg` of the intersection points (the zeros). (orbit closure
  computed; trdeg equality open)
- §10 Critic caveat: **Baker survives in the effective/Diophantine rate** (how fast the diagonal
  approaches the boundary zero-variety) — G2's hard column = "zeros **and** effective flow-rate."

### The classical landing + the ℚ-obstruction (#68)
- §33 **Papanikolas 2008** proves the *full* statement `trdeg(periods)=dim G_M` over `F_q(t)` by
  exactly the field's mechanism (a σ-difference-Galois group computing transcendence); CM locus =
  Wüstholz/Chudnovsky/Cohen–Shiga–Wolfart (§58); tori = §43.2. (imports / proven cases)
- §33.3 the **ℚ-obstruction named:** `F_q(t)` has a *single* Frobenius ⟹ finite difference eqn ⟹
  Papanikolas runs; ℚ has *infinitely many* `σ_p` + Hölder ⟹ no finite eqn ⟹ must go infinite-order.
  **The F₁ / missing-Frobenius wall = the G2 ℚ-gap.**
- §34.2 infinite-base **ABP criterion** = the precise ℚ-form of G2: (A) existence of an archimedean
  trivialization `ψ`, finite order; (B) the linear-independence criterion. **(B) plausibly FREE**
  (ℚ-indep of `{log p}`, ledger-proven); **the entire ℚ-content is (A).**
- §37 **constructs (A): `ψ(s)=∏_{k≥0} ζ(s+k)`** — solves `ψ(s)=ζ(s)ψ(s+1)`, infinite-order,
  numerically verified (dps 25). §37.5: its ABP regularity = "1/ζ has poles only on Re=½" = RH (no
  bypass — difficulty conserved).

### The height-vacuum diagnosis + secular resolution (#69 — the deepest analysis)
- §17 three-pillar S–S architecture: Pillar 1 (Siegel's lemma) + Pillar 2 (zero/multiplicity
  estimate) — **both FREE** from ℚ-indep of `{log p}` — + **Pillar 3 (Liouville/height lower bound).**
- **§17.3 the height vacuum (the actual 165-year wall):** the zeros `{γ_n}` carry **no arithmetic
  height** (no number field, no house, no Weil height) ⟹ no transcendence engine can run directly on
  them. *Not positivity, not circularity — a HEIGHT VACUUM.* (the single most important G2 diagnostic)
- **§17.4 the resolution (the field's one non-trivial structural move):** change coordinates to the
  **secular constants `P_k = Σ_ρ ρ^{−k}`** (Voros superzeta) — same spectral information
  (Hadamard-equivalent) but **heighted** (explicit periods). Lands G2 in **Nesterenko / period-theory
  / motivic-Galois** territory — a domain *with* transcendence tools. *Air: secular forms recalled
  from Voros 2010, flagged for re-derivation.*
- §19 explicit secular formula: `P_1 = 1 + γ_E/2 − ½log4π` (matches Davenport ✓);
  `P_k = 1 − (−1)^k ζ(k)/2^k − a_{k−1}`, `a_j := [s^j](ζ'/ζ)(s)`. Consequence:
  **`ℚ({P_k}) ⊇ {odd zeta values}`** ⟹ G2 *entails* alg. independence of `ζ(3),ζ(5),…` (the
  Ball–Rivoal–Zudilin frontier where methods already exist).
- §11–12 the proof METHOD (corrects the fiber-functor approach): don't make the fiber functor carry
  the zeros (de Branges `⊗↦⊕`, **not** Tannakian); Mahler's architecture = (Tannakian ⊗-category) +
  (separate multiplicity estimate). §14: the correct multiplicity estimate = **subtorus avoidance =
  LI = PSLQ**. §15–16: ℵ₀-uniform mechanism = equidistribution discrepancy `D_K < N^{-2}` = the
  explicit-formula prime sum (difficulty conserved).

### The proof factored into 4 explicit pieces (#71 — the most actionable)
- §3 **T-up PROVED** (the easy half / upper bound): `trdeg ≤ dim G_M`, by specialization. *Half of G2,
  proved; Tier-A formalizable.*
- §4 the lower bound factors into THREE named obstructions:
  - **A — Siegel's lemma in ∞ variables — SUPPLIED (§8):** the diagonal pullback is a **friable
    (S-smooth) Dirichlet polynomial** `F(s)=Σ_m λ_m n_m^{−s}`; the weighted Siegel's lemma =
    **Bombieri–Vaaler 1983**, explicit height (ledger-backed `boundedExponentVectorEquivSmooth`,
    `diagonalAuxiliaryForm_eq_dirichletPolynomial`). New bridge: transcendence auxiliary functions =
    smooth-number Dirichlet polynomials. (→ [[bucket-new-sibling-conjectures]], object N5)
  - **B — multi-q Shidlovsky zero estimate — finite-S PROVED (Lemma 5)** (reduction to multivariate
    Mahler, Adamczewski–Faverjon); open part = **Conjecture 5′ (uniformity in S)** = "where infinitely
    many operators stops being free." Flatness `F_pq=1` is load-bearing.
  - **C — arithmetic of the L-values — the irreducible residue:** the values `n_m^{−s_0}` are
    ζ-values/zero ordinates, not controlled. **Same wall as `ζ(5)`-open**, isolated as a single
    arithmetic obstruction = `spec(H_L)=Spec(L)` keystone = the F₁ arithmetic.
- §8.3 Prop 8.3 (the race): G2's lower bound = "vanishing order `T` beats the explicit height+size
  budget against the arithmetic lower bound on `|F^{(T)}(s_0)|`." A,B explicit; **C the only ungoverned
  term.** §6 Prop 6 (orbit-not-group, PROVED): ζ = the most non-generic diagonal ⟹ small orbit ⟹ hard.
- §2 citation ladder: Level 0 = André–Beukers; Level 1 = Adamczewski–Faverjon (Mahler); Level 2 =
  multivariate Mahler; **Level 3 (infinite-base) = OPEN = G2.**

### The concrete arithmetic landing (#72 — the sharpest statement of G2's content)
- §8a **RIGOROUS `P_k` formula** (general, not just `P_1`): `P_k = 1 − (−1)^k ζ(k)/2^k − a_{k−1}`,
  `a_j=[s^j](ζ'/ζ)(0)`, `a_0=log(2π)`. §8b numerically confirmed (dps=40, N=2000). §8e Lean weld:
  `li_secular_pointwise` + `secular_li_pointwise_inv` (Li↔secular ℤ-triangular change of basis,
  ledger-proven both directions, axiom-clean Tier A).
- §10–11 **the period algebra:** `ℚ({P_k}) = ℚ(π, {ζ(2k+1)}, {Stieltjes γ_n})`. **So G2/DSS = joint
  algebraic independence of THREE recognizable blocks:** `{π}` (Lindemann ✓), `{ζ(odd)}` (Apéry–
  Ball–Rivoal–Zudilin frontier), `{Stieltjes γ_n}` (not even `γ_1` known irrational). PSLQ-verified
  identities (dps=80): `a_1=ζ(2)/2−γ_E²−2γ_1`, `a_2=ζ(3)−γ_E³−3γ_Eγ_1−(3/2)γ_2`. **The cleanest
  possible statement of G2's content.** The field's irreducibly-new (no-motive) object = the
  **Stieltjes block** and its non-conspiracy with odd-ζ.
- §3–4 **the Liouville substitute (the KEY new mechanism):** classical transcendence needs Liouville
  (nonzero algebraic ≥ H^{−c}) — absent for the transcendental spectrum. **Substitute = Weil explicit
  formula × ℚ-LI of `{log p}`** (`linearIndependent_log_primes`, Lean): a zero-side resonance pushes
  to a prime-side resonance, but the prime side is ℚ-non-resonant + integer-rigid ⟹ no low-complexity
  resonance. §6 correction: route through the carrier `m_ξ = −Ξ′/Ξ` (poles = zeros one at a time), so
  the substitute = rigidity of `{Λ(n)} ↦ {poles of m_ξ}`. (→ [[G5-unitarity-gatekeeper]],
  [[bucket-A1-A2-unification-the-carrier]])
- §7 retraction: the `σ_min` conditioning numeric is **retracted** as DSS evidence (measures sampling
  regularity, not arithmetic genericity); correct meter = subtorus avoidance = LI = PSLQ.

### Where the open core actually lives (#74 — period vs non-period divide)
- DSS = alg. independence of `{π} ∪ {ζ(odd)} ∪ {γ_n}`. The first two are **periods of `MTM(ℤ)`**
  (GPC-conditional, tooled); the **Stieltjes constants are conjecturally NOT periods** (exponential-
  period-like regularization constants). **Relocation: DSS = GPC + (DSS-cross),** where (DSS-cross) =
  `{γ_n}` alg. independent of the whole `MTM(ℤ)` period algebra — *a statement ACROSS the
  period/non-period divide.* **So G2's genuinely-open core is the Stieltjes side, not the zeta side.**
  Right framework = exponential-motives / Nori motives (Fresán–Jossen). Strategy: aim the Nesterenko
  lower bound at the **`s=1` Laurent data of ζ** (where the `γ_n` live). (→ [[bucket-the-seam-archimedean-obstruction]])

### The two transcendence towers (#80 SEED-U)
- The transcendence tower recurses **motivically, not spectrally**: the superzeta values `P_k` carry a
  **motivic Galois action** (Kontsevich–Zagier / mixed-Tate) — *that* is the next tower level, not a
  second `G_L`. The two towers' non-interaction IS the seam (spectral/difference-Galois tower dead at
  level 2; additive/period/motivic tower alive). *Falsifiable (Voros's explicit `𝒵(2m)`), routes into
  Nesterenko/motivic-Galois.* (→ [[bucket-new-sibling-conjectures]])

### The edge corner is solved — Baker (#93)
- §1–2 value-transcendence tower graded by **motivic type:** even ζ(2k) = Tate (Lindemann); odd
  ζ(2k+1) = mixed Tate (Brown); **edge `L(1,χ)` = SOLVED by BAKER** (Baker–Birch–Wirsing); central
  `ζ^{(j)}(½)` = non-motivic, OPEN. **Difficulty NON-MONOTONIC:** the edge is *easier* than odd
  integers. **Baker = the anti-Tate period conjecture (B9/G2) PROVED at the edge.**
- §3 **the Stieltjes constants are the rung ABOVE Baker** — the FE-transferred Laurent coeffs of ζ at
  `s=1`, NOT Baker-tame (we don't know `γ_E` irrational). Concrete G2 sub-target: **"is there a Baker
  for the Stieltjes constants?"** (the field's genuinely-new, no-motive transcendence content)

---

## Status ledger for this bucket

| Piece | Tier / grade | Source |
|---|---|---|
| upper bound `trdeg ≤ dim G_M` (T-up) | **`[PROVED HERE]`**, Tier-A formalizable | #71 §3 |
| `P_k` closed form + Li↔secular ℤ-basis | **ledger-proven** (`li_secular_pointwise`) + numeric | #72 §8 |
| `ℚ({P_k}) = ℚ(π,{ζodd},{γ_n})` reduction | draft-claimed + PSLQ (dps 80) | #72 §11 |
| obstruction A (Siegel ∞-vars) | **supplied** = Bombieri–Vaaler (import) | #71 §8 |
| obstruction B (zero estimate) | finite-S **PROVED**; uniformity open (Conj 5′) | #71 §4 |
| obstruction C (arithmetic of L-values) | **OPEN — the irreducible residue** | #71 §4 |
| over `F_q(t)`: full G2 | **THEOREM** (Papanikolas) | #68 §33 |
| edge `s=1` | **THEOREM** (Baker) | #93 |
| Stieltjes-block independence (DSS-cross) | **OPEN core** (beyond GPC) | #74 |

## Open core / the work package
**Prove the lower bound `trdeg ≥ dim(G_L·δ)`** = govern obstruction **C** = the Nesterenko-type
multiplicity estimate on the heighted `P_k`, aimed at the **`s=1`/Stieltjes** data (not integer
ζ-values). Concrete next target: **a "Baker for the Stieltjes constants."** Formalize the *reduction*
`DSS ⟺ {π,ζodd,Stieltjes} indep` + the conditional Nesterenko→DSS as Lean `Prop`s (`FieldConjectures`).

## Cross-references
- [[bucket-the-seam-archimedean-obstruction]] — the open core is archimedean (Stieltjes/Γ-factor).
- [[bucket-A1-A2-unification-the-carrier]] — DSS = the carrier germ's *infinite jet* (A2 face).
- [[G5-unitarity-gatekeeper]] — the same carrier `m_ξ` carries the RH face; one rigidity bound feeds both.
- [[bucket-new-sibling-conjectures]] — friable-auxiliary object (N5), motivic period tower, family-DSS/GSH.
- [[bucket-function-field-proving-ground]] — over `F_q(t)`, G2 is Papanikolas's theorem.
