# The multiplier-dichotomy theorem — the σ-coboundary class of the multiplier is the archimedean–prime (Source A / Source B) divide

- **ID:** multiplier-dichotomy-theorem
- **Stage:** 0-backlog-lean
  obstruction + the Source-A/B corollary + the `F_q` shadow. Hard hypertranscendence converse is IMPORT
  (Hölder 1887 for `Γ`; Adamczewski–Dreyfus–Hardouin / Hardouin–Singer for general rational multiplier).
- **Type:** THEOREM (paper) — **grade BRIDGE** (Door-2 fails: each case rests on a single parent — gauge
  theory + van der Put–Singer for the holonomic case, Hölder/ADH for the hypertranscendental case; the
  organizing *divide* is the payload, not a joint-`σ_p` native theorem, consistent with §59/§60 = Source-B
  BRIDGE).
- **Priority:** FOUNDATIONAL — the first provable theorem of the Hölder-recentering (two-sources framing).
- **Source:** `two-sources-of-hypertranscendence.md` (this is its extractable 1→2 theorem); corpus #90 §64 /
  **SEED-G** (`support-extraction-log.md` L191–196: "the Γ-recurrence `Γ_ℝ(s+2)=(s/2π)Γ_ℝ(s)` makes the
  archimedean place a difference module with the **unique non-constant polynomial multiplier** `(s/2)/π`;
  all finite places have **constant** multipliers; **TWO independent sources of hypertranscendence**");
  Hölder 1887; van der Put–Singer (rank-1 difference Galois); Adamczewski–Dreyfus–Hardouin / Hardouin–Singer
  (difference→differential hypertranscendence); 00-status rows #2, #3, #130.
- **Provenance (standing-order corpus check):** the two-source / polynomial-vs-constant-multiplier
  *framing* is pre-named in #90 §64 (SEED-G) and recorded as 00-status #130. **DeWitt's increment is the
  proof:** identifying the σ-**coboundary class** (not merely "constant vs polynomial") as the exact
  dividing invariant, proving the gauge-trivialization (case I) and the degree-at-infinity obstruction
  (case II separation) elementarily here, and pinning the hard converse as a precisely-attributed import.
  No `5-failed` card touches this; no `2-fully-proven`/`3-formalized` card states the dichotomy.

---

## Setup

A **rank-1 difference module** over a difference field `(K, σ)` (with `σ` an automorphism, field of
constants `C = K^σ`) is `M = (K·e, σ)` with `σe = a·e`, `a ∈ K^×` the **multiplier**. A **solution** is a
nonzero `f` in a difference-ring extension with `σf = a·f` (analytically, a meromorphic function with that
functional relation). Two multipliers `a, a'` give **gauge-isomorphic** modules iff `a' = a·σ(g)/g` for some
`g ∈ K^×` (set `e' = g·e`).

The relevant incarnations:
- **Archimedean (Source A) — additive shift.** `K = ℂ(z)`, `σ : z ↦ z+1`. The `Γ`-factor:
  `σf = z·f` (i.e. `Γ(z+1) = z·Γ(z)`), multiplier `a(z) = z`; for `Γ_ℝ`, `a = s/2π` (#90 §64). Multiplier is
  a **non-constant polynomial**.
- **Prime (Source B) — `q`-dilation.** `K = ℂ(x)`, `σ_p : x ↦ q·x`, `q = p^{-1}` (not a root of unity).
  The Bohr generator `x = x_p = p^{-s}`: `σ_p x_p = q·x_p`, multiplier `a = q ∈ ℂ^×` **constant**. The Euler
  factor `f_p = (1-x_p)^{-1}` has multiplier `a = (1-x)/(1-qx)`, a **coboundary** (see below).

**The dividing invariant.** Say `a ∈ K^×` is **constant-up-to-coboundary (CC)** if `a = c·σ(g)/g` for some
`c ∈ C^×`, `g ∈ K^×`. (Constant multipliers are the case `g=1`.) The theorem is that CC is exactly the
holonomic/Source-B regime, and its failure (with a degree-at-∞ witness) is the hypertranscendental/Source-A
regime.

---

## Theorem (multiplier dichotomy)

Let `M = (K·e, σe = a·e)` be rank-1, `f` a nonzero solution.

**(I) CC ⟹ holonomic / differentially algebraic. [PROVED HERE]**
If `a = c·σ(g)/g` (`c ∈ C^×`, `g ∈ K^×`) then:
1. `M` is gauge-isomorphic over `K` to the constant module `(K·e', σe' = c·e')`;
2. its difference-Galois group is `⊂ 𝔾_m` — abelian, `dim ≤ 1` (van der Put–Singer, rank-1);
3. in the shift realization `K = ℂ(z)`, `M` admits the **differentially algebraic** solution
   `f = g·c^z`, satisfying the first-order **linear ODE** `f' = (g'/g + log c)·f` over `ℂ(z)⟨log c⟩`.
   (When `c = 1` this is rational: `f = g`.)

**(II) Degree-at-infinity obstruction. [PROVED HERE]** For `K = ℂ(z)`, `σ : z↦z+1`: every `g ∈ ℂ(z)^×`
satisfies `g(z+1)/g(z) → 1` as `z → ∞`. Hence `c·σ(g)/g → c ∈ ℂ^×` (finite, nonzero). Therefore any
`a ∈ ℂ(z)^×` with **`deg_∞(a) ≠ 0`** (a zero or pole at `∞` — in particular any non-constant polynomial,
which has a pole at `∞`) is **not CC**: case (I) cannot apply.

**(III) Not-CC ⟹ hypertranscendental. [IMPORT]** If `a` is not CC, then `f` satisfies no algebraic
differential equation over `ℂ(z)` — `f` is differentially transcendental (hypertranscendental). Concretely
`a(z) = z` gives `f = Γ`, hypertranscendental (**Hölder 1887**); the general rational-multiplier converse is
**Adamczewski–Dreyfus–Hardouin / Hardouin–Singer** (difference→differential hypertranscendence criterion).

---

## Proofs

### (I) CC ⟹ holonomic [PROVED HERE]
Let `a = c·σ(g)/g`. Gauge by `e' = e/g` (i.e. `h = 1/g`). The new multiplier is
`a' = a·σ(h)/h = a·σ(1/g)/(1/g) = a·(g/σ(g)) = (c·σ(g)/g)·(g/σ(g)) = c`. So `σe' = c·e'`:
`M ≅ (K e', σe' = c e')` over `K`, a **constant** module. (1) ✓.

(2) A rank-1 constant module `σe' = c e'` has Picard–Vessiot group the Zariski closure in `GL_1 = 𝔾_m` of
the cyclic group generated by the solution's transformation: `= 𝔾_m` when `c` is not a root of unity,
`= μ_n` when `c^n = 1`. In all cases `⊂ 𝔾_m`: abelian, `dim ≤ 1` (van der Put–Singer, *Galois Theory of
Difference Equations*, rank-1 classification). ✓.

(3) Shift case `K = ℂ(z)`, `σ:z↦z+1`. The function `z ↦ c^z = e^{z log c}` solves `σh = c·h`
(`c^{z+1}=c·c^z`). Then `f := g·c^z` solves `σf = σ(g)·c·c^z = (c σ(g)/g)·(g c^z) = a·f`. ✓ And
`f'/f = g'/g + log c ∈ ℂ(z)⟨log c⟩`, so `f' = (g'/g + log c)·f`: a first-order linear ODE over `ℂ(z)` with
the single constant `log c` adjoined. Hence `f` is differentially algebraic. ✓.

**Source-B instances.**
- *Prime generator* `x_p`: multiplier `a = q = p^{-1} ∈ ℂ^×` (constant, `g=1`, `c=q`). DA solution
  `x_p = p^{-s} = e^{-(log p)s}`, `x_p' = -(log p)x_p`. Holonomic, group `⊂𝔾_m`. ✓
- *Euler factor* `f_p = (1-x)^{-1}` (q-dilation `σ_q : x↦qx`): take `g = (1-x)^{-1}`, then
  `σ_q(g)/g = (1-x)/(1-qx) = a`, with `c=1`. So `a` is a pure coboundary and the solution is **rational**
  (`f_p = g`), the strongest holonomic form. ✓ (Confirms 00-status #2: each Euler factor solves a
  first-order `q`-difference equation; here it is exhibited as a coboundary, hence gauge-trivial.)

### (II) Degree-at-infinity obstruction [PROVED HERE]
Let `g ∈ ℂ(z)^×`. As `z→∞`, `g(z) ~ b·z^{d}` with `b ∈ ℂ^×`, `d = deg(num) − deg(den) ∈ ℤ`. Then
`g(z+1)/g(z) ~ b(z+1)^d / (b z^d) = (1 + 1/z)^d → 1`. Hence for any `c ∈ ℂ^×`, `c·σ(g)/g → c`, a finite
nonzero limit at `∞`. Define `deg_∞(a) := deg(den) − deg(num)` (the order of vanishing of `a` at `∞`; `<0` =
pole at `∞`). If `a` is CC then `a` has the finite nonzero limit `c` at `∞`, forcing `deg_∞(a) = 0`.
Contrapositive: `deg_∞(a) ≠ 0 ⟹ a` is not CC. A non-constant polynomial `a` has a pole at `∞`
(`deg_∞ = −deg a < 0`), so it is not CC. In particular `a(z)=z` (the `Γ` multiplier) is not CC. ∎

> This is the precise sense in which "non-constant polynomial multiplier" lands on the hypertranscendental
> side: it is not the degree per se but the **failure to be a constant times a shift-coboundary**, and the
> degree-at-`∞` invariant is an elementary, checkable witness for that failure.

### (III) Not-CC ⟹ hypertranscendental [IMPORT, precisely attributed]
The hard converse — that failure of CC forces differential transcendence of the solution — is classical:
- **`a(z) = z` (the `Γ`-factor):** `f = Γ` is hypertranscendental — **Hölder 1887** (the corpus's founding
  archimedean import, 00-status #4).
- **general `a ∈ ℂ(z)^×` not CC:** **Adamczewski–Dreyfus–Hardouin** (difference equations and
  hypertranscendence) / **Hardouin–Singer** (differential Galois theory of difference equations): a
  rank-1 (more generally diagonal) difference equation has differentially algebraic solutions iff it is
  "trivial" — exactly the CC/telescoping condition. *(Cited from the literature; not re-proved here. The
  banked corollary depends only on the `Γ` case, which is Hölder.)*

---

## Corollary (the Source-A / Source-B divide) [the organizing payload]

The multiplier's **CC class** is the archimedean–prime dividing line:

| | operator | multiplier `a` | CC? | regime | grade |
|---|---|---|---|---|---|
| **Source B** (prime) | `σ_p : x_p↦p^{-1}x_p` | constant `p^{-1}` / coboundary (Euler) | **yes** | holonomic, Galois `⊂𝔾_m`, decoupling per lane | BRIDGE/holonomic |
| **Source A** (archimedean) | `s↦s+1` on `Γ` | `s/2π` (non-const. polynomial) | **no** (deg-∞ ≠ 0) | hypertranscendental (Hölder) | IMPORT |

So: **every finite (prime) place is CC ⟹ Source B is per-lane holonomic** (the decoupling/axis-mode regime,
BRIDGE in isolation — `../2-fully-proven/erosion-cocycle-reducibility.md`), and **the archimedean place is the
unique non-CC place ⟹ Source A is hypertranscendental** (Hölder). The two sources are separated by one
intrinsic, computable invariant of the rank-1 difference module — its multiplier's coboundary class — and the
keystone **C5 is their weld** (a theorem using a non-CC archimedean lane and the CC prime lanes *jointly and
irreducibly*; `archimedean-prime-cross-term.md`), not either source alone.

## `F_q` shadow (Door-5) [PROVED HERE, structural]
Over `F_q(C)` every place is a power of one Frobenius: the place-dilations `g_v = q^{−deg v}` are **constant**
multipliers (no archimedean place exists). Hence **every** rank-1 place-module is CC ⟹ case (I) ⟹
holonomic/rational; there is **no non-CC (Source-A) place**, so no weld. This is exactly the function-field
degeneration `corank(Λ_ff)=1`, `ζ_C` holonomic (Weil) recorded in
`../2-fully-proven/function-field-holonomicity-degeneration.md` (#121): the dichotomy **predicts** the
`F_q` (all-CC, holonomic) vs `ℚ` (one non-CC archimedean place, hypertranscendental) split, and identifies
the missing single Frobenius with the missing non-CC place.

---

## Door passport — BRIDGE
- **Door-1:** refers to the rank-1 `σ`-module and the `σ_p`/archimedean generators — native carriers, but
  used one lane at a time.
- **Door-2 (master key): FAILS → BRIDGE.** Strip the multi-`q` vocabulary: case (I) is gauge theory + rank-1
  van der Put–Singer; case (III) is Hölder/ADH. Each case is a single parent; **no joint-`σ_p` apparatus is
  load-bearing.** The organizing *divide* (CC class = archimedean/prime) is the new content but it classifies
  the borders — it is not itself a weld theorem. Honest grade: a clean BRIDGE-grade foundational theorem, the
  Source-A/B analogue of G1's §59 verdict.
- **Door-3:** the CC class is a genuine difference-module invariant, but it is a per-lane (rank-1) invariant,
  not the joint corank — so it is the BRIDGE-level invariant, not the native C5★ one.
- **Door-4:** lives at the borders (Source A alone = differential Galois; Source B alone = decoupling), not in
  the weld — by design (this card *defines* the borders the weld sits between).
- **Door-5:** ✓ recovers `F_q` (all-CC ⟹ holonomic/Weil) and the single-prime border (vdPS).

---

## What is proved here vs imported (honest split)
- **PROVED HERE:** (I) the gauge-trivialization CC ⟹ holonomic with explicit DA solution `f=g c^z` and
  Galois `⊂𝔾_m`; (II) the degree-at-`∞` obstruction (elementary, airtight) placing every non-constant
  polynomial multiplier off the CC class; the Source-A/B **corollary** (the organizing divide); the `F_q`
  shadow.
- **IMPORT:** (III) the hard converse not-CC ⟹ hypertranscendental — **Hölder 1887** for `a=z` (`Γ`, all the
  banked corollary needs), and **ADH / Hardouin–Singer** for the general rational multiplier (cited; flag to
  verify the exact statement/reference against the literature before any publication-ready claim).
- **CONSEQUENCE:** the two-sources framing (#130) now has a proven backbone: the multiplier's coboundary
  class is the exact, computable invariant separating Source A from Source B, and C5 = their weld.

## Gates
- [x] 0 → 1  in-progress: dichotomy stated precisely (CC class, not just "constant vs polynomial"); both
  cases' inputs pinned; import-vs-proved-here split written; Door passport.
- [x] 1 → 2  fully-proven: case (I) gauge-trivialization proved; case (II) degree-at-∞ obstruction proved;
  Source-A/B corollary + `F_q` shadow established; hard converse (III) attributed import (Hölder + ADH).
  **Grade BRIDGE.**
- [ ] 2 → 3  formalized: Lean anchors **DONE** for (I)'s gauge multiplier identity and local DA-ODE:
  `ccGaugeMultiplier_eq_const` in `formal/GaloisForLFunctions/MultiplierDichotomy.lean` proves
  `a·σ(1/g)/(1/g)=c` when `a=c·σ(g)/g`, and `hasDerivAt_mul_exp_const_ode` proves the local derivative
  identity for `f(z)=g(z) exp(z*lam)`, i.e. `f'=(g'/g+lam)f` where `g z ≠ 0`. The global shift equation
  `σf=a·f` is also Lean-backed by `ccShiftSolution_eq`. Remaining Lean targets: Picard-Vessiot
  classification for the rank-one constant module; (II) `g(z+1)/g(z) → 1` for rational `g` ⟹ deg-∞
  obstruction; reuse the prime-lane floor (`localEulerFactor_q_difference`, `logPrime_no_rat_relation`).
  Case (III) is an import gap — mark it.
- [ ] 3 → 4  publication-ready: "the multiplier-coboundary dichotomy of rank-1 difference modules: the
  archimedean–prime divide and the location of the keystone weld."

## Cross-references
- `two-sources-of-hypertranscendence.md` — the framing this theorem grounds (its 1→2 gate, executed here).
- `archimedean-prime-cross-term.md` — the C5 weld carrier the corollary points to (a non-CC × CC joint theorem).
- `gamma-module-construction.md` — the polynomial-multiplier worked example (`M_∞`, `a=s/2π`); the canonical
  non-CC lane.
- `../../door/G1-difference-holder.md` — Source-B (constant/coboundary, BRIDGE) per-prime floor; Source-A
  (Hölder, import).
- `../2-fully-proven/function-field-holonomicity-degeneration.md` (#121) — the `F_q` all-CC degeneration the
  Door-5 shadow recovers.

## Log
- 2026-06-19 — created in 0-backlog (framing's extractable theorem).
- 2026-06-19 — DeWitt: pulled to in-progress; **proved → 2-fully-proven (BRIDGE)**. Identified the dividing
  invariant as the σ-**coboundary class** (CC) of the multiplier (sharper than "constant vs polynomial").
  Proved case (I) gauge-trivialization (CC ⟹ holonomic, Galois `⊂𝔾_m`, DA solution `f=g c^z`) and case (II)
  the degree-at-∞ obstruction (`g(z+1)/g(z)→1` ⟹ non-constant-polynomial multipliers are non-CC, putting
  `Γ` on the hypertranscendental side) — both elementary, airtight. Hard converse (III) attributed import:
  Hölder 1887 (`Γ`) + ADH/Hardouin–Singer (general). Established the Source-A/B corollary (CC class = the
  archimedean–prime divide; C5 = the weld) and the `F_q` all-CC ⟹ holonomic Door-5 shadow (predicts the
  `corank` 1 vs ∞ split, #121). Library-backlog ticket filed for 00-status #130 / new theorem row.
- 2026-06-19 (Leaner) — added Lean anchors `ccGaugeMultiplier_eq_const` and
  `hasDerivAt_mul_exp_const_ode` in `formal/GaloisForLFunctions/MultiplierDichotomy.lean`, proving the
  case-(I) gauge identity `a·σ(1/g)/(1/g)=c` from `a=c·σ(g)/g` in abstract commutative group notation and
  the local analytic ODE identity for `f(z)=g(z) exp(z*lam)`. Added the module to the root import and axiom
  audit; `lake build` and `scripts/check_axioms.sh` pass with 250 audited theorem outputs and no `sorry`.
  Card remains in `2-fully-proven`; the Picard-Vessiot classification, degree-at-infinity obstruction, and
  imported hypertranscendence converse are not fully formalized.
- 2026-06-19 (Leaner) — corrected Lean status: `ccShiftSolution_eq` already formalizes the global shift
  equation for the case-(I) solution `f(z)=g(z) exp(z*lam)`. Updated
  `../3-formalized/cc-gauge-trivialization-identity.md` to keep the paper proof and Lean certificate in sync.
  Remaining unformalized pieces are Picard-Vessiot classification, the rational degree-at-infinity obstruction,
  and the imported Hölder/ADH hypertranscendence converse.

## Lean return note — 2026-06-19 (Leaner)

Returned from `2-fully-proven`: the case-(I) gauge identity and local ODE identity are Lean-backed, but the card's whole theorem also includes the global shift solution equation, the rational degree-at-infinity obstruction, and the Hölder/ADH hypertranscendence converse. Those are not formalized.

## Triage note — 2026-06-19 (Professor): returned to 2-fully-proven (user-directed; Leaner over-return)

Per @user ("send tickets that are clearly 'leaner is just lazy' back to fully-proven"): Leaner's return was a
**Lean-library-coverage objection** (no formal model of the imported / categorical / analytic objects), **not** a
paper-proof defect. This is a **paper-proven BRIDGE theorem** whose proof legitimately credits classical imports;
those imports are to be carried as hypotheses/axioms (or formalized separately) at the Lean stage — not a reason to
reject the paper proof. The card's stated theorem is proved at its 1→2 gate; any co-located open conjecture
(C5★ / ω=0 / Schanuel / apex) is explicitly a SEPARATE open core, not part of this theorem. Re-banked for Lean re-attempt.
