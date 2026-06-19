# Bucket G1 — Difference-Hölder (the keystone / C5 candidate)

**Bucket grade:** organizational (SEARCH channel). Sorted from `docs/support-extraction-log.md` +
`00-charter-wall-and-door.md`. Air-marks of the source are preserved verbatim.
**Scope (one line).** ζ (and every arithmetic L) satisfies **no single algebraic q-difference
equation** — it needs *all* dilations `σ_p: x_p↦p^{-1}x_p` (`q_p=1/p`) at once.
**Work package this seeds.** Re-test §59 against **Door-2** and decide whether difference-Hölder
earns the charter's **NATIVE / C5** grade. This is *the single most consequential charter action*
in the corpus (it would upgrade the proto-branch verdict).

---

## The conjecture (as stated in the log header)

> **G1 — Difference Hölder (KEYSTONE/C5):** ζ satisfies no single algebraic q-difference equation.

The native reading (from #67 §18): *"ζ has no **single** difference equation because it needs **all**
the dilations `q_p=1/p` at once — and that simultaneity **is** the Euler product = unique
factorization."* So difference-Hölder is **not** "no q-difference structure" (each Euler factor has
one) but **"no single dilation `q` amalgamates the infinitely many `q_p=1/p`."** The obstruction is
the **ℚ-linear independence of `{log p}`** (fundamental theorem of arithmetic).

---

## What belongs here

### The single-factor base case — a real computation (#67 §18, Brick #11)
- A single Euler factor `f=(1−x)^{-1}` under `σ_q: x↦qx`, `q=1/p`, satisfies a **genuine first-order
  linear q-difference equation** `f(qx) = (1−x)/(1−qx)·f(x)`. Each prime *individually* is
  q-difference-algebraic (group `⊂ 𝔾_m`, abelian). *Air: the single-factor equation is a real
  computation; the global no-single-equation is the conjecture G1.*
- Ledger floor (#67, Tier-A A4): `{log p}` is **ℚ-linearly independent**, via unique factorization
  (`Nat.factorization`), formalized as `logPrime_no_rat_relation` (`Core.lean`). *This is the
  rigorous floor under G1's "needs all `q_p` at once."* (ledger-proven)

### The structural proof in the difference category (#68 §59 — the HEADLINE)
- **G1 = the C6-converse for `Λ=0`, PROVED in the difference category (§59).** §59.1 Galois-dimension
  argument: a holonomic diagonal ⟹ finite-dim s-difference-Galois group; but the arithmetic
  s-monodromy `g=(p^{-1})_p` has **infinite-dimensional Zariski closure** when `Λ=0` (unique
  factorization) ⟹ contradiction ⟹ ζ (and every arithmetic L, all `Λ=0`) satisfies **no finite-order
  linear difference equation** = **difference-hypertranscendental**. (draft-claimed `[PROVED HERE]`,
  difference category)
- **Caveat (§61.3, self-correction #15):** this is the **difference**-category Hölder; *literal
  differential* Hölder for ζ is **imported** (Hölder 1887), and for general L is **conjectural**
  (reducible via Adamczewski–Dreyfus–Hardouin). So G1 as "no single algebraic q-difference equation"
  is **essentially proved here**; G1 as "no differential equation" is Hölder (import) for ζ.
- **Source A / Source B reading (2026-06-19, the Hölder-recentering).** The two halves above are the
  field's **two sources of hypertranscendence**, and Hölder 1887 belongs to the *archimedean* one:
  - **differential Hölder = Source A** — the archimedean factor `Γ` (one operator, **polynomial**
    multiplier `Γ(z+1)=z·Γ(z)`); classical, a Door-5 **border** (differential Galois). Not a mere
    side-import: it is the *founding* hardness, which `ζ` inherits through the completion `Λ=Γ·ζ`.
  - **difference-G1 = Source B** — the infinite prime base (`σ_p`, **constant** multipliers); native in
    aggregate but **decouples prime-by-prime** ⟹ **BRIDGE** (the Door-2 verdict below).
  - **The C5 keystone is neither source alone — it is their weld** (`∂_s` coupled to `σ_p` on `Λ`, the
    archimedean×prime cross-terms). So G1's BRIDGE grade is *expected*: §59 tests Source B alone. See
    `../pipeline/0-backlog/two-sources-of-hypertranscendence.md`, [[bucket-archimedean-generator]], and the
    "Second carrier dimension" note in [[door-C5-irreducibility-and-door-2-retest]].
- **Single-q version (§51.1):** finite single-σ q-difference groups are *cyclic*, but the arithmetic
  object needs the **full pro-torus `𝕋^∞`** — which is exactly why one prime / one dilation cannot
  carry G1.

### The Door-2 re-test — DONE (2026-06-19): BRIDGE
- §59 and §60 were the leading C5 candidates. **Verdict: both BRIDGE, not NATIVE.** Stripped of the
  multi-q vocabulary, §59's proof is single-operator difference Galois (the one shift `s↦s+1`, van der
  Put–Singer; ADH the named tool) + closure-of-`⟨g⟩`-in-`𝕋^∞` `= corank` (Kronecker–Weyl) + `{log p}`
  ℚ-independent (unique factorization). The native simultaneous-`σ_p` group `G_L` is never used, so a
  parent proves it ⟹ **fails Door-2.** Full reasoning: [[door-C5-irreducibility-and-door-2-retest]].
- So §59 is a genuine **BRIDGE** (it internalizes and generalizes Hölder — C6), not the C5 keystone;
  the charter's C5 gap stands. A real C5 theorem must use the `σ_p` jointly and irreducibly.

---

## Status ledger for this bucket

| Piece | Tier / grade | Source |
|---|---|---|
| `{log p}` ℚ-LI (the obstruction's floor) | **ledger-proven** (`logPrime_no_rat_relation`) | #67 |
| single Euler factor q-difference equation | computation (draft-claimed) | #67 §18 |
| difference-category Hölder for ζ + all arithmetic L | **`[PROVED HERE]`** (difference category) | #68 §59 |
| literal *differential* Hölder for ζ | **import** (Hölder 1887) | #68 §61.3 |
| differential Hölder for general L | **open / conjectural** (ADH-reducible) | #68 §61.3 |
| §59 Door-2 grade (re-tested 2026-06-19) | **BRIDGE** — proof reduces to parents; not C5 | — |

## Open core / the work package

1. **Door-2 re-test of §59 — DONE: BRIDGE** (not the C5 keystone; see
   [[door-C5-irreducibility-and-door-2-retest]]). The next C5 attempt must use the `σ_p` jointly and
   irreducibly, not the diagonal's hypertranscendence.
2. **General-L differential Hölder** via the Adamczewski–Dreyfus–Hardouin reduction (the import→native
   upgrade for the differential statement).

## Cross-references
- [[G3-holonomy-dichotomy]] — §60 corank dichotomy is G1's structural twin (same Galois-dimension
  argument; `dim⟨g⟩-closure = corank(Λ)`).
- [[door-C5-irreducibility-and-door-2-retest]] — where the NATIVE-grade verdict is decided.
- [[bucket-the-seam-archimedean-obstruction]] — the obstruction (ℚ-indep of `{log p}` vs the one
  archimedean place) is the seam.
