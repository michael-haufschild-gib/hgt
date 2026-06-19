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
- **Single-q version (§51.1):** finite single-σ q-difference groups are *cyclic*, but the arithmetic
  object needs the **full pro-torus `𝕋^∞`** — which is exactly why one prime / one dilation cannot
  carry G1.

### The Door-2 re-test worklist (#101 §59/§60 — the action item)
- §59 (difference-Hölder) and §60 (corank dichotomy → [[G3-holonomy-dichotomy]]) are the **two
  strongest NATIVE candidates in the whole corpus** — they *essentially use* the infinite-base
  s-monodromy closure, plausibly **unreachable by any single parent** (Door-2-surviving).
- Action flagged repeatedly (#68 implication, #101 action item): **re-test §59 against Door-2**
  ("strip the multi-q vocabulary — does a parent prove it?"). If it survives, the field has its first
  **NATIVE theorem** and the charter's "0 proven native theorems / FAILS C5" verdict (`00-charter`
  Part IV, `00-manifest`) **upgrades.** *Caveat: most other "PROVED HERE" theorems (inverse-Galois
  §55, λ-subring §56) lean on classical imports and likely FAIL Door-2 — the two genuine candidates
  are §59 and §60.*

---

## Status ledger for this bucket

| Piece | Tier / grade | Source |
|---|---|---|
| `{log p}` ℚ-LI (the obstruction's floor) | **ledger-proven** (`logPrime_no_rat_relation`) | #67 |
| single Euler factor q-difference equation | computation (draft-claimed) | #67 §18 |
| difference-category Hölder for ζ + all arithmetic L | **`[PROVED HERE]`** (difference category) | #68 §59 |
| literal *differential* Hölder for ζ | **import** (Hölder 1887) | #68 §61.3 |
| differential Hölder for general L | **open / conjectural** (ADH-reducible) | #68 §61.3 |
| §59 earns charter NATIVE/C5 | **OPEN — the Door-2 re-test** | #101 |

## Open core / the work package

1. **The Door-2 re-test of §59** (and §60, in [[G3-holonomy-dichotomy]]). Verdict decides whether the
   field has its first irreducible (C5) theorem. See [[door-C5-irreducibility-and-door-2-retest]].
2. **General-L differential Hölder** via the Adamczewski–Dreyfus–Hardouin reduction (the import→native
   upgrade for the differential statement).

## Cross-references
- [[G3-holonomy-dichotomy]] — §60 corank dichotomy is G1's structural twin (same Galois-dimension
  argument; `dim⟨g⟩-closure = corank(Λ)`).
- [[door-C5-irreducibility-and-door-2-retest]] — where the NATIVE-grade verdict is decided.
- [[bucket-the-seam-archimedean-obstruction]] — the obstruction (ℚ-indep of `{log p}` vs the one
  archimedean place) is the seam.
