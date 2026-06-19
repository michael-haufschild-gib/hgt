# MOONSHOT — 2πi is the Frobenius: the missing F₁ is the log-monodromy / deck transformation at infinity

- **ID:** moonshot-2pi-monodromy-frobenius
- **Stage:** 0-backlog
- **Type:** MOONSHOT CONJECTURE (wild; <5% true; far beyond SOTA) — **the most grounded of the set; test first**
- **Priority:** FIELDS MEDAL (+)
- **Target of attack:** **untie `ω∈H²(G_L)` / construct the missing archimedean Frobenius F₁** (#27/#71;
  `compute-omega-h2-gl.md` §S, `a_∞=½log2π`).
- **Source:** chat thread 2026-06-19 (archimedean-Frobenius moonshots).

## The wild claim
At a finite prime, cyclotomy gives roots of unity and Frobenius. ℝ has **no roots of unity past `±1`**, so the
"cyclotomic Frobenius at ∞" is missing — *that* is the knot. But ∞ has one infinite-order object finite primes
lack: **the monodromy of `log`.** `x^s = e^{s log x}` is multivalued; encircling `0` adds `2πi`.

> **Conjecture (2πi-Frobenius).** The missing archimedean Frobenius is the **deck transformation `2πiℤ`** of
> the universal cover of `ℂ*` — the **infinite-order refinement of complex conjugation** (which is only the
> order-2 `Frob_∞` in the archimedean Weil group). `ω` = the **`2πi`-monodromy class**; `a_∞=½log2π` contains
> the `2π` by construction. **"Untie the knot" = unwind `log` around the `s=1` pole; the knot IS the branch
> cut.**

## Untie move / test (concrete, near-term)
1. Is `[ω]` exactly the class of the **`log`-monodromy** in `H²(G_L)`?
2. Does the **FE-gluing of `a_∞`** (the open Layer-2 of `compute-omega §S`) reduce to the **winding number
   around the `s=1` pole** `= N(T)` (the zero-count; the `moonshot-rh-spectral-flow-index` `[ω]=N(T)`
   quantization)? — **checkable against the existing `compute-omega §S` machinery.**
3. **Untie:** if so, the Frobenius is the integer winding; `ω=0` ⟺ the winding is trivial after FE-gluing.

## Why <5%
"`2πi` as a Frobenius" conflates a transcendence period with a field endomorphism; the refinement of the
order-2 `Frob_∞` to infinite order has no current mechanism. But it is the **only** idea here with a
ready-made test and it explains the `2π` in `a_∞`.

## Door / grade
MOONSHOT. If `[ω] =` log-monodromy `= N(T)`, it instantly fuses the archimedean knot with the
topological-charge moonshots (Frobenius = winding = `a_∞`'s `2π`, one object) — a strong D2 unification.

## Cross-references
- `compute-omega-h2-gl.md` (#27, §S) — `a_∞`, the FE-gluing; the test target.
- `moonshot-rh-spectral-flow-index.md` (M2, `[ω]=N(T)` quantization) — this gives the **Frobenius reading** of
  that winding; `moonshot-prime-skyrmion-no-clock.md` (M3) — the winding/texture sibling.
- `omega-splits-wild-kernel-freeness.md` — the wild-kernel/`ω` splitting the monodromy would refine.

## Log
- 2026-06-19 — filed (archimedean-Frobenius moonshot set). Missing F₁-Frobenius = `2πiℤ` log-monodromy /
  deck transformation, infinite-order refinement of order-2 complex conjugation; `ω` = the monodromy class;
  untie = unwind `log` at `s=1`. SO-1: "monodromy" is used for function-field Deligne–Katz and the winding
  moonshots; the *log-branch-as-archimedean-Frobenius* reading is distinct. **Flagged to test first.**
