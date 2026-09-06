# The integer lag law

- **ID:** `integer-lag-law`
- **Stage:** 4-publication-ready
- **Type:** THEOREM (Lean)
- **Knowledge label:** `[NEW THEOREM] [FORMALISED] [PUBLICATION READY]`
- **Manuscript:** `integer-lag-law-manuscript.md`
- **Source boundary:** the genus-kernel explicit formula, the Landau theorem, Bohr almost periodicity,
  Kronecker's theorem and the integral-basis theorem are corpus theorems; every statement of the
  manuscript is proved internally.

## Closed claim

With `a_n = [(n − ψ(n)) + n(Σ_{m≤n}Λ(m)/m − log n + γ) − log 2π + S(n)]/√n` and `a_1 = 2 + γ − log 4π`:

1. RH ⟺ `a_n ≤ a_1` for all `n ≥ 1` ⟺ `(a_n)` bounded above ⟺ bounded below; dichotomy (all `|a_n| ≤ a_1`,
   or unbounded both ways).
2. Unconditionally `limsup a_n ≥ a_1`; under RH `a_1` is the supremum of every tail, reached along `b^m` for every `b`.
3. Unconditionally `E(n) = a_n√n` is `> (a_1 − ε)√n` and `≤ −η√n` infinitely often; RH ⟺ `Φ` Bohr almost periodic.
4. Under RH, `inf_{n≥2} a_n = −a_1` ⟺ no odd integer relation among the ordinates.

Open (recorded, not claimed): the single-base criterion RH ⟺ `sup_m a_{b^m} < ∞` (open core: `b`-resonance).

## Gates

- [x] 0 → 1: exact formula and criterion isolated (Route O lag form)
- [x] 1 → 2: complete paper proofs (card `1-in-progress/weil-lag-function-bochner-form.md` §§1–9)
- [x] 2 → 3: Lean theorems, targeted builds, axiom audit (`3-formalized/lag-explicit-formula-lean.md`)
- [x] 3 → 4: manuscript with certificate table

## Anti-theatre closure

- No numerical input in any proof; the pod run is illustration only.
- The criterion is not a re-encoding of a known one: it is one-sided, exact, and the constant is the
  sequence's own value at `n = 1`.
- The floor law is a genuine equivalence with a Diophantine condition, not a corollary of LI.
- It remains a receiver for RH: the manuscript says so in §7.

## Log
- 2026-09-06 — Lean closure of Theorems 1–6; manuscript written; stage 4.
