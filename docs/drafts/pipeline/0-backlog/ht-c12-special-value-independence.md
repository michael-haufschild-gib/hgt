# Generic special-value independence — finite jet values algebraically independent

- **ID:** ht-c12-special-value-independence
- **Stage:** 0-backlog
- **Type:** CONJECTURE
- **Source:** ../../door/bucket-hypertranscendence.md · C12
- **Statement:** For generic point `a` and generic `f ∈ HT`, the jet values `f(a), f'(a), …, f^{(n)}(a)` are algebraically independent over the constant field, for every finite `n`.

## Goal
Promote the note's explicit warning ("function-level independence does NOT imply value-level") into a second-step **value-level** hypothesis. Door: this is the **(B) value-relations** side — the same axis as the wild kernel `K` / Stieltjes constants `γ_n` whose value-independence is the field's frontier.

## Door grade (hint)
**Apex-adjacent (value-level, (B)-side).** NOT BRIDGE. For the *native* objects (e.g. `γ_n = ` jet/period data of the digamma/`E_1` connection) the corresponding statement is exactly **DSS = K free = H₂(Lie K)=0 — open** (Schanuel/Nesterenko-type). The generic-`f` version is the structural shadow of that apex.

## Approach
Do NOT expect an elimination-to-Hölder collapse — that is the whole point (the (A)→(B) gap). Attack the generic statement via a measure/genericity argument (each algebraic relation among jet values cuts a proper subvariety of `(a, f)`-space); the hard native instance routes to the regulator-injectivity / Schanuel-for-periods machinery. Methods: 1 split, 2 attack-as-false (algebraic-valued HT functions exist), 14 weaken to "generic/almost-every `a`".

## Gates
- [ ] 0 → 1  in-progress: well-posed over a fixed base K and function category; source-pure; attack idea; Door passport sketch
- [ ] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [ ] 2 → 3  formalized: Lean theorem, `lake build` green, `check_axioms.sh` PASS
- [ ] 3 → 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Cross-references
- `gamma-zeta-differential-independence.md`, `exponential-period-dss-cross.md`, `hypertranscendence-axis-synthesis.md` §2–§3 (the `γ_n` as value-level coordinates; DSS apex).
- `../../door/bucket-hypertranscendence.md` · C12; sibling value-level card C13.

## Log
- 2026-06-20 — created in 0-backlog from bucket C12. Graded apex-adjacent (value-level) — the native instance is the DSS apex.

## 2026-06-24 source audit — generic version likely known

Haiku entropy-drew C12 after the finite-jet nonidentifiability theorem. The finite-jet theorem does **not** refute
the generic C12 claim: it only proves HT alone imposes no finite value relation, since any finite jet table can
be realized by an HT function. Thus C12 must be read as a genericity/value-level statement, not as a consequence
of function-level HT.

Source audit found a close known framework: Jones--Kirby--Le Gal--Servi, *On local definability of holomorphic
functions* (arXiv:1712.07064). Their Definition 3.1 defines strongly transcendental holomorphic functions by
transcendence-degree lower bounds for finite jets at tuples of distinct points, and Proposition 3.2 states that
`ST(U)` is residual in `O(U)`. This appears to cover the generic finite-jet value-independence phenomenon in a
stronger form, at least over the countable/base-field setting used there.

Verdict: C12 should not be promoted as new generic mathematics without isolating a delta beyond strong
transcendence. The HGT-useful conclusion is conceptual: C12 is the value-level/generic backdrop, while the
finite-jet nonidentifiability theorem shows that no such independence follows from HT alone. Native arithmetic
instances (`γ_n`, DSS/wild-kernel freeness) remain open and are not advanced by the generic Baire theorem.
