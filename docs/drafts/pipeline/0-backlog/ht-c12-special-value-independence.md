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
