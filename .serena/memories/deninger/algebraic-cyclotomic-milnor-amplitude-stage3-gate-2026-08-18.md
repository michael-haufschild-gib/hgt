# Deninger algebraic cyclotomic Milnor amplitude — Stage-3 gate

Audited `docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/deninger/deninger-algebraic-cyclotomic-milnor-amplitude.md` on 2026-08-18.

- Exact headline: for every algebraic `F/ℚ`, `K_q^M(F) ⊗ ℝ = 0` for `q ≥ 2`, plus the full two-term amplitude and downstream `E∞` statement.
- Existing unconditional Lean: `RHTower.deningerRationalMilnorRealVanishing` and `RHTower.deningerRationalMilnorAmplitude` in `formal/GaloisForLFunctions/RHTower/DeningerRationalMilnorAmplitude.lean`; this is only the `F = ℚ` specialization. It compiled with `lake env lean`; axiom prints give exactly `[propext, Classical.choice, Quot.sound]`; it is already imported by `GaloisForLFunctions.RHTower`.
- Existing general declaration `RHTower.deningerMilnorRealVanishing_of_tameKernelTorsion` in `DeningerMilnorRealShape.lean` takes an explicit `hTK` premise: torsion of the degree-two tame kernel of every finite number-field subextension. Hence it cannot support Stage 3 under the no-hypothesis rule.
- The exact missing theorem is the active Stage-1 `garland-tame-kernel-torsion` / `garland-formalization-programme`: Garland finiteness (`K₂(O_K)` finite, so tame kernel torsion) for arbitrary number fields. External audit confirms Garland's 1971 Annals paper; no existing library theorem proves it.
- Do not move original card to Stage 3 or replace its statement by `F = ℚ`: that would be a strict weakening. Its additional E∞/derived statement also remains unformalized because corresponding homotopy-theoretic infrastructure is absent.
- `scripts/formal_tools.py lint` currently fails only on seven unrelated HTGeometry modules unreachable from the umbrella; do not fix outside scope without direction.

## 2026-08-18 exact infrastructure progress

- Added and wired `formal/GaloisForLFunctions/HTGeometry/SteinbergWeylTriangle.lean`.
- It proves, unconditionally from the presentation, `steinbergWeyl_triangle_mul`: `w_ik(u) w_kj(v) w_ik(-u) = w_ij(uv)`, plus the `v = 1` specialization and exchange form. The proof uses only existing Weyl conjugation theorems; final `lake build GaloisForLFunctions.HTGeometry.SteinbergWeylTriangle` succeeded.
- `#print axioms` for all three declarations gives exactly `[propext, Classical.choice, Quot.sound]`.
- This is genuine rank-three word infrastructure for Milnor Lemma 9.8. The remaining local core is exact `w_ij(u) w_ij(-1) w_ij(1-u) = w_ij(u(1-u))` (and its orientation/word-normalisation dependencies); do not assert a triangle-defect-to-symbol identity without proving it.
