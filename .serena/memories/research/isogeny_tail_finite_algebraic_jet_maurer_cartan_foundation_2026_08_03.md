# Isogeny-tail finite algebraic jet/Maurer–Cartan foundation (2026-08-03)

Closed unconditionally in Lean:
- `formal/GaloisForLFunctions/HTGeometry/AlgebraicGroupJet.lean`: truncated arc algebra `R[t]/(t^(n+1))`; augmentation; antitone order ideals; restriction; scheme-valued jets for arbitrary/non-affine group schemes; constant/evaluation split; target maps; coefficient-algebra prolongation with identity/composition.
- `formal/GaloisForLFunctions/HTGeometry/MaurerCartanJetQuotient.lean`: for commutative group schemes, canonical normalization `j / const(eval j)`, product trivialization `J^nG(R) ≃ G(R) × ker(eval)`, quotient `J^nG(R)/constant(G(R)) ≃ ker(eval)`, and for every `H ≤ G(R)` the position–velocity split `J^nG(R)/H ≃ (G(R)/H) × ker(eval)`.
- `formal/GaloisForLFunctions/HTGeometry/AlgebraicGroupInfiniteJet.lean`: coherent inverse-limit `J∞G(R)`, finite projections with common evaluation, constant section, infinite Maurer–Cartan split, and `J∞G(R)/H ≃ (G(R)/H) × basedInfiniteJets` for every constant subgroup `H`.
- Card module imports quotient foundation; HTGeometry umbrella wired.

Verification:
- direct `lake env lean` passes both new files and `IsogenyTailMaurerCartanHolography.lean`.
- targeted build of `GaloisForLFunctions.HTGeometry.IsogenyTailMaurerCartanHolography` passes.
- axiom audit: only `propext`, `Classical.choice`, `Quot.sound`.
- no stale Lean processes.

Card remains Stage 2. Exact open cores: finite-etale quotient/jet compatibility and fixed fields; Zariski-closed stabilizers; inverse-limit infinite jets; smooth char-0 identification of based jets with iterated Lie data; quotient scheme `G/H`; invariant differential function-field generation; logarithmic-derivative genericity/dtrdeg=dim; scheme quotient descent.

Important: concurrent unrelated commit `dbb329b5f` accidentally captured initial versions of the two new modules under an unrelated commit message. Current coefficient-prolongation additions and wiring/docs remain working-tree changes. Preserve unrelated worktree edits.