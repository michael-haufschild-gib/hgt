# QECLean provenance

Vendored copy of <https://github.com/Stavan-Jain/QECLean>, commit
`7d8bf6da3953448ece3d9e60a4f0324f3ca9c24d` (2026-07-27, `main`), Apache-2.0
(`LICENSE` here).

Upstream builds on Lean/mathlib `v4.30.0-rc2` with a mathlib `master` pin
(`a3fde5017d59fa3cef8d4d24999f6b9b71b89a3b`); here it builds on `v4.32.2`.
The two-release gap required in-tree proof repairs, listed below.

## Deviations from upstream

1. Imports rewritten `QEC.*` → `GaloisForLFunctions.QECLean.*`; the module
   tree under `QEC/` is otherwise mirrored one-for-one.  Declaration
   namespaces are untouched — everything still lives under `Quantum`,
   `Quantum.Stabilizer`, `Quantum.Stabilizer.Homological.BB`, etc.
2. Upstream's `[leanOptions]` are restored per module, since our `lakefile.toml`
   sets none of them: `autoImplicit false`, `relaxedAutoImplicit false`,
   `maxSynthPendingDepth 3`.
3. Not vendored: `QEC/Stabilizer/Codes/_TEMPLATE.lean` (a scaffold whose body
   is a deliberate `sorry`) and its import line in `Stabilizer/Codes.lean`;
   `Playground.lean` (scratch); `QECLight.lean` (an alternative reduced import
   surface for memory-constrained CI, not a distinct theorem set).
4. v4.30 → v4.32 drift repairs (proof-only; no statement was weakened):
   - `AddMonoidAlgebra` became a one-field structure over `M →₀ R` and is no
     longer defeq to `Finsupp`.  `Homological/BBEpsFreeGroupAlgebra.lean` now
     goes through `.coeff` and `AddMonoidAlgebra.sum_coeff_single`.
   - Several `simpa`/`convert` steps whose simp-normal forms shifted were
     replaced by explicit `calc`/`rw`/`exact` chains: `Foundations/Basic.lean`,
     `RepetitionCode/LogicalX.lean`, `PauliGroup/Representation.lean`,
     `PauliGroup/TransversalConjugation.lean`, `Homological/Code.lean`.
   - `PauliGroup/Commutation.lean`: the `Fin 4` phase-parity arguments were
     rebuilt on three new private lemmas (`val_nsmul_two`,
     `nsmul_two_eq_zero_iff_even`, `nsmul_two_eq_two_iff_odd`) plus a
     structural identity `mulOp_phasePower_eq_add_card_nsmul`, replacing
     `nsmulRec`-unfolding `simp_all`/`erw` chains that no longer fire.

## Trust: `native_decide`

Upstream is `sorry`-free, and so is this copy.  It does, however, use
`native_decide` in 59 modules (357 call sites) — chiefly the concrete-code
distance certificates (bivariate-bicycle/gross, Steane distance, rotated
surface, concatenation independence).  Those theorems therefore depend on the
`Lean.ofReduceBool` axiom (compiler trust), not only on
`[propext, Classical.choice, Quot.sound]`.  The Pauli/binary-symplectic layer,
the stabilizer framework, and the toric-code chain-complex development are
kernel-only.  Check any endpoint you rely on with `#print axioms`.

The repo lint gate (`scripts/formal_tools.py lint`) is line-based and does not
flag `native_decide`; treat this section as the axiom map.

## Duplicate audit

Scanned every fully-qualified declaration name in this subtree against the rest
of `formal/GaloisForLFunctions` (3 799 vendored names vs 147 450 corpus names):
**no collisions**.

The other vendored quantum area, `GaloisForLFunctions/QuantumAlg`
(Lean-QuantumAlg: circuits, QFT, Shor, amplitude amplification), lives in the
root `QuantumAlg` namespace and covers quantum *algorithms*; this area covers
quantum *error correction* in the `Quantum` namespace.  They share no
declarations and neither imports the other.  mathlib v4.32.2 has no stabilizer
or QEC development.
