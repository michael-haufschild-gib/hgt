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
   - `Homological/BBConvRing.lean`: `convEquiv` now factors through
     `AddMonoidAlgebra.coeffLinearEquiv`; a new `convEquiv_single` replaces the
     removed `AddMonoidAlgebra.single_apply`, and `mul_apply_antidiagonal`
     became `coeff_mul_antidiag`.  `Homological/BBBocksteinTransport.lean`
     follows suit, and derives surjectivity of `mapDomainRingHom` through
     `coeff_injective` instead of `Finsupp.mapDomain_surjective` directly.
   - `Toric/{WrappingInvariants,DualWrappingInvariants,StabilizerCode}.lean`,
     `Concatenation/Independence.lean`, `Gross/{CRTFrame,StabilizerCode}.lean`,
     `Z3Z6/StabilizerCode.lean`: `convert … using 1` now leaves definitional
     side goals (`(0 : α → ZMod 2) x = 0`, `f = ⇑fLinearMap`) that used to
     close silently; each is discharged by `rfl` or by `congr_fun` on the
     membership hypothesis.
   - `Gross/SafeFloor/MImClassify.lean`: two `dsimp only` calls that are now
     no-ops (an error in v4.32, previously accepted).
   - Two `exact?` proof-search tactics left in upstream
     `Toric/DualWrappingInvariants.lean` were replaced by the proofs they find
     (`toric_finrank_ker_cutMap_eq_one`, `toricDualBoundaries_le_toricDualCycles`).
   - Style-linter fixes so the repo's `lint --build` gate stays warning-free:
     four `omit [Fact (Odd L)] [Fact (3 ≤ L)] in` in
     `RotatedSurface/H1Dimension.lean`, three no-op `change` tactics removed,
     and two unused `simp` arguments dropped.

## Trust: `native_decide`

Upstream is `sorry`-free, and so is this copy.  It does, however, use
`native_decide` in 59 modules (357 call sites) — chiefly the concrete-code
distance certificates (bivariate-bicycle/gross, Steane distance, rotated
surface, concatenation independence).  Those theorems carry per-call
`…_native.native_decide.ax_…` axioms (compiler trust) on top of
`[propext, Classical.choice, Quot.sound]`.

Audited here with `#print axioms`:

| Endpoint | Axioms |
|---|---|
| `NQubitPauliGroupElement.commutes_iff_even_anticommutes` | kernel-only |
| `StabilizerGroup.ToricCodeN.toricCodeN_distance_eq_L` (toric distance `= L`) | kernel-only |
| `StabilizerGroup.Steane7.transversalH_Steane7_isLogicalGate` | kernel-only |
| `Stabilizer.Homological.BB.grossStabilizerCode_hasCodeDistance_12_uncond` | + ~100 `native_decide` axioms |

So the headline toric result is kernel-checked; the gross-code `[[144,12,12]]`
distance certificate is not.  Check any endpoint you rely on with
`#print axioms`.

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
