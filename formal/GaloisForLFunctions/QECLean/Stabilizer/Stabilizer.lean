import GaloisForLFunctions.QECLean.Stabilizer.Foundations
import GaloisForLFunctions.QECLean.Stabilizer.Framework
import GaloisForLFunctions.QECLean.Stabilizer.Geometry
import GaloisForLFunctions.QECLean.Stabilizer.Codes

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

/-!
# Stabilizer formalism — top-level umbrella

Top-down structure of the stabilizer-code library:

1. `Foundations` — Pauli + binary-symplectic algebra (pure algebra; floor)
2. `Geometry`    — lattice-family-agnostic primitives
3. `Framework`   — abstract stabilizer / homological theory
4. `Codes`       — concrete codes (toric, rotated-surface, repetition, small)

Layering: `Foundations < {Geometry, Framework} < Codes`.
-/
