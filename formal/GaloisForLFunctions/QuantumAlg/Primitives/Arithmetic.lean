/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import GaloisForLFunctions.QuantumAlg.Init
public import GaloisForLFunctions.QuantumAlg.Primitives.Arithmetic.BitSlice
public import GaloisForLFunctions.QuantumAlg.Primitives.Arithmetic.Comparator
public import GaloisForLFunctions.QuantumAlg.Primitives.Arithmetic.PlainAdder
public import GaloisForLFunctions.QuantumAlg.Primitives.Arithmetic.PlainAdder.Schedule
public import GaloisForLFunctions.QuantumAlg.Primitives.Arithmetic.PlainAdder.StructuredCircuit

/-!
# Reversible arithmetic primitives

This module re-exports reusable non-modular reversible-arithmetic primitives:
bit-slice base-gate blocks, comparator schedule shells, plain-adder interfaces,
folded plain-adder schedule shells, and plain-adder structured same-Circuit
witness interfaces.  Modular arithmetic units are re-exported by
`QuantumAlg.Primitives.MAU`.
-/

@[expose] public section
