/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import GaloisForLFunctions.QuantumAlg.Init
public import GaloisForLFunctions.QuantumAlg.Primitives.EllipticCurve.PointAddition
public import GaloisForLFunctions.QuantumAlg.Primitives.EllipticCurve.Resource
public import GaloisForLFunctions.QuantumAlg.Primitives.EllipticCurve.CleanComposition
public import GaloisForLFunctions.QuantumAlg.Primitives.EllipticCurve.ScalarMultiplication
public import GaloisForLFunctions.QuantumAlg.Primitives.EllipticCurve.ScalarMultiplicationEndpoint
public import GaloisForLFunctions.QuantumAlg.Primitives.EllipticCurve.ScalarMultiplication.StructuredCircuit

/-!
# Elliptic-curve primitives

This module re-exports elliptic-curve circuit-facing primitive components,
including encoded structured-circuit witness layers.
-/

@[expose] public section
