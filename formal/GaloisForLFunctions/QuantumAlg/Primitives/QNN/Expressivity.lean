/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import GaloisForLFunctions.QuantumAlg.Init
public import GaloisForLFunctions.QuantumAlg.Util.Polynomial.Trigonometric
public import GaloisForLFunctions.QuantumAlg.Primitives.QSP
public import GaloisForLFunctions.QuantumAlg.Primitives.ParameterShift
public import GaloisForLFunctions.QuantumAlg.Primitives.GeneralizedParameterShift
public import GaloisForLFunctions.QuantumAlg.Primitives.QNN.Ansatz
public import GaloisForLFunctions.QuantumAlg.Primitives.QKernel
public import GaloisForLFunctions.QuantumAlg.Primitives.QNN.Overparam

/-!
# Quantum machine learning expressivity

Umbrella module for the expressivity pillar of quantum machine learning. The
development runs from the trigonometric-polynomial substrate through
single-qubit realizability, variational cost classes and shift rules, quantum
phase processing, singular-value transformation, kernel expressivity, and the
QFIM capacity ceiling.

This umbrella is distinct from `QuantumAlg.Primitives.QKernel.Expressivity`,
which is a content module for embedding quantum-kernel realizability and is
re-exported here through the quantum-kernel umbrella.

- `QuantumAlg.Init` — the shared public prelude for Lean-QuantumAlg modules.
- `QuantumAlg.Util.Polynomial.Trigonometric` — the trigonometric-polynomial
  substrate for frequency representations and shift rules.
- `QuantumAlg.Primitives.QSP` — single-qubit QSP realizability together with
  the QPP and QSVT phase-processing descendants.
- `QuantumAlg.Primitives.ParameterShift` — the frequency-one cost class and
  its exact two-point parameter-shift rule.
- `QuantumAlg.Primitives.GeneralizedParameterShift` — finite-frequency first-
  and second-derivative shift rules.
- `QuantumAlg.Primitives.QNN.Ansatz` — multi-gate variational ansatzes
  whose coordinate costs are trigonometric and admit parameter shifts.
- `QuantumAlg.Primitives.QKernel` — fidelity, Fourier, concentration,
  advantage, and embedding-kernel expressivity results.
- `QuantumAlg.Primitives.QNN.Overparam` — the QFIM-rank capacity ceiling,
  achievable-rank saturation, concrete QFIM realization, and resulting QNN
  overparametrization bounds.
-/

@[expose] public section
