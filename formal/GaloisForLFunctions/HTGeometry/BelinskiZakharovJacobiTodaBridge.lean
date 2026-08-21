import GaloisForLFunctions.HTGeometry.KerrNewmanBelinskiZakharovBridge
import GaloisForLFunctions.HTGeometry.JacobiTodaRiccatiLaw

/-!
# Belinski--Zakharov residues in a finite Jacobi--Toda boundary law

The finite Jacobi--Toda Riccati law has a terminal rank-one boundary defect.  This module fixes a
closed, nontrivial coefficient system and identifies its two-mode defect with the rank-one residue
already used by the BZ dressing layer.  The result is an exact finite-dimensional algebraic bridge,
not a claim that Toda flow is a gravitational inverse-scattering reduction.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Closed off-diagonal coefficients for a canonical Jacobi--Toda instance. -/
def belinskiZakharovJacobiTodaA (n : ℕ) : ℝ := n

/-- The canonical Jacobi--Toda diagonal coefficients vanish. -/
def belinskiZakharovJacobiTodaB (_ : ℕ) : ℝ := 0

/-- The canonical off-diagonal derivative coefficients vanish. -/
def belinskiZakharovJacobiTodaAPrime (_ : ℕ) : ℝ := 0

/-- The diagonal derivative required by the nonisospectral Toda law. -/
def belinskiZakharovJacobiTodaBPrime (n : ℕ) : ℝ :=
  2 * ((n : ℝ) - 1) * belinskiZakharovJacobiTodaA n ^ 2 -
    2 * ((n : ℝ) + 1) * belinskiZakharovJacobiTodaA (n + 1) ^ 2 -
      belinskiZakharovJacobiTodaB n ^ 2

/-- The declared coefficient system satisfies the Toda derivative relations without any external
solution or regularity premise. -/
theorem belinskiZakharovJacobiToda_deriv :
    JacobiTodaDeriv belinskiZakharovJacobiTodaA belinskiZakharovJacobiTodaB
      belinskiZakharovJacobiTodaAPrime belinskiZakharovJacobiTodaBPrime := by
  refine ⟨?_, ?_, ?_⟩
  · norm_num [belinskiZakharovJacobiTodaA]
  · intro n
    rfl
  · intro n
    simp [belinskiZakharovJacobiTodaA, belinskiZakharovJacobiTodaB,
      belinskiZakharovJacobiTodaAPrime]

/-- The canonical coefficient system has the exact finite Riccati law with its terminal
rank-one boundary residue. -/
theorem belinskiZakharovJacobiToda_riccati (m : ℕ) :
    jacobiCompression belinskiZakharovJacobiTodaAPrime belinskiZakharovJacobiTodaBPrime (m + 1)
      = jacobiCompression belinskiZakharovJacobiTodaA belinskiZakharovJacobiTodaB (m + 1) *
          connectionCompression belinskiZakharovJacobiTodaA (m + 1)
        - connectionCompression belinskiZakharovJacobiTodaA (m + 1) *
          jacobiCompression belinskiZakharovJacobiTodaA belinskiZakharovJacobiTodaB (m + 1)
        - jacobiCompression belinskiZakharovJacobiTodaA belinskiZakharovJacobiTodaB (m + 1) *
          jacobiCompression belinskiZakharovJacobiTodaA belinskiZakharovJacobiTodaB (m + 1)
        - (2 * ((m : ℝ) + 1) * belinskiZakharovJacobiTodaA (m + 1) ^ 2) •
            Matrix.vecMulVec (fun i : Fin (m + 1) => if (i : ℕ) = m then (1 : ℝ) else 0)
              (fun i : Fin (m + 1) => if (i : ℕ) = m then (1 : ℝ) else 0) :=
  jacobiCompression_deriv_eq_riccati _ _ _ _ belinskiZakharovJacobiToda_deriv m

/-- In two modes, a terminal Jacobi boundary residue is a BZ rank-one residue. -/
theorem belinskiZakharovTerminalJacobiResidue_eq
    (coefficient : ℝ) :
    coefficient • Matrix.vecMulVec (fun i : Fin 2 => if (i : ℕ) = 1 then (1 : ℝ) else 0)
      (fun i : Fin 2 => if (i : ℕ) = 1 then (1 : ℝ) else 0) =
      belinskiZakharovRankOneResidue ![0, coefficient] ![0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [belinskiZakharovRankOneResidue, Matrix.vecMulVec]

/-- The two-mode canonical Jacobi--Toda Riccati defect is the explicit BZ residue
`![0,16] ⊗ ![0,1]`. -/
theorem belinskiZakharovJacobiToda_twoModeRiccati :
    jacobiCompression belinskiZakharovJacobiTodaAPrime belinskiZakharovJacobiTodaBPrime 2
      = jacobiCompression belinskiZakharovJacobiTodaA belinskiZakharovJacobiTodaB 2 *
          connectionCompression belinskiZakharovJacobiTodaA 2
        - connectionCompression belinskiZakharovJacobiTodaA 2 *
          jacobiCompression belinskiZakharovJacobiTodaA belinskiZakharovJacobiTodaB 2
        - jacobiCompression belinskiZakharovJacobiTodaA belinskiZakharovJacobiTodaB 2 *
          jacobiCompression belinskiZakharovJacobiTodaA belinskiZakharovJacobiTodaB 2
        - belinskiZakharovRankOneResidue ![0, 16] ![0, 1] := by
  have h := belinskiZakharovJacobiToda_riccati 1
  norm_num [belinskiZakharovJacobiTodaA] at h
  rw [belinskiZakharovTerminalJacobiResidue_eq] at h
  simpa using h

end

end GaloisForLFunctions.HTGeometry
