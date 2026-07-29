import GaloisForLFunctions.HTGeometry.MatrixPrincipalSymbolDerivationLawHorizon
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Algebra.Order.Star.Real

/-!
# Before-time causal chambers

A real-linear self-adjoint first principal symbol selects a distinguished open cone of candidate
laws: those directions in which the symbol is positive definite.  This cone is convex and avoids
the determinant horizon.  For a coefficient-flat varying-derivation system satisfying the exact
lower law, every law in the cone is therefore hypertranscendental for its own selected derivation.

The mathematical statement is unconditional.  The physical assertion that reflection positivity
of a quantum field theory produces such a symbol pencil remains a separate conjectural
realization problem.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open Set

variable {g ι : Type*} [AddCommGroup g] [Module ℝ g]
  [Fintype ι] [DecidableEq ι]

/-- Candidate law directions whose first real matrix principal symbol is positive definite. -/
def matrixPrincipalCausalChamber
    (firstSymbol : g →ₗ[ℝ] Matrix ι ι ℝ) : Set g :=
  {A | (firstSymbol A).PosDef}

omit [Fintype ι] [DecidableEq ι] in
/-- Positive combinations of two causal law directions remain causal. -/
theorem matrixPrincipalCausalChamber_pos_add
    (firstSymbol : g →ₗ[ℝ] Matrix ι ι ℝ)
    {A B : g} (hA : A ∈ matrixPrincipalCausalChamber firstSymbol)
    (hB : B ∈ matrixPrincipalCausalChamber firstSymbol)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    a • A + b • B ∈ matrixPrincipalCausalChamber firstSymbol := by
  change (firstSymbol (a • A + b • B)).PosDef
  rw [map_add, map_smul, map_smul]
  exact (hA.smul ha).add (hB.smul hb)

omit [Fintype ι] [DecidableEq ι] in
/-- The causal chamber of a real-linear matrix pencil is convex. -/
theorem matrixPrincipalCausalChamber_convex
    (firstSymbol : g →ₗ[ℝ] Matrix ι ι ℝ) :
    Convex ℝ (matrixPrincipalCausalChamber firstSymbol) := by
  rw [convex_iff_add_mem]
  intro A hA B hB a b ha hb hab
  by_cases ha0 : a = 0
  · subst a
    have hb1 : b = 1 := by simpa using hab
    simpa [hb1] using hB
  by_cases hb0 : b = 0
  · subst b
    have ha1 : a = 1 := by simpa using hab
    simpa [ha1] using hA
  exact matrixPrincipalCausalChamber_pos_add firstSymbol hA hB
    (lt_of_le_of_ne ha (Ne.symm ha0))
    (lt_of_le_of_ne hb (Ne.symm hb0))

/-- Every causal direction is off the determinant horizon. -/
theorem matrixPrincipalCausalChamber_det_ne_zero
    (firstSymbol : g →ₗ[ℝ] Matrix ι ι ℝ)
    {A : g} (hA : A ∈ matrixPrincipalCausalChamber firstSymbol) :
    (firstSymbol A).det ≠ 0 :=
  (hA.det_pos).ne'

omit [Fintype ι] [DecidableEq ι] in
/-- A supplied positive direction witnesses that the causal chamber is nonempty. -/
theorem matrixPrincipalCausalChamber_nonempty
    (firstSymbol : g →ₗ[ℝ] Matrix ι ι ℝ)
    (e : g) (he : (firstSymbol e).PosDef) :
    (matrixPrincipalCausalChamber firstSymbol).Nonempty :=
  ⟨e, he⟩

variable {k L : Type*} [Field k] [Field L] [Algebra k L] [Algebra ℝ L]

/-- **Hypertranscendental causal chamber.**  In an exact coefficient-flat varying-derivation
system, every positive-definite first-symbol direction lies in the hypertranscendental phase for
the derivation selected by that very direction. -/
theorem matrixPrincipalCausalChamber_derivationIndependent
    (source : ℕ → ι → L) (observable : ι → L)
    (law : g → Derivation k L L)
    (symbol : ℕ → g → Matrix ι ι ℝ)
    (firstSymbol : g →ₗ[ℝ] Matrix ι ι ℝ)
    (hfirst : ∀ A, symbol 0 A = firstSymbol A)
    (hflat : MatrixCoefficientPrincipalSymbolFlat symbol)
    (e : g) (he : ∀ n, (symbol n e).det ≠ 0)
    (hlaw : ∀ A, MatrixPrincipalLowerLaw source
      (fun n i ↦ selectedDerivationJet (law A) n (observable i))
      (fun n ↦ symbol n A))
    (hsource : AlgebraicIndependent ℝ (fun p : ℕ × ι ↦ source p.1 p.2)) :
    matrixPrincipalCausalChamber firstSymbol ⊆
      {A | DerivationIndependentOver ℝ (law A) observable} := by
  intro A hA
  have hspectrum := derivationLawDependentSet_eq_firstSingularSet_of_coefficientFlat
    source observable law symbol hflat e he hlaw hsource
  by_contra hdependent
  have hmem : A ∈ derivationLawDependentSet (K := ℝ) law observable := hdependent
  rw [hspectrum] at hmem
  have hdet : (symbol 0 A).det ≠ 0 := by
    rw [hfirst A]
    exact matrixPrincipalCausalChamber_det_ne_zero firstSymbol hA
  exact hdet hmem

end

end GaloisForLFunctions.HTGeometry
