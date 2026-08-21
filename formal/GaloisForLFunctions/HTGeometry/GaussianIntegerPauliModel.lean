/-
# The Gaussian-integer model of the Pauli ensemble

Every Pauli word has entries in `{0, ±1, ±i}`, so the whole Pauli algebra of a finite register is
defined over the Gaussian integers, and the complex register operators are the images of Gaussian
integer matrices under the ring homomorphism `GaussianInt.toComplex`.  A coefficient vector with
rational entries therefore presents the ensemble Hamiltonian as one rational scalar times a
Gaussian-integer matrix: exact arithmetic in a decidable ring.

Main results:
* `gaussQubitPauli`, `gaussPauliMatrix` — the Pauli words over the Gaussian integers.
* `map_gaussPauliMatrix`, `map_gaussZeroProductState` — they present the complex data.
* `pauliEnsemble_eq_smul_map_gaussPauliEnsemble` — **the ensemble at rational coefficients**.
-/
import GaloisForLFunctions.HTGeometry.PauliOperatorNormSandwich
import GaloisForLFunctions.HTGeometry.ProductStabilizerCliffordOrbit
import GaloisForLFunctions.HTGeometry.PauliEnsembleCliffordCovariance
import Mathlib.NumberTheory.Zsqrtd.GaussianInt

open Matrix

noncomputable section

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

/-- Pauli `X`, `Y`, `Z` over the Gaussian integers. -/
def gaussQubitPauli (q : Fin 3) : Matrix Bool Bool GaussianInt :=
  if q = 0 then
    fun x y => if x = y then 0 else 1
  else if q = 1 then
    fun x y => if x = y then 0 else if x = false then ⟨0, -1⟩ else ⟨0, 1⟩
  else
    fun x y => if x = y then (if x = false then 1 else -1) else 0

theorem toComplex_gaussQubitPauli (q : Fin 3) (x y : Bool) :
    GaussianInt.toComplex (gaussQubitPauli q x y) = finiteQubitPauli q x y := by
  fin_cases q <;> fin_cases x <;> fin_cases y <;>
    simp [gaussQubitPauli, finiteQubitPauli, GaussianInt.toComplex_def']

/-- The four single-qubit Pauli labels over the Gaussian integers. -/
def gaussPauliOption : Option (Fin 3) → Matrix Bool Bool GaussianInt
  | none => 1
  | some q => gaussQubitPauli q

theorem toComplex_gaussPauliOption (p : Option (Fin 3)) (x y : Bool) :
    GaussianInt.toComplex (gaussPauliOption p x y) = boolPauliOption p x y := by
  cases p with
  | none =>
      by_cases h : x = y
      · subst h
        simp [gaussPauliOption, boolPauliOption, Matrix.one_apply_eq]
      · simp [gaussPauliOption, boolPauliOption, Matrix.one_apply_ne h]
  | some q => exact toComplex_gaussQubitPauli q x y

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

/-- A Pauli word of a finite register, over the Gaussian integers. -/
def gaussPauliMatrix (P : σ → Option (Fin 3)) :
    Matrix (FiniteQubitConfiguration σ) (FiniteQubitConfiguration σ) GaussianInt :=
  fun x y => ∏ s, gaussPauliOption (P s) (x s) (y s)

theorem map_gaussPauliMatrix (P : σ → Option (Fin 3)) :
    (gaussPauliMatrix P).map GaussianInt.toComplex = finitePauliMatrix P := by
  ext x y
  rw [Matrix.map_apply, gaussPauliMatrix, map_prod]
  refine Finset.prod_congr rfl fun s _ => ?_
  exact toComplex_gaussPauliOption (P s) (x s) (y s)

/-- The all-zero product state over the Gaussian integers. -/
def gaussZeroProductState : FiniteQubitConfiguration σ → GaussianInt :=
  fun x => ∏ s, (if x s then 0 else 1)

theorem map_gaussZeroProductState (x : FiniteQubitConfiguration σ) :
    GaussianInt.toComplex (gaussZeroProductState x) = zeroProductState σ x := by
  have hz : zeroProductState σ x = ∏ s, boolZeroState (x s) := rfl
  rw [gaussZeroProductState, map_prod, hz]
  refine Finset.prod_congr rfl fun s _ => ?_
  by_cases h : x s <;> simp [h, boolZeroState]

/-- The ensemble Hamiltonian with integer coefficients, over the Gaussian integers. -/
def gaussPauliEnsemble (m : (σ → Option (Fin 3)) → ℤ) :
    Matrix (FiniteQubitConfiguration σ) (FiniteQubitConfiguration σ) GaussianInt :=
  ∑ P, m P • gaussPauliMatrix P

theorem map_gaussPauliEnsemble (m : (σ → Option (Fin 3)) → ℤ) :
    (gaussPauliEnsemble m).map GaussianInt.toComplex
      = ∑ P, ((m P : ℂ)) • finitePauliMatrix P := by
  have hring : ∀ A : Matrix (FiniteQubitConfiguration σ) (FiniteQubitConfiguration σ) GaussianInt,
      A.map GaussianInt.toComplex = GaussianInt.toComplex.mapMatrix A := fun _ => rfl
  rw [gaussPauliEnsemble, hring, map_sum]
  refine Finset.sum_congr rfl fun P _ => ?_
  rw [map_zsmul, ← hring, map_gaussPauliMatrix]
  exact (Int.cast_smul_eq_zsmul ℂ (m P) (finitePauliMatrix P)).symm

/-- **The ensemble at rational coefficients.**  If every coefficient product `w_P J_P` is `m_P / D`
then the Hamiltonian is `D⁻¹` times the image of a Gaussian-integer matrix. -/
theorem pauliEnsemble_eq_smul_map_gaussPauliEnsemble
    (w J : (σ → Option (Fin 3)) → ℝ) (m : (σ → Option (Fin 3)) → ℤ) {D : ℝ} (hD : D ≠ 0)
    (hm : ∀ P, D * (w P * J P) = (m P : ℝ)) :
    pauliEnsemble w J = ((D⁻¹ : ℝ) : ℂ) • ((gaussPauliEnsemble m).map GaussianInt.toComplex) := by
  rw [map_gaussPauliEnsemble, pauliEnsemble, Finset.smul_sum]
  refine Finset.sum_congr rfl fun P _ => ?_
  rw [smul_smul]
  congr 1
  have : (m P : ℝ) = D * (w P * J P) := (hm P).symm
  rw [show ((m P : ℂ)) = (((m P : ℝ)) : ℂ) by push_cast; ring, this]
  have hDC : ((D : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hD
  push_cast
  field_simp

end GaloisForLFunctions.HTGeometry

end
