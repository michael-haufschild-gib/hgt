import GaloisForLFunctions.HTGeometry.FiniteUnitaryEuclideanExponentialMeasure
import GaloisForLFunctions.HTGeometry.FiniteUnitaryUniformExponentialAtlas

/-!
# Analytic finite words of Euclidean unitary exponential coordinates

An ordered finite product of self-adjoint exponentials is real analytic in its literal finite
Euclidean coordinates.  Determinant normalization preserves that analyticity, and compact
uniformization promotes the resulting local charts to a fixed-length global covering family.
-/

open Matrix
open scoped Matrix.Norms.L2Operator

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The ordered product of a finite tuple of Euclidean self-adjoint exponential coordinates. -/
def finiteUnitaryEuclideanExponentialWord
    (ι : Type*) [Fintype ι] [DecidableEq ι] (N : ℕ)
    (X : Fin N → Fin (Module.finrank ℝ (selfAdjoint (Matrix ι ι ℂ))) → ℝ) :
    Matrix.unitaryGroup ι ℂ :=
  (List.ofFn fun i => selfAdjoint.expUnitary
    (finiteUnitarySelfAdjointCoordinateEquiv ι (X i))).prod

/-- Splitting the first coordinate of an ordered Euclidean exponential word. -/
theorem finiteUnitaryEuclideanExponentialWord_succ
    {ι : Type*} [Fintype ι] [DecidableEq ι] (N : ℕ)
    (X : Fin (N + 1) → Fin (Module.finrank ℝ (selfAdjoint (Matrix ι ι ℂ)) ) → ℝ) :
    (finiteUnitaryEuclideanExponentialWord ι (N + 1) X : Matrix ι ι ℂ) =
      (selfAdjoint.expUnitary (finiteUnitarySelfAdjointCoordinateEquiv ι (X 0)) :
        Matrix ι ι ℂ) *
        (finiteUnitaryEuclideanExponentialWord ι N (Fin.tail X) : Matrix ι ι ℂ) := by
  have hword : (fun i : Fin (N + 1) => selfAdjoint.expUnitary
      (finiteUnitarySelfAdjointCoordinateEquiv ι (X i))) =
      Fin.cons (selfAdjoint.expUnitary (finiteUnitarySelfAdjointCoordinateEquiv ι (X 0)))
        (fun i => selfAdjoint.expUnitary
          (finiteUnitarySelfAdjointCoordinateEquiv ι (Fin.tail X i))) := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · rfl
  unfold finiteUnitaryEuclideanExponentialWord
  rw [hword, List.ofFn_cons, List.prod_cons]
  rfl

/-- Matrix coefficients of every fixed-length ordered Euclidean exponential word are real
analytic. -/
theorem analyticAt_finiteUnitaryEuclideanExponentialWord_coe
    {ι : Type*} [Fintype ι] [DecidableEq ι] (N : ℕ)
    (X : Fin N → Fin (Module.finrank ℝ (selfAdjoint (Matrix ι ι ℂ)) ) → ℝ) :
    AnalyticAt ℝ (fun Y =>
      (finiteUnitaryEuclideanExponentialWord ι N Y : Matrix ι ι ℂ)) X := by
  induction N with
  | zero =>
    simpa [finiteUnitaryEuclideanExponentialWord] using
      (analyticAt_const : AnalyticAt ℝ
        (fun _ : Fin 0 → Fin (Module.finrank ℝ (selfAdjoint (Matrix ι ι ℂ)) ) → ℝ =>
          (1 : Matrix ι ι ℂ)) X)
  | succ N ih =>
    let tailProj : (Fin (N + 1) → Fin (Module.finrank ℝ (selfAdjoint (Matrix ι ι ℂ)) ) → ℝ) →L[ℝ]
        (Fin N → Fin (Module.finrank ℝ (selfAdjoint (Matrix ι ι ℂ)) ) → ℝ) :=
      ContinuousLinearMap.pi fun j : Fin N =>
        ContinuousLinearMap.proj (R := ℝ)
          (φ := fun _ : Fin (N + 1) =>
            Fin (Module.finrank ℝ (selfAdjoint (Matrix ι ι ℂ)) ) → ℝ) j.succ
    have htailProj : AnalyticAt ℝ
        (fun Y : Fin (N + 1) → Fin (Module.finrank ℝ (selfAdjoint (Matrix ι ι ℂ)) ) → ℝ =>
          Fin.tail Y) X := by
      change AnalyticAt ℝ (tailProj :
        (Fin (N + 1) → Fin (Module.finrank ℝ (selfAdjoint (Matrix ι ι ℂ)) ) → ℝ) →
          (Fin N → Fin (Module.finrank ℝ (selfAdjoint (Matrix ι ι ℂ)) ) → ℝ)) X
      exact tailProj.analyticAt _
    have htail : AnalyticAt ℝ
        (fun Y : Fin (N + 1) → Fin (Module.finrank ℝ (selfAdjoint (Matrix ι ι ℂ)) ) → ℝ =>
          (finiteUnitaryEuclideanExponentialWord ι N (Fin.tail Y) : Matrix ι ι ℂ)) X :=
      AnalyticAt.comp
        (f := fun Y : Fin (N + 1) → Fin (Module.finrank ℝ (selfAdjoint (Matrix ι ι ℂ)) ) → ℝ =>
          Fin.tail Y)
        (g := fun Z : Fin N → Fin (Module.finrank ℝ (selfAdjoint (Matrix ι ι ℂ)) ) → ℝ =>
          (finiteUnitaryEuclideanExponentialWord ι N Z : Matrix ι ι ℂ))
        (ih (Fin.tail X)) htailProj
    have hheadProj : AnalyticAt ℝ
        (fun Y : Fin (N + 1) → Fin (Module.finrank ℝ (selfAdjoint (Matrix ι ι ℂ)) ) → ℝ =>
          Y 0) X := by
      exact (ContinuousLinearMap.proj (R := ℝ)
        (φ := fun _ : Fin (N + 1) =>
          Fin (Module.finrank ℝ (selfAdjoint (Matrix ι ι ℂ)) ) → ℝ) 0).analyticAt _
    have hhead : AnalyticAt ℝ
        (fun Y : Fin (N + 1) → Fin (Module.finrank ℝ (selfAdjoint (Matrix ι ι ℂ)) ) → ℝ =>
          (selfAdjoint.expUnitary (finiteUnitarySelfAdjointCoordinateEquiv ι (Y 0)) :
            Matrix ι ι ℂ)) X :=
      AnalyticAt.comp
        (f := fun Y : Fin (N + 1) → Fin (Module.finrank ℝ (selfAdjoint (Matrix ι ι ℂ)) ) → ℝ =>
          Y 0)
        (g := fun Z : Fin (Module.finrank ℝ (selfAdjoint (Matrix ι ι ℂ)) ) → ℝ =>
          (selfAdjoint.expUnitary (finiteUnitarySelfAdjointCoordinateEquiv ι Z) : Matrix ι ι ℂ))
        (analyticAt_finiteUnitaryEuclideanExp_coe (ι := ι) (X 0)) hheadProj
    rw [show (fun Y : Fin (N + 1) → Fin (Module.finrank ℝ (selfAdjoint (Matrix ι ι ℂ)) ) → ℝ =>
      (finiteUnitaryEuclideanExponentialWord ι (N + 1) Y : Matrix ι ι ℂ)) =
      (fun Y => (selfAdjoint.expUnitary (finiteUnitarySelfAdjointCoordinateEquiv ι (Y 0)) :
        Matrix ι ι ℂ) *
        (finiteUnitaryEuclideanExponentialWord ι N (Fin.tail Y) : Matrix ι ι ℂ)) by
          funext Y
          exact finiteUnitaryEuclideanExponentialWord_succ N Y]
    exact hhead.mul htail

/-- Determinant-normalized finite Euclidean exponential words are real analytic. -/
theorem analyticAt_finiteSpecialUnitaryNormalizedEuclideanExponentialWord_coe
    {ι : Type*} [Fintype ι] [DecidableEq ι] (i0 : ι) (N : ℕ)
    (X : Fin N → Fin (Module.finrank ℝ (selfAdjoint (Matrix ι ι ℂ)) ) → ℝ) :
    AnalyticAt ℝ (fun Y =>
      (specialUnitaryNormalize i0 (finiteUnitaryEuclideanExponentialWord ι N Y) :
        Matrix ι ι ℂ)) X := by
  apply analyticAt_specialUnitaryNormalize_coe_of_analyticAt i0
  exact analyticAt_finiteUnitaryEuclideanExponentialWord_coe N X

/-- A dimension-dependent finite Euclidean exponential word reaches every finite unitary matrix. -/
theorem exists_finiteUnitary_uniform_euclideanExponentialWord
    (ι : Type*) [Fintype ι] [DecidableEq ι] :
    ∃ N : ℕ, ∀ U : Matrix.unitaryGroup ι ℂ,
      ∃ X : Fin N → Fin (Module.finrank ℝ (selfAdjoint (Matrix ι ι ℂ)) ) → ℝ,
        finiteUnitaryEuclideanExponentialWord ι N X = U := by
  obtain ⟨N, hN⟩ := exists_finiteUnitary_uniform_expUnitary_prod ι
  refine ⟨N, fun U => ?_⟩
  obtain ⟨K, hK⟩ := hN U
  refine ⟨fun i => (finiteUnitarySelfAdjointCoordinateEquiv ι).symm (K i), ?_⟩
  simpa [finiteUnitaryEuclideanExponentialWord] using hK

/-- A dimension-dependent normalized Euclidean exponential word reaches every finite special
unitary matrix. -/
theorem exists_finiteSpecialUnitary_uniform_normalizedEuclideanExponentialWord
    (ι : Type*) [Fintype ι] [DecidableEq ι] (i0 : ι) :
    ∃ N : ℕ, ∀ S : Matrix.specialUnitaryGroup ι ℂ,
      ∃ X : Fin N → Fin (Module.finrank ℝ (selfAdjoint (Matrix ι ι ℂ)) ) → ℝ,
        specialUnitaryNormalize i0 (finiteUnitaryEuclideanExponentialWord ι N X) = S := by
  obtain ⟨N, hN⟩ := exists_finiteUnitary_uniform_euclideanExponentialWord ι
  refine ⟨N, fun S => ?_⟩
  obtain ⟨X, hX⟩ := hN (specialUnitaryToUnitary S)
  refine ⟨X, ?_⟩
  rw [hX]
  exact specialUnitaryNormalize_toUnitary i0 S

end

end GaloisForLFunctions.HTGeometry
