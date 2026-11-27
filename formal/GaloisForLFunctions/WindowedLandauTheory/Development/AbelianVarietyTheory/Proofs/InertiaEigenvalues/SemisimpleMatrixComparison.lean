import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleColumnRepresentation
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleTraceComparison
import Mathlib.LinearAlgebra.Matrix.Trace

/-! The trace of a semisimple general linear representation in
characteristic zero determines its conjugacy class. -/

open WindowedLandauTheory.MainNotions.N

namespace GlobalTheory.SemisimpleMatrix

theorem exists_conj_of_trace_eq {Γ k : Type} [Group Γ] [Field k] [CharZero k] {n : ℕ}
    (ρ σ : Γ →* GL (Fin n) k) (hρ : IsSSRep ρ) (hσ : IsSSRep σ)
    (h : ∀ g, (ρ g).val.trace = (σ g).val.trace) :
    ∃ P : GL (Fin n) k, ∀ g, σ g = P * ρ g * P⁻¹ := by
  obtain ⟨e, he⟩ := GlobalTheory.TraceIso.exists_equiv_of_trace_eq (colRep ρ) (colRep σ)
    (colRep_semisimple ρ hρ) (colRep_semisimple σ hσ) (fun g => by
      simpa only [colRep_apply, Matrix.trace_toLin'_eq] using h g)
  let P : GL (Fin n) k :=
    ⟨LinearMap.toMatrix' e.toLinearMap, LinearMap.toMatrix' e.symm.toLinearMap,
      by rw [← LinearMap.toMatrix'_comp]; simp,
      by rw [← LinearMap.toMatrix'_comp]; simp⟩
  refine ⟨P, fun g => ?_⟩
  apply (eq_mul_inv_iff_mul_eq).mpr
  apply Units.ext
  rw [Units.val_mul, Units.val_mul]
  apply Matrix.toLin'.injective
  rw [Matrix.toLin'_mul, Matrix.toLin'_mul]
  have hP : Matrix.toLin' P.val = e.toLinearMap := Matrix.toLin'_toMatrix' _
  rw [hP]
  apply LinearMap.ext
  intro v
  exact (he g v).symm

end GlobalTheory.SemisimpleMatrix
