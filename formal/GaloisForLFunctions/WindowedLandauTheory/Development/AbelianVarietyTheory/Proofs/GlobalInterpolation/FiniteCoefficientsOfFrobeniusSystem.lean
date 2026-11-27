import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CompactPadicCoefficientField
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleMatrixComparison
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

/-! A finite set of coefficients suffices to realize any continuous
semisimple representation with a prescribed dense Frobenius system. -/

noncomputable section

open WindowedLandauTheory.MainNotions.N

namespace GlobalTheory.CompactRepField

private theorem exists_finite_entry_set (l : ℕ) [Fact l.Prime]
    {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [T2Space Γ]
    {a : ℕ} (ρ : Γ →* GL (Fin a) (PadicAlgCl l))
    (hc : Continuous fun g => (ρ g).val) :
    ∃ S : Finset (PadicAlgCl l), ∀ K : IntermediateField ℚ_[l] (PadicAlgCl l),
      (∀ z ∈ S, z ∈ K) → ∀ g s t, (ρ g).val s t ∈ K := by
  obtain ⟨L, hLfin, hL⟩ := exists_finiteDimensional_entries_mem l Γ a ρ
    (fun i j => hc.matrix_elem i j)
  letI := hLfin
  classical
  let b := Module.finBasis ℚ_[l] L
  refine ⟨Finset.univ.image (fun i => (b i : PadicAlgCl l)), fun K hK g i j => ?_⟩
  have hsub : ∀ x : L, (x : PadicAlgCl l) ∈ K := by
    intro x
    have hx := b.mem_span x
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      exact hK _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))
    | zero => exact K.zero_mem
    | add y z _ _ hy hz => exact K.add_mem hy hz
    | smul c y _ hy => exact K.smul_mem hy
  exact hsub ⟨_, hL g i j⟩

/-- Choose coefficients for one realization. Equality on the dense test
set gives equality of traces everywhere and hence conjugacy of all
semisimple realizations. -/
theorem exists_finite_coefficients_of_frobenius_system (l : ℕ) [Fact l.Prime]
    (ι : PadicAlgCl l ≃+* ℂ)
    {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [T2Space Γ]
    (a : ℕ) (U : Set Γ) (p : Γ → Polynomial ℂ) (hU : Dense U) :
    ∃ S : Finset ℂ, ∀ K : IntermediateField ℚ_[l] (PadicAlgCl l), (∀ z ∈ S, ι.symm z ∈ K) →
      ∀ ρ : Γ →* GL (Fin a) (PadicAlgCl l), (Continuous fun g => (ρ g).val) → IsSSRep ρ →
        (∀ g ∈ U, (ρ g).val.charpoly.map ι.toRingHom = p g) →
        ∃ P : GL (Fin a) (PadicAlgCl l), ∀ g i j, (P⁻¹ * ρ g * P).val i j ∈ K := by
  classical
  by_cases h : ∃ ρ : Γ →* GL (Fin a) (PadicAlgCl l), (Continuous fun g => (ρ g).val) ∧
      IsSSRep ρ ∧ ∀ g ∈ U, (ρ g).val.charpoly.map ι.toRingHom = p g
  · obtain ⟨ρ₀, hc₀, hs₀, hp₀⟩ := h
    obtain ⟨S, hS⟩ := exists_finite_entry_set l ρ₀ hc₀
    refine ⟨S.image ι, fun K hK ρ hc hs hp => ?_⟩
    have htrace (r : Γ →* GL (Fin a) (PadicAlgCl l))
        (hr : Continuous fun g => (r g).val) : Continuous fun g => (r g).val.trace :=
      continuous_finsetSum _ fun i _ => hr.matrix_elem i i
    have heq : Set.EqOn (fun g => (ρ₀ g).val.trace) (fun g => (ρ g).val.trace) U := by
      intro g hg
      have hpol := Polynomial.map_injective ι.toRingHom ι.injective ((hp₀ g hg).trans (hp g hg).symm)
      change (ρ₀ g).val.trace = (ρ g).val.trace
      rw [Matrix.trace_eq_neg_charpoly_nextCoeff, Matrix.trace_eq_neg_charpoly_nextCoeff, hpol]
    have hall (g : Γ) : (ρ₀ g).val.trace = (ρ g).val.trace :=
      closure_minimal (fun _ hx => heq hx) (isClosed_eq (htrace ρ₀ hc₀) (htrace ρ hc)) (hU g)
    obtain ⟨P, hP⟩ := SemisimpleMatrix.exists_conj_of_trace_eq ρ₀ ρ hs₀ hs hall
    refine ⟨P, fun g i j => ?_⟩
    rw [hP, show P⁻¹ * (P * ρ₀ g * P⁻¹) * P = ρ₀ g by group]
    exact hS K (fun z hz => by simpa using hK (ι z) (Finset.mem_image_of_mem _ hz)) g i j
  · exact ⟨∅, fun _ _ ρ hc hs hp => (h ⟨ρ, hc, hs, hp⟩).elim⟩

end GlobalTheory.CompactRepField
