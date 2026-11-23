import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.TracedLaurentResidue
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.LogarithmicOriginTrace
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.CechDifferentialComplex

/-! The traced logarithmic residue descends to top Čech cohomology. -/

noncomputable section

open GlobalTheory.CechDR
open scoped GlobalTheory.CechDR

namespace GlobalTheory.PD

variable {k F E : Type} [Field k] [Field F] [Field E]
  [Algebra k F] [Algebra k E] [Algebra F E] [IsScalarTower k F E]
  {d : ℕ} {x : Fin (d + 1) → F}

/-- Field trace followed by Laurent residue on logarithmic coefficients. -/
def topResidue (τ : DR k E →ₗ[E] E) (ρ : F →ₗ[k] k) : DR k E →ₗ[k] k :=
  ρ.comp (((Algebra.trace F E).restrictScalars k).comp (τ.restrictScalars k))

theorem topResidue_apply (τ : DR k E →ₗ[E] E) (ρ : F →ₗ[k] k) (u : DR k E) :
    topResidue τ ρ u = ρ (Algebra.trace F E (τ u)) := rfl

/-- Evaluating the residue on a top-degree Čech boundary gives zero. -/
theorem IsFinCover.topResidue_cech_boundary [CharZero k] (h : IsFinCover k E x)
    (τ : DR k E →ₗ[E] E) (hτ : IsTop (x := x) τ) (ρ : F →ₗ[k] k) (hρ : IsRes x ρ)
    {b : Finset (Fin (d + 1)) → DR k E}
    (hb : b ∈ (cech (fun I => omB k E (rB k E x I) d)).B d) :
    topResidue τ ρ (b Finset.univ) = 0 := by
  let A (I : Finset (Fin (d + 1))) := omB k E (rB k E x I) d
  obtain ⟨a, ha, rfl⟩ := hb
  change topResidue τ ρ (deltaL k (Fin (d + 1)) (DR k E) a Finset.univ) = 0
  rw [deltaL_apply, map_sum]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [map_zsmul]
  have ha' := (Submodule.mem_pi.mp ha) (Finset.univ.erase j) (Set.mem_univ _)
  change a (Finset.univ.erase j) ∈
    (if (Finset.univ.erase j).Nonempty ∧ ((Finset.univ.erase j).card : ℤ) = (d : ℤ) - 1 + 1 then
      A (Finset.univ.erase j) else ⊥) at ha'
  split_ifs at ha' with hj
  · rw [topResidue_apply, h.traced_residue_eq_zero_of_missing_chart τ hτ ρ hρ
      (Finset.notMem_erase j _) hj.1 _ ha', smul_zero]
  · rw [(Submodule.mem_bot k).mp ha', map_zero, smul_zero]

section Tower

variable {K : Type} [Field K] [Algebra k K] [Algebra F K] [Algebra K E]
  [IsScalarTower k F K] [IsScalarTower k K E] [IsScalarTower F K E]
  [Module.Finite F K] [Module.Finite K E] [Algebra.Etale K E]

/-- The base residue of the exterior trace annihilates the normalized
cover's top Čech boundaries. -/
theorem IsFinCover.topResidue_traceDR_cech_boundary [CharZero k] (h : IsFinCover k E x)
    (τ : DR k K →ₗ[K] K) (hτ : IsTop (x := x) τ) (ρ : F →ₗ[k] k) (hρ : IsRes x ρ)
    {b : Finset (Fin (d + 1)) → DR k E}
    (hb : b ∈ (cech (fun I => omB k E (rB k E x I) d)).B d) :
    topResidue τ ρ (traceDR k K E (b Finset.univ)) = 0 := by
  obtain ⟨⟨τ', hτ'⟩, hvol, _⟩ := h.topDegreeForms
  have hbd := h.topResidue_cech_boundary τ' hτ' ρ hρ hb
  have hbdeg : b Finset.univ ∈ ⋀[E]^d Ω[E⁄k] := by
    obtain ⟨a, ha, rfl⟩ := hb
    change deltaL k (Fin (d + 1)) (DR k E) a Finset.univ ∈ _
    rw [deltaL_apply]
    refine Submodule.sum_mem _ fun j _ => zsmul_mem ?_ _
    have hj := (Submodule.mem_pi.mp ha) (Finset.univ.erase j) (Set.mem_univ _)
    change a (Finset.univ.erase j) ∈
      (if (Finset.univ.erase j).Nonempty ∧ ((Finset.univ.erase j).card : ℤ) = (d : ℤ) - 1 + 1 then
        omB k E (rB k E x (Finset.univ.erase j)) d else ⊥) at hj
    split_ifs at hj
    · exact omB_le_degree hj
    · rw [(Submodule.mem_bot k).mp hj]
      exact zero_mem _
  rw [topResidue_apply, hvol τ' hτ' _ hbdeg, traceDR_vol0_coefficient τ hτ]
  exact hbd

end Tower

end GlobalTheory.PD
