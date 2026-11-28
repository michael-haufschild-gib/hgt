import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Dephasing.PairedFields.SpectralEdge.IndependentFields.PhysicalDate
import GaloisForLFunctions.HTGeometry.ContinuousPlateauGrid

/-! # Continuous-time visits at a fixed gate budget -/

open MeasureTheory Set
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.LocalPatches.RampWindows
open Dephasing.PairedFields Dephasing.PairedFields.SpectralEdge
noncomputable section
local instance : IsProbabilityMeasure pathPauliDisorderLaw := by unfold pathPauliDisorderLaw; infer_instance

/-- A visit at any real time in [A,T] implies a centered test at a nearby
grid time. The spectral comparison and physical speed tail are each charged
once, independent of the duration and number of readings. -/
theorem centered_fixed_budget_window (n s r : ℕ) (hr : r ≤ Fintype.card (Fin (n+2) → Bool))
    {A T L ρ h M : ℝ} (hA : 0 ≤ A) (hT : 0<T) (hL : |L| ≤ T)
    (hρ : 0<ρ) (hh : 0<h) (hM : 0 ≤ M) (ε : ℝ) :
    let R := firstRanks (Fin (n+2) → Bool) r hr
    let u (i : Fin (plateauGridCount (T-A) h)) := min T (plateauGridPoint A h i)
    let H (ω : PathPauliDisorder) := pathHamiltonian (pathPauliDisorderShell ω n)
    pathPauliDisorderLaw.real {ω | ∃ t∈Icc A T, HasProjectiveCircuitApproximation
      (n+2) ε s (unitaryEvolution (H ω) t)} ≤
      pathPauliDisorderLaw.real {ω | M<‖H ω‖}+
      ((∑ i, Real.sqrt ((pairLaw n).real (centeredFit n (s+s) R
        (Real.sqrt 2*(u i*(L/T))) (2*(ε+M*h+ρ))))) +
        8*Fintype.card (PathLabel n)*(r:ℝ)^2*L^2/(T*ρ^2)) := by
  intro R u H
  let ι := Fin (plateauGridCount (T-A) h)
  have hu (i : ι) : |u i| ≤ T := by
    rw [abs_of_nonneg (le_min hT.le (hA.trans (plateauGridPoint_le A hh.le i)))]
    exact min_le_left ..
  let E (i : ι) := BlockDilations.affordableDraw n s (ε+M*h) (u i)
  let X (ω : PathPauliDisorder) (l : PathLabel n) := pathPauliDisorderShell ω n l
  have hsub : {ω | ∃ t∈Icc A T, HasProjectiveCircuitApproximation (n+2) ε s
        (unitaryEvolution (H ω) t)} ⊆ {ω | M<‖H ω‖} ∪ X ⁻¹' (⋃ i, E i) := by
    rintro ω ⟨t,ht,z,hz,C,hs,herr⟩
    by_cases hspeed : M<‖H ω‖
    · exact Or.inl hspeed
    right
    have htg : t∈Icc A (A+(T-A)) := by rwa [show A+(T-A)=T by ring]
    obtain ⟨i,hi⟩ := exists_plateauGrid_near hh A htg
    have hnear : |u i-t| ≤ h := by
      dsimp only [u]
      rcases le_total T (plateauGridPoint A h i) with hclip | hclip
      · rw [min_eq_left hclip,abs_of_nonneg (sub_nonneg.mpr ht.2)]
        have hdir := (abs_le.mp hi).1
        linarith only [hclip,hdir]
      · rwa [min_eq_right hclip,abs_sub_comm]
    apply mem_iUnion.mpr
    refine ⟨i,z,hz,C,hs,?_⟩
    have hd := norm_unitaryEvolution_time_sub_le
      (isSelfAdjoint_pathHamiltonian (pathPauliDisorderShell ω n)) (u i) t
    have he : ‖unitaryEvolution (H ω) (u i)-unitaryEvolution (H ω) t‖ ≤ M*h :=
      hd.trans (mul_le_mul (le_of_not_gt hspeed) hnear (abs_nonneg _) hM)
    exact (norm_sub_le_norm_sub_add_norm_sub _ (unitaryEvolution (H ω) t) _).trans
      ((add_le_add he herr).trans_eq (add_comm ..))
  exact (measureReal_mono hsub).trans ((measureReal_union_le ..).trans (add_le_add le_rfl
    (centered_physical_schedule n r hr hT hL hρ (fun _ : ι => s) (fun _ => ε+M*h) u hu)))

#print axioms centered_fixed_budget_window
end
end GaloisForLFunctions.HTGeometry.LocalPatches.RampWindows
