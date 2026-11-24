import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnSpacing.PhysicalComponents.Depth.AllDepths
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnSpacing.PhysicalComponents.CircuitWindows.ComponentSweep
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.LocalSimulation.Precision.QuadraticBits

/-! # Whole affordable intervals centered on actual entries to the scalar tube -/

open Filter Finset Set MeasureTheory Real
namespace GaloisForLFunctions.HTGeometry.ReturnSpacing.PhysicalComponents.EntryWindows
open SharpOccupation EmptyVisitFlux Depth
noncomputable section

/-- Entries whose full two-sided time interval admits the given physical
gate budget. Each date can use a different circuit. -/
def covered {N : ℕ} (H : selfAdjoint (Register N)) (s : ℕ) (ε R : ℝ) (A : Finset ℝ) : Finset ℝ := by
  classical
  exact A.filter fun u => ∀ v : ℝ, |v-u| ≤ R → v∈visitSet H s ε

private theorem inflate {N s : ℕ} (H : selfAdjoint (Register N)) {a w R J ε δ h : ℝ}
    (hw : w∈visitSet H 0 δ) (hd : |w-a| ≤ J) (he : δ+h ≤ ε)
    (hs : ∀ t : ℝ, |t| ≤ R+J → t∈visitSet H s h) :
    ∀ v : ℝ, |v-a| ≤ R → v∈visitSet H s ε := by
  intro v hv
  have hlag : |v-w| ≤ R+J := by
    rw [show v-w=(v-a)+(a-w) by ring]
    exact (abs_add_le ..).trans (add_le_add hv (by simpa only [abs_sub_comm a w] using hd))
  obtain ⟨z,hz,C,hC,hfit⟩ := affordable_add_time H (x:=w) (y:=v-w) hw (hs _ hlag)
  rw [show w+(v-w)=v by ring] at hfit
  exact ⟨z,hz,C,by simpa only [zero_add] using hC,hfit.trans he⟩

/-- At fixed error, the depth law gives a lower fraction of genuine
scalar entries supporting an entire exponentially long affordable interval.
The observation starts at any prescribed or sample-dependent nonnegative date. -/
theorem gaussian_entry_window_mass (γ α : ℝ) (hγ : 0 ≤ γ) (hγα : γ < α) (hα : α ≤ 1) :
    ∃ m > 0, ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop,
      let N := k+3
      let H : selfAdjoint (Register N) := ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),isSelfAdjoint_pathHamiltonian _⟩
      let E := fun i => -H.2.isHermitian.eigenvalues i
      let R := (2:ℝ)^(γ*(N:ℝ))/2
      let s := ⌊(2:ℝ)^(α*(N:ℝ))⌋₊
      let h := 1/(2:ℝ)^((N/m)^2)
      ∀ ε∈Ioo (0:ℝ) (sqrt 2), ∀ δ∈Ioc (0:ℝ) ε, δ+h ≤ ε → ∀ a ≥ (0:ℝ),
        ∀ p < (physicalArc δ/physicalArc ε)^(2^N-2:ℕ), ∀ᶠ T : ℝ in atTop,
          let A := entriesAfter E (physicalArc ε) a T
          p < ((covered H s ε R A).card:ℝ)/A.card := by
  classical
  obtain ⟨m,hm,hcompile⟩ := LocalPatches.gaussian_quadratic_precision_compiler γ α hγ hγα hα
  obtain ⟨A,B,hA,_,hwidth⟩ := CircuitWindows.gaussian_component_sweep
  obtain ⟨K,hK⟩ := exists_nat_gt (2*A)
  refine ⟨m,hm,?_⟩
  filter_upwards [hcompile,hwidth,gaussian_scalar_component_depth] with ω hc hw hdepth
  filter_upwards [hc,(tendsto_add_atTop_nat 1).eventually hw,eventually_ge_atTop K] with k hc hw hk
  intro N H E R s h ε hε δ hδ he a ha p hp
  have hN : 0 < (N:ℝ) := by dsimp only [N]; positivity
  have hsmall : A/(N:ℝ) ≤ 1/2 := by
    apply (div_le_iff₀ hN).mpr
    have hKN : (K:ℝ) ≤ N := by exact_mod_cast (show K ≤ N by dsimp only [N]; omega)
    linarith only [hK,hKN]
  have hR : 1 ≤ (2:ℝ)^(γ*(N:ℝ)) := one_le_rpow (by norm_num) (mul_nonneg hγ hN.le)
  have hfit (t : ℝ) (ht : |t| ≤ R+1/2) : t∈visitSet H s h :=
    hc t (ht.trans (by dsimp only [R]; linarith only [hR]))
  have hd := hdepth k a ha ε hε δ hδ
  filter_upwards [hd.eventually_const_lt hp] with T hfreq
  let F := entriesAfter E (physicalArc ε) a T
  have sub : reached (visitSet H 0 ε) (visitSet H 0 δ) F ⊆ covered H s ε R F := by
    intro u hu
    obtain ⟨hu,w,huw,hwδ,hseg⟩ := mem_filter.mp (show u∈F.filter _ from hu)
    have hdist : |w-u| ≤ 1/2 := by rw [abs_of_nonneg (sub_nonneg.mpr huw)]; exact (hw ε hε u w huw hseg).1.trans hsmall
    exact mem_filter.mpr ⟨hu,inflate H hwδ hdist he hfit⟩
  exact hfreq.trans_le (div_le_div_of_nonneg_right (by exact_mod_cast Finset.card_le_card sub) (Nat.cast_nonneg _))

#print axioms gaussian_entry_window_mass
end
end GaloisForLFunctions.HTGeometry.ReturnSpacing.PhysicalComponents.EntryWindows
