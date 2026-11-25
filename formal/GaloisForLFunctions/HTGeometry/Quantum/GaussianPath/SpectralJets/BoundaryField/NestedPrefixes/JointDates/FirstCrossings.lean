import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.BoundaryField.NestedPrefixes.JointDates.ProductNull
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrecisionReturns.GaussianLaw

/-! # Joint null sets for the first post-crossing returns of two nested registers -/

open Set Filter Real MeasureTheory
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpectralJets.BoundaryField.NestedPrefixes.JointDates
open PrecisionReturns
noncomputable section

/-- The first positive date at which the near-Hilbert budget has error 9/80. -/
def firstCrossing (k : ℕ) (ω : PathPauliDisorder) (σ : ℝ) : Prop :=
  let h := orbitCircuitDistance (generator k ω) (nearHilbertContinuousCircuitBudget (k+3))
  0<σ ∧ h σ=9/80 ∧ ∀ t∈Ico 0 σ, h t<9/80

private theorem outside_at_crossing {k : ℕ} {ω : PathPauliDisorder} {σ : ℝ}
    (h : firstCrossing k ω σ) : 1/10<orbitCircuitDistance (generator k ω) 0 σ := by
  by_contra! hh
  obtain ⟨z,hz,C,hC,herr⟩ := (hasProjectiveCircuitApproximation_iff_infDist _ 0 (1/10:ℝ)).mpr hh
  have hp := (hasProjectiveCircuitApproximation_iff_infDist _
    (nearHilbertContinuousCircuitBudget (k+3)) (1/10:ℝ)).mp
    ⟨z,hz,C,hC.trans (Nat.zero_le _),herr⟩
  change orbitCircuitDistance (generator k ω) (nearHilbertContinuousCircuitBudget (k+3)) σ≤1/10 at hp
  rw [h.2.1] at hp
  norm_num at hp

/-- For every pair of sufficiently long strictly nested registers, the two
first scalar dates following their own first crossings avoid a prescribed
planar null set. Each register uses the original draw and error one tenth. -/
theorem gaussian_nested_distinguished_dates (S : ℕ → ℕ → Set (ℝ × ℝ))
    (hm : ∀ j k, MeasurableSet (S j k)) (hn : ∀ j k, volume (S j k)=0) :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∃ J : ℕ, ∀ j≥J, ∀ k>j, ∃ σ τ : ℝ,
      firstCrossing j ω σ ∧ firstCrossing k ω τ ∧
      (firstVisit (generator j ω) σ 0 (1/10),firstVisit (generator k ω) τ 0 (1/10))∉S j k := by
  have hε : (1/10:ℝ)∈Ioo (0:ℝ) (sqrt 2) := ⟨by norm_num,
    by nlinarith only [sq_sqrt (by norm_num : (0:ℝ)≤2),sqrt_nonneg 2]⟩
  have hd (j k : ℕ) : ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ (_ : j<k) (σ τ : ℝ),
      firstCrossing j ω σ → firstCrossing k ω τ →
      (firstVisit (generator j ω) σ 0 (1/10),firstVisit (generator k ω) τ 0 (1/10))∉S j k := by
    by_cases h : j<k
    · filter_upwards [gaussian_joint_entry_dates h hε hε (S j k) (hm j k) (hn j k)] with ω hω
      exact fun _ σ τ hσ hτ => hω σ τ hσ.1 hτ.1 (outside_at_crossing hσ) (outside_at_crossing hτ)
    · exact .of_forall fun _ hh => (h hh).elim
  filter_upwards [gaussian_first_crossing_precision_wait,
    ae_all_iff.mpr fun j => ae_all_iff.mpr (hd j)] with ω hω hjoint
  obtain ⟨J,hJ⟩ := eventually_atTop.mp hω
  have first (k : ℕ) (hk : J≤k) : ∃ τ, firstCrossing k ω τ := by
    obtain ⟨τ,ht,he,hp,_⟩ := hJ k hk
    exact ⟨τ,ht,he,hp⟩
  refine ⟨J,fun j hj k hk => ?_⟩
  obtain ⟨σ,hσ⟩ := first j hj
  obtain ⟨τ,hτ⟩ := first k (hj.trans hk.le)
  exact ⟨σ,τ,hσ,hτ,hjoint j k hk σ τ hσ hτ⟩

#print axioms gaussian_nested_distinguished_dates
end
end GaloisForLFunctions.HTGeometry.SpectralJets.BoundaryField.NestedPrefixes.JointDates
