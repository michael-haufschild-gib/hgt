import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.AdaptiveSampling.ContactRecurrence.ScalarFace
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.EntrySensitivity.GaussianChart

/-! # Scalar visits at bounded tick gaps on the actual first-excursion clock -/

open Filter Set MeasureTheory Matrix Real
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.AdaptiveSampling.ContactRecurrence
open EmptyVisitFlux PrecisionReturns
noncomputable section

/-- Every lattice through a first scalar contact has bounded gaps
between visits at precisely the contact error. The step and the
outside observation origin may both be chosen from the frozen draw. -/
theorem gaussian_first_scalar_tick_gaps (ε : ℝ) (hε : 0<ε) (hs : ε<sqrt 2) :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ k : ℕ, let N := k+3
      let H : selfAdjoint (Register N) := ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),
        isSelfAdjoint_pathHamiltonian _⟩
      ∀ a > (0:ℝ), ε<orbitCircuitDistance H 0 a → let v := firstVisit H a 0 ε
        ∀ τ : ℝ, ∃ B : ℕ, ∀ n : ℤ, ∃ j ∈ Icc n (n+B),
          HasProjectiveCircuitApproximation N ε 0 (unitaryEvolution H.val (v+(j:ℝ)*τ)) := by
  filter_upwards [EntrySensitivity.gaussian_first_empty_inward_face ε hε hs] with ω hω k
  intro N H a ha hout v τ
  obtain ⟨i,j,hf⟩ := hω k a ha hout
  obtain ⟨B,hB⟩ := face_tick_gaps (SharpOccupation.physicalArc_spec hε hs).1.1 hf τ
  refine ⟨B,fun n => ?_⟩
  obtain ⟨l,hl,hfit⟩ := hB n
  exact ⟨l,hl,(physical_visit H hε hs _).mp hfit⟩

/-- Starting at the actual robust crossing, use the first empty return
wait as the clock period. At error one tenth every sufficiently long
block of consecutive ticks then contains another empty-circuit visit. -/
theorem gaussian_unshifted_first_excursion_tick_gaps :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop, let N := k+3
      let H : selfAdjoint (Register N) := ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),
        isSelfAdjoint_pathHamiltonian _⟩
      let P := nearHilbertContinuousCircuitBudget N
      ∃ σ > (0:ℝ), orbitCircuitDistance H P σ=9/80 ∧
        (∀ t∈Ico 0 σ, orbitCircuitDistance H P t<9/80) ∧
        let v := firstVisit H σ 0 (1/10)
        0<v-σ ∧ ∃ B : ℕ, ∀ n : ℕ, ∃ j ∈ Icc n (n+B),
          HasProjectiveCircuitApproximation N (1/10) 0 (unitaryEvolution H.val (σ+(j:ℝ)*(v-σ))) := by
  have hs : (1/10:ℝ)<sqrt 2 := by nlinarith only [sq_sqrt (by norm_num : (0:ℝ)≤2),sqrt_nonneg 2]
  filter_upwards [gaussian_first_scalar_tick_gaps (1/10) (by norm_num) hs,
    FirstGate.gaussian_first_crossing_one_gate] with ω hω hc
  filter_upwards [hc] with k hk
  intro N H P
  obtain ⟨σ,hσ,hcross,hbefore,_⟩ := hk
  have hfar : 1/10<orbitCircuitDistance H 0 σ := by
    by_contra! hh
    obtain ⟨z,hz,C,hC,he⟩ := (hasProjectiveCircuitApproximation_iff_infDist _ 0 (1/10:ℝ)).mpr hh
    have hle : orbitCircuitDistance H P σ≤1/10 := (hasProjectiveCircuitApproximation_iff_infDist ..).mp
      ⟨z,hz,C,hC.trans (Nat.zero_le _),he⟩
    rw [hcross] at hle
    norm_num at hle
  refine ⟨σ,hσ,hcross,hbefore,?_⟩
  intro v
  refine ⟨sub_pos.mpr (FirstGate.first_empty_entry_of_outside H (by norm_num) hs hfar).1,?_⟩
  obtain ⟨B,hB⟩ := hω k σ hσ hfar (v-σ)
  refine ⟨B,fun n => ?_⟩
  obtain ⟨l,hl,hfit⟩ := hB ((n:ℤ)-1)
  obtain ⟨hlo,hhi⟩ : (n:ℤ)-1≤l ∧ l≤(n:ℤ)-1+(B:ℤ) := hl
  let j := (l+1).toNat
  have hj : (j:ℤ)=l+1 := Int.toNat_of_nonneg (by omega)
  have ht : (j:ℝ)=(l:ℝ)+1 := by exact_mod_cast hj
  refine ⟨j,⟨by omega,by omega⟩,?_⟩
  rw [ht,show σ+((l:ℝ)+1)*(v-σ)=v+(l:ℝ)*(v-σ) by ring]
  exact hfit

#print axioms gaussian_first_scalar_tick_gaps
#print axioms gaussian_unshifted_first_excursion_tick_gaps
end
end GaloisForLFunctions.HTGeometry.AdaptiveSampling.ContactRecurrence
