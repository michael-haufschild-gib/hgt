import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.SelectedDates.AlgebraicCurves.PhysicalPhases
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.ExactContacts.CoarseVisits.FreeBasisFloor

/-! # A common fine-error gate floor at the first scalar return in every basis -/

open Set Filter Matrix MeasureTheory Real Finset
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpectralJets.SelectedDates.AlgebraicCurves
open ExactContacts.CoarseVisits PrecisionReturns
noncomputable section

private theorem card_outside {I : Type} [Fintype I] [DecidableEq I] (i j : I) (hne : i≠j) :
    Fintype.card (Outside i j)=Fintype.card I-2 := by
  let S := (univ.erase i).erase j
  let e : Outside i j ≃ ↥S := Equiv.subtypeEquivRight (fun k => by
    change (k≠i ∧ k≠j) ↔ k ∈ (Finset.univ.erase i).erase j
    simp [and_comm])
  rw [Fintype.card_congr e,Fintype.card_coe]
  simp only [S,card_erase_of_mem (mem_erase.mpr ⟨hne.symm,mem_univ _⟩),card_erase_of_mem (mem_univ i),card_univ]
  omega

/-- At the first scalar visit at error one tenth after the actual robust
crossing, some positive error costs more than floor((2^N−3)/16) gates
in every basis. The same error works for all free changes of basis. -/
theorem gaussian_tenth_first_return_basis_floor :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop, let N := k+3
      let H : selfAdjoint (Register N) := ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),
        isSelfAdjoint_pathHamiltonian _⟩
      let P := nearHilbertContinuousCircuitBudget N
      ∃ σ > (0:ℝ), orbitCircuitDistance H P σ=9/80 ∧
        (∀ t∈Set.Ico 0 σ, orbitCircuitDistance H P t<9/80) ∧
        let v := firstVisit H σ 0 (1/10)
        ∃ δ > (0:ℝ), ∀ W : unitaryGroup (Fin N → Bool) ℂ,
          ¬HasProjectiveCircuitApproximation N δ ((2^N-3)/16) (W.val*unitaryEvolution H.val v*star W.val) := by
  have hs : (1/10:ℝ)<sqrt 2 := by nlinarith only [sq_sqrt (by norm_num : (0:ℝ)≤2),sqrt_nonneg 2]
  filter_upwards [gaussian_first_scalar_independent_ratios ℚ (1/10) (by norm_num) hs,
    FirstGate.gaussian_first_crossing_one_gate] with ω hratio hcross
  filter_upwards [hcross] with k hk
  intro N H P
  obtain ⟨σ,hσ,hc,hb,_⟩ := hk
  have hfar : 1/10<orbitCircuitDistance H 0 σ := by
    by_contra! h
    obtain ⟨c,hc',C,hC,he⟩ := (hasProjectiveCircuitApproximation_iff_infDist _ 0 (1/10:ℝ)).mpr h
    have hP : orbitCircuitDistance H P σ≤1/10 := (hasProjectiveCircuitApproximation_iff_infDist ..).mp
      ⟨c,hc',C,hC.trans (Nat.zero_le _),he⟩
    rw [hc] at hP
    norm_num at hP
  refine ⟨σ,hσ,hc,hb,?_⟩
  intro v
  obtain ⟨i,j,hij,_,hi⟩ := hratio k σ hσ hfar
  apply positive_basis_floor
  rintro W ⟨z,hz,C,hC,herr⟩
  have h := exact_ratio_bound H v j (fun l : Outside i j => l.val) hi W C z hz
    (sub_eq_zero.mp (norm_le_zero_iff.mp herr))
  rw [card_outside i j hij,Fintype.card_fun,Fintype.card_fin,Fintype.card_bool] at h
  change 2^N-2 ≤ C.gateCount*16 at h
  have hcap := Nat.div_mul_le_self (2^N-3) 16
  have hdim : 3≤(2:ℕ)^N := (by norm_num : 3≤2^3).trans (Nat.pow_le_pow_right (by decide) (by dsimp [N]; omega))
  omega

#print axioms gaussian_tenth_first_return_basis_floor
end
end GaloisForLFunctions.HTGeometry.SpectralJets.SelectedDates.AlgebraicCurves
