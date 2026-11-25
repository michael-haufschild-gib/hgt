import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.SelectedDates.AlgebraicCurves.ClosingRatio
import GaloisForLFunctions.HTGeometry.PrescribedModulusPhases
import GaloisForLFunctions.HTGeometry.BigradedCorank

/-! # The unique possible algebraic dependence at a first scalar entry -/

open Set MeasureTheory Matrix Real
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpectralJets.SelectedDates.AlgebraicCurves
open PrecisionReturns
noncomputable section

/-- At every prescribed error, the off-pair ratios are independent even
over the closing ratio. Including that last ratio preserves independence
over the rationals precisely when the error is transcendental. -/
theorem gaussian_first_scalar_ratio_field (ε : ℝ) (hε : 0<ε) (hs : ε<sqrt 2) :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ k : ℕ, let N := k+3
      let H : selfAdjoint (Register N) := ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),
        isSelfAdjoint_pathHamiltonian _⟩
      let E := H.2.isHermitian.eigenvalues
      ∀ a > (0:ℝ), ε<orbitCircuitDistance H 0 a → let v := firstVisit H a 0 ε
        ∃ i j : Fin N → Bool, i≠j ∧
          let p := fun l => anchorPhase E l v/anchorPhase E j v
          let x := fun _ : Unit => p i
          let y := fun l : Outside i j => p l.val
          p i=closingRatio ε ∧ AlgebraicIndependent (IntermediateField.adjoin ℚ (range x)) y ∧
            (AlgebraicIndependent ℚ (Sum.elim y x) ↔ Transcendental ℚ (ε:ℂ)) := by
  let z := closingRatio ε
  let K := IntermediateField.adjoin ℚ (range fun _ : Unit => z)
  letI : Countable K := (countable_intermediateFieldAdjoin (countable_range _)).to_subtype
  filter_upwards [gaussian_first_scalar_independent_ratios K ε hε hs] with ω hω k
  intro N H E a ha hout v
  obtain ⟨i,j,hij,⟨q,hg⟩,hi⟩ := hω k a ha hout
  refine ⟨i,j,hij,?_⟩
  intro p x y
  have hp : p i=z := anchor_div_at_closing_gap E hg
  have hK : IntermediateField.adjoin ℚ (range x)=K := by dsimp only [x,K]; rw [hp]
  have hy : AlgebraicIndependent (IntermediateField.adjoin ℚ (range x)) y := by
    rw [hK]
    exact hi
  refine ⟨hp,hy,?_⟩
  rw [algebraicIndependent_sumElim_intermediateField_iff,and_iff_left hy,algebraicIndependent_unique_type_iff]
  change Transcendental ℚ (p i) ↔ _
  rw [hp]
  exact not_congr (closingRatio_algebraic_iff hε hs)

/-- At one tenth the only possible dependence comes from a closing
ratio satisfying the displayed rational quadratic. -/
theorem gaussian_tenth_first_scalar_relation :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ k : ℕ, let N := k+3
      let H : selfAdjoint (Register N) := ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),
        isSelfAdjoint_pathHamiltonian _⟩
      let E := H.2.isHermitian.eigenvalues
      ∀ a > (0:ℝ), 1/10<orbitCircuitDistance H 0 a → let v := firstVisit H a 0 (1/10)
        ∃ i j : Fin N → Bool, i≠j ∧
          let p := fun l => anchorPhase E l v/anchorPhase E j v
          10000*(p i)^2-19601*p i+10000=0 ∧ AlgebraicIndependent
            (IntermediateField.adjoin ℚ {p i}) (fun l : Outside i j => p l.val) := by
  have hs : (1/10:ℝ)<sqrt 2 := by nlinarith only [sq_sqrt (by norm_num : (0:ℝ)≤2),sqrt_nonneg 2]
  filter_upwards [gaussian_first_scalar_ratio_field (1/10) (by norm_num) hs] with ω hω k
  intro N H E a ha hout v
  obtain ⟨i,j,hij,hp,hi,_⟩ := hω k a ha hout
  refine ⟨i,j,hij,?_⟩
  intro p
  change p i=closingRatio (1/10) at hp
  refine ⟨?_,?_⟩
  · have h := closingRatio_add_inv (by norm_num : (0:ℝ)<1/10) hs
    have hz : closingRatio (1/10)≠0 := Complex.exp_ne_zero _
    norm_num at h
    rw [hp]
    field_simp [hz] at h
    linear_combination h
  · have hr : range (fun _ : Unit => p i)={p i} := by
      ext z
      constructor
      · rintro ⟨_,rfl⟩
        exact mem_singleton _
      · intro h
        exact ⟨(),(mem_singleton_iff.mp h).symm⟩
    change AlgebraicIndependent (IntermediateField.adjoin ℚ (range fun _ : Unit => p i))
      (fun l : Outside i j => p l.val) at hi
    rwa [hr] at hi

#print axioms gaussian_first_scalar_ratio_field
#print axioms gaussian_tenth_first_scalar_relation
end
end GaloisForLFunctions.HTGeometry.SpectralJets.SelectedDates.AlgebraicCurves
